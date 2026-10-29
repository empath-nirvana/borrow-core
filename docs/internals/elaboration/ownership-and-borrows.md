# Cells and borrows

This chapter is the core form of the guide's [Ownership and borrows](../../../book/src/guide/ownership.md): the
cell constants, the borrow constants and their lifetimes, written out.

## Persistent and linear values

A type is **persistent** when its values hold no resource: `1`, `0`, `i32`, `i64`, `!A`, and
pairs, sums, `box` and `mu` types built from persistent types. A variable of a persistent type
can be used any number of times, or not at all.

Using a persistent value again copies it, in compiled code, for every use but the last. For
`i32`, `bool` and their pairs that copy is a few words and is never written. For recursive data
(a `mu` type, or anything holding one) the copy allocates every node, so a use that copies is
written `clone(x)`:

```bc
type List = mu X. 1 + (i32 * X)

def nil : List = roll inl ()
fn cons(x: i32, t: List) -> List = roll inr (x, t)
fn sum_alg(r: 1 + i32 * i32) -> i32 = match r { inl u -> 0 | inr (x, n) -> n + x }
def sum : !(List => i32) = fold_own[1 + i32 * X, i32] sum_alg

main -> i32 * i32 =
  let l = cons(1, cons(2, nil));
  (sum(clone(l)), sum(l))
-- answer: (i32[3], i32[3])
```

Without `clone`, the use that would copy is an error, which names the use after it:

```bc,reject
type List = mu X. 1 + (i32 * X)

def nil : List = roll inl ()
fn cons(x: i32, t: List) -> List = roll inr (x, t)
fn sum_alg(r: 1 + i32 * i32) -> i32 = match r { inl u -> 0 | inr (x, n) -> n + x }
def sum : !(List => i32) = fold_own[1 + i32 * X, i32] sum_alg

main -> i32 * i32 =
  let l = cons(1, cons(2, nil));
  (sum(l), sum(l))
-- expect: 10:8: `l` is used again at 10:16, so this use copies it, and its type `mu X. 1 + i32 * X` holds recursive data: the copy allocates every node. Write `clone(l)` to copy it here, or do not use `l` after this
```

The last use takes the value itself, and one only read through a borrow is not copied at all.

Every other value is **owned**, and its variable is used exactly once. Cells (`ref A`), borrows
(`imm 'a A`, `mut 'a A`) and thunks (`U C`) are owned. Using an owned variable twice is an
error:

```bc,reject
main : F i32 =
  k <- return (thunkv fun (y : i32) -> return y);
  return ((unbang host[add32]) (k i32[1], k i32[2]))
-- expect: 3:32: `k` is used twice here, and its type `i32 => i32` is not persistent
```

Leaving an owned value unused is not always an error: the checker frees an unused cell for you
(see [Implicit destructors](implicit-destructors.md)).

## Cells

A cell is a heap location that owns its contents.

| constant | type |
|---|---|
| `alloc[A]` | `A => ref A` |
| `free[A]` | `ref A => A` |
| `swap[A, B]` | `ref A => B => ref B * A` |

`swap` puts a new value in the cell and hands back the old one. The new value may have a
different type, so a cell can be emptied (`swap[A, 1] c ()`) and refilled later.

```bc
main : F i32 =
  r <- return (alloc[i32] i32[5]);
  q <- return (swap[i32, i32] r i32[8]);
  let (r2, old) = q;
  new <- return (free[i32] r2);
  return ((unbang host[sub32]) (new, old))
-- answer: i32[3]
```

`r` is consumed by `swap`, which returns the cell again as `r2`. The cell cannot be used after it
is freed, and cannot be freed twice: both are uses of a variable already consumed.

```bc,reject
main : F (i32 * i32) =
  r <- return (alloc[i32] i32[1]);
  return (free[i32] r, free[i32] r)
-- expect: 3:10: `r` is used twice here, and its type `ref i32` is not persistent
```

```bc,reject
main : F i32 =
  r <- return (alloc[i32] i32[1]);
  x <- return (free[i32] r);
  q <- return (swap[i32, i32] r x);
  let (r2, y) = q;
  return (free[i32] r2)
-- expect: 3:3: `r` is used twice here, and its type `ref i32` is not persistent
```

## Borrowing

A borrow gives temporary access to a cell without giving up ownership. It lasts for a
**lifetime**, written `'x`, and a lifetime is introduced by a callback: the owner passes the cell
and a function, the function runs with the borrow, and the owner gets the cell back together with
the function's result.

| constant | type |
|---|---|
| `withbor1['x, A, B]` | `ref A => (all 'x < dom. imm 'x A => box 'x B) => ref A * B` |
| `withbor2['x, @b, A, B]` | `ref A => (all 'x < dom. mut 'x A => box 'x B) => ref A * B` |
| `withbor3[@a, 'x, A, B]` | `mut @a A => (all 'x < dom. mut 'x A => box 'x B) => mut @a A * B` |

`withbor1` lends the cell immutably, `withbor2` mutably, and `withbor3` reborrows a mutable borrow
for a shorter lifetime. The callback's type is read as follows.

- `all 'x < dom. …` is a function of the lifetime `'x`, which is shorter than every lifetime in
  scope. `dom` is the meet of those lifetimes; at the top of `main` it is `top`, or `'main` in a body
  that names `main`'s lifetime (see below). A callback is
  written `thunkv Fun 'x < top. return (…)`, where `Fun 'x < @. M` binds the lifetime.
- `imm 'x A => box 'x B` takes the borrow and returns a `B` in a **box** for `'x`. `boxed['x] V`
  builds the box, and it checks that everything `V` uses outlives `'x`. This is what stops a
  borrow from escaping its lifetime.

The lifetime name in the brackets and the name in `Fun` are the same binder.

### Reading through an immutable borrow

`withload[@a, 'x, A, B] : imm @a A => (all 'x < dom. view 'x A => box 'x B) => B` reads the
cell through the borrow. The callback receives `view 'x A`, the contents as seen through the
borrow: at a type with no cells, such as `i32`, that is the value itself.

```bc
main : F i32 =
  r <- return (alloc[i32] i32[7]);
  q <- return (withbor1['x, i32, i32] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x i32) ->
            n <- return (withload['x, 'y, i32, i32] b
                   (thunkv Fun 'y < dom. return (thunkv fun (v : i32) -> return (boxed['y] v))));
            return (boxed['x] n))));
  let (r2, n) = q;
  m <- return (free[i32] r2);
  return ((unbang host[add32]) (n, m))
-- answer: i32[14]
```

An immutable borrow is owned like any other value, so it is used once. `copy[@a, A]` splits it
into two, and `forget_imm[@a, A]` discards one.

### Writing through a mutable borrow

`withswap[@a, A, B] : mut @a A => (A => A * B) => mut @a A * B` takes the contents out, runs a
function on them that returns new contents and a result, and puts the new contents back.

```bc
main : F i32 =
  r <- return (alloc[i32] i32[1]);
  q <- return (withbor2['x, top, i32, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (m : mut 'x i32) ->
            w <- return (withswap['x, i32, 1] m (thunkv fun (v : i32) ->
                   return ((unbang host[add32]) (v, i32[41]), ())));
            let (m2, u) = w;
            let () = u;
            return (boxed['x] ()))));
  let (r2, u) = q;
  let () = u;
  return (free[i32] r2)
-- answer: i32[42]
```

`withswap` hands the borrow back as `m2`. It is not used again, so the checker discards it (a
borrow's destructor does nothing). `withbor2`'s second bracket argument, here `top`, is a
lifetime that the contents' type lasts at least as long as.

A mutable borrow cannot be copied, so two mutable borrows of one cell are never live together:

```bc,reject
main : F 1 =
  r <- return (alloc[i32] i32[1]);
  q <- return (withbor2['x, top, i32, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (m : mut 'x i32) ->
            p <- return (m, m);
            return (boxed['x] ()))));
  return ()
-- expect: 5:25: `m` is used twice here, and its type `mut 'x i32` is not persistent
```

### A borrow cannot escape

A callback's result is boxed at its lifetime, and a box may hold only what outlives it. Here the
callback tries to return a closure that captures the borrow `b`, to be called after the borrow
has ended:

```bc,reject
main : F 1 =
  r <- return (alloc[i32] i32[1]);
  q <- return (withbor1['x, i32, 1 => 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x i32) ->
            return (boxed['x] (thunkv fun (u : 1) -> return (forget_imm['x, i32] b))))));
  return ()
-- expect: 5:21: `boxed['x]`: `b`, of type `imm 'x i32`, is used inside, and it cannot be shown to outlive `'x`
```

## Shortening a lifetime

`(V :> @a)` views a borrow `imm @b A` or `mut @b A` at a shorter lifetime `@a`. The checker must
be able to show `@a ⊑ @b` from the lifetimes in scope. Lifetimes nest: a lifetime introduced
inside a callback for `'x` is shorter than `'x`.

## Lifetime parameters, bounds, and `main`'s lifetime

A function's lifetime parameter `fn f<'c>(…)` stands for a lifetime strictly shorter than `top`,
so a call needs a lifetime to pass. `main` runs under a lifetime of its own, `'main`, which lasts
for its whole body and can be passed by name, `f ['main](…)`. A call that does not determine a
lifetime, from its arguments or the type expected of its result, passes `dom`, the meet of the
lifetimes in scope: `'main` at the top of `main`.

A box outlives the lifetime it is bounded by: `box 'c T` outlives `'c` itself. So a closure
bounded by `main`'s lifetime is made, called and closed in `main` with no scope of its own:

```bc
include aff

fn counter<'c>(start: i32) -> box 'c Aff[i32, i32]<'c> =
  aff_new_boxed[ref i32, i32, i32]['c](alloc(start), !thunkv fun (s : ref i32) ->
    < fun (a : i32) ->
        cx <- return (swap[i32, i32] s i32[0]);
        let (c, x) = cx;
        cu <- return (swap[i32, i32] c (x + a));
        let (c1, u) = cu;
        return (x + a, c1),
      n <- return (free[i32] s); return () >)

main -> i32 =
  let k = counter(10);
  let (a, k) = aff_call(k, 1);
  let (b, k) = aff_call(k, 2);
  aff_close(k);
  a + b
-- answer: i32[24]
```

`'main` is a borrow of a unit cell, and a cell holding `1` takes no memory, so it costs nothing
at run time. Outside `main`, a lifetime that a call leaves undetermined where no lifetime is in
scope is an error. The spelling `'main` is provisional.

A generic function's lifetime parameters are unrelated to the lifetimes in its type arguments,
unless a **lifetime bound** relates them. `aff_new_boxed` is declared

    fn aff_new_boxed[S, A, B]<'c>(s: S, step: …) -> box 'c Aff[A, B]<'c>
        where S: 'c = …

and `where S: 'c` makes each instance's `'c` shorter than every lifetime in the type given for
`S` (cf. Rust's `S: 'c`). Its body can then box the state at `'c`, and the box is checked at each
instance, at its types. At `S = mut 'x i32`, `'c` is below `'x`, so a caller passes a lifetime
shorter than `'x`; at `S = ref i32` there is no lifetime in `S`, and `'c` is only below `top`.
The spelling `where S: 'c` is provisional.

A closure that captures `mut 'x T` is bounded by a lifetime strictly below `'x`, never by `'x`
itself, so it is made inside a scope below `'x` (`corpus/aff-capture.bc`).

