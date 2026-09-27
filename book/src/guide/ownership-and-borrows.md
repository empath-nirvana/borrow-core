# Ownership and borrows

## Persistent and linear values

A type is **persistent** when its values hold no resource: `1`, `0`, `i32`, `i64`, `!A`, and
pairs, sums, `box` and `mu` types built from persistent types. A variable of a persistent type
can be used any number of times, or not at all.

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
  scope. `dom` is the meet of those lifetimes; at the top of `main` it is `top`. A callback is
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
lifetime that the contents' type outlives.

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
