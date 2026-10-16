# Recursive data and folds

## Recursive types

`mu X. A` is the recursive type whose values are `A` with `X` standing for the type itself.
`roll V` builds one from an unrolled value and `unroll V` exposes one layer.

```text
type Nat  = mu X. 1 + X                   -- zero, or a successor
type List = mu X. 1 + (ref i32 * ref X)   -- empty, or a cell holding the head and a cell holding the rest
```

A `mu` type must be closed, and `X` may not occur under `mut` or inside a computation type
(under `U`).

A list node is naturally a block (see [the previous chapter](blocks-and-families.md)): with
`shape Node = node (leaf i32) (leaf List)`, `block Node` is `ref i32 * ref List`, so
`alloc_s[Node]` allocates one node as one block.

```text
def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))
```

## Recursion

A function may call itself, and functions may call one another: they form a recursive group, and
a **driver** runs it (SPEC §20, §21). The group is the fixed point of its *generator*, the members'
bodies with their calls of the group going to a self-reference, and each of those calls is a
direct call. The default driver, `bounded`, needs nothing written: it takes the fixed point as
native calls, carrying a budget of depth, and when the budget is spent it performs `exhausted()`,
an error like any other (`include rec`). So a recursive function's row has `Exhausted`, and
something handles it:

```bc
include rec

type Tree = mu X. 1 + (X * (i32 * X))

def empty : Tree = roll inl ()
fn mk(l: Tree, v: i32, r: Tree) -> Tree = roll inr (l, (v, r))

fn build(d: i32) -> Tree = if d == 0 { empty } else { mk(build(d - 1), d, build(d - 1)) }

fn sum(t: Tree) -> i32 =
  match unroll t {
    inl u -> 0
  | inr (l, p) -> let (v, r) = p; sum(l) + v + sum(r)
  }

fn down(n: i32) -> i32 = if n == 0 { 0 } else { 1 + down(n - 1) }

main -> i32 * i32 =
  let s = with on_exhausted(!{ u -> 0 - 1 }) { sum(build(4)) };
  let d = with on_exhausted(!{ u -> 0 - 1 }) { down(20000) };
  (s, d)
-- answer: (i32[26], i32[4294967295])
```

`down(20000)` is deeper than the budget, so it performs `exhausted()`, which unwinds every level
(running what each level must finalise) and reaches `on_exhausted`. A recursion that must go
deeper runs under the heap driver, `with deep { down(20000) }`, which keeps its pending calls in
a buffer instead of on the stack, and is div.

A recursion may do what any function does. It may use a handler's capability: the capability is
passed down with each call and handed back with each answer, as to any function that uses one. It
may yield, or perform any operation, which goes to the handler around the call from outside. Its
members may answer different types: the fixed point is taken at the record of their functions.
A recursion whose body has a `while` or a `loop` is not provided yet: it is div, and its
`Exhausted` would be performed inside its loop, where no handler reaches.

A recursion may be **generic**. `lib/list.bc` (`include list`) gives `List[A]` with `nil`,
`cons`, and the recursive templates `map`, `filter` and `fold`. Each use at new types is an
instance of the whole recursion at those types, and a block given to one may itself perform
operations, which go to the handlers where the block is written:

```bc
include list

main -> List[bool] * i32 = with on_exhausted(!{ u -> (nil(), 0) }) {
  let xs = cons(3, cons(0 - 1, cons(4, nil())));
  (map(xs, !{ x -> x > 1 }), fold(cons(1, cons(2, nil())), 0, !{ (a, x) -> a + x }))
}
-- answer: (inr (inr (), inr (inl (), inr (inr (), inl ()))), i32[3])
```

The members of a generic recursion take the same type parameters, and a call of itself is at
them: a recursion that calls itself at other types is not provided.

A **layer** runs around each call a recursion makes of itself. It is a function of the call and
its argument, generic in their types, and `with L { … }` applies it to the recursions called in the
block, before their fixed point is taken: it transforms the generator, and the recursion knows
nothing of it.

```bc
include rec

effect Count { fn tick() -> i32 }

handler count(mut n: i32): Count = { tick() = { n = n + 1; n } }

fn counted[A, B](call: !(A => B), a: A) -> B = tick(); call(a)

fn fib(n: i32) -> i32 = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }

main -> i32 * i32 =
  let c = alloc(0);
  let f = with count(&mut c) { with counted { with on_exhausted(!{ u -> 0 - 1 }) { fib(10) } } };
  (f, free(c))
-- answer: (i32[55], i32[176])
```

`fib(10)` makes 176 calls of itself, each counted; the call from outside is not.

A `def` written in the core text is not a recursion: its body is code over a fixed point the
kernel provides (`unfold`, the folds, `bounded_fix`), and a name it uses is declared before it:

```bc,reject
def twice : i32 => i32 = thunkv fun (x : i32) -> return (inc (inc x))

def inc : i32 => i32 = thunkv fun (x : i32) -> return x

main : F i32 = return (twice i32[0])
-- expect: 1:58: unknown variable `inc`
```

Recursion over data is a **fold**, and a loop that may not terminate is a `delay` (see
[Codata](codata.md)). Each fold is a typing rule, proved sound once, and each always terminates.
A fold is given an **algebra**: what to do with one layer, once the recursive positions have been
replaced by their results.

A fold's shape argument is the body of the `mu` type, written with `X` for the recursive
positions. `X` may occur only as `X` or `ref X`, under `*` and `+`, and not alone.

## Consuming a structure: `fold_own`

`fold_own[F, R] : !(A′ => R) => !((mu X. F) => R)` consumes the structure. The algebra's
argument `A′` is `F` with each recursive position replaced by `R`. Here the list is summed and
freed in one pass:

```bc
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

-- `1 + ref i32 * ref X` with the recursive position replaced by the result `i32`.
def sum_alg : !(1 + ref i32 * i32 => i32) =
  !thunkv fun (r : 1 + ref i32 * i32) ->
    case r {
      inl u -> return i32[0]
    | inr p -> let (c, s) = p; return ((unbang host[add32]) (free[i32] c, s))
    }

def sum : List => i32 = unbang (fold_own[1 + ref i32 * ref X, i32] sum_alg)

main : F i32 = return (sum (cons (i32[100], cons (i32[20], cons (i32[3], nil)))))
-- answer: i32[123]
```

The algebra is handed each head cell `c` and must consume it; here it frees it.

## Reading a structure: `fold_imm`

`fold_imm[F, 'y, @c, R] : !(all 'y < top. A_R => R) => !(all 'y < @c. imm 'y (mu X. F) => R)`
folds over an immutable borrow. The algebra is polymorphic in the borrow's lifetime `'y`, and its
argument `A_R` is `F` with `view 'y` applied to each leaf and `R` at each recursive position: for
the list, `1 + (imm 'y i32 * i32)`. The result `R` must outlive every lifetime, so it cannot
contain a borrow.

```bc
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def plus : i32 * i32 => i32 = unbang host[add32]

def sum_alg : !(all 'y < top. 1 + (imm 'y i32 * i32) => i32) =
  !thunkv Fun 'y < top. return (thunkv fun (r : 1 + (imm 'y i32 * i32)) ->
    case r {
      inl u -> return i32[0]
    | inr p -> let (b, s) = p;
               n <- return (withload['y, 'x, i32, i32] b
                      (thunkv Fun 'x < dom. return (thunkv fun (v : i32) -> return (boxed['x] v))));
               return (plus (n, s))
    })

def sum_list : !(all 'a < top. imm 'a List => i32) =
  fold_imm[1 + (ref i32 * ref X), 'a, top, i32] sum_alg

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

main : F i32 =
  l <- return (cons (i32[100], cons (i32[20], cons (i32[3], nil))));
  r <- return (alloc[List] l);
  q <- return (withbor1['x, List, i32] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x List) ->
            n <- return ((unbang sum_list) ['x] b);
            return (boxed['x] n))));
  let (r2, n) = q;
  return n
-- answer: i32[123]
```

`(unbang sum_list) ['x]` instantiates the fold at the borrow's lifetime. The list and its cell
are still owned by `r2` at the end, and the checker frees them (see
[Implicit destructors](implicit-destructors.md)).

## Updating in place: `fold_reuse`

`fold_reuse[F, R] : !(A″ => R) => !((mu X. F) => R)` consumes the structure like `fold_own`, but
hands the algebra each emptied `ref X` cell as a `ref 1` beside the result, so the algebra can
refill it with `swap` instead of allocating. Its argument `A″` has `ref 1 * R` at each `ref X`.
This maps `+1` over a list in place, under a mutable borrow, and then reads the list back as the
decimal digits of one number:

```bc
type List = mu X. 1 + (ref i32 * ref X)
shape Node = node (leaf i32) (leaf List)

def nil : List = roll (inl ())

def cons : i32 * List => List =
  thunkv fun (p : i32 * List) -> return (roll (inr (alloc_s[Node] p)))

def map_inc_alg : !(1 + ref i32 * (ref 1 * List) => List) =
  !thunkv fun (r : 1 + ref i32 * (ref 1 * List)) ->
    case r {
      inl u -> return (roll (inl u))
    | inr p ->
        let (rn, q) = p;
        cx <- return (swap[i32, 1] rn ());
        let (c, x) = cx;
        cu <- return (swap[1, i32] c ((unbang host[add32]) (x, i32[1])));
        let (c1, u1) = cu;
        let () = u1;
        let (c2, t) = q;
        cu2 <- return (swap[1, List] c2 t);
        let (c3, u2) = cu2;
        let () = u2;
        return (roll (inr (c1, c3)))
    }

def map_inc : List => List = unbang (fold_reuse[1 + ref i32 * ref X, List] map_inc_alg)

def digits_alg : !(1 + ref i32 * i32 => i32) =
  !thunkv fun (r : 1 + ref i32 * i32) ->
    case r {
      inl u -> return i32[0]
    | inr p ->
        let (rn, t) = p;
        return ((unbang host[add32]) (free[i32] rn, (unbang host[mul32]) (t, i32[10])))
    }

def digits : List => i32 = unbang (fold_own[1 + ref i32 * ref X, i32] digits_alg)

main : F i32 =
  l <- return (cons (i32[1], cons (i32[3], cons (i32[5], nil))));
  r <- return (alloc[List] l);
  q <- return (withbor2['x, top, List, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : mut 'x List) ->
            w <- return (withswap['x, List, 1] b (thunkv fun (k : List) -> return (map_inc k, ())));
            let (b2, u) = w;
            let () = u;
            return (boxed['x] ()))));
  let (r2, u) = q;
  let () = u;
  return (digits (free[List] r2))
-- answer: i32[642]
```

The list `[1, 3, 5]` becomes `[2, 4, 6]`, read head last as `642`.

## Current limits

- Folds recurse on the WebAssembly stack, so a very deep structure can overflow it (planned:
  stack-safe lowering, #50).
- Mutually recursive data types are not yet exercised (#32).
