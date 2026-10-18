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

The surface's recursion (a function that calls itself, its drivers `bounded` and `deep`, and
layers) is in [Data and generics](../guide/data.md#recursion). In the core, a recursive group is
the bounded fixed point of its *generator*: the record of the members' bodies, each call of the
group a call of the self-reference. `bounded` is the kernel's `bounded_fix` at a budget of depth,
whose end performs `Exhausted`; `deep` is a machine whose pending calls are frames in a growable
buffer (SPEC §20, §21). `bcc check` reports the generator and each copy.

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
