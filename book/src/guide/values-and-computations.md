# Values and computations

borrow-core is a call-by-push-value language: it has two kinds of type and two kinds of term.

- A **value type** classifies data: `1` (the unit, written `()`), `0` (no values), pairs
  `A * B`, sums `A + B`, integers `i32` and `i64`, cells `ref A`, borrows `imm 'a A` and
  `mut 'a A`, suspended computations `U C`, and `!A`.
- A **computation type** classifies something that runs: `F A` returns an `A`, a function
  `A -o C` takes an `A` and continues as `C`, and a lazy pair `C & D` offers two computations of
  which the caller runs one.

`main` is a computation. A program that returns an `i32` has `main : F i32`.

## Returning and binding

`return V` is the computation that returns the value `V`. `x <- M; N` runs `M`, binds its result
to `x`, and continues with `N`. There is no free-standing sequencing `M; N`: every step binds
a name, and a step that returns `()` is bound and taken apart with `let () = u;`.

```bc
main : F i32 =
  x <- return i32[20];
  y <- return ((unbang host[add32]) (x, x));
  return y
-- answer: i32[40]
```

`x : A <- M; N` annotates the bound variable when the checker cannot work out `M`'s type.

## Thunks

A computation is not a value, so it cannot be stored in a pair or passed to a function as it
is. `thunk M` suspends the computation `M : F A` as a value of type `U (F A)`, and `force t`
runs a thunk `t`.

```bc
main : F i32 =
  t <- return (thunk (return i32[7]));
  force t
-- answer: i32[7]
```

`force` takes a variable, not an expression: bind the thunk first.

A thunk of any other computation type, such as a function, is written `thunkv N`, and `N` must
be a literal function, `Fun`, or `<M, N>`, possibly under `nu_in`, `nu_out` or an ascription
(the forms whose meaning is already a closure; see [Terms](../reference/terms.md)). The checker
says which one to use:

```bc,reject
main : F i32 =
  t <- return (thunk (return i32[1]));
  u <- return (thunkv (force t));
  force u
-- expect: 3:16: `thunkv N` needs `N` not of type `F A`, but `N : F i32`; use `thunk`
```

## Functions

`fun (x : A) -> M` is a computation of type `A -o C` when `M : C`. The binder's type is always
written. A function value is its thunk, `thunkv fun (x : A) -> M`, of type `U (A -o C)`, and
the type `A => B` abbreviates `U (A -o F B)`: a function value that takes an `A` and returns a
`B`.

There are two ways to call a function.

- **At value level**, `V W` applies `V : A => B` to the value `W` and is a value of type `B`.
  This is call by value: `W` is computed first.
- **At computation level**, `M x` applies a computation `M : A -o C` to a *variable* `x`. To
  pass anything else, bind it first. This is A-normal form, and it is why `force f y` below binds
  `y` before the call.

```bc
def double : i32 => i32 =
  thunkv fun (x : i32) -> return ((unbang host[add32]) (x, x))

main : F i32 =
  f <- return (thunkv fun (x : i32) -> return (double x));
  y <- return i32[21];
  force f y
-- answer: i32[42]
```

`def` declares a top-level name. A `def` is a macro: each use is replaced by its body and checked
there, so a `def` can be used any number of times, even when its type is linear.

`run M` goes the other way from `return`: it reads a computation `M : F A` as a value of type
`A`, so a sequence of steps can appear where a value is expected.

```bc
main : F i32 =
  y <- return (run (x <- return i32[20]; return ((unbang host[add32]) (x, x))));
  return y
-- answer: i32[40]
```

## Pairs and sums

`(V, W)` is a pair, and `let (x, y) = V; M` takes one apart. There are no tuples of three or
more: nest pairs, `(a, (b, c))`.

`inl V` and `inr V` inject into a sum `A + B`, and `case` takes one apart. The arms are always
written `inl` first. `inl` and `inr` cannot work out the other half of the sum, so they need an
expected type, given here by an ascription `(V : A)`:

```bc
type B = 1 + 1

main : F i32 =
  p <- return (i32[3], (inr () : B));
  let (n, b) = p;
  case b {
    inl u -> return n
  | inr u -> return ((unbang host[mul32]) (n, n))
  }
-- answer: i32[9]
```

`type B = 1 + 1` is an abbreviation. Booleans are `1 + 1`, with `inr ()` as true.

## Lazy pairs

`<M, N>` is a computation of type `C & D` that offers two computations. The caller picks one with
`.1` or `.2`, and only that one runs. So both components may use the same variables: this is not
duplication, because only one of them happens.

```bc
main : F i32 =
  t <- return (thunkv < return i32[1], return i32[2] >);
  (force t).2
-- answer: i32[2]
```

Lazy pairs are how codata offers its observations: `next` and `close` (see
[Codata](codata.md)).

## The exponential `!A`

A value of type `!A` holds no resource, so it can be copied and dropped freely. `!thunkv N` and
`!thunk M` build one from a computation that uses only `!`-typed variables, and `unbang V` takes
the `A` out. The integer operations and the folds have `!` types: `host[add32]` is
`!(i32 * i32 => i32)`, which is why calls are written `(unbang host[add32]) (x, y)`.

```bc
def double : !(i32 => i32) =
  !thunkv fun (x : i32) -> return ((unbang host[mul32]) (x, i32[2]))

main : F i32 =
  f <- return double;
  return ((unbang f) ((unbang f) i32[5]))
-- answer: i32[20]
```

`f` is used twice. That is allowed because `!(i32 => i32)` is *persistent*: it holds no
resource. The next chapter is about the types that do.
