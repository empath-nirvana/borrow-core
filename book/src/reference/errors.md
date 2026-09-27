# Checker errors

`bcc` reports the first error it finds, as `file:line:column: message`. Parse errors come from
`bcc parse` and every later command; type errors from `bcc check` and every command that runs a
program. This chapter lists the errors by kind, with a program for each common one. The line and
column in each `-- expect:` line count from the first line of its example.

## Parse errors

The parser rejects programs outside the grammar before any checking. Examples, from
`corpus/fail/`:

| program | error |
|---|---|
| `main : F 1 = force f (g x)` | ``expected a declaration (`type`, `shape`, `def`, `extern` or `main`), found `(` `` (application takes variables only) |
| `main : F 1 = return (); return ()` | ``expected a declaration …, found `;` `` (no free-standing sequencing) |
| `def f : 1 => 1 = fun (x : 1) -> return x` | ``expected a value, found `fun` `` (a function value is `thunkv fun …`) |
| `def t : 1 = ((), (), ())` | ``expected `)`, found `,` `` (tuples are pairs) |
| `main : 1 + 1 = return (inl ())` | this is a value type, but a computation type is expected here |
| `type T = F A * B` | `` `F A` is a computation type, but a value type is expected here `` |
| `main : F 1 = case v { inr y -> return y \| inl x -> return x }` | ``expected `inl`, found `inr` `` |

## Linearity

**Used twice.** A variable whose type is not persistent is used more than once.

```bc,reject
main : F (i32 * i32) =
  r <- return (alloc[i32] i32[1]);
  return (free[i32] r, free[i32] r)
-- expect: 3:10: `r` is used twice here, and its type `ref i32` is not persistent
```

**Not consumed.** A variable is left unused and cannot be dropped: its type has no destructor,
it is declared `linear`, or it cannot be dropped where its scope ends (inside a value, where no
drop is inserted).

```bc,reject
main : F 1 =
  k <- return (thunk (return i32[1]));
  return ()
-- expect: 2:3: `k` is not consumed in its scope, and its type `U (F i32)` has no destructor
```

**Unbalanced arms.** The arms of a `case`, or the components of `<M, N>`, consume different
variables, and one of them has no destructor.

```bc,reject
main : F i32 =
  k <- return (thunk (return i32[1]));
  c <- return (inl () : 1 + 1);
  case c {
    inl u -> force k
  | inr u -> return i32[2]
  }
-- expect: 4:3: in this `case`, `k` is consumed in the `inl` arm but not in the `inr` arm, and its type `U (F i32)` has no destructor
```

**Promotion.** `!thunk` and `!thunkv` build a value that holds no resource, so their body may use
only `!`-typed variables.

```bc,reject
main : F i32 =
  r <- return (alloc[i32] i32[1]);
  g <- return (!thunk (return (free[i32] r)));
  return i32[0]
-- expect: 3:16: `!thunk` promotes only over `!` types, but `r`, of type `ref i32`, is used inside
```

**Externs.** `main` must consume every extern whose type is not persistent.

## Lifetimes

**A box that does not outlive its lifetime.** `boxed['x] V` needs everything `V` uses to outlive
`'x`. This is the error for a borrow that would escape its callback.

```bc,reject
main : F 1 =
  r <- return (alloc[i32] i32[1]);
  q <- return (withbor1['x, i32, 1 => 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x i32) ->
            return (boxed['x] (thunkv fun (u : 1) -> return (forget_imm['x, i32] b))))));
  return ()
-- expect: 5:21: `boxed['x]`: `b`, of type `imm 'x i32`, is used inside, and it cannot be shown to outlive `'x`
```

**An entailment the checker cannot show.** `:>`, `shorten` and `[@]` need `⊑` or `⊏` between
lifetimes. Here the borrow is stretched to a longer lifetime:

```bc,reject
main : F 1 =
  r <- return (alloc[i32] i32[1]);
  q <- return (withbor1['x, i32, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x i32) ->
            c <- return (b :> top);
            return (boxed['x] ()))));
  return ()
-- expect: 5:25: cannot show `top` ⊑ `'x` from the lifetime context
```

Other lifetime errors name a binder that is already bound, a lifetime not defined at that point,
or a `Fun 'x` whose body uses a variable whose type mentions `'x`.

## Types

**Mismatch.** A form's type differs from the one expected. Types are compared exactly, with no
α-conversion of lifetime binders (section 3).

```bc,reject
main : F i32 =
  u <- return ();
  return u
-- expect: 3:10: type mismatch: expected `i32`, but this has type `1`
```

**The wrong kind of type for a form.** Each form names what it needs:

```bc,reject
main : F i32 = return ((unbang host[add32]) (i32[1], inl ()))
-- expect: 1:54: `inl V` is checked against `i32`, which is not a `+` type
```

```bc,reject
main : F i32 =
  x <- return i32[1];
  force x
-- expect: 3:3: `force x` needs a `U` type, but `x : i32`
```

```bc,reject
main : F i32 =
  f <- (fun (x : i32) -> return x);
  return i32[0]
-- expect: 2:9: a bound computation must have a type `F A`, but this has type `i32 -o F i32`
```

**`thunk` or `thunkv`.** `thunk M` needs `M : F A`; `thunkv N` needs `N` at any other
computation type, and a literal λ.

```bc,reject
main : F i32 =
  t <- return (thunk (return i32[1]));
  u <- return (thunkv (force t));
  force u
-- expect: 3:16: `thunkv N` needs `N` not of type `F A`, but `N : F i32`; use `thunk`
```

**Names.** A variable or `def` is not in scope. A `def` cannot refer to itself or to a later
`def`.

```bc,reject
def loop : i32 => i32 = thunkv fun (x : i32) -> return (loop x)

main : F i32 = return (loop i32[0])
-- expect: 1:57: unknown variable `loop`
```

**Type restrictions.** A `mu` type must be closed, with its variable not under `mut` and not
inside a computation type.

```bc,reject
type T = mu X. 1 + (i32 => X)

main : F 1 = return ()
-- expect: 1:28: the type variable `X` occurs under `U` (inside a computation type)
```

## Side conditions of constants

Constants and derived forms check their side conditions (section 8 and section 9) and name the
one that fails.

```bc,reject
type T = mu X. 1 + !X
def f : !(T => 1) = fold_own[1 + !X, 1] (!thunkv fun (r : 1 + !1) -> return ())
main : F 1 = return ()
-- expect: 2:21: `!X` is not a fold shape: `X` may occur only as `X`, `ref X`, or under `*` and `+`
```

```bc,reject
shape Pair = node (leaf i32) (leaf i32)

main : F 1 =
  s0 <- return (alloc_s[Pair] (i32[1], i32[2]));
  r <- return (withbor_s_mut[Pair, 'c, 1] s0
         (thunkv Fun 'c < top. return (thunkv fun (m : fam mut 'c Pair) ->
            return (boxed['c] ()))));
  return ()
-- expect: 5:16: a block borrow needs a shape whose leaves are plain (no lifetime, no `U`)
```

Integer leaves are not yet plain (planned: #11).

## Incompleteness

A program can be well typed and still be rejected: the checker does not search for every
derivation. The known cases are listed in `Frontend/README.md` under *Incompleteness*: modes that
need an ascription, types compared without α-conversion, rules that apply only where written,
lifetime entailment without distributivity, and derived forms that cannot drop persistent
variables.
