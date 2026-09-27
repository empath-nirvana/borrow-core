# Implicit destructors

Types stay linear, but a program does not have to free every value by hand. Where an owned value
goes unused, the checker inserts a call of its **destructor**, and that call is the value's one
use. The program the checker returns is still an ordinary linear program, so the leak-freedom
theorem applies to it unchanged.

```bc
main : F i32 =
  r <- return (alloc[i32] i32[1]);
  s <- return (alloc[i32] i32[41]);
  x <- return (free[i32] s);
  return x
-- answer: i32[41]
```

`r` is never used, so the checker frees it before `main` returns: `live 0`.

## Which types have a destructor

| type | destructor |
|---|---|
| persistent types, `imm 'a A`, `mut 'a A` | nothing: they are discarded |
| `ref A` | `free`, then the destructor of `A` |
| `A * B`, `A + B`, `box 'a A` | the destructors of the parts |
| a `mu` type that a fold can traverse | a `fold_own` that destroys each layer |
| `U (C & F 1)` | `close`: force it and run `.2` |
| `U (stream A)`, `U (delay A)`, `U (iter A R R')` | `close`, then the destructor of the residual |

A thunk of any other type has no destructor: disposing of it means running it, which has effects
and may need an argument. Such a value must be used, and leaving it unused is an error that names
its type:

```bc,reject
main : F 1 =
  k <- return (thunk (return i32[1]));
  return ()
-- expect: 2:3: `k` is not consumed in its scope, and its type `U (F i32)` has no destructor
```

## Where the call goes

- **At the end of the path.** The destructor calls go just before the path's last computation
  (a `return`, a `force`, a call, a projection), after every effect of the path. A value never
  used is dropped at the end of its binder's scope.
- **Most recently bound first.**
- **Per branch.** A `case` arm or a `<M, N>` component that does not use a value drops it; one
  that does, does not. A value with no destructor must be used in every arm or in none:

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

A drop is never moved earlier than the end of the path. Closing codata runs code, so moving the
call would reorder effects.

## Opting out: `linear`

`linear x <- M; N` declares that `x` must be used explicitly. It is for values whose silent
destruction is a bug, such as a transaction that must be committed or aborted.

```bc,reject
main : F 1 =
  linear r <- return (alloc[i32] i32[1]);
  return ()
-- expect: 2:10: `r` is declared `linear` and is not consumed in its scope
```

## Current limits

- Only variables bound by `<-`, `let`, a `case` arm or `fun` are dropped. Inside a value (`run M`,
  `thunk M`, the scrutinee of a `case`), a variable consumed on one path must be consumed on
  every path.
- `linear` is available on `<-` binders only.
- Externs are never dropped.

`SPEC.md` §12 is the specification of this feature.
