# How it elaborates

Everything in the guide is *sugar*: before checking, the front end rewrites a surface program into
the **core** language, and the checker, the proofs and the compiler only ever see the core. The
core is small, each of its forms is one typing rule, and the theorems of [What is
proved](../proved.md) are about it. A surface feature adds nothing to the trusted base: a wrong
elaboration could give a program another meaning than intended, but what it produces is still
checked, so it cannot make a program unsafe.

`bcc desugar file.bc` prints the core program that a surface program stands for:

```bc
fn double(x: i32) -> i32 = x + x

main -> i32 =
  let c = alloc(20);
  let n = borrow imm c { b -> *b };
  double(n) + free(c) - 18
-- answer: i32[42]
```

```text
$ bcc desugar double.bc
def double : !(i32 => i32) =
  !thunkv fun (io_p0 : i32) ->
      x <- return io_p0;
      return (unbang host[add32]) (x, x)

main : F i32 =
  c <- return alloc[i32] i32[20];
  io_b2 <- return withbor1['io_l1, i32, i32] c (thunkv Fun 'io_l1 < dom.
        return (thunkv fun (b : imm 'io_l1 i32) ->
            io_bx <- return withload['io_l1, 'io_ly5_31, i32, i32] b (thunkv Fun 'io_ly5_31 < dom.
                  return (thunkv fun (io_dv : view 'io_ly5_31 i32) ->
                      return boxed['io_ly5_31] io_dv));
            return boxed['io_l1] io_bx));
  let (c, n) = io_b2;
  return (unbang host[sub32]) ((unbang host[add32]) ((unbang double) n, free[i32] c), i32[18])
```

The names starting `io_` are the elaboration's own. `bcc check` also prints what the elaboration
decided where it is not visible in the text: each function's row, which copy of a function a call
reaches, which handler an operation goes to, and how each handler is lowered.

The core can be written directly, and the chapters of this part do so, one feature each. A core
program and a surface program are the same file format; most programs mix the two only through
the library.

## Call-by-push-value, in brief

The core is a **call-by-push-value** (CBPV) calculus. It keeps two kinds of thing apart that most
languages blur:

- A **value** is data: `()`, a pair, `inl v`, an integer, a cell, a borrow. Its type is a
  **value type** (`1`, `A * B`, `A + B`, `i32`, `ref A`, `imm 'a A`).
- A **computation** is something that runs: `return v`, a function, a sequence of steps. Its type
  is a **computation type**. `F A` is a computation that returns an `A` (the surface's `-> A`),
  and `A -o C` a function that takes an `A` and continues as `C`.

The two are connected by two operations. `thunk M` suspends a computation as a value, of type
`U C`, which can be stored and passed; `force t` runs it. `x <- M; N` runs `M`, binds its result,
and continues with `N`. So a surface function `fn f(x: A) -> B` is the value `U (A -o F B)`,
written `A => B`, and a call is a `force` and an application. Making suspension explicit is what
lets the compiler see every closure, every loop's state and every continuation as data with a
known type, and what lets the type system say which values hold resources.

`!A` is a value that holds no resource, so it can be copied and dropped: the surface's `!(A =>
B)` closures. `ref A` is an owned heap cell, and `imm 'a A`, `mut 'a A` its borrows, lent by the
constants `withbor1`, `withbor2` and `withbor3` to a callback that runs within the lifetime `'a`.
The [glossary](../../glossary.md) has the rest of the vocabulary.

## What each surface form becomes

| surface | core |
|---|---|
| `fn f(x: A) -> B = e` | `def f : !(A => B) = !thunkv fun (x : A) -> …` |
| `let x = e; …` | `x <- return e; …`, or `x <- M; …` when `e` is a call |
| `if`, `match` | `case` on a sum |
| `+`, `<`, … at an integer | `(unbang host[add32]) (a, b)`, … |
| `&x`, `&mut x`, `borrow imm x { … }` | `withbor1`, `withbor2` around a callback; `x` rebound after |
| `*r` | `withload` |
| `let mut`, assignment | rebinding (SSA form) |
| an unused owned value | a destructor call the checker inserts |
| `for` over data | `count_fold` / `count_try`, the counted-loop constants |
| `while`, `loop` | a `delay`: codata driven one step at a time |
| a generator, a stored generator | a handler of `Yield`; codata `pull A B R` |
| an answering handler | a capability: a `mut` borrow of its state, and a function per clause |
| a control handler, `raise`, `await` | the kernel's `handle_with`, `perform`, `abort` (SPEC §19) |
| recursion | `bounded_fix` of a generator, or the `deep` machine |
| `poly` families, generics | one copy per type, chosen at compile time |

## The chapters

- [Values and computations](values-and-computations.md): CBPV's terms, thunks, functions, `!A`.
- [Cells and borrows](ownership-and-borrows.md): `alloc`, `swap`, `withbor`, lifetimes, `'main`.
- [Blocks and families](blocks-and-families.md): structs as blocks of cells, borrowed together.
- [Recursive data and folds](recursive-data.md): `mu` types and the three folds.
- [Codata](codata.md): `nu X. C`, streams, iterators and `delay`.
- [Integers and host operations](integers.md): the `host[…]` instructions.
- [Arrays](arrays.md): `array A`, its families of views.
- [Implicit destructors](implicit-destructors.md): where the checker inserts frees and closes.
- [Standard I/O as capabilities](standard-io.md): the streams as cells, and the `for` over input.
- [Divergence](divergence.md): loops in types, `div_fuel`, borrows around a loop.
