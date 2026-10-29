# borrow-core

borrow-core is a systems language for people who like Rust's ownership model and want a simpler
story for everything else. You own values and borrow them with `&` and `&mut`, as in Rust. There
is no garbage collector and no hidden reference counting: you write the allocations, and the
compiler inserts the frees.

Errors, I/O, generators and async are all built on one feature, *effects*: an operation you call
like a function, whose meaning is supplied by a `with` block further up. So there's no `Result`
to thread by hand, no `?`, and no separate `async` world: a function that can fail or wait is
called like any other. Handlers compile to plain calls, branches and state machines, and programs
compile to WebAssembly or, through LLVM, to native code.

## A taste

```
include fail
include textio

-- A port number must be between 1 and 65535.
fn check_port(p: i32) -> i32 with Fail[i32] =
  if p < 1 || p > 65535 { raise(p) } else { p }

-- The caller decides what a failure means: here, fall back to 8080.
fn port_or_default(p: i32) -> i32 =
  with default(8080) { check_port(p) }

main -> 1 =
  print_dec(port_or_default(443)); print_byte(b'\n');
  print_dec(port_or_default(99999)); print_byte(b'\n')
```

```text
$ bcc run port.bc
443
8080
()
live 0
```

The last two lines are from `bcc`: the value `main` returned, and `live 0`, the number of
allocations still alive at exit.

`raise` is an ordinary operation, and `with default(8080) { … }` is the handler that decides what
it means. Another caller could turn the same failure into a value with `to_result`, or let it
pass upward. [Effects and handlers](book/src/guide/effects.md#computation-parameters-and-) has a
longer example: a generic `retry` with backoff, tested against a fake timer.

## What it can do

- **Ownership and borrowing** as in Rust: values move, `&` and `&mut` lend them, and lifetimes
  appear in signatures. Nothing is copied behind your back: copying a list is written `clone(xs)`. → [Ownership and borrows](book/src/guide/ownership.md)
- **Data types** with records, variants, generics and pattern matching. Recursive data, nested
  as deep as you like (a tree whose children are a `Vec` of trees needs no `box`), and every
  allocation is one you wrote. Folds walk it by borrow, in place, or by consuming it.
  → [Data and generics](book/src/guide/data.md)
- **Errors** as `raise` and handlers. A function's effects are inferred, so nothing is annotated
  along the way, and an unhandled error is a compile-time error. → [Errors](book/src/guide/errors.md)
- **I/O as effects.** A function's type says what I/O it can do, and a test can swap in a fake
  stdout, clock or input. → [Input and output](book/src/guide/io.md)
- **Iteration**: `for` over ranges, arrays and generators, `yield`, adapters and `|>` pipelines
  that allocate nothing. The compiler knows which functions might loop forever, and `total fn`
  asks it to prove one doesn't.
  → [Iteration](book/src/guide/iteration.md)
- **Your own effects and handlers**, with state, several instances, and handlers that compile
  away. → [Effects and handlers](book/src/guide/effects.md)
- **Async without a separate async world**: `await` is an ordinary call, the scheduler is
  library code, and one `map` works for both plain and async callbacks. A task can borrow its own
  data across `await` without `Pin`. → [Async tasks](book/src/guide/async.md)
- **No garbage collector and no hidden allocation.** Values are freed when their owner is done
  with them, handlers compile to plain calls and branches, and programs allocate where the C or
  Rust version would. [`bench/`](bench) compares them.

For larger programs, see the Advent of Code and LeetCode ports in [`corpus/aoc/`](corpus/aoc)
and [`corpus/leetcode/`](corpus/leetcode).

## Getting started

You need [elan](https://github.com/leanprover/elan), which fetches the pinned Lean toolchain,
and [wasmtime](https://wasmtime.dev). On macOS, `brew bundle` installs both. Native builds also
need clang.

```sh
git clone https://github.com/empath-nirvana/borrow-core && cd borrow-core
lake exe cache get      # prebuilt Mathlib
lake build bcc          # the compiler, at .lake/build/bin/bcc
```

Write `hello.bc`:

```
include textio

main -> 1 =
  print_lit("Hello, world!\n")
```

and run it:

```text
$ bcc run hello.bc
Hello, world!
()
live 0
```

| command | what it does |
|---|---|
| `bcc run file.bc [args…]` | compile to WebAssembly and run under wasmtime |
| `bcc run --native file.bc` | compile through LLVM and run natively |
| `bcc interp file.bc` | run in the reference interpreter |
| `bcc compile file.bc -o out.wat` | write the WebAssembly text |
| `bcc compile --target native file.bc -o out.ll` | write the LLVM IR |

The [book](https://empath-nirvana.github.io/borrow-core/) teaches the language from there, starting
with [Getting started](https://empath-nirvana.github.io/borrow-core/getting-started.html), and has
[Recipes](book/src/recipes.md), a [Language reference](book/src/language-reference.md) and the
[Standard library](book/src/stdlib.md).
`mdbook serve book` builds it locally.

## Status

The language is young and still changing. The [Status](book/src/status.md) page lists what works
and what isn't built yet.

## Built on a proof

borrow-core started as a Lean formalisation of the paper *From Linearity to Borrowing* (Wagner,
Gierczak, Marshall, Li and Ahmed, OOPSLA 2025), and its safety rules are proved in Lean: a
program that compiles can't use memory after freeing it, free it twice or leak it.
[Safety guarantees](book/src/safety.md) says what that means for your programs, and
[`SPEC.md`](SPEC.md) is the precise definition.

## Contributing

Contributors start at [`docs/internals/`](docs/internals) (the core calculus, how the surface
elaborates into it, the proofs and the working rules) and [`SPEC.md`](SPEC.md).
