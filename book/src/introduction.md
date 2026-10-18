# Introduction

borrow-core is a systems language with ownership and Rust-style borrowing, compiled to
WebAssembly. Its borrow calculus is mechanised in Lean, starting from the mechanization of
Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing* (OOPSLA 2025), and the
checker that accepts a program builds a proof that it is well typed. Its specification is
[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md).

```bc
include textio

fn greet(n: i32) -> 1 =
  print_lit("hello, ");
  print_dec(n);
  print_byte(b'\n')

main -> i32 = greet(42); 0
-- output: hello, 42
-- answer: i32[0]
```

## What it is for

The language is built around a few commitments. Each is either built, or built in part; the
[Status](status.md) page says which.

- **One mechanism for effects.** Errors, input and output, iteration, async tasks and recursion's
  depth limit are all *effects*: sets of operations, called like functions and given their
  meaning by handlers. `raise` is an operation, a generator is a function that performs `yield`,
  `await` is an operation, and standard output is an effect that `main` is given. There is no
  `Result` threaded by hand, no `?`, no separate exception system, no separate iterator protocol.
  Allocation is meant to be one more (the heap as its outermost handler, arenas as handlers inside
  it); today it is a primitive and is not tracked in types (SPEC §35).
- **No colored functions.** A function that raises, waits or writes is called like any other. Its
  row, the effects it performs, is inferred, and the handler around the call serves them. A
  higher-order function such as `map` is written once and serves a pure callback, a failing one
  and an awaiting one alike.
- **Handlers are compiled away.** There is no handler stack and no run-time search. An operation
  that answers at once is a direct call of its clause; an operation that never returns, such as
  `raise`, is a branch after each call that may perform it; a computation that suspends, a task or
  a generator, is a state machine, as Rust compiles `async fn`. Each operation is resolved to its
  handler at compile time.
- **No garbage collector, and allocation where Rust or C would allocate.** Owned values are freed
  when their owner is done with them, by destructors the compiler inserts, and nothing is
  reference counted. A borrow of a local and the state of an answering handler are slots in
  the stack frame, and the corpus counts every allocation, indirect call and copy against what a C or
  Rust program would do.
- **Verified foundations.** The typing rules are proved sound in Lean: every run of a closed
  well-typed program is safe and leaves memory empty (no use after free, no double free, no
  leak), and code whose type has no loop terminates. A program that performs an operation no
  handler handles is not well typed. [What is proved](proved.md) states each theorem and what is
  trusted instead of proved: the compiler is tested, not yet verified.

## What is not built yet

The language is young. Among what a working program will miss: `struct`/`enum`-style data
declarations (types are written with pairs, sums and `mu`), modules, traits or bounds on type
parameters, bitwise operators, files and the network, threads, and an event loop for async I/O.
Some programs that should be accepted are refused, and some error messages describe the
elaborated program rather than the one you wrote; each known case has an issue. The
[Status](status.md) page lists all of it, with the SPEC section or issue for each. Spellings
throughout are provisional.

## How this book is organised

- **The language** teaches the surface language in the order a programmer meets it: values and
  functions, ownership, data and generics, errors, input and output, iteration, effects, async.
  Every example is a program `bcc` runs.
- **How it elaborates** shows the *core* the surface is translated into before checking: a
  call-by-push-value calculus in which every bind, thunk and borrow is written out. It is for
  readers who want to see what a program means to the checker and the proofs, and it is where
  the calculus is explained.
- **The reference** states the core syntax, the constants and their types, and the checker's
  errors.
- **About the project** has the status page, the theorems, how to contribute, the design
  decisions and a glossary.

## How this book is tested

Every program in this book is checked by the gate, `scripts/ci-local.sh`. A block marked `bc` is
checked by `bcc check`, run by the compiled WebAssembly, and its output is compared with the
`-- answer:` line in the block, the interpreter's output (checked again by the interpreter
whenever the block changes, and by `make gate-full`). Blocks that show errors are rejected by the
checker with exactly the message on their `-- expect:` line. See [Contributing](contributing.md#doc-tests).
