# Introduction

borrow-core is the core of a systems language: linear ownership with Rust-style borrowing, in a
call-by-push-value calculus, with a compiler to WebAssembly. It starts from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(OOPSLA 2025), whose calculus and logic are the baseline of the specification,
[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md).

This book has two halves. **The language** teaches the syntax that `bcc` accepts today, one
feature per chapter, with programs you can run. **The reference** states the syntax, the
constants and their types, and the checker's errors. The last part says what is proved about the
language and how the project is run.

The early chapters use the *core* syntax: call-by-push-value written out in full, where every
bind, `force`, `return` and thunk is on the page. It is verbose on purpose, because each form is
one typing rule. The later chapters (divergence, generators, effects) also use the surface
syntax, which elaborates into core before checking (`bcc desugar` prints the result). The surface
is draft 0 of [`docs/surface-cbpv.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/surface-cbpv.md),
still growing (#54), and its spellings are provisional.

## What the language has

- **Ownership and borrowing.** Owned cells, immutable and mutable borrows with lexical
  lifetimes, and reborrowing.
- **Call-by-push-value.** Value types and computation types are kept apart, so thunks, codata and
  the cost of suspending a computation are explicit.
- **An exponential `!A`** for values that hold no resource, so code can be stored and shared.
- **Blocks and family borrows.** Unboxed structs whose fields are separate places, borrowed
  together at one lifetime.
- **Recursive types and folds.** `mu` types, with borrowed, owned and in-place folds as typing
  rules.
- **Codata.** One former, `nu X. C`, with coiteration. Loops that may not terminate (`delay`),
  streams and finite iterators are abbreviations over it, and each has a mandatory `close`.
- **Integers.** `i32`, `i64` and the byte `u8`, with WebAssembly's operations.
- **Arrays and slices.** `array A`, a run of `n` places with `n` known at run time, with
  bounds-checked access and views of single elements; slice borrows lend part of an array, split
  it, and replace or swap its elements.
- **Implicit destructors.** An owned value that a program leaves unused is freed or closed by a
  destructor that the checker inserts.
- **Standard I/O.** `stdin`, `stdout` and `stderr` are linear capabilities, used through `mut`
  borrows; their operations are externs, compiled to WASI.
- **Divergence as an effect.** A function that may loop without bound has a loop in its type.
  This is inferred, and `total def` asserts that a function terminates.
- **Generators.** `gen fn` with `yield`, consumed by `for`, with adapters in `lib/adapters.bc`.
- **Counted loops and `for`.** Loops over a count, with an early exit, and `for` over counts,
  arrays, views and iterators.
- **Buffers, text and literals.** A growable `buf A`, UTF-8 strings and text views, and string
  literals.
- **Effects and handlers.** In the surface, `effect`, `handler` and `with` for operations that
  answer, and `Fail` for errors, both defined by elaboration into core (SPEC §18). In the kernel,
  handlers that capture the continuation, unwinding through borrows, and cancelling a stored
  continuation (SPEC §19); these are not yet reachable from the surface (#188).

There is no direct recursion: a function cannot call itself, and recursion is written with folds,
codata and loops. Making recursion an effect, a `rec` operation run by a driver, is decided
(decision 24) but not implemented.

## What is proved, and what is trusted

All in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

- Every typing rule is sound in a logical relation (the Fundamental Property), the kernel's
  effect handlers included.
- Every run of a closed well-typed program whose result holds no resource, under every
  allocator, is safe and continues to its result with memory empty: no use after free, no double
  free, no leak (adequacy). A program that performs an operation no handler handles is not
  typed at a pure result `F A`.
- A closed program whose type has no loop terminates on every run (totality).
- When `bcc check` accepts a program, it has built a proof of the typing judgment for it, so the
  theorems above apply to that program.
- Every theorem holds for every implementation of the integer operations, and the I/O theorems
  for every implementation of the externs that meets their contracts.

The compiler from checked programs to WebAssembly, including its lowering of handlers, is tested,
not yet proved: every program in `corpus/`, every kernel program and every runnable example in
this book gives the same answer compiled as in the Lean interpreter, and ends with no live
objects. The allocator, the WAT printer and wasmtime are trusted. [What is proved](proved.md) has
the details.

## How this book is tested

Every program in this book is checked by the gate, `scripts/ci-local.sh`. A block marked `bc` is
checked by `bcc check`, run by the interpreter and by the compiled WebAssembly, and its output is
compared with the `-- answer:` line in the block. Blocks that show errors are rejected by the
checker with exactly the message on their `-- expect:` line. See [Contributing](contributing.md#doc-tests).
