# Introduction

borrow-core is the core of a systems language: linear ownership with Rust-style borrowing, in a
call-by-push-value calculus, with a compiler to WebAssembly. It starts from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(OOPSLA 2025), whose calculus and logic are the baseline of the specification,
[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md).

This book has two halves. **The language** teaches the core syntax that `bcc` accepts today,
one feature per chapter, with programs you can run. **The reference** states the syntax, the
constants and their types, and the checker's errors. The last part says what is proved about the
language and how the project is run.

The syntax in this book is the *core* syntax: call-by-push-value written out in full, where every
bind, `force`, `return` and thunk is on the page. It is verbose on purpose, because each form is
one typing rule. A more pleasant surface syntax that desugars to it is being designed
(planned: [`docs/surface-cbpv.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/surface-cbpv.md), #54).

## What the language has

- **Ownership and borrowing.** Owned cells, immutable and mutable borrows with lexical
  lifetimes, and reborrowing.
- **Call-by-push-value.** Value types and computation types are kept apart, so thunks, codata and
  the cost of suspending a computation are explicit.
- **An exponential `!A`** for values that hold no resource, so code can be stored and shared.
- **Blocks and family borrows.** Unboxed structs whose fields are separate places, borrowed
  together at one lifetime.
- **Recursive types and folds.** `mu` types, with borrowed, owned and in-place folds as typing
  rules. There is no direct recursion.
- **Codata.** One former, `nu X. C`, with coiteration. Loops that may not terminate (`delay`),
  streams and finite iterators are abbreviations over it, and each has a mandatory `close`.
- **Integers.** `i32` and `i64` with WebAssembly's operations.
- **Arrays.** `array A`, a run of `n` places with `n` known at run time, with bounds-checked
  access and views of single elements.
- **Implicit destructors.** An owned value that a program leaves unused is freed or closed by a
  destructor that the checker inserts.

Externs with standard input and output (`SPEC.md` §11) are specified but not implemented; a
growable `Vec` and strings are planned as library code over arrays.

## What is proved, and what is trusted

All in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

- Every typing rule is sound in a logical relation (the Fundamental Property).
- A closed well-typed program runs to its result and leaves memory empty: no use after free, no
  double free, no leak (adequacy).
- When `bcc check` accepts a program, it has built a proof of the typing judgment for it, so the
  two theorems above apply to that program.
- Every theorem holds for every implementation of the integer operations.

The compiler from checked programs to WebAssembly is tested, not yet proved: every program in
`corpus/` and every runnable example in this book gives the same answer compiled as in the Lean
interpreter, and ends with no live objects. The allocator, the WAT printer and wasmtime are
trusted. [What is proved](proved.md) has the details.

## How this book is tested

Every program in this book is checked by CI. A block marked `bc` is checked by `bcc check`, run
by the interpreter and by the compiled WebAssembly, and its output is compared with the
`-- answer:` line in the block. Blocks that show errors are rejected by the checker with exactly
the message on their `-- expect:` line. See [Contributing](contributing.md#doc-tests).
