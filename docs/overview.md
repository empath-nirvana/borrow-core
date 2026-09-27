# Overview

borrow-core is the core of a systems language: linear ownership with Rust-style borrowing, in a
call-by-push-value calculus, with a compiler to WebAssembly. It starts from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(OOPSLA 2025), whose calculus (BoCa) and logic (BoLo) are the baseline (`SPEC.md` §1).

## What the language has

- **Ownership and borrowing:** owned references, immutable and mutable borrows with lexical
  lifetimes, reborrowing, and the paper's borrow constructs (`SPEC.md` §1).
- **An exponential `!T`** for values holding no resource, so code can be borrowed and closures
  shaped like Rust's `Fn`/`FnMut` are expressible (§2).
- **Call-by-push-value:** value types and computation types kept apart, so thunks, codata and
  the cost of reification are explicit (§3).
- **Blocks and family borrows:** unboxed structs whose fields are separate places, borrowed
  together at one lifetime (§5).
- **Recursive types and folds:** `μ` with borrowed, owned and in-place folds as typing rules (§6).
- **Codata:** one former `νX. C` with coiteration; the delay type for loops that may not
  terminate, streams and finite iterators are abbreviations over it, each with a mandatory
  `close` (§7).
- **Integers:** `i32`/`i64` with Wasm's operations (§8).
- **Arrays:** `[L]`, the run-time family of leaf places; `array A` owns `n` cells, borrowed in a
  cell and read through the family of leaf views (§9).
- **Persistent variables:** values holding no resource are copied and dropped freely (§10).

Specified but not yet implemented: externs and stdio (§11).

## What is proved

All in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

- **Fundamental Property:** every typing rule is sound in the logical relation (`fundamentalC`).
- **Adequacy:** a closed well-typed program runs to its result and leaves memory empty: no
  use-after-free, no double free, no leak (`adequacyC`). Loops that may not terminate are
  covered observation by observation: observed any number of times and then closed, they leave
  memory empty.
- **Checker soundness:** when `bcc check` accepts a program, it returns a proof of the typing
  judgment for it (`checkProgram_sound`), so the two theorems above apply to it.
- **Parametric arithmetic:** every theorem holds for every implementation of the integer
  operations, so nothing about arithmetic is assumed.

## What is trusted, and what is tested

- **The compiler is tested, not yet proved.** Every corpus program gives the same answer compiled
  as in the Lean interpreter, and ends with no live objects (`scripts/compile-corpus.sh`).
- **The allocator** is trusted against its written spec (`Backend/README.md`).
- **The WAT printer and wasmtime** are trusted.

The plan for proving the compiler is issue "Verification plan for the backend".
