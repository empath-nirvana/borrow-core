# Properties worth proving

A list of candidate properties for the language, grouped by what they buy. Nothing here is
decided; entries move into `SPEC.md` only through a spec entry. Status is as of 2026-09-25;
"✓" means machine-checked in this repository (library or `experiments/`).

## Usefulness

These are shown by exhibiting programs as much as by theorems. They are the standing check on
every other entry.

| # | Property | Statement | Status |
|---|---|---|---|
| U1 | A corpus that runs | A fixed set of programs typechecks, runs, and has an adequacy instance: linked list, growable vector, hash map, the iterator adapters, a parser, file I/O, an arena allocator, an index-based graph, string processing. | Small examples only (`Examples/`, experiment programs). |
| U2 | Loops and recursion | Programs can loop. | Missing: every program terminates; there is no `μ`/`ν` and no divergence capability. Blocks U1. |
| U3 | A Rust fragment embeds | Every program the Rust borrow checker accepts in a named fragment of safe Rust translates to a typed program here; known gaps (NLL-only programs, `unsafe` internals) are listed. | Open. |
| U4 | Rust's `unsafe` staples are safe | `split_at_mut`, `IterMut`, index-based mutation while iterating. | Static-length `split_at_mut` ✓ (`experiments/Places`). |
| U5 | Talks to the world | FFI to libc: files, allocation, output. | Later; needs K3. |
| U6 | Performance | Compiled benchmarks within a small factor of C/Rust. | Empirical; needs K1. |
| U7 | Writes itself | A parser and interpreter for the language, written in it. | Long-term. |

## Foundations

| # | Property | Statement | Status |
|---|---|---|---|
| F1 | Fundamental Property | Well-typed implies semantically typed. | ✓ |
| F2 | Adequacy | A closed program at `1` terminates and leaves memory empty. | ✓ |
| F3 | Conservative extension | Each extension preserves the meaning of every baseline program. | Open (`SPEC.md` §2 Open). |
| F4 | Divergence as a capability | Without the capability, programs terminate; with it, safety holds (step-indexed) and leak freedom holds on terminating runs. | Open; a second model. Pairs with U2. |

## Cost and reification

The aim is a cost model readable from types: shifts mark where reification can happen, and
escape, unknown code and multi-shot resumption decide whether it does.

| # | Property | Statement | Difficulty |
|---|---|---|---|
| C1 | Guaranteed deforestation | A linear iterator chain whose shifts cancel reduces to the fused loop, with no `F` of an intermediate. Linearity is the precondition of Wadler's theorem. | Medium; CBPV core. |
| C2 | Shift cancellation | A `↓` over known `!` code that does not escape leaves no closure at runtime. | Medium. |
| C3 | Reuse | When a linear consumer must realize an intermediate, the output occupies the consumed places; allocations do not exceed the unfused program's. | Medium; needs leaf places. |
| C4 | Stack discipline | Anything whose type does not outlive its scope is allocated and freed in LIFO order. | Medium. |
| C5 | Handler elimination | A tail-resumptive handler is equivalent to a direct call. | Medium. |
| C6 | One-shot continuations | Linear continuations need no copying and are implementable by stack switching. | Hard; needs a target model. |
| C7 | Borrows are free | Borrow constructs erase to pointer passing; lifetimes have no runtime content. | Easy to medium. |
| C8 | `pack`/`unpack` are free | A struct handle and its leaf family are the same at runtime. | Easy, once leaf places exist. |
| C9 | Types predict allocation | A type-level criterion for when a program allocates, proved sound. | Hard; collects C1–C8. |

## Borrowing and places

| # | Property | Statement | Status |
|---|---|---|---|
| P1 | Disjoint places | Borrows of disjoint places compose at one lifetime. | ✓ derived (`experiments/Places`). |
| P2 | Same-lifetime views through pointers | `Imm` projection through a `Ref`. | Scoped (`docs/scope-deep-freeze.md`); `six38_img` decides it. |
| P3 | Borrowing is capability passing | A program using borrows is equivalent to its linear capability-passing translation (the motivation of [CONF] Fig. 10). | Medium to hard. |
| P4 | Lifetime parametricity | A function polymorphic in `'a` cannot leak an `'a` borrow. | Hard. |
| P5 | `noalias` | `Mut` borrows justify LLVM `noalias`. | Hard; target side. |
| P6 | Variants | Borrowing a payload place is sound while the tag is fixed. | Open design question. |

## Compilation

| # | Property | Statement | Difficulty |
|---|---|---|---|
| K1 | Layout correctness | Places → layout → Wasm, as a simulation (CompCertO `injp`-style) preserving F1 and F2. | Hard. |
| K2 | Leak freedom at the target | Compiled code does not leak. | From K1 and F2. |
| K3 | Linking | Typed code links with foreign code that meets its semantic type (a realizability model). | Hard. |
| K4 | Moves are cheap | Ownership transfer compiles to nothing or a copy of the leaves. | Easy to medium. |

## Effects, grades and modes

| # | Property | Statement | Difficulty |
|---|---|---|---|
| E1 | Effect safety | Handled effects do not escape their handler. | Medium. |
| E2 | Grades | Graded use `□_r T` gives sound upper bounds; `!T` is the ω case. | Medium to hard. |
| E3 | Staging | Values at the compile-time mode are fully evaluated before runtime. | Hard. |
| E4 | Race freedom | With concurrency, `Mut` exclusivity rules out data races. | Later. |

## Suggested order

1. U2: recursion, which unblocks U1.
2. U1: the corpus, kept running from then on.
3. C7 and C8.
4. C1 or P3 as the first headline theorem.
