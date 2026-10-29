# Internals

Pages for contributors and for readers of the proofs, moved out of the book, which teaches the
surface language. [`SPEC.md`](../../SPEC.md) is the precise definition of the language.

- [`contributing.md`](contributing.md): how work is tracked, the definition of done, and the
  hygiene rules.
- [`proved.md`](proved.md): the theorems, where they live in the Lean sources, what is trusted,
  and what is not claimed.
- [`elaboration/`](elaboration/overview.md): how each surface feature elaborates into the core,
  as `bcc desugar` prints it: values and computations, cells and borrows, blocks and families,
  recursive data and folds, codata, integers and host operations, arrays, implicit destructors,
  standard I/O as capabilities, divergence.
- [`reference/`](reference/README.md): the core syntax, a guide to
  [`docs/syntax-core.md`](../syntax-core.md) section by section, and the checker's errors on core
  programs.
- [`docs/decisions.md`](../decisions.md) and [`docs/glossary.md`](../glossary.md): the design
  decisions and the glossary.

The `bc` examples in these pages were doc-tested while they were in the book; they are not run
by `scripts/book-doctest.sh`.
