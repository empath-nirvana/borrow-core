# borrow-core documentation

Start here. For learning the language, read the book: the guide and reference in
[`book/`](../book/src/SUMMARY.md), with doc-tested examples (`mdbook build book`). The pages
below are design and research notes.

| page | what it covers |
|---|---|
| [Overview](overview.md) | what the language is, what is proved, and what is trusted |
| [Pipeline](pipeline.md) | from a `.bc` file to WebAssembly: the `bcc` commands and the scripts |
| [Glossary](glossary.md) | the terms used across the spec, code and docs |
| [Design decisions](decisions.md) | what was chosen, and why |
| [Theory index](theory-index.md) | every experiment and theoretical note: its question, its answer, its Lean names, and the open problems |

## Reference

- [`SPEC.md`](../SPEC.md) — the language, as numbered entries. The authority on what the language
  is; its *Status* section says where each entry is implemented.
- [Core syntax](syntax-core.md) — the textual form the parser and checker accept.
- [Surface syntax](surface-cbpv.md) — draft 0 of the surface: CBPV at the surface, with sugar only
  for shifts that cancel (#54).
- [Typed elaboration](typed-elaboration.md) — how the surface is elaborated to core on inferred
  types, through the typed IR that `bcc tir` prints.
- [Properties worth proving](dream-properties.md) — the list of candidate theorems, including
  "can run useful programs".
- [`Core/README.md`](../Core/README.md), [`Frontend/README.md`](../Frontend/README.md),
  [`Backend/README.md`](../Backend/README.md) — each part of the code, in detail.
- [Adjudications](adjudications.md) — departures from the paper's printed text in the baseline.

## Designs

- [Effects and handlers: scoping](effects-scoping.md) — the staging of effects (#18): answering
  operations, `Fail`, control operations, and what each stage needs.
- [Effect polymorphism](effect-polymorphism.md) — functions over effectful computations (#161):
  copies over static names, provided and tunneled rows, site freshness, stored callbacks. A design;
  nothing is built.
- [Strings and slices](strings-slices-design.md) — slices, buffers, UTF-8 text and literals, end
  to end, with the status of each stage.
- [A Kubernetes operator](operator/README.md) — a design-down sketch of a target program in the
  language as it should be; it does not parse.

## Background and research notes

- Prior art: [memory model](prior-art-memory-model.md),
  [borrow splitting](prior-art-borrow-splitting.md),
  [effects, coeffects and borrowing](prior-art-effects-coeffects.md),
  [borrows as optics](prior-art-optics.md),
  [session types, par and modes](prior-art-sessions.md),
  [what Rust's designers wish they had done](prior-art-rust-wishlists.md)
- [Ideas: pointers, cycles, non-lexical lifetimes](ideas-pointers-and-lifetimes.md)
- [Ideas: handlers, classified by continuation use](ideas-handlers-and-borrows.md)
- Scoping notes: [deep freeze](scope-deep-freeze.md), [recursion](scope-recursion.md)
- [Salvage from l_lang](l-lang-salvage.md) — ideas and requirements kept from the previous language
- [l_lang kernel and literature](l-lang-kernel-and-lit.md) — its μ/ν techniques, the anatomy of
  its proof burden, and an annotated bibliography
- [Consolidation audit](consolidation-audit.md) — how the experiments became `Core/`
