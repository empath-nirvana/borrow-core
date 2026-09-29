# borrow-core documentation

Start here. For learning the language, read the book: the guide and reference in
[`book/`](../book/src/SUMMARY.md), with doc-tested examples (`mdbook build book`, or the `book`
artifact of any CI run). The pages below are design and research notes.

| page | what it covers |
|---|---|
| [Overview](overview.md) | what the language is, what is proved, and what is trusted |
| [Pipeline](pipeline.md) | from a `.bc` file to WebAssembly: the `bcc` commands and the scripts |
| [Glossary](glossary.md) | the terms used across the spec, code and docs |
| [Design decisions](decisions.md) | what was chosen, and why |

## Reference

- [`SPEC.md`](../SPEC.md) — the language, as numbered entries. The authority on what the language is.
- [Core syntax](syntax-core.md) — the textual form the parser and checker accept.
- [Surface syntax](surface-cbpv.md) — draft design: CBPV at the surface, with sugar only for shifts that cancel (#54).
- [Properties worth proving](dream-properties.md) — the list of candidate theorems, including
  "can run useful programs".
- [`Core/README.md`](../Core/README.md), [`Frontend/README.md`](../Frontend/README.md),
  [`Backend/README.md`](../Backend/README.md) — each part of the code, in detail.

## Background and design notes

- [Prior art: memory model](prior-art-memory-model.md), [prior art: borrow splitting](prior-art-borrow-splitting.md), [prior art: session types, par and modes](prior-art-sessions.md), [prior art: what Rust's designers wish they had done](prior-art-rust-wishlists.md)
- [Ideas: pointers, cycles, non-lexical lifetimes](ideas-pointers-and-lifetimes.md)
- [Ideas: handlers, classified by continuation use](ideas-handlers-and-borrows.md)
- Scoping notes: [deep freeze](scope-deep-freeze.md), [recursion](scope-recursion.md)
- [Salvage from l_lang](l-lang-salvage.md) — ideas and requirements kept from the previous language
- [l_lang kernel and literature](l-lang-kernel-and-lit.md) — its μ/ν techniques, the anatomy of its proof burden, and an annotated bibliography
- [Consolidation audit](consolidation-audit.md) — how the experiments became `Core/`
- [Adjudications](adjudications.md) — departures from the paper's printed text in the baseline
