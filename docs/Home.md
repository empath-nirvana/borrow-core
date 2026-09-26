# borrow-core documentation

Start here.

| page | what it covers |
|---|---|
| [Overview](overview.md) | what the language is, what is proved, and what is trusted |
| [Pipeline](pipeline.md) | from a `.bc` file to WebAssembly: the `bcc` commands and the scripts |
| [Glossary](glossary.md) | the terms used across the spec, code and docs |
| [Design decisions](decisions.md) | what was chosen, and why |

## Reference

- [`SPEC.md`](../SPEC.md) — the language, as numbered entries. The authority on what the language is.
- [Core syntax](syntax-core.md) — the textual form the parser and checker accept.
- [Properties worth proving](dream-properties.md) — the list of candidate theorems, including
  "can run useful programs".
- [`Core/README.md`](../Core/README.md), [`Frontend/README.md`](../Frontend/README.md),
  [`Backend/README.md`](../Backend/README.md) — each part of the code, in detail.

## Background and design notes

- [Prior art: memory model](prior-art-memory-model.md), [prior art: borrow splitting](prior-art-borrow-splitting.md)
- [Ideas: pointers, cycles, non-lexical lifetimes](ideas-pointers-and-lifetimes.md)
- Scoping notes: [deep freeze](scope-deep-freeze.md), [recursion](scope-recursion.md)
- [Salvage from l_lang](l-lang-salvage.md) — ideas and requirements kept from the previous language
- [Consolidation audit](consolidation-audit.md) — how the experiments became `Core/`
- [Adjudications](adjudications.md) — departures from the paper's printed text in the baseline
