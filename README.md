# borrow-core

A borrow calculus under a written specification, `SPEC.md`, starting from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(PACMPL 9:OOPSLA2:415, 2025), bolo-formalization commit `1658da9`.

- `docs/Home.md` — start here: overview, pipeline, glossary, design decisions.
- `SPEC.md` — the language: the paper's calculus as baseline (§1), then numbered entries.
- `Paper/`, `Support/` — the mechanization, with each entry's additions tagged `[spec §N]`.
  `Paper/INDEX.md` and `docs/adjudications.md` describe the baseline.
- `Examples/` — programs that exercise the entries.
- `Core/` — the call-by-push-value core with non-strict frame lifetimes, blocks, records and
  family borrows, recursive types and folds, and codata `νX. C` (`SPEC.md` §3–§7),
  tagged `[spec §N]`; `Core/README.md` describes it.
- `Frontend/` — the parser for the core syntax (`docs/syntax-core.md`) and the `bcc`
  executable (`lake exe bcc parse <file>`); `corpus/` holds its test programs
  (`scripts/parse-corpus.sh`). `Frontend/README.md` describes it.
- `Backend/` — the compiler from a checked `main` to WebAssembly (`lake exe bcc run <file>`),
  through a closure IR and a flat IR, each with an interpreter; `Backend/README.md` describes
  it. `scripts/compile-corpus.sh` compiles every corpus program with a `main`, runs it under
  `wasmtime`, and compares it with `Support`'s interpreter.
- `experiments/` — probes toward future entries, as non-default libraries the library never
  imports (`experiments/README.md`).

```sh
lake exe cache get
lake build
scripts/check-hygiene.sh
lake env lean scripts/AxiomCheck.lean
scripts/compile-corpus.sh       # needs wasmtime on PATH
```

Entry 1 (`SPEC.md` §2) adds the exponential `!T`: a value that holds no resource, which a borrow
keeps whole. `Examples/` loads closures through immutable and mutable borrows and calls them.

Entries 2–6 (`SPEC.md` §3–§7) are `Core/`: one typed world whose Fundamental Property and
adequacy cover every rule, into which the baseline embeds.
