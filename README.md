# borrow-core

A borrow calculus under a written specification, `SPEC.md`, starting from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(PACMPL 9:OOPSLA2:415, 2025), bolo-formalization commit `1658da9`.

- `SPEC.md` — the language: the paper's calculus as baseline (§1), then numbered entries.
- `Paper/`, `Support/` — the mechanization, with each entry's additions tagged `[spec §N]`.
  `Paper/INDEX.md` and `docs/adjudications.md` describe the baseline.
- `Examples/` — programs that exercise the entries.
- `experiments/` — probes toward future entries, as non-default libraries the library never
  imports (`experiments/README.md`).

```sh
lake exe cache get
lake build
scripts/check-hygiene.sh
lake env lean scripts/AxiomCheck.lean
```

Entry 1 (`SPEC.md` §2) adds the exponential `!T`: a value that holds no resource, which a borrow
keeps whole. `Examples/` loads closures through immutable and mutable borrows and calls them.
