# borrow-core

A borrow calculus under a written specification, `SPEC.md`, starting from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(PACMPL 9:OOPSLA2:415, 2025), bolo-formalization commit `1658da9`.

- `SPEC.md` — the language: the paper's calculus as baseline (§1), then numbered entries.
- `Paper/`, `Support/` — the mechanization, with each entry's additions tagged `[spec §N]`.
  `Paper/INDEX.md` and `docs/adjudications.md` describe the baseline.
- `Examples/` — programs that exercise the entries.

```sh
lake exe cache get
lake build
scripts/check-hygiene.sh
lake env lean scripts/AxiomCheck.lean
```

Entry 1 (`SPEC.md` §2) adds closed code, `fn T₁ T₂`: a function that captures nothing, which an
immutable borrow keeps callable. `Examples/CallBorrowed.lean` loads one through a borrow and
calls it.
