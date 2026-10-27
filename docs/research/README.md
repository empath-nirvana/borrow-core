# Research reports (2026-10-19)

These are raw research reports, kept so later design work can cite them. They are inputs, not decisions; the decisions are recorded in `docs/decisions.md` and on the issues.

- `mutation-paradigms.md`: what Rust uses `let mut` for, and six paradigms for expressing it here, each critiqued against the repo.
- `prior-art-graded-adjoint.md`: Granule, LNL, adjoint logic, QTT, graded CBPV, and borrows as modes or grades.
- `prior-art-modes-capabilities.md`: OxCaml modes and DRFCaml, Pony, Scala capture checking, Swift, Rust/RustBelt, Verona, Vale, Hylo, Austral, Mezzo, Cyclone.
- `dependent-types-spike.md` (2026-10-20, #625): Lean as the dependent layer for #624's laws, with `experiments/DepSpike`; QTT/Idris 2/BendTT, LNL_D, Flux and Liquid Haskell, DML, and Verus-style specs measured against the code and the kill criterion.
- `prior-art-session-types.md`: SILL, CP, GV, adjoint sessions, manifest sharing, session logical relations, and session types with handlers or borrows.
- `prior-art-bend.md` (2026-10-20, #619): Bend 1/HVM2 and Bend 2 (BendTT, BendRT), and whether the pure div-free fragment can be parallelised automatically; ends in a decision menu.

Citations marked (unverified) were not confirmed when the report was written.

The premise the user set afterwards (2026-10-19): the goal is not to rebuild Rust's borrow checker; a more limited, lexical, mostly second-class borrow checker with linearity may be enough.
- [`let-mut-as-place.md`](let-mut-as-place.md): `let mut` as a place through the borrow calculus, prototyped and measured (#626; code on branch `mut-place`).
