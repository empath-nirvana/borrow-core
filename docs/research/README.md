# Research reports (2026-10-19)

These are raw research reports, kept so later design work can cite them. They are inputs, not decisions; the decisions are recorded in `docs/decisions.md` and on the issues.

- `mutation-paradigms.md`: what Rust uses `let mut` for, and six paradigms for expressing it here, each critiqued against the repo.
- `prior-art-graded-adjoint.md`: Granule, LNL, adjoint logic, QTT, graded CBPV, and borrows as modes or grades.
- `prior-art-modes-capabilities.md`: OxCaml modes and DRFCaml, Pony, Scala capture checking, Swift, Rust/RustBelt, Verona, Vale, Hylo, Austral, Mezzo, Cyclone.
- `prior-art-session-types.md`: SILL, CP, GV, adjoint sessions, manifest sharing, session logical relations, and session types with handlers or borrows.

Citations marked (unverified) were not confirmed when the report was written.

The premise the user set afterwards (2026-10-19): the goal is not to rebuild Rust's borrow checker; a more limited, lexical, mostly second-class borrow checker with linearity may be enough.
