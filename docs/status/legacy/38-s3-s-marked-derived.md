
§3's marked derived nodes, typed `[let-poly]`, `[handle]` at tail clauses and `reify`, the lint,
the lifetime weakening and the key table are implemented in `scripts/gen-pin.py` (`DERIVED`,
`lint_texpr`, the `TLife` cases) and its templates (`scripts/pin/TExpr.tmpl.lean`:
`divLitB`, `safeDivB`, `walkB`, `selfCallB`, `lendCellB`, `Expr.pairL`, `Expr.toVal`,
`Expr.letBody`; `TDerives.tmpl.lean`; `TLife.tmpl.lean`: `LeΔ`, `ExtΔ`, `TExpr.domFree`,
`TExpr.reAb`, `weakenΔ`), `Frontend/Check/Derived.lean`, `Frontend/Check/Rules.lean`
(`rMarked`), `Frontend/Check/Checker.lean` (`DefEntry.lift?`), the elaborator's marks
(`Frontend/Sugar.lean`: `divUnchecked`, `forData`, `lendBorrow` and the borrow block of a cell;
`Frontend/Elab/Effects.lean`: `memberCall`) and keys (`DefKey`, `recordKey`, `Origin.defKey`,
`Elaborated.keys`). No change to `CDerives`, `Core/`, the relation, the machine, or any program's
erasure, run output, goldens or counts; `bcc check` reports a `def` with type parameters as
`checked once per instance`.
