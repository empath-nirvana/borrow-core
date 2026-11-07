
§3's derived nodes and `use` nodes are implemented in the templates of `scripts/gen-pin.py`
(`scripts/pin/TExpr.tmpl.lean`, `TDerives.tmpl.lean`: the nodes, `litFnE`, their rules and
projections), `Frontend/Check/TShift.lean` (`TExpr.shift`, `AbsF`, `TExpr.absF`,
`TExpr.absF_shift`), `Frontend/Check/Weaken.lean` (`TDerivesP.weaken`, `TDerivesAt.weaken`,
`TDerivesAt.use_projects`, `TDerivesP.use_projects`), `Frontend/Check/TTied.lean` (`TTied.use`,
`TTied.weaken`, `TTied.litFn`), `Frontend/Check/Rules.lean` (`rUse`, `rUseAt`, `rLitFn`), the
checker's cache of checked bodies (`DefEntry`, `CheckM`, `useDef`, `Frontend/Check/Checker.lean`)
and the core form `Val.mark` (`Frontend/Syntax.lean`, printed as the value it marks). No change to
`CDerives`, `Core/`, the relation, the machine, or any program's erasure, output, goldens or
counts.
