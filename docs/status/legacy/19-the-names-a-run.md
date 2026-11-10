
The names a run raises (§19 *Typing*) are stated as a run invariant in `Core/RaiseNames.lean`,
with no change to `CDerives`, the machine or the relation: `Expr.RaiseOK`, `HeapRaiseOK`,
`raiseOK_step1` and `raiseOK_steps`; a tied term is at its effect context's names
(`EffCtx.Names`, decided by `rcE`; `raiseOK_of_derivesAt`), its runs from the empty memory stay at
them (`raiseOK_reach`), and every cancel they reach keeps errors of those names (`KCfinNamed`,
`CancelsNamed`, `cancelsNamed_of_derivesAt`).
