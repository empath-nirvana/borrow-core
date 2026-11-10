
§3's split masks and §5's cell classes are implemented in `Frontend/Check/Masks.lean` (`Masks`,
`SplitMasks`, `SplitMasks.both_iff`, `SplitMasks.both_persistent`, `SplitMasks.ins`), the generated
typed rules (`scripts/gen-pin.py`: the `u.Rel` premise at a split, `TExpr.masks?`,
`TDerivesAt.split_masks`, `TDerivesP.split_masks`, `TDerivesP.copies`), `Frontend/Check/Fam.lean`
(`split_lemma`, `Fam.split`, `Fam.mapB`), the builders at a split (`Rules.lean`, `TTied.lean`,
`Weaken.lean`'s `splitP_route`), §10's check on the masks (`Frontend/Check/Copies.lean`),
`Frontend/Check/Cells.lean` (`VTy.eraseLife`, `TExpr.cells`, `cellClasses`, `cellsOkB_sound`),
`Checked.cells` and `Checked.cells_closed`, `Backend/Cells.lean` (`bcc-counts --cells`) and
`scripts/check-cells.sh`. No change to `CDerives`, `Core/`, the relation, the machine, or any
program's erasure, output, goldens or counts.
