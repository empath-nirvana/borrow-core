import ResearchTree.TreeSemObs
/-!
# The tree archive's registered hypotheses, checked  `[spec §62]`

`Core/Assumptions.lean` lists `KeepKripkeRun` and `KeepKripkeRunNil` in its `outside` register
(their definitions are in this archive, outside `Core`'s imports). These are that register's two
`example`s, moved here unchanged (#1133): each restates the existing refutation's type.
-/

section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

example : ¬ BoCa.Fig16.Tree.Wp.Obs.KeepKripkeRun (ℍ := ℍ) :=
  BoCa.Fig16.Tree.Wp.Obs.cerwpT_not_keepKripke
example : ¬ BoCa.Fig16.Tree.Wp.Obs.KeepKripkeRunNil (ℍ := ℍ) :=
  BoCa.Fig16.Tree.Wp.Obs.cerwpT_not_keepKripkeNil

end
