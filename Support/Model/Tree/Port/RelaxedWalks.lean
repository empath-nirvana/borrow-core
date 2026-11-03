import Support.Model.Tree.Port.FlatteningCells

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/RelaxedWalks.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — RelaxedWalks

`[about ours]`.  `ex(ρ)_○` has no `imm` cell, `⦇ρ⦈_○` is functional, and `○` never makes an `imm` cell from two non-`imm` ones.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
theorem CellUT.compR_ne_imm (ψ₁ ψ₂ ψ : CellUT Loc Val K) (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (h₁ : ψ₁.kind ≠ Kind.imm) (h₂ : ψ₂.kind ≠ Kind.imm) : ψ.kind ≠ Kind.imm := by
  cases h with
  | same => exact h₁
  | strict k => exact absurd (CellUT.CompatS.kinds k).1 h₁
  | mutMut => exact fun e => Kind.noConfusion e
  | mutOwn => exact fun e => Kind.noConfusion e
  | ownMut => exact fun e => Kind.noConfusion e
  | immOwn => exact absurd rfl h₁
  | ownImm => exact absurd rfl h₂
  | immMut => exact absurd rfl h₁
  | mutImm => exact absurd rfl h₂

/-- `[TR]` Lemma 6.36 at `○`.  `[as printed]` -/
theorem ExRT.immFree {ρ σ : ResUT Loc Val K} (h : ExRT ρ σ) : σ.ImmFree :=
  ExWT.immFree CellUT.compR_ne_imm h

/-- `⦇ρ⦈_○ = ag(ρ) ○ ex(ρ)_○` (`[TR]` Definition 6.1, p. 9) is single-valued.
`[about ours: `ResUT.FlatR` is the graph of `⦇ρ⦈_○` (G4)]` -/
theorem ResUT.FlatR.functional {ρ σ σ' : ResUT Loc Val K}
    (h : ρ.FlatR σ) (h' : ρ.FlatR σ') : σ = σ' := by
  obtain ⟨a, e, hag, hex, hc⟩ := h
  obtain ⟨a', e', hag', hex', hc'⟩ := h'
  have ha : a = a' := AgWT.functional hag hag'
  have he : e = e' := ExRT.functional hex hex'
  subst ha; subst he
  exact ResUT.CompR.functional hc hc'

end BoCa.Fig16.Tree

end
