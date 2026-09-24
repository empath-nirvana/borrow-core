import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.Walks

/-!
# Support — Model — RelaxedWalks

`[about ours]`.  `ex(ρ)_○` has no `imm` cell, `⦇ρ⦈_○` is functional, and `○` never makes an `imm` cell from two non-`imm` ones.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem CellU.compR_ne_imm (ψ₁ ψ₂ ψ : CellU Loc Val) (h : CellU.CompR ψ₁ ψ₂ ψ)
    (h₁ : ψ₁.kind ≠ Kind.imm) (h₂ : ψ₂.kind ≠ Kind.imm) : ψ.kind ≠ Kind.imm := by
  cases h with
  | same => exact h₁
  | strict k => exact absurd (CellU.CompatS.kinds k).1 h₁
  | mutMut => exact fun e => Kind.noConfusion e
  | mutOwn => exact fun e => Kind.noConfusion e
  | ownMut => exact fun e => Kind.noConfusion e
  | immOwn => exact absurd rfl h₁
  | ownImm => exact absurd rfl h₂
  | immMut => exact absurd rfl h₁
  | mutImm => exact absurd rfl h₂

/-- `[TR]` Lemma 6.36 at `○`.  `[as printed]` -/
theorem ExR.immFree {ρ σ : ResU Loc Val} (h : ExR ρ σ) : σ.ImmFree :=
  ExW.immFree CellU.compR_ne_imm h

/-- `⦇ρ⦈_○ = ag(ρ) ○ ex(ρ)_○` (`[TR]` Definition 6.1, p. 9) is single-valued.
`[about ours: `ResU.FlatR` is the graph of `⦇ρ⦈_○` (G4)]` -/
theorem ResU.FlatR.functional {ρ σ σ' : ResU Loc Val}
    (h : ρ.FlatR σ) (h' : ρ.FlatR σ') : σ = σ' := by
  obtain ⟨a, e, hag, hex, hc⟩ := h
  obtain ⟨a', e', hag', hex', hc'⟩ := h'
  have ha : a = a' := AgW.functional hag hag'
  have he : e = e' := ExR.functional hex hex'
  subst ha; subst he
  exact ResU.CompR.functional hc hc'

end BoCa.Fig16

end
