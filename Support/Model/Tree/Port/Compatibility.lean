import Support.Model.Tree.Port.Singletons

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Compatibility.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — Compatibility

`[about ours]`.  Cell-level compatibility read off tags, values and witnesses, and `○` at an `imm` cell.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `○` returns an `imm` operand as an `imm` cell over the same value and
witness: 6.14's "the resulting composites still agree on overlapping imm cells
up to lifetimes", at the cell level. -/
theorem CellUT.CompR.imm_left {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (hk : ψ₁.kind = Kind.imm) :
    ψ.kind = Kind.imm ∧ ψ.erase = ψ₁.erase ∧ ψ.wit = ψ₁.wit := by
  cases h with
  | same χ => exact ⟨hk, rfl, rfl⟩
  | strict k =>
      have hc := CellUT.compS_spec _ _ k
      exact ⟨CellUT.CompS.kind hc, (CellUT.CompS.erase hc).1, (CellUT.CompS.wit hc).1⟩
  | mutMut => exact absurd hk (by simp)
  | mutOwn => exact absurd hk (by simp)
  | ownMut => exact absurd hk (by simp)
  | immOwn => exact ⟨rfl, rfl, rfl⟩
  | ownImm => exact absurd hk (by simp)
  | immMut => exact ⟨rfl, rfl, rfl⟩
  | mutImm => exact absurd hk (by simp)

/-- A non-`own` `○` composite carries the witness of a non-`own` operand. -/
theorem CellUT.CompR.wit_of_ne_own {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind ≠ Kind.own) :
    (ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨ (ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  cases h with
  | same χ => exact Or.inl ⟨hk, rfl⟩
  | strict k =>
      exact Or.inl ⟨by rw [(CellUT.CompatS.kinds k).1]; simp,
        (CellUT.CompS.wit (CellUT.compS_spec _ _ k)).1⟩
  | mutMut a b v τ ha hb P Q hP hQ =>
      exact Or.inl ⟨by simp,
        (CellUT.wit_mutOf _ _ _ _ _ _).trans (CellUT.wit_mutOf a v τ ha P hP).symm⟩
  | mutOwn => exact Or.inl ⟨by simp, rfl⟩
  | ownMut => exact Or.inr ⟨by simp, rfl⟩
  | immOwn => exact Or.inl ⟨by simp, rfl⟩
  | ownImm => exact Or.inr ⟨by simp, rfl⟩
  | immMut => exact Or.inl ⟨by simp, rfl⟩
  | mutImm => exact Or.inr ⟨by simp, rfl⟩

/-- A cell `▶◀` the left operand of a `○` is `▶◀` its value.
`[about ours: the cell-level step `[TR]` Lemma 6.12's proof takes at a location
where both `ρ₂` and `ρ₃` are defined]` -/
theorem CellUT.CompatS.of_compR_left {χ ψ₁ ψ₂ ψ : CellUT Loc Val K}
    (h : CellUT.CompatS χ ψ₁) (hc : CellUT.CompR ψ₁ ψ₂ ψ) : CellUT.CompatS χ ψ := by
  obtain ⟨k, k₁, hv, hw⟩ := CellUT.compatS_iff.mp h
  obtain ⟨m₁, m₂, m₃⟩ := CellUT.CompR.imm_left hc k₁
  exact CellUT.compatS_iff.mpr ⟨k, m₁, hv.trans m₂.symm, hw.trans m₃.symm⟩

end BoCa.Fig16.Tree

end
