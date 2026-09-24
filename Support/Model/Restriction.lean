import Paper.S5_Model.Definitions
import Support.Model.Composition

/-!
# Support — Model — Restriction

`[about ours]`.  `ρ∣dom(σ)` and `ρ/dom(σ)`, the restriction `[TR]` §6 uses and neither document defines.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.restrictDom_get_of_some {ρ σ : ResU Loc Val} {l : Loc}
    {ζ : CellU Loc Val} (h : σ.get l = some ζ) :
    (ρ.restrictDom σ).get l = ρ.get l := by
  show (if (σ.get l).isSome then ρ.get l else none) = ρ.get l
  rw [h]; rfl

theorem ResU.restrictDom_get_of_none {ρ σ : ResU Loc Val} {l : Loc}
    (h : σ.get l = none) : (ρ.restrictDom σ).get l = none := by
  show (if (σ.get l).isSome then ρ.get l else none) = none
  rw [h]; rfl

theorem ResU.delDom_get_of_some {ρ σ : ResU Loc Val} {l : Loc}
    {ζ : CellU Loc Val} (h : σ.get l = some ζ) : (ρ.delDom σ).get l = none := by
  show (if (σ.get l).isSome then none else ρ.get l) = none
  rw [h]; rfl

theorem ResU.delDom_get_of_none {ρ σ : ResU Loc Val} {l : Loc}
    (h : σ.get l = none) : (ρ.delDom σ).get l = ρ.get l := by
  show (if (σ.get l).isSome then none else ρ.get l) = ρ.get l
  rw [h]; rfl

/-- A cell of `ρ|dom(σ)` is a cell of `ρ`. -/
theorem ResU.restrictDom_get_inv {ρ σ : ResU Loc Val} {l : Loc} {ζ : CellU Loc Val}
    (h : (ρ.restrictDom σ).get l = some ζ) : ρ.get l = some ζ := by
  cases e : σ.get l with
  | none => rw [ResU.restrictDom_get_of_none e] at h; exact absurd h (by simp)
  | some χ => rw [ResU.restrictDom_get_of_some e] at h; exact h

/-- `ρ = ρ|dom(σ) ● ρ/dom(σ)`, the splitting `[TR]` 6.56's appeal to 6.11
needs. -/
theorem ResU.restrictDom_compS (ρ σ : ResU Loc Val) :
    ResU.CompS (ρ.restrictDom σ) (ρ.delDom σ) ρ := by
  refine ⟨ResU.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · cases e : σ.get l with
    | none => exact Or.inl (ResU.restrictDom_get_of_none e)
    | some χ => exact Or.inr (ResU.delDom_get_of_some e)
  · cases e : σ.get l with
    | none =>
        show OptComp CellU.CompS ((ρ.restrictDom σ).get l) ((ρ.delDom σ).get l) (ρ.get l)
        rw [ResU.restrictDom_get_of_none e, ResU.delDom_get_of_none e]
        cases ρ.get l with
        | none => rfl
        | some χ => rfl
    | some χ =>
        show OptComp CellU.CompS ((ρ.restrictDom σ).get l) ((ρ.delDom σ).get l) (ρ.get l)
        rw [ResU.restrictDom_get_of_some e, ResU.delDom_get_of_some e]
        cases ρ.get l with
        | none => rfl
        | some ζ => rfl

end BoCa.Fig16

end
