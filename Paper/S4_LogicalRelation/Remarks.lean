import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Propositions
import Support.Statics.Contexts

/-!
# [TR] §4 Logical Relation — remarks on the definitions

Row 4.16's two directions between the `Mut` clause and `Supported`, and row
4.18's `sem_iff`.  Theorems about definition rows whose proofs use `[TR]` §6.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.16 · — no printed counterpart — · [TR] p. 4 · `[repair]`
-/
/-- A resource in `𝒱⟦Mut @a T⟧δ` exhibits a `β ⊒ @aδ` at which `𝒱⟦T⟧δ` is a
`Val → SProp_β`, and a value and a resource satisfying it.  `[about ours]` -/
theorem vDen_mut_supported {δ : LSub} {a : Lifetime.Life} {T : Ty} {v : Val} {ρ : WRes}
    (h : vDen (.mut a T) δ v ρ) :
    ∃ α β w σ, a.interp δ = some α ∧ α ⊑ β ∧ Supported β (vDen T δ) ∧ vDen T δ w σ := by
  obtain ⟨α, ha, ℓ, hsep⟩ := h
  obtain ⟨-, b, w, σ, hσ, Q, hw, hab, -, hofS⟩ := pure_sep_iff.mp hsep
  refine ⟨α, b, w, σ, ha, hab, fun u τ hu => ?_, ?_⟩
  · rw [← hofS] at hu
    exact hu.1
  · rw [← hofS]
    exact ⟨hσ, hw⟩

/-- The converse of `vDen_mut_supported`.  `[about ours]` -/
theorem vDen_mut_of_supported {δ : LSub} {a : Lifetime.Life} {T : Ty}
    {α β : Life} {w : Val} {σ : WRes} (ha : a.interp δ = some α) (hab : α ⊑ β)
    (hs : Supported β (vDen T δ)) (hw : vDen T δ w σ) (ℓ : BoCa.Loc) :
    ∃ ρ, vDen (.mut a T) δ (.loc ℓ) ρ := by
  have hofS : ofS (fun u => SPropU.toS β (vDen T δ u)) = vDen T δ := by
    funext u
    funext τ
    exact propext ((SPropU.toU_toS_iff β (vDen T δ u) τ).trans
      ⟨fun k => k.1, fun k => ⟨k, hs u τ k⟩⟩)
  have hcell := ptoMut_of_cell ℓ α β hab w σ (hs w σ hw)
    (fun u => SPropU.toS β (vDen T δ u)) hw
  rw [hofS] at hcell
  exact ⟨_, α, ha, ℓ, pure_sep_mk rfl hcell⟩

/-!
### 4.18 · — no printed counterpart — · [TR] p. 4 · `[about ours]`

Row 4.14 evaluated at `∅`, as a `Prop`; a persistent proposition holds exactly
when it holds of `∅`.  The §6.8 compatibility lemmas are stated at it.
-/
theorem sem_iff {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} :
    Sem Δ Γ e T ↔
      ∀ δ γ ρ, Δ.Models δ → gDen δ Γ γ ρ → wp (substAll γ e) (vDen T δ) ρ := by
  constructor
  · rintro ⟨-, hw⟩ δ γ ρ hδ hg
    have h₁ := hw δ γ PMap.empty PMap.empty ⟨rfl, hδ⟩ (ResU.comp_empty_right _)
    exact h₁ ρ ρ hg (compS_empty_left ρ)
  · intro h
    refine ⟨emp_empty, ?_⟩
    intro δ γ ρ₁ ρ₂ hd hc
    obtain ⟨rfl, hδ⟩ := hd
    have h₂ : ρ₂ = PMap.empty := eq_of_compS_empty_left hc
    subst h₂
    intro ρ₃ ρ₄ hg hc'
    have h₄ : ρ₄ = ρ₃ := eq_of_compS_empty_left hc'
    subst h₄
    exact h δ γ _ hδ hg

end BoCa.Fig16.LogRel

end
