import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Composition
import Support.Model.Propositions
import Support.Model.Singletons

/-!
# Literal readings — [TR] §6.6

* 6.130: `reborrow_emp_outside_stratum`, the added hypothesis measured at a
  resource outside `Res_α`;
* 6.131 (`↺V₁`): `RefPrintedChainResidual`, what the `Ref` bullet's printed chain
  leaves at our objects.

Nothing depends on this file.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### Lemma 6.131 (↺V₁) — literal reading

The record is in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`.
-/
/-- The entailment 6.131's `Ref` bullet reaches after "Apply IH", "Apply
theorem 6.130", "Apply `↺⋆`" and the unit law: antecedent
`↺_α (↺_α 𝒱⟦Imm̲ 'a T′⟧δ(v′))`, goal `↺_α 𝒱⟦Imm 'a T′⟧δ(v)`.  Not derived, and no
obstruction to it is verified.
`[about ours: the residual of 6.131's printed `Ref` chain, at our objects]` -/
def RefPrintedChainResidual (α : Life) (x : LifeVar) (δ : LSub) (T : Ty) (v : Val) : Prop :=
  ∀ v' : Val,
    reborrow α (reborrow α (vDen (T.immReborrow (.var x)) δ v'))
      ⊨ reborrow α (vDen (Ty.imm (.var x) T) δ v)

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.RebExample

/-! `[about ours]` -/
private def mutWit (w : Nat) : ResU Nat Nat := ResU.single 1 (CellU.ownOf w)

private theorem mutWit_stratum (w : Nat) (α : Life) : (mutWit w).InStratum α := by
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact trivial

private def mutInv : Nat → SPropS Nat Nat 3 := fun _ _ => True

private def mutCell (v w : Nat) : CellU Nat Nat :=
  CellU.mutOf 3 v (mutWit w) (mutWit_stratum w 3) mutInv trivial

/-- `ρ ≜ ℓ₀ ↦ mut(3, v, ℓ₁ ↦ own(w), λ_ _. ⊤)`. -/
private def mutRes (v w : Nat) : ResU Nat Nat := ResU.single 0 (mutCell v w)

private theorem mutRes_zero (v w : Nat) : (mutRes v w).get 0 = some (mutCell v w) :=
  ResU.single_get_self _ _

/-- `@ρ = 3`, so no `ρ′` is a reborrow of `ρ` at `α = 1`.
`[about ours: a non-inhabitant of the printed set]` -/
theorem not_reb_of_at (v w : Nat) (ρ' : ResU Nat Nat) : ¬ ResU.Reb 1 (mutRes v w) ρ' := by
  rintro ⟨hs, -⟩
  have hn : (3 : Nat) < 1 := hs 0 (mutCell v w) (mutRes_zero v w)
  omega

end BoCa.Fig16.RebExample

namespace BoCa.Fig16.BoLo

/-!
### Lemma 6.130 — literal reading

The record is in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`.
-/
/-- `↻_1 emp` does not hold at `ℓ₀ ↦ mut(3, v, ℓ₁ ↦ own(w), −)`, a resource
outside `Res_1`.
`[about ours: a resource outside `Res_α`, measured against `↻_α emp`]` -/
theorem reborrow_emp_outside_stratum (v w : Nat) :
    ¬ reborrow 1 (emp : SPropU Nat Nat) (RebExample.mutRes v w) := by
  rintro ⟨ρ', hr, -⟩
  exact RebExample.not_reb_of_at v w ρ' hr

end BoCa.Fig16.BoLo

end
