import CBPVMu.Compatibility

/-!
# CBPVMu — the delay type's relation

`D A = νX. F(A ⊕ U X) & F 1` is `cC`'s `delay` clause, the greatest fixed point `delayRel` of
`delayF` (`Relation.lean`).  `delayF` is monotone in the candidate (`delayF_mono`, from
`wpTS_mono` alone), so the greatest fixed point is a fixed point (`delayRel_out`,
`delayRel_roll`), and at the relation itself `delayF` is `cC` at the unrolling
`F(A ⊕ U(D A)) & F 1` (`cC_delay_iff`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The unrolling of `D A`: `F(A ⊕ U(D A)) & F 1`. -/
abbrev delayUnroll (A : VTy) : CTy := .amp (.ret (.sum A (.thunk (.delay A)))) (.ret .unit)

theorem delayQ_mono {VA : List SRec → Val → WProp} {R R' : CPred} (h : R.Le R')
    (ls : List SRec) (w : Val) : Entails (delayQ VA R ls w) (delayQ VA R' ls w) := by
  rintro σ (hn | ⟨v₂, σ₀, σ₃, hc, hp, ht⟩)
  · exact Or.inl hn
  · exact Or.inr ⟨v₂, σ₀, σ₃, hc, hp, fun ls' hk => h _ _ _ (ht ls' hk)⟩

theorem delayF_mono (VA : List SRec → Val → WProp) {R R' : CPred} (h : R.Le R') :
    (delayF VA R).Le (delayF VA R') := fun _ _ ρ ⟨h₁, h₂⟩ =>
  ⟨wpTS_mono (fun ls' w => delayQ_mono h ls' w) ρ h₁, h₂⟩

/-- Coinduction. -/
theorem delayRel_coind {VA : List SRec → Val → WProp} {R : CPred} (hR : R.Le (delayF VA R)) :
    R.Le (delayRel VA) :=
  fun _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem delayRel_out (VA : List SRec → Val → WProp) : (delayRel VA).Le (delayF VA (delayRel VA)) := by
  rintro ls e ρ ⟨R, hR, h⟩
  exact delayF_mono VA (delayRel_coind hR) ls e ρ (hR ls e ρ h)

/-- `roll`. -/
theorem delayRel_roll (VA : List SRec → Val → WProp) : (delayF VA (delayRel VA)).Le (delayRel VA) :=
  delayRel_coind (delayF_mono VA (delayRel_out VA))

/-- **`D A` is its unrolling**: `𝒞⟦D A⟧ = 𝒞⟦F(A ⊕ U(D A)) & F 1⟧`. -/
theorem cC_delay_iff (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.delay A) ls δ e ρ ↔ cC (delayUnroll A) ls δ e ρ :=
  ⟨fun h => delayRel_out _ ls e ρ h, fun h => delayRel_roll _ ls e ρ h⟩

end BoCa.Fig16.LogRel.CBPVMu

end
