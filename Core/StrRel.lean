import Core.Compatibility

/-!
# Core — the stream type's relation  `[spec §7]`

`Str A = νX. F(A ⊗ U X) & F 1` is `cC`'s `str` clause, the greatest fixed point `strRel` of
`strF` (`Relation.lean`).  `strF` is monotone in the candidate (`strF_mono`), so the greatest
fixed point is a fixed point (`strRel_out`, `strRel_roll`), and at the relation itself `strF` is
`cC` at the unrolling `F(A ⊗ U(Str A)) & F 1` (`cC_str_iff`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The unrolling of `Str A`: `F(A ⊗ U(Str A)) & F 1`. -/
abbrev strUnroll (A : VTy) : CTy := .amp (.ret (.tensor A (.thunk (.str A)))) (.ret .unit)

theorem strQ_mono {VA : List SRec → Val → WProp} {R R' : CPred} (h : R.Le R')
    (ls : List SRec) (w : Val) : Entails (strQ VA R ls w) (strQ VA R' ls w) := by
  rintro σ ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, hT⟩
  exact ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, fun ls' hk => h _ _ _ (hT ls' hk)⟩

theorem strF_mono (VA : List SRec → Val → WProp) {R R' : CPred} (h : R.Le R') :
    (strF VA R).Le (strF VA R') := fun _ _ ρ ⟨h₁, h₂⟩ =>
  ⟨wpTS_mono (fun ls' w => strQ_mono h ls' w) ρ h₁, h₂⟩

/-- Coinduction. -/
theorem strRel_coind {VA : List SRec → Val → WProp} {R : CPred} (hR : R.Le (strF VA R)) :
    R.Le (strRel VA) :=
  fun _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem strRel_out (VA : List SRec → Val → WProp) : (strRel VA).Le (strF VA (strRel VA)) := by
  rintro ls e ρ ⟨R, hR, h⟩
  exact strF_mono VA (strRel_coind hR) ls e ρ (hR ls e ρ h)

/-- `roll`. -/
theorem strRel_roll (VA : List SRec → Val → WProp) : (strF VA (strRel VA)).Le (strRel VA) :=
  strRel_coind (strF_mono VA (strRel_out VA))

/-- **`Str A` is its unrolling**: `𝒞⟦Str A⟧ = 𝒞⟦F(A ⊗ U(Str A)) & F 1⟧`.  `[spec §7]` -/
theorem cC_str_iff (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.str A) ls δ e ρ ↔ cC (strUnroll A) ls δ e ρ :=
  ⟨fun h => strRel_out _ ls e ρ h, fun h => strRel_roll _ ls e ρ h⟩

end BoCa.Fig16.LogRel.Core

end
