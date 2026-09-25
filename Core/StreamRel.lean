import Core.Compatibility

/-!
# Core — the stream type's relation  `[spec §7]`

`Stream A = νX. F(A ⊗ U X) & F 1` is `cC`'s `stream` clause, the greatest fixed point
`streamRel` of `streamF` (`Relation.lean`).  `streamF` is monotone in the candidate
(`streamF_mono`), so the greatest fixed point is a fixed point (`streamRel_out`,
`streamRel_roll`), and at the relation itself `streamF` is `cC` at the unrolling
`F(A ⊗ U(Stream A)) & F 1` (`cC_stream_iff`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The unrolling of `Stream A`: `F(A ⊗ U(Stream A)) & F 1`. -/
abbrev streamUnroll (A : VTy) : CTy := .amp (.ret (.tensor A (.thunk (.stream A)))) (.ret .unit)

theorem streamQ_mono {VA : List SRec → Val → WProp} {R R' : CPred} (h : R.Le R')
    (ls : List SRec) (w : Val) : Entails (streamQ VA R ls w) (streamQ VA R' ls w) := by
  rintro σ ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, hT⟩
  exact ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, fun ls' hk => h _ _ _ (hT ls' hk)⟩

theorem streamF_mono (VA : List SRec → Val → WProp) {R R' : CPred} (h : R.Le R') :
    (streamF VA R).Le (streamF VA R') := fun _ _ ρ ⟨h₁, h₂⟩ =>
  ⟨wpTS_mono (fun ls' w => streamQ_mono h ls' w) ρ h₁, h₂⟩

/-- Coinduction. -/
theorem streamRel_coind {VA : List SRec → Val → WProp} {R : CPred} (hR : R.Le (streamF VA R)) :
    R.Le (streamRel VA) :=
  fun _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem streamRel_out (VA : List SRec → Val → WProp) :
    (streamRel VA).Le (streamF VA (streamRel VA)) := by
  rintro ls e ρ ⟨R, hR, h⟩
  exact streamF_mono VA (streamRel_coind hR) ls e ρ (hR ls e ρ h)

/-- `roll`. -/
theorem streamRel_roll (VA : List SRec → Val → WProp) :
    (streamF VA (streamRel VA)).Le (streamRel VA) :=
  streamRel_coind (streamF_mono VA (streamRel_out VA))

/-- **`Stream A` is its unrolling**: `𝒞⟦Stream A⟧ = 𝒞⟦F(A ⊗ U(Stream A)) & F 1⟧`.  `[spec §7]` -/
theorem cC_stream_iff (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.stream A) ls δ e ρ ↔ cC (streamUnroll A) ls δ e ρ :=
  ⟨fun h => streamRel_out _ ls e ρ h, fun h => streamRel_roll _ ls e ρ h⟩

end BoCa.Fig16.LogRel.Core

end
