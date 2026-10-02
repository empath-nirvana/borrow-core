import Core.Fundamental

/-!
# GhostEnd — the fundamental lemma for a stack segment with a hole

A frozen stack segment is an evaluation context `K` whose frames hold values. Syntactically it
is an open term `E`, typed `Δ; (□ : B), Γ ⊢ E : C`. The hole is the variable `0`, and the frames'
values are a closing substitution `γ` for `Γ`. So `K[v] = E[v, γ]` (`SegOf`).

`segment_fundamental` is `fundamentalC` at that open term, restated for `K`: at every
`δ ∈ ⟦Δ⟧`, every record list, every `γ ∈ 𝒢⟦Γ⟧δ` and every `v ∈ 𝒱⟦B⟧δ`, `K[v] ∈ 𝒞⟦C⟧δ`. It is
a restatement, proved from `fundamentalC` and nothing else. Resume uses it by choosing `δ`: the
assignment the internal lifetimes get at the resumption.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `K` is the segment `E` closed by `γ`: plugging `v` is substituting `v` for the hole. -/
def SegOf (K : Kont) (E : Expr) (γ : List Val) : Prop :=
  ∀ v : Val, K.plug (.val v) = substAll (v :: γ) E

/-- **Step 0.** The fundamental lemma for a stack segment with a hole, at every assignment. -/
theorem segment_fundamental {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr} {B : VTy} {C : CTy}
    (hE : CDerives Δ (⟨B, true⟩ :: Γ) E (.comp C)) {K : Kont} {γ : List Val}
    (hK : SegOf K E γ) {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {v : Val}
    {ρv ργ ρ : WRes} (hv : vC true B ls δ v ρv) (hγ : gDenC ls δ Γ γ ργ)
    (hc : ResU.CompS ρv ργ ρ) : cC C ls δ (K.plug (.val v)) ρ := by
  rw [hK v]
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hγ
  exact fundamentalC hE δ (v :: γ) ls ρ hδ
    (gDenC_mk (by simpa using hlen) ⟨ρv, ργ, hc, hv, hgs⟩)

end GhostEnd
