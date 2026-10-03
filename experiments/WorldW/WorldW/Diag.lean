import WorldW.Wp

/-!
# WorldW — the frozen-list diagnostic (DESIGN §3.4, checkpoint 3)

**World: the W-draft, at Core's `ptoMutS`.** A diagnostic; it draws no conclusion alone. Its
distinguishing input need not arise, so a refutation of it measures our `ptoMutS`'s predicate
equality, not OQ-9 (a).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- After an older 6.64 frame closes, a younger `Mut` view of another place is still the view
`ptoMutS` reads at the shorter list. -/
def MutViewSurvivesOlderClose (T₃ : LifeVar → VTy) : Prop :=
  ∀ (ℓ₃ : BoCa.Loc) (α₃ : Life) (x₁ : LifeVar) (δ : LSub) (p₂ : FrameRec) (α₂ : Life)
    (ls ls' : List SRec) (ρ : WRes),
    (∀ x, x ∈ ls' ↔ (x ∈ ls ∧ ¬ LinOf (.imm (p₂, α₂)) x)) →
    ptoMutS ℓ₃ α₃ ls (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ →
    ptoMutS ℓ₃ α₃ ls' (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ

end WorldW

end
