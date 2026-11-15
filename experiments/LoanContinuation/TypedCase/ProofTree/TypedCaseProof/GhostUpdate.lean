import TypedCasePort.HandleX

/-! Generic registry-ghost updates inside the existing masked execution relation.
Updates preserve lifetime counts and mutable masking authorities. No execution rule is assumed.
-/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- Any frame-preserving registry update transports an X run backwards. -/
theorem rwpGX_ghost_update {g h : GRes}
    (hup : ∀ f, (f + g).Valid → (f + h).Valid)
    (htok : g.tok = h.tok) (hxm : g.xm = h.xm)
    {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (hrun : rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, h)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hma hoff htw htag hlow hfd j μ' e' hj hs
  have hC : (xf.2 + h).counted = (xf.2 + g).counted := by
    ext α
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, ← htok]
  have hwf' : WFC (xf.2 + h).counted xf := by rwa [hC]
  have hwx' : WFC (xf.2 + h).counted (ρ, h) := by
    intro α hα hcar
    rw [hC] at hα
    have hh := hwx α hα hcar
    change 0 < h.tok α
    rw [← htok]
    exact hh
  have hma' : MaskAuth M h := by
    intro l a ha
    have hh := hma l a ha
    cases a <;> simpa only [Auth.Held, ← htok, ← hxm] using hh
  have hr := hrun xf fρ ps μ hf hc (hup xf.2 hv) hwf' hwx' hsh hma' hoff
    htw htag hlow hfd j μ' e' hj hs
  refine ⟨hr.1, fun hfin => ?_⟩
  simpa only [EndOKX, Prod.fst, Prod.snd, hC] using hr.2 hfin

/-- The same update at the recursive effectful relation, for arbitrary stop tables and posts. -/
theorem erwpX_ghost_update {g h : GRes}
    (hup : ∀ f, (f + g).Valid → (f + h).Valid)
    (htok : g.tok = h.tok) (hxm : g.xm = h.xm)
    {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (hrun : erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, h)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq] at hrun ⊢
  exact rwpGX_ghost_update hup htok hxm hrun

#print axioms rwpGX_ghost_update
#print axioms erwpX_ghost_update
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
end
