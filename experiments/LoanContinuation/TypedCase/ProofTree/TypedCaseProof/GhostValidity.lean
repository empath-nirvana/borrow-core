import TypedCasePort.HandleX

noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The run itself supplies validity of its local ghost resource; clients need not assume it. -/
theorem rwpGX_ghost_valid {Φ : LocFam} {M : Mask} {Q : PostGX}
    {n : Nat} {ls : List SRec} {e : Expr} {x : XRes}
    (h : x.2.Valid → rwpGX (ℍ := ℍ) Φ M Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hma hoff htw htag hlow hfd j μ' e' hj hs
  exact h (GRes.Valid.right hv) xf fρ ps μ hf hc hv hwf hwx hsh hma hoff
    htw htag hlow hfd j μ' e' hj hs

/-- Registry agreement can be derived under the actual erwpX validity guard. -/
theorem erwpX_ghost_valid {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX}
    {n : Nat} {ls : List SRec} {e : Expr} {x : XRes}
    (h : x.2.Valid → erwpX (ℍ := ℍ) Φ M Tb Q n ls e x) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e x := by
  rw [erwpX_eq]
  apply rwpGX_ghost_valid
  intro hv
  have hh := h hv
  rwa [erwpX_eq] at hh

#print axioms rwpGX_ghost_valid
#print axioms erwpX_ghost_valid
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
end
