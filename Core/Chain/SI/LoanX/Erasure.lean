import Core.Chain.SI.LoanX.ErwpX

/-! The ghost-free, unmasked loan run entails main's existing term run
when its postcondition also returns no ghost [spec §62]. -/
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core

def liftPostG (Q : PostG) : PostGX :=
  fun _ _ k ls t x => x.2 = 0 ∧ Q k ls t x.1

/-- One direction of the zero-protocol boundary. The X run has stronger frame
obligations; this theorem makes no converse claim. -/
theorem rwpGX_erases {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : rwpGX (ℍ := ℍ) Φ ∅ (liftPostG Q) n ls e (ρ,0)) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hh hc htw htag _hImm hlow hfd j μ' e' hj hs hfin
  have hstart : (0 + 0 : GRes).Valid := by simpa using GRes.valid_zero
  have hwf : WFC (0 + 0 : GRes).counted (ρf,0) := by
    simpa [GRes.counted] using wfc_empty (ρf,0)
  have hwx : WFC (0 + 0 : GRes).counted (ρ,0) := by
    simpa [GRes.counted] using wfc_empty (ρ,0)
  have hx := h (ρf,0) fρ ps μ hh hc hstart hwf hwx
    (maskShallow_locs_empty ρ) (maskAuth_empty 0) (maskOff_empty ρf)
    htw htag hlow hfd j μ' e' hj hs
  obtain ⟨M',ρ',ρp,fρ',fρ'p,π,g',gp,ps',ls',h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,
    h₉,h₁₀,h₁₁,h₁₂,_,_,_,_,_,_,hAuth,_,_,_,hPost⟩ := hx hfin
  obtain ⟨hg,hQ⟩ := hPost
  have hM : M' = ∅ := by
    change g' = 0 at hg
    rw [hg] at hAuth
    exact MaskAuth.zero hAuth
  subst M'
  have hUpd : UpdVNm Φ (n - j) ∅ ρ π := by simpa using h₇
  have hRec : RecAgree ∅ ps' ps := by simpa using h₁₁
  have hList : ListAgree ∅ ls' ls := by simpa using h₁₂
  exact ⟨ρ',ρp,fρ',fρ'p,π,ps',ls',h₁,h₂,h₃,h₄,h₅,h₆,
    (updVNm_empty_iff).mp hUpd,h₈,h₉,h₁₀,
    (RecAgree.empty_iff).mp hRec,(ListAgree.empty_iff).mp hList,hQ⟩

#print axioms rwpGX_erases
end BoCa.Fig16.LogRel.Core.Chain.SI
