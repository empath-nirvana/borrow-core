import TypedCaseProof.ClaimHandle
import Core.Chain.SI.LoanX.MainBridge
import Core.Chain.SI.LoanX.Algebra

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

/-- A proposed resource-aware Ref clause. The heap cell owns no ghost; the stored value
retains its COMPLETE semantic resource, including owned continuation claims. -/
def RefX (R : Val → XProp) (p : Val) (x : XRes) : Prop :=
  ∃ (a : Loc) (v : Val) (y : XRes), p = Val.loc a ∧
    CompX (ResU.single a (CellU.ownOf v),0) y x ∧ R v y

def liftVal (R : Val → WRes → Prop) : Val → XProp := fun v x => x.2 = 0 ∧ R v x.1

/-- Exact actual-main Ref clause recovery at ZERO protocol resource. This includes
R=vN(U C), without claiming any erwpX→current-WP execution equivalence. -/
theorem RefX_zero_iff (A : VTy) (δ : BoCa.Lifetime.LSub) (Θ : LocTy) (n : Nat)
    (p : Val) (ρ : WRes) :
    RefX (liftVal (fun v r => vN (ℍ := ℍ) A δ Θ n v r)) p (ρ,0) ↔
      vN (ℍ := ℍ) (.ref A) δ Θ n p ρ := by
  constructor
  · rintro ⟨a,v,y,hp,hc,_,hR⟩
    exact ⟨a,v,y.1,hp,hc.1,hR⟩
  · rintro ⟨a,v,r,hp,hc,hR⟩
    exact ⟨a,v,(r,0),hp,⟨hc,by simp⟩,rfl,hR⟩

/-- Heap storage cannot hide or discard a positive ghost assertion of the payload. -/
theorem RefX_preserves_owned {R : Val → XProp} {J : GRes → Prop} {p : Val} {x : XRes}
    (hJ : ∀ v y, R v y → J y.2) (hr : RefX R p x) : J x.2 := by
  obtain ⟨a,v,y,_,hc,hR⟩ := hr
  have he : x.2 = y.2 := by simpa using hc.2
  rw [he]
  exact hJ v y hR

theorem RefX_intro {R : Val → XProp} {v : Val} {x : XRes} (hR : R v x)
    (a : Loc) {ρ : WRes} (hc : ResU.CompS (ResU.single a (CellU.ownOf v)) x.1 ρ) :
    RefX R (Val.loc a) (ρ,x.2) :=
  ⟨a,v,x,rfl,⟨hc,by simp⟩,hR⟩

#print axioms RefX_zero_iff
#print axioms RefX_preserves_owned
#print axioms RefX_intro
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
