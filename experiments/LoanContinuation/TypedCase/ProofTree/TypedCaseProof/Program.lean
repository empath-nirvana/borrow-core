import TypedCaseProof.TypedStore
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub)
open BoCa.BoLo (Kont Head hndE hndVal)
open Classical
theorem loanTab_caught {γ : Loc} {i : UInt32} {en : OpEntX}
    (h : loanTab γ 7 i = some en) : i = 0 ∧ en = loanEntry γ := by
  by_cases hi : i = 0
  · subst i
    have he : loanEntry γ = en := Option.some.inj (by simpa [loanTab] using h)
    exact ⟨rfl,he.symm⟩
  · simp [loanTab,parkTab,hi] at h

theorem loanTab_down (γ : Loc) : (loanTab γ).Down where
  pa := by
    intro m i en ht k ls v x h
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; exact h
    · exact (parkTab_down γ).pa m i en ht k ls v x h
  fin := by
    intro m i en P ht hp
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; cases hp
    · exact (parkTab_down γ).fin m i en P ht hp
  wcl := by
    intro m i en ht ls ls' x₁ x₂ x hc h
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; exact h
    · exact (parkTab_down γ).wcl m i en ht ls ls' x₁ x₂ x hc h

def handler : Val := hndVal 7 (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)
def storedProgram (l : Loc) : Expr := hndE handler (borrowOut l)

/-- One complete restricted typed scalar-loan case. The proof opens the owned claim,
uses real capture with positive ownership, constructs typed Ref/U at heap storage,
passes a second actual suspension, retrieves and invokes the typed U at an admitted
current-main world, and discharges the matching claim. Its final post uses actual vN. -/
theorem storedProgram_typed (m : Registry) (Θ : LocTy) (γ l : Loc) (κ β : Life)
    (hfresh : m γ = none) (hs : WorldSat (put m γ [unitLoan l β]) Θ) (n : Nat) :
    vN (ℍ := ℍ) (.ref .unit) LSub.empty Θ n (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) ∧
    erwpX (ℍ := ℍ) phi (mask l κ) (opTableX (parkTab γ)) (scalarPost γ l κ) n []
      (storedProgram l) (ResU.single l (CellU.ownOf Val.unit),reg m + GRes.life κ) := by
  refine ⟨⟨l,Val.unit,PMap.empty,rfl,ResU.comp_empty_right _,rfl,rfl⟩,?_⟩
  refine handle_claim_le phi_down n (loanTab γ) (parkTab γ) (loanTab_down γ) (parkTab_down γ)
    7 (fun _ => Ownγ γ) (fun m i hm => ?_)
    (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)
    (scalarPost γ l κ) (scalarPost γ l κ) (scalarPost_down γ l κ)
    (fun i en ht => ?_) (fun i en ht => ?_) (fun M C k hk ls v x h => ?_)
    (fun i en ht => ?_) n le_rfl (mask l κ) [] (borrowOut l)
    (ResU.single l (CellU.ownOf Val.unit),reg m + GRes.life κ)
    (borrowOut_owned m Θ γ l κ β hfresh hs n)
  · simp [loanTab,hm]
  · obtain ⟨_,rfl⟩ := loanTab_caught ht
    exact ⟨rfl,rfl⟩
  · obtain ⟨rfl,rfl⟩ := loanTab_caught ht
    rfl
  · refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) (scalarPost_down γ l κ)
      (fun μ => step1Only_plug (Head.beta μ (.var 0) v) rfl .hole) ?_
    exact erwpX_val (fun _ => h)
  · obtain ⟨rfl,rfl⟩ := loanTab_caught ht
    refine ⟨storedClause,?_,fun M k hk ls v kv x hx =>
      storedClause_typed γ M (scalarPost γ l κ) (scalarPost_down γ l κ) k ls v kv x hx⟩
    simp [BoLo.clauseAt,Val.pair,storedClause,Val.lam,Expr.val,IsVal.lam]

#print axioms loanTab_down
#print axioms storedProgram_typed
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
