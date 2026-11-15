import TypedCaseProof.Protocol
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub)
open BoCa.BoLo (Kont Head performE opPayload)
open Classical
/-- Opening now creates an owned registry obligation together with the physical loan. -/
theorem open_owned {m : Registry} {γ l : Loc} {κ β : Life}
    (hfresh : m γ = none) (P : Val → SPropS Loc Val β)
    (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty β⟩)
    {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec} {e : Expr}
    (h : erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) P hw),
        (reg (put m γ [.mut l β P]) + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ)) :
    erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.ownOf Val.unit), reg m + GRes.life κ) := by
  apply erwpX_ghost_update ((allocate m γ [.mut l β P] hfresh).frame (GRes.life κ))
    (by funext a; simp [reg, claim, permit]) (by funext a; simp [reg, claim, permit])
  refine erwpX_mutLoanOpen (l := l) (κ := κ) (β := β) (P := P)
    (hstr := ResU.inStratum_empty β) (hw := hw) (by simp [mask]) _ ls (ResU.comp_empty_right _) ?_
  intro ρ hρ
  have he := eq_of_compS_empty_left (ResU.CompS.comm hρ)
  simpa only [he] using h

/-- Matched closure consumes both fragments and changes the authoritative entry to retired. -/
theorem close_owned {m : Registry} {γ l : Loc} {κ β : Life}
    (P : Val → SPropS Loc Val β) (u : Val) {h : ResU.InStratum β (PMap.empty : WRes)}
    (hu : P u ⟨PMap.empty, h⟩) {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec} {e : Expr}
    (hbody : erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.ownOf u), reg (put m γ []) + GRes.life κ)) :
    erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.mutOf β u PMap.empty h P hu),
        (reg m + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ) := by
  apply erwpX_ghost_update ((close m γ [.mut l β P]).frame (GRes.life κ))
    (by funext a; simp [reg, claim, permit]) (by funext a; simp [reg, claim, permit])
  refine erwpX_mutLoanEnd (l := l) (κ := κ) (β := β) (P := P)
    (hstr := h) (hw := hu) (by simp [mask]) _ ls (ResU.comp_empty_right _) ?_
  intro ρ hρ
  have he := eq_of_compS_empty_left (ResU.CompS.comm hρ)
  simpa only [he] using hbody

/-- Real stop rule carrying positive ghost ownership. -/
theorem claim_perform {Φ : LocFam} {M : Mask} {T : OpTabX} {Q : PostX}
    {name : UInt32} {J : UInt32 → GRes → Prop} {n : Nat} {ls : List SRec}
    (K : Kont) {m i : UInt32} {v : Val} {en : OpEntX} {x : XRes}
    (hK : K.HasHnd m = false) (hT : T m i = some en)
    (h : sepX (en.PA n ls v)
      (fun y => (m = name → J i y.2) ∧
        contShareX en n ls K (erwpXC (ℍ := ℍ) Φ (claimTable T name J) Q n M) y) x) :
    erwpX (ℍ := ℍ) Φ M (claimTable T name J) Q n ls
      (K.plug (performE (.val (opPayload m i v)))) x := by
  rw [erwpX_eq]
  refine rwpGX_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) ?_
  intro C
  exact Or.inr ⟨K,m,i,v,en,rfl,hK,hT,Or.inr rfl,h⟩

def borrowOut (l : Loc) : Expr := performE (.val (opPayload 7 0 (Val.loc l)))

theorem out_opened (m : Registry) (Θ : LocTy) (γ l : Loc) (κ β : Life)
    (hs : WorldSat m Θ) (hm : m γ = some [unitLoan l β]) (n : Nat) (ls : List SRec) :
    erwpX (ℍ := ℍ) phi (mask l κ)
      (claimTable (loanTab γ) 7 (fun _ => Ownγ γ)) (scalarPost γ l κ) n ls (borrowOut l)
      (ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β)
        (unitFamily β 0) ⟨rfl,rfl⟩),
        (reg m + claim γ [unitLoan l β] + permit γ [unitLoan l β]) + GRes.life κ) := by
  refine claim_perform (en := loanEntry γ) Kont.hole rfl (by simp [loanTab]) ?_
  refine ⟨_,PMap.empty,reg m + permit γ [unitLoan l β],claim γ [unitLoan l β] + GRes.life κ,
    ResU.comp_empty_right _,?_,?_,?_,?_⟩
  · simp only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm]
  · exact ⟨m,Θ,unitLoan l β,hs,hm,⟨Val.unit,ResU.inStratum_empty β,⟨rfl,rfl⟩,rfl,rfl⟩,rfl⟩
  · intro _; exact ⟨l,β,by simp [claim]⟩
  · constructor
    · intro he; cases he
    · intro ls' hls
      have he : ls' = ls := hls
      subst ls'
      constructor
      · intro k hk w y z hB hc
        simp only [erwpXC,hk,if_true]
        apply erwpX_ghost_valid
        intro hv
        obtain ⟨m',Θ',hs',d',hcell,hg⟩ := hB
        have hv' : (reg m' + claim γ [unitLoan l β] + permit γ [d'] + GRes.life κ).Valid := by
          rw [hc.2,hg] at hv
          simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hv
        have hd : unitLoan l β = d' := (List.cons.inj (match_return (GRes.Valid.left hv'))).1
        subst d'
        obtain ⟨u,h,hu,rfl,hy⟩ := hcell
        have heU : u = Val.unit := hu.1
        subst u
        have hzρ : z.1 = ResU.single l
            (CellU.mutOf β Val.unit PMap.empty h (unitFamily β 0) hu) :=
          (eq_of_compS_empty_left hc.1).trans hy
        have hzg : z.2 = (reg m' + claim γ [unitLoan l β] + permit γ [unitLoan l β]) + GRes.life κ := by
          rw [hc.2,hg]
          simp only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm]
        have hez : z = (ResU.single l (CellU.mutOf β Val.unit PMap.empty h (unitFamily β 0) hu),
          (reg m' + claim γ [unitLoan l β] + permit γ [unitLoan l β]) + GRes.life κ) := Prod.ext hzρ hzg
        rw [hez]
        apply close_owned (unitFamily β 0) Val.unit hu
        exact erwpX_val (fun _ => ⟨rfl,put m' γ [],Θ',hs'.close,by simp [put],rfl,
          l,Val.unit,PMap.empty,rfl,ResU.comp_empty_right _,rfl,rfl⟩)
      · intro he; exact (he rfl).elim

theorem borrowOut_owned (m : Registry) (Θ : LocTy) (γ l : Loc) (κ β : Life)
    (hfresh : m γ = none) (hs : WorldSat (put m γ [unitLoan l β]) Θ) (n : Nat) :
    erwpX (ℍ := ℍ) phi (mask l κ) (claimTable (loanTab γ) 7 (fun _ => Ownγ γ))
      (scalarPost γ l κ) n [] (borrowOut l)
      (ResU.single l (CellU.ownOf Val.unit),reg m + GRes.life κ) := by
  apply open_owned hfresh (unitFamily β 0) ⟨rfl,rfl⟩
  exact out_opened (put m γ [unitLoan l β]) Θ γ l κ β hs (by simp [put]) n []

#print axioms out_opened
#print axioms borrowOut_owned
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
