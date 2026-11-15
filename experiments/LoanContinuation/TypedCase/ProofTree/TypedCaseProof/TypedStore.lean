import TypedCaseProof.Execution
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open Classical
open BoCa.BoLo (Kont Head performE opPayload freeE hndE hndVal)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem parkTab_entry {γ : Loc} {m i : UInt32} {en : OpEntX}
    (h : parkTab γ m i = some en) : m = 8 ∧ i = 0 ∧ en = parkEntry γ := by
  unfold parkTab at h
  split at h
  · rename_i hm
    exact ⟨hm.1, hm.2, (Option.some.inj h).symm⟩
  · cases h

theorem parkTab_down (γ : Loc) : (parkTab γ).Down where
  pa := by
    intro m i en ht k ls v x h
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    exact h
  fin := by
    intro m i en P ht hP
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    cases hP
  wcl := by
    intro m i en ht ls ls' x₁ x₂ x hc h
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    exact h

def storedClause : Val := .lam (.letpair (.var 0)
  (.app (.app (storePark (.var 0)) (.val (Val.inj₁ .unit))) (.var 1)))

/-- Typed retrieval consumes the real storage cell, keeps the U payload's owned ghost,
and invokes its admitted-world application theorem. -/
theorem typed_retrieve_resume {γ : Loc} {M : Mask} {Q : PostX} (hQ : Q.Down)
    {k n : Nat} {ls : List SRec} {a : Loc} {w : Val} {ρloan ρref ρall : WRes}
    {gloan gref : GRes} (hr : ScalarRef (ℍ := ℍ) γ M Q k ls (Val.loc a) (ρref,gref))
    {m : Registry} {Θ : LocTy} (hs : WorldSat m Θ)
    (hret : ReturnedAt γ m (n - 1) ls w (ρloan,gloan))
    (hc : ResU.CompS ρloan ρref ρall) (hi : n - 1 < k) :
    erwpX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q n ls
      (((Kont.appL (.appL .hole (Val.inj₁ .unit)) w).comp
        (.seq .hole (freeE (.val (Val.loc a))))).plug (.val Val.unit))
      (ρall,gloan + gref) := by
  apply erwpX_ghost_valid
  intro hv
  obtain ⟨s,kv,xk,hp,hstore,hU⟩ := hr
  have he : a = s := by
    have hh := congrArg Subtype.val hp
    simpa [Val.loc] using hh
  subst s
  have hg : gref = xk.2 := by simpa using hstore.2
  obtain ⟨ρbody,hbody,hown⟩ := compS_reassoc hstore.1 (ResU.CompS.comm hc)
  apply storePark_finish phi_down (opTableX_local (parkTab γ))
    (opTableX_down (parkTab_down γ)) hQ
    (.appL (.appL .hole (Val.inj₁ .unit)) w) a kv hown
  have hvalid : (xk.2 + gloan).Valid := by
    change (gloan + gref).Valid at hv
    simpa only [hg,GRes.add_comm] using hv
  have hh := (ScalarU_apply hU hi hs hret
    (z := (ρbody,xk.2 + gloan)) ⟨hbody,rfl⟩ hvalid).2
  simpa only [hg,GRes.add_comm,Kont.plug] using hh

/-- The clause's input comes from real typed capture: a positive claim AND the derived
execution obligation. It constructs ScalarU, then a compositional ScalarRef at allocation,
keeps it through the second stop, and retrieves/applies it at the returned typed world. -/
theorem storedClause_typed (γ : Loc) (M : Mask) (Q : PostX) (hQ : Q.Down)
    (k : Nat) (ls : List SRec) (v kv : Val) (x : XRes)
    (hx : sepX ((loanEntry γ).PA k ls v)
      (fun y => Ownγ γ y.2 ∧ KapRelX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q
        (loanEntry γ) k ls kv y) x) :
    erwpX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q k ls
      (.app storedClause.1 (.pair v.1 kv.1)) x := by
  cases k with
  | zero => exact erwpX_zero
  | succ k =>
    obtain ⟨ρ,g⟩ := x
    obtain ⟨ρloan,ρk,ga,gk,hc,hg,hA,ho,hK⟩ := hx
    change g = ga + gk at hg
    have hU : ScalarU (ℍ := ℍ) γ M Q (k + 1) ls kv (ρk,gk) := ScalarU_of_capture ho hK
    obtain ⟨m,Θ,d,hs,hmd,hcell,hga⟩ := hA
    change ga = reg m + permit γ [d] at hga
    apply erwpX_ghost_valid
    intro hvalid
    have hreg : (reg m + gk).Valid := GRes.Valid.left
      (show ((reg m + gk) + permit γ [d]).Valid by
        change g.Valid at hvalid
        rw [hg,hga] at hvalid
        simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hvalid)
    obtain ⟨l,β,howned,hkey⟩ := owned_key hs hreg ho
    refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) hQ
      (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v kv)) rfl .hole) ?_
    refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) hQ
      (fun μ => step1Only_plug (Head.letpair μ v kv _) rfl .hole) ?_
    have hh := storePark_compat (ℍ := ℍ) phi_down (M := M)
      (opTableX_local (parkTab γ)) (opTableX_down (parkTab_down γ)) hQ
      (.appL (.appL .hole (Val.inj₁ .unit)) v) kv
      (n := k + 1) (ls := ls) (ρ := ρ) (g := g) (fun a ρheap ha => by
        obtain ⟨ρref,hinside,houtside⟩ := compS_reassoc hc (ResU.CompS.comm ha)
        have hRef : ScalarRef (ℍ := ℍ) γ M Q (k + 1) ls (Val.loc a) (ρref,gk) :=
          RefX_intro hU a (ResU.CompS.comm hinside)
        refine erwpX_perform_same (en := parkEntry γ)
          ((Kont.appL (.appL .hole (Val.inj₁ .unit)) v).comp
            (.seq .hole (freeE (.val (Val.loc a))))) rfl (by simp [parkTab]) ?_
        refine ⟨PMap.empty,ρheap,reg m,permit γ [d] + gk,compS_empty_left _,?_,?_,?_⟩
        · simpa only [hga,GRes.add_assoc] using hg
        · exact ⟨rfl,rfl,m,Θ,hs,rfl,l,β,howned⟩
        · constructor
          · intro he; cases he
          · intro ls' hls
            have he : ls' = ls := hls
            subst ls'
            constructor
            · intro j hj w y z hB hcz
              simp only [erwpXC,hj,if_true]
              obtain ⟨rfl,hy,m',Θ',hs',hgy⟩ := hB
              have hρ : z.1 = ρheap := by
                have hczρ : ResU.CompS ρheap PMap.empty z.1 := by simpa only [hy] using hcz.1
                exact eq_of_compS_empty_left (ResU.CompS.comm hczρ)
              have hg' : z.2 = (reg m' + permit γ [d]) + gk := by
                rw [hcz.2,hgy]
                simp only [GRes.add_assoc,GRes.add_comm]
              have hz : z = (ρheap,(reg m' + permit γ [d]) + gk) := Prod.ext hρ hg'
              rw [hz]
              exact typed_retrieve_resume hQ hRef hs' ⟨d,hcell,rfl⟩ houtside (by omega)
            · intro he; exact (he rfl).elim)
    simpa [storedClause,storePark,storeParkBody,park8E,Expr.subst,Expr.shift,
      Expr.val,Val.lam,Val.pair,Val.shift,Val.inj₁,Val.unit,Val.i32,freeE,performE,opPayload,
      Kont.plug,CancelIntercept.subst_shift_one] using hh

#print axioms typed_retrieve_resume
#print axioms storedClause_typed
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
