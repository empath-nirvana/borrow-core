import Core.Chain.SI.HandleX

/-!
# Stored mutable-loan experiment

Compile against cross-821 at bbf8f16af3c27646c85384d1dba3f5e9f1050ce3.
This file exercises existing erwpX rules; it adds no execution or typing rule.

The input already owns one cell, its mutable-loan mask, and authority. The handler really
captures a linear continuation, stores it in a heap cell, allocates/frees another cell,
retrieves the continuation, and resumes with the exact borrowed cell. The final postcondition
recovers the original ownership; the authority and mask remain. This is a relation-level
execution proof, separate from the proposed typed-world interpretation in TypedLoanOrder.lean.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.LoanBridgeProbe
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Kont performE opPayload)

def pred (β : Life) : Val → SPropS Loc Val β := fun _ _ => True

def borrowed (l : Loc) (β : Life) : WRes :=
  ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) (pred β) trivial)

def mask (l : Loc) (κ : Life) : Mask := {(l, Auth.mloan κ)}
def phi : LocFam := fun _ => none

def exactBorrow (l : Loc) (β : Life) : Nat → List SRec → Val → XProp :=
  fun _ _ v x => v = Val.loc l ∧ x.1 = borrowed l β ∧ x.2 = 0

def entry (l : Loc) (β : Life) : OpEntX where
  q := .lin
  remask := false
  PA := exactBorrow l β
  PB := exactBorrow l β
  fin := none
  wc := fun ls ls' _ => ls' = ls

def table (l : Loc) (β : Life) : OpTabX := fun m i =>
  if m = 7 ∧ i = 0 then some (entry l β) else none

def post (l : Loc) (κ _β : Life) : PostX := fun _ _ _ v x =>
  v = Val.loc l ∧ x.1 = ResU.single l (CellU.ownOf Val.unit) ∧ x.2 = GRes.life κ

def borrowOut (l : Loc) : Expr := performE (.val (opPayload 7 0 (Val.loc l)))

theorem borrowOutX (l : Loc) (κ β : Life) (n : Nat) :
  erwpX (ℍ := ℍ) phi (mask l κ) (opTableX (table l β)) (post l κ β)
    n [] (borrowOut l) (ResU.single l (CellU.ownOf Val.unit), GRes.life κ) := by
  refine erwpX_mutLoanOpen (l := l) (κ := κ) (v := Val.unit) (β := β) (hstr := ResU.inStratum_empty β) (P := pred β) (hw := trivial)
    (by simp [mask]) _ [] (ResU.comp_empty_right _) ?_
  intro ρm hρm
  have hρ : ρm = borrowed l β := eq_of_compS_empty_left (ResU.CompS.comm hρm)
  subst ρm
  rw [erwpX_eq]
  refine rwpGX_here (final_opPlug (K := .hole) (r := false)
    (payloadName_opPayload 7 0 (Val.loc l)) (by simp [OpFree, Kont.HasHnd])) ?_
  intro C
  right
  refine ⟨Kont.hole, 7, 0, Val.loc l, entry l β, rfl, rfl,
    by simp [table], Or.inr rfl, borrowed l β, PMap.empty, 0, GRes.life κ,
    ResU.comp_empty_right _, by simp, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · constructor
    · intro h; cases h
    · intro ls' hls
      have : ls' = [] := hls
      subst ls'
      constructor
      · intro k hk w y z hB hcomp
        rcases hB with ⟨rfl, hy, hyg⟩
        rcases hcomp with ⟨hc, hg⟩
        have hz : z.1 = borrowed l β := by rw [hy] at hc; exact eq_of_compS_empty_left hc
        have hzg : z.2 = GRes.life κ := by simpa [hyg] using hg
        simp only [erwpXC, hk, if_true]
        have heq : z = (borrowed l β, GRes.life κ) := Prod.ext hz hzg
        rw [heq]
        refine erwpX_mutLoanEnd (l := l) (κ := κ) (β := β)
          (hstr := ResU.inStratum_empty β) (P := pred β) (hw := trivial)
          (by simp [mask]) _ [] (ResU.comp_empty_right _) ?_
        intro ρo ho
        have hρo : ρo = ResU.single l (CellU.ownOf Val.unit) :=
          eq_of_compS_empty_left (ResU.CompS.comm ho)
        exact erwpX_val (fun _ => ⟨rfl, hρo, rfl⟩)
      · intro h; exact False.elim (h rfl)

theorem answer_inhabited (l : Loc) (β : Life) (k : Nat) (ls : List SRec) :
    (entry l β).PB k ls (Val.loc l) (borrowed l β, 0) := ⟨rfl, rfl, rfl⟩

theorem resume_world_allowed (l : Loc) (β : Life) (ls : List SRec) (x : XRes) :
    (entry l β).wc ls ls x := rfl

#print axioms borrowOutX
#print axioms answer_inhabited
#print axioms resume_world_allowed
end BoCa.Fig16.LogRel.Core.Chain.SI.LoanBridgeProbe

namespace BoCa.Fig16.LogRel.Core.Chain.SI.StoredLoanProbe
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LoanBridgeProbe
open BoCa.BoLo (Kont Head freeE hndE hndVal)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- Store a value, allocate and release a different cell, then destructively retrieve it. -/
def storeWaitBody : Expr :=
  .seq (freeE (.app (.val (.prim .alloc)) (.val Val.unit))) (freeE (.var 0))

def storeWait (e : Expr) : Expr :=
  .app (.val (.lam storeWaitBody)) (.app (.val (.prim .alloc)) e)

theorem phi_down : phi.Down := fun _ _ _ h => by cases h

/-- A heap round trip preserves the resources carried by the stored value. -/
theorem storeWait_compat {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX}
    (hL : Tb.Local) (hD : Tb.Down) {Q : PostX} (hQ : Q.Down)
    (K : Kont) (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes} {g : GRes}
    (h : erwpX (ℍ := ℍ) Φ M Tb Q (n - 1 - 1 - 1 - 1) ls (K.plug v.1) (ρ, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (K.plug (storeWait v.1)) (ρ, g) := by
  change erwpX Φ M Tb Q n ls
    (K.plug ((Kont.appR (.val (.lam storeWaitBody)) .hole).plug
      (.app (.val (.prim .alloc)) v.1))) (ρ, g)
  rw [← Kont.plug_comp]
  refine erwpX_alloc hΦ hL _ v (fun a ρa ha => ?_)
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hD hQ (fun μ => step1Only_plug (Head.beta μ storeWaitBody (Val.loc a)) rfl K) ?_
  change erwpX Φ M Tb Q (n - 1) ls
    (K.plug ((Kont.seq (.appR (.val (.prim .free)) .hole) (freeE (.val (Val.loc a)))).plug
      (.app (.val (.prim .alloc)) (.val Val.unit)))) (ρa, g)
  rw [← Kont.plug_comp]
  refine erwpX_alloc hΦ hL _ Val.unit (fun b ρb hb => ?_)
  rw [Kont.plug_comp]
  change erwpX Φ M Tb Q (n - 1 - 1) ls
    (K.plug ((Kont.seq .hole (freeE (.val (Val.loc a)))).plug (freeE (.val (Val.loc b))))) (ρb, g)
  rw [← Kont.plug_comp]
  refine erwpX_free hΦ hL _ b Val.unit hb ?_
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K) ?_
  exact erwpX_free hΦ hL K a v ha h

#print axioms storeWait_compat

def storedClause : Val := .lam (.letpair (.var 0)
  (.app (.app (storeWait (.var 0)) (.val (Val.inj₁ .unit))) (.var 1)))

def noOps : OpTabX := fun _ _ => none

theorem noOps_down : noOps.Down where
  pa := by intros; contradiction
  fin := by intros; contradiction
  wcl := by intros; contradiction

theorem post_down (l : Loc) (κ β : Life) : (post l κ β).Down := fun _ _ _ _ _ h => h

theorem storedClause_compat (l : Loc) (κ β : Life) (M : Mask) (k : Nat)
    (ls : List SRec) (v kv : Val) (x : XRes)
    (hx : sepX ((entry l β).PA k ls v)
      (KapRelX (ℍ := ℍ) phi M (opTableX noOps) (post l κ β) (entry l β) k ls kv) x) :
    erwpX (ℍ := ℍ) phi M (opTableX noOps) (post l κ β) k ls
      (.app storedClause.1 (.pair v.1 kv.1)) x := by
  cases k with
  | zero => exact erwpX_zero
  | succ k =>
    obtain ⟨ρ, g⟩ := x
    obtain ⟨ρa, ρk, ga, gk, hc, hg, hA, hK⟩ := hx
    refine erwpX_det phi_down (opTableX_down noOps_down) (post_down l κ β)
      (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v kv)) rfl .hole) ?_
    refine erwpX_det phi_down (opTableX_down noOps_down) (post_down l κ β)
      (fun μ => step1Only_plug (Head.letpair μ v kv _) rfl .hole) ?_
    have hresume : erwpX (ℍ := ℍ) phi M (opTableX noOps) (post l κ β)
        (k + 1 - 1 - 1 - 1 - 1) ls (.app (.app kv.1 (.val (Val.inj₁ .unit))) v.1) (ρ, g) := by
      exact hK ls rfl _ (by omega) v (ρa, ga) (ρ, g) hA
        ⟨ResU.CompS.comm hc, hg.trans (GRes.add_comm ga gk)⟩
    have hh := storeWait_compat phi_down (opTableX_local noOps)
      (opTableX_down noOps_down) (post_down l κ β)
      (.appL (.appL .hole (Val.inj₁ .unit)) v) kv hresume
    simpa [storedClause, storeWait, storeWaitBody, Expr.subst, Expr.shift, Expr.val,
      Val.lam, Val.pair, Val.shift, Val.inj₁, Val.unit, freeE, Kont.plug,
      CancelIntercept.subst_shift_one] using hh

#print axioms storedClause_compat

theorem table_entry {l : Loc} {β : Life} {m i : UInt32} {en : OpEntX}
    (h : table l β m i = some en) : m = 7 ∧ i = 0 ∧ en = entry l β := by
  unfold table at h
  split at h
  · rename_i hm
    exact ⟨hm.1, hm.2, (Option.some.inj h).symm⟩
  · cases h

theorem table_down (l : Loc) (β : Life) : (table l β).Down where
  pa := by
    intro m i en ht k ls v x h
    obtain ⟨_, _, rfl⟩ := table_entry ht
    exact h
  fin := by
    intro m i en P ht hP
    obtain ⟨_, _, rfl⟩ := table_entry ht
    cases hP
  wcl := by
    intro m i en ht ls ls' x₁ x₂ x hc h
    obtain ⟨_, _, rfl⟩ := table_entry ht
    exact h

def handler : Val := hndVal 7 (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)

def storedProgram (l : Loc) : Expr := hndE handler (borrowOut l)

/-- A real must-resume handler stores the captured continuation in the heap, performs an
unrelated allocate/free, retrieves the continuation and resumes with the loan returned.
Both the capture cell and storage cells are consumed; the original ownership is recovered. -/
theorem storedProgram_erwpX (l : Loc) (κ β : Life) (n : Nat) :
    erwpX (ℍ := ℍ) phi (mask l κ) (opTableX noOps) (post l κ β)
      n [] (storedProgram l) (ResU.single l (CellU.ownOf Val.unit), GRes.life κ) := by
  refine erwpX_handle phi_down (table l β) noOps (table_down l β) noOps_down 7
    (fun m i hm => ?_) (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)
    (post l κ β) (post l κ β) (post_down l κ β)
    (fun i en ht => ?_) (fun i en ht => ?_) (fun M C k ls v x h => ?_)
    (fun i en ht => ?_) n (mask l κ) [] (borrowOut l)
    (ResU.single l (CellU.ownOf Val.unit), GRes.life κ) (borrowOutX l κ β n)
  · simp [table, noOps, hm]
  · obtain ⟨_, _, rfl⟩ := table_entry ht
    exact ⟨Or.inl rfl, rfl⟩
  · obtain ⟨_, rfl, rfl⟩ := table_entry ht
    rfl
  · refine erwpX_det phi_down (opTableX_down noOps_down) (post_down l κ β)
      (fun μ => step1Only_plug (Head.beta μ (.var 0) v) rfl .hole) ?_
    exact erwpX_val (fun _ => h)
  · obtain ⟨_, rfl, rfl⟩ := table_entry ht
    refine ⟨storedClause, ?_, fun M k ls v kv x hx => storedClause_compat l κ β M k ls v kv x hx⟩
    simp [BoCa.BoLo.clauseAt, Val.pair, storedClause, Val.lam, Expr.val, IsVal.lam]

#print axioms storedProgram_erwpX
end BoCa.Fig16.LogRel.Core.Chain.SI.StoredLoanProbe

end
