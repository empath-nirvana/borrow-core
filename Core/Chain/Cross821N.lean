import Core.Chain.PoolScopeN
import Core.Chain.CrossStopN
import Core.Chain.Hardest791N
import Core.Chain.SI.ILendCancelProg

/-!
# Cross-task lends across suspension, through `poolSchedAdequacyN`  `[spec §62]`

A task lends a cell it owns to a callback; the callback runs a scheduler scope
`(hnd HS e) (HS, [])` (`erwp_scopeV`, `Core/Chain/PoolScopeN.lean`) whose first task spawns a
child holding a borrow of the cell. The child holds the borrow across `park` while the task that
spawned it runs; the scope returns when its list is empty (every task it started ended or was
cancelled), which is the join; then the lend ends and the cell is freed.

* **`imm`, shared** (`rootI`, `rootIC`): the cell lent `imm` by `withborU dB c cbI`. The task `PI`
  spawns `CI = λ_. park (); !ℓ` with a copy of the borrow (6.116) and keeps the other; it reads
  `!ℓ` while `CI` is parked holding its copy, then parks (`rootI`: `CI` resumed, reads and ends)
  or cancels (`rootIC`: `CI`, the pool's top, cancelled while it holds the copy).
* **`mut`** (`rootM`, `rootMC`): the cell lent `mut` by `withborU dB c cbM`. The task `PM`
  spawns `CM = λ_. park (); ℓ := 7; forget ℓ` with the borrow itself and keeps nothing; `CM`
  holds the borrow across `park` and then writes through it (`rootM`), or is cancelled while it
  holds it (`rootMC`).

Under `HS` the child runs first (the spawn clause parks the spawner), its `park` resumes the
spawner and keeps the child beneath, so the spawner's next operation finds the child on the
pool's top.

Each root is one task of the top-level `HS`, at the table `TJN`, through
`poolSchedAdequacyN` (`progOfN_orDiverges`). The lend is the frame of one segment of that task
(`erwp_I_frame`, `erwp_M_frame`, at the empty table, lifted): the spawn, `park` and `cancel` of
the scope are handled inside the callback, so no stop leaves the lend. That is the restriction
`Core/Chain/CrossStopN.lean` shows forced: a stop that carries the borrow out of the lending
segment is refused by `↭` (`not_crossTaskILend`, `not_crossTaskMLend`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Cross821
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolSpawn
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolScope
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn (HS)
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs (parkE cancelE spawnE)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal clauseAt
  capTag ubindE)

set_option linter.unusedSimpArgs false

/-! ### Stops holding a resource that owns nothing -/

section Stops
variable {Φ : LocFam} {PS : Nat → List SRec → Val → WProp}

/-- A cancel run from a context with no finaliser, holding `R` that owns nothing. -/
theorem cancel_hold (K : Kont) (hKH : ∀ m, K.HasHnd m = false) (hKC : ∀ m, K.Catches m = false)
    {R : WRes} (hR : NoOwn R) (k : Nat) (ls : List SRec) :
    cancelOblN (ℍ := ℍ) Φ OpTabN.empty k ls (K.dead.plug (raiseE (.val (cancelVal none)))) R := by
  show erwp (ℍ := ℍ) Φ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) k ls _ _
  rw [dead_plain _ hKH (hKC 0), erwp_eq]
  exact rwpG_here (final_opPlug (r := true) (payloadName_cancelVal none) (hKC 0))
    (Or.inr (Or.inl ⟨_, none, pure_sep_mk ⟨rfl, hKC 0⟩
      ⟨PMap.empty, R, compS_empty_left _, emp_empty, hR⟩⟩))

/-- **A `park` or `cancel` holding `R`**, in a context with no handler and no catcher: resumed
at `()`, the context's run from `R`; cancelled, the cancel's `raise` owning nothing. -/
theorem erwp_stopHold {i : UInt32} (hi : tabOfN (ℍ := ℍ) Φ PS nP i = some (enParkN (ℍ := ℍ) Φ))
    (K : Kont) (hKH : ∀ m, K.HasHnd m = false) (hKC : ∀ m, K.Catches m = false) {R : WRes}
    (hR : NoOwn R) {Q : PostN} {n : Nat} {ls : List SRec}
    (hk : ∀ k', k' < n → ∀ ls', erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) Q k' ls'
      (K.plug (.val Val.unit)) R) :
    erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) Q n ls
      (K.plug (performE (.val (opPayload nP i Val.unit)))) R :=
  erwp_performG K (hKH nP) hi rfl (compS_empty_left _) ⟨rfl, rfl⟩ (fun h => by cases h)
    (fun ls' _ k' hk' w σB XB ⟨hw, hσ⟩ hXB => by
      subst hw hσ
      obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
      exact hk k' hk' ls')
    (fun ls' _ _ P hP => by cases hP; exact cancel_hold K hKH hKC hR _ _)

/-- A value, the resource owning nothing set aside. -/
theorem erwp_valDrop {Tb : TableN} {n : Nat} {ls : List SRec} (v : Val) {R : WRes}
    (hR : NoOwn R) : erwp (ℍ := ℍ) Φ Tb QVN n ls v.1 R :=
  erwp_garbage (compS_empty_left R) hR (erwp_val (v := v) rfl)

end Stops

/-! ### Case 1: the `imm` tasks -/

/-- `!x`. -/
def ldE (x : Expr) : Expr := .app (.val (.prim .load)) x

/-- The child, under the borrow's variable: `λ_. park (); !r`. -/
def CIv : Val := Val.lam (.seq parkE (ldE (.var 1)))

/-- The child at `ℓ`. -/
def CI (l : Loc) : Val := Val.lam (.seq parkE (ldE (.val (Val.loc l))))

/-- The rest of the spawner after its read: `park ()` (`b = false`) or `cancel ()` (`b = true`),
then `()`. -/
def tailE (b : Bool) : Expr := .seq (if b then cancelE else parkE) (.val Val.unit)

/-- **The spawner** at `ℓ`: `spawn (CI ℓ); !ℓ; tail`. -/
def PI (b : Bool) (l : Loc) : Expr :=
  .seq (spawnE (CI l)) (.seq (ldE (.val (Val.loc l))) (tailE b))

/-- The borrow `ℓ ↦ imm({A}, (), ∅)`. -/
abbrev VI (l : Loc) (A : Life) : WRes := CrossStop.viewI l A

/-- `!ℓ` through an `imm` cell, the cell kept as whatever `imm` cell `rwp_load_I` hands back. -/
theorem erwp_loadImm {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN}
    (K : Kont) (l : Loc) (A : Life) {n : Nat} {ls : List SRec}
    (hk : ∀ R : WRes, NoOwn R → erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (K.plug (.val Val.unit)) R) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug (ldE (.val (Val.loc l)))) (VI l A) := by
  refine erwp_bindR hΦ hL K (rwp_load_I ls l A (fun w _ => w = Val.unit) _ ⟨_, PMap.empty,
    ResU.comp_empty_right _, ⟨LSet.singleton A, Val.unit, PMap.empty, inStratum_empty A, rfl,
      rfl, le_refl _⟩, fun w ρc X hc hX => ?_⟩)
  obtain ⟨s, u', σ, hs, rfl, ⟨-, -, -, -, hw⟩, -⟩ := hc
  obtain rfl := eq_of_compS_empty_left hX
  subst hw
  exact hk _ (noOwn_single_imm l _ _ _ _)

section Child
variable {Φ : LocFam} {PS : Nat → List SRec → Val → WProp}

/-- **The `imm` child**, at any table `tabOfN Φ PS`: from its copy, `park` holding it, then the
read, then its answer with the copy set aside. -/
theorem childI_ok (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) (l : Loc)
    (A : Life) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (tabOfN (ℍ := ℍ) Φ PS)) QVN n ls (.app (CI l).1 (.val Val.unit))
      (VI l A) := by
  have hTD := opTableN_down (tabOfN_down (ℍ := ℍ) hΦ hPS)
  have hL := opTableN_local (tabOfN (ℍ := ℍ) Φ PS)
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.seq parkE (ldE (.val (Val.loc l))))) =
      (Kont.seq .hole (ldE (.val (Val.loc l)))).plug parkE := by
    simp [Kont.plug, Expr.subst, parkE, ldE, performE, opPayload, Val.pair, Val.i32, Val.unit,
      Val.loc, Expr.val, Val.prim]
  rw [e]
  refine erwp_stopHold (tabOfN_park _ _) _ (fun _ => rfl) (fun _ => rfl)
    (noOwn_single_imm l _ _ _ _) fun k' _ ls' => ?_
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact erwp_loadImm hΦ hL .hole l A fun R hR => erwp_valDrop Val.unit hR

/-- The child is a spawn payload at every index: verified at every indexed table from its
copy. -/
theorem childOKV_I (hΦ : Φ.Down) (l : Loc) (A : Life) (k : Nat) :
    ChildOKV (ℍ := ℍ) Φ (tabAtV (ℍ := ℍ) Φ) k (CI l) (VI l A) := fun j _ ls => by
  rw [tabAtV_eq]; exact childI_ok hΦ (spawnPAV_down _ _) l A j ls

end Child

/-- **The spawner at the scope's table `TJV`**: the spawn passes one copy of the borrow to the
child and keeps the other (6.116); resumed, it reads; then `park` or `cancel` holding its copy;
its answer with the copy set aside. -/
theorem PI_ok {Φ : LocFam} (hΦ : Φ.Down) (b : Bool) (l : Loc) (A : Life) (n : Nat)
    (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN (TJV (ℍ := ℍ) Φ)) QVN n ls (PI b l) (VI l A) := by
  have hTD := opTableN_down (TJV_down (ℍ := ℍ) hΦ)
  have hL := opTableN_local (TJV (ℍ := ℍ) Φ)
  set K₁ : Kont := .seq .hole (.seq (ldE (.val (Val.loc l))) (tailE b))
  have hKH : ∀ m, K₁.HasHnd m = false := fun _ => rfl
  have hKC : ∀ m, K₁.Catches m = false := fun _ => rfl
  show erwp (ℍ := ℍ) Φ _ _ _ _ (K₁.plug (performE (.val (opPayload nP 1 (CI l))))) _
  refine erwp_performG K₁ (hKH nP) (tabOfN_spawn _ _) rfl
    (compS_imm_dup l _ Val.unit PMap.empty (inStratum_empty A)) (childOKV_I hΦ l A n)
    (fun h => by cases h) (fun ls' _ k' _ w σB XB ⟨hw, hσ⟩ hXB => ?_)
    (fun ls' _ _ P hP => by cases hP; exact cancel_hold K₁ hKH hKC (noOwn_single_imm l _ _ _ _) _ _)
  subst hw hσ
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  show erwp (ℍ := ℍ) Φ _ _ _ _ ((Kont.seq .hole (tailE b)).plug (ldE (.val (Val.loc l)))) _
  refine erwp_loadImm hΦ hL _ l A fun R hR => ?_
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  have hstop : ∀ (i : UInt32), tabOfN (ℍ := ℍ) Φ (spawnPAV (ℍ := ℍ) Φ (tabAtV (ℍ := ℍ) Φ)) nP i =
      some (enParkN (ℍ := ℍ) Φ) → ∀ n' ls'', erwp (ℍ := ℍ) Φ (opTableN (TJV (ℍ := ℍ) Φ)) QVN n'
        ls'' (.seq (performE (.val (opPayload nP i Val.unit))) (.val Val.unit)) R :=
    fun i hi n' ls'' => erwp_stopHold hi (.seq .hole (.val Val.unit)) (fun _ => rfl)
      (fun _ => rfl) hR fun _ _ _ =>
        erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole)
          (erwp_valDrop Val.unit hR)
  cases b
  · exact hstop 0 (tabOfN_park _ _) _ _
  · exact hstop 2 (tabOfN_cancel _ _) _ _

/-! ### The lend around the scope, and the root -/

open BoCa.Fig16.Tree.Wp.Goal791 (dB letE allocE)
open BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791 (NF DB)

/-- **A run at the empty table is a run at every table**: it never stops. -/
theorem erwp_ofEmpty {Φ : LocFam} {T : OpTabN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) (fun k ls t Ψ Ψ' ρ _ h => ?_) n ls e ρ h
  rcases h with ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

theorem empty_ctxClosed (K : Kont) : OpTabN.empty.CtxClosed K :=
  fun _ _ _ _ h => by simp [OpTabN.empty] at h

/-- The scope's state: `HS` beside the empty list. -/
abbrev st₀ : Val := stateValN HS []

theorem HS_closed : closedAt 0 HS.1 = true := rfl
theorem st₀_closed : closedAt 0 st₀.1 = true := rfl

/-- The `imm` callback, under `λ_. λr.`: the scope `(hnd HS (spawn CIv; !r; tail)) (HS, [])`. -/
def cbI (b : Bool) : Val :=
  Val.lam (.lam (.app (hndE HS (.seq (spawnE CIv) (.seq (ldE (.var 0)) (tailE b)))) st₀.1))

theorem cbI_closed (b : Bool) : closedAt 0 (cbI b).1 = true := by
  cases b <;> rfl

/-- The callback run on the borrow: `cbI () ℓ`. -/
def cbIBody (b : Bool) (l : Loc) : Expr := .app (.app (.val (cbI b)) (.val .unit)) (.val (Val.loc l))

/-- The scope at `ℓ`. -/
def scopeI (b : Bool) (l : Loc) : Expr := .app (hndE HS (PI b l)) st₀.1

/-- The lender's end: the cell owned again. -/
def QI (l : Loc) : PostN := fun _ _ _ ρ => ∃ w, ptoOwn l w ρ

/-- **The `imm` lend**: `ℓ` lent `imm` at `A` (`erwp_I_frame` at the empty table, one segment) to
the callback, which runs the scope from the borrow (`erwp_scopeV`, `PI_ok`). -/
theorem lendI_ok {Φ : LocFam} (hΦ : Φ.Down) (b : Bool) (l : Loc) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (QI l) n ls (cbIBody b l)
      (ResU.single l (CellU.ownOf Val.unit)) := by
  obtain ⟨A, -⟩ := exists_fresh ls
  have hshape : vShape .unk ILendProg.δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk ILendProg.δ₀ := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := ⟨l, Val.unit, PMap.empty, .unk, ILendProg.δ₀⟩) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
  refine erwp_I_frame l .unk ILendProg.δ₀ hadm Val.unit ILendProg.PU (fun _ ρ h => ⟨h, trivial⟩)
    (fun _ _ _ _ h => h) (ILendProg.empty_ilendOK A) (fun _ _ _ _ _ _ h => h) n ls _
    PMap.empty _ PMap.empty _ (inStratum_empty A) (inStratum_empty A) rfl
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) ds hds (fun BI hBI => ?_)
  obtain rfl := eq_of_compS_empty_left hBI
  have hTD := opTableN_down OpTabN.empty_down
  have hQD : (IFPost l Val.unit ILendProg.PU A (QI l)).Down := fun _ _ _ _ h => h
  refine erwp_det hΦ hTD hQD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    (.appL .hole (Val.loc l))) ?_
  refine erwp_det hΦ hTD hQD (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
      (.app (hndE HS (.seq (spawnE CIv) (.seq (ldE (.var 0)) (tailE b)))) st₀.1))) =
      scopeI b l := by
    cases b <;>
    simp [Kont.plug, Expr.subst, Expr.shift, scopeI, PI, CI, CIv, tailE, ldE, hndE, spawnE,
      parkE, cancelE, performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Val.lam,
      Expr.val, Val.prim, Val.shift, subst_closedAt _ _ HS_closed (Nat.zero_le _),
      subst_closedAt _ _ st₀_closed (Nat.zero_le _)]
  rw [e]
  refine erwp_mono (Tb := opTableN OpTabN.empty) (Tb' := opTableN OpTabN.empty) (Q := QVN) (fun k ls' w ρ h => ?_) (opTableN_local _) n _ _ _
    (erwp_scopeV hΦ (PI_ok hΦ b l A n _))
  subst h
  refine ⟨fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩
  subst hl
  obtain rfl := eq_of_compS_empty_left hY
  have hv' : ρv = PMap.empty := hv
  subst hv'
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨_, rfl⟩

/-- `withborU dB ℓ cb`. -/
def WU (cb : Val) (l : Loc) : Expr :=
  .app (.app (.val (withborUV (.val dB))) (.val (Val.loc l))) (.val cb)

/-- What the lend answers: the pair, the cell owned again. -/
def QU (l : Loc) : PostN := fun _ _ v ρ => ∃ (b w : Val), v = Val.pair (Val.loc l) b ∧ ptoOwn l w ρ

theorem dB_closed : closedAt 0 dB.1 = true := rfl

/-- **`withborU dB ℓ cb`, its callback's run never stopping**: two steps to the callback under its
finaliser frame `then b. (ℓ, b) unwind dB ℓ` (`erwp_ubindClaim` at the empty table: no stop, so
no cancel run and no claim), then the pair. -/
theorem lendU_ok {Φ : LocFam} (hΦ : Φ.Down) {cb : Val} (l : Loc)
    (w₀ : Val) (n : Nat) (ls : List SRec)
    (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (QI l) n ls
      (.app (.app (.val cb) (.val .unit)) (.val (Val.loc l))) (ResU.single l (CellU.ownOf w₀))) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (QU l) n ls (WU cb l)
      (ResU.single l (CellU.ownOf w₀)) := by
  have hTD := opTableN_down OpTabN.empty_down
  have hQU : (QU l).Down := fun _ _ _ _ h => h
  refine erwp_det hΦ hTD hQU (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl
    (.appL .hole cb)) ?_
  refine erwp_det hΦ hTD hQU (fun μ => step1Only_plug (Head.beta μ _ cb) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 cb (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
      (thenE ((Expr.var 2).pair (Expr.var 0)) ((Expr.val dB).app (Expr.var 2))
        (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NF l) (DB l)) (.app (.app (.val cb) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NF, DB, Val.shift,
      Val.pair, Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt _ _ dB_closed (Nat.zero_le _)]
  rw [e₃]
  refine erwp_ubindClaim (T₁ := OpTabN.empty) (R := fun _ _ => False) hΦ OpTabN.empty_down
    OpTabN.empty_down (fun _ _ _ h => by simp [OpTabN.empty] at h)
    (fun _ _ _ h => by simp [OpTabN.empty] at h) (fun _ _ _ h => by simp [OpTabN.empty] at h)
    (NF l) (DB l) (fun _ _ _ h => h.elim) hQU (Qin := QI l) ?_ _ ls _ _ (erwp_ofEmpty h)
  rintro k' ls' v ρ ⟨w, rfl⟩
  refine erwp_det hΦ hTD hQU (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  simp [Kont.plug, Expr.subst, NF]
  exact erwp_val (v := Val.pair (Val.loc l) v) ⟨v, w, rfl, rfl⟩

/-- The root's body under its cell `c`: `let (c′, _) = withborU dB c cb in free c′`. -/
def RU (cb : Val) : Expr :=
  letE (.app (.app (.val (withborUV (.val dB))) (.var 0)) (.val cb))
    (.letpair (.var 0) (freeE (.var 1)))

/-- **The root**: `let c = alloc () in let (c′, _) = withborU dB c cb in free c′`. -/
def rootU (cb : Val) : Expr := letE (allocE (.val .unit)) (RU cb)

/-- **The root at the scheduler's table**, its callback's run never stopping: the cell allocated,
lent (`lendU_ok`), its pair taken apart and the cell freed, at the empty table, lifted. -/
theorem rootU_ok {Φ : LocFam} (hΦ : Φ.Down) {cb : Val} (hcb : closedAt 0 cb.1 = true)
    (h : ∀ l n ls, erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (QI l) n ls
      (.app (.app (.val cb) (.val .unit)) (.val (Val.loc l))) (ResU.single l (CellU.ownOf Val.unit)))
    {T : OpTabN} (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN T) QVN n ls (rootU cb) PMap.empty := by
  refine erwp_ofEmpty ?_
  have hTD := opTableN_down OpTabN.empty_down
  have hL := opTableN_local OpTabN.empty
  show erwp (ℍ := ℍ) Φ _ _ _ _ ((Kont.appR (.lam (RU cb)) .hole).plug
    (.app (.val (.prim .alloc)) (.val Val.unit))) _
  refine erwp_alloc hΦ hL (.appR (.lam (RU cb)) .hole) Val.unit (fun a σ₁ σ₂ ha hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  subst ha
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ (Val.loc a)) rfl
    .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc a) (RU cb)) =
      (Kont.appR (.lam (.letpair (.var 0) (freeE (.var 1)))) .hole).plug (WU cb a) := by
    simp [RU, WU, letE, Kont.plug, Expr.subst, subst_closedAt _ _ hcb (Nat.zero_le _),
      subst_closedAt _ _ (show closedAt 0 (withborUV (.val dB)).1 = true from rfl)
        (Nat.zero_le _), freeE, Val.prim, Expr.val]
  rw [e₁]
  have hKH : ∀ m, (Kont.appR (.lam (.letpair (.var 0) (freeE (.var 1)))) .hole).HasHnd m =
      false := fun m => by simp [Kont.HasHnd]
  have hKC : ∀ m, (Kont.appR (.lam (.letpair (.var 0) (freeE (.var 1)))) .hole).Catches m =
      false := fun m => by simp [Kont.Catches]
  refine erwp_bind hΦ _ hKH hKC (empty_ctxClosed _) (Q' := QU a) ?_ _ ls (WU cb a) _
    (lendU_ok hΦ a Val.unit _ ls (h a _ ls))
  rintro k'' ls'' v ρ ⟨b, w, rfl, rfl⟩
  simp only [Kont.plug]
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  simp [Kont.plug, Expr.subst]
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ (Val.loc a) b _) rfl
    .hole) ?_
  simp [Kont.plug, Expr.subst]
  show erwp (ℍ := ℍ) Φ _ _ _ _ (Kont.hole.plug (freeE (.val (Val.loc a)))) _
  exact erwp_free hΦ hL .hole a w ⟨_, PMap.empty, ResU.comp_empty_right _, rfl,
    erwp_val (v := w) rfl⟩

/-! ### Case 1: the programs -/

/-- The empty location family. -/
def Φe : LocFam := fun _ => none

theorem Φe_down : Φe.Down := fun _ _ _ h => by cases h

/-- `rootU (cbI b)`: the cell lent `imm` to the scope. -/
def rootI (b : Bool) : Expr := rootU (cbI b)

/-- **Case 1, the child resumed**: `progOf rootI false` is safe and leak-free or diverges. The
spawner lends its cell `imm`, spawns `CI` with a copy of the borrow inside the scope, reads `!ℓ`
while `CI` is parked holding its copy, then parks; `CI` is resumed, reads through its copy and
ends; the scope's list empties, the lend ends, and the cell is freed. -/
theorem crossImm : OrDiverges (ℍ := ℍ) (.app (hndE HS (rootI false)) st₀.1) :=
  progOfN_orDiverges Φe_down fun n =>
    rootU_ok Φe_down (cbI_closed false) (fun l n ls => lendI_ok Φe_down false l n ls) n []

/-- **Case 1, the child cancelled**: as `crossImm`, the spawner cancelling `CI`, the pool's top,
while `CI` is parked holding its copy of the borrow. -/
theorem crossImmC : OrDiverges (ℍ := ℍ) (.app (hndE HS (rootI true)) st₀.1) :=
  progOfN_orDiverges Φe_down fun n =>
    rootU_ok Φe_down (cbI_closed true) (fun l n ls => lendI_ok Φe_down true l n ls) n []

/-! ### Case 2: the `mut` tasks -/

open BoCa.Fig16.Tree.Wp.Goal791 (vField)
open BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791 (writeForget)

/-- The child, under the borrow's variable: `λ_. park (); r := 7; forget r`. -/
def CMv : Val := Val.lam (.seq parkE
  (.app (.lam (.app forget (.var 2))) (BoCa.Fig16.Tree.Wp.Goal791.storeE (.var 1) (.val vField))))

/-- The child at `ℓ`. -/
def CM (l : Loc) : Val := Val.lam (.seq parkE (writeForget l vField))

/-- **The spawner** at `ℓ`: `spawn (CM ℓ); tail`, the borrow passed to the child. -/
def PM (b : Bool) (l : Loc) : Expr := .seq (spawnE (CM l)) (tailE b)

/-- The borrow `ℓ ↦ mut(A, u, ∅, famF A j)`. -/
abbrev VM (l : Loc) (A : Life) (u : Val) (j : Nat) : WRes :=
  ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A) (famF A j) rfl)

section ChildM
variable {Φ : LocFam} {PS : Nat → List SRec → Val → WProp}

/-- **The write, then the borrow forgotten**, answering a value owning nothing
(`Hardest791.writeForget_ok`'s proof at `QVN`). -/
theorem writeForgetV_ok (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ)
    (l : Loc) (A : Life) (u v : Val) (j k : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (tabOfN (ℍ := ℍ) (Φ.set l A (famF A)) PS))
      QVN k ls (writeForget l v) (VM l A u j) := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hFl : Φ.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  have hTD := opTableN_down (tabOfN_down (ℍ := ℍ) hΦ' hPS)
  refine erwp_dump (opTableN_local _) k ls _ _ ?_
  refine erwp_bindR hΦ' (opTableN_local _) (.appR (.lam (.app forget (.val (Val.loc l)))) .hole)
    (rwp_M_antiFrame hΦ' hFl (ResU.comp_empty_right _) fun W X hW hX => ?_)
  obtain rfl := eq_of_compS_empty_left hW
  obtain rfl := eq_of_compS_empty_left hX
  refine rwp_store ls l u v _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, fun ρ₁ ρ₂ h₁ hc => ?_⟩
  subst h₁
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨v, PMap.empty, inStratum_empty A, rfl, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, fun X hX => ?_⟩
  obtain rfl := eq_of_compS_empty_left hX
  refine erwp_det hΦ' hTD (fun _ _ _ _ h => h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  refine erwp_det hΦ' hTD (fun _ _ _ _ h => h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨noOwn_single_mut l, rfl⟩

/-- **The `mut` child**, at any table `tabOfN`: from the borrow, `park` holding it, then the
write through it. -/
theorem childM_ok (hΦ : Φ.Down) (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) (l : Loc)
    (A : Life) (u : Val) (j n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (tabOfN (ℍ := ℍ) (Φ.set l A (famF A)) PS)) QVN
      n ls (.app (CM l).1 (.val Val.unit)) (VM l A u j) := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hTD := opTableN_down (tabOfN_down (ℍ := ℍ) hΦ' hPS)
  refine erwp_det hΦ' hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.seq parkE (writeForget l vField))) =
      (Kont.seq .hole (writeForget l vField)).plug parkE := by
    simp [Kont.plug, Expr.subst, parkE, writeForget, BoCa.Fig16.Tree.Wp.Goal791.storeE, forget,
      performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, vField,
      unit', Val.lam]
  rw [e]
  refine erwp_stopHold (tabOfN_park _ _) _ (fun _ => rfl) (fun _ => rfl) (noOwn_single_mut l)
    fun k' _ ls' => ?_
  refine erwp_det hΦ' hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact writeForgetV_ok hΦ hPS l A u vField j k' ls'

theorem childOKV_M (hΦ : Φ.Down) (l : Loc) (A : Life) (u : Val) (j k : Nat) :
    ChildOKV (ℍ := ℍ) (Φ.set l A (famF A)) (tabAtV (ℍ := ℍ) (Φ.set l A (famF A))) k (CM l)
      (VM l A u j) := fun j' _ ls => by
  rw [tabAtV_eq]; exact childM_ok hΦ (spawnPAV_down _ _) l A u j j' ls

end ChildM

/-- **The `mut` spawner at `TJV`**: the spawn passes the borrow itself to the child and keeps
nothing; resumed, `park` or `cancel` holding nothing. -/
theorem PM_ok {Φ : LocFam} (hΦ : Φ.Down) (b : Bool) (l : Loc) (A : Life) (u : Val) (j n : Nat)
    (ls : List SRec) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (TJV (ℍ := ℍ) (Φ.set l A (famF A)))) QVN n ls
      (PM b l) (VM l A u j) := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hTD := opTableN_down (TJV_down (ℍ := ℍ) hΦ')
  set K₁ : Kont := .seq .hole (tailE b)
  have hKH : ∀ m, K₁.HasHnd m = false := fun _ => rfl
  have hKC : ∀ m, K₁.Catches m = false := fun _ => rfl
  show erwp (ℍ := ℍ) _ _ _ _ _ (K₁.plug (performE (.val (opPayload nP 1 (CM l))))) _
  refine erwp_performG K₁ (hKH nP) (tabOfN_spawn _ _) rfl (ResU.comp_empty_right _)
    (childOKV_M hΦ l A u j n) (fun h => by cases h)
    (fun ls' _ k' _ w σB XB ⟨hw, hσ⟩ hXB => ?_)
    (fun ls' _ _ P hP => by cases hP; exact cancel_hold K₁ hKH hKC noOwn_empty _ _)
  subst hw hσ
  obtain rfl := eq_of_compS_empty_left hXB
  refine erwp_det hΦ' hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  have hstop : ∀ (i : UInt32), tabOfN (ℍ := ℍ) (Φ.set l A (famF A))
      (spawnPAV (ℍ := ℍ) (Φ.set l A (famF A)) (tabAtV (ℍ := ℍ) (Φ.set l A (famF A)))) nP i =
      some (enParkN (ℍ := ℍ) (Φ.set l A (famF A))) →
      erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (TJV (ℍ := ℍ) (Φ.set l A (famF A)))) QVN k'
        ls' (.seq (performE (.val (opPayload nP i Val.unit))) (.val Val.unit)) PMap.empty :=
    fun i hi => erwp_stopHold hi (.seq .hole (.val Val.unit)) (fun _ => rfl) (fun _ => rfl)
      noOwn_empty fun _ _ _ =>
        erwp_det hΦ' hTD QVN_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole)
          (erwp_val (v := Val.unit) rfl)
  cases b
  · exact hstop 0 (tabOfN_park _ _)
  · exact hstop 2 (tabOfN_cancel _ _)

/-- The `mut` callback, under `λ_. λr.`: the scope `(hnd HS (spawn CMv; tail)) (HS, [])`. -/
def cbM (b : Bool) : Val :=
  Val.lam (.lam (.app (hndE HS (.seq (spawnE CMv) (tailE b))) st₀.1))

theorem cbM_closed (b : Bool) : closedAt 0 (cbM b).1 = true := by
  cases b <;> rfl

/-- The scope at `ℓ`. -/
def scopeM (b : Bool) (l : Loc) : Expr := .app (hndE HS (PM b l)) st₀.1

/-- **The `mut` lend**: `ℓ` lent `mut` at `A` (`erwp_M_frame` at the empty table, one segment) to
the callback, which runs the scope from the borrow; the lender is handed the cell back at
whatever content the lend's family admits (`MFPost`). -/
theorem lendM_ok {Φ : LocFam} (hΦ : Φ.Down) (b : Bool) (l : Loc) (n : Nat) (ls : List SRec) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (QI l) n ls
      (.app (.app (.val (cbM b)) (.val .unit)) (.val (Val.loc l)))
      (ResU.single l (CellU.ownOf Val.unit)) := by
  obtain ⟨A, -⟩ := exists_fresh ls
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  refine erwp_M_frame (famF_down A) (empty_lendOK A) n n le_rfl ls _ Val.unit PMap.empty _
    PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A n) (fun _ _ h => h) rfl
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (fun BM hBM => ?_)
  obtain rfl := eq_of_compS_empty_left hBM
  have hTD := opTableN_down OpTabN.empty_down
  have hQD : (MFPost l A (famF A) (QI l)).Down := fun _ _ _ _ ⟨h₁, h₂⟩ =>
    ⟨h₁, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => h₂ w Y hY σ ⟨hσ, hF⟩ Z hZ⟩
  refine erwp_det hΦ' hTD hQD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    (.appL .hole (Val.loc l))) ?_
  refine erwp_det hΦ' hTD hQD (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l) (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit)
      (.app (hndE HS (.seq (spawnE CMv) (tailE b))) st₀.1))) = scopeM b l := by
    cases b <;>
    simp [Kont.plug, Expr.subst, Expr.shift, scopeM, PM, CM, CMv, tailE, writeForget, hndE,
      spawnE, parkE, cancelE, performE, opPayload, BoCa.Fig16.Tree.Wp.Goal791.storeE, forget,
      vField, unit', Val.pair, Val.i32, Val.unit, Val.loc, Val.lam, Expr.val, Val.prim, Val.shift,
      subst_closedAt _ _ HS_closed (Nat.zero_le _), subst_closedAt _ _ st₀_closed (Nat.zero_le _)]
  rw [e]
  refine erwp_mono (Tb := opTableN OpTabN.empty) (Tb' := opTableN OpTabN.empty) (Q := QVN)
    (fun k ls' w ρ h => ?_) (opTableN_local _) n _ _ _
    (erwp_scopeV hΦ' (PM_ok hΦ b l A Val.unit n n _))
  subst h
  refine ⟨inStratum_empty A, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => ?_⟩
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := eq_of_compS_empty_left hY
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨w, rfl⟩

/-! ### Case 2: the programs -/

/-- `rootU (cbM b)`: the cell lent `mut` to the scope. -/
def rootM (b : Bool) : Expr := rootU (cbM b)

/-- **Case 2, the child resumed**: `progOf rootM false` is safe and leak-free or diverges. The
spawner lends its cell `mut`, spawns `CM` with the borrow inside the scope and keeps nothing,
then parks; `CM`, parked with the borrow while the spawner ran, is resumed, writes `ℓ := 7`
through it and forgets it; the scope's list empties, the lend ends with the cell handed back,
and the cell is freed. -/
theorem crossMut : OrDiverges (ℍ := ℍ) (.app (hndE HS (rootM false)) st₀.1) :=
  progOfN_orDiverges Φe_down fun n =>
    rootU_ok Φe_down (cbM_closed false) (fun l n ls => lendM_ok Φe_down false l n ls) n []

/-- **Case 2, the child cancelled**: as `crossMut`, the spawner cancelling `CM`, the pool's top,
while `CM` is parked holding the borrow. -/
theorem crossMutC : OrDiverges (ℍ := ℍ) (.app (hndE HS (rootM true)) st₀.1) :=
  progOfN_orDiverges Φe_down fun n =>
    rootU_ok Φe_down (cbM_closed true) (fun l n ls => lendM_ok Φe_down true l n ls) n []

end BoCa.Fig16.LogRel.Core.Chain.SI.Cross821

end
