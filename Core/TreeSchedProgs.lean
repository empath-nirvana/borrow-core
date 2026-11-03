import Core.TreeSched

/-!
# Two programs `MultiBranchAdequacyT` applies to  `[spec §62]`

Two closed Core terms, each meeting `MultiBranchAdequacyT`'s premises, so the headline gives each
"safe or diverges, a value only at the empty memory, every `free` finds its cell". They
illustrate the theorem; they are not its goal. Both are shapes from `corpus/pending/` on
`pending-770`, written at the kernel level (the surface syntax does not compile yet).

* **`pingpong-mut.bc`, in part** (`PingPong`): the stepper the relay runs each task under (a
  handler whose clause hands the slot and the continuation back, `schedS_ok`, its answers a
  step-indexed fixpoint `QS`), and the two tasks at its table (`fill_cerwpT`, `drain_cerwpT`).
  The relay itself is not proved: it holds `fill`'s continuation across `drain`'s run, and the
  resume needs a re-reading of that continuation's stop list at the later world (`KapSchedT`'s
  `SRecsRR` premise, from `contShareT`). `drain` under the stepper owns no record, so
  `twp_keepsKap` (`Core/TreeResume.lean`) carries the continuation across its run; the relay is not
  yet written through it.
* **`async-handler-lends.bc`** (`asyncProg`, `asyncProg_safe`): a scheduler that resumes a task
  inside a state of its own. The task allocates `mine`, asks the scheduler, frees `mine` and answers
  the pair. At `ask` the scheduler allocates its state `cfg`, reads it, resumes the task with what
  it read while it keeps `cfg` beside the task (`kapSchedT_resume_beside`), and frees `cfg` when the
  task's answer comes back. The task's continuation owns a cell (`mine`, across the suspension), so
  `ask` is must-resume (`lin`): `κ` owns its capture cell (`twp_kappaCell`, `twp_kappaC_resume`).

**Departure.** The pending program borrows `mine` and `cfg` (`imm`). Here they are owned cells:
the lend rules over `twp` at the tree world (opening and ending a record, `TWNT.immFrame` and
`TWNT.immEnd` as `twp` steps) are row 6's, not in the library yet. So no task owns a record at a
stop (`oc` is "no records"), the mask history is empty (`maskHist_nil`), and the join condition a
scheduler's state must meet is validity alone. What the programs exercise is the scheduler's
structure: stored continuations owning cells and shares, resumed beside state the scheduler keeps.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt freeE)

/-! ### Facts the two programs share -/

/-- A re-read `own` singleton is itself. -/
theorem rr_single_own {K K' : WCactus} {Θ : LocTy} {l : BoCa.Loc} {v : BoCa.Val} {ρ' : TRes K'}
    (h : RR Θ (ResUT.single l (CellUT.ownOf (K := K) v)) ρ') :
    ρ' = ResUT.single l (CellUT.ownOf v) := by
  obtain ⟨ψ', rfl, hr⟩ := RR.of_sng h
  cases hr; rfl

/-- A composite with the empty resource is the other part. -/
theorem compS_empty_left_eq {K : WCactus} {a b : TRes K} (h : ResUT.CompS PMap.empty a b) : b = a :=
  ResUT.CompS.functional h (ResUT.CompS.comm (ResUT.compS_empty_right a))

theorem compS_empty_right_eq {K : WCactus} {a b : TRes K} (h : ResUT.CompS a PMap.empty b) : b = a :=
  ResUT.CompS.functional h (ResUT.compS_empty_right a)

/-- A table with no records at its stops: a mask history at it holds nothing. -/
theorem maskHist_nil {T : OpTabT} {n₀ : UInt32}
    (hoc : ∀ i en, T n₀ i = some en → ∀ w O, en.oc w O → O = []) {M : BoCa.Loc → Prop}
    (h : MaskHist T n₀ M) (x : BoCa.Loc) : ¬ M x := by
  intro hx
  obtain ⟨i, en, w, O, hT, ho, hm⟩ := h x hx
  obtain rfl := hoc i en hT w O ho
  simp [recMask] at hm

/-- Every resource avoids nothing beyond validity at a location set that holds nothing. -/
theorem fdMask_of_false {M : BoCa.Loc → Prop} (hM : ∀ x, ¬ M x) {w : TWd} {ρ : TRes w.K}
    (hv : ResUT.Valid ρ) : fdMask M w ρ :=
  ⟨hv, NoneAt.of_false hM ρ⟩

/-- A post whose answers do not read the index is downward closed. -/
theorem cerwpPostT_down {T : OpTabT} {Q : TPostV} (hQ : Q.Down) {Ψ : ContT} {F : TFrame}
    (hPA : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    (hfin : ∀ m i en, T m i = some en → en.fin = none) :
    (cerwpPostT (opTableT T) Q Ψ F).Down := by
  intro k w ls O t ρ h
  rcases h with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hA, hsh⟩
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ _ _ hq⟩
  · refine Or.inr ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hPA m i en hT _ _ _ _ _ hA,
      hsh.1, fun w' ρ' ls' O' hE hr hx hO => ⟨fun k' hk' a σ σ' hB hcσ =>
        (hsh.2 w' ρ' ls' O' hE hr hx hO).1 k' (by omega) a σ σ' hB hcσ,
        fun _ P hP => by rw [hfin m i en hT] at hP; cases hP⟩⟩

/-- A deterministic step in front of `cerwpT`, for free. -/
theorem cerwpT_det {Tb : TableT} {Q : TPostV} {F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e e' : Expr} {ρ : TRes w.K}
    (hD : (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q n) F).Down)
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : cerwpT (ℍ := ℍ) Tb Q F n w ls O e' ρ) :
    cerwpT (ℍ := ℍ) Tb Q F n w ls O e ρ := by
  rw [cerwpT_eq] at h ⊢
  exact twp_det hD hdet h

/-! ### `async-handler-lends`: a scheduler that resumes a task beside a state of its own -/

namespace Async

/-- The scheduler's name. -/
abbrev nA : UInt32 := 1

/-- The task's data and the scheduler's. -/
def three : Val := Val.i32 3
def ten : Val := Val.i32 10

/-- `let x = free mine in (x, theirs)`, under `theirs` (`0`) and `mine` (`1`). -/
def tB2 : Expr := .app (.lam (.pair (.var 0) (.var 1))) (.app (.prim .free) (.var 1))

/-- `let theirs = ask () in …`, under `mine` (`0`). -/
def tB1 : Expr := .app (.lam tB2) (performE (.val (opPayload nA 0 Val.unit)))

/-- **The task**: `let mine = alloc 3 in let theirs = ask () in let x = free mine in (x, theirs)`. -/
def task : Expr := .app (.lam tB1) (.app (.prim .alloc) (.val three))

/-- `let _ = free cfg in r`, under `r` (`0`), `t` (`1`), `cfg` (`2`). -/
def cB5 : Expr := .app (.lam (.var 1)) (.app (.prim .free) (.var 2))

/-- `let r = κ t in …`, under `t` (`0`), `cfg` (`1`), `κ` (`2`). -/
def cB4 : Expr := .app (.lam cB5) (.app (.app (.var 2) (.val (Val.inj₁ Val.unit))) (.var 0))

/-- `let t = load cfg in …`, under `cfg` (`0`). -/
def cB3 : Expr := .app (.lam cB4) (.app (.prim .load) (.var 0))

/-- `let cfg = alloc 10 in …`, under `κ` (`0`) and the payload (`1`). -/
def cB2 : Expr := .app (.lam cB3) (.app (.prim .alloc) (.val ten))

/-- **The clause of `ask`**: `λ(_, κ). let cfg = alloc 10 in let t = load cfg in
let r = κ t in let _ = free cfg in r`. -/
def askClause : Val := Val.lam (.letpair (.var 0) cB2)

def retClause : Val := Val.lam (.var 0)
def qsA : Val := Val.pair (Val.i32 0) Val.unit
def hsA : Val := Val.pair askClause Val.unit

/-- **The program**: the task under the scheduler. -/
def asyncProg : Expr := hndE (hndVal nA qsA retClause hsA) task

/-- `ask`: must-resume, no payload, answered `10`, the task owning no record at the stop, the
resumer's guarantee the join's. -/
def enAsk : OpEntT where
  q := .lin
  abort := false
  PA := fun _ _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = ten ∧ σ = PMap.empty
  fin := none
  fd := fdJoinT
  oc := fun _ O => O = []

def TA : OpTabT := fun m i => if m = nA ∧ i = 0 then some enAsk else none

/-- The task's and the program's answers own nothing. -/
def QA : TPostV := fun _ _ _ _ _ ρ => ρ = PMap.empty

theorem QA_down : QA.Down := fun _ _ _ _ _ _ h => h

theorem TA_some {m i : UInt32} {en : OpEntT} (h : TA m i = some en) : m = nA ∧ i = 0 ∧ en = enAsk := by
  unfold TA at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

theorem TA_down {Ψ : ContT} {F : TFrame} : (cerwpPostT (opTableT TA) QA Ψ F).Down :=
  cerwpPostT_down QA_down
    (fun m i en h k w ls v ρ hA => by obtain ⟨-, -, rfl⟩ := TA_some h; exact hA)
    (fun m i en h => by obtain ⟨-, -, rfl⟩ := TA_some h; rfl)

/-! #### The task at `cerwpT` -/

/-- The task's continuation after `ask`, at the answer `10`. -/
theorem task_cont {F : TFrame} (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (l : BoCa.Loc) :
    cerwpT (ℍ := ℍ) (opTableT TA) QA F k w ls O
      ((Kont.appR (.lam (tB2.subst 1 (Val.loc l))) .hole).plug (.val ten))
      (ResUT.single l (CellUT.ownOf three)) := by
  refine cerwpT_det TA_down (fun μ => step1Only_plug (Head.beta μ _ ten) rfl .hole) ?_
  show cerwpT (ℍ := ℍ) (opTableT TA) QA F k w ls O
    ((Kont.appR (.lam (.pair (.var 0) (.val ten))) .hole).plug
      (.app (.val (.prim .free)) (.val (Val.loc l)))) _
  rw [cerwpT_eq]
  refine twp_free TA_down _ l three (ResUT.compS_empty_right _) ?_
  refine twp_det TA_down (fun μ => step1Only_plug (Head.beta μ _ three) rfl .hole) ?_
  rw [← cerwpT_eq]
  exact cerwpT_val (v := Val.pair three ten) fun w₀ ρ₀ _ _ _ hr _ _ => RR.of_empty hr

/-- **The task is verified at the scheduler's table**, under any frame, from the empty
resource. -/
theorem task_cerwpT (n : Nat) (w : TWd) :
    cerwpT (ℍ := ℍ) (opTableT TA) QA (fun _ _ => True) n w [] [] task PMap.empty := by
  rw [cerwpT_eq]
  refine twp_alloc_here TA_down (Kont.appR (.lam tB1) .hole) three fun l ρ₁ hc => ?_
  obtain rfl := compS_empty_left_eq hc
  refine twp_det TA_down (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  rw [← cerwpT_eq]
  show cerwpT (ℍ := ℍ) (opTableT TA) QA _ n w [] []
    ((Kont.appR (.lam (tB2.subst 1 (Val.loc l))) .hole).plug
      (performE (.val (opPayload nA 0 Val.unit)))) _
  refine cerwpT_perform _ (by simp [Kont.HasHnd]) (show TA nA 0 = some enAsk by simp [TA]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := rr_single_own hr
  refine ⟨rfl, PMap.empty, _, ResUT.CompS.comm (ResUT.compS_empty_right _), ⟨rfl, rfl⟩,
    ⟨fun h => by simp [enAsk] at h, fun w' ρ' ls' O' _ hr' _ _ =>
      ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun h => absurd rfl h⟩⟩⟩
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := compS_empty_right_eq hcσ
  obtain rfl := rr_single_own hr'
  simp only [cerwpTC, hk', if_true]
  exact task_cont k' w' ls' O' l

/-! #### The scheduler -/

/-- `letpair` substitutes `κ` under the clause's three binders. -/
def E1body (κ : Val) : Expr :=
  .app (.lam (.app (.lam cB5) (.app (.app (κ.1.shift 2 0) (.val (Val.inj₁ Val.unit))) (.var 0))))
    (.app (.prim .load) (.var 0))

theorem e1_eq (κ : Val) :
    (cB2.subst 0 (κ.shift 1 0)).subst 0 Val.unit =
      .app (.lam (E1body κ)) (.app (.prim .alloc) (.val ten)) := by
  simp [cB2, cB3, cB4, cB5, E1body, Expr.subst, Val.shift, Expr.shift, ten, Val.i32, Val.inj₁,
    Val.unit, Expr.shift_shift]
  rw [Expr.subst_shift 2 0 2 _ _ (by omega) (by omega)]

def E2body (κ : Val) (l : BoCa.Loc) : Expr :=
  .app (.lam (.app (.lam (.var 1)) (.app (.prim .free) (.loc l))))
    (.app (.app (κ.1.shift 1 0) (.val (Val.inj₁ Val.unit))) (.var 0))

theorem e2_eq (κ : Val) (l : BoCa.Loc) :
    (E1body κ).subst 0 (Val.loc l) = .app (.lam (E2body κ l)) (.app (.prim .load) (.loc l)) := by
  simp [E1body, E2body, cB5, Expr.subst, Val.inj₁, Val.unit, Val.loc, Val.shift, Expr.shift]
  rw [Expr.subst_shift 1 0 1 _ _ (by omega) (by omega)]

/-- The clause's continuation around the resume: `let r = □ in let _ = free cfg in r`. -/
def resumeK (l : BoCa.Loc) : Kont :=
  .appR (.lam (.app (.lam (.var 1)) (.app (.prim .free) (.loc l)))) .hole

theorem e3_eq (κ : Val) (l : BoCa.Loc) :
    (E2body κ l).subst 0 ten =
      (resumeK l).plug (.app (.app κ.1 (.val (Val.inj₁ Val.unit))) (.val ten)) := by
  simp [E2body, resumeK, Kont.plug, Expr.subst, Val.inj₁, Val.unit, ten, Val.i32]
  rw [Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]

/-- After the resume: the scheduler frees its state and answers the task's answer. -/
theorem after_resume {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} (l : BoCa.Loc) (r : Val) :
    twp (ℍ := ℍ) F (valPost QA) k w ls O ((resumeK l).plug (.val r))
      (ResUT.single l (CellUT.ownOf ten)) := by
  have hD := valPost_down QA_down
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
  have e : (Expr.app (.lam (.var 1)) (.app (.prim .free) (.loc l))).subst 0 r =
      (Kont.appR (.lam (r.shift 1 0).1) .hole).plug (.app (.val (.prim .free)) (.val (Val.loc l))) := by
    simp [Expr.subst, Kont.plug, Val.loc, Expr.val]
  rw [e]
  refine twp_free hD _ l ten (ResUT.compS_empty_right _) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ ten) rfl .hole) ?_
  have e' : (r.shift 1 0).1.subst 0 ten = r.1 := by
    rw [Val.val_shift, Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]
  rw [e']
  exact twp_here (fun μ => final_val μ r) fun _ _ _ _ _ hr _ _ => ⟨r, rfl, RR.of_empty hr⟩

/-- The scheduler's state, kept beside the resumed task: `cfg ↦ own(10)`, no records. -/
def stateR (l : BoCa.Loc) : TRProp := fun _ O ρ => O = [] ∧ ρ = ResUT.single l (CellUT.ownOf ten)

theorem stateR_mono (l : BoCa.Loc) : (stateR l).Mono := by
  intro w w' O O' ρ ρ' _ hr hO ⟨h₁, h₂⟩
  subst h₁; subst h₂
  cases hO
  exact ⟨rfl, rr_single_own hr⟩

/-- **The clause of `ask`.** -/
theorem askClause_ok : SchedClauseT (ℍ := ℍ) TA nA QA enAsk askClause := by
  rintro M F k w ls O v κ ρ hFm hMh hoc hFM hcov hls hO ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  change O = [] at hoc
  subst hoc
  have hM : ∀ x, ¬ (M x ∨ recMask ([] : List (FrameRecT w.K)) x) := fun x hx =>
    hx.elim (maskHist_nil (fun i en h w O ho => by obtain ⟨-, -, rfl⟩ := TA_some h; exact ho)
      hMh x) (by simp [recMask])
  have hD := valPost_down QA_down
  rw [cerwpTE_iff]
  cases k with
  | zero => exact twp_zero
  | succ k₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  show twp (ℍ := ℍ) F (valPost QA) k₀ w ls [] (.letpair (.val (Val.pair Val.unit κ)) cB2) ρ
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ cB2) rfl .hole) ?_
  rw [e1_eq]
  refine twp_alloc_here hD (Kont.appR (.lam (E1body κ)) .hole) ten fun l ρ₁ hc₁ => ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  rw [e2_eq]
  have hl : ρ₁.get l = some (CellUT.ownOf ten) := by
    rw [ResUT.Comp.get_of_left_none hc₁ (ResUT.compatS_single_own (ResUT.CompatS.symm hc₁.1)),
      ResUT.single_get_self]
  refine twp_load hD (Kont.appR (.lam (E2body κ l)) .hole) l ten hl ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ ten) rfl .hole) ?_
  rw [e3_eq]
  refine twp_bind hFm (resumeK l) ?_
  have h := kapSchedT_resume_beside hκ hFM (Nat.lt_succ_self k₀) (a := ten) ⟨rfl, rfl⟩
    (ResUT.compS_empty_right ρ) hc₁ (covR_compS_own hc₁ hcov) hls hO (stateR_mono l)
    (fun _ h => by simp at h) ⟨rfl, rfl⟩ (fdMask_of_false hM (ResUT.valid_single_own l ten))
  rw [List.append_nil] at h
  refine twp_mono (fun k' w' ls' O' t ρ' ht => ?_) h
  obtain ⟨O₁, O₂, a, b, -, hab, ⟨r, rfl, hr⟩, -, rfl⟩ := ht
  change a = PMap.empty at hr
  subst hr
  obtain rfl := compS_empty_left_eq hab
  exact after_resume l r

/-- The return clause answers the task's answer. -/
theorem retClause_ok : SchedRetT (ℍ := ℍ) TA nA QA QA retClause := by
  intro M F k w ls O v ρ _ _ _ _ _ _ hv
  change ρ = PMap.empty at hv
  subst hv
  rw [cerwpTE_iff]
  refine twp_det (valPost_down QA_down) (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e : (Expr.var 0).subst 0 v = v.1 := by simp [Expr.subst]
  rw [e]
  exact twp_here (fun μ => final_val μ v) fun _ _ _ _ _ hr _ _ => ⟨v, rfl, RR.of_empty hr⟩

/-- **The scheduler meets `SchedOKT`.** -/
theorem async_schedOK : SchedOKT (ℍ := ℍ) TA nA qsA retClause hsA QA QA := by
  refine ⟨fun m i hm => by simp [TA, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    QA_down, retClause_ok, fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TA_some h
    rfl
  · obtain ⟨-, -, rfl⟩ := TA_some h
    exact hj
  · obtain ⟨-, rfl, rfl⟩ := TA_some h
    refine ⟨askClause, ?_, askClause_ok⟩
    simp [clauseAt, hsA, Val.pair, askClause, Val.lam, IsVal.lam]

/-- **`async-handler-lends` is safe, or diverges**: every configuration it reaches steps or is a
value, a value only at the empty memory, every `free` finds its cell. Through the headline. -/
theorem asyncProg_safe : OrDiverges (ℍ := ℍ) asyncProg :=
  multiBranchAdequacyT beforeP TA nA qsA retClause hsA QA QA task (fun _ _ _ _ _ _ h => h)
    async_schedOK fun n => task_cerwpT n _

end Async

/-! ### Facts about `KapSchedT` the stepper reads -/

/-- `KapSchedT` reads its answer predicate only below its index. -/
theorem kapSchedT_congr {Q₁ Q₂ : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v κ : Val} {ρ : TRes w.K}
    (hQ : ∀ j, j < k → ∀ w ls O v ρ, Q₁ j w ls O v ρ → Q₂ j w ls O v ρ)
    (h : KapSchedT (ℍ := ℍ) Q₁ M en k w ls O v κ ρ) : KapSchedT (ℍ := ℍ) Q₂ M en k w ls O v κ ρ := by
  refine ⟨h.1, fun w' ρ' ls' O' hE hr hx hO k' hk' a σ σ' hB hc F' hF'm hF'M => ?_⟩
  have h₁ := cerwpTE_iff.mp (h.2 w' ρ' ls' O' hE hr hx hO k' hk' a σ σ' hB hc F' hF'm hF'M)
  exact cerwpTE_iff.mpr (twp_mono_le (fun j hj _ _ _ _ _ ⟨r, hr', hq⟩ =>
    ⟨r, hr', hQ j (by omega) _ _ _ _ _ hq⟩) h₁)

theorem KapSchedT.down {Q : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v κ : Val} {ρ : TRes w.K}
    (h : KapSchedT (ℍ := ℍ) Q M en (k + 1) w ls O v κ ρ) : KapSchedT (ℍ := ℍ) Q M en k w ls O v κ ρ :=
  ⟨h.1, fun w' ρ' ls' O' hE hr hx hO k' hk' => h.2 w' ρ' ls' O' hE hr hx hO k'
    (by omega)⟩

/-- A frame avoiding more locations is one `κ` may be resumed under. -/
theorem KapSchedT.mask_mono {Q : TPostV} {M M' : BoCa.Loc → Prop} {en : OpEntT} {k : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v κ : Val} {ρ : TRes w.K}
    (hM : ∀ x, M x → M' x) (h : KapSchedT (ℍ := ℍ) Q M en k w ls O v κ ρ) :
    KapSchedT (ℍ := ℍ) Q M' en k w ls O v κ ρ :=
  ⟨h.1, fun w' ρ' ls' O' hE hr hx hO k' hk' a σ σ' hB hc F' hF'm hF'M =>
    h.2 w' ρ' ls' O' hE hr hx hO k' hk' a σ σ' hB hc F' hF'm
      fun w'' ρf hf => fdMask_le hM (hF'M w'' ρf hf)⟩

/-- **A tail resume**: `κ` at the clause's own world, under the clause's frame condition. -/
theorem kapSchedT_resume_tail {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v κ : Val} {ρk : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) Qout M en k w ls O v κ ρk) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask M w' ρf) {k' : Nat} (hk' : k' < k) {a : Val}
    {σ σ' : TRes w.K} (hB : en.PBv v k' w ls a σ) (hcσ : ResUT.CompS ρk σ σ')
    (hcov : CovR (sem w.Θ) w.K ρk) (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R)
    (hO : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R) :
    twp (ℍ := ℍ) F (valPost Qout) k' w ls O (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ' :=
  cerwpTE_iff.mp (hκ.2 w ρk ls O (TWd.Ext.refl _ _) (RR.refl hcov) (KeepRel.refl hls ρk)
    (RecsRR.refl hO) k' hk' a σ σ' hB hcσ F hFm hFM)

/-! ### `pingpong-mut`: a slot handed back and forth between two suspended tasks by a relay -/

namespace PingPong

/-- The relay's name and the stepper's. -/
abbrev nH : UInt32 := 1
abbrev nS : UInt32 := 2

def zero : Val := Val.i32 0
def one : Val := Val.i32 1

/-- `pass`: unrestricted (the continuation owns nothing), the slot handed out with the payload
and back with the answer. -/
def enPass : OpEntT where
  q := .unr
  abort := false
  PA := fun _ _ _ v ρ => ∃ (m : BoCa.Loc) (u : BoCa.Val), v = Val.loc m ∧
    ρ = ResUT.single m (CellUT.ownOf u)
  PBv := fun _ _ _ _ a σ => ∃ (m : BoCa.Loc) (u : BoCa.Val), a = Val.loc m ∧
    σ = ResUT.single m (CellUT.ownOf u)
  fin := none
  fd := fdJoinT
  oc := fun _ O => O = []

def TS : OpTabT := fun m i => if m = nS ∧ i = 0 then some enPass else none

theorem TS_some {m i : UInt32} {en : OpEntT} (h : TS m i = some en) :
    m = nS ∧ i = 0 ∧ en = enPass := by
  unfold TS at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

/-- **What a stepped task answers** (`Qt` its final answer): a stop at `pass`, the slot and the
continuation resumable at the answers below the index; or the task's end. A step-indexed
fixpoint: the continuation's answers are this predicate again. -/
def QS (Qt : TPostV) : (k : Nat) → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Val →
    TRes w.K → Prop
  | k, w, ls, O, v, ρ =>
    (∃ (m : BoCa.Loc) (u : BoCa.Val) (κ : Val), v = Val.inj₁ (Val.pair (Val.loc m) κ) ∧
      ρ = ResUT.single m (CellUT.ownOf u) ∧ O = [] ∧
      KapSchedT (ℍ := ℍ) (fun j w' ls' O' v' ρ' => if _h : j < k then QS Qt j w' ls' O' v' ρ'
        else False) (fun _ => False) enPass k w ls O (Val.loc m) κ PMap.empty) ∨
    (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ)
termination_by k => k

theorem QS_iff {Qt : TPostV} {k : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {v : Val} {ρ : TRes w.K} :
    QS (ℍ := ℍ) Qt k w ls O v ρ ↔
      (∃ (m : BoCa.Loc) (u : BoCa.Val) (κ : Val), v = Val.inj₁ (Val.pair (Val.loc m) κ) ∧
        ρ = ResUT.single m (CellUT.ownOf u) ∧ O = [] ∧
        KapSchedT (ℍ := ℍ) (QS (ℍ := ℍ) Qt) (fun _ => False) enPass k w ls O (Val.loc m) κ
          PMap.empty) ∨
      (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ) := by
  rw [QS]
  constructor
  · rintro (⟨m, u, κ, h₁, h₂, h₃, h₄⟩ | h)
    · exact Or.inl ⟨m, u, κ, h₁, h₂, h₃, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₄⟩
    · exact Or.inr h
  · rintro (⟨m, u, κ, h₁, h₂, h₃, h₄⟩ | h)
    · exact Or.inl ⟨m, u, κ, h₁, h₂, h₃, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₄⟩
    · exact Or.inr h

theorem QS_down {Qt : TPostV} (hQt : Qt.Down) : TPostV.Down (QS (ℍ := ℍ) Qt) := by
  intro k w ls O v ρ h
  rcases QS_iff.mp h with ⟨m, u, κ, h₁, h₂, h₃, h₄⟩ | ⟨r, h₁, h₂⟩
  · exact QS_iff.mpr (Or.inl ⟨m, u, κ, h₁, h₂, h₃, KapSchedT.down h₄⟩)
  · exact QS_iff.mpr (Or.inr ⟨r, h₁, hQt _ _ _ _ _ _ h₂⟩)

/-! #### The stepper -/

/-- `λ(m, κ). inj₁ (m, κ)`: hand the slot and the continuation to whoever ran the task. -/
def passClause : Val := Val.lam (.letpair (.var 0) (.inj₁ (.pair (.var 1) (.var 0))))
def stepRet : Val := Val.lam (.inj₂ (.var 0))
def qsS : Val := Val.pair (Val.i32 2) Val.unit
def hsS : Val := Val.pair passClause Val.unit
def HS : Val := hndVal nS qsS stepRet hsS

/-- A final answer read the same at every re-reading of the world. -/
def QtStable (Qt : TPostV) : Prop :=
  ∀ k (w w₀ : TWd) (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (ls₀ : List (SRecT w₀.K))
    (O₀ : List (FrameRecT w₀.K)) (r : Val) (ρ : TRes w.K) (ρ₀ : TRes w₀.K), w.Ext w₀ ρ →
    RRw (w := w) (w' := w₀) ρ ρ₀ → RecsRR w₀.Θ O O₀ → Qt k w ls O r ρ → Qt k w₀ ls₀ O₀ r ρ₀

theorem passClause_ok {Qt : TPostV} (hQt : Qt.Down) :
    SchedClauseT (ℍ := ℍ) TS nS (QS (ℍ := ℍ) Qt) enPass passClause := by
  rintro M F k w ls O v κ ρ _ hMh hoc _ _ _ _ ⟨ρa, ρk, hc, ⟨m, u, rfl, rfl⟩, hκ⟩
  change O = [] at hoc
  subst hoc
  obtain rfl := hκ.1 rfl
  obtain rfl := compS_empty_right_eq hc
  have hM : ∀ x, (M x ∨ recMask ([] : List (FrameRecT w.K)) x) → False := fun x hx =>
    hx.elim (maskHist_nil (fun i en h w O ho => by obtain ⟨-, -, rfl⟩ := TS_some h; exact ho)
      hMh x) (by simp [recMask])
  rw [cerwpTE_iff]
  have hD := valPost_down (QS_down (ℍ := ℍ) hQt)
  · refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (Val.loc m) κ)) rfl .hole) ?_
    show twp (ℍ := ℍ) F _ k w ls [] (.letpair (.val (Val.pair (Val.loc m) κ))
      (.inj₁ (.pair (.var 1) (.var 0)))) _
    refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ (Val.loc m) κ _) rfl .hole) ?_
    have e : ((Expr.inj₁ (.pair (.var 1) (.var 0))).subst 0 (κ.shift 1 0)).subst 0 (Val.loc m) =
        (Val.inj₁ (Val.pair (Val.loc m) κ)).1 := by
      simp [Expr.subst, Val.inj₁, Val.pair, Val.loc]
      rw [Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]
    rw [e]
    refine twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
    cases hO
    refine ⟨_, rfl, QS_iff.mpr (Or.inl ⟨m, u, κ, rfl, rr_single_own hr, rfl,
      KapSchedT.kripke (KapSchedT.mask_mono (fun x hx => hM x hx) hκ)
        (hE.of_compS_left (ResUT.CompS.comm (ResUT.compS_empty_right _))) RR.empty
        (KeepRel.of_srecsRR hl _) .nil⟩)⟩

theorem stepRet_ok {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    SchedRetT (ℍ := ℍ) TS nS Qt (QS (ℍ := ℍ) Qt) stepRet := by
  intro M F k w ls O v ρ _ _ _ _ _ _ hv
  rw [cerwpTE_iff]
  refine twp_det (valPost_down (QS_down (ℍ := ℍ) hQt))
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e : (Expr.inj₂ (.var 0)).subst 0 v = (Val.inj₂ v).1 := by simp [Expr.subst, Val.inj₂]
  rw [e]
  exact twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr _ hO =>
    ⟨_, rfl, QS_iff.mpr (Or.inr ⟨v, rfl, hst k w w₀ ls O ls₀ O₀ v ρ ρ₀ hE hr hO hv⟩)⟩

/-- **The stepper meets `SchedOKT`**, at every final answer of the task. -/
theorem schedS_ok {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    SchedOKT (ℍ := ℍ) TS nS qsS stepRet hsS Qt (QS (ℍ := ℍ) Qt) := by
  refine ⟨fun m i hm => by simp [TS, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    QS_down hQt, stepRet_ok hQt hst, fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TS_some h
    rfl
  · obtain ⟨-, -, rfl⟩ := TS_some h
    exact hj
  · obtain ⟨-, rfl, rfl⟩ := TS_some h
    exact ⟨passClause, by simp [clauseAt, hsS, Val.pair, passClause, Val.lam, IsVal.lam],
      passClause_ok hQt⟩

/-- **A stepped task, run under the stepper**, under any frame condition whose frames are valid:
the stepper's `[handle]` at the empty mask. -/
theorem stepped_twp {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) {F : TFrame}
    (hFm : F.Mono) (hFv : ∀ w ρf, F w ρf → ResUT.Valid ρf) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (he : cerwpT (ℍ := ℍ) (opTableT TS) Qt (fun _ _ => True) n w ls [] e ρ) :
    twp (ℍ := ℍ) F (valPost (QS (ℍ := ℍ) Qt)) n w ls [] (hndE HS e) ρ :=
  cerwpT_schedHandle (schedS_ok hQt hst) n (fun _ => False) F _ w ls [] e ρ hFm
    (maskHist_empty _ _) (fun w ρf h => fdMask_of_false (fun _ h => h) (hFv w ρf h))
    (fun x hx => by simp [recMask] at hx) (fun _ _ _ => trivial) he

/-! #### The two tasks -/

/-- The payload `(nS, (0, s))` of `pass`, the slot at the variable `i`. -/
def passE (i : Nat) : Expr := performE (.pair (.val (Val.i32 nS)) (.pair (.val (Val.i32 0)) (.var i)))

/-- **`fill`**: `λs. let _ = store s 1 in pass s`. -/
def fillV : Val := Val.lam (.app (.lam (passE 1)) (.app (.app (.prim .store) (.var 0)) (.val one)))

/-- **`drain`**: `λs. let s′ = pass s in let x = load s′ in (s′, x)`. -/
def drainB : Expr := .app (.lam (.pair (.var 1) (.var 0))) (.app (.prim .load) (.var 0))
def drainV : Val := Val.lam (.app (.lam drainB) (passE 0))

/-- `fill` answers the slot; `drain` the slot and what it read. -/
def Qf : TPostV := fun _ _ _ _ r ρ => ∃ (m : BoCa.Loc) (u : BoCa.Val), r = Val.loc m ∧
  ρ = ResUT.single m (CellUT.ownOf u)
def Qd : TPostV := fun _ _ _ _ r ρ => ∃ (m : BoCa.Loc) (u x : BoCa.Val),
  r = Val.pair (Val.loc m) x ∧ ρ = ResUT.single m (CellUT.ownOf u)

theorem Qf_stable : QtStable Qf := by
  rintro k w w₀ ls O ls₀ O₀ r ρ ρ₀ - hr - ⟨m, u, rfl, rfl⟩
  exact ⟨m, u, rfl, rr_single_own hr⟩

theorem Qd_stable : QtStable Qd := by
  rintro k w w₀ ls O ls₀ O₀ r ρ ρ₀ - hr - ⟨m, u, x, rfl, rfl⟩
  exact ⟨m, u, x, rfl, rr_single_own hr⟩

theorem TS_down {Qt : TPostV} (hQt : Qt.Down) {Ψ : ContT} {F : TFrame} :
    (cerwpPostT (opTableT TS) Qt Ψ F).Down :=
  cerwpPostT_down hQt
    (fun m i en h k w ls v ρ hA => by obtain ⟨-, -, rfl⟩ := TS_some h; exact hA)
    (fun m i en h => by obtain ⟨-, -, rfl⟩ := TS_some h; rfl)

/-- The stop at `pass`, the slot `l` handed out; the continuation `K`, given what `pass`
answers, is `Ψ`'s. -/
theorem pass_stop {Qt : TPostV} {F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    (K : Kont) (hK : K.HasHnd nS = false) (l : BoCa.Loc) (u : BoCa.Val)
    (hk : ∀ k', k' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K))
      (m : BoCa.Loc) (u' : BoCa.Val), cerwpT (ℍ := ℍ) (opTableT TS) Qt
        (fdAt enPass (Val.loc l) F O') k' w' ls' O' (K.plug (.val (Val.loc m)))
        (ResUT.single m (CellUT.ownOf u'))) :
    cerwpT (ℍ := ℍ) (opTableT TS) Qt F n w ls []
      (K.plug (performE (.val (opPayload nS 0 (Val.loc l))))) (ResUT.single l (CellUT.ownOf u)) := by
  refine cerwpT_perform K hK (show TS nS 0 = some enPass by simp [TS]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := rr_single_own hr
  refine ⟨rfl, _, PMap.empty, ResUT.compS_empty_right _, ⟨l, u, rfl, rfl⟩,
    ⟨fun _ => rfl, fun w' ρ' ls' O' _ hr' _ _ =>
      ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ P hP => by cases hP⟩⟩⟩
  obtain ⟨m, u', rfl, rfl⟩ := hB
  obtain rfl := RR.of_empty hr'
  obtain rfl := compS_empty_left_eq hcσ
  simp only [cerwpTC, hk', if_true]
  exact hk k' hk' w' ls' O' m u'

/-- **`fill` at the stepper's table**: from the slot, at every index. -/
theorem fill_cerwpT (n : Nat) (w : TWd) (ls : List (SRecT w.K)) (l : BoCa.Loc) (u : BoCa.Val) :
    cerwpT (ℍ := ℍ) (opTableT TS) Qf (fun _ _ => True) n w ls [] (.app fillV.1 (.loc l))
      (ResUT.single l (CellUT.ownOf u)) := by
  have hD := TS_down (Qt := Qf) (Ψ := cerwpTC (ℍ := ℍ) (opTableT TS) Qf n)
    (F := fun _ _ => True) (fun _ _ _ _ _ _ h => h)
  refine cerwpT_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  show cerwpT (ℍ := ℍ) (opTableT TS) Qf _ n w ls []
    ((Kont.appR (.lam ((passE 1).subst 1 (Val.loc l))) .hole).plug
      (.app (.app (.val (.prim .store)) (.val (Val.loc l))) (.val one))) _
  rw [cerwpT_eq]
  refine twp_store hD _ l u one (ResUT.compS_empty_right _) (ResUT.compS_empty_right _) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [← cerwpT_eq]
  show cerwpT (ℍ := ℍ) (opTableT TS) Qf _ n w ls []
    (Kont.hole.plug (performE (.val (opPayload nS 0 (Val.loc l))))) _
  refine pass_stop .hole rfl l one fun k' _ w' ls' O' m u' => ?_
  exact cerwpT_val fun w₀ ρ₀ _ _ _ hr _ _ => ⟨m, u', rfl, rr_single_own hr⟩

/-- **`drain` at the stepper's table**: from the slot, at every index. -/
theorem drain_cerwpT (n : Nat) (w : TWd) (ls : List (SRecT w.K)) (l : BoCa.Loc) (u : BoCa.Val) :
    cerwpT (ℍ := ℍ) (opTableT TS) Qd (fun _ _ => True) n w ls [] (.app drainV.1 (.loc l))
      (ResUT.single l (CellUT.ownOf u)) := by
  have hD := TS_down (Qt := Qd) (Ψ := cerwpTC (ℍ := ℍ) (opTableT TS) Qd n)
    (F := fun _ _ => True) (fun _ _ _ _ _ _ h => h)
  refine cerwpT_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  show cerwpT (ℍ := ℍ) (opTableT TS) Qd _ n w ls []
    ((Kont.appR (.lam (drainB.subst 1 (Val.loc l))) .hole).plug
      (performE (.val (opPayload nS 0 (Val.loc l))))) _
  refine pass_stop _ (by simp [Kont.HasHnd]) l u fun k' _ w' ls' O' m u' => ?_
  have hD' := TS_down (Qt := Qd) (Ψ := cerwpTC (ℍ := ℍ) (opTableT TS) Qd k')
    (F := fdAt enPass (Val.loc l) (fun _ _ => True) O') (fun _ _ _ _ _ _ h => h)
  refine cerwpT_det hD' (fun μ => step1Only_plug (Head.beta μ _ (Val.loc m)) rfl .hole) ?_
  show cerwpT (ℍ := ℍ) (opTableT TS) Qd _ k' w' ls' O'
    ((Kont.appR (.lam (.pair (.val (Val.loc m)) (.var 0))) .hole).plug
      (.app (.val (.prim .load)) (.val (Val.loc m)))) _
  rw [cerwpT_eq]
  refine twp_load hD' _ m u' (ResUT.single_get_self _ _) ?_
  refine twp_det hD' (fun μ => step1Only_plug (Head.beta μ _ u') rfl .hole) ?_
  rw [← cerwpT_eq]
  show cerwpT (ℍ := ℍ) (opTableT TS) Qd _ k' w' ls' O' (Val.pair (Val.loc m) u').1 _
  exact cerwpT_val fun w₀ ρ₀ _ _ _ hr _ _ => ⟨m, u', u', rfl, rr_single_own hr⟩

end PingPong

end BoCa.Fig16.Tree.Wp.SchedProgs

end
