import Core.TreePoolSched
import Core.TreeSchedRelay

/-!
# A scheduler handler that keeps a pool in its state, through `PoolSchedAdequacyT`  `[spec §62]`

The stack scheduler `HStack`: its one operation is `park` (`enPark`, the park stepper's entry,
cancellable). Its answers are functions of its pool (`PoolAns`):

* at a park, `λ(_, κ). λs. κ (inj₁ ()) () s`: the stopped task joins the pool (`poolAns_park`) and
  the pool's head, the task just parked, is resumed with the rest handed to what it answers
  (`poolAns_resume`): the state handed on is `s` itself;
* at a task's end, `λv. λ(h, p). case p {inj₁ (κ, p′). κ (inj₁ ()) () (h, p′) | inj₂ _. v}`: the
  pool's head is resumed with the rest (`poolAns_resume`), or, the pool empty, the task's answer is
  the program's.

`stack_schedOK` proves `SchedOKT` at `PoolAns` for every pool, of any length (the clauses are proved
for every pool the headline quantifies over, not for the pools this program reaches); so the
headline's scheduler premise has an instance. `stackProg_safe` is a closed program through the
headline: `(hnd HStack (let _ = park () in ())) (HStack, [])`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.PingPong (QtStable)
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt ccatchE raiseE
  cancelVal)

/-- `λ(_, κ). λs. κ (inj₁ ()) () s`. -/
def stackClause : Val :=
  Val.lam (.letpair (.var 0) (.lam (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.var 0))))

/-- `λv. λ(h, p). case p {inj₁ q. let (κ, s′) = q in κ (inj₁ ()) () (h, s′) | inj₂ _. v}`. -/
def stackRet : Val :=
  Val.lam (.lam (.letpair (.var 0) (.case (.var 0)
    (.letpair (.var 0) (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.pair (.var 4) (.var 0))))
    (.var 4))))

def hsStack : Val := Val.pair stackClause Val.unit
def HStack : Val := hndVal nP qsP stackRet hsStack

/-- The stack scheduler's pool invariant: every task stopped at `park`. -/
def InvStack (ts : List StoredT) : Prop := ∀ t ∈ ts, t.en = enPark ∧ t.v = Val.unit

/-- The program's answer, and every task's: `()`, owning nothing. -/
abbrev QS : TPostV := QB

/-- The resumed head, handed the rest, after the steps of `λs. …` and `case`/`let`. -/
def resumeE (κ : Val) (s : Val) : Expr :=
  .app (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val Val.unit)) s.1

/-- The clause's answer at a stop: `λs. κ (inj₁ ()) () s`. -/
def clauseAns (κ : Val) : Val :=
  Val.lam (.app (.app (.app (κ.shift 1 0).1 (.inj₁ .unit)) .unit) (.var 0))

theorem clause_after (κ : Val) :
    ((Expr.lam (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.var 0))).subst 0
      (κ.shift 1 0)).subst 0 Val.unit = (clauseAns κ).1 := by
  simp [Expr.subst, clauseAns, Val.lam]
  rw [Expr.shift_shift, Expr.subst_shift 1 0 1 _ _ (by omega) (by omega)]

theorem clause_beta (κ s : Val) :
    (Expr.app (.app (.app (κ.shift 1 0).1 (.inj₁ .unit)) .unit) (.var 0)).subst 0 s =
      resumeE κ s := by
  simp [Expr.subst, resumeE, Val.inj₁]
  exact Expr.subst_shift 0 0 0 _ _ (by omega) (by omega) |>.trans (Expr.shift_zero _ _)

/-- The return clause's body under `λv. λs.`, and its first branch. -/
def retL : Expr :=
  .letpair (.var 0) (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.pair (.var 4) (.var 0)))

def retBody : Expr := .letpair (.var 0) (.case (.var 0) retL (.var 4))

/-- The return clause's answer at `v`: `λs. …`. -/
def retAns (v : Val) : Val := Val.lam (retBody.subst 1 (v.shift 1 0))

theorem ret_after (v : Val) : (Expr.lam retBody).subst 0 v = (retAns v).1 := by
  simp [Expr.subst, retAns, Val.lam]

/-- The first branch with the handler substituted. -/
def retL' (h : Val) : Expr :=
  .letpair (.var 0) (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.pair (h.shift 3 0).1 (.var 0)))

theorem ret_s1 (v h p : Val) : (retBody.subst 1 (v.shift 1 0)).subst 0 (Val.pair h p) =
    .letpair (Val.pair h p).1 (.case (.var 0) retL (v.shift 3 0).1) := by
  conv_lhs => simp [retBody, retL, Expr.subst, Expr.shift_shift]
  rw [Expr.subst_shift 3 0 3 _ _ (by omega) (by omega)]
  rfl

theorem ret_s2 (v h p : Val) :
    ((Expr.case (.var 0) retL (v.shift 3 0).1).subst 0 (p.shift 1 0)).subst 0 h =
      .case p.1 (retL' h) (v.shift 1 0).1 := by
  conv_lhs => simp [retL, Expr.subst, Expr.shift_shift]
  rw [Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero,
    Expr.subst_shift 2 0 1 _ _ (by omega) (by omega), Expr.subst_shift 1 0 1 _ _ (by omega) (by omega)]
  rfl

theorem ret_nil (v : Val) : (v.shift 1 0).1.subst 0 Val.unit = v.1 :=
  (Expr.subst_shift 0 0 0 _ _ (by omega) (by omega)).trans (Expr.shift_zero _ _)

theorem ret_cons (h κ r : Val) :
    (retL' h).subst 0 (Val.pair κ r) = .letpair (Val.pair κ r).1
      (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.pair (h.shift 2 0).1 (.var 0))) := by
  conv_lhs => simp [retL', Expr.subst]
  rw [Expr.subst_shift 2 0 2 _ _ (by omega) (by omega)]
  rfl

theorem ret_cons_let (h κ r : Val) :
    ((Expr.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.pair (h.shift 2 0).1 (.var 0))).subst 0
      (r.shift 1 0)).subst 0 κ = resumeE κ (Val.pair h r) := by
  simp [Expr.subst, resumeE, Val.inj₁, Val.pair]
  rw [Expr.subst_shift 1 0 0 _ _ (by omega) (by omega), Expr.subst_shift 0 0 0 _ _ (by omega) (by omega),
    Expr.shift_zero, Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]
  exact ⟨rfl, rfl⟩

/-! ### The scheduler meets `SchedOKT` at `PoolAns`, for every pool -/

/-- **The park clause**: park the stopped task, resume the pool's head (the task just parked) with
the rest handed to what it answers. -/
theorem stackClause_ok :
    SchedClauseT (ℍ := ℍ) HStack (PoolAns (ℍ := ℍ) QS HStack InvStack) enPark stackClause := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HStack InvStack)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  show twp (ℍ := ℍ) F _ k w ls O (.letpair (.val (Val.pair Val.unit κ))
    (.lam (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit) (.var 0)))) _
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  rw [clause_after]
  refine twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨_, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvStack) hκ' hj hg hP hc' hσ hρ hap
    (CovR.of_compS_left hc' hcov) hls hO'
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HStack ts)) rfl .hole) ?_
  rw [clause_beta]
  exact poolAns_resume hg' hP' (a := Val.unit) (σ := PMap.empty) ⟨rfl, rfl⟩
    (ResUT.compS_empty_right ρ') (noneAt_empty _) hcov hv hF'm hF'M hi

/-- **The return clause**: the pool's head resumed with the rest, or the pool empty, the task's
answer the program's. -/
theorem stackRet_ok : SchedRetT (ℍ := ℍ) QS (PoolAns (ℍ := ℍ) QS HStack InvStack) stackRet := by
  rintro F k w ls O v ρ _ _ _ _ _ ⟨rfl, rfl, rfl⟩
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HStack InvStack)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  show twp (ℍ := ℍ) F _ k w ls [] ((Expr.lam retBody).subst 0 Val.unit) _
  rw [ret_after]
  refine twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨_, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc hσ hρ hap hcov hv hls hO' F' hF'm hF'M
  obtain rfl := compS_empty_left_eq hc
  have hQD := valPost_down QB_down
  cases ts with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hP
    refine twp_det hQD (fun μ => step1Only_plug (Head.beta μ _ (stateVal HStack [])) rfl .hole) ?_
    rw [Kont.plug, stateVal, ret_s1]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HStack (poolVal []) _) rfl .hole) ?_
    rw [Kont.plug, ret_s2]
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    rw [Kont.plug, ret_nil]
    exact twp_here (fun μ => final_val μ _) fun w₁ ρ₁ ls₁ O₁ _ hr₁ _ hO₁ => by
      cases hO₁; exact ⟨Val.unit, rfl, rfl, rfl, RR.of_empty hr₁⟩
  | cons t ts =>
    cases j with
    | zero => exact twp_zero
    | succ j₀ =>
    refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HStack (t :: ts))) rfl
      .hole) ?_
    rw [Kont.plug, stateVal, ret_s1]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HStack (poolVal (t :: ts)) _) rfl
      .hole) ?_
    rw [Kont.plug, ret_s2]
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair t.κ (poolVal ts)) _ _) rfl .hole) ?_
    rw [Kont.plug, ret_cons]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ t.κ (poolVal ts) _) rfl .hole) ?_
    rw [Kont.plug, ret_cons_let]
    have hB : t.en.PBv t.v j₀ w₀ ls₀ Val.unit PMap.empty := by
      rw [(hi t List.mem_cons_self).1]; exact ⟨rfl, rfl⟩
    simp only [List.nil_append] at hF'M ⊢
    exact poolAns_resume hg hP hB (ResUT.compS_empty_right _) (noneAt_empty _) hcov hv hF'm hF'M
      (fun u hu => hi u (List.mem_cons_of_mem _ hu))

/-- **The stack scheduler meets `SchedOKT`** with its answers functions of its pool. -/
theorem stack_schedOK :
    SchedOKT (ℍ := ℍ) TP nP qsP stackRet hsStack QS (PoolAns (ℍ := ℍ) QS HStack InvStack) := by
  refine ⟨fun m i hm => by simp [TP, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    poolAns_down _ _ _, stackRet_ok, fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TP_some h
    rfl
  · obtain ⟨-, -, rfl⟩ := TP_some h
    exact hj
  · obtain ⟨-, rfl, rfl⟩ := TP_some h
    exact ⟨stackClause, by simp [clauseAt, hsStack, Val.pair, stackClause, Val.lam, IsVal.lam],
      stackClause_ok⟩

/-! ### A closed program through the headline -/

theorem kU_unit {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableT TP) QS Fb F n w ls [] (kA.plug (.val Val.unit)) PMap.empty := by
  refine cerwpT_det (TP_down QB_down) (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    .hole) ?_
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem kU_cancel {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableT TP) QS Fb F n w ls []
      (ccatchE (kA.dead.plug (raiseE (.val (cancelVal none))))) PMap.empty := by
  refine cerwpT_det (TP_down QB_down) (fun μ => step1Only_plug (Head.cancel μ kA rfl) rfl
    .hole) ?_
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

/-- **`let _ = park () in ()` at the park table**, owning nothing, at every index and frame
condition: it parks, cancellable; resumed or cancelled it answers `()`. -/
theorem taskU_cerwpT (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT TP) QS Fb F n w ls [] taskA PMap.empty := by
  show cerwpT (ℍ := ℍ) (opTableT TP) QS Fb F n w ls [] (kA.plug (performE (.val (opPayload nP 0
    Val.unit)))) PMap.empty
  refine cerwpT_perform kA rfl (show TP nP 0 = some enPark by simp [TP]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨trivial, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩,
    (⟨(fun _ => rfl), fun w' ρ' ls' O' _ hr' _ hO' => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
      (fun _ _ k' hk' => ?_)⟩⟩ : contShareT enPark Fb n w₀ ls₀ [] kA Val.unit
        (cerwpTC (ℍ := ℍ) (opTableT TP) QS Fb n) PMap.empty)⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := RR.of_empty hr'
    obtain rfl := compS_empty_right_eq hcσ
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact kU_unit
  · obtain rfl := RR.of_empty hr'
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact kU_cancel

/-- The program: `(hnd HStack (let _ = park () in ())) s₀`. -/
def stackProg : Expr := .app (hndE HStack taskA) (stateVal HStack []).1

/-- **`stackProg` is safe, or diverges**, through `PoolSchedAdequacyT`, every premise discharged. -/
theorem stackProg_safe : OrDiverges (ℍ := ℍ) stackProg :=
  poolSchedAdequacyT beforeP TP nP qsP stackRet hsStack QS QS InvStack _ _ taskA
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) stack_schedOK (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    fun n => taskU_cerwpT n _ _ _ _

end BoCa.Fig16.Tree.Wp.SchedProgs.Stack

end
