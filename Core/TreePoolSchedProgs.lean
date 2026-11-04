import Core.TreePoolSched
import Core.TreeSchedRelay
import Core.TreeSemC

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

/-- The stack scheduler's invariant: every entry a ready task stopped at `park`. -/
def InvStack (ts : List StoredJ) : Prop :=
  ∀ t ∈ ts, t.t.en = enPark ∧ t.t.v = Val.unit ∧ t.join = false

/-- The program's answer: `()`, owning nothing. -/
abbrev QS : TPostV := QB

/-- **A task's answer under the stack schedulers**: `()`, owning no record, holding copies of
lends (`ViewsT`), which its end hands to the nearest joiner. -/
def QV : TPostV := fun _ _ _ O r ρ => r = Val.unit ∧ O = [] ∧ ViewsT ρ

theorem QV_down : QV.Down := fun _ _ _ _ _ _ h => h

theorem QS_QV {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {v : Val}
    {ρ : TRes w.K} (h : QS k w ls O v ρ) : QV k w ls O v ρ := by
  obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, ViewsT.empty⟩

/-- The resumed top, handed the rest, after the steps of `λs. …` and `case`/`let`. -/
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

/-- The return clause's body under `λv. λs.`, and its first branch: the top's entry
`((tag, κ), s′)`, `κ` resumed with `(h, s′)`. -/
def retL : Expr :=
  .letpair (.var 0) (.letpair (.var 1)
    (.app (.app (.app (.var 0) (.inj₁ .unit)) .unit) (.pair (.var 6) (.var 2))))

def retBody : Expr := .letpair (.var 0) (.case (.var 0) retL (.var 4))

/-- `λv. λ(h, p). case p {inj₁ q. let (e, s′) = q in let (_, κ) = e in κ (inj₁ ()) () (h, s′) |
inj₂ _. v}`. -/
def stackRet : Val := Val.lam (.lam retBody)

def hsStack : Val := Val.pair stackClause Val.unit
def HStack : Val := hndVal nP qsP stackRet hsStack

/-- A substitution below a shift by more than its index undoes one step of the shift. -/
theorem subst_shift0' (d j : Nat) (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

/-- **An entry the return clause may resume**: at `()` with what it has collected (copies of
lends; nothing for a task that is not a joiner). -/
def RetOK (t : StoredJ) : Prop :=
  ∀ k w (ls : List (SRecT w.K)) (c : TRes w.K), ViewsT c → (t.join = false → c = PMap.empty) →
    t.t.en.PBv t.t.v k w ls Val.unit c

/-! ### The scheduler meets `SchedOKT` at `PoolAns`, for every stack -/

/-- **The park clause**: park the stopped task, resume the stack's top (the task just parked) with
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
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hH hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvStack) false (fun _ => False) Val.unit hκ' hj hg hP
    hc' hσ hρ hH (fun _ h => h.elim) hap (CovR.of_compS_left hc' hcov) hls hO'
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HStack ts)) rfl .hole) ?_
  rw [clause_beta]
  exact poolAns_resume hg' hP' (a := Val.unit) (σ := PMap.empty)
    (fun c σ' _ hj hcσ => by
      obtain rfl := hj rfl
      obtain rfl := compS_empty_left_eq hcσ
      exact ⟨rfl, rfl⟩)
    (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _) (HoldsIn.empty _ _) hcov hv hF'm hF'M hi

/-- **The return clause**, for any scheduler whose invariant says the return clause may resume
each entry (`RetOK`): the finished task's copies handed to the nearest joiner, the stack's top
resumed with the rest (`poolAns_depositResume`); or, the stack empty, the task's answer the
program's, its copies then nothing (`ViewsT.eq_empty`). -/
theorem stackRet_okAt {H : Val} {Inv : List StoredJ → Prop}
    (hInv : ∀ t ts, Inv (t :: ts) → RetOK t ∧ Inv ts) :
    SchedRetT (ℍ := ℍ) QV (PoolAns (ℍ := ℍ) QS H Inv) stackRet := by
  rintro F k w ls O v ρ _ _ _ _ _ ⟨rfl, rfl, hVρ⟩
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS H Inv)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  cases hO
  have hV₀ : ViewsT ρ₀ := hVρ.rr hr
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc hσ hρA hρH hap hcov hv hls hO' F' hF'm hF'M
  have hQD := valPost_down QB_down
  cases ts with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hP
    obtain rfl := compS_empty_right_eq hc
    obtain rfl := hV₀.eq_empty hv hρH
    refine twp_det hQD (fun μ => step1Only_plug (Head.beta μ _ (stateVal H [])) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateVal, poolVal, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ H (Val.inj₂ Val.unit) _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    exact twp_here (fun μ => final_val μ ⟨_, .unit⟩) fun w₁ ρ₁ ls₁ O₁ _ hr₁ _ hO₁ => by
      cases hO₁; exact ⟨Val.unit, rfl, rfl, rfl, RR.of_empty hr₁⟩
  | cons t ts =>
    cases j with
    | zero => exact twp_zero
    | succ j₀ =>
    refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal H (t :: ts))) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateVal, poolVal, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ H (poolVal (t :: ts)) _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, poolVal, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair t.tag t.t.κ) (poolVal ts)) _ _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair t.tag t.t.κ) (poolVal ts) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ t.tag t.t.κ _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    simp only [List.nil_append] at hF'M hρA hap ⊢
    exact poolAns_depositResume hg hP (ResUT.CompS.comm hc) hV₀ hρH hρA
      (fun c hV hj => (hInv t ts hi).1 _ _ _ c hV hj) hcov hv hF'm hF'M (hInv t ts hi).2

theorem stackRet_ok : SchedRetT (ℍ := ℍ) QV (PoolAns (ℍ := ℍ) QS HStack InvStack) stackRet :=
  stackRet_okAt fun t ts hi => ⟨fun _ _ _ c _ hj => by
      obtain ⟨he, -, hjn⟩ := hi t List.mem_cons_self
      rw [hj hjn, he]; exact ⟨rfl, rfl⟩,
    fun u hu => hi u (List.mem_cons_of_mem _ hu)⟩

/-- **The stack scheduler meets `SchedOKT`** with its answers functions of its stack. -/
theorem stack_schedOK :
    SchedOKT (ℍ := ℍ) TP nP qsP stackRet hsStack QV (PoolAns (ℍ := ℍ) QS HStack InvStack) := by
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

theorem taskU_cerwpTV (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT TP) QV Fb F n w ls [] taskA PMap.empty :=
  cerwpT_post_mono (opTableT_local TP) (fun _ _ _ _ _ _ h => QS_QV h) (taskU_cerwpT n Fb F w ls)

/-- The program: `(hnd HStack (let _ = park () in ())) s₀`. -/
def stackProg : Expr := .app (hndE HStack taskA) (stateVal HStack []).1

/-- **`stackProg` is safe, or diverges**, through `PoolSchedAdequacyT`, every premise discharged. -/
theorem stackProg_safe : OrDiverges (ℍ := ℍ) stackProg :=
  poolSchedAdequacyT beforeP TP nP qsP stackRet hsStack QV QS InvStack _ _ taskA
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) stack_schedOK (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) fun n => taskU_cerwpTV n _ _ _ _

end BoCa.Fig16.Tree.Wp.SchedProgs.Stack

end
