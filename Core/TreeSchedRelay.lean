import Core.TreeSchedProgs
import Core.TreeSchedPool
import Core.TreeLend
import Core.Fix

/-!
# The park stepper: a task parks holding a share, and is resumed or cancelled  `[spec §62]`

A stepper whose one operation `park` is cancellable and hands the task's continuation, with the
share it owns, back to whoever ran the task (`schedP_ok`). A relay running tasks under it holds
their continuations as a pool (`Core/TreeSchedPool.lean`): `QP`'s continuation is `KapSchedT` at
the masks of the records the parked task owns at its stop, so it joins a pool (`poolT_park`), and
is resumed (`poolT_resume`) or cancelled under the stepper again (`poolT_cancel`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.PingPong (stepRet QtStable)
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt freeE ccatchE
  raiseE cancelVal)

/-- The stepper's name. -/
abbrev nP : UInt32 := 3

/-- `park`: cancellable, no payload and no answer resource; the continuation owns its share. The
parked branch may own records at the stop. -/
def enPark : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ _ => True

def TP : OpTabT := fun m i => if m = nP ∧ i = 0 then some enPark else none

theorem TP_some {m i : UInt32} {en : OpEntT} (h : TP m i = some en) :
    m = nP ∧ i = 0 ∧ en = enPark := by
  unfold TP at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

/-- `λ(_, κ). inj₁ κ`: hand the continuation to whoever ran the task. -/
def parkClause : Val := Val.lam (.letpair (.var 0) (.inj₁ (.var 0)))
/-- `park`'s tag is cancellable (`1`). -/
def qsP : Val := Val.pair (Val.i32 1) Val.unit
def hsP : Val := Val.pair parkClause Val.unit
def HP : Val := hndVal nP qsP stepRet hsP

/-- **What a task run under the park stepper answers**: parked, its continuation and the share it
owns, resumable and cancellable under the stepper at the answers below the index; or its end. -/
def QP (Qt : TPostV) : (k : Nat) → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Val →
    TRes w.K → Prop
  | k, w, ls, O, v, ρ =>
    (∃ κ : Val, v = Val.inj₁ κ ∧
      KapSchedT (ℍ := ℍ) (fun j w' ls' O' v' ρ' => if _h : j < k then QP Qt j w' ls' O' v' ρ'
        else False) (recMask O) enPark HP k w ls O Val.unit κ ρ) ∨
    (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ)
termination_by k => k

theorem QP_iff {Qt : TPostV} {k : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {v : Val} {ρ : TRes w.K} :
    QP (ℍ := ℍ) Qt k w ls O v ρ ↔
      (∃ κ : Val, v = Val.inj₁ κ ∧
        KapSchedT (ℍ := ℍ) (QP (ℍ := ℍ) Qt) (recMask O) enPark HP k w ls O Val.unit κ ρ) ∨
      (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ) := by
  rw [QP]
  constructor
  · rintro (⟨κ, h₁, h₃⟩ | h)
    · exact Or.inl ⟨κ, h₁, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₃⟩
    · exact Or.inr h
  · rintro (⟨κ, h₁, h₃⟩ | h)
    · exact Or.inl ⟨κ, h₁, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₃⟩
    · exact Or.inr h

theorem QP_down {Qt : TPostV} (hQt : Qt.Down) : TPostV.Down (QP (ℍ := ℍ) Qt) := by
  intro k w ls O v ρ h
  rcases QP_iff.mp h with ⟨κ, h₁, h₃⟩ | ⟨r, h₁, h₂⟩
  · exact QP_iff.mpr (Or.inl ⟨κ, h₁, KapSchedT.down h₃⟩)
  · exact QP_iff.mpr (Or.inr ⟨r, h₁, hQt _ _ _ _ _ _ h₂⟩)

theorem parkClause_ok {Qt : TPostV} (hQt : Qt.Down) :
    SchedClauseT (ℍ := ℍ) HP (QP (ℍ := ℍ) Qt) enPark parkClause := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (QP_down (ℍ := ℍ) hQt)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  show twp (ℍ := ℍ) F _ k w ls O (.letpair (.val (Val.pair Val.unit κ)) (.inj₁ (.var 0))) _
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  have e : ((Expr.inj₁ (.var 0)).subst 0 (κ.shift 1 0)).subst 0 Val.unit = (Val.inj₁ κ).1 := by
    simp [Expr.subst, Val.inj₁]
    rw [Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]
  rw [e]
  refine twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  exact ⟨_, rfl, QP_iff.mpr (Or.inl ⟨κ, rfl,
    KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
      (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)⟩)⟩

theorem parkRet_ok {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    SchedRetT (ℍ := ℍ) Qt (QP (ℍ := ℍ) Qt) stepRet := by
  intro F k w ls O v ρ _ _ _ _ _ hv
  rw [cerwpTE_iff]
  refine twp_det (valPost_down (QP_down (ℍ := ℍ) hQt))
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e : (Expr.inj₂ (.var 0)).subst 0 v = (Val.inj₂ v).1 := by simp [Expr.subst, Val.inj₂]
  rw [e]
  exact twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr _ hO =>
    ⟨_, rfl, QP_iff.mpr (Or.inr ⟨v, rfl, hst k w w₀ ls O ls₀ O₀ v ρ ρ₀ hE hr hO hv⟩)⟩

/-- **The park stepper meets `SchedOKT`**, at every final answer of the task. -/
theorem schedP_ok {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    SchedOKT (ℍ := ℍ) TP nP qsP stepRet hsP Qt (QP (ℍ := ℍ) Qt) := by
  refine ⟨fun m i hm => by simp [TP, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    QP_down hQt, parkRet_ok hQt hst, fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TP_some h
    rfl
  · obtain ⟨-, -, rfl⟩ := TP_some h
    exact hj
  · obtain ⟨-, rfl, rfl⟩ := TP_some h
    exact ⟨parkClause, by simp [clauseAt, hsP, Val.pair, parkClause, Val.lam, IsVal.lam],
      parkClause_ok hQt⟩

/-- **A task run under the park stepper**, owning the records `O` at its start, under any frame
condition whose frames avoid a mask `M` holding their masks: the stepper's `[handle]`. The task's
base frame condition is met by every valid frame; its present one by every frame avoiding `M`. -/
theorem parked_twp {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) {F : TFrame}
    (hFm : F.Mono) {M : BoCa.Loc → Prop} (hFM : ∀ w ρf, F w ρf → fdMask M w ρf) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hOM : ∀ x, recMask O x → M x) {Fb Fe : TFrame} (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf)
    (hFe : ∀ w ρf, fdMask M w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT TP) Qt Fb Fe n w ls O e ρ) :
    twp (ℍ := ℍ) F (valPost (QP (ℍ := ℍ) Qt)) n w ls O (hndE HP e) ρ :=
  cerwpT_schedHandle (schedP_ok hQt hst) n M F Fb Fe w ls O e ρ hFm hFM hOM hFb hFe he

/-- **A parked task as a pool's stored task**: `QP`'s continuation at its mask `M`. -/
def parkedT (Qt : TPostV) (k : Nat) (M : BoCa.Loc → Prop) (κ : Val) : StoredT :=
  ⟨QP (ℍ := ℍ) Qt, M, enPark, HP, k, Val.unit, κ⟩

/-! ### Task A: parks holding a copy of a view, answers it back -/

theorem TP_down {Qt : TPostV} (hQt : Qt.Down) {Ψ : ContT} {F : TFrame} :
    (cerwpPostT (opTableT TP) Qt Ψ F).Down :=
  cerwpPostT_down hQt
    (fun m i en h k w ls v ρ hA => by obtain ⟨-, -, rfl⟩ := TP_some h; exact hA)

/-- **Task A**: `let _ = park () in ()`. Its resource is a copy of a lend's view, held across the
park and answered back. -/
def taskA : Expr := .app (.lam (.val Val.unit)) (performE (.val (opPayload nP 0 Val.unit)))

def kA : Kont := .appR (.lam (.val Val.unit)) .hole

/-- A's answer: `()`, owning no record, holding the copy `viewRes α ℓ`. -/
def QA (α : Life) (l : BoCa.Loc) : TPostV := fun _ _ _ O r ρ =>
  r = Val.unit ∧ O = [] ∧ ρ = viewRes α l

theorem QA_down (α : Life) (l : BoCa.Loc) : (QA α l).Down := fun _ _ _ _ _ _ h => h

theorem QA_stable (α : Life) (l : BoCa.Loc) : QtStable (QA α l) := by
  intro k w w₀ ls O ls₀ O₀ r ρ ρ₀ hE hr hO ⟨h₁, h₂, h₃⟩
  subst h₂; subst h₃; cases hO
  exact ⟨h₁, rfl, rr_view_eq hr⟩

/-- A's last step: `(λ_. ()) ()`, the copy answered back. -/
theorem kA_unit {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} (α : Life)
    (l : BoCa.Loc) :
    cerwpT (ℍ := ℍ) (opTableT TP) (QA α l) Fb F n w ls [] (kA.plug (.val Val.unit))
      (viewRes α l) := by
  refine cerwpT_det (TP_down (QA_down α l)) (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl
    .hole) ?_
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, rr_view_eq hr⟩

/-- A's cancel: `ccatch ((λ_. ()) (raise cancel))` answers `()` in one step, the copy kept. -/
theorem kA_cancel {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} (α : Life)
    (l : BoCa.Loc) :
    cerwpT (ℍ := ℍ) (opTableT TP) (QA α l) Fb F n w ls []
      (ccatchE (kA.dead.plug (raiseE (.val (cancelVal none))))) (viewRes α l) := by
  refine cerwpT_det (TP_down (QA_down α l)) (fun μ => step1Only_plug (Head.cancel μ kA rfl) rfl
    .hole) ?_
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, rr_view_eq hr⟩

/-- **Task A at the park stepper's table**, from a copy of a view, at every index and frame
condition: it parks, cancellable; resumed it answers the copy, cancelled it answers the copy. -/
theorem taskA_cerwpT (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) (α : Life)
    (l : BoCa.Loc) :
    cerwpT (ℍ := ℍ) (opTableT TP) (QA α l) Fb F n w ls [] taskA (viewRes α l) := by
  show cerwpT (ℍ := ℍ) (opTableT TP) (QA α l) Fb F n w ls [] (kA.plug (performE (.val (opPayload nP 0
    Val.unit)))) (viewRes α l)
  refine cerwpT_perform kA rfl (show TP nP 0 = some enPark by simp [TP]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := rr_view_eq hr
  refine ⟨trivial, PMap.empty, viewRes α l, ResUT.CompS.comm (ResUT.compS_empty_right _), ⟨rfl, rfl⟩,
    (⟨(fun h => by cases h), fun w' ρ' ls' O' _ hr' _ hO' => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
      (fun _ _ k' hk' => ?_)⟩⟩ : contShareT enPark Fb n w₀ ls₀ [] kA Val.unit
        (cerwpTC (ℍ := ℍ) (opTableT TP) (QA α l) Fb n) (viewRes α l))⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := rr_view_eq hr'
    obtain rfl := compS_empty_right_eq hcσ
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact kA_unit α l
  · obtain rfl := rr_view_eq hr'
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact kA_cancel α l

/-! ### The relay's loop: drive a parked task to its end -/

/-- The loop's body, `self` at 1 and the task's answer `r` at 0:
`case r {inj₁ κ. self (κ (inj₁ ()) ()), inj₂ x. x}`. -/
def driveB : Expr :=
  .case (.var 0) (.app (.var 2) (.app (.app (.var 0) (.inj₁ .unit)) .unit)) (.var 0)

theorem driveB_closed : closedAt 2 driveB = true := rfl

/-- **The relay's loop**, `Z (λself. λr. driveB)`: a parked task is resumed, and resumed again
each time it parks, until it answers. -/
def driveV : Val := fixV driveB

/-- Steps that take every heap to itself, in front of a `twp`, for free. -/
theorem twp_pure {F : TFrame} {Q : TPost} (hQ : Q.Down) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e e' : Expr} {ρ : TRes w.K}
    (hs : PureSteps (ℍ := ℍ) e e') (h : twp (ℍ := ℍ) F Q n w ls O e' ρ) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  revert h
  induction hs with
  | refl => exact id
  | tail _ hbc ih =>
      intro h
      exact ih (twp_det hQ (fun μ => by
        obtain ⟨K, a, a', rfl, rfl, hh, hn⟩ := hbc μ
        exact step1Only_plug hh hn K) h)

theorem selfV_drive_closed : closedAt 0 (selfV driveB).1 = true := selfV_closed driveB_closed

theorem drive_beta_at {S : Val} (hS : closedAt 0 S.1 = true) (r : Val) :
    (driveB.subst 1 S).subst 0 r = .case r.1
      (.app S.1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)) (.var 0) := by
  simp [driveB, Expr.subst, shift_closedAt _ 1 hS (Nat.zero_le _),
    subst_closedAt _ _ hS (Nat.zero_le _)]

/-- `drive r` unrolled: `case r {inj₁ κ. selfV (κ (inj₁ ()) ()), inj₂ x. x}`. -/
theorem drive_beta (r : Val) :
    (driveB.subst 1 (selfV driveB)).subst 0 r = .case r.1
      (.app (selfV driveB).1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)) (.var 0) :=
  drive_beta_at selfV_drive_closed r

theorem drive_case₁_at {S : Val} (hS : closedAt 0 S.1 = true) (κ : Val) :
    (Expr.app S.1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)).subst 0 κ =
      (Kont.appR S.1 .hole).plug (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val Val.unit)) := by
  simp [Expr.subst, subst_closedAt _ _ hS (Nat.zero_le _), Kont.plug, Val.inj₁]

theorem drive_case₁ (κ : Val) :
    (Expr.app (selfV driveB).1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)).subst 0 κ =
      (Kont.appR (selfV driveB).1 .hole).plug
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val Val.unit)) :=
  drive_case₁_at selfV_drive_closed κ

theorem drive_steps₁ (κ : Val) : ∀ μ, Step1Only (ℍ := ℍ) μ (.app driveV.1 (Val.inj₁ κ).1) μ
    (.case (Val.inj₁ κ).1
      (.app (selfV driveB).1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)) (.var 0)) := by
  intro μ
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ (driveB.subst 1 (selfV driveB)) (Val.inj₁ κ))
    rfl .hole
  rw [drive_beta] at h
  rw [driveV, fixV_eq driveB_closed]
  exact h

theorem drive_steps₂ (x : Val) : ∀ μ, Step1Only (ℍ := ℍ) μ (.app driveV.1 (Val.inj₂ x).1) μ
    (.case (Val.inj₂ x).1
      (.app (selfV driveB).1 (.app (.app (.var 0) (.inj₁ .unit)) .unit)) (.var 0)) := by
  intro μ
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ (driveB.subst 1 (selfV driveB)) (Val.inj₂ x))
    rfl .hole
  rw [drive_beta] at h
  rw [driveV, fixV_eq driveB_closed]
  exact h

/-- **A value beside the pool, at every extension**: the value's resource in `Qt` (carried along
re-reading, `QtStable`), the pool beside it. -/
theorem poolPost_here {Qt : TPostV} (hst : QtStable Qt) {ts : List StoredT} {F : TFrame}
    {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {Oa Ob : List (FrameRecT w.K)}
    {a b ρ : TRes w.K} {x : Val} (hx : Qt k w ls Oa x a) (hP : PoolT (ℍ := ℍ) ts w ls Ob b)
    (hc : ResUT.CompS a b ρ) (hb : NoneAt (recMask Oa) b) (ha : NoneAt (recMask Ob) a)
    (hap : ∀ p ∈ Oa, ∀ q ∈ Ob, p.le ≠ q.le) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) :
    twp (ℍ := ℍ) F (PoolPost (ℍ := ℍ) (valPost Qt) ts) k w ls (Oa ++ Ob) x.1 ρ := by
  refine twp_here (fun μ => final_val μ x) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  obtain ⟨Oa₀, Ob₀, rfl, hOa, hOb⟩ := forall₂_append_left hO
  obtain ⟨a₀, b₀, hra, hrb, hc₀⟩ := RR.split_retype hE.1 hc hcov hE.2 hr
  have hva := (ResUT.Valid.split hc hv).1
  have hvb := (ResUT.Valid.split hc hv).2
  exact ⟨Oa₀, Ob₀, a₀, b₀, rfl, hc₀,
    ⟨x, rfl, hst k w w₀ ls Oa ls₀ Oa₀ x a a₀ (hE.of_compS_left hc) hra hOa hx⟩,
    hP.kripke (hE.of_compS_right hc) hrb hOb (KeepRel.of_srecsRR hl _)
      (hcov.of_compS_right hc) hvb,
    (NoneAt.rr hE.1 hvb hrb hb).mono fun y hy => (recMask_rr hOa y).mpr hy,
    (NoneAt.rr hE.1 hva hra ha).mono fun y hy => (recMask_rr hOb y).mpr hy,
    apart_rr hOa hOb hap⟩

/-- **Driving a parked task to its end keeps the pool.** The task's answer `r` under the park
stepper (`QP`, owning `Oa`, resource `a`) beside a pool `ts` of any length (owning `Ob`), the two
apart; under frames avoiding all their records. At every end of `drive r` the task has answered
in `Qt`, beside the pool held at the end world and list, still apart. By strong induction on the
index: a parked answer joins the pool (`poolT_park`), is resumed at its head (`poolT_resume`) one
index below, and what the resume answers is driven again (`selfV` unrolls to the loop). -/
theorem drive_twp {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    ∀ (k : Nat) (ts : List StoredT) (F : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (Oa Ob : List (FrameRecT w.K)) (a b ρ : TRes w.K) (r : Val), F.Mono →
      (∀ w' ρf, F w' ρf → fdMask (recMask (Oa ++ Ob)) w' ρf) →
      QP (ℍ := ℍ) Qt k w ls Oa r a → PoolT (ℍ := ℍ) ts w ls Ob b → ResUT.CompS a b ρ →
      NoneAt (recMask Oa) b → NoneAt (recMask Ob) a → (∀ p ∈ Oa, ∀ q ∈ Ob, p.le ≠ q.le) →
      CovR (sem w.Θ) w.K ρ → ResUT.Valid ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
      (∀ x ∈ Oa, CovR (sem w.Θ) w.K x.R) →
      twp (ℍ := ℍ) F (PoolPost (ℍ := ℍ) (valPost Qt) ts) k w ls (Oa ++ Ob)
        (.app driveV.1 r.1) ρ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ts F w ls Oa Ob a b ρ r hFm hFM hQ hP hc hb ha hap hcov hv hls hOc
  have hD := PoolPost.down (ℍ := ℍ) (valPost_down hQt) ts
  rcases QP_iff.mp hQ with ⟨κ, rfl, hκ⟩ | ⟨x, rfl, hx⟩
  · -- parked: join the pool, resume at its head, drive what it answers
    cases k with
    | zero => exact twp_zero
    | succ k₀ =>
    have hP' := poolT_park (t := parkedT Qt (k₀ + 1) (recMask Oa) κ) hκ (fun _ => Iff.rfl) hP hc
      hb ha hap (CovR.of_compS_left hc hcov) hls hOc
    refine twp_step (drive_steps₁ κ) ?_
    refine twp_det hD (fun μ => step1Only_plug (Head.case₁ μ κ _ _) rfl .hole) ?_
    rw [Kont.plug, drive_case₁]
    have hres : twp (ℍ := ℍ) F (PoolPost (ℍ := ℍ) (valPost (QP (ℍ := ℍ) Qt)) ts) k₀ w ls
        (Oa ++ Ob) (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val Val.unit)) ρ :=
      poolT_resume (k' := k₀) (a := Val.unit) (σ := PMap.empty) (F := F) hP'
      (by simp [parkedT]) ⟨rfl, rfl⟩ (ResUT.compS_empty_right ρ) (noneAt_empty _) hcov hv
      (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl hx)) (hFM w' ρf hf))
    refine twp_bind_fd hFm (fun _ _ h => h) _ (fun w₀ ρf hf => (hFM w₀ ρf hf).2) hres ?_
    intro k₁ hk₁ w' ls' O' t ρ' hcov' hv' hls' hO' hpost
    obtain ⟨Oa', Ob', a', b', rfl, hc', ⟨r', rfl, hQ'⟩, hP'', hb', ha', hap'⟩ := hpost
    refine twp_pure hD (selfV_steps_in driveB_closed .hole r') ?_
    exact ih k₁ (by omega) ts _ w' ls' Oa' Ob' a' b' ρ' r'
      (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => h.2) hQ' hP'' hc' hb' ha' hap'
      hcov' hv' hls' (fun x hx => hO' x (List.mem_append_left _ hx))
  · -- answered: `x`
    refine twp_det hD (drive_steps₂ x) ?_
    refine twp_det hD (fun μ => step1Only_plug (Head.case₂ μ x _ _) rfl .hole) ?_
    have e : (Expr.var 0).subst 0 x = x.1 := by simp [Expr.subst]
    rw [Kont.plug, e]
    exact poolPost_here hst hx hP hc hb ha hap hcov hv

end BoCa.Fig16.Tree.Wp.SchedProgs.Park

end
