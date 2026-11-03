import Core.TreeSchedProgs
import Core.TreeSchedPool

/-!
# The park stepper: a task parks holding a share, and is resumed or cancelled  `[spec §62]`

A stepper whose one operation `park` is cancellable and hands the task's continuation, with the
share it owns, back to whoever ran the task (`schedP_ok`). A relay running tasks under it holds
their continuations as a pool (`Core/TreeSchedPool.lean`): `QP`'s continuation is `KapSchedT` at the
empty mask (a parked task owns no record at its stop), so it joins a pool (`poolT_park`), and is
resumed (`poolT_resume`) or cancelled under the stepper again (`poolT_cancel`).
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
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt freeE)

/-- The stepper's name. -/
abbrev nP : UInt32 := 3

/-- `park`: cancellable, no payload and no answer resource; the continuation owns its share. -/
def enPark : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ O => O = []

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
    (∃ κ : Val, v = Val.inj₁ κ ∧ O = [] ∧
      KapSchedT (ℍ := ℍ) (fun j w' ls' O' v' ρ' => if _h : j < k then QP Qt j w' ls' O' v' ρ'
        else False) (fun _ => False) enPark HP k w ls O Val.unit κ ρ) ∨
    (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ)
termination_by k => k

theorem QP_iff {Qt : TPostV} {k : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {v : Val} {ρ : TRes w.K} :
    QP (ℍ := ℍ) Qt k w ls O v ρ ↔
      (∃ κ : Val, v = Val.inj₁ κ ∧ O = [] ∧
        KapSchedT (ℍ := ℍ) (QP (ℍ := ℍ) Qt) (fun _ => False) enPark HP k w ls O Val.unit κ ρ) ∨
      (∃ r : Val, v = Val.inj₂ r ∧ Qt k w ls O r ρ) := by
  rw [QP]
  constructor
  · rintro (⟨κ, h₁, h₂, h₃⟩ | h)
    · exact Or.inl ⟨κ, h₁, h₂, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₃⟩
    · exact Or.inr h
  · rintro (⟨κ, h₁, h₂, h₃⟩ | h)
    · exact Or.inl ⟨κ, h₁, h₂, kapSchedT_congr (fun j hj _ _ _ _ _ hq => by
        simpa [hj] using hq) h₃⟩
    · exact Or.inr h

theorem QP_down {Qt : TPostV} (hQt : Qt.Down) : TPostV.Down (QP (ℍ := ℍ) Qt) := by
  intro k w ls O v ρ h
  rcases QP_iff.mp h with ⟨κ, h₁, h₂, h₃⟩ | ⟨r, h₁, h₂⟩
  · exact QP_iff.mpr (Or.inl ⟨κ, h₁, h₂, KapSchedT.down h₃⟩)
  · exact QP_iff.mpr (Or.inr ⟨r, h₁, hQt _ _ _ _ _ _ h₂⟩)

theorem parkClause_ok {Qt : TPostV} (hQt : Qt.Down) :
    SchedClauseT (ℍ := ℍ) TP nP HP (QP (ℍ := ℍ) Qt) enPark parkClause := by
  rintro M F k w ls O v κ ρ _ hMh hoc _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  change O = [] at hoc
  subst hoc
  obtain rfl := compS_empty_left_eq hc
  have hM : ∀ x, (M x ∨ recMask ([] : List (FrameRecT w.K)) x) → False := fun x hx =>
    hx.elim (maskHist_nil (fun i en h w O ho => by obtain ⟨-, -, rfl⟩ := TP_some h; exact ho)
      hMh x) (by simp [recMask])
  rw [cerwpTE_iff]
  have hD := valPost_down (QP_down (ℍ := ℍ) hQt)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  show twp (ℍ := ℍ) F _ k w ls [] (.letpair (.val (Val.pair Val.unit κ)) (.inj₁ (.var 0))) _
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  have e : ((Expr.inj₁ (.var 0)).subst 0 (κ.shift 1 0)).subst 0 Val.unit = (Val.inj₁ κ).1 := by
    simp [Expr.subst, Val.inj₁]
    rw [Expr.subst_shift 0 0 0 _ _ (by omega) (by omega), Expr.shift_zero]
  rw [e]
  refine twp_here (fun μ => final_val μ _) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  cases hO
  exact ⟨_, rfl, QP_iff.mpr (Or.inl ⟨κ, rfl, rfl,
    KapSchedT.kripke (KapSchedT.mask_mono (fun x hx => hM x hx) hκ) hE hr
      (KeepRel.of_srecsRR hl _) .nil⟩)⟩

theorem parkRet_ok {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) :
    SchedRetT (ℍ := ℍ) TP nP Qt (QP (ℍ := ℍ) Qt) stepRet := by
  intro M F k w ls O v ρ _ _ _ _ _ _ hv
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

/-- **A task run under the park stepper**, owning no record at its start, under any frame
condition whose frames are valid. -/
theorem parked_twp {Qt : TPostV} (hQt : Qt.Down) (hst : QtStable Qt) {F : TFrame}
    (hFm : F.Mono) (hFv : ∀ w ρf, F w ρf → ResUT.Valid ρf) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (he : cerwpT (ℍ := ℍ) (opTableT TP) Qt (fun _ _ => True) n w ls [] e ρ) :
    twp (ℍ := ℍ) F (valPost (QP (ℍ := ℍ) Qt)) n w ls [] (hndE HP e) ρ :=
  cerwpT_schedHandle (schedP_ok hQt hst) n (fun _ => False) F _ w ls [] e ρ hFm
    (maskHist_empty _ _) (fun w ρf h => fdMask_of_false (fun _ h => h) (hFv w ρf h))
    (fun x hx => by simp [recMask] at hx) (fun _ _ _ => trivial) he

/-- **A parked task joins a pool**: `QP`'s continuation, at the empty mask, its records none. -/
def parkedT (Qt : TPostV) (k : Nat) (κ : Val) : StoredT :=
  ⟨QP (ℍ := ℍ) Qt, fun _ => False, enPark, HP, k, Val.unit, κ⟩

theorem parked_mask (x : BoCa.Loc) {K : WCactus} :
    (fun _ => False : BoCa.Loc → Prop) x ↔ recMask ([] : List (FrameRecT K)) x := by
  simp [recMask]

end BoCa.Fig16.Tree.Wp.SchedProgs.Park

end
