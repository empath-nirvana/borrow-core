import Core.EffCancelTyped
import Targets.I.NoDropped
import Targets.Instance.CancelWitness

/-!
# The Instance — three cancel programs at `J₁` with unrestricted operations

Core's typed cancel programs (`Core/EffCancelTyped.lean`) at `J₁`, their rows tied to the effect
context `Ξu`, which declares `1` and `4` as resuming unrestricted operations `1 ↠ 1` and `2` and
`3` as abortive ones `1 ↠ 0`.  `Ξu` is not admissible: its resuming operations are `unr`.  Every
continuation is unrestricted, so the runs allocate no cell, and `look` computes them
(`lookRun`).

* **`progDropT`**: a finaliser raises `2`, kept; a later finaliser performs `4`, whose unrestricted
  handler drops its continuation, and the kept error with it.  Its complete run keeps an error and
  neither re-raises nor supersedes one: **`NoDroppedError` fails at `J₁` at `Ξu`**
  (`not_noDroppedError_unr`).  The restriction of the count to runs that capture no kept error is
  needed.
* **`cancelKeptT`**: a finaliser raises `3`, kept and re-raised at the canceller, and caught
  outside.  Its complete run keeps one error, re-raises one, and captures no context holding a kept
  error (`noDroppedErrorNKC_reads`): the restricted count is not vacuous.
* **`progNC₁T`**: a finaliser performs `4`, whose handler cancels the finaliser's continuation, a
  cancel nested in a cancel.  Its run reaches the cancel of `capture 4 H K` with a `ccatch` and a
  `cfin` frame in `K`: **`CancelsNoCtl` fails at `J₁` at `Ξu`** (`not_cancelsNoCtl_J₁`).
  `CancelsNoCtl` was S5's hypothesis before frame deadness; S5 no longer reads it.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.CancelIntercept (rSig pSig finR finKD injlV constC hU H₁T
  cancelCT thenU performU raiseU progDropT progNC₁T cancelKeptT progKDT progFinT bodyT K c₃ H₂ finV)
open BoCa.BoLo (Head Kont Steps Step1 Heap performE raiseE hndE hndVal opPayload cancelVal kappa
  ccatchE cfinE ubindE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt LMem runM stepM stepM_sound)

/-! ### The effect context -/

/-- `1` and `4` resuming unrestricted `1 ↠ 1`, `2` and `3` abortive unrestricted `1 ↠ 0`. -/
def Ξu : EffCtx := fun n =>
  if n = 1 ∨ n = 4 then [(.unr, .unit, .unit)]
  else if n = 2 ∨ n = 3 then [(.unr, .unit, .zero)]
  else []

/-- An operation `Ξu` declares. -/
def UOp (o : OpSig) : Prop :=
  o.i = 0 ∧ o.q = .unr ∧ o.A = .unit ∧
    (((o.n = 1 ∨ o.n = 4) ∧ o.B = .unit) ∨ ((o.n = 2 ∨ o.n = 3) ∧ o.B = .zero))

/-- A row of `Ξu`'s operations is tied to `Ξu`. -/
theorem rowAt_Ξu {S : Row} (h : ∀ o ∈ S, UOp o) : RowAt Ξu S := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  obtain ⟨hi, hq, hA, hB⟩ := h o hm
  rw [hi]
  rcases hB with ⟨h1 | h4, hB⟩ | ⟨h2 | h3, hB⟩
  · refine ⟨by rw [h1]; decide, by simp [Ξu, h1], ?_⟩
    simp [Ξu, h1, hq, hA, hB]
  · refine ⟨by rw [h4]; decide, by simp [Ξu, h4], ?_⟩
    simp [Ξu, h4, hq, hA, hB]
  · refine ⟨by rw [h2]; decide, by simp [Ξu, h2], ?_⟩
    simp [Ξu, h2, hq, hA, hB]
  · refine ⟨by rw [h3]; decide, by simp [Ξu, h3], ?_⟩
    simp [Ξu, h3, hq, hA, hB]

theorem uOp_rSig2 : UOp (rSig 2) := ⟨rfl, rfl, rfl, .inr ⟨.inl rfl, rfl⟩⟩
theorem uOp_rSig3 : UOp (rSig 3) := ⟨rfl, rfl, rfl, .inr ⟨.inr rfl, rfl⟩⟩
theorem uOp_pSig1 (F : CTy) : UOp (pSig 1 F) := ⟨rfl, rfl, rfl, .inl ⟨.inl rfl, rfl⟩⟩
theorem uOp_pSig4 (F : CTy) : UOp (pSig 4 F) := ⟨rfl, rfl, rfl, .inl ⟨.inr rfl, rfl⟩⟩

/-! ### The derivations, tied to `Ξu`

Core's derivations (`Core/EffCancelTyped.lean`), rule for rule, each `[perform]`, `[raise]` and
`[handle]` with its row tied to `Ξu`. -/

section Typing
variable {Δ : LifeCtx}

theorem du_idV (S : Row) (A : VTy) :
    CDerivesAt Ξu Δ [] (.val CancelIntercept.idV) (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret (.var (.here .nil)))))

theorem du_injlV (S : Row) (A B : VTy) :
    CDerivesAt Ξu Δ [] (.val injlV) (.val (retTy S A (.sum A B))) :=
  .bangThunkV (dead_noLive .nil) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.sumI₁ (.var (.here .nil))))))

theorem du_constC_raise (S : Row) {R : VTy} {v : Val}
    (hv : CDerivesAt Ξu Δ [⟨.unit, false⟩] (.val v) (.val R)) :
    CDerivesAt Ξu Δ [] (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .zero) (.ret .unit))) :=
  .bangThunkV (dead_noLive .nil) rfl (.lamDead (.effSub (RowLe.nil S) (.ret hv)))

theorem du_constC_op (S : Row) {R : VTy} {F : CTy} {v : Val}
    (hv : CDerivesAt Ξu Δ [⟨.tensor .unit (kTy S R .unr .unit F), true⟩] (.val v) (.val R)) :
    CDerivesAt Ξu Δ [] (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .unit) F)) := by
  show CDerivesAt Ξu Δ [] (.val (constC v))
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S R .unr .unit F)) (CTy.effOf S R)))))
  exact .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret hv)))

theorem du_cancelCT {S : Row} {F : CTy} (hF : F.isTop = false) (hle : RowLe (F.rowOf ++ S) S) :
    CDerivesAt Ξu Δ [] (.val cancelCT) (.val (clauseTy S .unit (.unr, .unit, .unit) F)) := by
  show CDerivesAt Ξu Δ [] (.val cancelCT)
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S .unit .unr .unit F)) (CTy.effOf S .unit)))))
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .bind (A := .thunk (.amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F)))
    (.left (.right (.dead .nil))) (.ret (.bangE (.var (.here (.cons (.cons .nil)))))) ?_
  have h₂ : CDerivesAt Ξu Δ [⟨.thunk (.amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F)), true⟩,
      ⟨kTy S .unit .unr .unit F, false⟩, ⟨.unit, true⟩,
      ⟨.tensor .unit (kTy S .unit .unr .unit F), false⟩]
      (.app (.var 0) (.val (Val.inj₂ Val.unit))) (.comp (cancelTy S F)) :=
    .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F))
      (.here (.cons (.drop rfl (.cons .nil)))))
  have hC : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
  refine .effSub hle ?_
  rw [← hC]
  exact h₂

/-- The inner `[then]` of `progKDT`: `perform 1 then x. x unwind raise 2` at `{1⟨{2}⟩, 2}`. -/
theorem du_thenK₁ :
    CDerivesAt Ξu Δ [] (thenU (performU 1) (raiseU 2))
      (.comp (CTy.effOf [pSig 1 (finR 2), rSig 2] .unit)) := by
  show CDerivesAt Ξu Δ [] (thenE (.var 0) (raiseU 2) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 2) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit))
      (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_pSig1 _) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 2) (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_rSig2)
      rfl rfl .unit (.unitI (.cons .nil))

/-- The outer `[then]` of `progKDT`: its finaliser performs `4` below the inner one's kept `2`. -/
theorem du_thenK₂ :
    CDerivesAt Ξu Δ [] (thenU (thenU (performU 1) (raiseU 2)) (performU 4))
      (.comp (CTy.effOf [pSig 1 finKD, rSig 2, pSig 4 (finR 2)] .unit)) := by
  show CDerivesAt Ξu Δ [] (thenE (.var 0) (performU 4) (thenU (performU 1) (raiseU 2))) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (finR 2), rSig 2])
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ du_thenK₁ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · refine ⟨pSig 1 finKD, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      refine (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.of_mem fun o ho => ?_⟩)
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at ho
      subst ho
      exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
    · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · intro n i o o' hf hf' hc
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    swap
    · simp [capB, rSig, VTy.isZero] at hc
    obtain rfl : o' = pSig 1 finKD := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => ?_, fun n i o h => ?_⟩
    · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at hm
      subst hm
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
    · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      simp only [List.mem_singleton] at hm
      subst hm
      refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      rw [PendLe]
      refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h,
        fun n i o h ha => ?_⟩
      obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at hm
      subst hm
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro _ o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · refine ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => ?_⟩
      exact ⟨fun _ => rfl, fun h => absurd h (by decide), trivial⟩
    · exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effPerform (o := pSig 4 (.ret .unit))
      (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_pSig4 _) rfl rfl (.unitI (.cons .nil))

/-- `hnd (1, H₁T) …` in `progKDT`, at the outer row `{2, 4⟨{2}⟩}`. -/
theorem du_midK :
    CDerivesAt Ξu Δ [] (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4)))
      (.comp (CTy.effOf [rSig 2, pSig 4 (finR 2)] .unit)) := by
  show CDerivesAt Ξu Δ [] (hndExpr 1 [.unr] (.pair (.val CancelIntercept.idV) (.pair (.val cancelCT) (.val Val.unit)))
    (thenU (thenU (performU 1) (raiseU 2)) (performU 4))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finKD)
    (rowAt_Ξu fun o ho => by
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact uOp_pSig1 _
      · exact uOp_rSig2
      · exact uOp_pSig4 _)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ .unit) (.tensorI .nil (du_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig, pSig]) (by simp) du_thenK₂
  refine RowLe.of_mem fun o ho => ?_
  rw [show finKD.rowOf ++ [rSig 2, pSig 4 (finR 2)] =
    [rSig 2, pSig 4 (finR 2), rSig 2, pSig 4 (finR 2)] from rfl] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- `progKDT c` at `F (1 ⊕ 1)`, tied to `Ξu`, for a clause `c` of `H₄ₒ` at the cancel row `{2}`. -/
theorem du_progKDT {c : Val}
    (hc : CDerivesAt Ξu Δ [] (.val c)
      (.val (clauseTy [rSig 2] (.sum .unit .unit) (.unr, .unit, .unit) (finR 2)))) :
    CDerivesAt Ξu Δ [] (progKDT c) (.comp (.ret (.sum .unit .unit))) := by
  show CDerivesAt Ξu Δ [] (hndExpr 2 [.unr] (.pair (.val CancelIntercept.idV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit)))
    (hndE (hU 4 injlV c) (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4)))))
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    (rowAt_Ξu fun o ho => by simp [Row.ofEff] at ho; subst ho; exact uOp_rSig2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ _)
      (.tensorI .nil (du_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) ?_
  show CDerivesAt Ξu Δ [] (hndExpr 4 [.unr] (.pair (.val injlV) (.pair (.val c) (.val Val.unit)))
    (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4))))
    (.comp (CTy.effOf [rSig 2] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    (rowAt_Ξu fun o ho => by
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl
      · exact uOp_pSig4 _
      · exact uOp_rSig2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_injlV _ .unit .unit) (.tensorI .nil hc (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) ?_
  refine .effSub (RowLe.of_mem fun o ho => ?_) du_midK
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- **`progDropT`, tied to `Ξu`**, at `F (1 ⊕ 1)`. -/
theorem du_progDropT : CDerivesAt Ξu Δ [] progDropT (.comp (.ret (.sum .unit .unit))) :=
  du_progKDT (du_constC_op _ (.sumI₁ (.unitI (.drop rfl .nil))))

end Typing

/-! ### `progNC₁T` and `cancelKeptT`, tied to `Ξu` -/

section Typing2
variable {Δ : LifeCtx}

/-- The `[then]` of `progFinT`: `perform 1 then x. x unwind perform 4` at `{4, 1⟨{4}⟩}`. -/
theorem du_thenP :
    CDerivesAt Ξu Δ [] (thenU (performU 1) (performU 4))
      (.comp (CTy.effOf [pSig 4 (.ret .unit), pSig 1 (CancelIntercept.finP 4)] .unit)) := by
  show CDerivesAt Ξu Δ [] (thenE (.var 0) (performU 4) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (CancelIntercept.finP 4), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 4 (.ret .unit), rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (CancelIntercept.finP 4) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    refine ⟨pSig 4 (.ret .unit), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    rw [PendLe]
    exact Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h,
      fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit))
      (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_pSig1 _) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effPerform (o := pSig 4 (.ret .unit))
      (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_pSig4 _) rfl rfl (.unitI (.cons .nil))

/-- `hnd (4, H₄ᵢ) [·]` around `progFinT`'s `[then]`, at the outer row `{1⟨{4}⟩}`. -/
theorem du_innerP :
    CDerivesAt Ξu Δ [] (hndE (hU 4 CancelIntercept.idV (constC Val.unit)) (thenU (performU 1) (performU 4)))
      (.comp (CTy.effOf [pSig 1 (CancelIntercept.finP 4)] .unit)) := by
  show CDerivesAt Ξu Δ [] (hndExpr 4 [.unr] (.pair (.val CancelIntercept.idV) (.pair (.val (constC Val.unit))
    (.val Val.unit))) (thenU (performU 1) (performU 4))) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)])
    (fs := fun _ => .ret .unit)
    (rowAt_Ξu fun o ho => by
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl
      · exact uOp_pSig4 _
      · exact uOp_pSig1 _)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ .unit) (.tensorI .nil (du_constC_op _ (.unitI (.drop rfl .nil)))
      (.unitI .nil)))
    (by decide) (by simp [pSig]) (by simp) du_thenP

/-- `hnd (1, H₁T) …` in `progFinT`, at the outer row `{4}`. -/
theorem du_midP :
    CDerivesAt Ξu Δ [] (hndE H₁T (hndE (hU 4 CancelIntercept.idV (constC Val.unit))
      (thenU (performU 1) (performU 4)))) (.comp (CTy.effOf [pSig 4 (.ret .unit)] .unit)) := by
  show CDerivesAt Ξu Δ [] (hndExpr 1 [.unr] (.pair (.val CancelIntercept.idV)
    (.pair (.val cancelCT) (.val Val.unit)))
    (hndE (hU 4 CancelIntercept.idV (constC Val.unit)) (thenU (performU 1) (performU 4)))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => CancelIntercept.finP 4)
    (rowAt_Ξu fun o ho => by
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl
      · exact uOp_pSig1 _
      · exact uOp_pSig4 _)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ .unit) (.tensorI .nil (du_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [pSig]) (by simp) ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (CancelIntercept.finP 4).rowOf ++ [pSig 4 (.ret .unit)] = [pSig 4 (.ret .unit), pSig 4 (.ret .unit)]
      from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨pSig 4 (.ret .unit), rfl, OpSig.LeF.refl _⟩
  · refine .effSub (RowLe.of_mem fun o ho => ?_) du_innerP
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 1 (CancelIntercept.finP 4), rfl, OpSig.LeF.refl _⟩

/-- **`progNC₁T`, tied to `Ξu`**, at `F 1`. -/
theorem du_progNC₁T : CDerivesAt Ξu Δ [] progNC₁T (.comp (.ret .unit)) := by
  show CDerivesAt Ξu Δ [] (hndExpr 4 [.unr] (.pair (.val CancelIntercept.idV)
    (.pair (.val cancelCT) (.val Val.unit)))
    (hndE H₁T (hndE (hU 4 CancelIntercept.idV (constC Val.unit)) (thenU (performU 1) (performU 4)))))
    (.comp (CTy.effOf [] .unit))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)])
    (fs := fun _ => .ret .unit)
    (rowAt_Ξu fun o ho => by simp [Row.ofEff] at ho; subst ho; exact uOp_pSig4 _)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ .unit)
      (.tensorI .nil (du_cancelCT rfl (by simp [RowLe.refl, CTy.rowOf])) (.unitI .nil)))
    (by decide) (by simp) (by simp) du_midP

/-- The `[then]` of `cancelKeptT`: `perform 1 then x. x unwind raise 3` at `{2, 1⟨{3}⟩, 3}`. -/
theorem du_then₃ :
    CDerivesAt Ξu Δ [] ((CancelIntercept.uF (raiseU 3) .hole).plug (performU 1))
      (.comp (CTy.effOf [rSig 2, pSig 1 (finR 3), rSig 3] .unit)) := by
  show CDerivesAt Ξu Δ [] (thenE (.var 0) (raiseU 3) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 3) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 3, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit))
      (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_pSig1 _) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 3) (rowAt_Ξu fun o ho => by simp at ho; subst ho; exact uOp_rSig3)
      rfl rfl .unit (.unitI (.cons .nil))

/-- **`cancelKeptT`, tied to `Ξu`**, at `F (1 ⊕ 1)`. -/
theorem du_cancelKeptT : CDerivesAt Ξu Δ [] cancelKeptT (.comp (.ret (.sum .unit .unit))) := by
  show CDerivesAt Ξu Δ [] (hndExpr 3 [.unr] (.pair (.val injlV) (.pair (.val c₃) (.val Val.unit)))
    (bodyT 3)) (.comp (CTy.effOf [] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    (rowAt_Ξu fun o ho => by simp [Row.ofEff] at ho; subst ho; exact uOp_rSig3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_injlV _ .unit .unit)
      (.tensorI .nil (du_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) ?_
  show CDerivesAt Ξu Δ [] (hndExpr 1 [.unr] (.pair (.val CancelIntercept.idV)
    (.pair (.val cancelCT) (.val Val.unit))) ((K 3).plug (performU 1)))
    (.comp (CTy.effOf [rSig 3] .unit))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 3)
    (rowAt_Ξu fun o ho => by
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl
      · exact uOp_pSig1 _
      · exact uOp_rSig3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (du_idV _ .unit) (.tensorI .nil (du_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finR 3).rowOf ++ [rSig 3] = [rSig 3, rSig 3] from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩
  · show CDerivesAt Ξu Δ [] (hndExpr 2 [.unr] (.pair (.val CancelIntercept.idV)
      (.pair (.val (constC Val.unit)) (.val Val.unit)))
      ((CancelIntercept.uF (raiseU 3) .hole).plug (performU 1)))
      (.comp (CTy.effOf [pSig 1 (finR 3), rSig 3] .unit))
    exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
      (rowAt_Ξu fun o ho => by
        simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ho
        rcases ho with rfl | rfl | rfl
        · exact uOp_rSig2
        · exact uOp_pSig1 _
        · exact uOp_rSig3)
      .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
      (.tensorI .nil (du_idV _ .unit) (.tensorI .nil (du_constC_raise _ (.unitI (.cons .nil)))
        (.unitI .nil)))
      (by decide) (by simp [rSig, pSig]) (by simp) du_then₃

end Typing2

/-! ### The counts along a chain of head steps -/

section Chains
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}
variable (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner)

open Classical in
/-- Along a chain of head steps, the configurations keeping a new error are the steps at
`[cfin-raise]` keeping one (Core's unique decomposition, `keepAt_iff`). -/
theorem keepsOf_chainPath {μ : Heap} {s : R.St} : ∀ {e e' : Expr} {ch : List (Kont × Expr × Expr)},
    HeadChain (ℍ := ℍ) e ch e' →
      keepsOf ((μ, e), s) (chainPath R μ s ch) = ch.countP (fun x => decide (KeepRedex x.2.1))
  | _, _, _, .nil => rfl
  | _, _, _, @HeadChain.cons _ _ K a a' _ q hh _ hq => by
      show keepsOf ((μ, K.plug a), s) ((labelOf RF Ξ a, ((μ, K.plug a'), s)) :: chainPath R μ s q) = _
      refine (keepsOf_cons (R := R) ((μ, K.plug a), s) ((μ, K.plug a'), s) (labelOf RF Ξ a)
        (chainPath R μ s q)).trans ?_
      rw [keepsOf_chainPath hq, List.countP_cons]
      have e₁ : KeepAt ((μ, K.plug a), s).1.2 ↔ KeepRedex (K, a, a').2.1 := keepAt_iff (hh μ) K
      by_cases h : KeepRedex a
      · simp [h, e₁, Nat.add_comm]
      · simp [h, e₁]

open Classical in
theorem reraisesOf_chainPath {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {ch : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e ch e' →
      reraisesOf ((μ, e), s) (chainPath R μ s ch) =
        ch.countP (fun x => decide (ReraiseRedex x.2.1))
  | _, _, _, .nil => rfl
  | _, _, _, @HeadChain.cons _ _ K a a' _ q hh _ hq => by
      show reraisesOf ((μ, K.plug a), s) ((labelOf RF Ξ a, ((μ, K.plug a'), s)) :: chainPath R μ s q) = _
      refine (reraisesOf_cons (R := R) ((μ, K.plug a), s) ((μ, K.plug a'), s) (labelOf RF Ξ a)
        (chainPath R μ s q)).trans ?_
      rw [reraisesOf_chainPath hq, List.countP_cons]
      have e₁ : ReraiseAt ((μ, K.plug a), s).1.2 ↔ ReraiseRedex (K, a, a').2.1 := reraiseAt_iff (hh μ) K
      by_cases h : ReraiseRedex a
      · simp [h, e₁, Nat.add_comm]
      · simp [h, e₁]

open Classical in
theorem mergesOf_chainPath {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {ch : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e ch e' →
      mergesOf ((μ, e), s) (chainPath R μ s ch) = ch.countP (fun x => decide (MergeRedex x.2.1))
  | _, _, _, .nil => rfl
  | _, _, _, @HeadChain.cons _ _ K a a' _ q hh _ hq => by
      show mergesOf ((μ, K.plug a), s) ((labelOf RF Ξ a, ((μ, K.plug a'), s)) :: chainPath R μ s q) = _
      refine (mergesOf_cons (R := R) ((μ, K.plug a), s) ((μ, K.plug a'), s) (labelOf RF Ξ a)
        (chainPath R μ s q)).trans ?_
      rw [mergesOf_chainPath hq, List.countP_cons]
      have e₁ : MergeAt ((μ, K.plug a), s).1.2 ↔ MergeRedex (K, a, a').2.1 := mergeAt_iff (hh μ) K
      by_cases h : MergeRedex a
      · simp [h, e₁, Nat.add_comm]
      · simp [h, e₁]

end Chains

/-- A `ccatch` redex, by its shape. -/
def ccatchHeadB : Expr → Bool
  | .app (.prim .ccatch) _ => true
  | _ => false

/-- A running finaliser's `cfin` redex keeping an error, by its shape. -/
def cfinKeptB : Expr → Bool
  | .app (.app (.prim .cfin) s) _ => keptB s
  | _ => false

theorem ccatchHeadB_of_reraise {a : Expr} (h : ReraiseRedex a) : ccatchHeadB a = true := by
  obtain ⟨K, E, rfl, -⟩ := h; rfl

theorem cfinKeptB_of_merge {a : Expr} (h : MergeRedex a) : cfinKeptB a = true := by
  obtain ⟨K, E, E', rfl, -⟩ := h
  show keptB (cancelVal (some E)).1 = true
  rw [keptB_cancelVal]; rfl

open Classical in
theorem countP_le_of_imp {α : Type} (l : List α) {p : α → Prop} {b : α → Bool}
    (h : ∀ x, p x → b x = true) : l.countP (fun x => decide (p x)) ≤ l.countP b :=
  List.countP_mono_left fun x _ hx => h x (of_decide_eq_true hx)

/-! ### `progDropT`: a kept error dropped with an unrestricted continuation -/

section Drop

local notation "𝕌" => ourInst (ℍ := ℍ) orowRF Ξu J₁

theorem closed_progDropT : closedAt 0 progDropT = true := by
  simpa using closedAt_of_derives (du_progDropT (Δ := LifeCtx.empty)).toCDerives

/-- **`progDropT` is typed by `J₁`** at `Ξu`. -/
theorem der_progDropT_J₁ :
    (𝕌).der [] progDropT ((𝕌).F (orowAlg Ξu).unit (OVTy.ofV (.sum .unit .unit))) :=
  der_J₁_ret closed_progDropT du_progDropT

/-- `progDropT`'s run, the steps `look` finds. -/
def dropChain : List (Kont × Expr × Expr) := lookRun 20 progDropT

theorem dropChain_sound : HeadChain (ℍ := ℍ) progDropT dropChain (lookEnd 20 progDropT) :=
  lookRun_sound 20 progDropT

theorem dropChain_end : lookEnd 20 progDropT = (Val.inj₁ Val.unit).1 := by rfl

theorem dropChain_noCcatch : dropChain.all (fun x => !ccatchHeadB x.2.1) = true := by decide

theorem dropChain_noCfinKept : dropChain.all (fun x => !cfinKeptB x.2.1) = true := by decide

/-- The tenth step: the first finaliser's raise of `2` meets its `cfin`, and the cancel keeps it. -/
theorem dropChain_keep :
    (dropChain.map fun x => x.2.1)[9]? = some (cfinE (cancelVal none) (raiseU 2)) := by rfl

open Classical in
/-- **`NoDroppedError` fails at `J₁` at `Ξu`**: `progDropT`, typed by `J₁` at `F (1 ⊕ 1)`, runs to
`inj₁ ()` under the runner that answers nothing; on the way its first finaliser's raise of `2` is
kept (`[cfin-raise]`), and its second finaliser performs `4`, whose unrestricted handler drops the
continuation that holds the kept error.  The run keeps one error, re-raises none and supersedes
none.  So the count holds only where no continuation captures a kept error and is dropped:
`Ξu`'s resuming operations are `unr`. -/
theorem not_noDroppedError_unr : ¬ NoDroppedError (ℍ := ℍ) orowRF Ξu J₁ := by
  intro h
  have hch := dropChain_sound (ℍ := ℍ)
  have hpath : (𝕌).RPath (𝕌).R₀ ((𝕌).rinit (𝕌).R₀ progDropT)
      (chainPath (𝕌).R₀ Adequacy.emptyMem () dropChain) := rpath_chainPath (𝕌).R₀ hch
  have hl : (𝕌).lastC ((𝕌).rinit (𝕌).R₀ progDropT)
      (chainPath (𝕌).R₀ Adequacy.emptyMem () dropChain) =
        ((Adequacy.emptyMem, (Val.inj₁ Val.unit).1), ()) := by
    have := lastC_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
    rw [dropChain_end] at this
    exact this
  have hcomp : (𝕌).CompleteFrom (𝕌).R₀ ((𝕌).rinit (𝕌).R₀ progDropT)
      (chainPath (𝕌).R₀ Adequacy.emptyMem () dropChain) := by
    refine ⟨hpath, ?_⟩
    rw [hl]
    exact isVal_val _ (Val.inj₁ Val.unit)
  have hc := h (𝕌).R₀ r₀_respects progDropT (orowAlg Ξu).unit (OVTy.ofV (.sum .unit .unit))
    (answers_unit _) der_progDropT_J₁ (.sum .unit .unit) _ hcomp
  have ek := keepsOf_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
  have er := reraisesOf_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
  have em := mergesOf_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
  have hr : dropChain.countP (fun x => decide (ReraiseRedex x.2.1)) = 0 := by
    refine List.countP_eq_zero.2 fun x hx hd => ?_
    have h₁ := List.all_eq_true.1 dropChain_noCcatch x hx
    rw [ccatchHeadB_of_reraise (of_decide_eq_true hd)] at h₁
    cases h₁
  have hm : dropChain.countP (fun x => decide (MergeRedex x.2.1)) = 0 := by
    refine List.countP_eq_zero.2 fun x hx hd => ?_
    have h₁ := List.all_eq_true.1 dropChain_noCfinKept x hx
    rw [cfinKeptB_of_merge (of_decide_eq_true hd)] at h₁
    cases h₁
  have hk : 0 < dropChain.countP (fun x => decide (KeepRedex x.2.1)) := by
    have h₉ := dropChain_keep
    rw [List.getElem?_map] at h₉
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.1 h₉
    refine List.countP_pos_iff.2 ⟨x, List.mem_of_getElem? hx, decide_eq_true ?_⟩
    rw [hxa]
    exact ⟨.hole, 2, 0, Val.unit, rfl, by decide, rfl⟩
  have key := ek.symm.trans (hc.trans (congrArg₂ (· + ·) er em))
  rw [hr, hm] at key
  omega

end Drop

/-! ### `cancelKeptT`: the restricted count read -/

/-- A running finaliser's `cfin` redex, by its shape. -/
def cfinHeadB : Expr → Bool
  | .app (.app (.prim .cfin) _) _ => true
  | _ => false

theorem cfinHeadB_of_keep {a : Expr} (h : KeepRedex a) : cfinHeadB a = true := by
  obtain ⟨K, m, j, w, rfl, -, -⟩ := h; rfl

theorem noKeptCaptureAt_of_check {t : Expr} (h : (kc t == 0 || !hasPerformB t) = true) :
    NoKeptCaptureAt t := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact noKeptCaptureAt_of_kc (by simpa using h)
  · exact noKeptCaptureAt_of_noPerform (by simpa using h)

section Kept

local notation "𝕌" => ourInst (ℍ := ℍ) orowRF Ξu J₁

/-- `cancelKeptT`'s run, the steps `look` finds. -/
def keptChain : List (Kont × Expr × Expr) := lookRun 20 cancelKeptT

theorem keptChain_sound : HeadChain (ℍ := ℍ) cancelKeptT keptChain (lookEnd 20 cancelKeptT) :=
  lookRun_sound 20 cancelKeptT

theorem keptChain_end : lookEnd 20 cancelKeptT = (Val.inj₂ Val.unit).1 := by rfl

theorem keptChain_check :
    (chainTerms cancelKeptT keptChain).all (fun t => kc t == 0 || !hasPerformB t) = true := by
  decide

theorem keptChain_cfin : keptChain.countP (fun x => cfinHeadB x.2.1) = 1 := by decide

theorem keptChain_ccatch : keptChain.countP (fun x => ccatchHeadB x.2.1) = 1 := by decide

theorem keptChain_noCfinKept : keptChain.all (fun x => !cfinKeptB x.2.1) = true := by decide

/-- The tenth step keeps the finaliser's raise of `3`; the eleventh re-raises it at the
canceller. -/
theorem keptChain_keep :
    (keptChain.map fun x => x.2.1)[9]? = some (cfinE (cancelVal none) (raiseU 3)) := by rfl

theorem keptChain_reraise :
    (keptChain.map fun x => x.2.1)[10]? =
      some (ccatchE (raiseE (.val (cancelVal (some (opPayload 3 0 Val.unit)))))) := by rfl

theorem closed_cancelKeptT : closedAt 0 cancelKeptT = true := by
  simpa using closedAt_of_derives (du_cancelKeptT (Δ := LifeCtx.empty)).toCDerives

/-- **`cancelKeptT` is typed by `J₁`** at `Ξu`. -/
theorem der_cancelKeptT_J₁ :
    (𝕌).der [] cancelKeptT ((𝕌).F (orowAlg Ξu).unit (OVTy.ofV (.sum .unit .unit))) :=
  der_J₁_ret closed_cancelKeptT du_cancelKeptT

open Classical in
/-- **The restricted count reads a run that keeps an error** (`NoDroppedErrorNKC`, proved at
`J₁` by `I.noDroppedErrorNKC_J₁`): `cancelKeptT`, typed by `J₁` at `Ξu`, runs to `inj₂ ()` under
the runner that answers nothing; no `[op]` step of its run captures a context holding a kept error;
its finaliser's raise of `3` is kept once and re-raised once at the canceller. -/
theorem noDroppedErrorNKC_reads :
    ∃ q : List ((𝕌).Event × (𝕌).RConf (𝕌).R₀),
      (𝕌).der [] cancelKeptT ((𝕌).F (orowAlg Ξu).unit (OVTy.ofV (.sum .unit .unit))) ∧
      (𝕌).CompleteFrom (𝕌).R₀ ((𝕌).rinit (𝕌).R₀ cancelKeptT) q ∧
      (∀ j, j ≤ q.length → NoKeptCaptureAt ((𝕌).cfgAt ((𝕌).rinit (𝕌).R₀ cancelKeptT) q j).1.2) ∧
      keepsOf ((𝕌).rinit (𝕌).R₀ cancelKeptT) q = 1 ∧
      reraisesOf ((𝕌).rinit (𝕌).R₀ cancelKeptT) q = 1 ∧
      mergesOf ((𝕌).rinit (𝕌).R₀ cancelKeptT) q = 0 := by
  have hch := keptChain_sound (ℍ := ℍ)
  let q := chainPath (𝕌).R₀ Adequacy.emptyMem () keptChain
  have hpath : (𝕌).RPath (𝕌).R₀ ((𝕌).rinit (𝕌).R₀ cancelKeptT) q := rpath_chainPath (𝕌).R₀ hch
  have hl : (𝕌).lastC ((𝕌).rinit (𝕌).R₀ cancelKeptT) q =
      ((Adequacy.emptyMem, (Val.inj₂ Val.unit).1), ()) := by
    have := lastC_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
    rw [keptChain_end] at this
    exact this
  have hk : keptChain.countP (fun x => decide (KeepRedex x.2.1)) = 1 := by
    refine le_antisymm ((countP_le_of_imp _ fun x h => cfinHeadB_of_keep h).trans
      keptChain_cfin.le) ?_
    have h₉ := keptChain_keep
    rw [List.getElem?_map] at h₉
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.1 h₉
    refine List.countP_pos_iff.2 ⟨x, List.mem_of_getElem? hx, decide_eq_true ?_⟩
    rw [hxa]
    exact ⟨.hole, 3, 0, Val.unit, rfl, by decide, rfl⟩
  have hr : keptChain.countP (fun x => decide (ReraiseRedex x.2.1)) = 1 := by
    refine le_antisymm ((countP_le_of_imp _ fun x h => ccatchHeadB_of_reraise h).trans
      keptChain_ccatch.le) ?_
    have h₁₀ := keptChain_reraise
    rw [List.getElem?_map] at h₁₀
    obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.1 h₁₀
    refine List.countP_pos_iff.2 ⟨x, List.mem_of_getElem? hx, decide_eq_true ?_⟩
    rw [hxa]
    exact ⟨.hole, _, rfl, rfl⟩
  have hm : keptChain.countP (fun x => decide (MergeRedex x.2.1)) = 0 := by
    refine List.countP_eq_zero.2 fun x hx hd => ?_
    have h₁ := List.all_eq_true.1 keptChain_noCfinKept x hx
    rw [cfinKeptB_of_merge (of_decide_eq_true hd)] at h₁
    cases h₁
  refine ⟨q, der_cancelKeptT_J₁, ⟨hpath, by rw [hl]; exact isVal_val _ (Val.inj₂ Val.unit)⟩, ?_,
    (keepsOf_chainPath (𝕌).R₀ hch).trans hk, (reraisesOf_chainPath (𝕌).R₀ hch).trans hr,
    (mergesOf_chainPath (𝕌).R₀ hch).trans hm⟩
  intro j hj
  have hj' : j < (chainTerms cancelKeptT keptChain).length := by
    rw [chainTerms_length]; simp [q, chainPath] at hj; omega
  obtain ⟨t, ht⟩ : ∃ t, (chainTerms cancelKeptT keptChain)[j]? = some t :=
    ⟨_, List.getElem?_eq_getElem hj'⟩
  have hcfg := cfgAt_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) cancelKeptT keptChain j ht
  show NoKeptCaptureAt ((𝕌).cfgAt ((Adequacy.emptyMem, cancelKeptT), ()) q j).1.2
  rw [hcfg]
  exact noKeptCaptureAt_of_check (List.all_eq_true.1 keptChain_check t (List.mem_of_getElem? ht))

end Kept

/-! ### `progNC₁T`: a cancel nested in a cancel, at an unrestricted continuation -/

section NoCtl

local notation "𝕌" => ourInst (ℍ := ℍ) orowRF Ξu J₁

/-- `4` at `Ξu`. -/
def labU4 : (orowAlg Ξu).Lab := ⟨4, by decide, by simp [Ξu], by simp [Ξu]⟩

/-- The outer handler of `4` in `progNC₁T`, as A's handler: `λx. x`, and the cancelling clause. -/
def hndU4 : OVal × List OVal := (⟨CancelIntercept.idV.1, .lam⟩, [⟨cancelCT.1, .lam⟩])

theorem qsOf_U4 : qsOf Ξu 4 = (qualsVal [.unr]).1 := by simp [qsOf, Ξu]

theorem capture_U4 (K : Kont) :
    ((𝕌).capture labU4 hndU4 K).1 = kappa (hU 4 CancelIntercept.idV cancelCT) K := by
  show captureE 4 (qsOf Ξu 4) CancelIntercept.idV.1 [cancelCT.1] K = _
  rw [qsOf_U4]
  have hv : IsVal (hndValE 4 (qualsVal [.unr]).1 CancelIntercept.idV.1 [cancelCT.1]) :=
    (hU 4 CancelIntercept.idV cancelCT).2
  rw [captureE_of_val K hv]
  rfl

/-- `progNC₁T`'s run to the cancel of the outer `4`'s continuation. -/
def ncChain : List (Kont × Expr × Expr) := lookRun 13 progNC₁T

theorem ncChain_sound : HeadChain (ℍ := ℍ) progNC₁T ncChain (lookEnd 13 progNC₁T) :=
  lookRun_sound 13 progNC₁T

theorem ncChain_end :
    lookEnd 13 progNC₁T = cancelE (kappa (hU 4 CancelIntercept.idV cancelCT)
      (CancelIntercept.ccF (CancelIntercept.cfF (cancelVal none) .hole))) := by rfl

theorem closed_progNC₁T : closedAt 0 progNC₁T = true := by
  simpa using closedAt_of_derives (du_progNC₁T (Δ := LifeCtx.empty)).toCDerives

/-- **`progNC₁T` is typed by `J₁`** at `Ξu`. -/
theorem der_progNC₁T_J₁ :
    (𝕌).der [] progNC₁T ((𝕌).F (orowAlg Ξu).unit (OVTy.ofV .unit)) :=
  der_J₁_ret closed_progNC₁T du_progNC₁T

/-- **`CancelsNoCtl` fails at `J₁` at `Ξu`**: `progNC₁T`, typed by `J₁`, reaches the cancel of the
outer `4`'s continuation `capture 4 H K`, whose context `K` holds the cancel delimiter of the first
cancel and the running finaliser's `cfin` frame: the finaliser performed `4`, and the outer handler
cancels the finaliser's continuation (a cancel nested in a cancel, SPEC §19's `[cfin-cancel]`).
`CancelsNoCtl` was S5's hypothesis before frame deadness; the restated cancel trace passes the
running finaliser (`pend`), and S5 reads no such hypothesis. -/
theorem not_cancelsNoCtl_J₁ : ¬ CancelsNoCtl (ℍ := ℍ) orowRF Ξu J₁ := by
  intro h
  have hch := ncChain_sound (ℍ := ℍ)
  let q := chainPath (𝕌).R₀ Adequacy.emptyMem () ncChain
  have hpath : (𝕌).RPath (𝕌).R₀ ((𝕌).rinit (𝕌).R₀ progNC₁T) q := rpath_chainPath (𝕌).R₀ hch
  have hreach := Targets.A.EffectSystem.rreach_cfgAt hpath q.length le_rfl
  have hl : (𝕌).cfgAt ((𝕌).rinit (𝕌).R₀ progNC₁T) q q.length =
      ((Adequacy.emptyMem, lookEnd 13 progNC₁T), ()) :=
    lastC_chainPath (𝕌).R₀ (μ := Adequacy.emptyMem) (s := ()) hch
  have hK := h (𝕌).R₀ r₀_respects progNC₁T (orowAlg Ξu).unit (OVTy.ofV .unit) (answers_unit _)
    der_progNC₁T_J₁ _ .hole labU4 hndU4
    (CancelIntercept.ccF (CancelIntercept.cfF (cancelVal none) .hole)) hreach (by
      rw [hl]
      show lookEnd 13 progNC₁T = Kont.hole.plug (cancelE ((𝕌).capture labU4 hndU4 _).1)
      rw [capture_U4, ncChain_end]
      rfl)
  exact hK.1.1 rfl

end NoCtl

/-! ### `e7b` at an admissible context: the restricted count read there

`e7b`'s `wait` is affine, so its continuation owns a cell: the run allocates and frees, and `runM`
computes it.  `tracM` lists the configurations of that run. -/

/-- The configurations of the run `runM` computes, after each step. -/
def tracM : ℕ → LMem → Expr → List (LMem × Expr)
  | 0, _, _ => []
  | k + 1, m, e =>
      match stepM m e with
      | some (m', e') => (m', e') :: tracM k m' e'
      | none => []

section Trace
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}
variable (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (s : R.St)

/-- **The run `runM` computes is a path of our instance**, under every runner, at its state; its
configurations' terms are the run's. -/
theorem rpath_tracM : ∀ (k : ℕ) (m : LMem) (e : Expr),
    ∃ q : List ((ourInst (ℍ := ℍ) RF Ξ J).Event × (ourInst (ℍ := ℍ) RF Ξ J).RConf R),
      (ourInst (ℍ := ℍ) RF Ξ J).RPath R ((m.heap, e), s) q ∧
        q.map (fun x => x.2.1.2) = (tracM k m e).map Prod.snd
  | 0, m, e => ⟨[], .nil, rfl⟩
  | k + 1, m, e => by
      unfold tracM
      split
      · rename_i m' e' hs
        obtain ⟨K, a, a', he, he', hh⟩ := stepM_sound (ℍ := ℍ) hs
        obtain ⟨q, hq, hmap⟩ := rpath_tracM k m' e'
        refine ⟨(labelOf RF Ξ a, ((m'.heap, e'), s)) :: q, .cons ?_ hq, ?_⟩
        · rw [he, he']
          exact .mach (OStep.mach hh)
        · rw [List.map_cons, List.map_cons, hmap]
      · exact ⟨[], .nil, rfl⟩

variable {R}

/-- The term of a path's configuration. -/
theorem cfgAt_term (c₀ : (ourInst (ℍ := ℍ) RF Ξ J).RConf R)
    (q : List ((ourInst (ℍ := ℍ) RF Ξ J).Event × (ourInst (ℍ := ℍ) RF Ξ J).RConf R)) (j : ℕ) :
    ((ourInst (ℍ := ℍ) RF Ξ J).cfgAt c₀ q j).1.2 =
      ((c₀.1.2 :: q.map (fun x => x.2.1.2))[j]?).getD c₀.1.2 := by
  unfold A.EffectSystem.cfgAt
  rw [show (c₀.1.2 :: q.map (fun x => x.2.1.2)) =
      (c₀ :: q.map Prod.snd).map (fun x : (ourInst (ℍ := ℍ) RF Ξ J).RConf R => x.1.2) by simp,
    List.getElem?_map, Option.getD_map]

end Trace

section E7b

local notation "𝔸" => ourInst (ℍ := ℍ) orowRF ΞA J₁

/-- `e7b`'s run at `ΞA`. -/
def e7bTrace : List (LMem × Expr) := tracM 20 [] e7b21

theorem e7bTrace_length : e7bTrace.length = 16 := by decide

theorem e7bTrace_last : (e7bTrace.map Prod.snd)[15]? = some (Val.inj₂ Val.unit).1 := by rfl

theorem e7bTrace_check :
    (e7b21 :: e7bTrace.map Prod.snd).all (fun t => kc t == 0 || !hasPerformB t) = true := by
  decide

/-- The twelfth configuration: the finaliser's raise of `exn` under the cancel's `cfin`. -/
theorem e7bTrace_keep :
    (e7bTrace.map Prod.snd)[11]? = some (Kfb.plug (raiseE (.val (opPayload 1 0 Val.unit)))) := by
  rfl

theorem keepAt_Kfb : KeepAt (Kfb.plug (raiseE (.val (opPayload 1 0 Val.unit)))) := by
  refine ⟨K0b.comp (ccatchK .hole), _, ?_, .hole, 1, 0, Val.unit, rfl, by decide, rfl⟩
  rw [Kfb, Kont.plug_comp]
  rfl

open Classical in
/-- **The restricted count reads a typed run at an admissible context**: at `ΞA`, `e7b`, typed by
`J₁`, runs to `inj₂ ()` under the runner that answers nothing (its `wait` continuation's cell
allocated and freed); no `[op]` step of its run captures a context holding a kept error, and its
finaliser's raise of `exn` is kept.  So `I.noDroppedErrorNKC_J₁` says of this run that the kept
error is re-raised at its canceller or loses to an earlier one. -/
theorem noDroppedErrorNKC_reads_ΞA :
    ∃ q : List ((𝔸).Event × (𝔸).RConf (𝔸).R₀),
      (𝔸).der [] e7b21 ((𝔸).F (orowAlg ΞA).unit (OVTy.ofV (.sum (.sum boolT .unit) .unit))) ∧
      (𝔸).CompleteFrom (𝔸).R₀ ((𝔸).rinit (𝔸).R₀ e7b21) q ∧
      (∀ j, j ≤ q.length → NoKeptCaptureAt ((𝔸).cfgAt ((𝔸).rinit (𝔸).R₀ e7b21) q j).1.2) ∧
      0 < keepsOf ((𝔸).rinit (𝔸).R₀ e7b21) q := by
  obtain ⟨q, hq, hmap⟩ := rpath_tracM (Ξ := ΞA) (J := J₁) (𝔸).R₀ () 20 [] e7b21
  have hlen : q.length = 16 := by
    have := congrArg List.length hmap
    simp only [List.length_map] at this
    rw [this]; exact e7bTrace_length
  have hterm : ∀ j, ((𝔸).cfgAt ((𝔸).rinit (𝔸).R₀ e7b21) q j).1.2 =
      ((e7b21 :: e7bTrace.map Prod.snd)[j]?).getD e7b21 := by
    intro j
    rw [cfgAt_term]
    show ((e7b21 :: q.map (fun x => x.2.1.2))[j]?).getD e7b21 = _
    rw [hmap]
    rfl
  refine ⟨q, der_e7b_J₁ (by simp [ΞA]) (by simp [ΞA]), ⟨hq, ?_⟩, ?_, ?_⟩
  · -- the run ends at `inj₂ ()`, a value
    have hl : ((𝔸).lastC ((𝔸).rinit (𝔸).R₀ e7b21) q).1.2 = (Val.inj₂ Val.unit).1 := by
      show ((𝔸).cfgAt _ q q.length).1.2 = _
      rw [hterm, hlen]
      show ((e7bTrace.map Prod.snd)[15]?).getD e7b21 = _
      rw [e7bTrace_last]
      rfl
    have hc : ((𝔸).lastC ((𝔸).rinit (𝔸).R₀ e7b21) q).1 =
        (((𝔸).lastC ((𝔸).rinit (𝔸).R₀ e7b21) q).1.1, (Val.inj₂ Val.unit).1) := Prod.ext rfl hl
    rw [hc]
    exact isVal_val _ (Val.inj₂ Val.unit)
  · intro j hj
    rw [hterm]
    apply noKeptCaptureAt_of_check
    have hj' : j < (e7b21 :: e7bTrace.map Prod.snd).length := by
      simp only [List.length_cons, List.length_map, e7bTrace_length]; omega
    rw [List.getElem?_eq_getElem hj', Option.getD_some]
    exact List.all_eq_true.1 e7bTrace_check _ (List.getElem_mem hj')
  · refine List.countP_pos_iff.2 ⟨12, List.mem_range.2 (by rw [hlen]; omega), decide_eq_true ?_⟩
    rw [hterm]
    show KeepAt (((e7bTrace.map Prod.snd)[11]?).getD e7b21)
    rw [e7bTrace_keep]
    exact keepAt_Kfb

end E7b

end Targets.Inst

end
