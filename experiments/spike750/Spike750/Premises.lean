import Core.PinLaw
import Core.Dtor

/-!
# #750 — which kernel premises the cancel-as-resume meets, and which it does not

Facts about today's definitions at the operations #750 proposes. None is a soundness claim.

* **`[lend-R]`'s `Row.ResumeO`.** The proposal's `await` answers `1 + 1` ("go on" / "cancelled") and
  the body raises an abortive `cancelled` on `inr`. That row fails `Row.ResumeO` twice: the answer
  is not `1` (`not_resumeO_awaitC`), and the raise is abortive (`not_resumeO_cancelled`). The
  machine-step variant (a linear `await` answering `1`, the cancel a new step that plugs a raise of
  the reserved name into the hole) meets `Row.ResumeO` as written (`resumeO_awaitLin`); its change
  is in `[handle]`'s `κ` type and the machine instead.
* **`[then]`'s cancel-row premise** reads only capturable operations (`capB`). A linear `await` is
  not capturable (`capB_awaitLin`), so a finaliser that awaits puts nothing in its cancel row; an
  affine `await` is (`capB_awaitAff`), which is how an awaiting finaliser makes today's cancel row
  non-empty and fails `Row.ResumeO` (wall 5).
* **`[let]`'s `hW`** asks `N`'s context to drop at a row with a non-linear operation. A row of the
  linear `await` alone has none (`not_cancels_awaitC`); with the abortive `cancelled` it has one
  (`cancels_awaitC_cancelled`). A task, or a queue of tasks, is a thunk under a box: not `VTy.OwnFree`
  (`not_drop_task`), so an abort never abandons one (decision 2 abandons `VTy.OwnFree` slots only).
* **No derived drop.** A linear `κ`, `U((B ⊸ C) & ⊤)`, and the proposal's task,
  `[@a] U((1 + 1) ⊸ C)`, have no destructor (`not_hasDtor_kappaLin`, `not_hasDtor_task`). Today's
  task, `U(νX. … & F 1)`, has one (`HasDtor.nu`, its `close` the cancel).
-/

namespace Spike750.Premises
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-- The proposal's `await : 1 ↠^lin 1 + 1` at the name `1`. -/
def awaitC : OpSig := ⟨1, 0, .lin, .unit, .sum .unit .unit, .ret .unit⟩

/-- The proposal's `cancelled : 1 ↠^aff 0` at the name `1`, abortive. -/
def cancelled : OpSig := ⟨1, 1, .cancel, .unit, .zero, .ret .unit⟩

/-- The machine-step variant's `await : 1 ↠^lin 1`. -/
def awaitLin : OpSig := ⟨1, 0, .lin, .unit, .unit, .ret .unit⟩

/-- Today's `await : 1 ↠^aff 1` (`lib/async.bc`'s `ctl await()`). -/
def awaitAff : OpSig := ⟨1, 0, .cancel, .unit, .unit, .ret .unit⟩

theorem not_resumeO_awaitC (x : LifeVar) : ¬ Row.ResumeO [awaitC] x := by
  intro h
  have := (h awaitC (by simp)).2.2.2.1
  simp [awaitC] at this

theorem not_resumeO_cancelled (x : LifeVar) : ¬ Row.ResumeO [awaitC, cancelled] x := by
  intro h
  have := (h cancelled (by simp)).1
  simp [OpSig.abort, cancelled, VTy.isZero] at this

theorem resumeO_awaitLin (x : LifeVar) : Row.ResumeO [awaitLin] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  exact ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [awaitLin, VFree] at h,
    fun _ _ => .unit, trivial⟩

theorem capB_awaitLin : capB awaitLin.q awaitLin.B = false := rfl
theorem capB_awaitC : capB awaitC.q awaitC.B = false := rfl
theorem capB_awaitAff : capB awaitAff.q awaitAff.B = true := rfl

theorem not_cancels_awaitC : ¬ Row.Cancels [awaitC] := by
  rintro ⟨o, ho, hq⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho; exact hq rfl

theorem cancels_awaitC_cancelled : Row.Cancels [awaitC, cancelled] :=
  ⟨cancelled, by simp, by decide⟩

/-- A task, a thunk under a box, is not `VTy.OwnFree`: no abort abandons it. -/
theorem not_drop_task (a : Lifetime.Life) (C : CTy) : ¬ VTy.OwnFree (.box a (.thunk C)) := by
  intro h; cases h

theorem not_drop_thunk (C : CTy) : ¬ VTy.OwnFree (.thunk C) := by
  intro h; cases h

/-- A linear `κ`, `U((B ⊸ C) & ⊤)`, has no derived drop. -/
theorem not_hasDtor_kappaLin (B : VTy) (C : CTy) : ¬ HasDtor (.thunk (.amp (.arr B C) .top)) := by
  intro h; cases h

/-- The proposal's task, `[@a] U((1 + 1) ⊸ C)`, has no derived drop. -/
theorem not_hasDtor_task (a : Lifetime.Life) (C : CTy) :
    ¬ HasDtor (.box a (.thunk (.arr (.sum .unit .unit) C))) := by
  intro h; cases h with
  | box h' => cases h'

end Spike750.Premises
