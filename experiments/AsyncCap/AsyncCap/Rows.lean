import AsyncCap.Derives

/-!
# AsyncCap — the rows the relaxed lend admits

`Row.ResumeO` is satisfiable by the operations the acceptance programs perform inside a relaxed
lend: the scheduler's `await : 1 ↠^aff 1` and the generator's `yield : i32 ↠^aff 1` (the operation
`corpus/reject/gen-self-borrow.bc` performs inside its borrow block). An abortive operation, and
an operation that answers data, are outside it.
-/

namespace BoCa.Fig16.LogRel.Core.AsyncCap
open BoCa BoCa.Fig16
open BoCa.Lifetime (LifeVar)

/-- `await : 1 ↠^aff 1` at the name `1`. -/
def awaitSig : OpSig := ⟨1, 0, .aff, .unit, .unit, .ret .unit⟩

/-- `yield : i32 ↠^aff 1` at the name `2`. -/
def yieldSig : OpSig := ⟨2, 0, .aff, .int .w32, .unit, .ret .unit⟩

/-- `raise : i32 ↠^aff 0`, abortive. -/
def raiseSig : OpSig := ⟨3, 0, .aff, .int .w32, .zero, .ret .unit⟩

theorem resumeO_await_yield (x : LifeVar) : Row.ResumeO [awaitSig, yieldSig] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · refine ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [awaitSig, VFree] at h, fun _ _ => .unit, trivial⟩
  · refine ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [yieldSig, VFree] at h, fun _ _ => .int, trivial⟩

theorem not_resumeO_raise (x : LifeVar) : ¬ Row.ResumeO [raiseSig] x := by
  intro h
  have := (h raiseSig (by simp)).1
  simp [OpSig.abort, raiseSig, VTy.isZero] at this

end BoCa.Fig16.LogRel.Core.AsyncCap
