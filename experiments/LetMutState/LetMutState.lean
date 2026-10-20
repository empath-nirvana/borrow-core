import Core.EffBorrow
import Core.PinDerives

/-!
# `let mut` as a `State` handler: the borrow boundary (#611)

`effect State[T] { linear ctl get() -> T; linear ctl put(v: T) }` is the effect a `let mut x : T`
would be an instance of, with the state the handler's parameter and no cell. As a row of the
name `n` it is `stateRow n A`: `get : 1 ↠^lin A` at index 0 and `put : A ↠^lin 1` at index 1,
each with the empty cancel row.

A borrow's callback is typed at one of three rows (SPEC §19, §29):

* the pure form: no operation at all;
* the unwinding form (`withbor1U` … `sliceBorrowImmU`): a row with `Row.Unwind 'x`, every
  operation abortive;
* the relaxed lend R1 (`CDerivesP.lendR`, under `PinLaw`): a row with `Row.ResumeO 'x`, every
  operation answering `1`.

`stateRow` is neither of the last two (`stateRow_not_unwind`, `stateRow_not_resumeO`) and is not
empty, so a `get` or `put` of `x` inside a borrow block (`corpus/parse-int.bc`'s `sum`, in
`borrow imm line { … }`) has no typing as an operation of `x`'s handler. The state has to cross
the borrow as data: into the callback and back out with its result.
-/

namespace LetMutState
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-- `State[A]`'s operations, as a row of the name `n`. -/
def stateRow (n : UInt32) (A : VTy) : Row :=
  Row.ofEff n [(.lin, .unit, A), (.lin, A, .unit)] 0

theorem get_mem (n : UInt32) (A : VTy) :
    (⟨n, 0, .lin, .unit, A, .ret .unit⟩ : OpSig) ∈ stateRow n A := by
  simp [stateRow, Row.ofEff, finsNil]

/-- **No unwinding borrow carries `State`**: `get` is linear, so it is not abortive. -/
theorem stateRow_not_unwind (n : UInt32) (A : VTy) (x : LifeVar) :
    ¬ (stateRow n A).Unwind x := fun h => by
  have := (h _ (get_mem n A)).1
  simp [OpSig.abort] at this

/-- **No relaxed lend carries `State` at a state type other than `1`**: R1's row answers `1` at
every operation, and `get` answers the state. -/
theorem stateRow_not_resumeO (n : UInt32) {A : VTy} (hA : A ≠ .unit) (x : LifeVar) :
    ¬ Row.ResumeO (stateRow n A) x := fun h =>
  hA (h _ (get_mem n A)).2.2.2.1

/-- The row is not empty, so it is not the pure form's either. -/
theorem stateRow_ne_nil (n : UInt32) (A : VTy) : stateRow n A ≠ [] := by
  simp [stateRow, Row.ofEff]

end LetMutState
