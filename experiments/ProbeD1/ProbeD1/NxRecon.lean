import ProbeD1.NxFloor

/-!
# ProbeD1 — `reconB′` written as the language writes it (`NEXT.md` §10.3)

The correction of 2026-10-08 (ii): in this language `retry` is an effect handler installed around
the borrow, and the borrow's callback performs operations; it captures no retry combinator. The
synthesis' sketch (§11) put `retry` inside the callback, so the callback captured `retryR`, a
persistent row-polymorphic value, and the `∀I` row's context held it (`NEXT.md` §3.4, 3b-ii).
Written as the language writes it, the program is:

    resumer wait (retry (lend tt (Λ. λb. x ← *b; wait (); y ← *b; y)));
    timeout (lend tt (Λ. λb. x ← *b; wait (); y ← *b; y))

`retry` handles `Fail` around the lend, re-running the attempt once on a raise; `resumer` resumes
`wait`; `timeout` cancels it, and the cancel ends the lend's frame by its finaliser. Each attempt
lends a fresh cell holding `tt`. `*b` reads the cell through the view.

* **The term** (`reconB'`) and its run (`reconB'_eval`: `(tt, ff)` and no cell left; the
  interpreter's run is evidence, as for `genSelf_eval`).
* **Push-stability, judged against this program** (`reconCb_allI`): the borrow's callback is
  closed (by reading `reconCbBody`: it reads only the view, its own binder), so its `∀I` row can be
  read at the empty context, where the row is proved at every index (`allIRowMUFree0`). That the
  program's typing applies the row at a context with no live `U` slot is [unchecked]: the typing is
  not built. What the program owes beyond that is the suspension inside the lend: the callback
  performs `wait` while the 6.64 lend is open, and `timeout`'s cancel ends that lend's frame
  (statements 1–3, tier 2).

The typing at the probe's rule set is not built here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag dFlag)
open BoCa.BoLo (performE)
open Targets (handleWithRet resumeArg cb lendCell)

/-- `wait : 1 ↠^aff 1`, the operation `0` of the name `9`. -/
def waitE : Expr := performE (opArgE 9 0 (.val .unit))

/-- **The borrow's callback body**, under the view `b` (index `0`): `x ← *b; wait (); y ← *b`, and
`x` consumed by a case whose branches answer `y`. -/
def reconCbBody : Expr :=
  bindE (.app (.val (.prim .load)) (.var 0))
    (.seq waitE
      (bindE (.app (.val (.prim .load)) (.var 1))
        (.case (.var 1) (.var 1) (.var 1))))

/-- **The borrow's callback**: `Λ. λb. reconCbBody`. -/
def reconCb : Expr := cb reconCbBody

/-- **One attempt**: lend a fresh cell holding `tt` to the callback, free the cell, answer the
callback's answer. -/
def reconAttempt : Expr := lendCell (.inj₂ unit') reconCb

/-- The answer clause `λx. x`. -/
def idClause : Expr := .val (.lam (.var 0))

/-- **`retry` around an attempt**: handle `Fail` (`raise : 1 ↠^aff 0`, the name `1`); on a raise,
attempt once more under a handler that answers `ff` on a second raise. -/
def retryH (e : Expr) : Expr :=
  handleWithRet 1 idClause
    (.val (.lam (.seq (.var 0) (handleWithRet 1 idClause (.val (.lam (.seq (.var 0) (.inj₁ unit'))))
      e))))
    e

/-- The clause that cancels the continuation and answers `ff`. -/
def cancelFF : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app (.var 0) (.val (.inj₂ .unit))) (.seq (.var 0) (.inj₁ unit'))))))

/-- **`reconB′`, as the language writes it**: the scheduler resumes `wait` around `retry` around the
first lend; `timeout` cancels `wait` around the second; the answer is the pair. -/
def reconB' : Expr :=
  bindE (handleWithRet 9 idClause resumeArg (retryH reconAttempt))
    (bindE (handleWithRet 9 idClause cancelFF reconAttempt)
      (.pair (.var 1) (.var 0)))

/-- **`reconB′` runs**: `(tt, ff)`, the first lend's callback resumed past `wait`, the second's
cancelled with its lend's frame ended by the finaliser, and no cell left. -/
theorem reconB'_eval :
    (match eval reconB' with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- **The `∀I` row at the empty context**, where the closed callback can be read: the row holds
there at every index (`allIRowMUFree0`). -/
theorem reconCb_allI : AllIRowMAt (ℍ := ℍ) .binder0 [] :=
  allIRowMUFree0 [] (fun s hs => by simp at hs)

end ProbeD1

end
