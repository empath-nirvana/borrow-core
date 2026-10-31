import Core.PinLaw
import Spike750.Runs
import Spike750.Premises

/-!
# #750 round 2 — the targets against the kernel rules on this branch

The rules (`Core/`, SPEC §29a): `[await-c]` (`CDerives.effAwait`, `[perform]`'s `hac`), the
cancel-only widening `Row.ResumeOC` of `[lend-R]` with `PinStop` widened, and `[then]` with `Div`
in the finaliser's row (`CDerivesP.effThenDiv`, `PinLaw.fin`), its `Div` recorded in each
cancellable operation's cancel row (`hfin` at `OpSig.finRead`), read by `Row.CancelTotal`.

* **Premises** at each target's rows: which hold, which fail.
* **Runs** of the transaction and of the completion read, written as the checker would erase
  them (`awaitE`), by `Support`'s interpreter (`eval`, by `decide`) and the falsifier with lend
  tags.

No statement here is a typing derivation of a whole target.
-/

namespace Spike750.Round2
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (hndE hndVal raiseE performE ubindE opPayload)
open BoCa.Lifetime (LifeVar)
open Spike750.Runs (lit storeE dOwn clauseCancelled falsify)

/-! ### Rows -/

/-- `await : 1 ↠^lin 1 + 1` at the name `1`, its cancel row `F` (what the finalisers a cancel at
it runs may perform). -/
def awaitF (F : CTy) : OpSig := ⟨1, 0, .lin, .unit, .sum .unit .unit, F⟩

/-- `await` at the empty cancel row. -/
abbrev await0 : OpSig := awaitF (.ret .unit)

/-- `cancelled : 1 ↠^aff 0` at the name `1`. -/
def cancelled : OpSig := ⟨1, 1, .cancel, .unit, .zero, .ret .unit⟩

/-- A completion wait `1 ↠^lin 1` at the name `1`, operation `2`: not cancellable. -/
def complete : OpSig := ⟨1, 2, .lin, .unit, .unit, .ret .unit⟩

/-- `await_n`'s own row. -/
abbrev rowAwait : Row := [await0, cancelled]

/-- The rollback's row: it awaits. -/
abbrev rowD : Row := [await0, cancelled]

/-- The transaction's row: `await`'s cancel row records the rollback's row. -/
abbrev rowTxn : Row := [awaitF (CTy.effOf rowD .unit), cancelled]

theorem awaitB_await (F : CTy) : (awaitF F).awaitB = true := rfl

/-- `[await-c]`: `[perform]` refuses `await` itself. -/
theorem perform_refuses_await (F : CTy) : ¬ (awaitF F).awaitB = false := by
  rw [awaitB_await]; decide

/-- `[await-c]`'s premises at `await_1`'s row. -/
theorem effAwait_premises :
    Row.find rowAwait 1 0 = some await0 ∧ await0.awaitB = true ∧ await0.A = .unit ∧
    Row.find rowAwait 1 1 = some cancelled ∧ cancelled.abort = true ∧ cancelled.A = .unit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem resumeOC_two (x : LifeVar) (F : CTy) : Row.ResumeOC [awaitF F, cancelled] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact .inr (.inl ⟨rfl, by simp [awaitF], fun h => by simp [awaitF, VFree] at h,
      fun _ _ => .unit, trivial⟩)
  · exact .inr (.inr ⟨rfl, rfl, rfl, rfl, by decide, awaitF F, by simp, rfl, rfl⟩)

/-- **The transaction's lend row is admitted by the widened `[lend-R]`.** -/
theorem resumeOC_txn (x : LifeVar) : Row.ResumeOC rowTxn x := resumeOC_two x _

/-- **R1 as it was refuses it**: the answer `1 + 1` and the abortive `cancelled`. -/
theorem not_resumeO_txn (x : LifeVar) : ¬ Row.ResumeO rowTxn x := by
  intro h
  have := (h cancelled (by simp)).1
  simp [OpSig.abort, cancelled, VTy.isZero] at this

/-- The completion read's lend row: `await`, `cancelled`, and the completion wait. -/
theorem resumeOC_io (x : LifeVar) :
    Row.ResumeOC [awaitF (CTy.effOf [complete] .unit), cancelled, complete] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact .inr (.inl ⟨rfl, by simp [awaitF], fun h => by simp [awaitF, VFree] at h,
      fun _ _ => .unit, trivial⟩)
  · exact .inr (.inr ⟨rfl, rfl, rfl, rfl, by decide, awaitF (CTy.effOf [complete] .unit),
      by simp, rfl, rfl⟩)
  · exact .inl ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [complete, VFree] at h,
      fun _ _ => .unit, trivial⟩

/-- **`[then]`'s premises for the transaction's rollback**, `effThen` (no `Div`): the rollback's
row is below the transaction's, its row has no `Div`, and `await`'s cancel row records it. -/
theorem then_premises_txn :
    RowLe rowAwait rowTxn ∧ RowLe rowD rowTxn ∧ Row.divB rowD = false ∧
    (∀ n i o o', Row.find rowAwait n i = some o → Row.find rowTxn n i = some o' →
      o.finRead = true → ThenLe o.fin rowD o'.fin) := by
  have hF : ∀ X, FinLe (.ret .unit) X := fun X => by
    rw [FinLe]; right; exact ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf] at h⟩
  have hle : RowLe rowAwait rowTxn := by
    refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨awaitF (CTy.effOf rowD .unit), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
    · exact ⟨cancelled, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
  refine ⟨hle, hle, rfl, fun n i o o' hf hf' _ => ?_⟩
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · obtain rfl : o' = awaitF (CTy.effOf rowD .unit) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]; right
    refine ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, awaitF] at h, fun n i o h => ?_⟩
    refine ⟨o, by simpa [awaitF, CTy.rowOf_effOf] using h, OpSig.Sig.refl o, fun hc => ?_⟩
    obtain ⟨hm, -, -⟩ := Row.find_mem h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [capB, cancelled, awaitF, VTy.isZero] at hc
  · simp [OpSig.finRead, capB, cancelled, OpSig.awaitB, VTy.isZero] at *

/-- The termination-sensitive reading: the transaction's row is `CancelTotal` (its rollback has
no `Div`). -/
theorem cancelTotal_txn : Row.CancelTotal rowTxn := by
  intro o ho _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-! ### The nursery -/

/-- The nursery's wait for its children, in its finaliser: `Div`'s `tick` beside the awaits. -/
abbrev rowWait : Row := [await0, cancelled, tickSig]

/-- The parent's row: `await`'s cancel row records the finaliser's `Div`. -/
abbrev rowNursery : Row := [awaitF (CTy.effOf rowWait .unit), cancelled, tickSig]

/-- **(a): the finaliser is typed** by `effThenDiv`: the body `await_1` has no capturable
operation, so `hcap` holds; `effThen`'s `hSD` does not. -/
theorem nursery_thenDiv_premises :
    (∀ o ∈ rowAwait, capB o.q o.B = false) ∧ Row.divB rowWait = true := by
  refine ⟨fun o ho => ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> rfl

/-- **(a): the cancel row says so.** The parent's row is not `CancelTotal`: a cancel of it may
not end, which `run_in`'s cancel-at-budget reads. -/
theorem not_cancelTotal_nursery : ¬ Row.CancelTotal rowNursery := by
  intro h
  have := (h (awaitF (CTy.effOf rowWait .unit)) (by simp) rfl).2
  exact absurd this (by decide)

/-- **(a): the lend refuses the nursery.** The children hold the request's borrow, so the wait
is inside the lend, and the lend's row then holds `tick`, which no clause of `Row.ResumeOC`
admits: not resuming at `1`, not cancellable (it is `Div`'s), not abortive. -/
theorem not_resumeOC_nursery (x : LifeVar) : ¬ Row.ResumeOC rowNursery x := by
  intro h
  rcases h tickSig (by simp) with h | h | h
  · exact absurd h.2.2.2.1 (by simp [tickSig, nextTy])
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)

/-- **(b): a fuelled wait cannot end its run at exhaustion with the children left.** A task
(`[@a] U((1 + 1) ⊸ C)`) is not `VTy.OwnFree`, so `[let]`'s `hW` refuses a slot holding one across a
row with an abortive operation (the exhaustion's `exhausted()`), and decision 2 abandons none. -/
theorem not_drops_task (a : Lifetime.Life) (C : CTy) :
    ¬ Ctx.OwnFree [⟨.box a (.thunk (.arr (.sum .unit .unit) C)), true⟩] := by
  intro h
  exact Spike750.Premises.not_drop_task a _ (h ⟨_, true⟩ (List.mem_singleton.mpr rfl) rfl)

/-! ### Runs

The task `hnd (1, H) (withborU d c (λ_. λm. B))` as in `Runs.lean`, its scheduler's clauses
handing `κ` out (`inr k`) so that a driver decides each resume. -/

/-- The answer clause: `λ(c, v). free c; inl v`. -/
def hRetL : Val :=
  Val.lam (.letpair (.var 0) (.app (.lam (.inj₁ (.var 1))) (.app (.prim .free) (.var 1))))

/-- A clause that hands its continuation out: `λ(x, k). inr k`. -/
def clauseOut : Val := Val.lam (.letpair (.var 0) (.inj₂ (.var 0)))

def taskL (qs hs : Val) (B : Expr) : Expr :=
  .app (.lam (hndE (hndVal 1 qs hRetL hs)
      (.app (.app (Fig16.LogRel.Core.withborUE dOwn) (.var 0)) (.lam (.lam B)))))
    (.app (.prim .alloc) (lit 10))

/-- The transaction under the lend, `m` at index 0: `x ← await_1 then (m := 5; 5) unwind
(await_1; m := 99)`: the commit writes 5; the rollback awaits, then writes 99. -/
def bodyTxn : Expr :=
  thenE (.seq (storeE (.var 1) (lit 5)) (lit 5)) (.seq (awaitE 1) (storeE (.var 1) (lit 99)))
    (awaitE 1)

/-- `κ.1 v`. -/
def resumeK (k v : Expr) : Expr := .app (.app k (Val.inj₁ Val.unit).1) v

/-- Drive a task that stops twice: answer `a₁` at the first stop and `a₂` at the second. -/
def drive2 (a₁ a₂ : Expr) (t : Expr) : Expr :=
  .app (.lam (.case (.var 0) (.inj₁ (.var 0))
      (.app (.lam (.case (.var 0) (.inj₁ (.var 0))
          (.app (.lam (.case (.var 0) (.inj₁ (.var 0)) (.inj₂ .unit)))
            (resumeK (.var 0) a₂))))
        (resumeK (.var 0) a₁))))
    t

def txn : Expr :=
  taskL (qualsVal [.lin, .cancel]) (Val.pair clauseOut (Val.pair clauseCancelled Val.unit))
    bodyTxn

/-- **Cancelled**: the first `await` is answered `inr ()` (the cancel), the rollback's `await`
`inl ()`: the rollback writes 99 inside the lend, the lend ends, `cancelled`'s clause answers 7. -/
def txnCancel : Expr := drive2 (Val.inj₂ Val.unit).1 (Val.inj₁ Val.unit).1 txn

/-- **Committed**: the first `await` answered `inl ()`. -/
def txnCommit : Expr := drive2 (Val.inj₁ Val.unit).1 (Val.inj₁ Val.unit).1 txn

theorem txnCancel_eval :
    (match eval txnCancel with | .value ⟨.inj₁ (.prim (.lit (.i32 7))), _⟩ false => true | _ => false)
      = true := by decide

theorem txnCommit_eval :
    (match eval txnCommit with | .value ⟨.inj₁ (.prim (.lit (.i32 5))), _⟩ false => true | _ => false)
      = true := by decide

/-- The completion read: `await_1` for the submission, its rollback a completion wait (`1.2`, not
cancellable) and then the host's write into the buffer (42), inside the lend. -/
def bodyIO : Expr :=
  thenE (.seq (storeE (.var 1) (lit 5)) (lit 5))
    (.seq (performE (opPayload 1 2 Val.unit).1) (storeE (.var 1) (lit 42)))
    (awaitE 1)

def io : Expr :=
  taskL (qualsVal [.lin, .cancel, .lin])
    (Val.pair clauseOut (Val.pair clauseCancelled (Val.pair clauseOut Val.unit))) bodyIO

/-- **Cancelled in flight**: the submission's `await` answered `inr ()`; the completion wait is
resumed (the completion arrived); the write lands inside the lend, then the lend ends. -/
def ioCancel : Expr := drive2 (Val.inj₂ Val.unit).1 Expr.unit io

theorem ioCancel_eval :
    (match eval ioCancel with | .value ⟨.inj₁ (.prim (.lit (.i32 7))), _⟩ false => true | _ => false)
      = true := by decide

#eval falsify txnCancel
#eval falsify txnCommit
#eval falsify ioCancel

end Spike750.Round2
