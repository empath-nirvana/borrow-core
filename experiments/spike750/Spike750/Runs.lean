import Core.EffBorrow
import Backend.Falsify

/-!
# #750 — the cancel as a resume, run on today's machine

Kernel terms, written as the checker would erase them, run by `Support`'s interpreter (`eval`) and
by the falsifier with lend tags (`Backend.Falsify.interpSource`, `bcc interp --check tags`). No
rule, step or primitive is added: every term here is a term of today's kernel.

The task is `hnd (1, H) (withborU d c (λ_. λm. B))`: a relaxed lend of the owner's cell `c` as
`m`, its body `B` awaiting under a finaliser that itself awaits and then writes 99 through `m`.

* **`cancelResume`** (#750's proposal). `await` is operation `1.0`, linear, answering `1 + 1`; the
  body raises `1.1` (abortive) on `inr`. The scheduler's clause for `1.0` reads the argument: the
  body's `await` (`inl ()`) it cancels by **resuming** `κ` with `inr ()`; the finaliser's `await`
  (`inr ()`) it resumes with `inl ()`. The region is live, so the finaliser's `await` is caught by
  the task's own handler. The run answers `inl 7` ("cancelled"), the write through `m` happens
  with the lend's tag active, and every cell is freed.
* **`cancelDead`** (today's §19 cancel). The same task with `await` affine, answering `1`, the
  clause cancelling `κ` by its second branch (`κ (inj₂ ())`). The region is dead
  (`Kont.dead`), so the finaliser's `await` passes it and no live handler of `1` is left: the run
  is stuck at an unhandled operation. This is wall 5 of the literature pass, as a run.

Both programs are refused by the checker today: `cancelResume` at `[lend-R]`'s `Row.ResumeO`
(its row holds an abortive operation and an operation answering `1 + 1`;
`experiments/spike750/bc/p2-cleanup-awaits.bc`), `cancelDead` at `[then]`'s cancel-row premise
(the finaliser's `await` must be in the cancel row of the body's `await`, and `Row.ResumeO` asks it
empty). Neither run is a typing claim.
-/

namespace Spike750.Runs
open BoCa
open BoCa.BoLo (hndE hndVal raiseE performE ubindE opPayload)
open BoCa.Fig16.LogRel.Core (withborUE qualsVal)

/-- An `i32` literal. -/
def lit (n : UInt32) : Expr := (Val.i32 n).1

/-- `store l v`. -/
def storeE (l v : Expr) : Expr := .app (.app (.prim .store) l) v

/-- The owner's finaliser `d = λc. free c`, as the checker writes it. -/
def dOwn : Expr := .lam (.app (.lam (.app (.lam .unit) (.var 0))) (.app (.prim .free) (.var 0)))

/-- The handler's answer clause: `λ(c, v). free c; inr v`. -/
def hRet : Val := Val.lam (.letpair (.var 0) (.app (.lam (.inj₂ (.var 1))) (.app (.prim .free) (.var 1))))

/-- The task's body under the lend, `m` at index 0:
`r <- perform (1, (0, inl ())) unwind (s <- perform (1, (0, inr ())); case s {inl. m := 99 | inr. ()});
 case r {inl. m := 5; 5 | inr. raise (1, (1, ()))}` -/
def bodyResume : Expr :=
  ubindE
    (Val.pair
      (Val.lam (.case (.var 0) (.seq (storeE (.var 2) (lit 5)) (lit 5))
        (raiseE (opPayload 1 1 Val.unit).1)))
      (Val.lam (.app (.lam (.case (.var 0) (storeE (.var 3) (lit 99)) .unit))
        (performE (opPayload 1 0 (Val.inj₂ Val.unit)).1))))
    (performE (opPayload 1 0 (Val.inj₁ Val.unit)).1)

/-- The scheduler's clause for `1.0` at a linear `κ`: `λ(x, k). case x {inl. (k (inl ())) (inr ())
| inr. (k (inl ())) (inl ())}`: the body's `await` cancelled by a resume, the finaliser's resumed. -/
def clauseResume : Val :=
  Val.lam (.letpair (.var 0) (.case (.var 1)
    (.app (.app (.var 1) (Val.inj₁ Val.unit).1) (Val.inj₂ Val.unit).1)
    (.app (.app (.var 1) (Val.inj₁ Val.unit).1) (Val.inj₁ Val.unit).1)))

/-- The clause for the abortive `1.1`: `λ_. inl 7`, "cancelled". -/
def clauseCancelled : Val := Val.lam (.inj₁ (lit 7))

/-- The task under its scheduler, the lend of a fresh cell holding 10. -/
def task (qs hs : Val) (B : Expr) : Expr :=
  .app (.lam (hndE (hndVal 1 qs hRet hs)
      (.app (.app (withborUE dOwn) (.var 0)) (.lam (.lam B)))))
    (.app (.prim .alloc) (lit 10))

/-- **#750's cancel**: `await` linear, the cancel a resume with `inr ()`. -/
def cancelResume : Expr :=
  task (qualsVal [.lin, .cancel]) (Val.pair clauseResume (Val.pair clauseCancelled Val.unit)) bodyResume

/-- The task's body for today's cancel: `await` answering `1`, the finaliser awaiting and writing. -/
def bodyDead : Expr :=
  ubindE
    (Val.pair (Val.lam (.seq (storeE (.var 1) (lit 5)) (lit 5)))
      (Val.lam (.seq (performE (opPayload 1 0 (Val.inj₂ Val.unit)).1) (storeE (.var 1) (lit 99)))))
    (performE (opPayload 1 0 (Val.inj₁ Val.unit)).1)

/-- Today's clause: `λ(x, k). k (inr ()); inl 7`, the cancel branch of an affine `κ`. -/
def clauseDead : Val :=
  Val.lam (.letpair (.var 0) (.seq (.app (.var 0) (Val.inj₂ Val.unit).1) (.inj₁ (lit 7))))

/-- **Today's cancel**: `await` affine, the cancel `κ`'s second branch over the dead region. -/
def cancelDead : Expr :=
  task (qualsVal [.cancel]) (Val.pair clauseDead Val.unit) bodyDead

/-! ### The runs -/

/-- `cancelResume` answers `inl 7`, every cell freed. -/
theorem cancelResume_eval :
    (match eval cancelResume with | .value ⟨.inj₁ (.prim (.lit (.i32 7))), _⟩ false => true | _ => false)
      = true := by
  decide

/-- `cancelDead` is stuck at an operation no live handler receives. -/
theorem cancelDead_eval :
    (match eval cancelDead with | .stuck .unhandled => true | _ => false) = true := by
  decide

/-- The falsifier with lend tags: the write through `m` in the finaliser is inside the lend, and
every tag ends. Prints the answer and `live 0`. -/
def falsify (e : Expr) : String :=
  match Backend.Falsify.interpSource ⟨.fresh, true⟩ 100000 e with
  | .ok (o, _) => String.fromUTF8! o.out
  | .error s => "error: " ++ s

#eval falsify cancelResume
#eval falsify cancelDead

/-! ### Two more schedulers for the same task

* **`cancelRecancel`**: the scheduler answers the finaliser's `await` with `inr ()` too, so the
  finaliser takes its `inr` arm (no write) and the cancel goes on: the run still ends at `inl 7`.
* **`cancelHeld`**: the scheduler hands the task back to its caller when the task stops inside its
  cleanup (`inr k'`), with the lend still open; the caller, a queue's holder, resumes it later
  with `inl ()`. This is the configuration a scheduler's queue holds in target program 3. -/

/-- The clause that cancels at the body's `await` and again at the finaliser's. -/
def clauseRecancel : Val :=
  Val.lam (.letpair (.var 0) (.case (.var 1)
    (.app (.app (.var 1) (Val.inj₁ Val.unit).1) (Val.inj₂ Val.unit).1)
    (.app (.app (.var 1) (Val.inj₁ Val.unit).1) (Val.inj₂ Val.unit).1)))

def cancelRecancel : Expr :=
  task (qualsVal [.lin, .cancel]) (Val.pair clauseRecancel (Val.pair clauseCancelled Val.unit)) bodyResume

/-- The clause that cancels at the body's `await` and, at the finaliser's, answers `inr k'`: the
task stopped in its cleanup, handed out. -/
def clauseHand : Val :=
  Val.lam (.letpair (.var 0) (.case (.var 1)
    (.app (.app (.var 1) (Val.inj₁ Val.unit).1) (Val.inj₂ Val.unit).1)
    (.inj₂ (.var 1))))

/-- The holder: `case task {inl v. inl v | inr k'. (k' (inl ())) (inl ())}`. -/
def cancelHeld : Expr :=
  .app (.lam (.case (.var 0) (.inj₁ (.var 0))
      (.app (.app (.var 0) (Val.inj₁ Val.unit).1) (Val.inj₁ Val.unit).1)))
    (task (qualsVal [.lin, .cancel]) (Val.pair clauseHand (Val.pair clauseCancelled Val.unit)) bodyResume)

theorem cancelRecancel_eval :
    (match eval cancelRecancel with | .value ⟨.inj₁ (.prim (.lit (.i32 7))), _⟩ false => true | _ => false)
      = true := by
  decide

theorem cancelHeld_eval :
    (match eval cancelHeld with | .value ⟨.inj₁ (.prim (.lit (.i32 7))), _⟩ false => true | _ => false)
      = true := by
  decide

#eval falsify cancelRecancel
#eval falsify cancelHeld

end Spike750.Runs
