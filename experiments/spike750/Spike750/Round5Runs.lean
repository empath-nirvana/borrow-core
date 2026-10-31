import Spike750.Round2

/-!
# #743 round 5 — #750's cancel-by-resume with cleanup that waits, at depth 1–5

Kernel terms, written as the checker would erase them, run by the falsifier's source interpreter
(`Backend.Falsify.interpSource`) at both allocators (`least`, `fresh`) with lend tags. Round 2's
transaction and completion read (`Round2.bodyTxn`, `Round2.bodyIO`) nested: level `j` of `d` lends
a fresh cell, awaits (`await_1`, cancellable) and lends the next level's cell inside, under a
`[then]` whose finaliser either awaits and writes through the level's view (the rollback: a
cleanup that waits) or waits on the completion `1.2` (lin, answering `1`, not cancellable) and
writes 42 (the completion read). Every callback is closed but for its view, as a typed one is.

A driver answers each stop from a list: the `k`-th `await` on the way down is the cancel
(`inr ()`), the cleanup waits on the way up are answered `inl ()` or, for a **second cancel during
cleanup**, `inr ()` (the rollback's `await` raises `cancelled` inside its finaliser, and the unwind
goes on outward). A completion wait has no `inr`: it is answered `()`, so a second cancel cannot
end the lend before the write lands (#750's completion rule).

No statement here is a typing derivation of the terms.
-/

namespace Spike750.Round5Runs
open BoCa
open BoCa.BoLo (hndE hndVal raiseE performE ubindE opPayload)
open BoCa.Fig16.LogRel.Core (withborUE qualsVal awaitE thenE)
open Spike750.Runs (lit storeE dOwn clauseCancelled)
open Spike750.Round2 (taskL clauseOut resumeK)

/-- `c ← alloc 10; p ← withborU d c (λ_. λm. B); let (c, v) = p; free c; v`. -/
def lendIn (B : Expr) : Expr :=
  .app (.lam (.app (.lam (.letpair (.var 0) (.app (.lam (.var 1)) (.app (.prim .free) (.var 1)))))
      (.app (.app (withborUE dOwn) (.var 0)) (.lam (.lam B)))))
    (.app (.prim .alloc) (lit 10))

/-- The finaliser at a level, the view at index 1: the rollback (`await`, then `m := 99`) or the
completion read (the completion wait `1.2`, then `m := 42`). -/
def finE (io : Bool) : Expr :=
  if io then .seq (performE (opPayload 1 2 Val.unit).1) (storeE (.var 1) (lit 42))
  else .seq (awaitE 1) (storeE (.var 1) (lit 99))

/-- Level `j` of `d`, the view at index 0: `x ← (await_1; lend the next level) then (m := 5;
j + 1) unwind fin`. -/
def level (io : Bool) (d : Nat) (j : Nat) : Expr :=
    if j + 1 < d then
      thenE (.seq (storeE (.var 1) (lit 5)) (lit (UInt32.ofNat (j + 1)))) (finE io)
        (.seq (awaitE 1) (lendIn (level io d (j + 1))))
    else
      thenE (.seq (storeE (.var 1) (lit 5)) (lit (UInt32.ofNat (j + 1)))) (finE io) (awaitE 1)
  termination_by d - j


/-- The task: the scheduler's clauses hand `κ` out at `1.0` and `1.2`, `cancelled` answers 7. -/
def task (io : Bool) (d : Nat) : Expr :=
  taskL (qualsVal [.lin, .cancel, .lin])
    (Val.pair clauseOut (Val.pair clauseCancelled (Val.pair clauseOut Val.unit))) (level io d 0)

/-- Drive a task through the answers, in order. -/
def driveN : List Expr → Expr → Expr
  | [], t => .app (.lam (.case (.var 0) (.inj₁ (.var 0)) (.inj₂ .unit))) t
  | a :: as, t => .app (.lam (.case (.var 0) (.inj₁ (.var 0)) (driveN as (resumeK (.var 0) a)))) t

def inlE : Expr := (Val.inj₁ Val.unit).1
def inrE : Expr := (Val.inj₂ Val.unit).1

/-- The answers: `k - 1` awaits answered `inl`, the `k`-th cancelled (`k = 0`: none, all `d`
answered `inl`); then the `k` cleanup waits, the `i`-th a second cancel when `sc i`. -/
def answers (io : Bool) (d k : Nat) (sc : Nat → Bool) : List Expr :=
  if k = 0 then List.replicate d inlE
  else List.replicate (k - 1) inlE ++ [inrE] ++
    (List.range k).map fun i => if io then Expr.unit else if sc i then inrE else inlE

def run (o : Backend.Falsify.Opts) (e : Expr) : String :=
  match Backend.Falsify.interpSource o 1000000 e with
  | .ok (out, st) => (String.fromUTF8! out.out).trimAsciiEnd.toString ++ " | " ++ st
  | .error s => "error: " ++ s

/-- Every schedule at depth `d`: no cancel, a cancel at each level, each with no second cancel,
every cleanup cancelled again, and every other one. -/
def schedules (io : Bool) (d : Nat) : List (String × List Expr) :=
  ("commit", answers io d 0 fun _ => false) ::
  (List.range d).flatMap fun k =>
    [(s!"cancel@{k + 1}", answers io d (k + 1) fun _ => false)] ++
    (if io then [] else
      [(s!"cancel@{k + 1}+2nd-all", answers io d (k + 1) fun _ => true),
       (s!"cancel@{k + 1}+2nd-odd", answers io d (k + 1) fun i => i % 2 == 1)])

/-- One line per (depth, schedule, allocator): the answer, `live`, and the falsifier's counts. -/
def report (io : Bool) : List String :=
  (List.range 5).flatMap fun d' =>
    let d := d' + 1
    (schedules io d).flatMap fun (nm, as) =>
      [⟨.least, true⟩, ⟨.fresh, true⟩].map fun (o : Backend.Falsify.Opts) =>
        s!"{if io then "io" else "txn"} d={d} {nm} {repr o.alloc}: {run o (driveN as (task io d))}"

#eval (report false).foldl (· ++ "\n" ++ ·) ""
#eval (report true).foldl (· ++ "\n" ++ ·) ""

end Spike750.Round5Runs
