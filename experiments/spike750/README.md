# #750 spike: a cancel as a resume with a raise

The question is whether a linear `κ` with no derived drop, together with a cancel that is a resume
with a raise at the suspension point, makes a lend held across `await` end only after the task's
own cleanup, including cleanup that awaits, without effectful derived drops and without widening
`PinLaw`.

**Answer: no.** The first half holds. It can be stated with today's machine and no new step, and
derived drops stay pure. The second half fails, because `PinLaw` must widen. The relaxed lend's
body must be allowed to stop, be resumed, and then unwind past the lend through finalisers that
stop again. Today's `[lend-R]` premise `Row.ResumeO` excludes that body
(`Premises.not_resumeO_awaitC`, `not_resumeO_cancelled`). Kill criterion 3 applies.

Labels: **[proved in Lean]**, **[checked by inspection]**, **[not verified]**.

## Files

- `Spike750/Runs.lean`: the task of target program 2, written as the checker erases kernel terms
  and run on today's machine. `Support`'s `eval` checks it by `decide`; the falsifier checks it
  with lend tags (`bcc interp --check tags`).
  - `cancelResume_eval`, `cancelRecancel_eval`, `cancelHeld_eval` are #750's cancel. Each
    answers `inl 7` with `live 0`, and the falsifier passes all three.
  - `cancelDead_eval` is today's `κ.2` cancel. The finaliser's `await` passes the dead region and
    the run is stuck at an unhandled operation (wall 5, as a run).
- `Spike750/Premises.lean`: which premises the proposal meets, and which it does not.
- `bc/p2-cleanup-awaits.bc`: the same task in the core text. `bcc check` refuses it at `[lend-R]`.

## The rules

1. **Qualifier.** `await : 1 ↠^lin 1 + 1` (today: `aff`, answering `1`), so
   `κ = U(((1+1) ⊸ F_Σ R) & ⊤)`. A task is `[@d] U((1+1) ⊸ F_Σ (A + Task))`.
   - It is class 3 of §12, with no destructor. Today's task, `U(νX. … & F 1)`, has one.
     (`not_hasDtor_kappaLin`, `not_hasDtor_task` [proved in Lean])
2. **`[await-c]`.** A cancellable operation is performed only through
   `await_n ≜ perform_n (0, ()) to r. case r {inl u. return u | inr u. raise_n (1, u)}`. Here
   `cancelled_n : 1 ↠^aff 0` has the same name `n`. Plain `[perform]` of the operation is refused.
   - Without this rule, `inr` is a value the body may ignore.
3. **The cancel step is a resume**: `cancel κ ≜ (force κ).1 (inr ())`. There is no new step.
   - `hnd(n,H) K[inr ()]` steps to `hnd(n,H) K[raise(n,(1,()))]`.
   - `[finalise]` then runs `K`'s finalisers innermost first, with the region live, so a
     finaliser's `await` is caught by the task's own handler.
   - `[unwind]` ends at the `cancelled` clause.
   - This is `cancelResume_eval` [proved in Lean]; the falsifier reports the finaliser's write
     inside the lend.
4. **`[lend-R]`.** `Row.ResumeO` must admit:
   - an operation answering `1 + 1`;
   - the abortive `cancelled`, raised only by `[await-c]`. This is OQ-1, restricted.

   `PinStop`'s premise widens with it. The variant with a machine step is no better:
   - Its rules: `κ_lin = U((B ⊸ F_Σ R) & F_Σ R)`, `κ.2 ↦ hnd(n,H) K‡[raise(⊥, none)]` with `K‡` =
     `K` without its `ccatch` frames, and `hnd(n,H) K[raise(⊥,e)] ↦ h_c e`.
   - It keeps `Row.ResumeO` as written (`resumeO_awaitLin` [proved in Lean]).
   - But `PinStop` then ranges over a stop inside the lend during a `⊥`-unwind, with `cfin`
     frames in `κ`. That is M7's configuration [checked by inspection].
5. **Interception.**
   - There is none, by construction. Under `[await-c]` the raise sits at `K`'s hole, and `K` is
     free of `n` by `[op]`'s side condition. `[finalise]` runs `D` *before* the pending raise,
     so `D` cannot catch it. [checked by inspection]
   - What bounds the cancel is `[then]`'s `hSD` (decision 69: no `Div` in a finaliser) and the
     finitely many frames of `K`. On every run the cancel performs finitely many `await`s, if the
     canceller keeps resuming. [checked by inspection; the theorem "finalisers are total" is open,
     as today]
   - Catch-and-continue would be bounded only if the task's whole row had no `Div`. Not proposed.
6. **Decision 2 and a scheduler's queue.**
   - A task is not `VTy.Drop` (`not_drop_task` [proved in Lean]), and neither is a `μ` of tasks:
     `VTy.Drop` has no `μ` case.
   - So `[let]`'s `hW` refuses a queue that is live across an abortive operation, and decision 2
     abandons none.
   - A `[then]` finaliser cannot drain the queue either. Driving a cancelled task to its end is an
     unbounded loop, and `hSD` refuses `Div` in a finaliser.
   - Consequences:
     - A scheduler cancels from a `Div` loop in its body (`run_until_empty`).
     - `run_in`'s budgeted cancel-then-`exhausted()` is refused, because a cancelled task may hand
       back a task (`A + Task`).

## Target programs

1. **io_uring, borrowed buffer.** Refused today (`Row.ResumeO`).
   - Under the rules it is *expressed*, conditional on:
     - the widened `PinLaw`;
     - an extern contract that the host holds the view until the `await` on the completion is
       resumed. A host operation that keeps a view past its call is trusted.
   - Its kernel shape is program 2's. [checked by inspection]
   - M8 (an owned buffer in and out) stays unconditional.
2. **`finally D`, where `D` awaits.** Refused today (wall 5; `cancelDead_eval` is stuck).
   - Under the rules it is *expressed*, conditional on the widened `PinLaw`
     (`cancelResume_eval`, `cancelRecancel_eval`).
   - Lowering: the finaliser's `await` is one more resumption point of the task's state machine,
     and the cancel is a call. [not verified; §27's backend rejects a finaliser that suspends]
3. **Nursery.** *Refused*, not unsound.
   - Children borrowing the parent's data is unconditional today (`spawn_in`, BOXED-κ).
   - Waiting for cancelled children is a `Div` loop inside the borrow's scope, which is
     #743's P2 class. It is refused on main, and still refused under the rules unless #743 step 1
     or R2 admits it.
   - Under a cancel of the parent, the wait is a loop in a finaliser, which decision 69 refuses.
   - The holder's configuration runs: a queue holding a task stopped in its cleanup with the lend
     open, resumed later (`cancelHeld_eval`).

## Kill criteria

1. **Effectful derived drops: not needed.** The cleanup is written finalisers, driven by resumes.
   Tasks have no derived drop at all.
2. **A cancel with no bound on termination: not triggered with `[await-c]`.** The bound is
   decision 69's `hSD` [checked by inspection]. Without `[await-c]` it is triggered, because the
   task can ignore `inr` and loop.
3. **A `Row.ResumeO` widening anyway: triggered.** The widening is OQ-1, restricted to
   `cancelled`, not M7's empty-cancel-row relaxation. The variant with a machine step lands on
   M7's configuration.

## Open questions

- Does an OQ-1-restricted widening count as "no gain" against M7?
  - What it buys:
    - a cleanup's `await` goes to the task's own scheduler, not the canceller's;
    - the region stays live, so D3 does not arise for the task's own handlers;
    - no new machine step;
    - the same widening, generalised to every abortive operation, also admits
      `reject/async-r1-raise-across.bc`.
- Should bounded schedulers keep cancel-at-budget? That would mean giving `await` a cancel row
  that records whether a task's cleanup may await, so that a task whose cleanup does not await
  cancels in one call.
- Is `[await-c]`, a rule that refuses plain `[perform]` of an operation, acceptable as a kernel
  rule?
