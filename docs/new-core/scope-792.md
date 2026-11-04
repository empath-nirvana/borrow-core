# Scope: `[handle]` for every typed handler at the tree relation, forwarding included (#792)

Part of #771 (D13's coverage limit, #789 S4). Branch `tree-792`, on `tree-core`. Built from the
second spike (`handle-spike` 7039072e, `experiments/HandleSpike/Param*.lean`), which said yes.

## 0. The hardest case

**A handler that forwards an operation to an outer handler, inside a lend, whose outer clause
cancels the stored continuation while the forwarded operation's finaliser performs.** The task
opens a lend and stops at a cancellable operation of the outer handler's, holding the lend cell
across the stop; the operation passes outward through the forwarding handler. The outer clause
cancels the stored continuation. The unwinding (`K†`, with the forwarding handler's frame removed)
runs the task's finaliser, which performs the outer handler's operation again while the lend is
still open, and comes back to the outer clause as an ordinary stored continuation. Resumed or
cancelled again, it ends the lend and answers `()` owning nothing.

It stays in. The general lemma covers it (`cerwpT_handle`'s forwarded-stop cancel case) and a
closed instance exercises it through the pool scheduler's adequacy (`progFwdCancel_safe`: the
loan-cancel task `LC` under a forwarding handler, cancelled by `HS`'s `cancel` clause).

## 1. Kernel target

`[handle]` without `hdv` at `cerwpT`/`twp`, for every handler `hnd (n₀, (qs, (h_ret, hs)))`
between a computation at a table `T` and an outer table `To`:
- clauses that resume, store `κ` (stop), or cancel it;
- operations of other names forwarded to `To`;
- by induction on the index, the conclusion again `cerwpT` at `To`, so a stack of any depth is
  one induction on the stack.

`twp` and `EndT` keep their statements.

## 2. The change the spike found: the cancel owed at every canceller

With `contShareT` owing the cancel branch at the stopper's own continuation relation (its table,
its answer), a forwarded cancellable stop fails: the unwinding has the forwarding handler's frame
removed (`K†`, `dead_hndK`), so the outer stop owes it at the outer table and the outer answer,
and the cancel answers `()` (spike `Counter.forward_cancel_fails`).

The change (spike, second answer): `contShareT`'s cancel clause owes the unwinding at **every
canceller**: at every table `T′` and base `Fb′` meeting the entry's canceller condition, it is
`cerwpT (opTableT T′) Qunit Fb′`, answering `()` owning nothing.

- `OpEntT.cn`: the operations the unwinding may perform.
- `CancelOK cn T T′`: `T′` has `T`'s entries at `cn`, and `T′`'s payload relations are downward
  closed (`PADown`).
- `cerwpT` takes its table, answer and base after the colon (the cancel's table varies), defined
  by recursion on the index; `TableT` reads the cancel relation (`ContP`).

### `CancelOK` against D15

D15 (kept by #793): the cancel branch has to run because a cancelled task may hold `own` cells
(used, not lost), `mut` cells (one holder), a copy only the frame holds, or a view's last copy.
The unwinding runs `[then]` finalisers and the unwinding borrow forms. Read against that:

- **`cn` agreement.** A `[then]` finaliser may perform (the hardest case). The canceller must
  handle what it performs; the stopper's table is the only description of those operations the
  share has. Needed by D15 now; not per-type cleanup.
- **`PADown T′`.** The unwinding's run steps deterministically, which needs its postcondition
  downward closed (`cerwpPostT_down`), so the canceller's payload relations must be. Technical,
  not cleanup.
- **`Qunit` (the answer `()`, owning nothing, no records).** This is decision 73's guarantee: the
  cancelled branch's resources are used and its lends ended. Not cleanup.

Nothing in `CancelOK` exists only to run per-type cleanup; nothing is dropped. The spike's `cn` is
kept as a predicate on operations (the finaliser's operations are a property of the program, not
of a type's close).

## 3. What changes

| Statement | Change |
|---|---|
| `OpEntT` | gains `cn` |
| `contShareT` | takes the stopper's table `T` and the cancel relation `Ψc`; the cancel clause owes `Ψc T′ Fb′` at every `CancelOK` canceller |
| `TableT` | reads the cancel relation (`ContP → …`); `Local`, `Incl`, `Down` read both relations |
| `cerwpPostT` | takes the cancel relation |
| `cerwpT` | arguments after the colon; the table reads `cerwpTK` (the relation at `Qunit` at each canceller) |
| `SchedOKT`, `SchedOKTLe` | gain the return clause at `Qunit` and `PADown T` (the scheduler is its own tasks' canceller) |
| `twp`, `EndT` | unchanged |

## 4. Not doing; tempting shortcuts → stop

- A hypothesis that the outer answer contains `()`, or that forwarded entries have no cancel
  branch: both restrict handlers; the spike's first answer shows the restriction is otherwise
  needed.
- A statement naming a depth, a handler shape or a number of clauses.
- Anything for per-type cleanup (decision 73).
- Scheduler-interface changes beyond §3's (#795 is on `tree-795`): report instead.

## 5. Status

See the PR body.
