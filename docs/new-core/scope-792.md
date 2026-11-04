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

## 2. The cancel owed at the entry's cancel row (Core's design)

With `contShareT` owing the cancel branch at the stopper's own continuation relation (its table,
its answer), a forwarded cancellable stop fails: the unwinding has the forwarding handler's frame
removed (`K†`, `dead_hndK`), so the outer stop owes it at the outer table and the outer answer,
and the cancel answers `()` (spike `Counter.forward_cancel_fails`).

**Core's chain-world rule is the default** (`Core/EffDefs.lean`, `Core/EffRules.lean`, SPEC §27).
There an entry carries its cancel obligation, `OpEnt.fin = some (cancelObl Tk)`: the unwinding
`K†[raise cancel]` run at the cancel row's table `Tk`, answering `()`. Where a cancel is run, the
canceller's table includes the row (`ewp_ccatch`'s `T.Le Tout`), and rows grow outward (`[sub]`).
The port keeps that shape:

- `OpEntT.cn` is the cancel row, as a set of operations; the unwinding is owed at the stopper's
  table restricted to it (`T.restrict en.cn`), answering `Qunit` (`()`, owning nothing, no records).
- Inclusion is checked where the cancel is run, by `cerwpT_table_mono`: the scheduler and a handler
  run their own operations' cancels at their tasks' table (`restrict_le`); a forwarding handler's
  outer stop owes the cancel at the outer table's row (`restrict_mono`, from `HandleOKT`'s clause
  that the forwarded entry's row is the outer table's).

**Where the tree departs from Core, and why each is forced:**

| Departure | Why |
|---|---|
| The row is a set of keys over the stopper's table, not a table in the entry | An entry whose unwinding performs its own operation (`LC`'s finaliser parks again at `park`) names itself; a table in the entry would be a circular definition. Core's rows are finite trees and would type `LC` with a two-level row; tree-core's D15 already owed the cancel at the stopper's own table, which is the same self-reference |
| `cerwpT` recurses on the index alone (table, answer and base after the colon) | The cancel is owed at another table (the row) and answer (`Qunit`) than the stop's own |
| The base `Fb′` is quantified, over every base every valid frame meets | Core has no frame conditions. A forwarded cancel is run under the outer handler's base, not the stopper's |
| `Qunit` asks the resource empty | Core's cancel end is `NoOwn` with garbage dropped (`wpG_garbage`); the tree has no `ρ⁺` (D4). Decision 73: the cancelled branch's resources are used and its lends ended |

**The spike's `CancelOK` is dropped.** The spike quantified the cancel over every canceller table
`T′` with `CancelOK en.cn T T′` (the row's entries in `T′`, `T′`'s payloads downward closed). With
the obligation fixed at the row, that quantifier is `cerwpT_table_mono` at the use site, as in Core,
and its `PADown T′` conjunct is not needed anywhere: the scheduler's and the general handler's
statements carry no `PADown` of the tasks' table. Nothing in it existed for per-type cleanup; the
row (`cn`) is needed because a `[then]` finaliser may perform (the hardest case).

## 3. What changes

| Statement | Change |
|---|---|
| `OpEntT` | gains `cn`, the cancel row |
| `contShareT` | takes the stopper's table `T` and the cancel relation `Ψc`; the cancel clause owes `Ψc (T.restrict en.cn) Fb′` at every base `Fb′` every valid frame meets |
| `TableT` | reads the cancel relation (`ContP → …`); `Local`, `Down` read both relations |
| `cerwpPostT` | takes the cancel relation |
| `cerwpT` | arguments after the colon; the table reads `cerwpTK` (the relation at `Qunit` at a table) |
| `TableT.Incl`, `opTableT_incl` | retired; `cerwpT_table_mono` is stated over operation tables |
| `SchedOKT`, `SchedOKTLe` | gain the return clause at `Qunit` when an operation owes a cancel branch (`OpTabT.Cancels`) |
| `Park.schedP_ok`, `parked_twp` | gain that the task's answer accepts `Qunit` (park is cancellable); met at `QB` |
| `Park.taskA_cerwpT` | retired: a task holding a borrowed view copy across a cancellable park, whose cancel answered the copy back. A cancel answers `()` owning nothing, so it cannot hand the copy back |
| `twp`, `EndT` | unchanged |

## 4. Not doing; tempting shortcuts → stop

- A hypothesis that the outer answer contains `()`, or that forwarded entries have no cancel
  branch: both restrict handlers; the spike's first answer shows the restriction is otherwise
  needed.
- A statement naming a depth, a handler shape or a number of clauses.
- Anything for per-type cleanup (decision 73).
- Scheduler-interface changes beyond §3's (#795 is on `tree-795`): report instead.

## 5. Results

- `cerwpT_handle`, `cerwpT_handleQ`, `cerwpT_handleStack` (`Core/TreeHandleFwd.lean`).
- `progFwdCancel_safe`, `progFwdCancel3_safe`: the hardest case at depth 1 and 3, through
  `PoolSchedAdequacyT` (`Core/TreeHandleFwdProgs.lean`).
- `handleC_ok`: a handler whose clause cancels under the handler meets `HandleOKT` with its
  cancellable operation (`TCk_cancels`), so the clause and `Qunit` return premises are met
  non-vacuously.

Open: the forwarding instances' handlers have no clause the task reaches (they forward
everything); a closed program with a forwarding handler whose own clause resumes `κ` inside its
lend (`HandlerLendProg`'s shape) is not built. The `…Le` (spawn) variant of `cerwpT_handle` is not
built; `cerwpT_schedHandle_le` covers the spawning scheduler at the top.
