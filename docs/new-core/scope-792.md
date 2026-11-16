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
  table restricted to it (`T.restrict en.cn`), answering the entry's cancel answer (`QC`).
- Inclusion is checked where the cancel is run, by `cerwpT_table_mono`: the scheduler and a handler
  run their own operations' cancels at their tasks' table (`restrict_le`); a forwarding handler's
  outer stop owes the cancel at the outer table's row (`restrict_mono`, from `HandleOKT`'s clause
  that the forwarded entry's row is the outer table's).

**The cancel's answer is the entry's** (`OpEntT.QC`). Core's cancel answers `1`, the rest of the
cancelled branch dropped as `NoOwn` garbage (`wpG_garbage`). The tree has no `ρ⁺` (D4), so what a
cancelled branch still holds goes back through the answer, as #817 does: park's cancel answer is
`QCV` (`()`, no records, copies of lends, `ViewsT`), the same relation as #817's task answer `QV`
(`QV := QCV`), so `poolTJ_cancel` deposits a cancelled task's copies at the nearest joiner. The
answer travels with the entry, not the stopper, so a forwarded cancel answers the same at the
outer handler; the handler asks its return clause at each cancellable own operation's `QC`.
`Park.taskA_cerwpT` (a cancel handing a borrowed copy back) holds again.

**Departures from Core's shape, and their status:**

| Departure | Status |
|---|---|
| 1. The row as keys over the stopper's table, not a table in the entry | **Not reverted, no Lean configuration.** Core's rows are finite trees ordered by `RowLe` (an entry at a key with a smaller row is below the table's). Porting that needs `OpEntT` as a nested inductive with a row field and `cerwpT_table_mono` up to the entry order. `LC` under `HS` would then be typed with a two-level row at `park`. I have not built that and have not shown it fails; the keys route admits rows of any depth (an unwinding that performs its own operation names itself), which tree-core's D15 already admitted by owing the cancel at the stopper's own table |
| 2. `cerwpT` recursing on the index alone | **Follows from 1, no separate configuration.** With the row as keys, the cancel is owed at `cerwpT` itself at another table and answer, so the relation recurses. With Core's shape the obligation would be a relation built before the entry (`cancelObl Tk`), and `cerwpT` could keep its parameters before the colon. Reverting 1 reverts 2 |
| 3. The cancel's base quantified | **Reverted.** The cancel is owed under frames meeting the stopper's base and the entry's `fd`, as a resume. A canceller at another base runs it there by `cerwpT_base_mono`; `cerwpT_handle` asks that the outer base's frames meet the inner base (`hFbI`), and a stack that each base's frames are the valid ones |
| 4. `Qunit` | **Replaced** by the entry's cancel answer (above) |

`CancelOK` is dropped: with the obligation fixed at the row, its quantifier is
`cerwpT_table_mono` at the use site, as in Core, and its `PADown` conjunct is needed nowhere.

## 3. What changes

| Statement | Change |
|---|---|
| `OpEntT` | gains `cn` (the cancel row) and `QC` (the cancel's answer) |
| `contShareT` | `contShareT T en F k w ls O K v Ψ Ψc`: the cancel clause owes `Ψc (T.restrict en.cn) en.QC F (fdAt en v F O′) w′ O′ k′ ls′ (unwindE K) ρ′` |
| `ContP` | `OpTabT → TPostV → TFrame → ContT` |
| `TableT` | reads the cancel relation (`ContP → …`); `Local`, `Down` read both relations |
| `cerwpPostT` | takes the cancel relation |
| `cerwpT` | arguments after the colon; the table reads `cerwpTK` (the relation at a table and answer) |
| `TableT.Incl`, `opTableT_incl` | retired; `cerwpT_table_mono` is stated over operation tables; #817's `InclLe` reads the cancel relation |
| `SchedOKT`, `SchedOKTLe` | gain the return clause at each cancellable operation's `QC` |
| `Park.schedP_ok`, `parked_twp` | gain that the task's answer accepts `QCV`; `taskB_parked` is read at `QCV` |
| `QV` | `abbrev QV := QCV` |
| `twp`, `EndT` | unchanged |

## 4. Not doing; tempting shortcuts → stop

- A hypothesis that the outer answer contains `()`, or that forwarded entries have no cancel
  branch: both restrict handlers; the spike's first answer shows the restriction is otherwise
  needed.
- A statement naming a depth, a handler shape or a number of clauses.
- Anything for per-type cleanup (decision 73).
- Scheduler-interface changes beyond §3's (#795 is on `tree-795`): report instead.

## 5. Results

- `cerwpT_handle`, `cerwpT_handleQ`, `cerwpT_handleStack` (`Core/TreeHandleFwd.lean`);
  `cerwpT_table_mono`, `cerwpT_base_mono` (`Core/TreeWpEff.lean`).
- `progFwdCancel_safe`, `progFwdCancel3_safe`: the hardest case at depth 1 and 3, through
  `PoolSchedAdequacyT` under #817's `HS` (`Core/TreeHandleFwdProgs.lean`).
- `handleC_ok`: a handler whose clause cancels under the handler meets `HandleOKT`, its clause and
  cancel-answer return premises met non-vacuously.
- `progJoin_safe`, `progCancel_safe`, `Park.taskA_cerwpT` hold at the new share.

**Next (not built; sized before starting):**
1. A closed program where a forwarding handler's own clause resumes `κ` inside its lend: a handler
   `hnd_ask` between `{ask} ∪ tabAt k` and `tabAt k`, its clause `askClause` (allocate, load,
   resume, free) proved at `ClauseT` at `tabAt k` rather than at the empty table, under `HS`.
   About 150–250 lines: `askClause_ok`'s proof re-read at `cerwpT (opTableT (tabAt k))`, the task
   table and its down-closure, the root and the adequacy.
2. The spawn variant `cerwpT_handle_le` (clauses asked at stops `k ≤ N`), so a forwarding handler's
   clause may run a task under itself. About 100 lines if `cerwpT_handleQ` takes the bound as a
   parameter and `cerwpT_handle` becomes its instance.
3. Departure 1: Core's finite rows with `RowLe`, or a configuration showing them insufficient at
   the tree.
