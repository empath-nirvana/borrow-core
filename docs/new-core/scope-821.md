# Scope: #821, cross-task lends across suspension on the chain relation

Branch `cross-821`, from `chain-791` (254aaa19).

## Target

`OrDiverges` through `poolSchedAdequacyN` for (1) an `imm` lend shared with a spawned child that
holds the view across `park` while the spawner reads, the child resumed or cancelled; (2) a `mut`
lend to a spawned child that holds the borrow across `park` and writes through it, the child
resumed or cancelled.

## Result

### The obstruction: a stop that carries a borrow out of the lending segment

`Core/Chain/CrossStopN.lean`.

- `erwp_refuses_borrowOut`: `rwpG` asks `ρ ↭ π` at every stop. A segment whose start holds no
  borrow of `ℓ` in its flattening cannot stop with a payload holding a non-`own` cell at `ℓ`: that
  cell is in `⦇π⦈` with its kind, and `↭`'s `imm` clause (an equivalence) or `mut` clause (each
  `mut` cell of `⦇π⦈` has one in `⦇ρ⦈`) asks it of `⦇ρ⦈`. From any configuration the relation
  quantifies over.
- `not_crossTaskILend`: `CrossTaskILend` (`forest`'s `erwp_I_frameK` without the payload condition,
  restated here with `ILendOKX`) is refuted. At the table `TOutI 0 0` (one `lin` entry whose
  payload is a copy of the borrow; `ILendOKX` holds), the borrowed run `perform` is in `erwp` at
  every index (the borrow duplicated by 6.116, one copy to the payload), and the lender's run from
  `0 ↦ own(())` is not (`erwp_refuses_borrowOut₀`). Every hypothesis discharged; the world is
  `TWNC.alloc` from the empty one.
- `not_crossTaskMLend`: the same for the Mut Frame (`erwp_M_frame` without `LendOK.pa`), the
  payload the `mut` borrow itself.

So with the scheduler at the top level, a child spawned with a borrow of its spawner's lend is not
expressible at `erwp`: the spawn is a stop of the lending task, and `erwp`'s frame rules fold the
borrow back at every stop (`ILendOK.pa`, `LendOK.pa`: the payload in `Res_A`). No pool-level fact
can help, since the refusal is at the stop, before any scheduler runs.

**The restriction** is Core's: an operation a borrowed callback performs outside the callback
carries a payload free of the borrow's lifetime (`Row.Suspend`, `Core/TreeGoal791.lean`, decidable
on the row; `ILendOK.pa`/`LendOK.pa` at the tables). A child that holds the borrow is spawned into a
scheduler handled inside the callback.

### The cases under the restriction: proved

`Core/Chain/PoolScopeN.lean`, `Core/Chain/Cross821N.lean`.

- `TJV`: `TJN` with the spawn's payload any resource the child is verified from (`spawnPAV`,
  `ChildOKV`). `hs_schedOKV`: the same scheduler code `HS` meets `SchedOKN` at `TJV`
  (`PoolSpawnN`'s clause proofs; the spawn clause runs its child from the payload's resource beside
  the pool).
- `erwp_scopeV`: `(hnd HS e) (HS, [])` inside a task, from the empty pool, never stops outside and
  answers a value owning nothing (`poolAnsN_run_le` at the empty pool and the empty table). The
  scope returns only when its list is empty: that is the join.
- The programs, each `rootU cb = let c = alloc () in let (c′, _) = withborU dB c cb in free c′`:
  - `cbI b = λ_. λr. (hnd HS (spawn (λ_. park (); !r); !r; t_b; ())) (HS, [])`,
    `t_false = park ()`, `t_true = cancel ()`;
  - `cbM b = λ_. λr. (hnd HS (spawn (λ_. park (); r := 7; forget r); t_b; ())) (HS, [])`.

  Under `HS` the child runs first, its `park` resumes the spawner with the child beneath, so: in
  `cbI`, the spawner reads `!r` while the child is parked holding its copy; then the spawner's
  `park` resumes the child (it reads and ends) or its `cancel` cancels it while it holds the copy.
  In `cbM`, the child is parked holding the borrow while the spawner runs; the spawner's `park`
  resumes it and it writes through the borrow, or its `cancel` cancels it.
- The lend is one segment of the root task: `erwp_I_frame` (`lendI_ok`) and `erwp_M_frame`
  (`lendM_ok`) at the empty table, the callback's scope never stopping outside;
  `withborU`'s finaliser frame by `erwp_ubindClaim` at the empty table (no stop, so no claim:
  `R = ⊥`); the root lifted to `TJN` (`erwp_ofEmpty`).

| headline | statement | hypotheses | axioms |
|---|---|---|---|
| `crossImm` | `OrDiverges ((hnd HS (rootI false)) (HS, []))` | none | propext, Classical.choice, Quot.sound |
| `crossImmC` | `OrDiverges ((hnd HS (rootI true)) (HS, []))` | none | same |
| `crossMut` | `OrDiverges ((hnd HS (rootM false)) (HS, []))` | none | same |
| `crossMutC` | `OrDiverges ((hnd HS (rootM true)) (HS, []))` | none | same |

All four go through `poolSchedAdequacyN` (`progOfN_orDiverges`). No premise is added to any Frame
or rule.

## Departures

- The child is spawned into a scheduler scope inside the lend's callback, not into the top-level
  pool. Forced: `not_crossTaskILend`, `not_crossTaskMLend`, `erwp_refuses_borrowOut`. The top-level
  `HS` sees one task, which never stops.
- No explicit `join` operation: `HS` has none (its `par` has no entry in the chain tables); the
  scope's return, reached only at the empty list, is the join.
- The `mut` lender gets its cell back at every content the family admits (`MFPost`), as in #820;
  the written value is not read back.

## What is left

- A child in the top-level pool holding a borrow of a lend of a stored task. Not expressible at
  `erwp` (above). Core's Capture layer (`SI/Capture.lean`, `cerwp`, `cerwp_scope` with the join's
  frame condition `joinFd`) states lends left open across stops; it has no deep-handler rule at
  `cerwp` (only `cerwp_gen`, one handled run at a time) and no pool adequacy. Building
  `PoolSchedAdequacyC` over `cerwp`, with `HS`'s clauses proving `joinFd` at the joiner's resume,
  is the route; not started.
- `HS`'s `par` at the chain tables.

## The outer pool: `PoolSchedAdequacyC`

`Core/Chain/PoolC.lean`, `Core/Chain/PoolJoinC.lean`, `Core/Chain/Cross821C.lean`.

### The general theorem

- `cerwp_schedHandle_le`: `[handle]` for a scheduler at `cerwp` (`cerwp_gen`'s cases, by induction
  on the index), each clause given the stopped task's continuation as `KapRelC`: resumed under the
  stopped run's frame condition with the entry's `fd`, owning the records the stop owned; cancelled
  (D15, `κ (inj₂ ())`) through the entry's cancel obligation `PcanC`.
- `PoolSchedAdequacyC` / `poolSchedAdequacyC`: `PoolSchedAdequacyN`'s structure over `cerwp`. A
  stored task records its frame condition, records and payload (`StoredC`); the pool is the
  separating conjunction of their shares (`PoolC`); the scheduler keeps a **bag** of what ended
  tasks hold (no garbage at `cerwp`); its invariant `Inv` is read at the running task's frame
  condition. Moves: `poolAnsC_run_le`, `_park`, `_resume` (part of the bag as the answer's
  resource, the frame condition proved of the rest of the pool and bag), `_cancel`, `_resumeSnd`,
  `_cancelSnd`. The program's answers own no record and hold only `imm` cells (`cerwp_adequacy`).

### The scheduler `HJ`

`parkC` (cancellable), `spawn`, `cancel`, `join ℓ` (`joinEnt`), `parkL` (must-resume). A task's end
puts what it holds (`QinJ`: copies, `ViewsC`) in the bag. `join ℓ` with the pool empty resumes the
joiner with the bag's copies of `ℓ` (`ViewsC.split`), the rest of the bag flattening to nothing at
`ℓ` (`ViewsC.flat_none`): `joinFd`. `hj_schedOKC`: `HJ` meets `SchedOKC` at `TJC` for every task at
that table; `progOfC_orDiverges` closes any root through `poolSchedAdequacyC`.

### Case 1: proved

| headline | statement | hypotheses | axioms |
|---|---|---|---|
| `crossImmJ` | `OrDiverges ((hnd HJ (rootI false)) (HJ, []))` | none | propext, Classical.choice, Quot.sound |
| `crossImmJC` | `OrDiverges ((hnd HJ (rootI true)) (HJ, []))` | none | same |

`rootI b = let c = alloc () in (spawn (λ_. parkC (); !c); !c; tail; ()); join c; free c`, `tail`
`parkL ()` or `cancel ()`. The child is spawned into the top-level pool with a copy of the borrow;
the root reads `!c` while the child is parked holding its copy; the root suspends to the scheduler
(`parkL`/`cancel`) with the lend open (its record and copy in its stored continuation); the child
is resumed and ends, or is cancelled, its copy going to the bag; `join c` returns it; the lend ends
in that segment (`cerwp_scope`); `c` is freed.

### Restrictions

Kept from `CaptureScope`: the lent cell's payload empty; the borrowed run's operations must-resume
with empty answers (the scope's body is at `tabInN`, the lend's stops at the must-resume part
`tabLinC`); the body at `erwp0`.

New, of `HJ` (the general theorem has none of them):

- **`join` is a barrier**: it resumes only with no other task stored, else diverges.
- **After a join the program is one task**: the join pushes a marker; `spawn` above it diverges.
  Reason: `contShareC` resumes a continuation under its run's frame condition and its entry's
  `fd`, so a task resumed from `join ℓ` carries `joinFd ℓ` at every later resume; a stored share is
  opaque to the scheduler, so it can establish `joinFd ℓ` only when no other task holds a share.
  I have not verified in Lean that this is forced (only that `HJ` meets its obligations with it).
- Tasks end holding copies only (`QinJ`).

### Case 2 (`mut`): not derived

Not derived, no obstruction verified. What is missing: `joinEntM`'s answer is the `mut` cell at the
joined location. A child's answer at a fixed table says only that it holds some resource; nothing
in `KapRelC`, in a task's answer, or in the scheduler's code (which cannot compare locations) ties
a `mut` cell a child leaves to the joiner that lent it, so the scheduler cannot prove the joiner's
answer; and a `mut` cell left in the bag at the program's end would fail the `AllImm` answer.
Routes, not built: per-task answers delivered to a waiting spawner (fork-join, as the tree track's
`PoolTJ` for copies), or a resource the lender holds that names the loan.

Gate: `gate-serial.sh gate`, ALL PASSED (`~/repos/scratch-archive/cross821/gate2.log`).

## Join by task handle: not derived

Target: `spawn` answers a handle; `join h` waits for that child and answers its result, the
borrows it held; finished answers kept per handle until joined; no barrier. Headlines
`crossImmJ`/`crossImmJC` re-proved and `crossMutJ`/`crossMutJC` on such a scheduler.

**Not derived.** No scheduler was built; no headline changed. `crossImmJ`, `crossImmJC` stand on
`HJ` as above. `crossMutJ`, `crossMutJC`: not derived, no obstruction to the design verified.

### Obstructions at the relation (`Core/Chain/Cross821Obs.lean`)

These are facts about `cerwp`, not about handles. Each holds of every scheduler meeting
`SchedOKCLe`.

- **`crwpG`'s `EndC` (`SI/Capture.lean:57`) has no `↭`.** A run may stop or end holding a copy of
  any `imm` cell its frame holds (the world is unchanged, 6.116). Every scheduler's clauses accept
  such a share (`kapRelC_end`, `hj_joinerEntry`). `joinFd ℓ` fails at every valid frame holding a
  cell at `ℓ` (`not_joinFd_of_holds`). So an `imm` lend's join cannot be resumed while any
  continuation that ran during the lend is stored, whether or not the joiner has joined every
  child it lent to. Per-handle answers return the children's copies but do not remove copies held
  elsewhere. Two such joiners, each stored beside a copy of the other's lend, can be resumed in
  neither order (`hj_joinersDeadlock₀`). Core's `rwpG` (`SI/RwpG.lean:49`) asks `ρ ↭ π` at every
  end, which refuses a copy the run did not start with, so it would rule this out. But `rwpG` also
  refuses a stop whose payload holds the borrow (`not_crossTaskILend`), so the cross-task case
  cannot be stated at `erwp` at all.
- **`contShareC` (`SI/CaptureE.lean:69`) resumes at `F ρf ∧ en.fd v ρf`.** Frame conditions
  accumulate. A task resumed from `join ℓ` is owed `joinFd ℓ` at every later resume
  (`fdAnd_joinFd`). The return clause accepts tasks ending with a copy at `ℓ` (`hj_qin_copy`), and
  a frame holding one falsifies that condition (`hj_joined_blocked`). This is why `HJ`'s joined
  task runs alone. A resume at `en.fd v ρf` alone would remove it. No proof in `SI/` reads `F`
  past the segment after a stop (`cerwp_scopeK` reads only `joinFd`), but I have not checked that
  the change goes through.

### Not derived for the handle design, no obstruction verified

- **Handle to answer.** The scheduler's code must reach a child's answer from the handle value the
  program passes to `join`. The language has no equality on locations, and a search over stored
  answers needs a loop in the scheduler's code (none of `count`, `boundedFix`, `iterate` has a
  `cerwp` rule). The alternative is a handle the scheduler dereferences: a cell it owns. A forged
  or stale handle would then be loaded without a resource. `join`'s `PA` can ask only for a
  resource the joiner holds, and `WRes` has no unforgeable token. Missing: a per-handle resource
  the joiner hands back (ghost state, or a typed handle), or a lookup with a `cerwp` rule.
- **Cancelled `mut` child.** A cancelled task's leftover is answered at the entry's fixed
  `fin = PcanC Qc`. `OpEntN.fin` does not read the payload, and the cancel run's value is `()`
  (`Head.cancel`), so neither ties the leftover's `mut` cell to the lender's location. This
  affects `crossMutJC` with the borrow in the child's share across a cancellable park. Routes, not
  built: the borrow handed to the scheduler in the park's payload (payload-dependent `PA`/`PBv`), or
  a table indexed by the location (as `CrossProgM`, `TCM l`), which needs the cell allocated before
  the scheduler.
- **`mut` without these.** A `mut` join has `fd = True` (`joinEntM`) and a `mut` cell cannot be
  copied, so neither obstruction above applies to `mut`. A `mut` join by handle is blocked only by
  the handle-to-answer gap.

### Restrictions

`CaptureScope`'s are kept (empty lent-cell payload; must-resume, empty-answer body operations;
`erwp0`). A handle join inside an `imm` scope's body would have a non-empty answer, which
`ScopeTabs.inner` refuses.
