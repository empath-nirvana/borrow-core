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
