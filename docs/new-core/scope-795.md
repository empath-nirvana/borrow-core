# Scope: borrows shared across tasks and returned at join (#795)

Part of #771. SPEC §62. Builds on the scheduler interface of `Core/TreePoolSched.lean`
(`PoolAns`, `SchedOKT`, `PoolSchedAdequacyT`) and the shape of the stack-pool interface
(`PoolTJ`/`PoolAnsJAt`) checked on the `join-spike` branch.

## 1. Target

The scheduler interface on the stack-pool shape: the invariant covers the running task and the
pool, each entry's `imm` cells only at its own masks or where its nearest joiner shares. Over it:

- `poolSchedAdequacyT` re-proved at the new interface;
- spawn at any depth;
- join returns a child's view copies to the lender, for any number of children and any nesting;
- a theorem through the general headline: a parent lends to several children, interleaved,
  possibly cancelled, and ends the lend after joining them, at depth 1 and depth 3.

No statement fixes a number of children, a depth or a scheduler shape. No hypothesis stands in
for an unproved fact.

## 2. Order and criteria (set before the result)

1. **Merged copies.** Children's copies of a lend cell compose to `ℓ ↦ imm(S, (), ∅)`, `S` the
   union of their lifetime sets; `twp_lendEnd` asks for `viewRes α ℓ`.
   - (B), first: every view at the location of a record proper carries that record's frame
     lifetime, so `S = {α}`. Changes no statement.
   - (A): `twp_lendEnd` at `imm(S)`. A statement change: propose it, stop, report.
   - Outcome (a) a route proved: items 2–4. (b) both fail, each failure a Lean configuration
     with every hypothesis discharged: build a decidable fence on types or the frame condition,
     proved non-vacuous, covering the target shapes. (c) undetermined: report the step, stop.
2. **No new unknowns without evidence**: a new open question is stated as an elaborating
   `def … : Prop` or a configuration, and work stops.
3. **Items 2–4**: a second, unstarted child (`KapSchedT` at a synthesized continuation, or a
   `fork` operation); the park clause without the swap; depth 2 (children that spawn, with the
   step-indexed table); the moves re-proved, cancel and swap included; the example scheduler and
   its programs. The new per-task obligation (`imm` cells only at own masks or shared locations)
   discharged for `L` and `LC`.

Only the scheduler interface's statements change (`PoolAns`/`SchedOKT`/`PoolSchedAdequacyT` →
the J forms), plus route A's with the user's OK. `twp`'s rules are unchanged.

## 3. Hardest case

Depth 3 with cancellation: a task three spawns deep holding a copy of a lend opened at the root,
siblings interleaved, one cancelled, the lender ending the lend only after every join.

## 4. NOT-do

- Fixed child counts or depths in any statement.
- Test-shaped headlines (a theorem about one program standing in for the general one).
- Routing around the invariant: no hypothesis that assumes the join's hand-back, no
  per-program apartness premises, no restriction back to two-way apartness.
- Importing `experiments/`.

## 5. State

**Item 1: outcome (a), route B.** `Core/TreeLendJoin.lean`: `frameLife_of_tagged` (a tagged record
proper's frame is at its tag, `TaggedT` with `not_desc_proper`), `proper_view_single` (every cell
at its location has lifetime set `{α}`, `view_at_lender`), `twp_lendEnd_imm` (end a lend at
`imm(S, (), ∅)`, the list carrying the lend's record; `S = {α}` at every start world, then
`twp_lendEnd` unchanged). No statement changed.

**Items 2–4: built.**

| Piece | Where |
|---|---|
| the stack (`PoolTJ`, with each joiner's collected copies), `twp_frame_keep_sh`, `HoldsIn`/`twp_holdsIn`, `ViewsT`, `twp_keepsPoolJ`, `poolTJ_resume`, `poolTJ_cancel`, `PoolTJ.swap`, `PoolTJ.deposit` | `Core/TreePoolShare.lean` |
| the interface (`PoolAnsAt`/`PoolAns`/`GoodT` over `PoolTJ` and the running task), the moves (park as ready or joiner, resume, resume-second, cancel, cancel-second, deposit-and-resume, run), `poolSchedAdequacyT` | `Core/TreePoolSched.lean` |
| the stack scheduler and its return clause (deposit, then resume the top) | `Core/TreePoolSchedProgs.lean` |
| `HS` with `park`, `spawn`, `cancel`, `par`; indexed tables `tabAt`; the unstarted child `κU` | `Core/TreePoolSpawn.lean` |
| the loan, cancel and depth-3 tests | `Core/TreePoolSpawnProgs.lean` |
| a lend shared by a tree of tasks at every depth, ended after the join (`progJoin_safe`, `progJoin_depth1`, `progJoin_depth3`) | `Core/TreePoolJoinProgs.lean` |

**Second child.** A continuation the `par` clause builds (`κU H th`), proved a stored task
(`kapSchedT_κU`), not a `fork` operation: it needs no new kernel primitive.

**The per-task obligation** (`imm` cells only at own masks or where the nearest joiner shares) is
carried by every run (`twp_holdsIn`), so no task proves it: a task starts with it (the root and a
spawned child hold nothing; a `par` child holds copies at what its parent shares) and every run
keeps it. `L` and `LC` meet it with no change to their proofs.

**Over #806's `EndT`.** `tree-795` is merged with `tree-core` after #806, whose `EndT` reads `↭`
along the walks (`UpdA`) and row 5.27's `mut` clause by `InvKeptA`. No #795 statement changed.
Two proofs read `EndT`'s clauses:
- `twp_frame_keep_sh` takes `twp_frame_keep`'s new steps: `UpdA.frame` (with `MutOne` at both
  ends), `UpdA.widen` at `recMaskClosed`, `InvKeptA.frame`, and `fdEsc_of_updA` for the framed
  records not at `S`.
- `twp_holdsIn` reads `UpdA`'s end clause. An end `imm` cell outside the end's masks is kept from
  a start `imm` cell (`XCell`) or absorbed by one (`CellSub`); the third disjunct, a cell from
  beneath a start ancestor, is a `mut` cell, which `HoldsIn` does not read. The `imm` cell
  absorbed by the end world is a start-side disjunct, which `HoldsIn` does not read either. So
  `UpdA` forced no new case.
