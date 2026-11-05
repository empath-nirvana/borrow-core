# Scope: #791 over the chain relation per task, plus the pool

Branch `chain-791`, from `origin/tree-core` (35fc7c0e).

## Target

`OrDiverges` for #791's hardest case, proved over Core's step-indexed chain relation per task
(`erwp`, `cerwp`, the Mut Frame and Anti-Frame across stops), with tasks related by the pool
invariant (`PoolTJ`'s design, #817):

- a task holds a `mut` reborrow of a boxed field of its borrowed record, two levels deep, across
  a `park`;
- another task opens and ends its own lend meanwhile;
- the first task is resumed, and everything ends with memory empty;
- separately, the same with the parked task cancelled.

The new constants of `goal-791` (`Row.Suspend`, the field reborrow) are data. No new judgment.

## Kill criteria (fixed in advance)

- **A.** A needed chain theorem does not exist, has a `sorry` or axiom, or proves less than
  claimed: stop, and name it and what it would take.
- **B.** The graft scenario (a task opens a lend `α` and suspends; the handler opens its own lend
  `β` and resumes the continuation inside `β`) is not provable as a program over the chain
  relation: build the reachable configuration where the chain relation fails, and stop.
- **C.** A build step fails: stop with the configuration and the exact step. No added hypotheses,
  no fences without the user's approval; conditions are accepted only as decidable conditions on
  types or rules.
- Anything unexpected is stated as an elaborating `def … : Prop` and reported, not explored.

## Status

**Step 1 (the chain pieces): verified, no kill.** Built on `tree-inv` (92b6cc49) and `forest`
(2a264e68); every theorem's axioms are `[propext, Classical.choice, Quot.sound]`.

- Must-resume only (`q = .lin`): `erwp_M_frame` (`LendOK`), `erwp_withbor3` (`LendOK`, `AFOK`),
  `erwp_reborrow` (`RebOK`).
- Cancellable stops admitted: `erwp_M_frameC` (`LendOKC`; the lender's stops at `claimT`, its
  cancel runs ending at the lend's claim), `erwp_M_frameTF` (the same, its stops guarded by the
  fold), `erwp_M_antiFrameC` (the claim of a lend inside consumed, the cell sealed at the cancel's
  `raise`), `erwp_reborrowT`.
- No `erwp_withbor3C`. The field reborrow across a cancellable stop is the composite
  `erwp_M_antiFrameC` ∘ `erwpG_frameT` ∘ `erwp_M_frameTF`, which `AntiCancelProg.openC_ok`
  already proves for a program.
- `KapRelN`'s cancel entry is D15's: `κ.1 (inj₂ ())`, the continuation's cancel branch, whose body
  is Core's abortive `raise` of `cancelVal`. The chain proofs use Core's claim at that `raise`
  (`claimR`), so cancel is resume into the cancel branch, accounted by Core's claim.

**Step 2 (the graft scenario as a program): proved, no kill.**
- `forest`: `ForestHandlerProg.progH_orDiverges`, via `ExtK`.
- Here, at `extF` (which subsumes `ExtK`: a resumer that adds records keeps every relevant
  record): `HandlerLendProg.progHL_orDiverges` and `HandlerLendAll.anti_underL`, the latter with
  the task holding a `mut` reborrow of a boxed field of its borrowed value across `y`.

**Step 3, done:**
- `Core/Chain/SI/*` lifted from `tree-inv` (84 modules), building against `tree-core`'s Core
  unchanged.
- The per-task halves of the hardest case, as single-task programs:
  - `AntiLendProg.progAnti_orDiverges` (resumed);
  - `AntiCancelProg.progAntiCancel_orDiverges` (cancelled).

## Next steps, in order

1. **The chain scheduler** (`Core/Chain/Pool*.lean`). Port `TreePoolSched`/`TreePoolSpawn`
   (`SchedOKT`, `PoolAns`, `poolSchedAdequacyT`) to `erwp` as `SchedOKN`, `PoolAnsN`,
   `poolSchedAdequacyN`:
   - a stored entry is a `KapRelN` share at its own stop list, resumed at `extF`;
   - the pool is the separating conjunction (`ResU.CompS`) of the entries' shares. `PoolTJ`'s
     masks, `AvoidUnsh`, `HoldsIn` and `RecsApart` are the tree's form of that separation;
   - the table carries `park`, `spawn` and `cancel` only. `rootMut`/`rootMutC` do not perform
     `par`, and `erwp_handle` checks clauses only at the table's entries.
2. **Task A with the `goal-791` constants.**
   - `withborUE`: `erwp_M_frameC` around `f [] r`, with the `then … unwind d r` frame by
     `erwp_ubindClaim`.
   - `withborFE`: `load r`, then `AntiLendProg.open_ok` (resumed) or
     `AntiCancelProg.openC_ok` (cancelled), with the field's lend at the callback `cbField`.
   - `dRec` consumes `c`'s claim, as `AntiCancelProg.Dc_ok`.
3. **`thL`, `thC` at `erwp`**, from `TreePoolSpawnProgs`' `L` and `Cbody`.
4. **`rootMut`, `rootMutC` at the chain table**, then `HardestCase791`/`HardestCase791C`
   (`Core/TreeGoal791.lean`; the statements are about `progOf`, so they do not depend on the
   relation) through `poolSchedAdequacyN`.

**Not yet done:** an audit of the lifted files' prose for history (stage numbers, round numbers,
spike numbers).
