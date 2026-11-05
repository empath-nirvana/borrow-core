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

## Done: the four steps

1. **The chain scheduler** (`Core/Chain/PoolN.lean`): `StoredN`, `PoolN` (the separating
   conjunction of the stored continuations' `KapRelN` shares, each with its entry's world condition
   at every list with the current list's members), `PoolAnsN`, `GoodN`, `SchedOKNLe`/`SchedOKN`
   (the premises of `erwp_handle_le` at the empty outer table, each cancel run at the scheduler's
   own table), the moves (`poolAnsN_run_le`, `poolAnsN_park`, `poolAnsN_resume`,
   `poolAnsN_cancel`, `PoolN.swap`, `PoolN.perm`, `poolAnsN_resumeSnd`, `poolAnsN_cancelSnd`), and
   `poolSchedAdequacyN`. General: any table, any scheduler meeting `SchedOKN`, any invariant of its
   list, no fixed task count or order. `erwp_handle_le` (`SI/HandleN.lean`) is `erwp_handle` with its
   clauses asked at the stops up to `N`; `erwp_handle` is its corollary.
   `HS` at the chain table `TJN` (`Core/Chain/PoolSpawnN.lean`): park, spawn and cancel entries,
   children's tables indexed (`tabAtN`), `hs_schedOKN`, `progOfN_orDiverges`. `HS`'s `par` clause
   has no entry in `TJN`.
2. **Task A** (`Core/Chain/Hardest791N.lean`, `taskA_ok`): `withborU dRec` is `erwp_M_frameT` +
   `claimT_canS` (the record's claim at the cancel's `raise`) under `erwp_ubindClaim` (`dRec`
   consumes the claim, `dRec_ok`); `withborF dFwd` is the anti-frame (`erwp_M_antiFrameC`) around
   `cbField () (!c)` (`openF_ok`: `load`, then the field's lend by `erwp_M_frameTF` with the opened
   cell framed by `erwpG_frameT`), and the field's finaliser frame `then … unwind dFwd c` outside
   the anti-frame by `erwp_ubind` (`cancelOblN_ubind`, the finaliser holding nothing).
3. **`thL`, `thC`** at every indexed table (`thL_ok`: the cell lent `mut` across `park` by
   `erwp_M_frameT`, inside `L`'s finaliser frame by `erwp_ubindClaim`; `thC_ok`).
4. **The roots** (`rootMut_ok`, `rootMutC_ok`) and `hardestCase791`, `hardestCase791C` through
   `poolSchedAdequacyN`. Axioms `[propext, Classical.choice, Quot.sound]`.

Departures from the plan above, none a kill:
- Task A's proof is the same for both roots, and uses the cancellable-stop pieces in both: every
  entry of `TJN` is cancellable, so a stop owes a cancel run whether or not it is taken.
  `AntiLendProg.open_ok` (must-resume) is not used.
- `withborF`'s finaliser frame is not in the plan; it sits outside the anti-frame, at the plain
  table, where `erwp_ubind` applies.
- `TJN`'s cancel obligations are cancel runs at the empty table: a cancelled task's unwinding
  performs no operation. `SchedOKN` itself allows any cancel table inside the scheduler's.
- A task's and the program's answer `QVN` is a value owning nothing (the value is not `()`: the
  field's content after its lend is not tracked).
