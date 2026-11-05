# Scope: threads with parallel adequacy (stretch goal on #771)

Branch `threads-scope`, at 4d0d9d6f (the `cross-821` scope, `docs/new-core/scope-821-loans.md`).
This is a design document. No Lean is added with it and none was elaborated for it: the Lean-like
statements below are unchecked sketches.

## Verdict

**YES, with one condition.** A route exists, at about 6.3k lines. The condition is that the
relation's run clause gains an **access guard**: every step of a run keeps the frame's cells. That
change touches the run-level modules, about fifteen of them, not every rule. #821 stage 2 must
respect the six constraints in §8 so that the guard and the machine can be added later without
re-proving stage 2.

Without the guard, parallel adequacy at the semantic relation is **not derived. The obstruction
is at `rwpG`'s run clause** (`Core/Chain/SI/RwpG.lean`), through the undone write in §2.3.

**Correction to the premise in #771's comment.** `erwp` does not quantify over a frame at every
step. `rwpG` fixes the frame at the start of a **segment** (a run from a resumption to the next
stop) and then quantifies over every *solitary* run of the term from that memory. A step taken by
another thread is therefore not one of the frames `erwp` quantifies over. A reduction theorem
(§2) is what makes it one.

---

## Design summary

The machine is a pool of threads over one heap. Any thread may take a `Step1` at any time.
`spawn`, `join`, `park` and `cancel` are operations that no handler inside the thread catches.
The machine is their outermost handler, as route I (#212) has it for platform effects: a thread
stopped at one of them is `Final` for `Step1` (`final_opPlug`), and the machine resolves the stop.
Each thread is proved at `erwpX` against **the same task table** (spawn/park/join/cancel) that
stage 2's in-language scheduler `HH` is proved against. So one task derivation runs under either
runtime.

Adequacy goes in two steps:

1. **Serialisation.** The guard and the locality of `Step1` make the steps of two threads that
   hold disjoint resources commute. Every interleaved run can therefore be reordered into one in
   which each thread's segment runs contiguously, ending at its stop. This is Lipton's reduction
   with a per-segment footprint.
2. **Pool adequacy.** On serialised runs, the argument is stage 2's: a pool invariant (`PoolS`,
   `TokPost`, the registry) over thread states, preserved at each segment's end by that thread's
   `erwpX` conclusion instantiated at the *current* frame, and at each machine transition by the
   table's `PA`/`PB`.

`↭`, `TWNC`/`TWNX` and the index are stable because every segment's conclusion is read at the
frame that holds when it ends, as in the cooperative pool. The memory model is sequential
consistency through data-race freedom: the guard plus disjointness is data-race freedom for every
interleaving (§5).

---

## 1. The machine

**Definitions** (module `Par/Machine`):

```
structure PCfg where
  μ    : Heap
  ths  : List (Option Expr)   -- thread a; `none` once joined
  used : Set Loc              -- every location ever allocated

inductive PStep : PCfg → PCfg → Prop
  | run  : ths[a] = some e → Step1 μ e μ' e' → AllocFresh used μ μ' → …        -- any thread
  | spawn: ths[a] = some (K.plug (performE (spawnP f))) → K.HasHnd spawn = false →
           ths' = (ths.set a (K.plug (handle b))) ++ [some (app f unit)]        -- b fresh index
  | join : ths[a] = some (K.plug (performE (joinP b))) → ths[b] = some (val w) →
           ths' = (ths.set a (K.plug w)).set b none
  | park : ths[a] = some (K.plug (performE parkP)) → ths' = ths.set a (K.plug unit)
```

- **A join whose target has not finished has no step.** A deadlock is therefore a stuck
  configuration, not a divergence, so `OrDivergesPar` (below) proves deadlock freedom, as stage 2's
  stuck empty-ready branch does.
- **Cancel** is a machine transition on a target **stopped** at one of its stops. It runs the
  entry's `fin` branch as the target thread. A cancel of a target that is mid-segment waits until
  the target stops (§7, item (d)).
- **`AllocFresh`**: an allocation picks a location outside `used`, so no location is reused across
  threads. This is the one place the machine departs from `Head.alloc` (any `μ ℓ = none`). Every
  `run` step is still a `Step1` step. The weaker variant, where a thread may reuse the locations
  it freed itself, also serialises; it is open which to take (§10).
- **`OrDivergesPar P`**: every configuration reached from `⟨∅, [some P], ∅⟩` satisfies one of
  three things. Some `PStep` applies. Or thread `0` is a value, every other thread is `none`, and
  `μ = ∅`. Every `free` finds its cell.

**Relation to today's machine.**
- A pool with one thread that never spawns is `Steps`, up to `AllocFresh`.
- `OrDivergesPar` at one thread implies `OrDiverges` for the runs that never reuse a freed
  location. The full single-thread `OrDiverges` stays `erwpX_adequacy`'s.

**The cooperative pool is not an instance; it is a separate theorem with a shared invariant.**
- `PoolN`, `PoolSpawnN` and stage 2's `HH` are one closed expression `(hnd H e₀) s₀` stepping in
  `Step1`. The tasks are continuations stored in the scheduler's state.
- The parallel machine has no scheduler expression: its thread states are machine data.
- A serialised parallel run does not simulate `HH`, because `HH` fixes an order (its ready list)
  and the machine picks any.
- What is shared is the per-task layer: the table, the `erwpX` derivations of tasks, and the
  invariant (`PoolS`, `TokPost`, registry, `PBv`). Two adequacy theorems are built on it:
  `poolSchedAdequacyS` (stage 2) and `parAdequacy` (here).

## 2. Why per-segment frames are enough, given a guard

### 2.1 What `erwp` quantifies over

`rwpG Φ Q n ls e ρ` quantifies over:
- a frame `ρf` with `fρ = ρf ● ρ`, `TWNC fρ ps (rsOf ls)`, `Tagged`, `Lower fρ μ`;
- then every `StepsN j μ e μ' e'` (`j < n`) of `e` **alone**, and asks `EndOKG` at a `Final`
  configuration.

The steps in between carry no condition: no world, no `↭`, no frame. This is deliberate. The
docstring of `SI/WpN.lean` says the 6.66 anti-frame "keeps the printed proof's shape: nothing in
between is asked to be a `↭`-image of the start". The frame is quantified again only when a
continuation is resumed after a stop (`erwpC`, `contShareN`). So frames are **per segment**.

`SI/Ewp.lean`'s `ewp` is per step. It is LinearActris's `WP₀` at one thread: "every step keeps
the frame", that is, `μ' = σ' ⊎ σf`. But it is over plain heap fragments, with no `↭`, `TWNC` or
records.

### 2.2 What must hold when other threads step in between

Suppose thread A runs a segment from its world piece `ρ_A` while B steps. Three things must hold.

- **(S1) The index.** A's index counts A's own steps only. *Stable*: interleaving does not change
  how many steps A takes.
- **(S2) `↭` at A's end.** `UpdVN Φ k ρ_A π_A` (stage 1: `UpdVNm` at a mask) relates A's start and
  end pieces. *Stable*: it mentions no other piece.
- **(S3) The world condition at A's end.** `EndOKG` gives `TWNC (ρf_A ● ρ'_A ● ρp)` at **A's start
  frame** `ρf_A`. If B ended a segment in the meantime, B's pieces have changed, and that conjunct
  describes a world that no longer exists. *Not stable as stated.* Composing A's and B's
  conclusions directly would need a diamond lemma for `TWNC`: from `TWNC(X●A●B)`, `TWNC(X●A'●B)`
  and `TWNC(X●A●B')`, conclude `TWNC(X●A'●B')`. That is not derived. It is also unlikely to be
  cheap, because `TWNC` is a history (`immFrame`, `reb`, canonical images), and stage 2 lets
  records change at wholly-held lifetimes.

**Serialisation removes S3 instead of proving the diamond.** Move every step of A's segment to
just before A's stop. A's segment then runs contiguously, from the memory and world that hold at
that point.
- A's piece is still `ρ_A`, because nobody else touched it.
- The rest of the world is the current frame, which composes with `ρ_A` by the pool invariant.
- `erwpX` quantifies over every frame, so A's derivation applies at that frame. S3 is then exactly
  the cooperative case.

Serialisation needs three facts:

- **(G) the guard.** Every step of a run from `ρ`, under frame `ρf`:
  - writes or frees only locations outside `dom ⦇ρf⦈`;
  - reads only locations outside the part of `⦇ρf⦈` that the frame holds exclusively.

  Fresh locations are outside both.
- **(L) locality of `Step1`.** A step that accesses only the locations in a set `F` is also a step,
  with the same result, from any memory that agrees on `F`, provided its allocation is free there.
  This is a lemma about `Head`'s rules and `Kont.plug`.
- **(N) no reuse across threads** (`AllocFresh`). Without it, "A frees ℓ, B allocates ℓ; B frees
  ℓ′, A allocates ℓ′" has no serialisation. Repairing that needs renaming equivariance of `Step1`
  over block renamings, which is #212's B4 and is not derived for `tab`.

From G, L and N:
- A's accesses are in `dom ⦇ρ_A⦈` together with A's fresh locations, and its writes are in `A`'s
  exclusive part together with A's fresh locations.
- At any moment before A's stop, the pool invariant makes `ρ_A` compose with every other thread's
  piece.
- So a write by one thread never meets an access by the other. Adjacent steps of different threads
  commute.

**Does the loan design give G?** Partly, and the remainder costs a retrofit.
- Stage 2's `mut` loan moves the cell to the borrower, and the lender keeps only `xm`. G forbids
  the lender's run from touching that cell, because it is in the frame.
- Stage 1's mask (`UpdVNm` reads `↭` only outside `M`) says nothing about the steps of the run. G
  is what makes that mask safe in parallel.
- The token design keeps `imm` cells shared by copy. G permits reads of them and forbids writes.
- Neither stage puts G into the definition: `rwpG`'s steps are unconstrained.

### 2.3 Why G is needed: the undone write

```
def UndoneImmWrite : Prop :=
  -- A holds a copy imm({α}, v, ∅) at ℓ; the frame holds another copy.
  rwp Φ (fun _ _ _ σ => σ = ρ_A) n ls
    (seq (store ℓ 0) (store ℓ v)) ρ_A
```

- `EndOK` reads only the end of the run, and the memory there equals the start's. So I expect
  `UndoneImmWrite` to hold at every `n`. This is #212's B1 at `rwp`. It is not machine-checked.
- If it holds, take a thread B that holds the other copy and runs `if load ℓ = v then () else
  stuck`. B is in `rwp` at every frame, because `imm`/`imm` composes only agreeing values.
- Interleave A's first store, then B's load. B is stuck.
- So `parAdequacy` stated over semantic threads, without G, would conclude `OrDivergesPar` of a
  stuck pool.

Typing does not rescue it. The pool's own scheduler code, the tables' clauses and future extern
contracts are semantic, not typed.

**G is the heap shadow of `ewp`'s step clause** ("every step keeps the frame"), now read at the
flattening ⦇·⦈ so that agreeing `imm` copies can be read by both sides. It is #212's U1 at segment
granularity, with one difference: `rwpG` quantifies universally over runs. G is then a conjunct
that every *structural* combinator passes on (bind: the continuation's frame `ρf ● ρ⁺` contains
`ρf`; frame: `ρf ● ρ₂` contains `ρf`). It is not a witness that every rule must construct, as
`wpTS`'s ∃-run was.

## 3. Shared ghost state

- **Lifetime tokens** compose by adding fractions. **Validity of the composed whole** keeps each
  sum ≤ 1. This is not disjointness: two threads may each hold `[α]_{q}`.
- **`xm`** is exclusive, which is disjointness.
- **The registry** is `Auth(Loc ⇀ Agree(Ret))`.
  - In the machine, `●` is held by the pool invariant, not by a thread or a heap cell.
  - `tok r` is held by the joiner and `wr r` by the child.
- **Can a thread's step invalidate another's ghost facts?**
  - Not at a step: ghost state changes only at segment ends. Stage 1's change 6 makes every ghost
    change frame-preserving, since the end composes with the same frame.
  - After serialisation, "the same frame" is the current composite, which includes every other
    thread's ghost piece. So B's `[α]_q`, `wr`, `tok` and `xm` survive A's segment end.
  - `C`, the set of counted lifetimes, is read from the world at each segment's frame quantifier.
    A mint by B between two of A's stops is seen at A's next segment.
  - This already happens in the cooperative pool, where other tasks run between a task's stops.
    So it is not new with preemption.
- **Machine transitions** (spawn, join, cancel) update `●`. Their preservation proofs are the
  machine's, from the table's `PA`/`PB`/`PBv` and `wr g = r` at the registry. This is the same
  content as `HH`'s clauses, without the slot cell.

## 4. Adequacy

**Statement.** `parAdequacy`: `P` is in `erwpX` at the task table `TJX`, at every index, from
`(∅, ∅)`, and its post owns nothing, ghost included. Then `OrDivergesPar P`.

**Invariant over serialised configurations** (`ParInv n`):
- The world is `W = (⊛ᵢ ρᵢ) ● g● ● ρ⁺`, where:
  - the `ρᵢ` are the threads' pieces;
  - `g●` is the registry authority;
  - `ρ⁺` is the garbage, which is `NoOwn`.
- The world satisfies `TWNX W ps (rsOf ls)` and `Tagged`, and `Lower W μ`.
- Each live thread is in one of four states:
  - **ready**: `erwpX Φ TJX Q k ls eᵢ ρᵢ`, with `k` above its remaining steps;
  - **stopped** at a `TJX` entry: its `PA` part and its `contShareN` (park and spawn resolved at
    once; join pending);
  - **done**: a value meeting its post, holding `wr`'s obligation for its registry entry;
  - **joined**: `none`, holding nothing.
- `TokPost` holds over the spawn tree.

**Proof shape.** Iris adequacy, from "Iris from the ground up" §6.

- That theorem uses `wptp` over the pool and a state interpretation re-established at every
  thread-pool step.
- We re-establish it at every segment end and machine transition, on serialised runs, and
  serialisation (§2) lifts the result to every run.
- LinearActris (POPL 2024, Thm 5.4) adds global progress from an acyclic connectivity graph, and
  leak freedom from linearity. Ours specialises both to the spawn tree, through `TokPost`, as
  stage 2 does following Jacobs–Balzer–Krebbers.

**Progress at a reached configuration.** Every mid-segment thread can step:
- its solitary projected run is safe, by `erwpX`;
- its next step accesses only its footprint, by G;
- so by L the step exists in the real memory.

Otherwise every thread is at a stop or finished, and four cases cover it:
- **park** and **spawn** always resolve.
- **join** resolves if its target is done.
- **The post-order-least unfinished thread is not blocked.** Its join targets come before it in
  post-order (`TokPost`), so they are done. This is stage 2's `not_mutualWait` argument.
- **Leak freedom.** Thread 0 is a value whose post owns nothing. Answers carry no tokens (stage 2),
  so every `tok` has been consumed, and every child has been joined. The world is then `ρ⁺`, which
  is `NoOwn`, so `μ = ∅`, as in `erwpX_adequacy`.

**Index.** Choose `n` greater than the length of the run observed. A spawned child gets its index
from the spawn entry's `PA`, as `ChildOKN`/`tabAtN` do in `PoolSpawnN`.

## 5. Memory model

**Confirmed, with what it rests on.** With synchronisation only through spawn, join and park (and
later one-shot or session channels), and no atomics, the interleaving machine is faithful under
the C/LLVM model. That is the DRF-SC guarantee:
- Adve and Hill, ISCA 1990: data-race-free programs appear sequentially consistent on weakly
  ordered hardware;
- Boehm and Adve, PLDI 2008: the C++ model gives SC semantics to programs without data races.

It rests on four things.
1. **Data-race freedom in the sense those theorems use**: no SC execution has two conflicting,
   unordered accesses. That is what G, the disjointness in `ParInv`, and N give for every
   interleaving of `PStep`. It is a corollary to state and prove (`parDRF`). It is not an extra
   assumption.
2. **Synchronisation compiled as synchronisation.** Spawn and join lower to operations the C model
   orders by happens-before, such as `pthread_create`/`join` or acquire/release on the join slot.
   This is a Backend2 obligation, trusted like every other lowering.
3. **The allocator.** N abstracts a thread-safe allocator whose reuse of freed memory is ordered
   by its own synchronisation. That refinement is trusted at the backend.
4. **Granularity is irrelevant under DRF.** A `Head` step that writes a multi-word value, or `tab`
   filling a block, need not be atomic in hardware, because nothing reads concurrently.

**What atomics or `Mutex` would add later** (#212 route I's "hole" capabilities):
- **SC atomics** as opaque capabilities: each operation is one machine transition on a location
  outside every thread's piece. Interleaving stays faithful, because DRF-SC covers programs whose
  only races are on SC atomics (Boehm–Adve).
- **Relaxed or acquire/release atomics** are not interleaving-faithful. They need a weak memory
  model (such as RC11, or Iris's iRC11 or Cosmo). That is outside this route.
- **A `Mutex`**: `lock` transfers the protected cell into the locker's piece and `unlock`
  transfers it back. That is resource transfer at a stop, the same shape as join. The cost is
  progress: lock cycles break `TokPost`. So `Mutex` needs a lock-order discipline, or a weaker
  adequacy statement in which a blocked lock is allowed to diverge.

## 6. What can be sent between threads

Sending happens at the spawn stop (the child thunk's resource goes in `PA`) and at join (`PBv`).
What crosses is whatever the resource algebra can split. With rule-level typing (#789), this is
derived from types.

- **Owned values and cells** move.
- **`imm` borrows** go as a copy plus a token fraction `[α]_q` (stage 2). `WF_C` forces the
  fraction to come with the copy.
- **`mut` borrows** go as the whole cell. The lender keeps `xm`.
- **Persistent values** hold ∅ and cross freely.
- **Closures** cross with their captured resource, under the same three rules. A closure that
  captures an `imm` copy at a counted lifetime carries a fraction.
- **Continuations** (`κ` cells) are owned cells with their share. They can move, which amounts to
  task migration.
- **Capabilities** that answer operations by call (`Mut` views, stateless `!` providers) move or
  are shared as above.

**What must not be sent, by the tables rather than by a type class:**
- **A thunk with outward control operations other than the machine's.** The child's table is
  `TJX`, so an uncaught `raise` or `await` in the child is a stop that the table does not allow.
  Errors cross only as data in the join answer, which is #212's L5(i′).
- **Handles in answers** (stage 2's NOT-do). Handles in a spawn payload are allowed exactly when
  `TokPost` is kept.
- **Segment-local, uncounted borrows** (`erwp_I_frame`). They fold at every stop, so they cannot
  reach a spawn payload.
- **Opaque host values.** `Imm̲ opq = Unk`, so whether they can be sent or shared is a field of
  their extern contract (route I).

**RustBelt's `Send`/`Sync`, read here.**
- In RustBelt, `Send` and `Sync` are semantic properties because type interpretations depend on
  the thread id, for `Rc`- and `Cell`-like types. Ours do not depend on it, and there is no
  interior mutability, so every model type is `Send`.
- Every `imm` view is `Sync` *because of G*: without G, the undone write makes `imm` not `Sync`.
- RustBelt's lifetime logic is used only for its fractional tokens, as in stage 2.

## 7. The cooperative pool and preemption

With preemption, any thread may be suspended at any `Step1`, not only at its stops. The
per-thread relation does not see it: serialisation moves every preempted step back into its
segment. What changes is the pool, which has many threads mid-segment at once, and the places
where the loan design reads `HH`'s code.

Places in `scope-821-loans.md` that assume a task switch happens only at `park` (or at a stop):

| | place | assumption | avoidable? |
|---|---|---|---|
| (a) | §2 "the lender holds its lifetime wholly in two segments" | segments are stop to stop | Holds unchanged. Preemption does not end a segment. |
| (b) | §3 the handle slot: a physical cell `a ↦ own(…)` owned by the scheduler; `join` loads `!a` and stores the waiter | the slot is touched by one thread, the scheduler | Yes. In the machine the slot is machine state, and the registry entry and `PBv` carry the meaning. An in-language *parallel* scheduler would share the slot between workers and need atomics (§5). So the slot must not be the semantic carrier of the handle (constraint C2). |
| (c) | §3 "otherwise … resume the next ready task" | one task runs at a time | Holds per serialised run. `PoolS` must not depend on "exactly one task is not stopped" (C3). |
| (d) | §4 "A child's park shows `wr g`"; cancel finds the child parked | a canceller runs only when the child is at a stop | Partly. The machine cancels at the target's next stop, and a target that finishes first is joined instead. Recorded as a cooperative fact of `HH`. |
| (e) | §5 "`HH`'s empty-ready branch is unreachable", written as a stuck term | scheduler-specific | Yes. The machine's analogue is "no `PStep` applies", refuted by the same `TokPost` argument. |
| (f) | §7 must-resume for a task holding `[α]_1` or `xm` with loans out | the scheduler must eventually resume it | A liveness obligation on `HH`. In the machine, threads are never left unresumed except at a pending join, so nothing is needed for safety. |
| (g) | Stage 1 change 1: frames and starts `WF_C` for "the world's `C`" | `C` is read at each segment start | Already per segment. Must stay so (C4). |
| (h) | `PoolN`'s entries are continuations stored in the scheduler's state value | tasks live in the scheduler's heap state | Yes, if `PoolS`'s entry is stated as `erwpX` at an expression, or as a stop with its `contShareN`, independent of `stateValN` (C3). |

## 8. Constraints for #821 stage 2

Short and exact. Each one keeps the threads route open without changing stage 2's done-when.

- **C1 (run-level confinement).** Only these unfold the run quantifier of `rwpG`/`erwpX` (the
  `intro ρf fρ ps μ … hrun` pattern):
  - stage 1's structural rules (`_le`, `_det`, `_val`, `_bind`, `_frame`);
  - the heap primitives (`SI/HeapN`);
  - a single reframing lemma, `erwpX_reframe`: the inner derivation instantiated at a frame `ρF`
    with `dom ⦇ρF⦈ ⊇ dom ⦇ρf⦈` and the exclusive part of `ρF` ⊇ that of `ρf`.

  Every other stage-2 rule (`TokLift`, `LendX`, `HandleX`, `PoolS`, `HH`) goes through these.
  Today's frame-changing rules (`IFrameN`, `IStopN`, `StopFrameN`, `AntiStopN`, `RebRuleN`,
  `RebStopC/D`, `MutSemN`, `HandleN`) each unfold it directly. Keeping new rules out of that list
  is what keeps the G retrofit at about fifteen modules.
- **C2 (the table is the interface).** The spawn/park/join/cancel table `TJX` (its entries' `PA`,
  `PB`, `PBv g`, `wc`, `fin`) is a fixed definition that names neither `HH`'s code nor the slot
  cell. `HH` is proved against it.
- **C3 (pool invariant independent of the scheduler).** `PoolS`, `TokPost` and the registry are
  stated over a finite family of task states: ready (`erwpX` at an expression), stopped (an entry's
  `PA` part with its `contShareN`), done, or joined.
  - `●` is a ghost piece of the invariant, not a heap cell or a field of `HH`'s state value.
  - Nothing in them assumes that exactly one task is not stopped.
  - `HH`'s `SchedOK` is a layer above.
- **C4 (no ghost fact fixed across stops).** `C`, and every ghost fact a task relies on, is read at
  the frame quantifier of the segment that uses it. None is fixed for a task at spawn or carried
  across its stops.
- **C5 (no transient writes outside the task's own cells).** No stage-2 rule, scheduler clause or
  program writes a location its start frame holds, not even temporarily, and in particular no
  write to a shared `imm` cell. G would refute such a proof when it is added.
- **C6 (cancel only at a stop).** Cancellation acts on a stopped task only (already true). `HH`'s
  reliance on finding the child parked is written down where it is used.

## 9. Size and modules

| module | content | lines |
|---|---|---|
| `SI/Guard` + retrofit | G as a conjunct of `rwpG`/`EndOKG`'s run clause (and stage 1's `erwpX` copy); `Step1` access sets per `Head` rule; G through the structural rules, `HeapN`, `HandleN`, `LoopN`, `Adequacy`, and the frame-changing rules listed in C1; `erwpX_reframe` | 1500 changed or added |
| `Par/Machine` | `PCfg`, `PStep`, `AllocFresh`, `OrDivergesPar`, the one-thread embedding | 300 |
| `Par/Local` | (L): `Step1` locality and commutation of disjoint steps, over `Head`'s rules, `Kont.plug` and `tab` blocks | 700 |
| `Par/Serial` | serialisation of every `PSteps` run into segment-contiguous order; the projected solitary run of each mid-segment thread | 1200 |
| `Par/PoolPar` | `ParInv` over C3's task states; preservation at segment ends and machine transitions; progress through `TokPost`; `parAdequacy`; `parDRF` | 1500 |
| `Par/Programs` | stage 2's `rootIJ` and `rootMJ` under the machine, from the *same* task derivations: `crossImmPar` and `crossMutPar` (`OrDivergesPar`, no hypotheses); a parallel split of a `mut` slice | 800 |
| `Par/UndoneWrite` | `UndoneImmWrite` proved, and the stuck pool without G, as a configuration (records why G is needed) | 300 |

That is about 6.3k lines: 1.5k in existing modules, 4.8k new. It comes after stage 2 and the
rule-level result. The typing side (which types are sendable, derived from the rules) belongs to
#789's rule-level work and is not counted. Nothing here needs a weak memory model, a new typing
judgment, or step-indexing beyond what `erwp` has.

**Kill criteria for the build:**
- G is not derivable for one of the frame-changing rules in C1 (the reborrow escrow frames
  `ρbχ`/`ρF` are the risk);
- serialisation needs renaming equivariance (N fails to suffice);
- `parAdequacy` needs a hypothesis;
- `PoolS` cannot be shared, and the machine needs its own copy of the invariant.

Any of these is to be delivered as a configuration at `rwpG`, `PStep`, `ParInv` or `TokPost`.

## 10. Open questions

- **`UndoneImmWrite`.** I expect it to hold, and have not built it. If it fails, G may be
  derivable from the frame quantifier: reads of frame-exclusive cells look excluded through
  `TWNC.free`, and writes would be the remaining part. Then the retrofit shrinks. Not derived.
- **G at the reborrow rules.** Whether `RebStopC/D`'s inner frames dominate the outer one in
  domain and exclusive part. Not checked.
- **No reuse, or reuse by the freeing thread.** Both serialise. The second matches thread-local
  allocators. Which to take is a modelling choice.
- **Cancel of a running target:** wait for its next stop, or refuse. And whether a cancel of a
  target that has finished becomes a join.
- **Join with errors.** Only as data (`try` in the child). #212's L5 choices (i) and (iii) are not
  needed by this route.
- **Channels.** The handle is a one-shot channel. Multi-use channels need `TokPost` generalised to
  connectivity graphs (Jacobs–Balzer–Krebbers) and session protocols (LinearActris). Not scoped.
- **Fairness and liveness.** Not claimed. `OrDivergesPar` is safety, progress and leak freedom.
- **`Φ` per thread**, and the tagged list `ls`. Stage 2's open "the `Φ` the pool fixes for tasks"
  carries over. Every thread is assumed at the root's list members, as in `PoolN`.
- **Parallel `Loop` drivers and div mains** (#212's U6). The machine runs each thread's `Loop`
  value as ordinary steps, and `OrDivergesPar` already allows divergence. A law relating parallel
  and sequential loop drivers is not scoped.
- **Whether `parAdequacy` should also yield `HH`'s answers** (a parallel run equals some `HH`
  schedule). Not needed for `OrDivergesPar`. It would need the observational (binary) relation
  noted on #771.

## Literature, and where we depart

- **Jacobs, Hinrichsen, Krebbers, POPL 2024 (LinearActris).**
  - *Taken:* `WP₀`'s shape (already `SI/Ewp`), adequacy for `fork` as initialisation,
    preservation and progress, and leak freedom from linearity.
  - *Departure:* our relation is per segment over typed worlds, so we serialise before applying
    the per-step argument, where LinearActris's wp is per step. Our channel is the one-shot
    handle.
- **Jacobs, Balzer, Krebbers, POPL 2022 (connectivity graphs).** Acyclicity gives progress. We
  specialise it to the spawn tree's post-order (`TokPost`), as stage 2 does.
- **Jung et al., JFP 2018 (Iris from the ground up).** The thread-pool step relation (pick a
  thread, step it, append forked threads) and adequacy through `wptp`.
  - *Departure:* fork, join and park are stops resolved by the machine, not primitive steps that
    return forked threads.
  - *Departure:* no invariants or later modality beyond `erwp`'s index.
- **Jung et al., POPL 2018 (RustBelt).** `Send`/`Sync` as semantic properties, and fractional
  lifetime tokens. Here every model type is `Send` and every `imm` view is `Sync` given G (§6).
- **Lipton, CACM 1975 (reduction).** The serialisation of §2. Commutation comes from G and the
  disjointness of pieces.
- **Adve and Hill, ISCA 1990; Boehm and Adve, PLDI 2008.** DRF-SC (§5).
- **#212's October scoping.**
  - Route C's U1 is G here, moved from a ∃-run witness in `wpTS` to a conjunct of `rwpG`'s ∀-run
    clause, which is why it is now confined to the run-level modules.
  - B4 (renaming) is avoided by N.
  - B1 (the undone write) is the reason G is needed.
  - Route I's opaque capabilities are §5's later step.
