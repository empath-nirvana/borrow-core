# Scope: #821, join by task handle through loan accounting at `erwp`

Branch `cross-821`, after 7b7657b2. This is a scope document for review. No Lean is added with it.
The build is a later unit.

## Kernel target

`OrDiverges` through a pool adequacy theorem at Core's `erwp`, keeping `ρ⁺` and `↭`, for
borrows handed to tasks spawned into the outer pool. The borrows are tracked by **loan
accounting**. The lender's ghost state records what it has handed to other tasks, `join h`
returns those shares, and the graph of handles between tasks stays acyclic.

## What the existing obstructions say, read together

- `erwp_refuses_borrowOut`, `not_crossTaskILend`, `not_crossTaskMLend` (`Core/Chain/CrossStopN.lean`).
  At a stop, `↭` sees a payload borrow at `ℓ` that the segment's start did not hold, and it
  refuses. That is correct for an untracked copy. It is too strong for a borrow the lender knows
  it has lent.
- `Core/Chain/Cross821Obs.lean`. `cerwp` removed `↭` to let the lend stay open. It then has no way
  to stop a run from ending with a copy it never held (`kapRelC_end`). The lend's end then needs
  a fact about every other task (`joinFd`), which is a frame condition. Frame conditions
  accumulate (`fdAnd_joinFd`), and two joiners can block each other (`hj_joinersDeadlock₀`).
- Read together, these say the lend's end has to be **local**. The lender has to be able to tell,
  from its own resource, that nothing of the lend is held anywhere else. `erwp` quantifies over
  every frame at every segment. So the lender can end a lend opened in an earlier segment only if
  (a) across stops it holds an **exclusive** cell at `ℓ`, which no valid frame can hold beside
  it, and (b) every share it handed out is **counted**, so that holding every count means no
  other share exists. Core's same-task Frame meets (a) by folding the cell back to `own` at every
  stop (`SI/IStopN.lean`). It never needs (b), because no share leaves the segment. Core's `imm`
  copies are idempotent (`compS_imm_dup`, 6.116), so they cannot carry (b).

This is my reading of the existing facts, not a new Lean configuration. Build step 0 states it
as `ImmEndAfterResume`: an `immFrame` lend whose lend cell is held across a stop, ended at a
later segment, at `erwp`. The build then refutes it at a frame holding a copy (`compS_imm_dup`,
`not_joinFd_of_holds`). Until that exists, the claim reads: not derived; obstruction expected at
`rwpG`'s frame quantifier.

## The design in one paragraph

The resource gains a **ghost component** beside `WRes`, as Iris pairs the heap with a ghost
resource algebra. It holds three things:

- **fractional read shares** of a cross-task `imm` lend (Boyland);
- the **lender's authority piece** for each cross-task lend it has open;
- an **agreement triple** per spawned task: the scheduler's slot record, the joiner's handle
  token and the child's writer token (Iris `Auth(Agree)`).

A cross-task `imm` lend freezes the lender's cell. `TWNC.mutFold` turns `own(v)` into a `mut`
cell whose predicate is `{v}`, which is exclusive and read-only. The lender takes the authority
and the full share. Borrowers hold only ghost shares, and they read through a coherence clause
of the world. A cross-task `mut` lend moves the `mut` cell itself and leaves the lender an
authority marker. `↭` stays at every end. It is **masked only at locations where the run holds
an authority**. So a payload can carry a borrow exactly when the run's authority lists it as a
loan, and every other copy is still refused. `spawn` allocates a physical **slot** cell owned by
the scheduler, plus the agreement triple. The child's end, or its cancel run, writes its answer
into the slot. `join h` hands over the token and gets back exactly the shares the token names.
The lend ends locally when the authority holds the full share again. Tokens are ghost, and the
garbage `ρ⁺` holds no ghost state. So handles are linear and children are joined. Tokens move
only down the spawn tree. So every wait-for edge goes backward in the spawn tree's post-order,
and the scheduler's "nothing ready" branch is unreachable. That branch is written as a stuck
term, so `OrDiverges` itself excludes deadlock.

## 1. The loan record

**Authoritative state.** The lender's authority piece in the ghost component, at the lent
location `ℓ`:

- `xi q true v` for an `imm` lend: the lender's own share `q`, the authority flag, and the frozen
  value `v`;
- `xm` for a `mut` lend.

At most one authority can exist per location (validity). The outstanding loans of an `imm` lend
are `1 − q`, held as shares elsewhere, and the composite's validity keeps the sum at most 1. The
lender's **handle tokens** say which task returns which share.

**What borrowers hold.**

- `imm`: `xi q false v` (ghost) and **no `WRes` cell at `ℓ`**. Shares split and merge by
  composition (`q₁ + q₂ ≤ 1`, same `v`). This replaces 6.116 for cross-task lends only.
- `mut`: the `WRes` cell `ℓ ↦ mut(β, u, ∅, P̂)` itself, whole.

**Why a ghost component, not a field, and not a new `CellU` kind.**

- The natural field is a share on `ImmU` (`Paper/S5_Model/Definitions.lean`). It is the printed
  §5 carrier. `immOf` has 2444 uses in 171 files. `CellU.CompS`'s existential changes shape, and
  so does every proof that destructures it.
- A new `CellU` kind for the handle token has no location to live at. A ghost location would
  collide with physical allocation, because `Lower` would skip the cell and `alloc` could pick
  the location. Putting it at the slot's location needs an `own ● tok` clause in `●`, and every
  `●`/`○` lemma would then case-split on it.
- A ghost component touches neither. Every `erwp` derivation lifts with any ghost frame
  (`erwpX_of_erwp`, built the way `cerwp_of_erwp` lifts `erwp`). The new coordinate is a field of
  the resource the relation is indexed by, so there is still one relation.
- The fallback is a share field on `ImmU`. That is decision **D1** below.

**Coherence (the lend's invariant).** The world validity becomes
`TWNX W G ps rs := TWNC W ps rs ∧ GCoh W G ∧ G.Valid`. `GCoh` says:

- every `xi _ _ v` at `ℓ` has `W` at `ℓ` equal to the frozen `mut(β, v, ∅, {v})`;
- every slot or token at `a` has `a ↦ own(_)` in `W`.

This plays the part of an Iris invariant. We need neither Iris's invariants nor its later
modality: the world validity is already global, and `erwp` is already step-indexed.

## 2. `↭` at a stop: the exact change

`EndOKG` (`SI/RwpG.lean`) becomes `EndOKX`, over `XRes = WRes × GRes`, with four changes. The
rest is unchanged: `Hash`, `CompS` and `Lower` on the `W` part, `Tagged`, and `ps′ ~ ps`,
`ls′ ~ ls`, which are unchanged because cross-task lends create no `FrameRec`.

1. `UpdVN Φ k ρ π` becomes `UpdVNm Φ k M ρ.W π.W`, where `M := auth(ρ.G) ∪ auth(π.G)`, the
   locations where the run holds an authority at its start or its end. `UpdVNm` is `UpdN`'s
   `imm` and `mut` clauses read at locations `∉ M`, with validity as before.
2. `NoOwn ρp` becomes `NoOwn ρp.W ∧ ρp.G = ∅`. The garbage keeps `ρ⁺` and holds no ghost state.
3. `TWNC fρ′p ps′ (rsOf ls′)` becomes `TWNX`.
4. Ghost changes between start and end are frame-preserving, which comes for free: the end must
   compose with the same frame.

What this does:

- **A loaned `imm` share crosses a stop as a ghost share.** `↭` does not read `G`. Shares cannot
  be created, because they are conserved by `G.Valid`. A **`WRes` copy** of a same-task lend in a
  payload is still refused at every unmasked location (`erwp_refuses_borrowOut` stays true for
  it).
- **A loaned `mut` cell in a payload is accepted exactly at `ℓ ∈ M`**, that is, when the run holds
  `xm` at `ℓ`, which is the loan record. A borrower holds no authority. Its `↭` stays unmasked, so
  `PredStep` keeps the cell's predicate it returns.
- **The lender's own transitions are accepted** because they are masked: `own(v)` becomes the
  frozen cell or nothing, and `own(u)` comes back at the end.

So `cerwp` lost `↭` everywhere, and `rwpG` enforced it at the lender's own lent location. `EndOKX`
lifts it at the run's own authority locations only.

## 3. The handle

I take the suggested shape, with three changes.

- **Slot.** `spawn` allocates a physical cell `a ↦ own(live)`, owned by the scheduler. Its
  states are `live`, `live` with a waiter `κ_J`, and `done w`. The child's end writes
  `done w`. If a joiner is waiting, the scheduler resumes it directly instead of writing.
- **Ghost triple at `a`.** The scheduler holds `slot r`, the joiner `tok r`, and the child
  `wr r`. Here `r : List Loan` is the task's return list, with
  `Loan ::= imm ℓ q v | mut ℓ β P̂`. Composition is defined only if all three `r` agree.
  - The token makes handles unforgeable: a forged `a` has no `tok`, and a stale one was consumed
    at its join.
  - The writer token ties the child's park and cancel to its slot (item 4).
  - The handle value is `loc a`.
- **Ghost argument on entries.** `OpEntN` gains a ghost argument `g : List Loan`, read by `PA`,
  `PB`/`PBv` and `fin`. The stop becomes `∃ g, PA g ⋆ contShare g`, the binder of an
  `∀x. {P x} op {Q x}` specification. Old entries ignore `g`. This is a field, and the reason is
  that `PBv` reads only the payload value, not the token in `PA`'s resource.
- **No lookup, no scheduler loop.** `join (loc a)` loads `!a`.
  - `done w`: free `a`, consume `slot r ● tok r`, resume the joiner with `w` and the resources `r`
    names.
  - `live`: store the joiner's `κ` into `a`'s waiter field and resume the next ready task.
  - Nothing compares locations, and the deep handler's recursion is the only iteration.

**Why not the alternatives.**

- A single cell for slot and right fails. The joiner needs an exclusive right while the
  scheduler writes, and `●` composes only `imm`/`imm`.
- A two-cell ticket (`t ↦ own(loc a)`) needs ghost agreement anyway, so that `PBv` knows `r`. It
  also costs a physical cell.
- A per-handle answer list needs equality on locations, which the language does not have.

## 4. Cancellation

The child's park stops choose `g = r`. The park's `PA g` includes `wr g` at the child's slot, and
`PB g` returns it. So at the scheduler, `slot r ● wr g` forces `g = r`. The park entry's
`fin g` is a cancel obligation at `erwpX` (the analogue of `PcanC`, new) answering `QRet g`: the cancel run's end holds exactly the loans `g` names, plus `wr g`.

`HH` runs the cancel branch with the child as current, and its end goes through the return path
like any end: `a := done(())` with those resources. `join` returns them.

This ties the leftover (an `imm` share or the `mut` cell) to its loan through `wr`/`slot`
agreement, not through the payload or the answer value. `OpEntN.fin` still does not read the
payload. It reads `g`.

## 5. Progress at joins

**Invariant `TokPost`.** Every `tok b` is held by a task `J` with `b <_post J`, in the post-order
of the spawn tree, with children ordered by spawn time. Equivalently, the waits-for edges point
backward in post-order. This is preserved by:

- `spawn` by `P` of `C`. `tok C` goes to `P`, and `C <_post P`. Tokens moved in the payload from
  `P` to `C` still point backward, since `C` is inserted just before `P` in post-order.
- `join`, which consumes a token.
- a task's end, because answers carry no token (`r` holds only loans) and garbage holds no ghost
  state.

New tasks never reorder existing ones.

**Why it holds.** A token is created for the spawner. It moves only into tasks spawned later, by
spawn payloads, and those tasks lie outside the child's subtree. It never moves up. This is
Jacobs–Balzer–Krebbers's acyclicity specialised to a tree. A token moves along an existing edge,
and here a post-order measure replaces the general connectivity graph, because nothing is sent
back up.

**Progress.** Take any state with a waiting joiner. The post-order-least live task that is not
done is not waiting, since its target would be smaller and live. So it is running or in the
ready list. `HH`'s empty-ready branch is therefore unreachable. It is written as a stuck term, so
the headline's `OrDiverges` proves it unreachable. A scheduler that spins on a deadlock would be
caught.

**`hj_joinersDeadlock₀`** comes from `joinFd` frame conditions and from shares conjured by
`kapRelC_end`. `erwpX` has neither: a lend ends at `xi 1 true` with no frame condition, and `↭`
refuses conjured copies. The waits-for form of that configuration, two joiners each waiting on
the other's slot, contradicts `TokPost` (`b <_post J` and `J <_post b`). The build states this as
`not_mutualWait`.

## 6. The same-task Frame as a special case

`erwp_I_frame`, `erwp_I_frameC` and `erwp_M_frame`/`_frameT`/`_frameF`/`_frameR` are the instance
with **no loan out at any stop**. Their tables keep the payload borrow-free (`ILendOK.pa`,
`LendOK.pa`). At a stop, the fold back to `own(v)` is the exclusive cell (a) of the opening
section. With nothing handed out, freezing is not needed, and no ghost state is created. They
lift unchanged through `erwpX_of_erwp`. No statement changes.

(There is no declaration named `erwp_I_frameK` on this branch. The cancellable form is
`erwp_I_frameC`.)

**`erwp` and `cerwp` collapse.** Each of `cerwp`'s three changes is replaced:

| `cerwp`'s change | replaced by |
|---|---|
| owned records `O` | the ghost authority (cross-task lends create no `FrameRec`) |
| no garbage | `ρ⁺` kept, with no ghost part |
| qualified frames `F`/`fd` | the lend's end is local at the full share |

`erwp` is `erwpX` at ghost-free resources and frames. So for the cross-task case `cerwp` is not
needed. That closes SPEC §62's "the two relations merge" item in design. The build does not
remove `cerwp`, `PoolC` or `PoolJoinC`. Removing them is a later unit, once nothing depends on
them.

## 7. `CaptureScope`'s restrictions

- **Empty lent-cell payload (`ρ_P = ∅`): kept.** A frozen cell with an escrow would need shares
  of the escrow's cells for nested reads. That belongs to #791, as with `ViewsT`. The headlines
  use `alloc ()`.
- **Must-resume, empty-answer body operations.**
  - *Empty answers: lifted.* `spawn` answers a handle and `join` answers loans. These are the
    loan operations.
  - *Must-resume: lifted for borrowers.* The children's parks are cancellable, as the cancel
    variants need.
  - *Kept for a task holding an authority.* Cancelling a lender with loans out needs joins inside
    its unwinding. That is a separate case, and the headlines do not need it.
- **`erwp0`: lifted.** `erwpX` keeps `ρ⁺`. Loans are ghost, and the garbage holds no ghost state,
  so no loan can be put in garbage.

**New restrictions.** Both are stated in the build's SPEC entry.

- A join's answer is a value plus exactly the loans `r` names. It carries no handle and no owned
  cell.
- A cross-task `mut` borrower keeps the cell's predicate (`PredStep` at the pool's `Φ`).

## 8. Done-when for the build unit

**The scheduler `HH`.** Operations: `parkC` (cancellable), `parkL`, `spawn (th, loans)`,
`join h`, `cancel`. Its state is the ready list plus the current task's slot. There is no
barrier, a `spawn` after a `join` is allowed, and the empty-ready branch is stuck.

**The pool theorem.** `PoolSchedAdequacyS`/`poolSchedAdequacyS` over `erwpX`, with the pool given
as the ready list plus slot cells (`PoolS`, `TokPost` as part of the invariant). Its moves are:

- `run`, `park`, `resume`, `cancel`;
- `spawn` (allocate the slot and the triple);
- `wait` (store the joiner in a slot);
- `finish` (write `done`, or resume the waiter);
- `joinDone`.

**The programs.** The lend is written in the text with `withborU` (`dB`), as in
`Core/Chain/Cross821N.lean`. The spawns go to the top-level `HH`.

- `rootIJ b`:
  1. Lend `c` imm.
  2. Spawn `C₁` and `C₂`, each `λ_. parkC (); !r`, each holding a share.
  3. Read `!c`.
  4. **`join h₁` while `C₂` is parked holding its share of the same lend.** This is what
     `not_joinFd_of_holds` blocked.
  5. **Spawn `C₃` after the join**, with a share.
  6. Then `parkL ()` (`b = false`), or `cancel ()` (`b = true`), which cancels a parked child that
     holds a share.
  7. Join `h₂` and `h₃`, end the lend, free `c`.
- `rootMJ b`:
  1. Lend `c` mut.
  2. Spawn `C₁ = λ_. parkC (); r := 7; ()` with the `mut` cell.
  3. Then `parkL ()`, or `cancel ()`, which cancels `C₁` while it is parked holding the cell.
  4. Join `h₁`.
  5. **Lend to `C₂` after the join** and join it.
  6. End the lend, free `c`.

**Headlines.**

| headline | statement |
|---|---|
| `crossImmJ` | `OrDiverges ((hnd HH (rootIJ false)) (HH, …))` |
| `crossImmJC` | `rootIJ true` |
| `crossMutJ` | `rootMJ false` |
| `crossMutJC` | `rootMJ true` |

Each goes through `poolSchedAdequacyS`, with no hypotheses and with `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`. Also:

- `not_mutualWait`;
- `ImmEndAfterResume` refuted (build step 0);
- a SPEC §62 entry written first.

The theorems the four headlines rule out by name are:

- a scheduler that frees a slot or `c` early (a stuck load);
- one that loses a slot (a non-empty heap at the end);
- one that resumes a joiner before its child's loans are back (the lend's end is not derivable);
- one that deadlocks (the stuck branch is reached).

**Hardest case.**

- Case 2's child **writes through the `mut` borrow after its park**. Its resumed segment stores
  through the cell, its `↭` is unmasked, and it returns the cell through its slot. The lender's
  join gives the cell back, and the lender unfolds it at `xm`.
- In the cancel variant, the child is **cancelled while parked holding the cell**. Its cancel run
  ends holding it at `fin r`, and `wr`/`slot` agreement routes it to the slot.
- For `imm`, the hardest case is step 4 of `rootIJ`: the join is resumed beside another share of
  the same lend.

## 9. Kill and fallback criterion

**Kill.** The build stops if any of these happens:

- a headline needs a hypothesis;
- `HH` needs a barrier or a spawn-after-join ban;
- the pool theorem needs a premise standing in for `TokPost`;
- one of `updVNm_frame` (6.48 at a mask), `erwpX_of_erwp` or `GCoh` preservation under the lifted
  steps is not derived.

**Delivery on a kill.** The obstruction is delivered as a Lean configuration at the named
definition, every hypothesis discharged. The candidate definitions are `UpdVNm`, `EndOKX`,
`TWNX`/`GCoh`, `PoolS` and `TokPost`. The report also lists:

- unspent hypotheses;
- unused uniqueness results;
- which of the run-up lemmas (the `erwpX` rules, the frozen-cell load, the share load) are
  unbuilt.

**Fallback.** The scoped form: `crossImm`, `crossImmC`, `crossMut` and `crossMutC` (already proved,
`Core/Chain/Cross821N.lean`). SPEC states the restriction "cross-task borrows are scoped". The
cross-task lend is held by a child spawned into a scheduler inside the lend's callback.

## 10. NOT-do, and the tempting shortcuts (→ STOP)

- Patching `cerwp`'s `EndC` alone (adding `↭` there) → STOP. The frame conditions and owned
  records remain, and so do the deadlock and the accumulation.
- A barrier join (resume only with no other task), or forbidding `spawn` after `join` → STOP.
- A stand-in hypothesis for acyclicity or for progress → STOP. `TokPost` is proved from the moves.
- Opening loans only in the proof (a ghost lend around code with no borrow form) → STOP. The lend
  is `withborU` in the text.
- A share field on `Paper/`'s `ImmU`, or any edit of a printed `Paper/` definition, without the
  user's decision on D1 → STOP.
- Editing the statements of `erwp`'s existing rules (`erwp_I_frame`, `erwp_M_frame`, …) → STOP.
  They are lifted, not changed.
- A scheduler that searches its pool by location, or a loop in a clause, to find a child → STOP.
  The slot is dereferenced.
- Answers that carry handles or owned cells "for convenience" → STOP. That is a separate
  extension.
- Removing `cerwp`, `PoolC` or `PoolJoinC` in this unit → STOP.

## 11. Size estimate and modules

About 9k lines, range 7–11k. Comparable: `PoolJoinC` + `PoolC` + `Cross821C` ≈ 2.0k for `HJ`
alone.

| module | content | lines |
|---|---|---|
| `Core/Chain/SI/Ghost.lean` | `GRes`: `xi`, `xm`, `slot`/`tok`/`wr`; validity, composition, frame-preserving updates | 500 |
| `Core/Chain/SI/XRes.lean` | `XRes`, `Hash`/`CompS`/`Lower` on pairs, `TWNX`, `GCoh` | 700 |
| `Core/Chain/SI/UpdMask.lean` | `UpdVNm`, `updVNm_frame`, `updVNm_trans`, `UpdVN → UpdVNm` | 500 |
| `Core/Chain/SI/ErwpX.lean` | `EndOKX`, `rwpX`, `erwpX`; bind, frame, det, val, le; `erwpX_of_erwp` | 900 |
| `Core/Chain/SI/HandleX.lean` | `[handle]` at `erwpX`, κ cells, resume, cancel; the ghost argument on entries | 600 |
| `Core/Chain/SI/LendX.lean` | cross-task `imm` (freeze, shares, frozen and share loads, end at `xi 1 true`); cross-task `mut` (`xm`, end) | 900 |
| `Core/Chain/PoolS.lean` | `PoolS`, `TokPost`, moves, progress, `not_mutualWait`, `PoolSchedAdequacyS` | 1600 |
| `Core/Chain/PoolHH.lean` | `HH`'s code, `SchedOK` at `PoolAnsS` | 1600 |
| `Core/Chain/Cross821X.lean` | `rootIJ`, `rootMJ`, four headlines, `ImmEndAfterResume` | 1300 |

## Open questions

- **D1, for the user.** Is the share a ghost component beside `WRes` (recommended), or a field on
  `Paper/`'s `ImmU`? The field means the printed §5 carrier stops being the printed one; memory
  "`Paper/` may go" says to raise exactly this.
- **`updVNm_frame`.** Does 6.48's aliasable case (`agMutCarry`, the immutable ancestor) go through
  at a mask? At `ρ_P = ∅` no walk passes below `ℓ`, so I expect yes. Not derived.
- **Lifting `[handle]`.** Does `erwp_handle_le` lift through `erwpX_of_erwp`, or does it have to
  be re-proved? Clauses now receive shares with ghost parts. I expect it has to be re-proved.
- **The `Φ` the pool fixes for tasks.** A `mut` borrower's `PredStep` at `Φ ℓ = none` is equality,
  which the headlines meet. Covered families are not examined.
- **Typing.** How the checker marks a lend as cross-task (a field on the borrow form's index
  record), and `Imm`'s interpretation as a ghost share, are not designed here. The headlines are
  semantic programs.
- **The lender's view is not read back.** The lender gets the `mut` cell back at any content its
  predicate admits (as `MFPost`). Whether the headlines should also read back `7` is open.
