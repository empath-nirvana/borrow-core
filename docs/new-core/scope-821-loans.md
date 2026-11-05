# Scope: #821, one relation, then join by task handle through lifetime tokens

Branch `cross-821`, after 7b7657b2. This is a scope document for review. No Lean is added with it.
The build comes in two stages, each a later unit with its own done-when.

## Kernel target

`OrDiverges` through a pool adequacy theorem at **one** relation, for borrows handed to tasks
spawned into the outer pool. Today there are two relations, `erwp` and `cerwp`. The one relation
keeps `erwp`'s `ρ⁺` and `↭`, and `erwp` is its ghost-free instance. Shared borrows stay `imm`
cells that can be copied freely. What is counted is the **lifetime**, by fractional tokens
`[α]_q` as in RustBelt. A handoff to another task passes a fraction along with the copy. `join h`
returns the fraction, and the lend ends when the lender holds `[α]_1` again. The graph of handles
between tasks stays acyclic.

## Stage plan

| stage | what lands | new loan feature | size |
|---|---|---|---|
| 1. One relation | `erwpX` defined once, in its final form; `erwp` proved its ghost-free instance; its structural rules and adequacy; `cerwp` and everything built on it retired | none | about 3.0k lines added, 6.0k deleted |
| 2. Loans | token rules, counted lend across stops, `mut` loans, `[handle]` at `erwpX`, `PoolS`, `HH`, four headlines | yes | about 7.0k lines (7.8k if `CrossProg` is re-proved) |

Stage 2 changes nothing stage 1 defines. It only adds rules, the pool theorem and programs.

---

## Stage 1: one relation

### The relation

`XRes = WRes × GRes`. `GRes` is a ghost resource algebra (`Core/Chain/SI/Ghost.lean`) with three
parts. Each part's composition and validity is standard.

- **Lifetime tokens**, `Life → Frac`. They compose by adding fractions, and validity keeps each
  sum at most 1 (Boyland; RustBelt's `[α]_q`).
- **`mut` authorities** `xm`, keyed by `Loc` and exclusive.
- **The task registry**, Iris `Auth(Loc ⇀ Agree(Ret))`. The scheduler holds `●`. Each entry has
  two exclusive fragments: `tok r`, held by the joiner, and `wr r`, held by the child.

`Ret := List Loan`, with `Loan ::= imm α q | mut ℓ β P̂`.

`erwpX` is `erwp`'s definition (`SI/ErwpN.lean`) over `XRes`, with its end `EndOKX` in place of
`EndOKG` (`SI/RwpG.lean`). Its world condition is `TWNX W G ps rs := TWNC W ps rs ∧ G.Valid`.

**`WF_C`.** For a set of lifetimes `C`, a part satisfies `WF_C` when, for every `α ∈ C`, the part
holds a positive fraction of `[α]` whenever its flattening holds an `imm` cell carrying `α`.
`C` is the set of lifetimes with a token anywhere in the world.

**Changes against `rwpG`/`EndOKG`:**

1. **The frame quantifier.** Frames range over `XRes`. The frame and the start resource are each
   `WF_C`, for the world's `C`.
2. **`↭` with a mask.** `UpdVN Φ k ρ π` becomes `UpdVNm Φ k M ρ.W π.W`: `UpdN`'s `imm` and `mut`
   clauses, read only at locations outside `M`. `M` contains:
   - the locations of records whose lifetime is **wholly held**, as `[α]_1`, in `ρ.G` or `ρ′.G`;
   - the locations where `ρ.G` or `ρ′.G` holds an `xm`.

   Here `ρ′` is the end resource without the garbage. At a stop it is the payload together with
   the share.
3. **Records.** `ps′ ~ ps` and `ls′ ~ ls` hold except at the records whose lifetime is wholly held
   at the start or at the end (that is, `ps Δ ps′` is contained in those records).
4. **Garbage.** It is `NoOwn` on `W`, as now. It may hold tokens. The end's `ρ′` and `ρp` are each
   `WF_C`.
5. **Posts and tables.** `C` is passed to the post as an index coordinate. A table's stop clause
   splits `ρ′` into a payload and a share that are each `WF_C`.
6. **World and ghost changes.** `TWNC` becomes `TWNX`. A ghost change between start and end is
   frame-preserving by construction, because the end must compose with the same frame.

### `erwp` is the ghost-free instance

**`erwp_iff_erwpX0`, an equivalence.** For every `Φ`, table `Tb`, post `Q`, index, list,
expression and `ρ`:

`erwp Φ Tb Q n ls e ρ ↔ erwpX Φ Tb↑ Q↑ n ls e (ρ, ∅)`

`Q↑` and `Tb↑` are `Q` and `Tb` with every part they describe ghost-free.

- **(→)**
  - A frame with ghost state can count only lifetimes `α` of which `ρ` holds no copy. If `ρ` held
    one, it would have no fraction and the start would not be `WF_C`, so that frame is excluded.
  - `↭` with no mask (the run holds no token) lets the end's copies be only the start's. So no
    end part holds a copy at a counted lifetime.
  - Lends opened inside the run are closed at its end, or folded at its stops.
- **(←)**
  - Use the frame `(ρf, ∅)`. `WF_∅` is vacuous.
  - With ghost-free posts and tables, `ρ′.G = ∅`, so `M = ∅` and `ps′ = ps`. `EndOKX` then reads
    as `EndOKG`.
  - The continuations follow by induction on the index.

**No existing `erwp` proof changes.** `erwp`'s definition is untouched. The equivalence is a
theorem about it, so every `erwp` rule and headline holds at the instance.

### What the lift does not give

The token lift `erwpX_of_erwp_tok` belongs to stage 2. It is **one direction only**:
`erwp ρ → erwpX (ρ, g)` for any `g` that makes `ρ` `WF_C`. At each end it hands `g`'s
fractions to the parts that hold copies, using that `↭` makes the end's copies the start's.

The converse fails. `erwpX` at `(ρ, [α]_1)` quantifies over fewer frames than `erwp` at `ρ`: no
frame holds a copy at `α`. So that `erwpX` derivation says nothing at frames `erwp` covers. The
build states this as `not_erwp_of_erwpX_tok`, a configuration at a frame holding a copy of a
lend at `α`, every hypothesis discharged.

### Retiring `cerwp`

`crwpG`, `cerwp` and `contShareC` are deleted (`SI/Capture.lean`, `SI/CaptureE.lean`). For each
result now stated at `cerwp`:

| result | stage 1 | departures it removes |
|---|---|---|
| `SI/Capture`, `SI/CaptureE`, `SI/CaptureGen`, `SI/CaptureHeap`, `SI/CaptureAdequacy` | delete | owned records `O` with `Split`; no garbage; qualified frames `F` and the entry's `fd`; no `↭` at ends; frame conditions accumulating in `contShareC` |
| `SI/CaptureScope` (`cerwp_scope`) | delete; replaced in stage 2 by the counted lend across stops, which ends at `[α]_1` | the scope's body ending at `join(ℓ)` with the frame condition `joinFd`; the lender's copy kept beside every segment; ending a lend outside the segment that opened it only through a resumer's guarantee |
| `SI/CaptureScopeM` (`cerwp_scopeM`) | delete; replaced in stage 2 by the `mut` loan rule (`xm`) | the borrow returned only through a join answer that names the cell's `P̂` (`joinPBvM`) |
| `SI/CrossProg`, `SI/CrossProgM` (`prog_orDiverges`, `progD_orDiverges`, `progM_orDiverges`, `progDM_orDiverges`) | delete (recommended; superseded by stage 2's headlines), or re-prove in stage 2 at `HH`'s relation | a hand-written two-handler scheduler with a fixed event order; join by location |
| `PoolC` (`poolSchedAdequacyC`) | delete; replaced in stage 2 by `PoolS` over `erwpX` | the scheduler's bag of what ended tasks hold; the invariant read at the running task's frame condition |
| `PoolJoinC` / `HJ` (`hj_schedOKC`, `progOfC_orDiverges`) | delete | the barrier join; the marker that forbids `spawn` after a join; tasks ending with copies only (`QinJ`) |
| `Cross821C` (`crossImmJ`, `crossImmJC`) | delete; restated in stage 2 under the same names at `HH` | all of `HJ`'s, inherited |
| `Cross821Obs` | delete; its lesson is recorded here | none (observations about `cerwp`) |
| `SI/Erwp0` | delete; `erwpX` keeps `ρ⁺` | the garbage-free relation `erwp0` |
| `SI/CactusInv` | delete; it is stated over `crwpG` and unused | none |

`SI/Uncapture` is kept. It holds world lemmas (`capture_world`, `uncapture_world`) with no
`cerwp`, and stage 2 reuses them. The tree track's `cerwpT` is a separate relation and is not
touched. SPEC §62's evidence lines naming `cerwp_scope(M)`, `CrossProg(M)` and `CactusInv` are
updated.

### The one conflict in stage 1's requirements

The six `cerwp` headlines cannot be stated at `erwp = erwpX0`. Those are `prog_orDiverges`,
`progD_orDiverges`, `progM_orDiverges`, `progDM_orDiverges`, `crossImmJ` and `crossImmJC`. Each
passes a borrow out of its lending segment at a stop, and `erwp_refuses_borrowOut` refutes such a
stop at every index. That is a named configuration with every hypothesis discharged.

So "retire `cerwp` in stage 1" and "every existing chain headline still proved in stage 1" cannot
both hold for these six. The choices:

- **(i) Recommended.** Delete them in stage 1 and restate them in stage 2. None of them is on
  `main`, the branch merges only after stage 2, and so no merged state lacks them.
- **(ii)** Keep the `cerwp` files until stage 2 restates the headlines, and retire them there.

Every other chain headline stands through `erwp_iff_erwpX0`. That includes `crossImm*` and
`crossMut*` (scoped, `Cross821N`) and the `SI/*Prog` programs.

### Stage 1 done-when

- `erwpX`, `EndOKX`, `UpdVNm`, `WF_C`, `GRes` and `TWNX` are defined, and stage 2 uses them
  unchanged.
- `erwp_iff_erwpX0` is proved in both directions.
- `erwpX`'s structural rules: `erwpX_le`, `_det`, `_val`, `_bind` and `_frame`, the last needing
  `updVNm_frame`, which is 6.48 at a mask.
- `erwpX_adequacy`: a closed program from `(∅, ∅)` at the empty table, whose post owns nothing,
  ghost included, is `OrDiverges`.
- The retirement table is carried out, under option (i) or (ii).
- `lake build` of `Core.Chain` is clean. Every remaining `erwp` headline is still proved, and
  `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
- The SPEC §62 entry is written first.

**Stage 1 sizes.**

| module | content | lines |
|---|---|---|
| `SI/Ghost` | `GRes` and its validity and composition | 500 |
| `SI/XRes` | the pair, `Hash`/`CompS`/`Lower` on it, `WF_C`, `TWNX` | 400 |
| `SI/UpdMask` | `UpdVNm`, `updVNm_frame`, `updVNm_trans` | 700 |
| `SI/ErwpX` | the relation and its structural rules | 800 |
| `SI/ErwpX0` | `erwp_iff_erwpX0` | 400 |
| `SI/AdequacyX` | `erwpX_adequacy` | 200 |

That is about 3.0k added, with 6.0k deleted.

---

## Stage 2: loan accounting at the one relation

### Why lifetimes, read against the obstructions

- **`erwp_refuses_borrowOut` and `not_crossTaskILend`.** At a stop, `↭` refuses a payload borrow
  that the segment's start did not hold. Once its lifetime is wholly held, the lender is masked
  at that location.
- **`Cross821Obs`.** `cerwp` lost `↭`. A run could then end with a copy it never held, so the lend
  could end only through a frame condition (`joinFd`), and frame conditions accumulate and
  deadlock.
- **What is needed.** A lend's end must be local. `erwpX` quantifies over every frame at every
  segment, so the lender must know from its own resource that no frame holds a copy at `ℓ`.
- **How tokens give it.** Copies cannot be counted, but the lifetime can. A lender holding
  `[α]_1` knows from validity that no frame holds any fraction of `α`. From `WF_C`, no frame then
  holds any copy carrying `α`, at any depth. So `TWNC.immEnd` is valid at every frame `erwpX`
  quantifies over.

**Step 0** states `ImmEndAfterResume` at `erwp`: an `immFrame` lend held open across a stop and
ended at a later segment. It refutes it at a frame holding a copy (`compS_imm_dup`). This is why
the count is needed, as a configuration.

**Point 2's outcome: adopted.** I found no part of the cross-task `imm` case that needs a
representation other than the token one. I have no configuration showing that the token design
fails anywhere. So the previous design's frozen cell and per-cell ghost shares are gone.

- **One representation.** An `imm` borrow is the same `imm` cell whether or not it crosses a task.
- **No marking.** Every lend opened by the native lend rule mints `[α]_1` at a fresh `α`, so the
  checker has nothing to mark.
- **`mut` is as before.** The cell moves and the lender keeps `xm`.

### 1. The loan record

- **For `imm`.** The lend's existing `FrameRec`, made by `TWNC.immFrame` and kept in `ps`, plus
  the token. The lender holds `[α]_q`. The outstanding loans are the fractions summing to `1 − q`
  held elsewhere, and the lender's handle tokens say which task returns which fraction. No new
  field and no new `CellU` kind.
- **For `mut`.** `xm` at `ℓ`, exclusive.
- **What each borrower holds.**
  - `imm`: a copy `imm({α}, v, ∅)` and `[α]_q`. A borrower may sub-lend by splitting its
    fraction.
  - `mut`: the `mut` cell, whole.

### 2. `↭` at a stop

`EndOKX`'s mask (stage 1) does the following.

- **The lender's own transitions are masked.** The lender holds its lifetime wholly in two
  segments: the first, where its start has `own(v)` and its stop has the lend cell open, and the
  last, where its start has the lend cell and its end has `own(v)`. In between it holds only part
  of the token, so `↭` applies unmasked and its copies stay the same.
- **Copies.** A payload copy at `α` comes with a fraction because of `WF_C`. `↭` keeps copies from
  being conjured, because the end's copies are the start's. A copy at an uncounted lifetime
  behaves as today.
- **`mut`.** A `mut` cell in a payload is accepted exactly at `xm` locations.

### 3. The handle

- **Slot.** A physical cell `a ↦ own(live | live+waiter κ_J | done w)`, owned by the scheduler.
- **Registry entry.** `a ↦ r`. The scheduler holds `●`, the joiner `tok r` and the child `wr r`.
  - **Correction to the previous draft.** That draft's coherence clause did not stop a task from
    minting a fake slot and token pair. Under `●`, minting either fragment needs the
    authoritative piece, which only the scheduler holds.
- **Ghost argument `g` on `OpEntN`.** It is read by `PA`, `PB`/`PBv` and `fin`.
- **`PBv g`.** The answer's resource is:
  - each `imm α q` entry's `[α]_q`, with any copies at `α`;
  - each `mut ℓ β P̂` entry's cell.
- **`join (loc a)` loads `!a`.**
  - `done w`: free `a`, consume `tok r`, and resume the joiner with `w` and the resource for `r`.
  - Otherwise: store the joiner in the waiter field and resume the next ready task.

There is no location equality and no loop in a clause.

### 4. Cancellation

A child's park shows `wr g`, so `g = r` at the registry. `fin g`'s cancel run ends holding `r`'s
fractions and cells. `HH`'s return path writes them into the slot. The leftover is tied to its
loan through the registry, not through the payload.

### 5. Progress at joins

**`TokPost`.** Every `tok b` is held by a task `J` with `b <_post J` in the spawn tree's
post-order. Spawn, join and a task's end keep it, because answers carry no tokens. The argument is
Jacobs–Balzer–Krebbers specialised to a tree.

- The post-order-least live task that is not done is not waiting.
- So `HH`'s empty-ready branch is unreachable. It is written as a stuck term, which makes it
  `OrDiverges`'s burden.
- `hj_joinersDeadlock₀`'s causes are absent: there is no `joinFd`, and no copy is conjured. Its
  waits-for form contradicts `TokPost` (`not_mutualWait`).

### 6. The same-task Frame

`erwp_I_frame`, `erwp_I_frameC` and the `erwp_M_frame*` rules hold at `erwpX0` through
`erwp_iff_erwpX0`. Inside a task that holds tokens, they hold through `erwpX_of_erwp_tok`.

The native counted lend (`erwpX_lend`) keeps the lend open across stops with no fold. It is the
general rule. `erwp_I_frame` is its instance where no fraction ever leaves the segment, and that
rule additionally folds at stops. There is no `erwp_I_frameK` on this branch.

### 7. Restrictions

- **Kept: the lent cell's payload is empty (`ρ_P = ∅`).** `WF_C` at depth for escrows with
  contents belongs to #791.
- **Lifted:**
  - empty answers;
  - must-resume operations for borrowers;
  - `erwp0`.
- **Kept: must-resume for a task holding `[α]_1`, or a `mut` authority, with loans out.**
- **New:**
  - a join's answer is a value plus exactly `r`;
  - a `mut` borrower keeps `P̂`.

### 8. Done-when for stage 2

- **Rules.**
  - `erwpX_of_erwp_tok` and `not_erwp_of_erwpX_tok`.
  - The counted `imm` lend: open with the mint, kept across stops, ended at `[α]_1` through
    `uncapture_world`.
  - The `mut` loan with `xm`.
  - `[handle]` at `erwpX`.
- **Pool theorem and scheduler.**
  - `PoolS` with `TokPost` and the registry.
  - `poolSchedAdequacyS`.
  - `HH`: no barrier, `spawn` allowed after `join`, the empty-ready branch stuck.
- **Programs.** Both use `withborU` in the program text.
  - `rootIJ b`: two children each hold a copy and a fraction.
    - `join h₁` happens while `C₂` still holds its share of the same lend.
    - `C₃` is spawned after that join.
    - The tail is `parkL ()`, or `cancel ()` of a parked share holder.
    - Then the remaining joins, the lend's end, and the free.
  - `rootMJ b`:
    - `C₁` writes `r := 7` after its park, or is cancelled while holding the cell.
    - Join, then a second loan after the join, join again, unfold.
- **Headlines.** `crossImmJ`, `crossImmJC`, `crossMutJ` and `crossMutJC`, each `OrDiverges` through
  `poolSchedAdequacyS`, with no hypotheses and the standard axioms. Also `not_mutualWait` and
  `ImmEndAfterResume` refuted.
- **Hardest cases.**
  - The `mut` child's write after its park, and its cancel while holding the cell.
  - For `imm`, the join resumed beside another share of the same lend.

### 9. Kill and fallback

**Kill** if any of these happens:

- a headline needs a hypothesis;
- `HH` needs a barrier or a ban on spawning after a join;
- a premise stands in for `TokPost`;
- one of `updVNm_frame` (stage 1), `erwpX_of_erwp_tok`, or `WF_C`'s preservation along the lifted
  steps is not derived.

The obstruction is then delivered as a configuration at `UpdVNm`, `EndOKX`, `WF_C`, `PoolS` or
`TokPost`.

**Fallback.** The scoped `crossImm`, `crossImmC`, `crossMut` and `crossMutC`, already proved, with
the restriction "cross-task borrows are scoped". Stage 1 stands either way.

### 10. NOT-do (→ STOP)

- A third relation next to `erwp` and `cerwp`, or keeping `cerwp` past its retirement.
- Patching `cerwp`'s `EndC`.
- A barrier join.
- A stand-in hypothesis for acyclicity.
- Opening loans only in the proof.
- A representation of `imm` borrows that depends on whether they cross a task.
- Fields on `Paper/`'s printed `CellU`.
- Editing `erwp`'s definition or the statements of its rules.
- Searching or looping in a clause.
- Handles or owned cells in answers.

### 11. Stage 2 sizes

| module | content | lines |
|---|---|---|
| `SI/TokLift` | `erwpX_of_erwp_tok`, `not_erwp_of_erwpX_tok` | 700 |
| `SI/LendX` | counted `imm` lend, `mut` loan, `ImmEndAfterResume` | 1100 |
| `SI/HandleX` | `[handle]` at `erwpX`, κ cells | 600 |
| `PoolS` | `PoolS`, `TokPost`, registry, moves, progress, `not_mutualWait`, `PoolSchedAdequacyS` | 1600 |
| `PoolHH` | `HH`'s code and `SchedOK` | 1600 |
| `Cross821X` | `rootIJ`, `rootMJ`, the four headlines | 1300 |

That is about 7.0k lines, plus about 0.8k if `CrossProg`/`CrossProgM` are re-proved.

## Literature, and where we depart

- **RustBelt** (Jung et al., POPL 2018, and the lifetime-logic appendix). We take its fractional
  lifetime tokens: ending a lifetime needs `[α]_1`, and shared borrows can be copied freely. We
  depart in three places:
  - shared borrows are Core's `imm` cells, with no borrow box and no accessor;
  - a holder carries the fraction beside its copy, so the `WF_C` clause replaces opening with a
    token;
  - inheritance is `TWNC.immEnd` and `uncapture_world`.
- **Connectivity graphs** (Jacobs, Balzer, Krebbers, POPL 2022). Acyclicity is the invariant. A
  post-order measure suffices because tokens never move up.
- **LinearActris** (POPL 2024). The handle is a one-shot channel. Linearity gives leak freedom
  (no token in garbage forms a handle that is never joined), and `OrDiverges` has its adequacy
  shape.
- **Boyland 2003, and Bornat et al. 2005.** Boyland's fractions are what the tokens use. Bornat
  et al.'s counting permissions were rejected: they need the source to count, while fractions
  split at the borrower (sub-loans).
- **Iris.** The registry is `Auth(Agree)`. Iris's invariants and later modality are not needed.

## Open questions

- **The six `cerwp` headlines:** option (i) chosen. The deletion waits on stage 1's relation
  (below).
- **`CrossProg`/`CrossProgM`:** delete (chosen).
- **`updVNm_frame`.** Derived at `ρ_P = ∅` (`Core/Chain/SI/UpdMask.lean`; stage 1 build, below).
- **`WF_C` at depth** (escrows) and its preservation along lifted steps. Not derived.
- **`C` as a post coordinate**, against the alternative of a table that reads the world. The
  design has not been checked against every table definition.
- **`[handle]` at `erwpX`.** I expect a re-proof rather than a lift.
- **The `Φ` the pool fixes for tasks.**
- **Typing.** `Imm`'s semantic type gains a fraction: copying splits it and releasing puts it in
  garbage. No checker marking is needed. That is fundamental-property work after stage 2.
- **Reading back `7` in `crossMutJ`.**

## Stage 1 build: where it stopped

**Derived** (`Core/Chain/SI/UpdMask.lean`, standard axioms):

- `UpdNm`/`UpdVNm` and their laws: the empty mask is `UpdN`/`UpdVN`, monotone in the mask,
  downward closed, and transitive at the union of the two masks.
- `updVNm_frame`, 6.48 at a mask, by `updVN_frame`'s proof at each unmasked location. The aliasable
  case reads the `imm` clause at the ancestor's location. `MaskShallow M ρ` is this scope's
  `ρ_P = ∅`: every `imm` cell of `ρ`'s flattening at a masked location has the empty witness. It is
  a hypothesis on the two updated resources, and it keeps the ancestor of an unmasked location
  unmasked (`ancestor_unmasked`).

**Not derived: `erwpX_bind`.** `rwpG_compose` composes the first run's `↭` with the second run's,
framed by the first run's garbage. At masks, the composite's mask must contain both runs' masks.
This scope draws a run's mask from its own start and end (change 2), so a lifetime or `xm` that
only the middle holds wholly is in both runs' masks and in neither end's.
`not_endpointMaskCompose` is that configuration at `UpdVNm` (an `xm` at `ℓ` held only in the
middle, `ℓ ↦ mut` at the middle and the end, nothing at the start). The records clause
(change 3, `ps Δ ps′`) composes the same way. Stage 2 needs this case: a lend opened inside a run
holds `[α]_1` at every bind boundary of that segment. I have not verified that `erwpX_bind` itself
fails at this scope's definition. The composite run may have ends other than the composed one.

So `erwpX`'s final form is not fixed, and this stage defines no `erwpX`, `GRes`, `WF_C` or
`TWNX`. It proves no equivalence, rules or adequacy, and deletes nothing. `cerwp` and its modules
stay.

**Routes examined. None is derived, and none is verified as an obstruction.**

- *Mask from the end together with its garbage, with tokens conserved in the run's region.* The
  composite mask then contains both runs' masks. But the (←) half of `erwp_iff_erwpX0` relies on
  `ρ′.G = ∅` giving the empty mask, and garbage holding a minted `[α]_1` would mask `α`'s cells.
- *A side condition on `erwpX_bind`: every lifetime and `xm` the intermediate post holds wholly is
  held wholly by the start.* The `↭` masks then compose. The records clause also needs a record's
  lifetime read at the middle to agree with the start's. `FrameRec` carries no lifetime, so the
  scope's "records whose lifetime is wholly held" needs a definition: `FrameLife` at which world, or
  the tag in `ls`. The lend rule that mints and ends `α` inside one run would prove its own
  composite.
- *Proving the composite at a saturated frame* (the frame holds every spare fraction, so the
  middle can hold wholly only what the start does). This fails for a lifetime carried only beneath
  a `mut` witness of `ρ`. No frame can carry such a lifetime without changing the world.

**Further gaps in the definition, found while working through stage 1 (none built):**

- *The frame's `WF_C` at the end.* Change 4 asks it of `ρ′` and `ρp`, not of the frame. A run that
  mints `[α]_1` at a lifetime the frame carries uncounted leaves a world whose frame the next
  segment's quantifier excludes. `erwpX_frame` also needs it: the inner run's frame is
  `F ● ρ₂`.
- *`erwpX_frame` and `WF_C`'s split.* `WF_C` of `ρ₁ ● ρ₂` does not give `WF_C` of `ρ₂`, because
  the fraction for `ρ₂`'s copy may sit in `ρ₁`. The rule needs the framed part to carry the
  fractions for its own copies.
