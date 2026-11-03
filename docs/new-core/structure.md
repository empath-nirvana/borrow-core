# The new Core: target structure

The structure SPEC §62 is built against, and its rules. Lean names and branches are in
`evidence.md`; conditions and gaps, numbered, in `conditions.md`.

## 1. The target theorem

For every closed, well-typed Core program `P` (including handlers that store one-shot
continuations, borrows live across suspensions, and borrows shared with spawned tasks):

> `OrDiverges P`: every reachable configuration is a value or steps; a value is reached only at
> the empty memory; every `free` finds its cell.

To be proved through **one** step-indexed linear relation: `fundamentalC` (every typing rule is
compatible) followed by adequacy. Termination is not claimed. Totality results stay with the
existing total relation, for the derivations that don't use the new rules (§8).

Done means that theorem. Passing test programs doesn't count.

## 2. What is proved and reused as is

| Piece | What it gives | Where |
|---|---|---|
| Step-indexed linear `ewp`/`erwp`, `[handle]` with no `hdv` | stored κ around unbounded loops | `SI/Ewp`, `SI/HandleN` |
| Effectful destructors on every exit | raise, cancel, early loop close, performing destructors | `Core/LetDtor*` (library); `FinCancelN`, `FinPerformN` |
| Index-relative `mut` cells (`UpdMutN`), 6.48 / 6.59 at the index | `mut` payloads under step-indexing | `UpdN`, `RebN` |
| Canonical images (`TWNC`, `TemplAt`, `TemplDAt`) | shared reborrows (root and deep) can't disagree; Core's results over them (`Core.C`, not `Core.Stdio`) | `TWNC`, `CanonDeep`, `CoreC` |
| `extF` + `LinDisj`/`DLinDisj`/`EscEx`, and `ext_extF` | where κ may resume; no restriction relative to Core's `Ext` | `ExtF`, `LinDisj`, `ExtExtF` |
| `extFT` and `ext_extFT` over the tree | where κ may resume at the tree world; no restriction relative to `ExtLT` (Core's `Ext` over the tree carrier), with `TWNT.exclUnique` in place of `LinDisj`/`DLinDisj`/`EscEx` | library: `Tree/World/ExtF`, `Tree/World/ExtExtF` |
| Same-task frames across stops | `mut`/`imm` lend, reborrow, deep reborrow, Anti-Frame, cancel/raise variants | `StopFrameN`, `IStopN`, `RebAcrossC`, `RebStopD`, `AntiStopN` |
| Capture as its own operation (`crwpG`/`cerwp`) | owned records per computation, no garbage, scoped join (the rules over any body; the programs `CrossProg`/`CrossProgM` with one child and a fixed order of events) | `Capture*`, `CrossProg*` |
| The tree order, the antichain carrier, re-reading | §4 | `Tree/` |
| The resume condition at every type, from the branch hypotheses (`hbr`, `hnα`) | `joinFd_of_branch`, `TWNC.noOwnUnder` | `Tree/JoinFd`, `Tree/NoOwnUnder` |

Stated but not yet used by any proof: `CactusInv` and its preservation lemmas (§5).

## 3. One relation

There are two relations: `erwp`, where a stop is treated like a return and the lend is folded,
and `cerwp`, where capture is its own operation. `cerwp`'s design becomes the relation, and
`erwp`'s rules become instances of it. The reason: `rwpG` reads a stop as a return, and that
reading is what forces the fold (the `forest` spike); keeping the reading keeps its workarounds.
For that the relation must:

1. **Restore abortive stops.** Raises under a live borrow hold at `erwp` and not yet at `cerwp`.
2. **Allow unrestricted (multi-shot-capable) entries whose share owns nothing** (condition 1).
3. **Make same-task frames instances of capture.** The fold-at-stop is capture of a one-frame
   branch, and re-lend is graft.
4. **Keep handler forwarding** (operations passing outward through `[handle]`).
5. Restore `↭` at stops where a lender needs it, or show that no lender does.

The relation is read over the tree world of §4 (`cerwpT`, `Core/TreeWpEff.lean`), with frame
records, `TWNT` and `TaggedT` (condition 21).

Open: are the table fields `fd` (resumer guarantee), `PBv` (payload-dependent answer) and `oc`
(owned records) principled? Each must be supplied by a typing rule (§6) or removed.

## 4. Lifetimes as a tree; the carrier; re-reading

**The tree order.** Lifetimes form a well-founded cactus. A fresh lifetime is a child of the
current branch's innermost one; siblings are incomparable. A graft whose capture point is above its
resume point adds order facts and removes none (`graft_mono`), so a stored branch grafted under a
newer lend has its lifetimes below that lend. The single chain is the case with one branch. Every
use of comparability in the closure `Tree/ChainUses.lean` scans falls into one of five classes
(`Tree/Comparability.lean`): the carrier's strata and cell operations; `↓α` as a covering child;
a lifetime chosen below two bounds, on a branch; a lifetime below the whole world, replaced by
premises read at one record; and `⊓ᾱ ∈ ᾱ` used to get a member. Two uses lie outside the scan
(condition 18).

**The antichain carrier.** Strata are indexed by finite sets of lifetimes, `Res_S` the
intersection of the members' strata. A combined `mut` cell carries an antichain:
`mut(β̄₁) ○ mut(β̄₂) = mut(min(β̄₁ ∪ β̄₂), …)`, which needs no stratum common to cousins. At the
chain it is the printed carrier (`chainEquiv`, with `✓`, `#` and flattening agreeing along it).
A valid world stays valid, carried, across a graft, with no renaming.

**Re-reading.** Semantic types are read at the current tree. A `mut` cell's invariant is its store
type read at the current tree, re-read when the tree grows (`reread`), not a fixed predicate:
a cell carried unchanged by `trU` is not a value of this `Mut` (`trU_not_kmono`). Store types are syntactic
codes read at the tree; the store typing grows at allocation and a location keeps its type
(condition 16). The relation's value types (`STy`, `Core/TreeSem.lean`) read the record list and
are downward closed and monotone along the tree and `KeepRel` for every former, `Mut` only at a
store-code payload (E1, #790), continuation and task types included (`Core/TreeSemK.lean`: a
captured `κ` is a value of its type); the computation types (`SCmp`, `Core/TreeSemC.lean`) are
downward closed, `F A` is Kripke along `KeepRel`, and they reach values under `U`. Effect rows
(`CTy.eff`) have no `SCmp` former yet (`docs/new-core/scope-782.md`).

## 5. The cactus invariant carries the proofs

State the invariant once, over all computations: running, stored in a κ, or spawned. Each owns
its resources and its frame records, pairwise disjoint. Imm views are duplicable. The world lowers
to memory.

The operations, each to be proved to preserve it:
- **step** of the running computation;
- **capture:** a branch, with its live lends' records, goes into a one-shot κ;
- **graft:** resuming κ attaches its branch, possibly under frames opened since, or under another
  parent; the tree grows and every branch is re-read;
- **unwind:** cancel or raise runs a branch's destructors and ends its lends in order;
- **spawn / join:** a lend's record is shared into children and passes back at the join.

**Adequacy is derived from preservation** (LinearActris Thm 5.4 shape), and the frame rules are
instances of these operations. A proof that goes around the invariant is not the target.

Status: `CactusInv` is stated with `cactus_step`, `cactus_move`, `joinReady_fd`, and not yet used.
Over the tree world (`Core/TreeCactus.lean`), `CactusInvT` is kept by step, growth, move, spawn and
join, and `cerwpT_adequacy` is derived through `cactusT_step` at one branch, with no programs. Open:
adequacy over several branches from preservation; adequacy at the relation the typing rules use;
the frame rules as instances of capture (condition 20).

Threads: the invariant is per computation. The two dependencies on sequential scheduling (a frame
fixed for a whole segment; `JoinReady` read at the resume) are kept separate, so a concurrent
separation logic reading can replace them (condition 19).

## 6. What the types and the invariant must carry

The open conditions are facts about distant code (where κ is resumed, what the handler holds, when
children end). They reach the typing rules as local facts, or are carried by the invariant:

- **Operation signatures:** qualifier (`lin` / `cancel` / `unr`), what payload and answer own,
  and their lifetimes relative to live borrows (conditions 3 and 4; not derived).
- **The resume condition from the branch invariant.** When a lend ends in a resumed segment,
  nothing outside the segment may hold its location. At the type `Imm 'r 1` the tree order
  supplies it (`fdFromLifetimeTypesT`). Types alone do not: not at `Imm 'r 1` in a single chain
  (`not_fdFromLifetimeTypes`), and not at closure types, which name no lifetime
  (`not_fdFromThunkTypesT`). At every type it is reduced to the branch hypotheses
  (`joinFd_of_branch`, with `TWNC.noOwnUnder`); over the tree world it holds at a join
  (`fdEsc_at_join`), other branches' steps keep it (`stepKeepsFdEsc`), and a lend's end is valid
  only when it holds (`r2_endBlockedByHolder`, `r3_joinEndNeedsFdEsc`) (condition 23).
- **Scoped spawn.** A lend shared across tasks ends only at a join. A branch resumed from a join
  asks that no other branch's flattening hold the joined location (`JoinReady`), which gives the
  resumer's frame condition (`joinFd`, `joinReady_fd`); it holds once every branch that held a
  borrow of the location has finished or been cancelled and handed its borrows to the joiner.
- **Unrestricted operations:** excluded while a borrow or owned resource is live, because a live
  lend folds an exclusive cell into the continuation's share, and an unrestricted continuation
  resumed twice would lend twice (argued); its share owning nothing is a clause of the share's
  definition (`contShareN`). Multi-shot continuations over duplicable state are a
  hypothesis, not a rule.

Each condition in `conditions.md` gets a row: which typing rule supplies it, or which side
condition Core lacks.

## 7. The fundamental theorem

Over the single relation:
1. `Row.tabN`, then 𝒱/𝒞 for every type: Imm, Mut (`vMut`), boxes, lifetimes, thunks
   (`vThunk`/`Covers`), μ, ν, ∀, type variables, families, opaque types, κ and task types. All
   downward closed and monotone along the tree. Done at the tree (`STy`, `SCmp`, κ and task
   types, `Core/TreeSem.lean`, `Core/TreeSemC.lean`, `Core/TreeSemK.lean`) for every former but
   `Mut` at a payload that is not a store code (#790) and effect rows (`CTy.eff`).
2. `SemJ`, then compatibility for every `CDerives` rule. The new rules are lend/reborrow/Anti-Frame
   across stops, spawn/join, `[let-dtor]`, and `[handle]` without `hdv`.
3. Adequacy to `OrDiverges` via §5.

Core's plain results over canonical worlds are `Core.C` (condition 8); over the tree world they
are part of step 2.

## 8. Termination

The step-indexed relation proves safety only. The total relation (`cC`, `Closing`,
`total_every_run`) keeps covering the derivations that don't use the new rules, with its
`[handle]` (with `hdv`), which keeps the compiler's totality facts
(`total_open`/`total_call`/`total_subrun`) where they hold. No total variant of the new rules:
programs that use `Div` rows or stored κ around loops aren't total, so a total rule for them
proves nothing. Two relations for two properties (safety, termination) is not the "second relation
for a new case" of §11.

## 9. Tests that exercise the invariant

Each test must go through §5, not around it:
- several children sharing an `imm` lend; one child holding a `mut` lend that writes;
- nested scopes; a child that spawns;
- the parent cancelled while its scope is open; a child cancelled; a raise under a live shared
  borrow;
- a loop: lend, spawn, join on every turn, under a storing scheduler, an unbounded run, no fuel;
- a forwarding handler between the task and the scheduler.

## 10. Outside this structure (tracked, not solved here)

- Core gaps: an inline-field projection for Imm/Mut; value-type polymorphism; arrays and
  `foldImm` across stops; `withswap` with a callback that stops.
- The recorded unreconciled point on 6.150.
- Lowering: per-task state machines, self-reference (pinning or a movability mode), per-state
  drop glue.
- Threads: a concurrent semantics and the multi-thread adequacy.

## 11. Not doing / tempting shortcuts (stop and report)

- Adding a field or condition to an operation table to make a test pass. Every condition traces
  to §5's operations or §6's types.
- A second relation for a new case. Extend the one relation.
- Tests with a fixed sequence of events and no loop presented as "no fuel".
- Proving a lemma about the invariant and then proving the tests without it.
- Restricting programs (unique-image types, segmentation, no borrows across suspensions) without
  showing nothing needed is lost.
- Calling an open item "the remaining thing".
