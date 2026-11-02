# #770 target structure: borrows and linear resources across suspensions

Status: draft for review, 2026-11-01. Nothing here is built against yet.
Inputs: `evidence.md`, `conditions.md`, branches `reb-canon` (head 18b15971) and `forest`.

## 1. The target theorem

For every closed, well-typed Core program `P` (including handlers that store one-shot continuations, borrows live across suspensions, and borrows shared with spawned tasks):

> `OrDiverges P`: every reachable configuration is a value or steps; a value is reached only at the empty memory; every `free` finds its cell.

It is proved through **one** step-indexed linear relation: `fundamentalC` (every typing rule is compatible) followed by adequacy. Termination is not claimed. Totality results stay with the existing total relation, for the derivations that don't use the new rules (§7).

Done means that theorem. Passing test programs doesn't count.

## 2. What is settled (proved, reusable as is)

| Piece | What it gives | Where |
|---|---|---|
| Step-indexed linear `ewp`/`erwp`, `[handle]` with no `hdv` | stored κ around unbounded loops | `SI/Ewp`, `SI/HandleN` |
| Effectful destructors on every exit | raise, cancel, early loop close, performing destructors | stages 1–8, `FinCancelN`, `FinPerformN` |
| Index-relative mut cells (`UpdMutN`), 6.48 / 6.59 at the index | mut payloads under step-indexing | `UpdN`, `RebN` |
| Canonical images (`TWNC`, `TemplAt`, `TemplDAt`) | shared reborrows (root and deep) can't disagree | `TWNC`, `CanonDeep` |
| `extF` + `LinDisj`/`DLinDisj`/`EscEx`, and `ext_extF` | where κ may resume; no restriction relative to Core's `Ext` | `ExtF`, `LinDisj`, `ExtExtF` |
| Same-task frames across stops | mut/imm lend, reborrow, deep reborrow, Anti-Frame, cancel/raise variants | `StopFrameN`, `IStopN`, `RebAcrossC`, `RebStopD`, `AntiStopN` |
| Capture as its own operation (`crwpG`/`cerwp`), `CactusInv` and its preservation | owned records per computation, no garbage, scoped join | `Capture*`, `CactusInv` (proof of concept) |

## 3. One relation

There are two relations today: `erwp`, where a stop is treated like a return and the lend is folded, and `cerwp`, where capture is its own operation. **Decision needed: `cerwp`'s design becomes the relation, and `erwp`'s rules become instances of it.** For that it must:

1. **Restore abortive stops.** Raises under a live borrow worked at `erwp` and don't at `cerwp`. That's a regression, and it has to be undone.
2. **Allow unrestricted (multi-shot-capable) entries whose share owns nothing.** This is the principled form of condition 1 in `conditions.md`.
3. **Make same-task frames instances of capture.** The fold-at-stop is capture of a one-frame branch, and re-lend is graft. Today they are separate proofs.
4. **Keep handler forwarding** (operations passing outward through `[handle]`).
5. Restore `↭` at stops where a lender needs it, or show that no lender does.

Open question: are the table fields `fd` (resumer guarantee), `PBv` (payload-dependent answer) and `oc` (owned records) principled? Each must be supplied by a typing rule (§5) or removed.

## 4. The cactus invariant carries the proofs

State `CactusInv` once, over all computations: running, stored in a κ, or spawned. Each owns its resources and its frame records, pairwise disjoint. Imm views are duplicable. The world is `TWNC`/`Tagged`, and it lowers to memory.

The operations, each proved to preserve it:
- **step** of the running computation;
- **capture:** a branch, with its live lends' records, goes into a one-shot κ;
- **graft:** resuming κ attaches its branch, possibly under frames opened since, or under another parent;
- **unwind:** cancel or raise runs a branch's destructors and ends its lends in order;
- **spawn / join:** a lend's record is shared into children, and passes back at the join. A shared lend ends only at a join (scoped spawn).

**Adequacy is derived from preservation** (LinearActris Thm 5.4 shape), and frame rules are corollaries of these operations. A proof that goes around the invariant (as the cross-task tests did) is not the target.

Threads: keep the invariant per computation. The two known dependencies on sequential scheduling (a frame fixed for a whole segment; `JoinReady` read at the resume instant) are listed and kept separate, so a CSL reading can replace them later.

## 5. What the types must carry

The open conditions are facts about distant code (where κ is resumed, what the handler holds, when children end). They must reach the typing rules as local facts:

- **Operation signatures:** qualifier (`lin` / `cancel` / `unr`), what payload and answer own, and their lifetimes relative to live borrows. That's conditions 3 and 4.
- **Continuation and task lifetimes** (the parked `Task@a` idea): a continuation or task holding borrows at `a` may only be stored somewhere scoped within `a`. Spawn takes a scope, and join ends it. Hypothesis: this one rule supplies `fd`, `oc` and the scoping, and subsumes the per-table conditions.
- **Unrestricted operations:** allowed under a live borrow only when everything live is duplicable. That's restricted multi-shot, which is an opening and not a goal.

Each condition in `conditions.md` gets a row: which typing rule supplies it, or which side condition Core lacks.

## 6. The fundamental theorem

Over the single relation:
1. `Row.tabN`, then 𝒱/𝒞 for every type: Imm, Mut (`vMut`), boxes, lifetimes, thunks (`vThunk`/`Covers`), μ, ν, ∀, type variables, families, opaque types, κ and task types carrying §5's information. All downward closed.
2. `SemJ`, then compatibility for every `CDerives` rule (about 105). The new rules are lend/reborrow/Anti-Frame across stops, spawn/join, and `[handle]` without `hdv`.
3. Adequacy to `OrDiverges` via §4.

Re-establishing Core's plain results at `TWNC` is part of step 2 (four world-building sites have no counterpart yet).

## 7. Termination

The step-indexed relation proves safety only. The total relation (`cC`, `Closing`, `total_every_run`) keeps covering the derivations that don't use the new rules. One open item: decide whether the new `[handle]` gets a total variant (with `hdv`) for programs that should be shown total.

## 8. Tests that exercise the invariant

Each test must go through §4, not around it:
- several children sharing an imm lend; one child holding a mut lend that writes;
- nested scopes; a child that spawns;
- the parent cancelled while its scope is open; a child cancelled; a raise under a live shared borrow;
- a loop: lend, spawn, join on every turn, under a storing scheduler, an unbounded run, no fuel;
- a forwarding handler between the task and the scheduler;
- later: multi-shot κ over duplicable state.

## 9. Outside this structure (tracked, not solved here)

- Core gaps: an inline-field projection for Imm/Mut; value-type polymorphism; arrays and `foldImm` across stops; `withswap` with a callback that stops.
- The recorded unreconciled point on 6.150.
- Lowering: per-task state machines, self-reference (pinning or a movability mode), per-state drop glue.
- Threads: a concurrent semantics and the multi-thread adequacy.

## 10. Not doing / tempting shortcuts (stop and report)

- Adding a field or condition to an operation table to make a test pass. Every condition traces to §4's operations or §5's types.
- A second relation for a new case. Extend the one relation.
- Tests with a fixed sequence of events and no loop presented as "no fuel".
- Proving a lemma about the invariant and then proving the tests without it.
- Restricting programs (unique-image types, segmentation, no borrows across suspensions) without showing nothing needed is lost.
- Calling an open item "the remaining thing".

## 11. Answers to the three questions earlier drafts left open

1. **`cerwp`'s design is the single relation.** The forest spike located the root cause: `rwpG` reads a stop as a return, and that is what forces the fold. Keeping that reading means keeping its workarounds. Conditions: §3's items 1–5.
2. **Continuation and task types carry lifetimes.** The open conditions are facts about distant code (§5), and modular checking needs them local, so the type of the thing that crosses the distance has to carry them. BoLo already has lifetimes in types, and Rust (`Future + 'a`) and Schuster et al. (region-typed continuations) do the same. Whether this one rule subsumes the per-table conditions is a hypothesis for §6 to test.
3. **No new total variant.** Programs that use `Div` rows or stored κ around loops aren't total, so a total rule for them proves nothing. The existing total relation and its `[handle]` (with `hdv`) stay for derivations that don't use the new rules, which keeps the compiler's totality facts (`total_open`/`total_call`/`total_subrun`) where they already hold. Two relations for two properties (safety, termination) is not the "second relation for a new case" in §10.
