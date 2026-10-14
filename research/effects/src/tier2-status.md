# Tier 2: status (shelved 2026-10-12)

> Superseded as the plan by [the separate problems](tier2-problems.md), which splits tier 2 into
> problems A–E. This page keeps the earlier findings.

**Tier 2** is a suspension (a continuation, a generator, an effectful object) that holds a borrow
across a stop. Today T1 refuses it (`Row.Unwind` on borrow callbacks).

**Status: open research, shelved on purpose.** Restart from this page, not from the branch.
Tier 2 stays a goal.

## Established (machine-checked)

- **Core's relation reads where lifetimes sit.** Its `∀` over lifetimes distinguishes a cell
  adjacent to the bound from one with room below it (`coreAllAdjacent`, `coreAllNotNatural`,
  `experiments/ProbeD1/ProbeD1/GapWitness.lean`).
- **Moving a suspended region's lifetimes breaks the relation.** This holds for re-instantiating
  internal lifetimes in general (`not_coreThawTop`, `BridgeProbe.lean`). It also holds for
  shifting a whole top segment at once, at every cut (`segShiftFailsAtEveryCut`, `SegShift.lean`).
  The gap that breaks it is where the resumer's own lends sit.
- **A plain thunk already cannot outlive a borrow it holds** (`thunk_not_outlives`). The
  "external lifetime" half of a lifetime-bounded suspension type therefore adds nothing.
- **ProbeD1's draft world** (a lend stack in every borrow callback's `∀`) never reproduced the
  borrow-only programs Core already accepts. Grounding found twelve divergences (`LEDGER.md`).
  Abandoned. Archived on branch `targets` (`d52f124`).

## Learned about the programs

| program | what it needs |
|---|---|
| `gen-adapters-io`, `gen-digits`, `gen-lazy`, `gen-lines` | no borrow at all. The iterator owns the capability; the blocker is K3 (a cancel that hands back an owned value) |
| `gen-self-borrow`, `for-lend-resumes` | the lends are internal; first-order fixes exist (ending the lend at the stop and re-lending), but they are **rejected as hacks** (nth order or nothing) |
| the reader object (`Log` handled outside the counter's lend) | a value derived from an internal borrow, live at a stop. **Genuinely hard** |
| lending iterators (yield a borrow of the generator's own state) | an internal lifetime escapes in an operation payload. **Genuinely hard** |
| `async-borrow` | tasks over a borrowed list, awaited before the lend ends |

## Refuted or abandoned approaches (do not retry without new evidence)

- a new relation with a lend stack in every `∀` (ProbeD1);
- one former `U@'a` plus a freeze binder (`BRIDGE.md`);
- packing the region's top segment and re-pushing it (`SegShift.lean`);
- "the cut-based `∀` already solves resumption": it held only inside ProbeD1's world.

## Unknown

- What the semantics of a suspension holding a borrow should be, in general (nth order).
- Whether interpreting the lifetime `∀` parametrically suffices.
  - That reading is unobservable only under premises (`foundations/interaction-algebra.md`
    §4.2), and lending iterators break PL1.
  - Not derived; no obstruction verified.

## Leads (from the 2026-10-12 survey, [prior-art/landing.md](prior-art/landing.md) §4)

- **The lifetime carrier is not settled.** Only the fundamental property, adequacy and the borrow
  guarantees are. A dense order would make adjacency undefinable (N15), but our construction
  recurses down `⊏`. First test: rebuild `GapWitness` over a dense carrier, recursing over the
  lifetimes in play.
- **Invalidation at the cut.** Internal borrows cannot be touched while suspended; borrows
  crossing in payloads (lending iterators) are invalidated by resuming. Anchor: the loan-set
  models (Oxide, Polonius, LLBC; paper proofs, a fine basis to transcribe; the gap is no
  closures or async).
- **Scoped tasks** via linear continuations (Swift's escape from the trilemma).
- **Resume versus cancel** when a consumer of a lent value aborts (Swift SE-0474).

## How to restart

1. **Finish part 1 first** (`foundations/effects-algebra.md`): the effect theory, stated and
   settled at Core.
2. **Start from models that solved a neighbouring problem:**
   - **Hazel** (de Vilhena and Pottier, POPL 2021): one-shot continuations that capture
     separation-logic resources.
   - **RustBelt's lifetime logic:** lifetimes as abstract tokens with inclusion, not as positions.

   Ask what *their* model of a lifetime would do with the adjacency problem.
3. **Test programs:** the reader object, a lending iterator, `async-borrow`, and a nested
   suspending callback.
4. **Rules:**
   - conservativity first (the relation agrees with Core on programs where no lend spans a stop);
   - a regression suite that can fail;
   - stop after two successive patches.

## Proposal (2026-10-12, not decided): no internal borrows across a suspension

A lend opened inside a suspendable computation must be returned before its next suspension
point. Lending is free between suspensions. Borrows from outside may be held across suspensions.
Lends end at last use (non-lexical), not only at block end.

This is today's T1 plus checker ergonomics, and it would make tier 2 *excluded by design for
now*. Evidence: [prior-art/no-borrows-across-suspension.md](prior-art/no-borrows-across-suspension.md).
- No passing program is newly rejected; all pending programs are blocked by other things.
- Non-lexical ending newly accepts `gen-self-borrow` and `lend-let-used`.
- C# 13 has nearly this rule.

What it costs:
- **Main loss:** a lazy generator over a borrowed linked structure. Each pointer hop is a
  `withload` at a shorter lifetime (`imm_view_rejected`). Its push-form fix needs K4 (effectful
  fold constants).
- Concurrent children sharing a parent's local.
- Lending-iterator adapter composition.
- Correction to the proposal's premise: a `for` over a stored generator inside a borrow block is
  rejected (SPEC §14).

**Status:** recorded as a proposal only; revisit after as much of tier 1 as possible has landed
in the kernel. K4 should be weighed in the tier-1 work, with "traverse a borrowed tree lazily" as
its acceptance program.
