# Tier 2: status (shelved 2026-10-12)

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
