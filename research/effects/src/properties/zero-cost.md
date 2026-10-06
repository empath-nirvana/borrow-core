# P13 Zero-cost lowering

## Statement

Each lowering class preserves behaviour:
- an answering handler is a direct call;
- an abortive clause is a branch;
- a suspension is a state machine.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §1.7: A₃'s `LoweringCorrect` (the lowered program observes exactly what the source does) and `ZeroCost` (on the corpus of terminating (E) programs, each lowered program allocates and dispatches no more than its fixed hand-written reference), over a fixed first-order target `Tgt` defined in A, in which no instruction captures, saves, restores or searches a stack, so erasure is structural. Out of the first pass; OQ-23 asks whether it is a theorem. The driven programs are not in the corpus. In Lean: both are stated (`Targets/A/Lowering.lean`); the reference programs themselves are not written, so `refCost` (zero at every entry) is unchecked; `LowClass` names the backend's lowering classes. OPEN.

## Why it matters

Koka; Effekt; the user's erasure requirement.

## Design space

- **A theorem** relating source and lowered runs (OQ-23).
- **Per-class laws plus corpus counts.**

## Evidence

The lowering is built, compiles and runs. The corpus parity counts exist.

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Placement of frozen frames gives Pin for free (see [Freeze as a binder](../foundations/freeze-binder.md)).

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
