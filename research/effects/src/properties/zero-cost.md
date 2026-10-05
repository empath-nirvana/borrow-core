# P13 Zero-cost lowering

## Statement

Each lowering class preserves behaviour:
- an answering handler is a direct call;
- an abortive clause is a branch;
- a suspension is a state machine.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

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
