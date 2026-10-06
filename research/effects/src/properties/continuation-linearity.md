# P8 Continuation linearity

## Statement

A continuation is used as its qualifier says: a linear one exactly once, an affine one at most once, with an explicit cancel when it is not used.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) (§6, P8). The resource half is not a separate target: it is T1's `Targets.ReleasedOnceAll` (exactly-once release on every complete run), read at the runs that capture a continuation. The use count, the property proper, is not stated: the machine does not observe a continuation's use, and how to observe it is OQ-50. It is beside done. In Lean: `Targets.P8a`, which is `Targets.ReleasedOnceAll` (`Statements/Linearity.lean`): PROVED at every typing system (`releasedOnceAll`), because its run premises carry the empty memory at the start and `Final` at the end, so its typing content is T1's `Terminates`. P8.b is named-only (OQ-50): OPEN.

## Why it matters

Survey A3 and T4; Tang et al. 2024; Affect.

## Design space

- **The lattice of multiplicities** ({0}, {1}, [0,1]), which is not a chain.
- **Grades on captured context.**
- Multi-shot is ignored ([decided constraints](../decisions.md)).

## Evidence

The qualifiers, `contShare`, `KapRel`, `[let]`/`[then]` premises (Core σ=[]).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Graded algebraicity must justify the grade premise.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
