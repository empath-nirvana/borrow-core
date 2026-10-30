# P8 Continuation linearity

## Statement

A continuation is used as its qualifier says: a must-resume one exactly once, a cancellable one exactly once by its resume or its cancel. Both are linear.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

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
