# P8 Continuation linearity

## Statement

A continuation is used as its qualifier says: a linear one exactly once, an affine one at most once, with an explicit cancel when it is not used.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §1.5: A's S6 `ContUse`. On every run of a typed program, no continuation is used more often than it was caught, a linear one is never cancelled, and on a complete run at a data answer each is used exactly as often as it was caught; uses are observed from the run's terms (resume and cancel sites). It is in done. The resource half is B4 with B5: B4 frees every cell a cancelled continuation held, and B5 (`ReleasedOnceReuse`) releases each allocation once, location reuse included. On runs that reuse no location, release exactly once is a tautology about runs (`releasedOnceAll`), and `P8a`, which read it at the runs that capture a continuation, is retired. In Lean: `ContUse` is stated, and OPEN at our instance. Its witnesses R1–R4 (`Targets/A/Programs.lean`), which any typing system that types one must fail, are not yet run at our machine. S6's proof route is OQ-50's (RESTRUCTURE §7 Q9).

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
