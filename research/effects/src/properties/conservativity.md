# P14 Well-bracketing conservativity

## Statement

Proofs that assume well-bracketed control (every call returns before its caller resumes) still hold where the operations a callback can perform preserve well-bracketing.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Survey A7; Dreyer–Neis–Birkedal 2010; Timany–Guéneau–Birkedal 2024.

## Design space

- **Tier 1:** keep T1, so well-bracketing holds by construction.
- **Tier 2:** state what is given up, and for which operation classes.

## Evidence

T1, the lexical stop at `Core/EffDefs.lean:40` (Core σ=[]).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Linearity removes the leak half of A7 (no `forget`).

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
