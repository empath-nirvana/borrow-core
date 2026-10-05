# P5 I3: drop finalises exactly once

## Statement

Dropping a suspended computation is a cancel. It runs every finaliser of the frozen frames exactly once, LIFO, and ends every lend it holds.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Survey A6 and T6. Voigt et al. 2025; Ahman–Bauer 2020; Congard et al. 2026. In an affine core this is hard (Koka "conjecture[s]" it). In a linear core it is a theorem shape.

## Design space

- **The interception policy:** can code inside the continuation catch the cancel? SPEC §19 as built is the decision.
- **Finaliser rows:** abort-only today (OQ-7).

## Evidence

`cancelTab`, `cancelOwed`, `ewp_kappa_cancel`, `ewp_cancel_absorb`; both cancel outcomes in `Core/EffCancel.lean` (Core σ=[]).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Linearity makes this tractable. See [Linearity, not affinity](../foundations/linearity.md).

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
