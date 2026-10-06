# P5 I3: drop finalises exactly once

## Statement

Dropping a suspended computation is a cancel. It runs every finaliser of the frozen frames exactly once, LIFO, and ends every lend it holds.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.I3` (§5), the preservation conjunct for drop: `ShareCancel`, the share's cancel conjunct at W, with an option-neutral closing clause (the cancel leaves nothing newly held). "Ends every lend it holds" needs OQ-57's accounting of which held frames a continuation froze; `CancelCloses` is named-only beside done until then, and its program-level form is in done (`CancelOrder` fires the lender's finaliser, `ReleasedOnceAll` releases its memory once). The finaliser order over complete cancel and unwind runs is `Targets.FinaliserOrder` (its unwind run checked on two frames whose inner finaliser raises), and `Targets.NoInterception` excludes intercepting a cancel. None claims termination. In Lean: `Targets.I3` is PROVED AT A RESTRICTION at Core σ=[] (`i3_core`: nothing is held, so the closing clause is vacuous); `Targets.NoInterception` is PROVED AT σ=[] (`noInterception_tier1`); `Targets.FinaliserOrder` is OPEN, its two-frame unwind run proved (`two_frame`); `CancelCloses` is named-only.

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
