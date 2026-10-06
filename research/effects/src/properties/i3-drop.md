# P5 I3: drop finalises exactly once

## Statement

Dropping a suspended computation is a cancel. It runs every finaliser of the frozen frames exactly once, LIFO, and ends every lend it holds.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §3.2, §3.7. In done, dropping a suspended computation is A's S5 `Cancellation`: a cancel fires the frozen finalisers innermost first, each once, keeps the first outside error and suppresses the region's own, and nothing intercepts it (`NoIntercept`, `UnwindOrder`). E7 and E9c observe each fire and end in their traces. B4 with B5 releases the memory a cancelled continuation held. The world-level preservation conjunct `I3` (`ShareCancel`, with an option-neutral closing clause: the cancel leaves nothing newly held) is the proof device's, beside done. "Ends every lend it holds" needs OQ-57's accounting of which held frames a continuation froze; `CancelCloses` is named-only until then. None claims termination. In Lean: S5 at our instance is OPEN (the bridges `noIntercept_of_core`, `unwindOrder_of_core` are not built). Its routes at Core are Core's `NoInterception tier1`, PROVED AT σ=[] (`noInterception_tier1`), and Core's `FinaliserOrder`, OPEN, with its two-frame unwind run proved (`two_frame`). `I3 coreW` is PROVED AT σ=[] (`i3_core`). `CancelCloses` is named-only.

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
