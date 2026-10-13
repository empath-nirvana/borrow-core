# P3 I1: a suspension is a value

## Statement

A suspended computation (a continuation) is a value of the resource world. It can be passed, stored and dropped like any owned thing, and its semantic type is well defined.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §3.2: in done, E9 (a continuation stored and resumed after its handler returned) and E1′ (a real suspension, resumed after its handler returned), with the program-level corollary `I1Prog` (stored suspensions: `storeCancel`, AT17). The world-level `I1` is the proof device's, beside done. In Lean: `I1 coreW` is PROVED AT σ=[] (`i1_core`); `I1Prog` follows from the combined theorem at `c = .any` (`i1Prog_of_combined`); E1′ and E9 at our instance are OPEN.

## Why it matters

Survey A1 ("Σ must type continuation values and the loans they hold"); System C's boxing; Affect.

## Design space

- **Second-class only:** cannot be stored.
- **Boxed first-class with a lifetime bound:** the `[gen]` rule, or an outlives rule at `U C` (OQ-28).
- **Freeze as a binder** over its internal locations, lifetimes and instances ([Freeze as a binder](../foundations/freeze-binder.md)).

## Evidence

`ewp_gen` (L14.3) on `lift-stage1` (Core σ=[]); the affine closure as ν codata (`Core/Aff.lean`, positivity only).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Second-class is cheap but cannot express a scheduler. Boxing needs a bound, and today no resource-holding `U C` has an outlives rule.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
