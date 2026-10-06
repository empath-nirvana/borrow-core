# P14 Well-bracketing conservativity

## Statement

Proofs that assume well-bracketed control (every call returns before its caller resumes) still hold where the operations a callback can perform preserve well-bracketing.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §3.6, §3.7: no conservativity statement is in done. `WBCore` (tier 1 is well-bracketed by construction) is a proved companion lemma. `ConservativeWB` (today's Core relation embeds into W at row-abortive types, at every index reachable from σ = []) and `EmbedsNil` (the same at the nil index) are the proof device's, since `ConservativeWB` needs `Mono` and `EmbedsNil` has not been checked against OQ-8's clause sets. The every-type form `Conservative` (A7 in full) is beside done. All are stated against today's relation, pinned by hash in `experiments/Targets/Targets/Audit.lean`, so redefining Core cannot meet them by definition. In Lean: `WBCore` is PROVED (`wbCore`); `ConservativeWB`, `EmbedsNil` and `Conservative` are PROVED AT σ=[] (`conservativeWB_core`, `embedsNil_core`, `conservative_core`) and OPEN at W.

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
