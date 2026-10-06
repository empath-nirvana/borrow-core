# P14 Well-bracketing conservativity

## Statement

Proofs that assume well-bracketed control (every call returns before its caller resumes) still hold where the operations a callback can perform preserve well-bracketing.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.WBCore` and `Targets.ConservativeWB` (§6, P14), the latter a conjunct of done: today's Core relation embeds into W at the types whose callbacks perform only `{fn, abort}` operations (row-abortive types), at every index reachable from σ = []. It is stated against today's relation, pinned by an audit, so redefining Core cannot meet it by definition. The every-type form `Targets.Conservative` (A7 in full) is beside done. In Lean: `Targets.WBCore` is PROVED (`wbCore`); `Targets.ConservativeWB` and `Targets.Conservative` are PROVED AT σ=[] at `coreW` (`conservativeWB_core`, `conservative_core`) and OPEN at W. Core's relation is pinned by hash in `experiments/Targets/Targets/Audit.lean`.

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
