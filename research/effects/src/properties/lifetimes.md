# P9 Lifetime soundness

## Statement

No capability is used outside its handler's extent, and no continuation is resumed after a lifetime it holds a loan from has ended.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §2.2: B7 `LifetimeSound`, in `B.Guarantees`, at the typing system's own outlives judgements (`J.out`, OQ-28), which every typing rule's transcription reads; over Core's types, so in done at `⟦J₂⟧`'s `∀`-free judgements. Stated at W only: the machine does not see a use past a lend's end. In Lean: `LifetimeSound coreB OutJ.core` is PROVED AT σ=[] (`lifetimeSound_core`), OPEN at W.

## Why it matters

Survey A4. System C; Osvald et al. 2016; capture sets (Boruch-Gruszecki et al.; System Capless in Lean 4).

## Design space

- **Second-class `resume`:** the property reduces to escape analysis.
- **Boxed continuations** with a bound `[@c]`.
- **Whether a handler site opens a lifetime** (OQ-3).

## Evidence

6.60 (`vC_outlives`, `vC_outlivesLe`); `Row.Unwind`'s outlives conjunct; `ewp_box_end` (Core σ=[]).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

The outlives judgment has no rule at `U C`.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
