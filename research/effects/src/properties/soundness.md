# P1 The combined theorem

## Statement

For every well-typed program, run under every allocator and every platform environment that respects its protocol, every run:
- never gets stuck: no use after free, no bad access;
- never stops at an operation outside its row;
- ends with memory empty except for the result's own resources;
- runs every finaliser exactly once, LIFO, on return, unwind and cancel.

Termination holds only for types without divergence. Tier 1 and tier 2 are the same theorem over different typing rules.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

BoLo's adequacy theorem with the effect conjuncts added. Literature: Bauer–Pretnar 2014; System C; Affect 2025; Tang et al. 2024. Survey A1, A2 and A6.

## Design space

- **Closed programs, or relative to the platform.** Platform operations (I/O, allocation) make relative adequacy necessary for real programs. The platform is a comodel or runner, and the theorem quantifies over all of them.
- **How it is proved: semantic** (our route, BoLo's logical relation without step-indexing) or **syntactic** (progress and preservation).

## Evidence

`fundamentalC` (`Core/Fundamental.lean:434`); `adequacyD`, `adequacyD_safe` (`Core/Demonic.lean:312, 325`); `adequacyD_obs` (`Core/EffPrograms.lean:41`); `reclaim`; the totality theorems. All at Core σ=[].

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Aliasing-xor-mutation is an invariant of the model, not an observable property of a sequential run. It becomes observable only with threads, as data-race freedom.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
