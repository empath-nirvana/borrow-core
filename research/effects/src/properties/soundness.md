# P1 Soundness

## Statement

For every well-typed program, run under every allocator and every platform environment that respects its protocol, every run:
- never gets stuck: no use after free, no double release, no bad access;
- never stops at an operation outside its row: no unhandled operation;
- at a div-free (data) answer, terminates at a value with the memory empty, so every owned cell and capability is released exactly once, those held by cancelled continuations included;
- for a program that returns a loop, is safe on every finite prefix of the runtime's drive;
- runs the finalisers of the frames it unwinds or cancels once each, innermost first.

A program's answer at the top is data or a loop, so no resource is left with its result. Termination holds only for div-free answers. Tier 1 and tier 2 are the same theorem over different typing rules. The same holds with capabilities given as externs meeting their contracts, together with platform operations.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.Soundness`, `Targets.SoundnessContracts` and `Targets.ReleasedOnceAll` (§3, T1; D9), conjuncts of the end state `Targets.EndStateAt` (§1.0), proved through `Targets.FL` and `Targets.Adequate` (§4). Main's row holds only platform operations, so an error must be handled before the top. In Lean: `Targets.Soundness`'s return conjunct is PROVED AT A RESTRICTION for Core's typing at the platform with no operation (`soundRetAt_tier1_none`), with the effect programs of `Core/EffPrograms.lean` as instances (`acceptedT1_*`); at platforms with operations and for driven loops it is OPEN, and so is `Targets.SoundnessContracts`. `Targets.ReleasedOnceAll` is PROVED at every typing system (`releasedOnceAll`). T1 from FL and adequacy is PROVED (`soundnessOfFL`).

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
