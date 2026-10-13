# P1 The combined theorem

## Statement

For every well-typed program, run under every allocator and every platform environment that respects its protocol, every run:
- never gets stuck: no use after free, no double release, no bad access;
- never stops at an operation outside its row: no unhandled operation;
- at a div-free (data) answer, terminates at a value with the memory empty, so every owned cell and capability is released, those held by cancelled continuations included; and each allocation is released once, even where the allocator reuses a location;
- for a program that returns a loop, is safe on every finite prefix of the runtime's drive;
- runs the finalisers of the frames it unwinds or cancels once each, innermost first.

A program's answer at the top is data or a loop, so no resource is left with its result. Termination holds only for div-free answers. Tier 1 and tier 2 are the same theorem over different typing rules. The same holds with capabilities given as externs meeting their contracts, together with platform operations.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §3.5: the combined theorem `I.Combined RF J M Adm c`. It holds A's properties at our instance at every admissible effect context, B's guarantees in the composite (`B.Guarantees`), the interaction's option-neutral rules (`Bounds`, `Interface`), the pins, and the composite's programs and rejections (`Accepts`, `Rejects`). Done is `Combined orowRF J₂ W admClosedOp .any` with `audit_W`; tier 1 is `Combined orowRF J₁ coreW admClosedOp .abortive`. Safety and leak freedom are B3 and B4 (`Sound`); with externs, B4′ (`SoundContracts`, externs meeting W's contract as a stated hypothesis); release exactly once, location reuse included, is B5 (`ReleasedOnceReuse`); effect safety is A's S3; finalisation on cancel and unwind is A's S5. Main's row holds only platform operations, so an error must be handled before the top. In Lean: done and tier 1 are OPEN (`J₁`, `J₂` and `W` are not built). `Sound`'s return conjunct is PROVED AT A RESTRICTION for Core's typing at the platform with no operation (`soundRetAt_tier1_none`), with the effect programs of `Core/EffPrograms.lean` as instances (`acceptedT1_*`). B3 and B4 from FL and adequacy (`soundnessOfFL`), B4′ from the same (`soundContractsOfFL`), and B5 from B4′ given the step-for-step simulation (`releasedOnceReuse_of_bumpSim`) are PROVED, generic; adequacy at platforms with operations and for driven loops, and `BumpSim` (OQ-43), are OPEN. `ReleasedOnceAll` is a tautology about runs (`releasedOnceAll`), a lemma, not a guarantee. The restricted tier-1 reduction `Tier1Core` (today's kernel, Core's world) has its world conjuncts and device proved, and B's guarantees from `Adequate coreB` and `BumpSim` (`tier1Core_guarantees_of`); it lacks A's (S) properties at our instance (the bridges, not built) and `I4a` at today's unr-free kernel.

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
