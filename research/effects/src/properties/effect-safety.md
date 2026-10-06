# P2 Effect safety

## Statement

A program typed `F_Σ A` only ever stops at operations in Σ. In particular, `F_∅ 1` performs no unhandled operation.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.EffSafe`, a conjunct of the end state, with `Targets.RowAlgSafe` and `Targets.RowLink` (T0): the row form the typing rules use, with row variables, forms an effect algebra (Yoshioka et al. Def. 3.5) that is safe (Def. 5.1), and its operations are the closed-row operations of `[sub]`, `[handle]` and row instantiation (§6, P2). The row form is a parameter (OQ-13); the minimal tail-variable form is the restricted instance. In Lean: `Targets.EffSafe` is PROVED AT σ=[] for Core's typing (`effSafe_tier1`, from `FL coreW tier1` and `AdequateEvery coreW`), OPEN at the end state; T0's `Targets.RowAlgSafe` and `Targets.RowLink` are PROVED AT A RESTRICTION, at the minimal tail-variable form (`rowAlgSafe_orowRF`, `rowLink_orowRF`).

## Why it matters

Bauer–Pretnar (Twelf); System C Cor. 4.8; Yoshioka–Sekiyama–Igarashi 2024. The last gives the conditions the effect algebra must meet: subeffecting cannot hide a performed label, and handling one label never erases another.

## Design space

- **Rows with row variables** (decided).
- **Capabilities.** Effect safety becomes an outlives check, as in System C.
- **Modal effects,** into which rows and capabilities both encode (Tang & Lindley 2026).

## Evidence

Implicit in `adequacyD` at `F_∅ 1` with `ewp_bot` (Core σ=[]). There is no named theorem.

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

With row variables in the kernel, the Yoshioka conditions must be checked against our row algebra, including `[sub]` and masking if we add it.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
