# P2 Effect safety

## Statement

A program typed `F_Σ A` only ever stops at operations in Σ. In particular, `F_∅ 1` performs no unhandled operation.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

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
