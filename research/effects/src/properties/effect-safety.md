# P2 Effect safety

## Statement

A program typed `F_Σ A` only ever stops at operations in Σ. In particular, `F_∅ 1` performs no unhandled operation.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §1.5: A's S1 `RowAlgebra` (the row form's algebra is lawful and safe, Yoshioka et al. Def. 3.5 and Def. 5.1, with rows as sums of signatures, `RowSig`, and typing closed under subeffecting, `SubClosed`) and S3 `EffSafe` (a typed program at row ε only ever stops at an operation of ε that nothing catches), both in done at our instance at every admissible effect context. E6 (`Tunnel`) adds no accidental handling. The row form is a parameter of done (OQ-13), fixed at the minimal tail-variable form `orowRF`. In Lean: S1 and S3 at our instance are OPEN (the bridges `rowAlgebra_ourInst`, `effSafe_of_core` are not built). Core's form `EffSafe tier1` is PROVED AT σ=[] (`effSafe_tier1`, from FL at BoLo, `FamEmpty` and `AdequateEvery`). Our rows' algebra is PROVED AT A RESTRICTION at `orowRF` (`rowAlgSafe_orowRF`, `rowLink_orowRF`). At every instance, an unhandled operation is untypable at the pure row (`not_der_unhandled`), and Def. 5.1's first condition follows from `RowSig` (`c1_of_rowSig`).

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
