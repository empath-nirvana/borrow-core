# P4 I2: capture and resume preserve the invariant

## Statement

Capture, which freezes a computation at an operation, and resume both preserve the global invariant (`TW.inv`, extended to W), including lends that span the suspension.

**Closed in part by decision 71 (`docs/decisions.md`).** No borrow is held across a suspension, so the clause for lends that span it is not a target: `docs/tombstones/lends-across-suspensions.md`.

As a binder: the relation and the invariant are equivariant under bijections of locations and instances and under order-respecting renamings of lifetimes. Resume and placement are instantiations.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

## Why it matters

Survey T1 (the capture lemma) and T5. System C Lemma 4.6; Tang et al. Thm 3.4. Tier 2 is exactly I2 for arbitrary nesting.

## Design space

- **Frames carried open in σ** (OQ-9 (a)).
- **Ghost-end:** end internal lends at the stop and re-lend fresh at resume (OQ-9 (b)). This is instantiation of bound lifetimes.
- **Where the future-world quantifier sits** (OQ-8).
- **The ordering of the lend stack** (D-ORD; the WorldW finding).

## Evidence

- GhostEnd spanning instances: `withbor_spans_yields_cC`, `imm_spans_yield`, `spans_two_affine_yields` (Core σ=[]).
- WorldW batch 1: resource-level hand-on and exit lemmas for 6.64, 6.65 and 6.150; `wpGW_nil` (probe).
- Restrat `mut_not_natural` refutes naturality at a stored Mut invariant. Whether it arises was never checked.

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

(a) costs the relation a no-copy-out-of-the-share property, and (b) costs it re-lendability (WorldW FINDING-1).

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
