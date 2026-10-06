# P4 I2: capture and resume preserve the invariant

## Statement

Capture, which freezes a computation at an operation, and resume both preserve the global invariant (`TW.inv`, extended to W), including lends that span the suspension.

As a binder: the relation and the invariant are equivariant under bijections of locations and instances and under order-respecting renamings of lifetimes. Resume and placement are instantiations.

**Lean target:** designed in [`experiments/Targets/DESIGN.md`](../../../../experiments/Targets/DESIGN.md) as `Targets.I2` (§5), at a class of rows a lend may span (abortive for tier 1, every unr-free row for the end state): `Arises` (every configuration arises, with the frames suspended computations hold counted), `StopVisible` (the stop restores the visible frames), `ShareResume` (the resume conjunct of the share at every future index), `FramesW` ([TR] 6.64 and 6.65 at W, the lend quantified once at the callback's start, GhostEnd's `O151AsStated` shape) and `SpanBorrows` (the six unwinding borrow constants at the spanning rows). The spanning typing rules are tier 2's pin `Targets.Tier2Pinned`, parametric in OQ-56's admissibility, bounded below by R-CLOSEDOP. At Core σ=[] I2 is proved only at abortive rows, where no lend spans a stop. The binder reading is `Targets.FreezeBinder`, a target beside done (`EndStateBinder`): its location half a symmetry, its lifetime half forward instantiation. In Lean: `Targets.I2` is PROVED AT A RESTRICTION at Core σ=[], at abortive rows (`i2_core_abortive`), OPEN at the end state; `Targets.FreezeBinder` is OPEN, and its first check, `Targets.NotVDenNaturalArises`, is stated and OPEN.

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
