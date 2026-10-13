# P4 I2: capture and resume preserve the invariant

## Statement

Capture, which freezes a computation at an operation, and resume both preserve the global invariant (`TW.inv`, extended to W), including lends that span the suspension.

As a binder: the relation and the invariant are equivariant under bijections of locations and instances and under order-respecting renamings of lifetimes. Resume and placement are instantiations.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §3.2, §3.6: in done, `Arises` (every configuration the world reaches arises, with the frames suspended computations hold counted), in I's `Interface`, and the tier-2 programs, accepted with their answers (`Tier2Programs`: `at02`, `at04`, `at12`, `at17`, `genSelf`). The rest of `I2` is the proof device's, beside done, since each part fixes an option of OQ-8 or OQ-9: `StopVisible` (the stop restores the visible frames), `ShareResume` (the resume conjunct of the share at every future index), `FramesW` ([TR] 6.64 and 6.65 at W) and `SpanBorrows` (the six unwinding borrow constants at the spanning rows). The spanning typing rules are `J₂`'s mechanism, recorded as `spanRules_J₂`, not a pin. The binder reading is `FreezeBinder`, beside done (`CombinedBinder`): its location half a symmetry, its lifetime half forward instantiation. In Lean: `Arises coreW` is PROVED AT σ=[] (`arises_core`); `I2` is PROVED AT A RESTRICTION at Core σ=[], at abortive rows (`i2_core_abortive`), and OPEN at W; `Tier2Programs` at a typing system is OPEN (the interpreter runs the programs, as evidence); `FreezeBinder` is OPEN, and its first check, `NotVDenNaturalArises`, is stated and OPEN.

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
