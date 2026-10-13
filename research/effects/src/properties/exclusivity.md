# P10 Exclusivity across the handler

## Statement

Every reachable configuration satisfies the aliasing invariant, counting the loans held by suspended frames, by running handler clauses, and by values in transit.

**Lean target:** [`experiments/Targets/RESTRUCTURE.md`](../../../../experiments/Targets/RESTRUCTURE.md) §2.2, §3.5: B6 `ExclusiveB` (every configuration the world reaches is a valid resource) in `B.Guarantees`, and I's `Exclusive` (the same counting the frames suspended computations hold, `SemWorld.held`) in `Interface`, both in done. In Lean: `ExclusiveB coreB` is PROVED AT σ=[] (`exclusiveB_core`, from `TW.valid`), and so is `Exclusive coreW` (`exclusive_core`); both OPEN at W.

## Why it matters

Survey A5 and T5(i); Ante (design); Hylo subscripts; Yarrow.

## Design space

- **The reborrow encoding:** a clause receives a reborrow of the capability, and `resume` hands it back.
- **Counting open lends in σ,** including 6.66's unfolded cells.

## Evidence

`TW`, `TI`, `TW.inv` (Core σ=[]); WorldW `entryRecorded_mut` (probe).

## Experiments

None yet. Entries go in the [track log](../tracks/log.md).

## Trade-offs and notes

Not observable sequentially; it is the invariant that makes P1 provable.

## Open questions

Cite OQ ids from `docs/effects-calculus/99-open-questions.md` as tracks reach them.
