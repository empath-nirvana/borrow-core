# P10 Exclusivity across the handler

## Statement

Every reachable configuration satisfies the aliasing invariant, counting the loans held by suspended frames, by running handler clauses, and by values in transit.

**Lean target:** not yet stated. It goes in the targets library with an enumerated `sorry`.

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
