# Standing instructions

## Spec first

`SPEC.md` is the specification; `Paper/`, `Support/` and `Examples/` implement it. The task is
to implement what the spec states, the way the paper mechanization transcribes what the paper
prints. Code an entry adds or changes is tagged `[spec §N]`.

- No change to the library without a spec entry that states it. If an implementation needs
  something the entry does not state, stop and change the entry first.
- Experiments live in `experiments/`. The library (`Paper/`, `Support/`, `Examples/`) never
  imports them; work from an experiment lands in the library only after its spec entry is
  written.
- Every entry says what it adds, which baseline theorems it must preserve, and what is open.
  The changelog records each version.

## Hygiene

- No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`, `unsafe` in
  `Paper/`, `Support/` or `Examples/`.
- Every result's `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
- `lake build` clean; `scripts/check-hygiene.sh` and the axiom check passing
  (`lake env lean scripts/AxiomCheck.lean`).
- Comments say what the code is, not how it got here.
