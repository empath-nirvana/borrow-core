# Standing instructions

## Spec first

<!-- ANCHOR: spec-first -->
`SPEC.md` is the specification; `Paper/`, `Support/` and `Examples/` implement it (§1–§2),
and `Core/` implements §3–§7. The task is
to implement what the spec states, the way the paper mechanization transcribes what the paper
prints. Code an entry adds or changes is tagged `[spec §N]`.

- No change to the library without a spec entry that states it. If an implementation needs
  something the entry does not state, stop and change the entry first.
- Experiments live in `experiments/`. The library (`Paper/`, `Support/`, `Examples/`, `Core/`)
  never imports them; work from an experiment lands in the library only after its spec entry is
  written.
- Every entry says what it adds, which baseline theorems it must preserve, and what is open.
  The changelog records each version.
<!-- ANCHOR_END: spec-first -->

## Growth discipline

<!-- ANCHOR: growth -->
The proof burden of the previous language grew until it was unmaintainable
(`docs/l-lang-kernel-and-lit.md` §2). Three rules (`docs/decisions.md` 19–21):

- **No new index on `CDerives`.** Put a new coordinate in a type former or in the model.
- **Generalize by deleting.** A general former lands in the same change that turns the fixed
  formers it replaces into abbreviations.
- **Do not invert `CDerives` casually.** Inversion lemmas, substitution over derivations, checker
  completeness or lowering proofs that invert typing need their cost stated in the issue or PR.

Prefer computation-type formers and derived forms over new value-type formers: a `VTy` former
costs about 100 match arms across `Core/`, a `CTy` former about 20, a `CDerives` rule one
compatibility lemma.
<!-- ANCHOR_END: growth -->

## Hygiene

- No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`, `unsafe` in
  `Paper/`, `Support/`, `Examples/` or `Core/`.
- Every result's `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
- `lake build` clean; `scripts/check-hygiene.sh` and the axiom check passing
  (`lake env lean scripts/AxiomCheck.lean`).
- Comments say what the code is, not how it got here.
