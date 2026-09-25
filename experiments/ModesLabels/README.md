# ModesLabels — ownership kinds as adjoint modes, lifetimes as labels

**Question.** Do the paper's three ownership kinds behave as adjoint-logic modes? Adjoint
logic (Reed; Pruiksma, Chargin, Pfenning, Reed) is parameterised by a preorder of modes
and a monotone `σ` assigning each mode its structural rules. Candidate:

| mode | types | `σ` |
|---|---|---|
| `lin` | `Ref T`, `T₁ ⊸ T₂`, `∀'a ⊏ @b. T` | none |
| `aff` | `Mut @a T` | `W` |
| `unr` | `Imm @a T`, `!T`, `1`, `Unk` | `W`, `C` |

`⊗`/`⊕` take the meet of their components; `[a] T` takes `T`'s mode. Lifetimes are not
modes: they label the two borrow constructors.

`!T` (`SPEC.md` §2) is `unr`: its resource is `∅`. `Free`, `free_compS` and
`compS_self_of_imm` are also in the library, as `Support/Model/Unr.lean`. Build:
`lake build Experiments`.

**Results** (`Modes.lean`; standard axioms only), over the typed world, at every type and
both modes of `vX`:

- `weaken_sound`: at a mode with `W`, `𝒱X⟦T⟧` holds no `own` cell — dropping the value
  leaks nothing.
- `contract_sound`, `dup_sound`: at a mode with `C`, `𝒱X⟦T⟧` holds only `imm` cells, and
  `𝒱X⟦T⟧ ⊨ 𝒱X⟦T⟧ ⋆ 𝒱X⟦T⟧` (the resource is idempotent under `●`; 6.116 `I-dup` at the
  cell).
- `mode_immReborrow`: `Imm̲ 'b T` is unrestricted at every `T`. The paper's metafunction is
  the projection to the top mode.

So `σ` is sound for the model as it stands: the structural rules the axiom table grants
(`copy` at `Imm`, `forget` at `Imm`/`Mut`/`Unk`, no `forget` at `Ref`) are the ones the
mode assignment predicts, and they hold semantically at every type of that mode, not only
at the axioms' types.

**Where the labels come in.** Adjoint logic's declaration of independence says a
proposition at mode `m` depends only on hypotheses at modes `≥ m`. Every constructor
respects it (`⊗`/`⊕`/`[a]` by the meet, `Ref`/`⊸`/`∀` because `lin` is the bottom) except
the two labelled ones: `Mut @a (Ref T)` is affine over a linear payload, and `Imm @a T` is
unrestricted over any payload. `weaken_sound` still holds there because the payload sits
inside the borrow cell's witness, not at the top level, and the label bounds how long the
cell lives; for `Imm` the payload is read through `Imm̲`, which restores independence
(`mode_immReborrow`). Reading: a label is a licence to break independence for the
duration of a scope, and the lender carries the obligation the payload represents.

**Caveats.**

- `σ` is checked for the model, not derived from a mode-indexed calculus: there is no
  syntax with mode annotations or shifts, and the shifts (`withbor`, `withload`,
  `withswap`) have not been expressed as adjoint `↑`/`↓`.
- The label reading of independence is an interpretation of where the proofs go through,
  not a theorem; stating it needs the shifts.

**Next.** The borrow axioms as shifts: `withbor : Ref T ⊸ (∀'a. Mut 'a T ⊸ ['a] U) ⊸ …`
as a labelled `lin → aff` shift and back, `withload` as `→ unr`, and check that the three
`Mut`/`Imm`-introducing compatibility lemmas are instances of one shift rule.
