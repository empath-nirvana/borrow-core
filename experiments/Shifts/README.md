# Shifts — the borrow axioms as labelled shifts

**Schema** (`Shifts.lean`). `shiftTy src view ret x bnd T₂ =
src ⊸ (∀'x ⊏ bnd. view 'x ⊸ ['x] T₂) ⊸ (src ⊗ T₂ | T₂)`. The four label-introducing
axioms are instances, by `rfl`:

| axiom | source | view | source mode → view mode | returned |
|---|---|---|---|---|
| `withbor` (1) | `Ref T₁` | `Imm 'x T₁` | lin → unr | yes |
| `withbor` (2) | `Ref T₁` | `Mut 'x T₁` | lin → aff | yes |
| `withbor` (3) | `Mut @a T₁` | `Mut 'x T₁` | aff → aff | yes |
| `withload` | `Imm @a T₁` | `Imm̲ 'x T₁` | unr → unr | no |

- The view's mode is never below the source's: a borrow lends upward, and the label is
  what makes lending above your own mode sound (ModesLabels).
- The source is returned exactly when its mode lacks contraction (`ret_iff_not_C`): an
  unrestricted source can be copied beforehand, so nothing needs to come back.
- `withswap` is not a shift: its callback is a bare `⊸` with no label, a linear exchange
  through the `Mut` cell.
- `withload`'s view is the payload projected to `unr` (`Imm̲`), not a pointer: it is a
  dereference under a label, where `withbor` lends a pointer.

**The gap the schema predicts.** Upward pairs are lin→aff, lin→unr, aff→aff, unr→unr and
**aff→unr**; the table has no axiom for the last, lending a `Mut` as an `Imm`
(`axWithborMITy`). Rust has it (`&mut T → &T`).

**Attempt at its compatibility lemma.** The existing proofs share one skeleton: open the
source (a `Ref` directly; a `Mut` by `wpTS_M_antiFrameX`), frame the payload at the view's
kind (`wpTS_I_frameX` for `Imm`, `wpTS_M_frameX` for `Mut`), run the callback at a fresh
lifetime, return. `withbor3` is anti-frame + `Mut` frame; `withbor1` is direct + `Imm`
frame. The missing pair would be anti-frame + `Imm` frame.

It does not compose as stated. `wpTS_I_frameX` takes `hQ`, stability of its postcondition
along every `Ext`; its proof spends `hQ` once, at the record-drop step
(`ext_drop`, `Support/TypedWorld/Wp.lean`). The postcondition the anti-frame supplies contains
`ptoMutS l α₀ ls'' _ ─⋆ Q`, whose antecedent is contravariant in the list, so it is not
stable along arbitrary `Ext`. At the drop step it plausibly is: the dropped record sits at
the fresh `α ⊏ ⊓Δδ`, below the cell's lifetime, so the cell's stored list is unchanged.

I have not derived `withborMI_compat` and have not verified that any obstruction is real.
The route: a variant of `wpTS_I_frameX` whose `hQ` is stated at the drop step, carrying the
bound on `α`, then the graft.

**Next: borrowing computations.** `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk`: a borrowed closure cannot be
called, since it may capture linear resources. ModesLabels suggests a mode-annotated
arrow: a closure whose resource holds only `imm` cells is `unr`, duplicable by the same
argument as `dup_sound` — Rust's `Fn` against `FnOnce`, with `FnMut` the `aff` case. The
crux is §12.69: the `Imm` payload is held at the observable view, which relaxes `⊸` to
`True`, because at a `⊸` position the full relation is resource-sensitive and the reborrow
cannot be chosen from types. Whether the chooser (`rebChooseO_top_tw`,
`rebChooseO_deep_tw`, `obs_transfer`) survives keeping `unr` arrows unrelaxed is the test.
