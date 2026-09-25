# Places: borrowing a family of disjoint places at one lifetime

**Question.** `experiments/Projection`, `Relaxed` and `FrameEnd` failed because a borrow of a
whole structure is one cell whose witness owns the parts, so a view of a part clashes with the
parent (`FrameEnd.Views.imm_view_rejected`, `mut_view_rejected`,
`mut_lens_beside_parent_invalid` in `docs/scope-deep-freeze.md`). With disjoint places a
structure is a tree of places whose leaves are separate locations. A borrow of a place is then a
family of leaf borrows at one lifetime, and projection takes a sub-family. This probe models a
place-record as a tuple of `Ref`s, `Ref A ⊗ Ref B`, and does not change the memory model. It asks:

1. Is borrowing several disjoint locations at one lifetime derivable from existing constructs?
2. If not, can it be added?
3. Do FP and adequacy hold? Do simultaneous `Mut` borrows of `s.a` and `s.b`, projection to a
   sub-family at the same lifetime, the `Imm` version, and `split_at_mut` at a static length
   work?

Build: `lake build Places`. Code: `Places/Family.lean` (the construct and its rules) and
`Places/Programs.lean` (checks b–e). Nothing in `Paper/`, `Support/`, `Examples/` or another
experiment is changed. `Places` imports `Records.Splits` and `Records.Programs` for the
context-splitting wrappers and `setG`.

## 1. Derivable: nested `withbor` and `⊑Mut`/`⊑Imm`

Yes. The binary family is a term of the language, and its typing is a derived rule of
`DerivesWf`. No constructor is added.

    withbor2 ≜ λp. λg. let (x, y) = p;
                 let (x′, r) = withbor x (Λ. λmx.
                                 let (y′, t) = withbor y (Λ. λmy. g () (mx, my));
                                 (y′, t));
                 let (y′, t) = r; ((x′, y′), t)

    withborM2_wf : Δ; • ⊢ withbor2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Mut 'c A ⊗ Mut 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T
    withborI2_wf : Δ; • ⊢ withbor2 : Ref A ⊗ Ref B ⊸ (∀'c ⊏ ⊓Δ. Imm 'c A ⊗ Imm 'c B ⊸ ['c] T) ⊸ (Ref A ⊗ Ref B) ⊗ T

This is how the derivation works (`withbor2_wf`, generic over `Mut`/`Imm` through `Borrows`):

- The outer `withbor` borrows `x` at `'a ⊏ ⊓Δ`. The inner one is typed at `Δ, 'a` and borrows
  `y` at `'b ⊏ ⊓(Δ, 'a) = 'a ⊓ ⊓Δ`.
- **Subsumption exists.** `⊑Mut` (row 2.18, `DerivesWf.mutSub`) concludes `Mut @a T` from
  `Mut @b T` and `Δ ⊨ @a ⊑ @b`. At `'b ⊑ 'a` (`entailsLe_inner`) it shortens `mx : Mut 'a A` to
  `Mut 'b A`. `⊑Imm` does the same for `Imm`.
- `g` is instantiated at `'b` by `∀E`, because `'b ⊏ ⊓Δ` (`entailsLt_inner`). So the callback
  receives `Mut 'b A ⊗ Mut 'b B`, both leaves at one lifetime. It is polymorphic in `'c`, so it
  cannot tell that the two leaves were borrowed at different times.
- The inner callback returns `g`'s `['b] T` directly. The outer callback must return
  `['a] (Ref B ⊗ T)`. `[]I` at `'a` is applied to `(y′, t)` after `mx` and `g` are consumed.

**Side conditions** (`Side2`, plus the arguments of `withborM2_wf`/`withborI2_wf`):

- scoping and binder freshness, which are `Bool` equations discharged by `rfl`;
- `∀E`'s renaming of `'c` to `'b` (`hinst`);
- at `Mut`, `withbor` form (2)'s `Δ ⊢ A ⊐ @b`;
- **`Δ, 'a ⊢ B ⊐ 'a` and `Δ, 'a ⊢ T ⊐ 'a`**, which `[]I` at `'a` needs. They hold for every `B`
  and `T` built from `1`, `⊗`, `⊕`, `Ref`, `!`, `[@e]`, `Imm @e` and `Mut @e`, with `@e` from `Δ`,
  because `'a ⊏ ⊓Δ`.

This derivation does **not** cover a `B` or a `T` that contains `⊸`, `∀` or `Unk` outside `!`:
no outlives rule applies to those. Primitive `withbor` has no such restriction on its `T₂`. I
have not derived the family rule at such `B` or `T` by another route, and have not verified that
any obstruction to it is real. None of the checks below needs it.

**n-ary.** The binary rule nests. Check (e) builds a 4-leaf family at one lifetime from two
nested `withbor2`s and `⊑Mut` (`d_innerCb`). A generic `withborN` over a list of leaf types was
not built.

## 2. Nothing was added, and the typed world was not asked anything

Because the construct is derived, FP and adequacy cover it with no new case. The semantic typing
`withborM2_sem` / `withborI2_sem` (`SemX Δ [] withbor2 …`) is
`Fig16.LogRel.Typed.fundamentalProperty` applied to the derivation.

Semantically the two leaves are **not** framed at one lifetime. The outer frame is at `α` and
the inner one is at `β ⊏ α`. "One lifetime" holds at the type: `𝒱⟦Mut 'b A⟧` accepts a cell at
any `b ⊒ δ('b)` (`ptoMutS`'s `α ⊑ b`), and `ptoImmS` likewise, which is what makes `⊑Mut` and
`⊑Imm` sound. So the question of whether the typed world's records and tags (`Tagged`,
`FrameLife`, `NestLife`, `CohE`) accept two frames at one tag `α` never arises. Each `Imm` leaf
gets its own 6.64 record at its own tag. The `Mut` leaves go through 6.65, which records nothing
in the tag list. I did not probe a primitive two-cell frame at one `α`.

Why the earlier clash does not arise here: no cell owns the leaves. The place-record
`Ref A ⊗ Ref B` is a value, not a cell, so there is no parent `imm`/`mut` cell whose witness holds
`ℓ₁ ↦ own`. A sub-family is a component of a tuple of borrows, not a view into a witness, and
`↭` is never asked to accept a cell below a parent.

## 3. Checks

Each program is closed and typed at `1`. It has an adequacy instance (`…_runs`, from
`Fig16.LogRel.Typed.adequacy`), a kernel-checked interpreter run with no leak (`…_eval`), and an
`…Obs_eval` that checks the values the record holds afterwards.

| | result | Lean |
|---|---|---|
| (a) FP + adequacy with the construct | **hold**: the construct is a derived rule; the semantic typing is FP at its derivation | `withborM2_wf`, `withborI2_wf`, `withborM2_sem`, `withborI2_sem`; every `…_runs` |
| (b) `Mut 'c` at `s.a` and at `s.b` together, both updated, record read back | **holds**. `swapBoth`: the callback holds `ma, mb : Mut 'c B` and uses `mb` inside `ma`'s `withswap`, which is `mem::swap(&mut s.a, &mut s.b)`. `(inj₁, inj₂)` becomes `(inj₂, inj₁)` | `d_swapBoth`, `swapBoth_runs`, `swapBothObs_eval` |
| (c) whole-record borrow recovered from the family; sub-family passed at the same lifetime | **holds**. `familyCalls`: `swapFn : ∀'d. Mut 'd B ⊗ Mut 'd B ⊸ Mut 'd B ⊗ Mut 'd B` is called with the family at `'c`; `setFn : ∀'d. Mut 'd B ⊸ Mut 'd B` with `s.a` alone at `'c`; the pair is reassembled and passed to `swapFn` again at `'c`. `(inj₁, inj₁)` becomes `(inj₁, inj₂)` | `d_famCb`, `familyCalls_runs`, `familyCallsObs_eval` |
| (d) `Imm` version of (b)/(c) | **holds**. `readFamily`: `withborI2`; `s.a`'s borrow is copied, read alone by `readOne : ∀'d. Imm 'd B ⊸ B`, and the whole family is read by `readBoth : ∀'d. Imm 'd B ⊗ Imm 'd B ⊸ B ⊗ B`, all at `'c`. It returns `(inj₁, (inj₁, inj₂))` | `d_readCb`, `readFamily_runs`, `readFamilyObs_eval` |
| (e) `split_at_mut`, static `n` | **yes, for free**. A slice of `n` is an `n`-tuple of `Ref`s. Its family at one lifetime comes from nested `withbor2` + `⊑Mut`, and the split is `⊗E` on the family. `splitFour`: a 4-family at `'e` is passed to `swapHalves`, which splits it into halves at `'d` and swaps within each | `d_splitFour`, `splitFour_runs`, `splitFourObs_eval` |

## What this does not give

- **A borrow of a boxed record.** The family is a replacement for `Mut 'a (A ⊗ B)` of a record
  stored in one cell. It is not a way out of that type. A record in one cell, `Ref (A ⊗ B)` or
  `Ref (Ref A ⊗ Ref B)`, is the parent-cell shape of the earlier experiments, and projecting out
  of its borrow is still the excluded same-lifetime view.
- **Moving the record as a whole** means moving the tuple of `Ref`s. That is a value, so it moves
  freely, but it is not one location.
- **Dynamic indices and slices of unknown length** are out of scope.

## Axioms and hygiene

`#print axioms`, checked with a scratch file importing `Places`: `withbor2_wf`, `withborM2_wf`
and `withborI2_wf` depend on `[propext, Quot.sound]`. `withborM2_sem`, `withborI2_sem` and every
`…_runs` depend on `[propext, Classical.choice, Quot.sound]`. The `…_eval`s depend on
`[propext]`. The directory has no `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`,
`partial` or `unsafe`. `lake build Places` adds no warnings of its own, and
`scripts/check-hygiene.sh` passes.
