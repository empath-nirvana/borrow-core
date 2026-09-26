# Optics: borrows as optics with a lifetime-scoped residual

**Question** (issue #27). Is a borrow an instance of a general abstraction, a linear optic whose
residual the lender holds for a lifetime? Can the borrow rules be lifted into that abstraction
without touching the Fundamental Property? The decisive test is whether a variant-payload
borrow (prism, then lens) and a list traversal come out of the existing rules.

The plan is `docs/prior-art-optics.md` §9. Build: `lake build Optics`. The library imports
`Core` and nothing imports it. `Paper/`, `Support/`, `Examples/` and `Core/` are unchanged.
`CDerives`, the relation and the typed world are unchanged as well. Every instance is a closed
`CDerives` derivation, so `fundamentalC` covers it with no new case (`Optic.sem`). Every law is
a statement about machine runs (`Steps`). The characterisations are `↔`, so they hold on every
run and every run they describe exists. `lift_cell`, `tag_frozen` and the shape law are their
consequences on every run. The laws are about the machine and cannot disturb the FP.

| file | contents |
|---|---|
| `Runs.lean` | runs as equations: a redex runs as its contractum, and `K[e]` runs `e` first (`steps_plug_iff`, `steps_beta_iff`, `steps_load_iff`, `steps_store_iff`, `steps_withswap_iff`, …) |
| `Lens.lean` | the interface `Optic`; instances `idLens`, `reLens`, `idImm`, `fstLens`, `famLens`; the combinators `Optic.lift` and `Optic.comp`; the accessor `overV` |
| `Laws.lean` | `over`'s runs; `over_id`, `over_fuse` |
| `Programs.lean` | `fieldProg`: a leaf of a place-record in a cell, written through a composite lens |
| `Getter.lean` | `Getter`, `immGetter` (`withload`); `withload_read`, `copy_runs`, `get_copy` |
| `Prism.lean` | `prism`, `prismB`, their lifts; `prismLift_runs`, `tag_frozen`; `variantProg` |
| `Traversal.lean` | IterMut (`iterMutV`, `d_iterMut`) and copy-in/copy-out (`mapOverV`, `d_mapOver`) over the common list; `iterProg`; the goal `AllAtOnceGoal`, stated |
| `Shape.lean` | `foldReuse`'s recursion as runs; IterMut's shape law `iterMut_shape`; `incCb_frame` |

## The interface

```
structure Optic (S F : Life → VTy) (W : VTy → VTy) (O : VTy → VTy → VTy) where
  run    : Val                       -- closed
  Adm    : LifeCtx → Life → LifeVar → Prop
  wf     : Adm Δ a x → plainV T → Dead Γ →
           CDerives Δ Γ run (S a ⊸ W(G) ⊸ S a ⊗ O(T, G))      G = ∀'x ⊏ ⊓Δ. F('x) ⊸ ['x] T
  Obs    : Heap → Heap → Val → Val → Val → Prop
  runs   : Steps μ (run s g) μ' w  ↔  ∃ t, w = (s, t) ∧ Obs μ μ' s g t          -- Rezip
```

This is the continuation form of `docs/prior-art-optics.md` §9. The borrower receives the focus
`F('x)` at a fresh `'x ⊏ ⊓Δ`, and the lender keeps the rest until the callback returns.
`runs` is the continuation form of Riley's Rezip (`ev ∘ Unzip = id`): every run returns the
source `s` itself. A lens is `W = id`, `O(T, _) = T`, and its `Obs` is `LensObs Dom focus`: the
callback runs on `focus s`, and nothing else happens.

The result type `T` ranges over `plainV` (`1`, `0`, `⊗`, `⊕`, `Ref`, `!`, `μ`). That is the
side condition `withborF2` already has: the result must outlive the outer lifetime.

| instance | built from | source → focus | `focus` |
|---|---|---|---|
| `idLens V` | `withbor`, form 2 | `Ref V → Mut 'x V` | `s` |
| `reLens V` | `withbor`, form 3 | `Mut @a V → Mut 'x V` | `s` |
| `idImm V` | `withbor`, form 1 | `Ref V → Imm 'x V` | `s` |
| `fstLens A B` | `withbor` on the first leaf, the second kept by the lender | `Ref A ⊗ Ref B → Mut 'x A` | `x` of `(x, y)` |
| `famLens A B` | `withborF2` (`Core/Family.lean`, nested `withbor` + `⊑Mut`) | `Ref A ⊗ Ref B → Mut 'x A ⊗ Mut 'x B` | `s` |
| `L.lift` | `withswap m (λs. L.run s g)` | `Mut @a S → F('x)`, for any optic `L` on an owned `S` | — |
| `splitMut A B` | `famLens` lifted | `Mut @a (Ref A ⊗ Ref B) → Mut 'x A ⊗ Mut 'x B` | — |
| `L₁.comp L₂` | nesting: `L₁` at `'x`, then `L₂` on `Mut 'x U` at `'y ⊏ 'x` | `S → F('y)` | `f₂ ∘ f₁` |
| `prism A B` / `prismB A B` | `case` + `withbor` | `Ref A ⊕ Ref B → Mut 'x A`, affine | — |

`comp` uses no `⊑Mut`. The second optic is typed at the source lifetime `'x`, and the client's
callback is instantiated at `'y` by `∀E`. The family lens contains `⊑Mut` inside `withborF2`.
The static-shape block borrow `withborS` has the same typing shape, and `Core`'s
`withborS_ret` is already its Rezip law. It is not restated here.

## Laws proved (every run)

**Stage 1**

- **Rezip** (`Optic.runs`, at every instance): the source comes back unchanged. At `lift` this
  is `Optic.lift_cell`: on every run of a lifted optic, the lender's cell holds exactly what it
  held before, whatever the callback did.
- **Composition** (`Optic.comp_obs`): the composite of two lenses is a lens whose focus is the
  composite of the foci (`f₂ ∘ f₁`, domain `Dom₁ s ∧ Dom₂ (f₁ s)`). The identity laws are the
  instances `focus = id` of `idLens` and `reLens`.
- **`over`** (`steps_over_iff`): `over ℓ f = lift ℓ (Λ. λmv. withswap mv f; …)` runs `f` on the
  focus cell's content, stores the result in the focus cell, and restores the source cell.
- **`&unit`** (`over_id`): `over ℓ (λv. (v, ()))` runs to `(ℓ, ())` and leaves the heap as it was.
- **`&assoc` / fusion** (`over_fuse`): `let (m, t) = over ℓ f; let (m′, u) = over m g;
  (m′, (t, u))` and `over ℓ (f ; g)` have the same runs. This holds when `f` and `g` are pure
  (`PureFn`) and the source and focus cells are distinct.

**Stage 2**

- **The put is the identity** (`immGetter.runs`, `withload_read`): `withload` loads and hands the
  content to the callback, and writes nothing. With the reading callback the heap is unchanged
  and the result is the content.
- **The view commutes with duplication** (`copy_runs`, `get_copy`): two reads through the two
  copies of an `Imm` return the same content and leave the heap unchanged. This is Clarke et
  al. Def 3.3's comonoid condition, at runs.

**Stage 3.** See the decisive test below.

**Stated, not proved**

- `over_id` and `over_fuse` at an *effectful* callback. At the bare machine a callback may
  write the lender's cells; typing forbids this and the machine does not. The laws above
  therefore carry `PureFn`, and the shape law carries `ElemFrame`. Deriving these frame facts
  from `fundamentalC` (a parametricity result of the logical relation) is not done.
- Riley's ZipZip, and the laws of the affine optics beyond `lift_cell`.
- Stage 4 (6.65/6.66 as an optic at the logic level) is not attempted.

## The decisive test

**(a) Variant payload, fresh lifetime, tag frozen: derived, with no new rule.**

```
prism  ≜ λs. λg. case s { inj₁ r ⇒ let (r′, t) = withbor r g in (inj₁ r′, inj₁ t)
                        | inj₂ r ⇒ (inj₂ r, inj₂ g) }
prism  : Ref A ⊕ Ref B ⊸ G  ⊸ (Ref A ⊕ Ref B) ⊗ (T ⊕ G)       G = ∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] T
prismB : Ref A ⊕ Ref B ⊸ !G ⊸ (Ref A ⊕ Ref B) ⊗ (T ⊕ 1)
(prismB).lift : Mut @a (Ref A ⊕ Ref B) ⊸ !G ⊸ Mut @a (Ref A ⊕ Ref B) ⊗ (T ⊕ 1)
```

- **The linear affine optic hands the unused callback back.** A callback of type `G` is a
  `U C`, and a `U C` is not persistent, so it cannot be dropped. The `!` form drops it (`G` under
  `!`, `Ctx.DeadP.drop`).
- The plan's literal type, a linear `G` with `T ⊕ 1`, is therefore not the typing derived. I have
  not derived it, and I have not verified that any obstruction to it is real.
- **Tag law** (`tag_frozen`, from `lift_cell`): on every run the variant's cell holds what it held
  before, so its tag is unchanged. This needs no hypothesis on the callback.
- `prismLift_runs` gives the runs exactly:
  - At `inj₁ r`, the callback runs on the payload cell `r`, and the cell gets `inj₁ r` back.
  - At `inj₂ r`, nothing runs and the heap is unchanged.
- **`variantProg`** borrows a cell holding `inj₁ (alloc (inj₁ ()))` mutably, writes the payload
  through the lifted prism at `'x ⊏ 'a`, and frees everything.
  - `adequacyC` runs it with no cell left (`variantProg_runs`).
  - The interpreter returns `inj₁ (inj₂ ())`: tag kept, payload written (`variantObs_eval`).
  - At `inj₂`, the interpreter returns `inj₂ (inj₁ ())`: nothing written (`variantObs₂_eval`).

**(b) List traversal: derived, with the shape law.**

Both forms are over the common list `L_E = μX. 1 ⊕ (Ref E ⊗ Ref X)`.

- **Copy-in/copy-out** (`d_mapOver`): `Mut @a L_E ⊸ Mut @a L_E ⊗ 1`, by
  `withswap m (λl. (foldReuse (mapRAlg f) l, ()))`.
- **IterMut** (`d_iterMut`): `L_E ⊸ !(∀'x ⊏ ⊓Δ. Mut 'x E ⊸ ['x] 1) ⊸ L_E ⊗ 1`.
  - `foldReuse`'s algebra lends each value cell by `withbor`, at its own fresh lifetime, and
    refills the emptied next cell with the traversed tail.
  - The algebra is built at run time around the callback and promoted under `!` over the
    callback's slot.
  - `iterProg` increments `[0, 0, 0]` element by element through `Mut 'x N`. It runs with no
    cell left, the interpreter returns `[1, 1, 1]` (`iterObs_eval`), and the nodes stay at their
    addresses (`iter_inPlace`).
- **Shape law** (`iterMut_shape`): every run of `iterMut v g` to a value
  - returns `(v, ())`, the same root;
  - leaves the list at the same node cells, with every next cell as it was;
  - writes only value cells;

  so the length is preserved.
  - The hypothesis `ElemFrame g` says the callback touches only the cell it is lent, which is
    what the borrow gives through typing. It holds at the program's callback (`incCb_frame`,
    `iterInc_shape`).
  - The proof steps through `foldReuse`'s recursion by induction on the nodes (`fold_shape`).
- **The borrow form at one lifetime is not derived.** Handing the callback every element at
  once, at one lifetime, over a list of dynamic length is stated as `AllAtOnceGoal E` in
  `Traversal.lean`: a closed value of type
  `L_E ⊸ (∀'c ⊏ ⊓Δ. (μX. 1 ⊕ (Mut 'c E ⊗ X)) ⊸ ['c] T) ⊸ L_E ⊗ T`.
  - For a static shape it is `withborS`.
  - I have not derived it for `L_E`, and I have not verified that any obstruction is real.
  - `docs/prior-art-optics.md` §9 predicted that this case needs L2, the multiplicative split
    `Mut_α (P ∗ Q) ⊢ Mut_α P ∗ Mut_α Q` of `docs/prior-art-borrow-splitting.md`. It is the exact
    goal this experiment leaves.

**Verdict.** Stages 1–3 need nothing beyond existing rules. The one piece not derived is the
all-at-once borrow form over a dynamic length (L2), stated above as a goal.

## What this unlocks

**(U1) A new program expressible — partial.**
- **Nothing becomes typable that was not.** Every instance is a `CDerives` derivation from
  existing constructors, so each program here could have been written by hand before.
- **The derived rules are new.** Nothing in `Core` gave them before:
  - a `Mut 'x` of a variant's payload at a fresh lifetime, with the tag frozen (lifted prism);
  - a `Mut 'x` of a place-record's leaf through a `Mut` of the cell holding the record (lifted
    `fstLens`, composed with `idLens`);
  - IterMut: each element of a dynamic-length list lent as a `Mut 'x E` to a callback. `Core`'s
    in-place map applies a value function `E ⊸ E`, not a borrow.
  - A split of a mutable borrow at a fresh lifetime, `Mut @a (Ref A ⊗ Ref B)` to
    `Mut 'x A ⊗ Mut 'x B` (`splitMut`, the family lens lifted). The borrow-splitting survey's
    table lists L2 at fresh lifetimes through `withswap` + `withbor` as unverified. Here it is a
    derivation, and `lift_cell` is its law.
- The all-at-once form (L2) is not unlocked.

**(U2) Proof obligations discharged once for a class — yes.**
- **Typing.**
  - `Optic.lift` and `Optic.comp` are generic: any instance lifts through `withswap` and
    composes with no derivation written for it.
  - `fieldProg` writes no derivation for its borrowing; its typing is `cellFst.wf`.
- **Laws.** Each is proved once and holds for every instance:
  - `Optic.lift_cell`, for every lifted optic. The variant's tag law is literally its instance.
  - `Optic.comp_obs`, for every pair of lenses.
  - `over_id` and `over_fuse`, for every lens in lens form.
  - `iterMut_shape`, for every callback satisfying `ElemFrame`.
- **The limit.**
  - Laws at an effectful callback carry a frame hypothesis that typing implies and the machine
    cannot see.
  - Discharging that hypothesis once from the logical relation is not done.

**(U3) Justified optimizations — yes, at pure callbacks and distinct cells.** Each item is an
equivalence of runs.

| law | what a compiler may do |
|---|---|
| `over_id` | erase a borrow that returns its focus unchanged: every run is `(ℓ, ())` with the heap untouched |
| `over_fuse` | fuse two sequential accesses through one lens into one: one load and one store instead of two each |
| `Optic.runs` | reuse the source handle across any borrow: the handle returned is the one passed in |
| `withload_read`, `get_copy` | answer two reads through copies of an `Imm` with one load |
| `lift_cell` | treat the store-back of `lift`/`withswap` as a no-op, **only if** the callback does not write the lender's cell (a frame condition, as above) |

**(U4) Fewer mechanisms — partial.**
- **One interface covers six borrow shapes.** Whole-cell borrow, reborrow, `Imm` borrow, a
  place-record leaf, a family and a variant payload are instances of one `Optic` structure,
  with one `lift`, one `comp` and one Rezip.
- **Two shapes needed separate structures.**
  - The `Imm` getter (`withload`): no source comes back.
  - IterMut: many foci, the callback under `!`, and `T` fixed to `1`.
- **`Core` loses no mechanism.** `swapField`, `loadField`, `loadCase`, `withborF2` and
  `withborS` remain separate derived rules; this experiment organises them and replaces none.
- **Affine composition is not built.** Composing a lens with the linear prism would put the
  unused callback, a `U C`, under the outer lifetime's box. `VOutlives` has no rule at `U C`
  (`Core/README.md`, Open), so I built composition for lenses only.

## What it means for "borrowing = temporally ordered residuation"

The experiment separates the two halves of the hypothesis along the line between the machine and
the type system.

- **The spatial half, residuation, is a machine fact.**
  - Every instance returns exactly its source (Rezip), holds the residual unchanged, and hands
    out the focus. The residual is the unborrowed leaf, the variant's tag cell, the list's next
    cells, or the lender's cell under `lift`.
  - Composition composes the foci.
  - These laws hold on every run with no hypothesis on the callback (`Optic.runs`, `lift_cell`,
    `tag_frozen`).
- **The temporal half, the lifetime order, appears only in typing.**
  - It is the fresh `'x ⊏ ⊓Δ` of each borrow and the nesting `'y ⊏ 'x` of `comp`.
  - Every law that needs more than residuation needs a frame fact: `PureFn` for `over_id` and
    `over_fuse`, distinct cells for fusion, `ElemFrame` for the shape law. Such a fact says the
    callback does not touch the lender's cells while the borrow is live.
  - That is what the lifetime discipline guarantees through `fundamentalC`, and what the bare
    machine cannot see.
- **The results fit the decomposition "residuation + a well-bracketed temporal order".**
  - Optics are its external, stateless view. They are adequate as an interface, as §6.1 of the
    survey predicted.
  - The one borrow form not derived is L2, where the temporal order would have to be shared
    across a dynamic number of lenders.
  - Whether the frame facts follow from the logical relation as a free theorem is the next
    question. This experiment does not settle it.
