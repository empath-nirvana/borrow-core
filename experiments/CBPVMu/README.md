# CBPVMu: `μ` as a value-type former of the typed world, with borrowing under `μ`

**Question.** `docs/scope-recursion.md` §6 names R4 as the main risk of recursive types: add `μ`
to CBPVWorld's `VTy`, give the relation, the shapes and the records their `μ` cases, and find
out whether the typed world's choosers and invariants accept a recursive payload. Then: does
`withload` work at `Imm 'a L` for the boxed list `L = μX. 1 ⊕ Ref X`, and does a borrowed fold
(recursion nested inside `withload` callbacks, each at a fresh `'b ⊏ 'a`) work?

Build: `lake build CBPVMu`. `experiments/CBPVWorld` is forked into `CBPVMu/` under the
namespace `BoCa.Fig16.LogRel.CBPVMu`, without its embedding files (`Embedding`,
`EmbeddingExamples`). Everything below it (`Paper`, `Support`) is imported unchanged.

Every result's axioms are `[propext, Classical.choice, Quot.sound]` or a subset. There is no
`sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

## What changed against CBPVWorld

| File | Change |
|---|---|
| `Types.lean` | `VTy.tvar n` (de Bruijn) and `VTy.mu A`; `rename`/`subst`/`inst`/`Cl` and their lemmas (`experiments/Recursion/Recursion/ImmMu.lean`'s set at `VTy`); `Occ`, `NoMut`; `immG` and its laws; `Imm̲` at `μ`; `VOutlives.tvar`/`.mu` |
| `Records.lean` | `RefPos.mu`, `MutPos.mu` (a closed `μ` is read at its unrolling); `TyEq` at `tvar`/`μ` |
| `World.lean` | `vShapeE` with a type-variable environment; `vShape` is `vShapeE none` |
| `Relation.lean` | `vCE` with a type-variable environment; `vC` is `vCE none` |
| `ShapeMu.lean` (new) | the shape relation at `μ`: substitution, monotonicity, unroll, induction principle, `δ`- and `TyEq`-congruence; `TyEq` is an equivalence and commutes with substitution |
| `RelMu.lean` (new) | the relation at `μ`: the same set, plus `vC_mu_ind` |
| `Images.lean`, `Invariant.lean`, `ReborrowShapes.lean`, `RelationFacts.lean` | the lemmas that went by induction on a type now go by the induction principles, or by induction on a position (list below) |
| `Fundamental.lean` | `roll`/`unroll` in `CDerives`, `roll_compatX`/`unroll_compatX` |
| `Fix.lean` (new) | `experiments/Recursion/Recursion/Fix.lean` at this world's `wpTS`, with `substAll_closed` |
| `Lists.lean`, `Count.lean`, `CountFree.lean`, `MapMut.lean` (new) | the programs; `CountFree.lean` also `withload_sized`, `MapMut.lean` also `wpTS_swap` |

`Wp`, `Reborrow`, `FrameRules`, `Compatibility`, `Computation`, `Compat` and `Examples` are
CBPVWorld's files with only the namespace changed. `TW`, the invariants (`ChainInv`, `DeepInv`,
`JointDeep`, …) and the choosers are unchanged.

## Step 1 — syntax

- `VTy ::= … | X | μX. A`, iso-recursive, de Bruijn. `U C` is a leaf for type variables:
  `subst` does not enter it. So `X` never occurs in a `⊸` domain, and `X` under a `U`-codomain
  is not bound by the enclosing `μ` (it reads the empty environment). W-types through `U` are
  therefore not expressible here.
- Positivity: `NoMut 0 A`, "`X` occurs in no `Mut` payload" (§2.2: the `Mut` clause stores its
  predicate by an equation).
- `Imm̲ 'b (μX. A) = μY. Imm̲ᵡ 'b A` (`VTy.immReborrow`'s `mu` clause, through `immG`). The laws
  used: `immReborrow_eq_immG`, `immReborrow_eq_immReb` (closed types), `immReborrow_unroll`
  (`Imm̲ 'b (A[μX.A/X]) = (Imm̲ᵡ 'b A)[Imm̲ 'b (μX.A)/Y]` at a closed `μ`), `immReborrow_mu`,
  `noMut_immG` (the output of `Imm̲` has no variable under `Mut`).
- `CDerives.roll` (`A[μX.A/X] ⊢ μX. A`, premises `NoMut 0 A` and `μX. A` closed) and
  `CDerives.unroll`, typing rules on the same term; no machine change.
- `VOutlives.mu : VOutlives Δ a A → VOutlives Δ a (μX. A)` with `VOutlives.tvar`, the scope
  note's `T[1/X]` read as "`X` outlives `@a`". `VOutlives.unroll` carries it to the unrolling.

## Step 2 — the relation

- `vCE η b A ls δ v`: at `X` the environment's candidate (`tEnvP`); at `μX. A`
  `NoMut 0 A ∧ (μX. A closed under η) ∧ ∀ P, (∀ …, vCE (⟨μX.A, P⟩ · η) … A … → P …) → P …`, the
  least fixed point joint over the mode and the record list. The environment carries the closed
  type each variable stands for, and the `Imm` clause reads `CohE` at the closed type
  (`tClose`): the scope note's "`η` must carry the closed type".
- A `μ` whose variable occurs under `Mut`, or which is not closed, is empty. This makes the
  unfolding hold without a well-formedness hypothesis on the type; `roll` asks for both.
- **Unroll equation**: `vC_mu_iff : vC b (μX.A) ↔ NoMut 0 A ∧ (μX.A) closed ∧
  vC b (A[μX.A/X])` (`vC_unfold`, `vC_roll`), from `vCE_subst`, `vCE_rename`, `vCE_some`,
  `vCE_congr_occ` and `vCE_mono_at` (monotone in an entry whose variable is outside every `Mut`
  payload). The shape relation: `vShape_mu_iff` (monotone everywhere, so only the closedness
  guard).
- **Induction principles**: `vShape_ind` and `vC_ind` — a property closed under one unfolding of
  every clause (`sF`, `vF`: the clause with the relation and the property at the positions it
  recurses to, the unrolling at `μ`) holds of the relation, at every type. At `μ` this is induction
  on the least fixed point, elsewhere on the type; the proof is one generalisation over
  environments. `vC_mu_ind` is the least-fixed-point induction at one `μ`.
- `vC_local` (`Ext`-stability), `vO_obs`, `vC_vShape`, **`vC_outlives` (6.60)**,
  `obs_transfer` and `relabel_obs` are re-proved by `vC_ind`; `vC_congr`/`cC_congr` and
  `vC_tyEq`/`cC_tyEq` as environment-general structural inductions (`vCE_congr`,
  `vCE_tyEq`), since equalities pass through the least fixed point by congruence.

## Step 3 — borrowing under `μ`

- **6.131 at `μ`**: `reborrow_vShape` by `vShape_ind`; at `μ` the hypothesis unrolls
  (`vShape_unfold`) and the conclusion rolls through the unrolling law
  (`vShape_immReborrow_mu_iff`). `six132_shape` is unchanged.
- The position lemmas: `image_at_pos`, `own_split`, `refPos_blocks`, `mut_split`,
  `mut_split_den`, `mutPos_unique`, `mut_ref_blocks` go by induction on the position (the `μ`
  case unrolls the escrow's shape); `image_dom`, `image_dom_mut` by `vShape_ind`;
  `relabel_obs`/`image_vC_of_shape` (6.131 at the program's relation) by `vC_ind`.
- `RefPos.mu`/`MutPos.mu` carry the closedness of the `μ`, so a position through a `μ` makes
  the unrolling law of `Imm̲` available where the image's shape is unrolled.
- **The chooser and invariant proofs accept `μ` unchanged.** `Reborrow.lean`
  (`rebChooseTW_top`/`_deep`), `Invariant.lean`'s world invariants, `FrameRules.lean`, `Wp.lean`
  and `Compatibility.lean` (including `withload_compatX`, 6.175) build with no edit. What they
  needed was the per-type lemmas above and the two new position constructors. A chain through a
  list's tails is `Chain.step` iterated, each step a `RefPos.mu (sumR (ref …))`.
- `CohE` reading the syntactic type needed no change to `Coh`: records hold closed types, the
  `Imm` clause reads the environment's closed type, and a tail borrow's type `Imm 'b L` is
  coherent with the chain position whose pointee type is `L` itself.
- `withload` at `Imm 'a L`: `withload_compatX` holds at every payload, `μ` included. The
  callback receives `Imm̲ 'x L = μY. 1 ⊕ Imm 'x L` (`listL_immReborrow`) and unrolls it with
  `CDerives.unroll`. The boxed tree `μX. 1 ⊕ (Ref X ⊗ Ref X)` unrolls under `Imm̲` to
  `1 ⊕ (Imm 'b T ⊗ Imm 'b T)` (`treeT_immReborrow_unroll`, `vC_tree_immReborrow`); no tree
  program is written.

## Step 4 — Fundamental Property and adequacy

`fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j` over the judgment with `roll`/`unroll`
(`roll_compatX`, `unroll_compatX`: the unroll equation under `wpTS_mono`). `adequacyC`,
`theorem32` and `corollary33` are unchanged.

## Step 5 — programs

Recursive functions are Z-combinator terms (`Fix.lean`), not named constants and not
`CDerives` rules. Each is given its semantic type by hand; programs are `CDerives` derivations
in a context holding the recursive functions, instantiated at their values.

**(a) Build a list, free it** (`Lists.lean`).
- `build3_derives`: `inj₂ (alloc (inj₂ (alloc (inj₂ (alloc (inj₁ ()))))))` derives at `L` with
  `roll`.
- `freeAll = Z (λself. λl. case l {inj₁ u. u | inj₂ r. self (free r)})`; `freeAll_wp` by
  `vC_mu_ind` at `L`; **`freeAll_semV : SemV Δ [] freeAll (U (L ⊸ F 1))`** at the real type.
- `build3Free_runs`: from the empty memory to `()` and the empty memory;
  `build3Free_eval`: the interpreter agrees.

**(b) Borrowed traversal** (`Count.lean`; the fuel-free version is `CountFree.lean`, below).
- `N = μX. 1 ⊕ X`; `vC_natN`: a numeral holds no resource.
- `countN = Z (λself. λk. case k {inj₁ _. c₀ | inj₂ k′. self k′ to g. step[g]})` returns the
  counter at fuel `k`, a `!U(∀'a ⊏ ⊤. Imm 'a L ⊸ F N)`. `c₀ = Λ. λl. forget l; 0` (`d_c₀`) and
  `step[g] = Λ. λl. withload l cb` with
  `cb = Λ. λu. case (unroll u) {inj₁ w. w; forget g; 0 | inj₂ t. g [] t to n. inj₂ n}` (`d_step`,
  `d_cb`) are `CDerives` derivations. In `cb` the tail borrow `t : Imm 'x L` lives at the load's
  fresh `'x ⊏ 'a`, and the recursive counter is instantiated at `'x` (`∀E`, `entails_x_top`).
  `countN_wp` is induction on the fuel; `countN_semV : SemV Δ [] countN (U (N ⊸ F countTy))`.
- `countProg`: build a 3-cell list, put it in a cell, borrow it immutably (`withbor`), count with
  fuel 3 inside the borrow, end the borrow, free the cell and the list, return the count.
  `countProg_derives` at `F N` in the context `countN, freeAll`; `countProg_runs`: it runs from
  the empty memory to a numeral and the empty memory; `countProg_eval`: the interpreter returns
  `3` with no cell left.

**(c) An in-place map through `Mut`** (`MapMut.lean`).
- `L′ = μX. 1 ⊕ Ref (N ⊗ X)` (`NoMut` holds: `X` is under `Ref`, not `Mut`), and the pure list
  `P = μX. 1 ⊕ (N ⊗ X)`.
- `wpTS_swap`: `swap ℓ v` at `ℓ ↦ w` as a `wpTS` rule (6.169's steps).
- `mapInc = Z (λself. λl. case l {inj₁ u. inj₁ u | inj₂ r. swap r () to q. let (r₁, c) = q in
  let (p, tl) = c in self tl to tl′. swap r₁ (inj₂ p, tl′) to q₂. let (r₂, u) = q₂ in u; inj₂ r₂})`
  increments every payload in the same cells, with no fuel: `mapInc_wp` is induction on a bound of
  the owned list's resource size (`dsize_tail_lt`: the tail's resource is smaller than the cell
  and the tail together). **`mapInc_semV : SemV Δ [] mapInc (U(L′ ⊸ F L′))`**.
- `toPure : U(L′ ⊸ F P)` frees the list into a pure list (`toPure_vC`); a pure list holds no
  resource (`vC_pureL_empty`).
- `mapProg`: build `[0, 0, 0]`, put it in a cell, borrow it mutably (`withbor`, `Mut 'x L′`), and
  in the callback `withswap b (λl. mapInc l to l′. (l′, ()))`, forget the borrow; end the
  borrow, free the cell, `toPure` the list. `mapProg_derives` at `F P` in the context
  `mapInc, toPure`; `mapProg_runs`: from the empty memory to a pure list and the empty memory;
  `mapProg_eval`: the interpreter returns `[1, 1, 1]` with no cell left.
- `withswap` moves the whole list out of the `Mut` cell, so the per-cell recursion is on owned
  cells. A map that recurses through `Mut` borrows of the tails (a `Mut 'x L′` per cell, by
  nested `withbor`/`withswap` at the tail's position) is not written here.

## The borrowed fold

A fold through `withload`, with the recursion nested inside the callbacks at fresh lifetimes,
works both on a fuel (`Count.lean`) and on the list itself (`CountFree.lean`).

**The measure.** The number of cells of the borrowed `imm` cell's witness (`dsize`, a `Finset`
card over `PMap.finite`). It crosses the `withload` boundary because the view the callback
receives is an image `χ ∈ reb_β(σ)` of the loaded cell's witness `σ`, and at the tail `ℓ′`
`reb_β`'s `own` clause makes the tail's witness `q/ℓ′` for a piece `q ≤ σ` holding `ℓ′`
(`typed_image_pos`); so the tail's witness has fewer cells (`dsize_del_lt`, `dsize_image_lt`).
No world invariant is added, and `vC`, `withload_compatX` and every existing signature are
unchanged.

**The lemma (option 1 of the task).** `withload_sized` is `withload` at `Imm a T₁` whose
callback is asked only at the views `χ ∈ 𝒱⟦Imm̲ 'x T₁⟧` that are images `χ ∈ reb_β(σ)` of a
witness `σ` observable at `T₁` with `K σ`, where `K` is any property the borrowed cell's own
witness has. Its proof is `withload_compatX`'s (6.144, 6.134, 6.150) with two changes: the
payload predicate handed to `wpTS_load_I` carries `K`, and the chooser is wrapped by
`rebChooseTW_sized`, which returns with the chosen image the witness it is an image of (the
chooser already produces `χ ∈ reb_β(σ)`; `withload_compatX`'s callback premise drops it).
The callback is proved by hand (not by `fundamentalC`), since its recursive call is typed only
on the smaller borrows.

**The program.**
- `countFree = Z (λself. Λ. λl. withload l (Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. self [] t to
  n. inj₂ n}))`, no fuel. `countFree_body`: induction on a bound of the witness size.
  **`countFree_semV : SemV Δ [] countFree (!U(∀'a. Imm 'a L ⊸ F N))`**, at the real type.
- `countFreeProg`: build a 3-cell list, put it in a cell, borrow it immutably, count, end the
  borrow, free the cell and the list, return the count; `countFreeProg_derives` at `F N` in the
  context `countFree, freeAll`; `countFreeProg_runs`: from the empty memory to a numeral and the
  empty memory; `countFreeProg_eval`: the interpreter returns `3` with no cell left.

## Against the scope note

- §2.1's environment is `Option (Nat → TEnt)` with the closed type and the candidate per
  variable; `vC := vCE none` is a notation, so every existing statement keeps its signature and
  every clause of `vC` at the old formers is definitionally the old one.
- §2.2's table holds for the `Imm` payload, `!`, `[@a]`, `Ref`, `⊗`, `⊕`. `U`-codomain
  positions are not supported (U is a leaf for type variables).
- §2.4's clause needed a payload substitution per bound variable (`immG`, as P-Imm̲ found), and
  its unrolling law holds at closed `μ`; the relation's closedness guard supplies that at every
  `μ` a proof unrolls, and `RefPos.mu` carries it along positions.
- §2.4's "main risk" — the chooser and invariant proofs at `RefPos.mu` — needed no edit to the
  choosers or invariants.
