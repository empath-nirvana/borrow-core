# CBPVMu: `μ` as a value-type former of the typed world, with borrowing under `μ`

**Question.** `docs/scope-recursion.md` §6 names R4 as the main risk of recursive types: add `μ`
to CBPVWorld's `VTy`, give the relation, the shapes and the records their `μ` cases, and find
out whether the typed world's choosers and invariants accept a recursive payload. Then: does
`withload` work at `Imm 'a L` for the boxed list `L = μX. 1 ⊕ Ref X`, and does a borrowed fold
(recursion nested inside `withload` callbacks, each at a fresh `'b ⊏ 'a`) work?

Build: `lake build CBPVMu`. `experiments/CBPVWorld` is forked into `CBPVMu/` under the
namespace `BoCa.Fig16.LogRel.CBPVMu`, without its embedding files (`Embedding`,
`EmbeddingExamples`). Everything below it (`Paper`, `Support`) is imported unchanged.
`DelayNaive.lean` also imports `experiments/LeafPlaces`' `Steps.lean` (step inversion).

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
| `Fundamental.lean` | `roll`/`unroll`, `foldImm`, `foldOwn`, `foldReuse` in `CDerives`; their compatibility lemmas |
| `Fix.lean` (new) | `experiments/Recursion/Recursion/Fix.lean` at this world's `wpTS`, with `substAll_closed`; imported before `Fundamental.lean` |
| `Sized.lean` (new) | `dsize`, `dsize_del_lt`, `dsize_tail_lt`, `rebChooseTW_sized`, `withload_sized`, `WitLt` |
| `FoldImm.lean`, `FoldOwn.lean`, `FoldReuse.lean` (new) | the fold rules' terms and soundness (`foldImm_compatX`, `foldOwn_compatX`, `foldReuse_compatX`); `FoldReuse.lean` also `wpTS_swap` |
| `Lists.lean`, `Count.lean`, `CountFree.lean`, `MapMut.lean`, `Folds.lean` (new) | the programs |
| `Blocks.lean` (new) | `experiments/LeafPlaces`' block view at `VTy`: `Shape`, `refTy`, `allocS`/`freeS` and their derived typing, `Packed`, `packed_node`, block allocation (`wpTS_allocS`) |
| `CommonList.lean` (new) | the common list shape `μX. 1 ⊕ Ref (N ⊗ X)` with each node one block; sum, map, `toPure` and free by the fold rules |
| `ReuseList.lean` (new) | the in-place map over the common list shape by `foldReuse`; `take`/`fill`; node addresses before and after |
| `Types.lean`, `Records.lean`, `Relation.lean` | `CTy.delay A` (`D A = νX. F(A ⊕ U X) & F 1`) and its free variables, lifetime substitution, `CTyEq`; `cC`'s `delay` clause, the greatest fixed point `delayRel` of `delayF` |
| `ShapeMu.lean`, `RelationFacts.lean`, `Computation.lean` | the `delay` cases of `TyEq`, `cC_congr`, `cC_tyEq`, the stack semantics, `cC_step` and `cC_bind` |
| `DelayRel.lean`, `Delay.lean`, `DelayApprox.lean`, `DelayPrograms.lean`, `DelayNaive.lean` (new) | the delay type and guarded recursion (*The delay type*, below) |

`Wp`, `Reborrow`, `FrameRules`, `Compatibility`, `Computation`, `Compat` and `Examples` are
CBPVWorld's files with only the namespace changed (`bindE` is defined in `FoldImm.lean`, which
`Fundamental.lean` imports, instead of `Examples.lean`). `TW`, the invariants (`ChainInv`, `DeepInv`,
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
(`roll_compatX`, `unroll_compatX`: the unroll equation under `wpTS_mono`) and the fold rules
`foldImm`/`foldOwn` (`foldImm_compatX`, `foldOwn_compatX`, `foldReuse_compatX`; see *The fold rules* and *The owned fold with reuse*). `adequacyC`,
`theorem32` and `corollary33` are unchanged.

## Step 5 — programs

In (a)–(c) recursive functions are Z-combinator terms (`Fix.lean`), not `CDerives` rules. Each
is given its semantic type by hand; programs are `CDerives` derivations in a context holding the
recursive functions, instantiated at their values. The fold rules (*The fold rules*, below)
replace the hand proofs for folds.

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
- `wpTS_swap` (`FoldReuse.lean`): `swap ℓ v` at `ℓ ↦ w` as a `wpTS` rule (6.169's steps).
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
`withload_sized` also takes a bound `m` and asks the callback only at `β < m`, as
`withload_compatX` asks it below `⊓Δδ`. In `countFree` the callback is proved by hand (not by
`fundamentalC`), since its recursive call is typed only on the smaller borrows; the rule
`foldImm` below removes the hand proof.

**The program.**
- `countFree = Z (λself. Λ. λl. withload l (Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. self [] t to
  n. inj₂ n}))`, no fuel. `countFree_body`: induction on a bound of the witness size.
  **`countFree_semV : SemV Δ [] countFree (!U(∀'a. Imm 'a L ⊸ F N))`**, at the real type.
- `countFreeProg`: build a 3-cell list, put it in a cell, borrow it immutably, count, end the
  borrow, free the cell and the list, return the count; `countFreeProg_derives` at `F N` in the
  context `countFree, freeAll`; `countFreeProg_runs`: from the empty memory to a numeral and the
  empty memory; `countFreeProg_eval`: the interpreter returns `3` with no cell left.

## The fold rules

Structured recursion as two `CDerives` constants, so that a fold is `foldImm alg` or
`foldOwn alg` with the algebra derived by the ordinary rules, and `fundamentalC` covers every
program that uses them. No sizes in types.

**The class** (`FShape`). `T ::= A | Ref X | X | T ⊗ T | T ⊕ T` with every leaf `A` closed
(`FShape.WF`) and `T ≠ X` (`FShape.Guarded`); `F.ty` is the body with `X` the type variable `0`.
`NoMut 0` and the closedness of `μX. T` follow (`FShape.noMut_ty`, `FShape.Cl_ty`). The boxed
list `μX. 1 ⊕ Ref X`, the numerals `μX. 1 ⊕ X`, `μX. 1 ⊕ (B ⊗ Ref X)` and the trees
`μX. B ⊕ (Ref X ⊗ Ref X)` are in it. Not in it: `X` under a `Ref` of a compound
(`L′ = μX. 1 ⊕ Ref (N ⊗ X)`), `X` under `Imm`, `Mut`, `!`, `[@a]`, and a body that is `X`.

**`foldImm`** (`FoldImm.lean`).

    Γ dead   T ∈ FShape   'y ∉ fv(μX. T)   'y ∉ fv(R)   ∀Δ′ @a. Δ′ ⊢ R ⊐ @a
    ─────────────────────────────────────────────────────────────────────────────────
    Δ; Γ ⊢ foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)

- `A_R = T.res 'y R`: `Imm̲ 'y T` with `R` at every `Ref X` and head `X`. `FShape.view_eq`: the
  view `withload` hands over at `Imm 'y M`, `M = μX. T`, unrolled, is
  `Imm̲ 'y (T[M/X]) = T.resRH 'y (Imm 'y M) (Imm̲ 'y M)`; `A_R` is it with `R` at both.
- The term is closed and generated from the shape: `foldImm = λg. Λ. λl. travK (Ref X) h l` with
  `h = λw. self g w`, `self = Z (λself. λg. λu. travK T (λw. self g w) u to r. g [] r)`, and
  `travK` at a leaf `w`, at `Ref X` `withload w (λ_. h)`, at `X` `h w`, at `⊗`/`⊕`
  componentwise. The machine is unchanged.
- `R` outlives every lifetime: each result leaves a `withload` callback at a fresh `'x` as
  `['x] R` (6.60, `vC_outlives`). The algebra is called at the load's lifetime `β ⊏ ⊤`, which
  `withload_sized`'s bound supplies.
- `foldImm_compatX`: `trav_spec` is induction on the shape, with the two recursive calls as
  hypotheses — through a sub-borrow (`PSpec`: `withload` at witness size `< n`) and on a smaller
  view (`HSpec`, head `X`). `Good M w χ n`: every `Ref` position of `w` holds, in `χ`, a cell
  whose witness has fewer than `n` cells. `good_of_image`: the view `withload` hands over is
  `Good` at the loaded witness's size (`own_split`, `typed_image_pos`, `dsize_del_lt`), at every
  `Ref` position of `T`, not only the list's tail. `pSpec_succ`: `withload_sized`, then the
  view's `HSpec`, then 6.60 for the callback's `['x]`. `hSpec_all`: induction on `n`, inside it
  on the view value's size.

**`foldOwn`** (`FoldOwn.lean`).

    Γ dead   T ∈ FShape
    ─────────────────────────────────────────────────────
    Δ; Γ ⊢ foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)

- `A′_R = T.resO R`: `T` with `R` at every recursive position; any `R`.
- `travO` at `Ref X` is `h (free w)`, at `X` `h w`; `foldOwn = λg. λw. self g w`.
- `foldOwn_compatX`: `travO_spec` by induction on the shape; `hOSpec_all` by strong induction on
  a bound of the owned resource's `dsize` (`dsize_tail_lt` at a freed cell), inside it on the
  value's size.

**Programs with no hand proof** (`Folds.lean`). Each fold is `foldImm alg` or `foldOwn alg`
with `alg` a `CDerives` derivation; each program is one closed `CDerives` derivation at `F R`
(`d_foldProg`: build, `alloc`, `withbor` at `Imm 'x M`, fold inside the borrow, end the
borrow, `free`, free the structure with an owned fold), run by `theorem32` and by the
interpreter.

| Fold | Type | Program | Result |
|---|---|---|---|
| `countFoldE = foldImm countAlg` | `!U(∀'a. Imm 'a L ⊸ F N)` (`countFold_semV` by `fundamentalC`) | `countFoldProg` | `3`, no cell left |
| `freeFoldE = foldOwn freeLAlg` | `U(L ⊸ F 1)` (`freeFold_semV` by `fundamentalC`), `freeAll` | used by `countFoldProg` | |
| `anyListE = foldImm anyLAlg` | `!U(∀'a. Imm 'a (μX. 1 ⊕ (B ⊗ Ref X)) ⊸ F B)` | `anyListProg` on `[false, true, false]` | `true`, no cell left |
| `anyTreeE = foldImm anyTAlg` | `!U(∀'a. Imm 'a (μX. B ⊕ (Ref X ⊗ Ref X)) ⊸ F B)`, two recursive calls per node | `anyTreeProg` on `node(false, node(false, true))` | `true`, no cell left |
| `natCopyE = foldImm countAlg` | `!U(∀'a. Imm 'a N ⊸ F N)`, recursion at a head `X` | `natCopyProg` on a cell holding `3` | `3`, no cell left |
| `freeBListE`, `freeBTreeE`, `freeNatE` | `foldOwn` at the three other shapes | the frees of the programs above | |

`*_runs` (adequacy) and `*_eval` (the interpreter, `decide`) for each program.

**Not done here** (done in *The common list shape*, below, with each node one block): a sum over
`L′ = μX. 1 ⊕ Ref (N ⊗ X)`, and `toPure`/`mapInc` through `foldOwn`: `L′`, with the node in one
cell, is outside the class. A borrowed fold at `Ref S` with `X` inside a compound `S` would load
`S` in a nested `withload`, and the leaves of `S` would be viewed at the inner load's lifetime,
which `A_R` at `'y` does not name. I have not derived such a rule and have not verified that any
obstruction is real. `foldImm`'s `R` must outlive every lifetime, so a fold returning a borrow
into the structure is not covered.

## The common list shape

Rust's `Box<Node { val, next }>` list is `μX. 1 ⊕ Ref (N ⊗ X)`. An owned `Ref` of an unboxed
product is a block, and a block's handle is the family of its leaf references
(`experiments/LeafPlaces`). So for one block `Ref (A ⊗ B)` is `Ref A ⊗ Ref B`, and the list is
`μX. 1 ⊕ (Ref N ⊗ Ref X)`, which is in `FShape`. Sum, map and `toPure` over it need no new fold
rule: only the block view, then `foldImm`/`foldOwn`.

**The form chosen: the split form is the representation.** `Ref (A ⊗ B)` is not a type former
of its own. A block handle's type is `refTy σ`, defined as the leaf family
(`refTy (node s₁ s₂) = refTy s₁ ⊗ refTy s₂`), so `Ref (A ⊗ B)` *is* `Ref A ⊗ Ref B`
(`refTy_pair`, `rfl`). The list's body `1 ⊕ refTy (N ⊗ X)` is `clistF`'s (`clistF_ty`, `rfl`).
This is option (a) of the task. There is no pack or unpack rule, so no term, typing rule or
relation clause is added. Splitting a handle is the identity (`packed_node`). The joining
direction is only sound, for a one-word handle, on leaves from one block: `crossPack` shows a
pair of references from two blocks has the same type. Here the only producer of a node handle
is `allocS`, which allocates one block (`wpTS_allocS`, `consC_block`). Keeping owned leaves from
being re-paired across blocks remains a checker rule, as in LeafPlaces. Option (b) (an unpack
rule and a pack rule restricted to block-origin leaves) would need a typing predicate that
tracks block origin, which the calculus does not have. `Ref` does not distribute over `⊕`: a
variant's leaf layout depends on its tag. That is out of scope here.

**Ported** (`Blocks.lean`, the same Lean as LeafPlaces at `VTy` and this world's `wpTS`).
`Shape`, `size`, `refTy`, `valTy`, `addr`; `allocS`/`freeS` as closed terms, typed leaf by leaf
through the existing `alloc`/`free` rules (`d_allocS`, `d_freeS`); `Packed`, `packed_node`;
`WpAt` and `wpAt_alloc`; block allocation `wpTS_allocS` (base above every allocated location,
leaves at `b, b+1, …`). Machine and `Loc = ℕ` unchanged. `withborS` (borrowing a block's leaves
at one lifetime) is not ported. The fold borrows the list through `withbor` of a cell holding
it, and each node's leaves are then read through `withload` at nested lifetimes.

**Derived programs, no hand proof** (`CommonList.lean`). A node is `consC n t =
inj₂ (allocS (N ⊗ L) (n, t))`, one block.

| Function | By | Type (`fundamentalC`) |
|---|---|---|
| `sumCE = foldImm sumAlg` | the algebra sees `1 ⊕ (Imm 'y N ⊗ N)`; it copies the payload with `natCopy` (a `foldImm`, derived at the algebra's lifetime context with its binder at `'1` and instantiated at `'y`, `d_natCopyAt`) and adds with `addE = foldOwn addAlg : N ⊸ F (U(N ⊸ F N))` | `!U(∀'a. Imm 'a L ⊸ F N)` (`sumC_semV`) |
| `mapIncCE = foldOwn mapCAlg` | frees the value leaf, allocates the incremented node as a fresh block | `U(L ⊸ F L)` (`mapIncC_semV`) |
| `toPureCE = foldOwn tpCAlg` | frees the value leaf | `U(L ⊸ F P)` (`toPureC_semV`) |
| `freeCE = foldOwn freeCAlg` | frees the value leaf, frees the numeral by `freeNat` | `U(L ⊸ F 1)` |

| Program | Derivation | Runs | Interpreter |
|---|---|---|---|
| `sumProg`: build `[1, 2, 3]`, borrow immutably, sum, end, free | `sumProg_derives` (`d_foldProg`) | `sumProg_runs` | `6`, no cell left (`sumProg_eval`) |
| `mapProgC`: build `[0, 0, 0]`, borrow mutably, `withswap` + `mapIncCE`, end, free the cell, `toPureCE` | `mapProgC_derives` (`MapMut.lean`'s program at the list of blocks; closed by binding the two folds) | `mapProgC_runs` | `[1, 1, 1]`, no cell left (`mapProgC_eval`) |

**Blocks.** `consC_block`: at every frame the typed world admits, a node is allocated as the
handle `(ℓ, ℓ + 1)` at `Ref N ⊗ Ref L`. `buildC_blocks`, `mapIncC_blocks`: the interpreter's
memory after `buildC`, and after `mapIncCE`, holds every node at adjacent cells `(ℓ, ℓ + 1)`, with
the payloads `[1, 2, 3]` and `[1, 1, 1]`.

**Against the in-place map.** `foldOwn` frees each `Ref X` cell before its algebra runs, so
`mapIncCE` rebuilds the list in fresh blocks. The in-place map is `foldReuse`, below.
`MapMut.lean`'s `mapInc` over `L′` (the node one cell holding a pair) stays a hand proof: `L′`
is outside `FShape`.

## The owned fold with reuse

Functional-but-in-place (Perceus-style reuse): the owned fold hands its algebra the cells it
consumed, so the algebra can rebuild into them.

    Γ dead   T ∈ FShape
    ──────────────────────────────────────────────────────
    Δ; Γ ⊢ foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)

- `A″_R = T.resR R`: `T` with `R` at a head `X` and **`Ref 1 ⊗ R` at every `Ref X`**: the
  emptied cell and the fold of its former content. Any `R`.
- **No new type former.** The reuse token ("`Hole`") is an owned `Ref 1`. `swap : Ref A ⊸ B ⊸
  Ref B ⊗ A` already changes a cell's content type, so the token is made by `swap w ()` and
  consumed by `swap c x`. Two closed derived functions name the operations (`ReuseList.lean`):
  `take = λr. swap r () : Ref A ⊸ F (Ref 1 ⊗ A)` and `fill : Ref 1 ⊗ A ⊸ F (Ref A)` (swap in, drop
  the `()`). In this model every leaf is one cell, whatever its type, so a token of `Ref 1` can be
  filled at any `A`. A token is ordinary owned data. The algebra may also free it, or return it.
- The term is `foldOwn`'s with the `Ref X` clause of the traversal replaced: `travR` at `Ref X` is
  `swap w () to q. let (c, v) = q in h v to r. (c, r)`, where `foldOwn`'s is `h (free w)`.
  `foldReuse = λg. λw. self g w`, recursion by the Z combinator; machine unchanged.
- `foldReuse_compatX`: `foldOwn_compatX`'s proof with the `Ref X` case of the traversal
  (`travR_spec`) through `wpTS_swap`. The measure is the same: the content's resource is smaller
  than the cell's (`dsize_tail_lt` at the cell before the swap), and the emptied cell is carried
  as a frame across the recursive call. No world invariant is added and `vC` is unchanged.
  `fundamentalC` gains the case.

**The in-place map, derived** (`ReuseList.lean`). Over `L_E = μX. 1 ⊕ (Ref E ⊗ Ref X)` the
algebra at a cons node sees `(rn, (c, t)) : Ref E ⊗ (Ref 1 ⊗ L_E′)`.
`mapRAlg f = case r {inj₁ u. inj₁ u | inj₂ p. let (rn, q) = p in let (c, x) = take rn in
inj₂ (fill (c, f x), fill q)}` refills the value leaf with `f` of its content and the emptied
next leaf with the mapped tail. It is a `CDerives` derivation for any closed `f : E ⊸ F E′`
(`d_mapRAlg`), and `mapRE f = foldReuse (mapRAlg f) : U(L_E ⊸ F L_E′)` (`d_mapR`).

| Function | Type (`fundamentalC`) |
|---|---|
| `mapIncRE = foldReuse (mapRAlg inc)` | `U(L ⊸ F L)` (`mapIncR_semV`) |
| `isZeroRE = foldReuse (mapRAlg isZero)` | `U(L_N ⊸ F L_B)` (`isZeroR_semV`): the element type changes |

| Program | Derivation | Runs | Interpreter |
|---|---|---|---|
| `mapProgR`: build `[0, 0, 0]`, borrow mutably, `withswap` + `mapIncRE`, end, free the cell, `toPureCE` (`MapMut.lean`'s program) | `mapProgR_derives` | `mapProgR_runs` | `[1, 1, 1]`, no cell left (`mapProgR_eval`) |

**In place** (the interpreter, `decide`; `nodesOf` reads the list as `(address, payload)` with
each node at adjacent cells `(ℓ, ℓ + 1)`):

- `buildC0_nodes`: the built `[0, 0, 0]` has nodes at `4, 2, 0`.
- `mapIncR_inPlace`: after `mapIncRE`, `[1, 1, 1]` at `4, 2, 0`, the same addresses.
- `mapIncC_moves`: after `foldOwn`'s `mapIncCE`, the nodes are at `10, 8, 6`.
- `isZeroR_inPlace`: `[0, 1, 0]` at `4, 2, 0` becomes `[true, false, true]` at `4, 2, 0`.

**A map that changes the element type** reuses the cells too (`isZeroRE`, `N → B`). In this
model a leaf is one cell at every type, so "leaf sizes match" holds of every pair of types; a
layout with sized leaves would need the token to carry its size, which is not modelled.

**Not done.** A shared (`Imm`/`Mut`) structure is not reused: `foldReuse` consumes an owned one.
The token is not restricted to the node it came from: the algebra may put a cell of one node
into another (still one cell per leaf, still owned); joining leaves from two blocks into one
node handle is `CommonList`'s `crossPack` concern, a checker rule, unchanged here.

## The delay type and guarded recursion

**Question.** General recursion as one rule, by a guarded `fix` on the delay type
`D A = νX. F(A ⊕ U X) & F 1`: `next` (`π₁`) returns `now a` (`inj₁ a`) or `later t` (`inj₂ t`,
`t : U(D A)` the rest), and `close` (`π₂`) disposes of an unfinished computation, since the state
is linear. Does interpreting `ν` by its finite approximations agree with the direct greatest
fixed point, how is `▷` expressed, and do the rule, the Fundamental Property and adequacy hold?

**The type.** `CTy.delay A`, a computation type, so the typed world's records never see it (`U`
is a leaf). `cC (.delay A) = delayRel (vC true A)`, the greatest fixed point
`⋃{R | R ⊆ delayF R}` written as `∃ R` (`Relation.lean`), with the candidate indexed by the
record list and the expression at a fixed `δ` (`D A` binds no lifetime). `delayF` is monotone by
`wpTS_mono` alone; `cC_delay_iff`: `⟦D A⟧ = ⟦F(A ⊕ U(D A)) & F 1⟧` (`DelayRel.lean`). Every
existing result builds with the new case; the new cases of the `CTy` inductions go through the
unrolling.

**Step 1: approximations** (`DelayApprox.lean`). `approx 0 = ⊤`, `approx (n+1) = delayF
(approx n)`, `approxLim = ⋂ₙ approx n`.
- `delayRel_le_approxLim`: the greatest fixed point lies below the intersection.
- `approxLim_le_delayRel`: the converse holds if `wpTS` commutes with the intersection of a
  decreasing chain of postconditions (`WpChainCommutes`); `delayRel_iff_approxLim` under it.
  Inside `delayF` everything else commutes (`delayQ_lim`): the `⌜w = injᵢ v⌝ ⋆ _` splits are
  forced, the disjunction is decided by the value, `thunkR` is a `∀`.
- What is left is the `∃` in `wpTS` over the post-state witness
  `(ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls')`: each `n` may choose its own ghost world, frame
  part and record list. Over a finite witness type a decreasing chain commutes with `∃`
  (`exists_forall_of_finite`); over `ℕ` it does not (`not_exists_forall`, `n ≤ w`). `wpTS`'s
  witnesses range over worlds (lifetimes in `ℕᵒᵈ`, nested witnesses) and lists, so the finite
  case does not apply; the delay functor's own branching (`π₁`/`π₂`, `inj₁`/`inj₂`) is finite
  but is not where the `∃` is. I have not derived `WpChainCommutes` and have not verified that
  any obstruction to it is real.
- The rule below does not need the approximations: it is proved at the greatest fixed point.

**Step 2: `▷`, by the shape of the step's type; no new former.**
- `f = λd. later (g d)` with `g : U(D A) ⊸ D A` typed like any other term is **not** a
  guardedness condition (`DelayNaive.lean`). `skip d = ⟨(d π₁) to x. case x {inj₁ a. now a |
  inj₂ t. t π₁}, d π₂⟩` is a derivation (`d_skip`, `skip_sem`), and `N = later (skip N)` (`NV`,
  by the Z combinator) is not in `⟦D 1⟧` (`naive_not_delay`, `naive_not_sem`): `N`'s `next`
  returns `later t` (`nv_next_run`), and every run of `t`'s `next` revisits its start
  (`cyc_step`, 14 deterministic steps), so none terminates (`tv_next_diverges`). `skip` observes
  its argument twice per `later` it emits.
- A `▷` former read as the one-step shift on approximations needs Step 1's converse, and every
  term to be non-expansive at every level; the unindexed relation gives neither.
- What works: the step's `next` returns, under `F`, a result or a **state**, never a `D A`, so
  it cannot observe the recursive computation. `later` is `inj₂` of the next state; the rule
  supplies the recursive call.

**Step 3: the rule** (`Delay.lean`, `Fundamental.lean`).
- `fixD : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`, a closed constant (`fixDV`, the Z combinator
  over `fBD`), a `CDerives` rule (`CDerives.fixD`) with `delayIn`/`delayOut` (`D A` and its
  unrolling, on the same term). `fixD step s` is the fixed point
  `f s = ⟨step s π₁ to x. case x {inj₁ a. now a | inj₂ s′. later (f s′)}, step s π₂⟩`
  (`etaD_next`, `etaD_close`, `nextKS_now`, `nextKS_later`).
- **`fixD_compatX`**: coinduction with the candidate `{fixD step s | s ∈ 𝒱⟦S⟧}` (`candD`,
  `candD_post`). No approximation and no index.
- `fundamentalC` covers `fixD`, `delayIn`, `delayOut`; `adequacyC`, `theorem32` are unchanged.

**Step 4: adequacy** (`DelayPrograms.lean`). `driveE n` observes `d : U(D A)` at most `n`
times: `inj₁ a` at `now a`, else `close` after the `n`-th `later` and `inj₂ ()`. `d_drive`: it
derives at `F(A ⊕ 1)` for every `n`, so for a closed `e : U(D A)`, `e to d. driveE n` is an
ordinary closed program (`drive_derives`). **`drive_runs_unit`** (`D 1`) and **`drive_runs_nat`**
(`D N`): from the empty memory to `inj₁` of a result or `inj₂ ()`, and the empty memory.

**Step 5: programs** (`DelayPrograms.lean`), each a derivation (`progD`: state, `fixD step`,
the thunk `⟨(f s) π₁, (f s) π₂⟩`, the driver) with no hand proof; runs by `theorem32`, and the
interpreter by `decide`.
- (a) `countDownProg`: state `(n, acc) : N ⊗ N`, `now acc` at `n = 0`, else
  `later (n - 1, acc + 1)`; `close` frees both numerals. From `(3, 0)`, ten observations:
  `countDownProg_runs`; the interpreter returns `now 3` with no cell left (`countDownProg_eval`).
- (b) `loopProg`: `fixD (λs. ⟨return later s, return s⟩) ()`, never `now`; five observations
  then `close` (`loopProg_runs`, `loopProg_eval`: closed, no cell).
- (c) `counterProg`: state `r : Ref N`; `next` increments the cell in place by two `swap`s and
  emits `later r`; `close` frees the cell and its numeral. Four observations then `close`
  (`counterProg_runs`, `counterProg_eval`: closed, no cell).

**Not done.** `fixD` is iteration with a state: a recursive call in non-tail position needs an
explicit stack in the state (a `μ` list) or a `bind` on `D`, which is expressible as a `fixD`
with state `U(D A) ⊕ U(D B)` and a `!` continuation but is not written here. Collatz is not
written (unary halving is a fold of its own). `D A` has no `Imm̲`/`Mut` interaction beyond `U`
being a leaf. The continuity question of Step 1 is open.

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
