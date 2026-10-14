# PartialLife: does Core need every two lifetimes comparable?

Build with `lake build PartialLife`. There is no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`, and every declaration's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]` (407 declarations checked). The library does not import
this directory.

## The question

Core's lifetimes are `Life := ℕᵒᵈ` (`Paper/S5_Model/Definitions.lean:104`), a chain: every two
lifetimes are comparable. `experiments/DenseCarrier` proved that over a chain the cell equation has a
solution exactly when there is no infinite ascending sequence (`carrier_iff`), and that every such
chain has only the identity automorphism (`carrier_rigid`). Rigidity comes from "chain and
well-founded"; a well-founded partial order can have automorphisms that swap incomparable branches.

Suspension needs incomparable lifetimes: two interleaved tasks each borrow their own local across a
suspension, and neither borrow outlives the other. **Does BoLo's model, or Core's relation, need
every two lifetimes comparable, or only a well-founded measure?**

## The answer

* **The carrier needs only a well-founded measure.** Over every partial order the cell equation has
  a solution exactly when there is no infinite ascending sequence (`carrierP_iff`; with `⊓ᾱ`, `⊔ᾱ`
  the lattice's, `carrierL_iff`). Two branches of lifetimes under one `⊤` carry it, and swapping
  them is an automorphism (`two_branches_nonrigid`). Rigidity came from the chain.
* **The relation's clauses need only a partial order with a top.** The fragment `DenseCarrier`
  rebuilt (`1`, `⊗`, `U`, `Ref`, `[@a]`, `Mut`, `F`, `⊸`, `⊤`, `∀`) is rebuilt over a partial order
  of lifetimes: at `Life` it is Core's (`vP_id`, `cP_id`), and it is invariant under every order
  automorphism, the `∀` clause included (`vP_map`, `cP_map`, `semP_map`). No clause compares two
  lifetimes beyond `≤` and `<`; `@a ⊔ @b` and `@a ⊓ @b` are read as least upper and greatest lower
  bounds where they exist. The `∀` rules hold over it (`allI_compatP`; `allE_compatP` with its
  premise `Δ ⊨ @a ⊏ @b` read on the partial order).
* **Core's proofs compare two lifetimes in 12 places** (census class (iii)). Four do so only in
  the proof; three of them are proved again here without it (`Reproved.lean`). Eight state one of
  three order facts, and each fact is, in a lattice, *equivalent* to every two lifetimes being
  comparable
  (`sup_lt_iff_chain`, `lt_inf_iff_chain`, `le_of_not_lt_iff_chain`). All of them are about cells'
  strata: the composition of `imm` cells (a union's witness at `⊔ᾱ`, a composite's stratum at
  `⊓ᾱ`, `○`'s `mut(α ⊓ β)`) and one typed-world step (a reborrow's view no longer than its frame,
  through `StratumLe`). 2502 declarations rest on the eight, `fundamentalC` and `adequacyC` among
  them. On strata ordered partially each would be restated (an `imm` cell's stratum read pointwise
  over its borrowers, the non-strict stratum read directly), not proved again.
* **The statics read entailment on a chain.** `Δ ⊨ @a ⊏ @b` quantifies over `ℕ`-valued
  substitutions, and the checker's search has two strict rules that hold only on chains: it
  accepts `'x ⊓ 'y ⊏ 'a ⊓ 'b` and `'x ⊔ 'y ⊏ ⊤` at a context where both fail on a partial order
  (`checker_meet_not_partial`, `checker_join_not_partial`).
* **Two interleaved suspended borrows** at incomparable lifetimes, each beneath its own task's
  lifetime, form a typed world, are related at `Mut 'x 1 ⊗ Mut 'y 1`, `F (Mut 'x 1 ⊗ Mut 'y 1)` and
  `U (F (Mut 'x 1)) ⊗ U (F (Mut 'y 1))`, and stay related under the swap of the branches
  (`interleaved`).

**Kill criterion: not met.** No machine-checked result here shows that the cell equation or a rule
of the relation needs comparability in a way no well-founded partial order can supply. What is
machine-checked: the eight statement-level places state facts equivalent to comparability, about
Core's encoding of `imm` strata and of the non-strict stratum, each with a reading that holds on
partial orders; the checker's two strict rules fail on a partial order, a change to the statics;
and, with Core's cells kept on their chain, 6.65's choice of a fresh lifetime cannot be read beneath
one task's branch (`no_fresh_bound`), so the route `DenseCarrier` used for the borrow rules does not
carry over as it stands. No patch was tried.

## 1. Census

`scripts/Census.lean` walks the elaborated type and value of every declaration of `Paper/`,
`Support/` and `Core/` (14365 declarations) and records, at every application node:

* an instance argument whose class is applied to `Life` (the chain class `LinearOrder`, `SemilatticeInf`, `Max`,
  `Preorder`, `Decidable (a ≤ b)`, …), with the constant applied: what the constant asks of the order;
* an iff lemma that holds only on chains (`not_le`, `sup_lt_iff`, `lt_inf_iff`, `Nat.max_lt`, …) and
  the direction it is used in (`Iff.mp`/`Iff.mpr`), or a rewrite with it;
* a `Life` passed to an `ℕ` slot or an `ℕ` to a `Life` slot (a fact about `ℕ` used at `Life`), with
  the constant applied, as `DenseCarrier`'s census did;
* `Life.down`, `OrderDual.ofDual`/`toDual` at `ℕ`, `WellFounded.fix`, a proof built by `omega`;
* in declarations that mention the statics' `ℕ`-valued lifetimes (`SLife`, `Life.interp`,
  `LifeCtx.Models`, `EntailsLt`, `EntailsLe`), `ℕ`-instances beyond a partial order and `Nat`
  comparability lemmas.

`scripts/classify.py` puts each declaration in the strongest class one of its findings is in:

* **(iii)** compares two lifetimes no relation is known between (`le_total`, `le_of_not_gt`,
  `sup_lt_iff.mpr`, `lt_inf_iff.mpr`, `Nat.max_lt`, `Nat.le_total` at `Life`);
* **(iv)** reads that no lifetime lies strictly between `↓a` and `a` (`DenseCarrier`'s class (c));
* **(ii)** uses `⊓` or `⊔` of two lifetimes, or a lifetime beneath finitely many: a meet- or
  join-semilattice;
* **(i)** uses the order only: `≤`, `<`, `⊤`, preorder and partial-order lemmas (`lt_of_lt_of_le`,
  `le_trans`, `not_le.mpr`, …), `↓α` as some strictly shorter lifetime (no least lifetime), a
  decidable test of `<` (a `List.filter`), the construction by well-founded recursion, `δ` carried
  as `ℕ`.

| class | places | `Paper/` | `Support/` | `Core/` | rests on it |
|---|---|---|---|---|---|
| (iii) compares two lifetimes | 12 | 5 | 6 | 1 | 2499 |
| (iv) discreteness | 12 | 3 | 9 | 0 | 229 |
| (ii) a meet-semilattice: `⊓`, a common lower bound | 98 | 23 | 48 | 27 | |
| (ii) a join-semilattice: `⊔` | 7 | 6 | 1 | 0 | |
| (i) the order only | 374 | 103 | 125 | 146 | |
| all | 503 | 140 | 189 | 174 | |

(Places are distinct file and line, 535 declarations with generated ones merged into their source.
"Rests on it": declarations of `Paper/`, `Support/`, `Core/` that use one, directly or through
others, out of 12188 (`scripts/Deps.lean`); `fundamentalC` and `adequacyC` rest on both classes.)

**Class (iii), place by place.** "Statement" means the declaration's statement, read at its cells,
is the order fact named, which `OrderFacts.lean` proves equivalent to comparability in a lattice;
"proof" means the statement holds without it.

| place | uses | in | what it states about the order | rests on it |
|---|---|---|---|---|
| `Paper/S5_Model/Definitions.lean:370` `LSet.union` | `Nat.le_total` | definition | the union of two borrower sets has a greatest and a least member (Core's encoding of `℘⁺(Life)`) | 2504 |
| `Paper/S5_Model/Definitions.lean:603` `CellU.InStratum.sup` | `sup_lt_iff.mpr` | statement | `a < c ∧ b < c → a ⊔ b < c` (`sup_lt_iff_chain`): a union's witness at `⊔ᾱ` | 1143 |
| `Paper/S5_Model/Definitions.lean:640` `ResU.InStratum.sup` | `CellU.InStratum.sup` | statement | the same, at a resource | 1142 |
| `Support/Model/AlgebraInstances.lean:52` `CellU.CompS.inStratum` | `Nat.max_lt` | statement | `γ < a ∧ γ < b → γ < a ⊓ b` (`lt_inf_iff_chain`): a composite `imm` cell at `⊓ᾱ` | 336 |
| `Support/Model/Outlives.lean:62` `cellCompS_inStratum` | `Nat.max_lt.mpr` | statement | the same (`Cell_α` closed under `●`) | 310 |
| `Support/Model/Outlives.lean:73` `cellCompR_inStratum` | `Nat.max_lt.mpr` | statement | the same, and `○`'s `mut(α ⊓ β, …)` (`Cell_α` closed under `○`) | 308 |
| `Paper/S6_2_NonStandardLemmas/Lemmas.lean:1868` `ResU.atLife_comp_sqsupset` (`[TR]` 6.45) | `lt_inf_iff.mpr` | statement | the same, at `@ρ` | 1 |
| `Core/Wp.lean:200` `frameLife_reb_like` | `le_of_not_gt` | statement | `¬ α ⊏ β → β ⊑ α` (`le_of_not_lt_iff_chain`): a reborrow at `β` with `StratumLe W β` (`∀ β′ ⊏ β, W ∈ Res_β′`) gives views no longer than a frame at `α` | 175 |
| `Support/Model/Algebra.lean:59` `CellU.compS_assoc` | `le_total` | proof | re-proved by `InStratum.mono` along `sup_le_sup_left` (`compS_assoc'`) | 966 |
| `Support/Model/Algebra.lean:197` `SPropS.conj_assoc` | `le_total` | proof | re-proved by `InStratum.mono` along `inf_le_left` (`conj_assoc'`) | 908 |
| `Paper/S6_5_NonStandardEntailments/Lemmas.lean:502` `ptoImm_agree` (`[TR]` 6.115) | `sup_lt_iff.mpr` | proof | re-proved with the stratum the given composition carries (`ptoImm_agree'`) | 3 |
| `Support/Model/Algebra.lean:230` `CellU.compR_assoc_forward` | `le_total`, `ResU.InStratum.sup` | proof | the composites' strata are in the compositions it is given, as in `compS_assoc'`; not re-proved | 907 |

`Reproved.lean` states each re-proved lemma with the library's type (`*_same`, by `rfl`), and the
census run on it puts every declaration in class (ii). The statement-level places would be restated
on partial strata: an `imm` cell `imm(ᾱ, v, ρ)` in `Cell_α` when `α ⊏ a` for every `a ∈ ᾱ`, its
witness in `Res_a` for every `a ∈ ᾱ` (on a chain the same sets as Core's `⊓ᾱ ⊐ α`, `ρ ∈ Res_⊔ᾱ`);
`ᾱ` a set of borrowers that need not have a greatest or least member, in place of `LSet`;
`StratumLe W β` read as "every cell of `W` is `⊒ β`". `○`'s `mut(α ⊓ β, …)` would need the same pointwise reading for the `mut` cells
agreement builds. None of these restatements is carried out.

**Class (iv)** is `DenseCarrier`'s class (c): the non-strict stratum "every cell `⊒ α`" written
`ρ ∈ Res_{↓α}`, read back by "no lifetime strictly between `↓a` and `a`". On a partial order it can
hold at some lifetimes and fail at others: on each branch of `TwoBranches` a `↓α` exists
(`down_on_branch`), at the meet of the two branches' first lifetimes none does (`no_down_at_meet`).

**Class (ii)**: `exists_fresh` (`Core/Wp.lean:168`, a lifetime beneath every record, built as
`(Σ ofDual) + 1`), `exists_shorter` (`↓(gi ⊓ gb)`), the borrow rules' fresh bound (`a₂ ⊓ m`) and
the frame rules' (`b₀ ⊓ ↓(γ ⊓ β)`), `○`'s `mut(α ⊓ β)`, `@ρ` as a meet (`ResU.atOn`), `SPropS.conj`
at `a ⊓ b` on the meet side; `⊔ᾱ`, `Life.join`, `[TR]` 6.99 on the join side. `TwoBranches` is a
lattice with a lifetime beneath any finitely many (`exists_lt_all`); the three-point `Vee` has no
lifetime beneath its two branches (`vee_no_lower_bound`).

**The statics.** `LifeCtx.Models`, `EntailsLt`, `EntailsLe` (`Paper/S2_Statics/Definitions.lean:290`,
`362`, `421`) quantify over `ℕ`-valued substitutions: entailment on a chain. 625 and 623
declarations rest on `EntailsLt` and `EntailsLe`. The statics' own proofs over `ℕ` use only `≤` from
`<` (`entailsLe_of_entailsLt`), `⊤` (`entails_x_top`) and a lifetime one below its bound
(`canonList_models`); the other `ℕ` findings in declarations that mention the statics are context
and family indices and termination measures. The checker (`Frontend/Check/Decide.lean:333`, outside
the census's scope) decides entailment by `ordB`, whose rules `@a ⊏ @b₁ ⊓ @b₂` from both and
`@a₁ ⊔ @a₂ ⊏ @b` from both hold only on chains (`Statics.lean`). Whether any corpus program needs
them is not checked.

The full lists of places are at the end.

## 2. The layer equation over a partial order (`Cell.lean`)

`CellFP` is `Paper/S5_Model`'s `CellF` with `Life` replaced by a partial order `L`, field for field,
`ᾱ` in Core's encoding (`LSetP`: a greatest and a least member). `CellFL` is the row as printed
over a lattice: `ᾱ` a nonempty finite set, `⊓ᾱ`, `⊔ᾱ` its infimum and supremum.

* `carrierP_iff`, `carrierL_iff`: **a solution exists exactly when `L` is reverse-well-founded**
  (`WellFoundedGT`), over every partial order and every lattice. Existence is the paper's recursion
  down `⊐` (`CellGP`, `CellGL`); non-existence is `Cantor.lean`'s argument: along `a₀ < a₁ < ⋯` a
  `mut` cell at `aₙ` stores any predicate on the cells at `aₙ₊₁` (`predInjP`), so the cardinals
  would descend forever (`no_descent_of_inj`). Neither direction compares lifetimes `⊐` does not.
* `two_branches_carrier`, `two_branches_nonrigid`: `TwoBranches = ℕᵒᵈ × ℕᵒᵈ` carries the model in
  both readings, and the swap of coordinates is an order automorphism other than the identity.
  Task 1's lifetimes are `br₁ n = (n, 0)`, task 2's `br₂ m = (0, m)`, incomparable for `n, m ≥ 1`
  (`br_incomparable`); their meets `(n, m)` lie beneath both.
* `vee_nonrigid`, `vee_no_lower_bound`: `⊤` over two incomparable points carries the model, has the
  swap, and has no lifetime beneath both points.

So `carrier_rigid` is a fact about chains: the layer equation itself needs a well-founded measure
and nothing else. The automorphisms act on the order; their action on a solution's cells
(`DenseCarrier`'s `pact` for the positioned carrier) is not built here.

## 3. The relation over a partial order of lifetimes (`Reading.lean`, `Relation.lean`, `Faithful.lean`, `Symmetry.lean`)

As in `DenseCarrier`, Core's cells, resources, `wpTS`, typed world and records stay as they are, on
Core's slots; the relation reads its lifetimes in a second order `L`, here any partial order with a
top. `DenseCarrier` read the slots through a strictly monotone map; into a partial order a strictly
monotone image of the slots is a chain, so two cells could never be read at incomparable
lifetimes. Here the reading is any map keeping `⊤` (`Reading`); `Reading.Extends` says the slot
order extends it (a slot read strictly below another is strictly below it), so the slots are a
chain extending the order of what they are read at: a schedule.

**Every change from Core's clauses.**

| Core | here | why |
|---|---|---|
| `δ : LSub` (values `ℕ`), `Life.interp` | `δ : LSubD L`, `interpP` | the relation's lifetimes are `L`'s |
| `@a ⊔ @b`, `@a ⊓ @b`: `min`, `max` on `ℕ` | least upper, greatest lower bound where it exists (`lubOpt`, `glbOpt`); undefined otherwise | `L` need not have them; in a lattice they are `⊔`, `⊓` (`lubOpt_eq`, `glbOpt_eq`) |
| `cC` at `∀`: `∀ α : Life` | `∀ α : L` | the quantifier ranges over `L` |
| `ptoMutS`: `α ⊑ b` | `ptoMutP`: `α ⊑ ι b` | `α` is in `L`, `b` a slot |
| `box`/`Outlives`: `α ⊏ @ψ` | `boxP`/`OutlivesP`: `α ⊏ ι(@ψ)` | as above |
| `LifeCtx.Models`, `EntailsLt`, `EntailsLe` | `ModelsP`, `EntailsLtP`, `EntailsLeP` | over `L` |

No clause asks two lifetimes to be comparable; Core's model compares a cell with a cell or a record
on the slots (`σ ∈ Res_b`, `x.2 ⊐ b`, `Ext`), unchanged.

* `vP_id`, `cP_id`: **at `L = Life` and the identity reading the relation is Core's** `vC true` and
  `cC` at every type of the fragment (through `DenseCarrier.vD_id`, `cD_id`; `vP_eq_vD`,
  `cP_eq_cD` at every type).
* `vP_map`, `cP_map`: **the relation is invariant under every order automorphism `π` of `L`**,
  moving the reading `δ ↦ δ.map π` and the slots' reading `ι ↦ ι.map π`. `interpP_map` carries
  least upper and greatest lower bounds (`lubOpt_map`, `glbOpt_map`, from `OrderIso.isLUB_image`);
  the `∀` clause re-indexes its quantifier by `π`, which needs `π` onto. `semP_map`: the semantic
  judgment is invariant.

## 4. Two interleaved suspended borrows (`Interleave.lean`)

The order is `TwoBranches`; the reading `ι₂` reads Core's slot `s` at `Nat.unpair s`. It is a
bijection from the slots onto `TwoBranches` (`ι₂_slotOf`, `slotOf_ι₂`), and the slot order extends it
(`ι₂_extends`, from the pairing's monotonicity).

* The lifetime context `'x ⊏ 'a, 'y ⊏ 'b, 'a ⊏ ⊤, 'b ⊏ ⊤` read at `'a ↦ br₁ 1`, `'b ↦ br₂ 1`,
  `'x ↦ br₁ 2`, `'y ↦ br₂ 2` (`modelsP_Δ₂`): each borrow beneath its own task's lifetime, neither
  beneath the other nor beneath the other task's (`δ₂_shape`).
* The resource: `ℓ₁ ↦ mut(s₁, (), ∅, 𝒱⟦1⟧)` and `ℓ₂ ↦ mut(s₂, (), ∅, 𝒱⟦1⟧)`, at the slots read at
  `br₁ 2` and `br₂ 2` (`ι₂_s₁`, `ι₂_s₂`). On Core's chain `s₁ < s₂` (`s₁_lt_s₂`): the schedule
  orders what the reading does not.
* `interleaved_world`: **a typed world** (`TW`, built by `TW.alloc` twice and `TW.mutFold` twice)
  **and a valid resource** (`ResU.Valid`).
* `interleaved_related`, `suspended_related`: **related** at `Mut 'x 1 ⊗ Mut 'y 1`, `return (ℓ₁, ℓ₂)`
  at `F (Mut 'x 1 ⊗ Mut 'y 1)`, and the two tasks suspended, each a thunk `λ_. return ℓᵢ` holding its
  borrow, at `U (F (Mut 'x 1)) ⊗ U (F (Mut 'y 1))`.
* `interleaved_swap`: **the swap of the two branches preserves the relation** at the configuration,
  keeps `δ₂ ∈ ⟦Δ₂⟧` and keeps the slot order extending the reading; after it the cell at `s₁` is
  read on task 2's branch (`swapped_reading`). `interleaved` assembles all of it.

**A fresh lifetime beneath the resumer's** (`fresh_on_branch`). Given finitely many slots, the
cells and records in play, and a lifetime `br₁ n` of task 1, there is a slot below every one of the
given slots, as Core's proofs pick (`exists_fresh`, `↓`), read on task 1's branch beneath `br₁ n`
and incomparable with every lifetime of task 2 below `⊤`. The schedule puts the new slot below
everything; the reading puts it beneath the resumer's branch only.

## 5. What carrying Core's proofs over reads (`Forall.lean`, `Interleave.lean`, `Statics.lean`)

`DenseCarrier` carried `∀I`, `∀E` and `withbor` over a chain `L` with a monotone reading
(`allI_compatD`, `allE_compatD`, `withbor2_compatD`). Over a partial order with a reading the slot
order extends:

* **`∀I` and `∀E` hold** (`Forall.lean`): `DenseCarrier`'s proofs, Core's step for step, compare no
  two lifetimes; `allI_compatP` as stated there, `allE_compatP` with its premise read on `L`
  (`EntailsLtP`), since Core's premise over `ℕ` does not carry to a partial order (the last item).
* **reading → strata holds** (`inStratum_of_outlivesP`): cells read strictly above `β` lie in
  `Res_A` for every slot `A` read at or below `β`. This is the direction `withbor2_compatD` uses at
  6.60 and at the callback's `['x]` (`outlivesD_slot`, `.mp`).
* **strata → reading fails** (`ι₂_not_monotone`): a slot below another is not read below it.
  `ptoMutD_slot` uses this direction for the borrow handed to the callback, at a cell `⊒` the fresh
  slot; at the fresh slot itself it is not needed.
* **6.65's freshness is not read beneath one branch** (`no_fresh_bound`): 6.65's premise
  `И α. …` must hold at every slot below some bound, and the borrow rule establishes it by
  instantiating the callback `∀'x ⊏ ⊓Δ` at each such slot's reading, which needs the reading beneath
  `⊓Δ`; below every slot bound some slots are read on task 2's branch. `DenseCarrier.fresh_bound`
  supplied such a bound for a monotone reading. A 6.65 whose `И` ranges over the slots read on the
  borrower's branch has what it needs below any finitely many slots (`fresh_on_branch`); it is not
  stated or proved here.
* **The premises are read on `L`**: `∀E`'s `Δ ⊨ @a ⊏ @b` is Core's, over `ℕ`; carried to a chain `L`
  by `DenseCarrier.entailsLtD_of_entailsLt`, it does not carry to a partial order
  (`checker_meet_not_partial`, `checker_join_not_partial`).

With the strata themselves a partial order (§2) and no second order, `И` ranges over the lifetimes
below its bound, all beneath `⊓Δ` when the bound is, and there is no reading to cross; there the
census's statement-level class (iii) places are what would be restated, class (iv) too
(`no_down_at_meet`), and Core's fresh lifetime beneath every record (`exists_fresh`) is a common
lower bound beneath both tasks' frames, not beneath the resumer's branch only.

## What it means for problem B

Problem B (`research/effects/src/tier2-problems.md`) decided the closed package: a suspended
self-borrow is ended while its value is stored and re-made at a fresh lifetime on each opening, with
lifetimes kept as the model's well-founded measure. The reason given is that stratification is
ordered by ancestry: a `mut` cell's witness must strictly outlive it.

* **The decision does not depend on comparability.** The layer equation's `mut` layer is the same
  over every partial order (`MutFP`: the witness lies in strata strictly above the cell's
  lifetime), so a live self-borrow at a hidden `'x` still cannot sit under a `mut` cell at `'q`
  unless `'x ⊐ 'q`. A partial order adds no room there.
* **The closed package needs no incomparable lifetimes.** By the decision's own terms every
  suspended self-borrow is ended at the stop, so no task holds a borrow while another runs, and the
  interleaved-tasks test program meets only nested borrows, which Core's chain orders.
* **Live interleaved borrows are not excluded by the lifetime order.** Two borrows held across
  interleaved suspensions, at incomparable lifetimes, are a valid typed world related at their
  types, symmetric under the swap of the tasks (`interleaved`), with Core's cells on their chain
  used as a schedule. Carrying the fundamental property to them would need, at least: the statics'
  entailment read on the partial order and the checker's two strict rules dropped; 6.65 with its
  fresh lifetime ranging over the borrower's branch (`no_fresh_bound`); and, if the strata
  themselves were made partial, the eight statement-level places restated. None of this is derived.

## What is open

* **The fundamental property over a partial-order reading.** Not derived. `∀I` and `∀E` are proved
  (`∀E` with its premise read on `L`); the borrow rules need 6.65 restated with its fresh lifetime
  over the borrower's branch (§5), and the other rules `DenseCarrier`'s §8 lists are not re-done.
* **Strata ordered partially.** Core's model with its strata in a partial order (cells at
  incomparable strata, no second order): the restatements of §1's eight places, and the typed world
  over them. Not attempted.
* **The checker on a partial order.** Whether any corpus or kernel program needs the two strict
  rules: not checked.
* **`CellU.compR_assoc_forward` without comparison**: the same argument as `compS_assoc'`; not
  re-proved.
* **The automorphisms' action on a solution's cells** over a partial order (`DenseCarrier`'s `pact`
  with the strata moving): not built.

## Files

| file | content |
|---|---|
| `PartialLife/Cell.lean` | the layer equation over a partial order and a lattice: `carrierP_iff`, `carrierL_iff`; `TwoBranches`, `two_branches_nonrigid`; `Vee`, `vee_no_lower_bound` |
| `PartialLife/Reading.lean` | `Reading`, `Reading.Extends`; `lubOpt`, `glbOpt` and their maps; `interpP`, `atLifeP`, `LtLifeP`, `ModelsP`, `EntailsLtP`, `EntailsLeP` |
| `PartialLife/Relation.lean` | `InStratumP`, `OutlivesP`, `boxP`, `ptoMutP`, `vP`, `cP`, `SemP` |
| `PartialLife/Faithful.lean` | `vP_id`, `cP_id`: Core's relation at `Life` |
| `PartialLife/Symmetry.lean` | `vP_map`, `cP_map`, `semP_map` |
| `PartialLife/Interleave.lean` | `ι₂`, `interleaved`, `fresh_on_branch`; `inStratum_of_outlivesP`, `ι₂_not_monotone`, `no_fresh_bound` |
| `PartialLife/Statics.lean` | `checker_meet_not_partial`, `checker_join_not_partial` |
| `PartialLife/OrderFacts.lean` | `sup_lt_iff_chain`, `lt_inf_iff_chain`, `le_of_not_lt_iff_chain`; `exists_lt_all`; `down_on_branch`, `no_down_at_meet` |
| `PartialLife/Reproved.lean` | `conj_assoc'`, `compS_assoc'`, `ptoImm_agree'` |
| `PartialLife/Forall.lean` | `allI_compatP`, `allE_compatP`; `interpP_applySub`, `vP_congr`, `cP_tyEq`, `CTyEqP.instLife` |
| `scripts/Census.lean`, `scripts/classify.py`, `scripts/Deps.lean` | the census |

Reproduce the census: `lake env lean experiments/PartialLife/scripts/Census.lean > census.txt`, then
`python3 experiments/PartialLife/scripts/classify.py census.txt`;
`lake env lean experiments/PartialLife/scripts/Deps.lean` for what rests on classes (iii) and (iv).

## Census places

**(iii) compares two lifetimes: 12**

- `Core/Wp.lean`: 200 `frameLife_reb_like`
- `Paper/S5_Model/Definitions.lean`: 370 `LSet.union`, 603 `CellU.InStratum.sup`, 640 `ResU.InStratum.sup`
- `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: 1868 `ResU.atLife_comp_sqsupset`
- `Paper/S6_5_NonStandardEntailments/Lemmas.lean`: 502 `ptoImm_agree`
- `Support/Model/Algebra.lean`: 59 `CellU.compS_assoc`, 197 `SPropS.conj_assoc`, 230 `CellU.compR_assoc_forward`
- `Support/Model/AlgebraInstances.lean`: 52 `CellU.CompS.inStratum`
- `Support/Model/Outlives.lean`: 62 `cellCompS_inStratum`, 73 `cellCompR_inStratum`

**(iv) discreteness: 12**

- `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: 620 `ResU.six27`, 2490 `ResU.six52_H1`, 2608 `ResU.six52_sub_inStratum`
- `Support/Model/Outlives.lean`: 417 `Life.not_lt_of_down_lt`, 428 `CellU.not_at_lt_of_inStratum_down`, 458 `Life.le_of_down_lt`, 469 `CellU.wit_inStratum_of_down`, 521 `ExW.inStratum_at`, 548 `AgW.inStratum_at`, 578 `ResU.flat_inStratum_at`, 606 `ResU.updV_outlives_at`, 625 `ResU.Sub.inStratum`

**(ii) a meet-semilattice: `⊓`, a common lower bound: 98**

- `Core/Compatibility.lean`: 244 `withload_compatX`, 934 `withbor1_compatX`, 1024 `withbor2_compatX`, 1106 `withbor3_compatX`
- `Core/EffBorrow.lean`: 270 `withbor2U_compatX`, 353 `withbor3U_compatX`, 444 `withbor1U_compatX`, 545 `withloadU_compatX`, 642 `sliceBorrowMU_compatX`, 724 `sliceBorrowIU_compatX`
- `Core/EffWp.lean`: 67 `wpG_I_frameX`, 356 `wpG_M_frameX`
- `Core/FrameRules.lean`: 50 `wpTS_I_frameX`, 339 `wpTS_M_frameX`
- `Core/Images.lean`: 83 `lift_view`, 109 `CellU.CompR.back_view`, 954 `compatR_imm_congr'`
- `Core/Invariant.lean`: 383 `compR_mut_src`, 1210 `CellU.CompR.lift_full`
- `Core/Reborrow.lean`: 222 `wpG_reborrow`
- `Core/Sized.lean`: 100 `withload_sized`
- `Core/SliceFrames.lean`: 160 `wpG_M_frameList`, 316 `wpG_I_frameList`
- `Core/Slices.lean`: 59 `sliceBorrowM_compatX`, 175 `sliceBorrowI_compatX`
- `Core/Wp.lean`: 96 `CellIn.of_left`, 168 `exists_fresh`
- `Paper/LiteralReadings/S4_LogicalRelation.lean`: 44 `MutImmCell.lset_meet`, 49 `MutImmCell.inRel_same`
- `Paper/S5_Model/Definitions.lean`: 286 `Life.meet`, 329 `ResU.atOn`, 334 `ResU.atOn_ub`, 345 `ResU.atOn_lub`, 647 `ResU.InStratum.inf_left`, 820 `SPropS.conj`, 826 `SPropS.conj_holds`, 1513 `CellU.CompR` (`casesOn`, `rec`, `recOn`), 1520 `CellU.CompR.mutMut`
- `Paper/S6_1_StandardLemmas/Lemmas.lean`: 1546 `CellU.compatR_iff`
- `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`: 46 `fresh_frame`, 254 `wp_M_frame`
- `Paper/S6_5_NonStandardEntailments/Lemmas.lean`: 327 `fresh_mono`, 355 `fresh_L`, 403 `fresh_sep`, 520 `TR.lemma_6_115`, 521 `TR.«I-ag»`, 527 `ptoImm_agree_eq`
- `Paper/S6_8_FundamentalProperty/Lemmas.lean`: 1246 `withbor1_compat`, 1360 `withbor2_compat`, 1475 `withbor3_compat`
- `Support/LogicalRelation/Compatibility.lean`: 415 `tyLifeMeet`, 448 `TyLife.combine`
- `Support/Model/Algebra.lean`: 108 `CellU.compR_own_left`, 117 `CellU.compR_own_right`, 186 `Life.meet_assoc`
- `Support/Model/AlgebraInstances.lean`: 44 `CellU.CompS.at`
- `Support/Model/Ancestors.lean`: 57 `CellU.CompR.imm_source`, 133 `CellU.CompR.nonimm_source`, 199 `CellU.CompR.imm_left_eq`
- `Support/Model/ClosingSentence.lean`: 283 `CellU.compR_immBeta_imm`
- `Support/Model/Compatibility.lean`: 45 `CellU.CompR.imm_left`, 64 `CellU.CompR.wit_of_ne_own`
- `Support/Model/Composition.lean`: 56 `CellU.compR_same_mutMut`, 68 `CellU.CompR.inv`, 102 `CellU.compR_mutMut_of_eq`, 117 `CellU.compR_mutMut_det`, 141 `CellU.CompR.functional`, 240 `CellU.CompR.erase`, 256 `CellU.CompR.wit`, 295 `SPropS.conj_comm`, 301 `CellU.CompR.comm`
- `Support/Model/Lifetimes.lean`: 19 `Life.meet_comm`, 21 `Life.meet_self`
- `Support/Model/Outlives.lean`: 89 `cellCompR_at_le_imm`, 269 `CellU.CompR.lsOf_inv`
- `Support/Model/Reborrow.lean`: 51 `CellU.CompR.erase_left`, 57 `CellU.CompR.erase_right`, 63 `CellU.CompR.nonown_left`, 79 `CellU.CompR.nonown_right`
- `Support/Model/ReborrowRule.lean`: 35 `exists_shorter`
- `Support/Model/RelaxedWalks.lean`: 21 `CellU.compR_ne_imm`
- `Support/Model/Surgery.lean`: 42 `CellU.CompR.ls_imm`, 156 `CellU.CompR.imm_union`
- `Support/Model/Update.lean`: 124 `CellU.CompR.imm_nonimm_left`
- `Support/TypedWorld/Compatibility.lean`: 313 `withload_compatX`, 1002 `withbor1_compatX`, 1092 `withbor2_compatX`, 1171 `withbor3_compatX`
- `Support/TypedWorld/FrameRules.lean`: 50 `wpTS_I_frameX`, 339 `wpTS_M_frameX`
- `Support/TypedWorld/Images.lean`: 82 `lift_view`, 108 `CellU.CompR.back_view`, 961 `compatR_imm_congr'`
- `Support/TypedWorld/Invariant.lean`: 383 `compR_mut_src`, 1218 `CellU.CompR.lift_full`
- `Support/TypedWorld/Reborrow.lean`: 221 `wpTS_reborrow`
- `Support/TypedWorld/Wp.lean`: 96 `CellIn.of_left`, 168 `exists_fresh`

**(ii) a join-semilattice: `⊔`: 7**

- `Paper/LiteralReadings/S6_5_NonStandardEntailments.lean`: 44 `not_iAgreeAtJoin`
- `Paper/S5_Model/Definitions.lean`: 283 `Life.join`, 1468 `CellU.compS`
- `Paper/S6_5_NonStandardEntailments/Lemmas.lean`: 105 `box_4`, 112 `TR.lemma_6_99`, 113 `TR.«[]4»`
- `Support/Model/Entailments.lean`: 99 `IAgreeAtJoin`

**(i) the order only: 374 places**, listed by `classify.py`'s output.
