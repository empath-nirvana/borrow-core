# DenseCarrier: Core's relation over a dense lifetime order

Build with `lake build DenseCarrier`. There is no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`, and every result's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]`. The library does not import this directory.

## The question

Tier 2 needs Law 2: a lend ended at a stop is re-lent at a fresh lifetime beneath the resumer's
list, and the suspended region's frames are related at that lifetime. On `Life = ℕᵒᵈ` three
machine-checked facts block it:

* `ProbeD1/GapWitness.lean`: Core's `∀` clause holds at a cell adjacent to its bound and fails at a
  cell of the same order type with room below it (`coreAllAdjacent`, `coreAllNotNatural`,
  `not_coreAllImpCutAll`);
* `ProbeD1/SegShift.lean`: shifting the lifetimes below a cut breaks the relation at every cut
  (`segShiftFailsAtEveryCut`);
* `ProbeD1/BridgeProbe.lean`: re-instantiating a region's lifetimes breaks it (`not_coreThawTop`).

The hypothesis: over a dense order such as `(ℚ, <)` there is always room between lifetimes, and
the order is homogeneous, so a relation invariant under its automorphisms is invariant under the
moves Law 2 makes. The known cost: `Paper/S5_Model` builds the cells by well-founded recursion down
`⊏` on `ℕ`, which a dense order does not support. The proposed replacement: recurse over the
lifetimes in play.

## The outcome

1. **The stratification index cannot be dense** (`Cantor.lean`, proved). The paper's layer
   equation `Cell_α ≅ own + imm(Imm_α) + mut(Mut_α)`, written over any linear order, has a solution
   exactly when the order has no infinite ascending chain (`carrier_iff`). A `mut` cell of stratum
   `α` stores an arbitrary predicate on the cells of a stratum above it, so along an ascending chain
   the cardinals of the strata would descend forever. No dense order with two points carries the
   paper's model (`no_carrier_of_dense`, `no_carrier_withTopRat`).
2. **What can be dense is the order the relation reads.** The cells keep a reverse-well-ordered
   index, the *slots* (the lifetimes in play; Core's own `Life = ℕᵒᵈ`, so Core's model is reused
   unchanged). The relation reads its lifetimes in a second order `L`, the reading `δ` and the `∀`
   range over `L`, and a cell is compared with an `L`-lifetime through an order embedding `ι` of the
   slots into `L`. At `L = Life` and `ι = id` the fragment built here is Core's relation
   (`vD_id`, `cD_id`).
3. **Gap test, at a dense `L`: passed** (proved). The adjacency witness cannot be built
   (`not_denseCoreAllAdjacent`): the clause fails at every cell below its bound, and so does not
   tell configurations of one order type apart (`dense_same_order_type`). The relation is invariant
   under every order automorphism of `L` (`cD_map`, `vD_map`, `semD_map`). The same generic
   theorems at `L = Life` reproduce `CoreAllAdjacent` (`coreAllAdjacentD`, and through `cD_id`
   ProbeD1's own statement, `coreAllAdjacent_via_cD`).
4. **Shift test, at `L = WithTop ℚ`: passed** (proved). Every segment shift, at every cut, by every
   `k > 0`, preserves and reflects the relation at every configuration and every type of the
   fragment (`segShift_iff`, `segShiftInvD`). The same fragment at `L = Life` fails at every cut
   (`segShiftFailsAtEveryCutD`).
5. **FL map**: the `∀` rules are re-proved over every `L` at Core's own premises (`allI_compatD`,
   `allE_compatD`). Every other rule transfers by porting the relation layer to `δ : LSubD L` and
   `ι`; none needs new mathematics; one hypothesis is needed, a slot below every lifetime of `L`
   (§5).

**Kill criterion: not met.** The paper's carrier does need recursion down a reverse-well-founded
order (`carrier_iff`), so it cannot recurse down a dense `⊏`. But the recursion need not run on the
order the relation reads: recursion over the lifetimes in play (the slots) replaces recursion over
`Life`, and the shift does not fail over the dense carrier.

**What this does not settle: Law 2 itself.** See *What is open*.

## 1. Census

`scripts/Census.lean` walks the elaborated value and type of every declaration of `Paper/`,
`Support/` and `Core/` and reports every application where a `Life` fills an `ℕ` slot or an `ℕ`
fills a `Life` slot (the two are definitionally equal, so this is exactly where a fact about `ℕ`
is used at `Life`), and every use of `OrderDual.ofDual`/`toDual` at `ℕ`, `Life.down`,
`WellFounded.fix` and `Nat.lt_wfRel`. A grep found no instance-level use (`WellFoundedGT`,
`SuccOrder`, `Nat.find`, strong induction) at `Life`. `scripts/classify.py` sorts the findings;
`scripts/Deps.lean` computes what rests on them. This agrees with `Restrat/Audit.lean`: no
definition computes a lifetime, and `↓` occurs as an existential witness or in a hypothesis
`ρ ∈ Res_{↓α}`.

Classes: **(a)** carrier-independent once `Life` is any dense unbounded linear order with `⊤`;
**(b)** needs recursion over the lifetimes in play; **(c)** genuinely needs discreteness.

| class | places | `Paper/` | `Core/` | `Support/` | layer |
|---|---|---|---|---|---|
| (a) | 305 | 58 | 142 | 105 | 282 relation (they read `δ`), 23 model |
| (b) | 2 | 2 | 0 | 0 | model |
| (c) | 12 | 3 | 0 | 9 | model |
| total | 319 | 63 | 142 | 114 | |

(Places are distinct file and line; 323 declarations.)

* **(a)** splits by what the `ℕ` is used for: `δ` and `@aδ` carried as `ℕ` (263; `LSub` stores
  `ℕ`, `Life.interp` returns `Option ℕ`, and the relation uses the value as a `Life`); `↓` as some
  strictly shorter lifetime (23; `NoMinOrder`); `ofDual`/`toDual` (5; the definition of `↓` and
  `exists_fresh`, a lifetime below finitely many records); an `ℕ` order lemma at `Life` (14;
  `Nat.le_trans`, `min`/`max` lemmas, which hold in every linear order).
* **(b)** is the construction itself, `Cell` and `Cell_eq`. 2901 of the library's 10132
  declarations rest on it (`scripts/Deps.lean`). It cannot be ported to a dense `Life`
  (`no_carrier_of_dense`).
* **(c)** is one cluster: the non-strict stratum "every cell `⊒ α`" written as the strict
  `ρ ∈ Res_{↓α}`, read back by the two facts `Life.le_of_down_lt` and `Life.not_lt_of_down_lt`
  (no lifetime strictly between `↓a` and `a`), and their users, among them the transcriptions of
  `[TR]` 6.27 and 6.52. 214 declarations rest on them, `fundamentalC` and `adequacyC` among them
  (through 6.65's frame rule and 6.150's reborrow rule, which use 6.27 and 6.52). Over a dense
  `Life` each would have to be restated with the non-strict stratum `StratumLe`
  (`Core/World.lean`) in place of `Res_{↓α}`; not attempted.

**The cost of the real switch.** Making `Life` itself dense is impossible: (b) has no dense
version. The switch that is possible keeps (b), (c) and the 23 model-level (a) places on the slots
untouched, and ports the 282 relation-level (a) places, with everything that rests on them, to
`δ : LSubD L` and `ι`. That port is mechanical (§5).


## 2. The carrier

**The index of the strata** (`Cantor.lean`). `CellFG` is `Paper/S5_Model`'s `CellF` with `Life`
replaced by a linear order `L`, field for field, and `IsCarrier Cell` says a family of types solves
it.

* `carrier_of_wellFoundedGT`: over a reverse-well-founded `L` the paper's recursion builds a
  solution (`CellG`, `CellG_eq`). Finite orders and `ℕᵒᵈ` are reverse-well-founded, so recursion
  over finitely many lifetimes in play works.
* `predInj`: a `mut` cell of stratum `α` stores any predicate on the cells of a stratum `β ⊐ α`,
  injectively. `no_carrier_of_strictMono`: with an infinite ascending chain `a₀ < a₁ < ⋯`,
  `#Cell_{aₙ} ≥ 2^#Cell_{aₙ₊₁} > #Cell_{aₙ₊₁}`, a descending sequence of cardinals.
* `carrier_iff`: a solution exists exactly when `L` is reverse-well-founded.
* `exists_strictMono_of_dense`, `no_carrier_of_dense`, `no_carrier_withTopRat`,
  `no_carrier_withTopRat_BoCa`: a dense order with two points has such a chain, so no solution, at
  `WithTop ℚ` and at `[TR]` §3's `Loc` and `Val`.

Keeping a dense order as the index would need the stored predicates restricted (finitely
supported, or syntactic); not attempted, since the index need not be dense.

**The construction** (`Carrier.lean`, `Relation.lean`). The carrier the relation reads is any
linear order `L` with a top; the dense instance is `WithTop ℚ` (`Rat.lean`), with Core's slot `n`
at `-n` and slot `0` at `⊤` (`ratSlots`, below every lifetime a slot: `ratSlots_unbounded`).

* `Slots L`: a strictly monotone map from Core's `Life` (the slots) into `L`, `⊤` to `⊤`.
* `LSubD L`, `interpD` (`⊤`, `⊔`, `⊓` of `L`), `atLifeD`, `LtLifeD`, `ModelsD`, `EntailsLtD`.
* `InStratumD`, `OutlivesD`, `boxD`, `ptoMutD`; the relation `vD` at `1`, `[@a]`, `Mut`, and `cD` at
  `F`, `⊸`, `⊤`, `∀`; `gSepD`, `gDenD`, `SemD`. `FragV`/`FragC` name the fragment.

Everything else is Core's own definition, imported, not copied: cells, resources, `●`, `○`, the
walks, `↭`, `wpTS` with its typed world `TW` and tagged record lists, `⋆`, `─⋆`, `⌜−⌝`.

**Every change from Core's clauses, and why.**

| Core | here | why |
|---|---|---|
| `δ : LSub` (values `ℕ`), `Life.interp` | `δ : LSubD L`, `interpD` | the reading's lifetimes are `L`'s |
| `cC` at `∀`: `∀ α : Life` | `∀ α : L` | the `∀` ranges over the dense order |
| `ptoMutS`: `α ⊑ b` | `ptoMutD`: `α ⊑ ι b` | `α` is an `L`-lifetime, `b` a slot |
| `box`/`Outlives`: `α ⊏ @ψ` | `boxD`/`OutlivesD`: `α ⊏ ι(@ψ)` | as above |
| `LifeCtx.Models`, `EntailsLt` | `ModelsD`, `EntailsLtD` | over `L`; Core's premises carry over (§5) |

The stratified recursion is not replaced; it stays where `carrier_iff` allows it, on the slots.
**Faithfulness**: at `L = Life`, `ι = Slots.id`, `vD_id` and `cD_id` give equality with Core's
`vC true` and `cC` at every fragment type, record list, reading and resource; so ProbeD1's
statements are this fragment's at that instance (`coreAllAdjacent_via_cD`).

## 3. The gap test (`Gap.lean`, `Equivariance.lean`)

The configuration of `GapWitness.lean` at a general bound: `gapC c = ∀'0 ⊏ @c. F (Mut '0 1)`, the
value `Λ. return ℓ₀`, and a `mut` cell at a slot `b` below the bound `m = @cδ`.

* `holdsD`: if no lifetime of `L` lies strictly between `ι b` and `m`, the clause holds at the
  inner view `ℓ₀ ↦ mut(b, (), ∅, 𝒱⟦1⟧)`.
* `failsD`: if some `α` of `L` lies strictly between them, the clause fails at every single `mut`
  cell at `b` with an empty witness (the run's `↭` keeps the cell's slot, and `α ⊑ ι b` is false).
* At `L = Life`: `coreAllAdjacentD` (holds at the cell at `1`, fails at the cell at `2`),
  `coreAllAdjacent_via_cD` (ProbeD1's `CoreAllAdjacent` itself, through `cD_id`).
* At a densely ordered `L`, every `ι`: `dense_fails`, `dense_fails_innerView` (fails at every slot
  below the bound), `dense_same_order_type` (two cells below the bound: related at one iff at the
  other), and the dense analogue of `CoreAllAdjacent` (`DenseCoreAllAdjacent`: holds at one slot
  below `⊤`, fails at another) is false: `not_denseCoreAllAdjacent`,
  `not_denseCoreAllAdjacent_one_two` (at Core's slots `1` and `2`).
* **Equivariance**, at every `L`: an order automorphism `π` moves the reading (`δ.map π`) and the
  slots (`ι.map π`); `vD_map`, `cD_map` (equalities), `semD_map`. The only clause that needs `π`
  onto is `∀`, re-indexed by `α' = π α`. On `ℕᵒᵈ` the only automorphism is the identity.

## 4. The shift test (`Shift.lean`, `Rat.lean`)

The segment shift at the cut `c` by `k > 0` (`shiftQ c k`): every lifetime strictly below `c`
moves down by `k`, the rest stays; it is an order embedding, not onto. On a configuration it
moves what the relation reads in `L`, the slots' positions (`shiftSlots ι c hk`) and the reading;
the resource, records and term are the model's and stay. This is `SegShift.lean`'s move: reading,
records and resource moved together, with the move made on the positions.

* `exists_aut_agree`, `config_bound`, `slots_bound`: on a configuration's lifetimes (every slot
  position and every value of the reading) the shift agrees with an order automorphism of
  `WithTop ℚ`: the translation when `c = ⊤`, else `plIso`, which translates up to the greatest
  relevant lifetime below the cut, stretches the rest of the way up to the cut, and fixes the cut
  and above.
* `segShift_iff`: **the shifted configuration is related exactly when the configuration is**, at
  every cut, `k`, slots, type, records, reading, term and resource. `segShiftInvD` is the dense
  analogue of `SegShift.SegShiftInv`.
* `not_denseCoreAllNotNatural`: the dense analogue of `CoreAllNotNatural` (related before the
  shift at `⊤` by `1`, not after) is false. `cD_imp_cutAllD`: the relation implies the
  position-`∀` (`ProbeD1/Gap.lean`'s reading (A), `CutAllC`), the dense analogue of
  `NotCoreAllImpCutAll` being its negation. `cD_comp_of_agree`: any move agreeing with an
  automorphism on the configuration's lifetimes leaves the relation unchanged, at every `L`.
* At `L = Life`: `segShiftFailsAtEveryCutD`: every shift by `k > 0` (`Restrat.Emb.shift`, on the
  positions), at every cut, breaks the relation at the cell adjacent to the cut.

## 5. The FL map

What each rule of `fundamentalC` (`Core/Fundamental.lean`) reads in the lifetime order, and what
its compatibility proof needs when `δ` and the `∀` move to `L`. Re-proved here: `allI`, `allE`.
The rest is the reading of the existing proofs, not re-proved.

| rules | read in `L` | transfer |
|---|---|---|
| `var`, `unitI`, `tensorI`, `sumI₁₂`, `thunkF`, `thunkV`, `ret`, `bind`, `force`, `lam`, `app`, `withI`, `proj₁₂`, `topI`, `unitE`, `tensorE`, `sumE`, `zeroE`, `bangThunkF/V`, `bangE`, `copyBang`, `forgetBang`, `lolliE`, `ofRet`, `roll`, `unroll`, `nuIn`, `nuOut`, `unfoldN`, `foldOwn`, `foldReuse` | nothing; `δ` is passed through; `U`'s Kripke order `Ext` compares slots | unchanged, `δ` re-typed |
| `alloc`, `free`, `swap`, `lit`, `hostOp`, `arrNew`, `arrFree`, `arrSize`, `arrReplace`, `countFold`, `countTry`, `boundedFix` | nothing | unchanged |
| `effSub`, `effPerform`, `effRaise`, `effLet`, `effThen`, `effHandle` | nothing: operation types are closed in lifetimes | unchanged |
| `allI` | `∀` over `L`, `⟦Δ⟧` | **re-proved**, Core's proof step for step: `allI_compatD` |
| `allE` | `∀` at `@aδ`; `Δ ⊨ @a ⊏ @b` | **re-proved**: `allE_compatD`, through `CTyEqD.instLife` and `cD_tyEq` (Core's `CTyEq.instLife` with `interpD`). Its premise is Core's own `LifeCtx.EntailsLt` over `ℕ`, carried to `L` by `entailsLtD_of_entailsLt`: a reading's values are finitely many, and re-read by rank (`rankIn`) in `ℕᵒᵈ` they keep `⊤`, `⊔`, `⊓` and the strict order |
| `allEV` | `allE` under `U` | transfers as `allE` does, once `U` is built over `L` |
| `immSub`, `mutSub` | `α ⊑ ι b`, antitone in `α`; `Δ ⊨ @a ⊑ @b` | transfers; the premise by `entailsLeD_of_entailsLe` (proved) |
| `boxI`, `boxE` | `[α]` through `ι`; 6.60 (`vC_outlives`) | transfers: 6.60's induction reads the order of `L` and `ι`'s monotonicity |
| `copy`, `forgetImm`, `forgetMut`, `forgetUnk`, `arrLen`, `arrGet`, `arrCopy`, `arrForget`, `sliceGetM`, `sliceLenM`, `sliceSplitI/M`, `sliceEmptyI/M`, `sliceReplaceM`, `sliceSwapM` | the `Imm`/`Mut` clauses through `ι`; `Imm`'s coherence `CohE` compares the type at `δ` with a record's `(T, δ)` | transfers once records carry `LSubD L` (`FrameRec.δ`) and the typed world's 6.64 premises (`vShape`) read `L` through `ι`: a re-indexing of `FrameRecords`, `World` and the shapes |
| `withbor1/2/3`, `withload`, `withswap`, their unwinding forms, `sliceBorrowM/I` (and `U`), `foldImm` | the callback's `∀` at a fresh lifetime | transfers. Core instantiates the callback at the lifetime `α` of `И`'s cell (6.64/6.65), a slot; here at `ι α`, with `И`'s bound taken at a slot whose position is below `@(⊓Δ)δ`. **Needs a slot below every lifetime of `L`** (`ratSlots_unbounded` at `WithTop ℚ`). The frames, their `↓`-strata and the (c) places stay on the slots, untouched; plus the record re-indexing above |
| `adequacyC`, `theorem32` | `δ = ∅` | unchanged |

**New mathematics: none for FL.** The work is the port of the relation layer (the 282
relation-level (a) places and what rests on them), the record and typed-world re-indexing, the
fresh-slot hypothesis, and the two premise transfers (proved).

## What is open

**Law 2 itself.** The shift test moves every lifetime the configuration reads, slot positions
included: after `shiftSlots`, no slot sits in the gap `[c − k, c)`. The resumer's lends are cells,
so at slots, and in the shifted world they cannot sit in that gap. Putting them there means moving
the region's lifetimes past slots that stay. An order embedding of the slots cannot: the region's
slots and the resumer's are one order, and with fresh lifetimes taken below everything in play the
resumer's slots lie below the region's. Law 2 does it by ending the region's lends and re-lending
at fresh slots below the resumer's, with the region's reading moved to them. Re-slotting the region's cells by an order embedding, each stored
predicate moved to its image, is not the way: it is not natural at `Mut 'a (Imm 'b 1)`
(`Restrat.MutCounterexample.mut_not_natural`), where the moved interpretation holds at the gap the
embedding leaves and the moved predicate refuses it. So the re-lend re-creates the region's `mut`
cells with their predicates re-read at the moved reading. Whether the region's relation survives
that is Law 2: not derived, no obstruction verified. What this probe removes is the obstruction ProbeD1 machine-checked against
it: over a dense `L` the relation does not read the room between a cell and a bound
(`dense_same_order_type`), and moves of a whole configuration are invisible to it (`cD_map`,
`segShift_iff`).

**The rest of the relation over `L`.** Built here: `1`, `[@a]`, `Mut`, `F`, `⊸`, `⊤`, `∀`, with
Core's records and typed world. Not built: the other formers' clauses, records over `L`, and the
compatibility lemmas of §5 other than `allI`/`allE`.

## Files

| file | content |
|---|---|
| `DenseCarrier/Cantor.lean` | the layer equation over any linear order; `carrier_iff`, `no_carrier_of_dense` |
| `DenseCarrier/Carrier.lean` | `Slots`, `LSubD`, `interpD`, `atLifeD`, `LtLifeD`, `ModelsD`, `EntailsLtD` |
| `DenseCarrier/Relation.lean` | `ptoMutD`, `OutlivesD`, `boxD`, `vD`, `cD`, `SemD` |
| `DenseCarrier/Faithful.lean` | `vD_id`, `cD_id`: Core at `L = Life` |
| `DenseCarrier/Equivariance.lean` | `vD_map`, `cD_map`, `semD_map` |
| `DenseCarrier/Gap.lean` | `holdsD`, `failsD`, the gap test |
| `DenseCarrier/Rat.lean` | `WithTop ℚ`: `ratSlots`, `shiftQ`, `plIso`, `exists_aut_agree` |
| `DenseCarrier/Shift.lean` | the shift test |
| `DenseCarrier/FL.lean` | `allI_compatD`, `allE_compatD`, the premise transfers |
| `scripts/Census.lean`, `scripts/classify.py`, `scripts/Deps.lean` | the census |

Reproduce the census: `lake env lean experiments/DenseCarrier/scripts/Census.lean > census.txt`,
then `python3 experiments/DenseCarrier/scripts/classify.py census.txt`;
`lake env lean experiments/DenseCarrier/scripts/Deps.lean` for what rests on (b) and (c).

## Census places

**(b) the stratified construction: 2**

- `Paper/S5_Model/Definitions.lean`: 185 `Cell`, 199 `Cell_eq`

**(c) discreteness: 12**

- `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: 620 `ResU.six27`, 2490 `ResU.six52_H1`, 2608 `ResU.six52_sub_inStratum`
- `Support/Model/Outlives.lean`: 417 `Life.not_lt_of_down_lt`, 428 `CellU.not_at_lt_of_inStratum_down`, 458 `Life.le_of_down_lt`, 469 `CellU.wit_inStratum_of_down`, 521 `ExW.inStratum_at`, 548 `AgW.inStratum_at`, 578 `ResU.flat_inStratum_at`, 606 `ResU.updV_outlives_at`, 625 `ResU.Sub.inStratum`

**(a) a strictly shorter lifetime, `↓`: 23**

- `Core/Compatibility.lean`: 1024 `withbor2_compatX`
- `Core/EffBorrow.lean`: 269 `withbor2U_compatX`, 641 `sliceBorrowMU_compatX`, 723 `sliceBorrowIU_compatX`
- `Core/EffWp.lean`: 67 `wpG_I_frameX`, 356 `wpG_M_frameX`
- `Core/FrameRules.lean`: 50 `wpTS_I_frameX`, 339 `wpTS_M_frameX`
- `Core/SliceFrames.lean`: 160 `wpG_M_frameList`, 316 `wpG_I_frameList`
- `Core/Slices.lean`: 59 `sliceBorrowM_compatX`, 175 `sliceBorrowI_compatX`
- `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: 601 `Life.down_sqsubset`, 606 `TR.lemma_6_63`, 2477 `ResU.reb_inStratum_down`
- `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`: 79 `wp_I_frame`, 254 `wp_M_frame`
- `Paper/S6_5_NonStandardEntailments/Lemmas.lean`: 150 `box_ex_R`, 355 `fresh_L`
- `Support/Model/ReborrowRule.lean`: 35 `exists_shorter`
- `Support/Model/Strata.lean`: 18 `ResU.exists_stratum`
- `Support/TypedWorld/FrameRules.lean`: 50 `wpTS_I_frameX`, 339 `wpTS_M_frameX`

**(a) `ofDual`/`toDual` at `ℕ`: 5**

- `Core/Wp.lean`: 80 `mem_rsOf`, 168 `exists_fresh`
- `Paper/S5_Model/Definitions.lean`: 362 `Life.down`
- `Support/TypedWorld/Wp.lean`: 80 `mem_rsOf`, 168 `exists_fresh`

**(a) an `ℕ` order lemma at `Life`: 14**

- `Paper/S5_Model/Definitions.lean`: 370 `LSet.union`, 479 `LSet.singleton`
- `Paper/S6_5_NonStandardEntailments/Lemmas.lean`: 327 `fresh_mono`, 470 `ptoImm_antitone`, 600 `ptoMut_antitone`
- `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`: 72 `reborrow_ptoOwn`, 134 `reborrow_ptoMut`
- `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean`: 747 `wp_load_I_nonvacuous`
- `Support/Model/Algebra.lean`: 186 `Life.meet_assoc`
- `Support/Model/AlgebraInstances.lean`: 52 `CellU.CompS.inStratum`
- `Support/Model/Lifetimes.lean`: 32 `LSet.ext`
- `Support/Model/Outlives.lean`: 62 `cellCompS_inStratum`, 73 `cellCompR_inStratum`, 89 `cellCompR_at_le_imm`

**(a) `δ` and `@aδ` carried as `ℕ`: 263**

- `Core/Arrays.lean`: 83, 209
- `Core/Compat.lean`: 342, 449, 455, 467, 481
- `Core/Compatibility.lean`: 244, 529, 552, 565, 651, 674, 693, 729, 747, 831, 918, 934, 1106, 1193
- `Core/Computation.lean`: 41, 105, 211, 260
- `Core/CountFree.lean`: 114, 153, 210, 223
- `Core/EffBorrow.lean`: 149, 162, 352, 443, 544
- `Core/EffRules.lean`: 827
- `Core/FoldImm.lean`: 233, 342, 347, 354, 485, 505, 511, 521, 549, 621
- `Core/FrameRecords.lean`: 213
- `Core/Images.lean`: 334, 391, 458, 706, 913, 1052, 1142, 1195, 1468, 1563, 1651
- `Core/Invariant.lean`: 52, 795, 856, 994, 1005, 1014, 1321, 1390, 1461, 1802, 1921, 2308, 2339, 2401, 2554, 2701, 2763, 2775
- `Core/Nu.lean`: 354
- `Core/Persistent.lean`: 61
- `Core/Reborrow.lean`: 130, 179
- `Core/ReborrowShapes.lean`: 43, 139, 150
- `Core/RelMu.lean`: 244, 421, 455
- `Core/Relation.lean`: 151
- `Core/RelationFacts.lean`: 47, 136, 222, 237, 242, 262, 329, 366, 476, 573, 684, 772, 952, 1169, 1239, 1451, 1669, 1832, 1852, 1958
- `Core/ShapeMu.lean`: 169, 322, 369, 532, 610, 671
- `Core/Sized.lean`: 100, 196
- `Core/SliceOps.lean`: 114, 125, 130, 294
- `Core/Slices.lean`: 161, 265
- `Core/Stdio.lean`: 235, 239, 572, 576
- `Core/World.lean`: 97, 122, 128
- `Core/Wp.lean`: 329
- `Paper/LiteralReadings/S4_LogicalRelation.lean`: 49
- `Paper/LiteralReadings/S6_8_FundamentalProperty.lean`: 123, 223, 361, 825, 868, 1024
- `Paper/S4_LogicalRelation/Definitions.lean`: 53, 101, 108, 189
- `Paper/S4_LogicalRelation/Remarks.lean`: 32, 45
- `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: 3619
- `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`: 479, 648, 665, 666, 683, 693, 694, 713, 730
- `Paper/S6_8_FundamentalProperty/Lemmas.lean`: 631, 725, 766, 807, 918, 957, 1091, 1139, 1170, 1246, 1360, 1475, 1604, 1706, 1707, 1715, 1725, 1731, 1751
- `Support/LogicalRelation/Compatibility.lean`: 182, 200, 206, 279, 459, 552, 667
- `Support/LogicalRelation/Facts.lean`: 30, 140, 144, 148, 327, 357, 366, 387, 543, 553
- `Support/Model/Subtraction.lean`: 47
- `Support/TypedWorld/Compatibility.lean`: 313, 598, 621, 634, 720, 743, 762, 798, 816, 900, 987, 1002, 1092, 1171, 1258
- `Support/TypedWorld/Images.lean`: 370, 425, 479, 727, 920, 1059, 1139, 1194, 1449, 1544, 1632
- `Support/TypedWorld/Invariant.lean`: 52, 795, 844, 1002, 1013, 1022, 1317, 1375, 1433, 1755, 1874, 2261, 2292, 2354, 2507, 2654, 2716, 2728
- `Support/TypedWorld/Reborrow.lean`: 129, 178
- `Support/TypedWorld/ReborrowShapes.lean`: 32, 120, 131
- `Support/TypedWorld/Records.lean`: 168
- `Support/TypedWorld/Relation.lean`: 67
- `Support/TypedWorld/RelationFacts.lean`: 46, 78, 120, 148, 182, 281, 361, 416, 440, 541, 614, 628, 683, 738, 809, 1000, 1179, 1343, 1363, 1480
- `Support/TypedWorld/World.lean`: 53, 77, 83
- `Support/TypedWorld/Wp.lean`: 328

