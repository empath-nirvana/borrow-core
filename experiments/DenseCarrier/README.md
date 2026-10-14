# DenseCarrier: Core's relation over a dense lifetime order

Build with `lake build DenseCarrier`. There is no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`, and every result's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]`. The library does not import this directory.

On a Core with the tier-1 effect kernel (branch `law2-typed-world`) only `Cantor`, `Carrier`,
`Relation`, `Faithful`, `Equivariance`, `Rat`, `Nominal` and `Positioned` build: `FL` and `Borrow`
read the computation types before `F_Σ` gained its cancel row, and `Gap`, `Reslot` and every file
after them import `ProbeD1`, which imports `Targets`, written against the cancel payload that
carried handler names. The first-order re-lending and `core_relend_derivable` are proved again
there at Core's relation (`experiments/Law2/Law2/Remake.lean`).

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
moves Law 2 makes. The question: **can a suspended region's lifetimes be moved — cells, resource,
records and reading together — so that the resumer's lends sit in a gap beneath them, with the
relation preserved, at every cut?**

## The outcome

**No, on any carrier tried.** The moves the relation does not see (positions, step 4) cannot put a
slot in the gap; the move that frees slots there (re-slotting, step 5) breaks the relation, inside
the fragment, at every cut; and a carrier with cells at every lifetime of a dense order storing
every finitely supported predicate does not exist (step 7). Each failure is a machine-checked
statement. Re-making the region's cells in place of moving them is *Re-lending*.

1. **The stratification index cannot be dense** (`Cantor.lean`). The layer equation
   `Cell_α ≅ own + imm(Imm_α) + mut(Mut_α)` over a linear order has a solution exactly when the
   order has no infinite ascending chain (`carrier_iff`), and every order that carries it is rigid
   (`carrier_rigid`).
2. **The two-order design** (§2): Core's cells, unchanged, on the slots `Life = ℕᵒᵈ`; the relation
   reads its lifetimes in a second order `L` through an order embedding `ι` of the slots. At
   `L = Life`, `ι = id` it is Core's relation (`vD_id`, `cD_id`).
3. **Gap test: passed** (§3). At a dense `L` the `∀` reads no room between a cell and its bound
   (`not_denseCoreAllAdjacent`, `dense_same_order_type`), and the relation is invariant under every
   automorphism of `L` (`cD_map`).
4. **Moving the slots' positions: invariant** (§4). A segment shift of `L` applied to the slots'
   positions and the reading preserves and reflects the relation at every cut (`segShift_iff`).
   It is a corollary of `cD_map` and the homogeneity of `ℚ`, and it moves no cell.
5. **The faithful shift — cells re-slotted, records, reading moved — fails** (§5).
   For every `L`, every placement `ι`, every re-slotting `θ` other than the identity and every
   reading move `ψ` agreeing with `ι ∘ θ ∘ ι⁻¹` on the slots, a borrow of a borrow is related at
   `Mut 'a (Mut 'b 1)` and at `F (Mut 'a (Mut 'b 1))` before the move and not after
   (`not_reslotInvV`, `not_reslotInvC`), at every cut (`reslotFailsAtEveryCut`); probe 1's own
   position shift is such a `ψ` (`shiftQ_ratSlots`). The bridge — re-slotting equals moving `ι` —
   fails at the same type, without `Imm` (`not_bridgeV`). The dense thaw at the top cut fails
   (`not_denseThawTop`). In Core the same configuration refutes
   `SegShift.SegShiftInv` and `Bridge.CoreThawTop` at a type with no `∀`
   (`not_segShiftInv_noAll`, `not_coreThawTop_noAll`).
6. **No slot in the gap** (§6). A placement of the slots keeps their order and the
   slots between any two (`slots_between_iff`, `placement_keeps_order`); the gap probe 1's shift
   opens in `L` holds no slot (`shiftSlots_gap_empty`). The move that does free slots there is the
   re-slotting of step 5, which breaks the relation.
7. **A dense carrier storing every finitely supported predicate does not exist** (§7). The
   full layer equation with cells at every lifetime, acted on by the automorphisms of `L`, every
   finitely supported predicate storable (nominal sets with ordered atoms), has no solution over an
   order with an infinite ascending chain (`no_fsCarrier`), at a dense `L`
   (`no_fsCarrier_of_dense`), even with supports restricted to lifetimes at or above the cell
   (`no_fsCarrier_withTopRat_above`). At `Life` Core's cells are one (`fsCarrier_life`). A carrier
   storing a restricted class of predicates, finite carriers glued along embeddings
   (`carrier_of_wellFoundedGT`), and a carrier whose strata are kept apart from the lifetimes
   (`Positioned.lean`) are not ruled out.
8. **FL map** (§8): `allI`, `allE` and `withbor` (2) re-proved over every `L`; every other rule
   transfers by the port of the relation layer.

**Kill criterion: met**, at each step: the faithful shift by `not_reslotInvC` and
`not_reslotInvV`, the dense thaw by `not_denseThawTop`, a slot in the gap by
`shiftSlots_gap_empty` with `not_reslotInvC`, a dense carrier storing every finitely supported
predicate by `no_fsCarrier`.

**Law 2 re-makes the region's lends, it does not move them** (*Law 2*). Re-made, they re-lend at
every first-order type at every depth, and every term Core's typing derives re-lends at every type;
at `U` re-lending reads room, on every lifetime order (*Re-lending*).

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
version (`no_carrier_of_dense`), nor one storing every finitely supported predicate
(`no_fsCarrier`, §7). The switch that is possible keeps (b), (c) and the 23 model-level (a) places on the slots
untouched, and ports the 282 relation-level (a) places, with everything that rests on them, to
`δ : LSubD L` and `ι`. That port is mechanical (§8).

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
* `carrier_rigid`: an order that carries the model has only the identity automorphism (a
  reverse-well-ordered order is rigid). So an order carrying the cells has no automorphism to move
  a lifetime with, and the order whose automorphisms move lifetimes has to be a second one.

Keeping a dense order as the index with every finitely supported predicate storable is §7: no such
carrier exists (`no_fsCarrier`). A restricted class of stored predicates, or strata kept apart from
the lifetimes (`Positioned.lean`), is not ruled out. Syntactic stored predicates are not attempted.

**The construction** (`Carrier.lean`, `Relation.lean`). The carrier the relation reads is any
linear order `L` with a top; the dense instance is `WithTop ℚ` (`Rat.lean`), with Core's slot `n`
at `-n` and slot `0` at `⊤` (`ratSlots`, below every lifetime a slot: `ratSlots_unbounded`).

* `Slots L`: a strictly monotone map from Core's `Life` (the slots) into `L`, `⊤` to `⊤`.
* `LSubD L`, `interpD` (`⊤`, `⊔`, `⊓` of `L`), `atLifeD`, `LtLifeD`, `ModelsD`, `EntailsLtD`.
* `InStratumD`, `OutlivesD`, `boxD`, `ptoMutD`; the relation `vD` at `1`, `⊗`, `U`, `Ref`,
  `[@a]`, `Mut`, and `cD` at `F`, `⊸`, `⊤`, `∀`, one mutual block as Core's; `gSepD`, `gDenD`,
  `SemD`. `FragV`/`FragC` name the fragment.

Everything else is Core's own definition, imported, not copied: cells, resources, `●`, `○`, the
walks, `↭`, `wpTS` with its typed world `TW` and tagged record lists, `⋆`, `─⋆`, `⌜−⌝`.

**Every change from Core's clauses, and why.**

| Core | here | why |
|---|---|---|
| `δ : LSub` (values `ℕ`), `Life.interp` | `δ : LSubD L`, `interpD` | the reading's lifetimes are `L`'s |
| `cC` at `∀`: `∀ α : Life` | `∀ α : L` | the `∀` ranges over the dense order |
| `ptoMutS`: `α ⊑ b` | `ptoMutD`: `α ⊑ ι b` | `α` is an `L`-lifetime, `b` a slot |
| `box`/`Outlives`: `α ⊏ @ψ` | `boxD`/`OutlivesD`: `α ⊏ ι(@ψ)` | as above |
| `LifeCtx.Models`, `EntailsLt` | `ModelsD`, `EntailsLtD` | over `L`; Core's premises carry over (§8) |

**The cell recursion is unchanged.** The cells, resources and their recursion are Core's own,
`Paper/S5_Model`'s `Cell` by `WellFounded.fix` down `⊏` on `Life = ℕᵒᵈ`, slot for slot; only the
relation reads `L`. **The statics are unchanged too**: typing, `Δ ⊨ @a ⊏ @b`, `Δ ⊨ @a ⊑ @b` and
`Δ ⊨ @a` stay Core's, over `ℕ` (`SLife`, `LifeCtx.Models` on `LSub`); `ModelsD` and `EntailsLtD`
are the relation's reading of them over `L`, and Core's premises reach it through
`entailsLtD_of_entailsLt`, `entailsLeD_of_entailsLe` and `definedD_of_defines` (§8).
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

## 4. Moving the slots' positions (`Shift.lean`, `Rat.lean`)

The segment shift of `L` at the cut `c` by `k > 0` (`shiftQ c k`): every lifetime strictly below
`c` moves down by `k`, the rest stays; it is an order embedding, not onto. Here it moves what the
relation reads in `L`, the slots' positions (`shiftSlots ι c hk`) and the reading; the resource,
records and term stay, so no cell changes slot. This is invariance under moving slot positions,
a corollary of `cD_map` and the homogeneity of `ℚ`. It is not `SegShift.lean`'s move, which
re-slots the cells and the records: that move is §5's.

* `exists_aut_agree`, `config_bound`, `slots_bound`: on a configuration's lifetimes (every slot
  position and every value of the reading) the shift agrees with an order automorphism of
  `WithTop ℚ`: the translation when `c = ⊤`, else `plIso`, which translates up to the greatest
  relevant lifetime below the cut, stretches the rest of the way up to the cut, and fixes the cut
  and above.
* `segShift_iff`: **the configuration with its positions and reading shifted is related exactly
  when the configuration is**, at every cut, `k`, slots, type, records, reading, term and
  resource; `segShiftInvD` states it as an invariance.
* `not_denseCoreAllNotNatural`: `CoreAllNotNatural` with the move made on positions is false.
  `cD_imp_cutAllD`: the relation implies the position-`∀`, its renaming of positions and reading
  by every automorphism of `L`. `cD_comp_of_agree`: any move agreeing with an automorphism on the
  configuration's lifetimes leaves the relation unchanged, at every `L`.
* At `L = Life`: `segShiftFailsAtEveryCutD`: every position shift by `k > 0`
  (`Restrat.Emb.shift`), at every cut, breaks the relation at the cell adjacent to the cut.

## 5. Re-slotting a region (`Reslot.lean`)

ProbeD1's move, over `L`: every cell re-slotted by `θ : Restrat.Emb c` (`θ.relRU`: its lifetime
moved, its witness moved, its stored predicate moved to its image), every record by
`Targets.srecRestrat θ`, the reading by any `ψ : L → L` with `ψ (ι s) = ι (θ s)` for every slot.
`ReslotInvV`/`ReslotInvC` state that this preserves and reflects the relation at every fragment
type.

* **The witness** (`rhoMM`, `vD_rhoMM`): a borrow of a borrow,
  `ℓ ↦ mut(n+1, ℓ′, ℓ′ ↦ mut(n, (), ∅, 𝒱⟦1⟧), 𝒱⟦Mut 'b 1⟧δ)`, related at `Mut 'a (Mut 'b 1)` with
  `'a`, `'b` read at the two slots' positions, and at `F (Mut 'a (Mut 'b 1))` with `return ℓ`; a
  typed world (`tw_nested`), so `wpTS` cannot hold at it vacuously.
* **Why it fails** (`ofS_relS_ne_vD_mb`): a re-slotting other than the identity moves its least
  moved slot `g` below `g` and leaves `g` with no preimage (`exists_gap`). At the moved reading
  `𝒱⟦Mut 'b 1⟧` holds at a `mut` cell at `g`; the re-slotted outer cell stores the image of its predicate, which
  holds only at re-slotted resources. So no re-slotted resource is related at
  `Mut 'a (Mut 'b 1)` (`not_vD_mm_relRU`), and no re-slotted typed world runs to such a value
  (`not_wpTS_mm_relRU`: `↭` keeps each `mut` cell's stored predicate, and every `mut` cell of a
  re-slotted flattening stores an image, `Restrat.Emb.flatAt_mut_moved`). This is
  `Restrat.MutCounterexample.mut_not_natural`'s mechanism, with `Mut` in place of `Imm`.
* `not_reslotInvV`, `not_reslotInvC`, `reslotFailsAtEveryCut`: the failure at every `L`, `ι`,
  `θ ≠ id`, `ψ`, and at every segment shift by `k > 0` at every cut. `shiftQ_ratSlots`: at
  `WithTop ℚ` probe 1's position shift is a `ψ` for `Restrat.Emb.shift`, so `not_reslotInvC_rat`
  is the faithful version of §4's shift. `reslot_fails_vD'`, `reslot_fails_cD'`: the same when
  the slots are also placed anew after the move (`ψ ∘ ι = ι' ∘ θ`), so re-slotting combined with
  any position move fails; `exists_readingMove`: such a `ψ` exists for every `ι`, `ι'`, `θ`.
* `remake_not_move`: at the moved reading, the borrow of a borrow made afresh at the moved slots —
  same locations and values, each `mut` cell storing `𝒱⟦−⟧` at the moved reading — is related,
  and the moved one, whose cells store images, is not.
* `not_bridgeV`: re-slotting the resource and records by `θ` is not moving the slots' positions to
  `ι ∘ θ` (`Slots.reslot`). The fragment has no `Imm`, and the bridge fails without it; adding
  `Imm` adds `mut_not_natural`'s own witness and restores nothing.
* `not_denseThawTop`, `not_denseThawTop_rat`: `Bridge.CoreThawTop` over `L`, at every `ι` and
  every `ψ` agreeing with `shift ⊤ 1`.
* In Core, through `cD_id`: `core_reslot_fails`, `not_segShiftInv_noAll`, `not_coreThawTop_noAll`.
  ProbeD1's witnesses read the room below a `∀`'s bound, which a dense `L` removes; this one has
  no `∀` and fails at every lifetime order.

## 6. No slot in the gap (`Reslot.lean`)

A cell sits at a slot, so a lifetime of `L` carries a cell only at a slot's position.

* `slots_between_iff`, `no_slot_between_adjacent`: under every placement the slots whose positions
  lie between two slots' positions are the slots between them; adjacent slots stay adjacent.
* `placement_keeps_order`: lends taken below the region's stay below them under every placement,
  so no position move puts the region beneath the resumer's lends.
* `shiftSlots_gap_empty`, `shiftQ_gap_nonempty`: the gap `[q − k, q)` probe 1's shift opens in `L`
  is not empty and holds no slot.

So the moves the relation is invariant under (positions, `cD_map`) cannot put a slot in the gap,
and the moves that free slots there by carrying each stored predicate to its image (`θ.relRU`,
with or without new positions, §5) break the relation: no such move puts the resumer's lends in a
gap beneath the region with the relation preserved. Re-making the region's cells frees the same
slots and keeps the relation at every first-order type (*Re-lending*).

## 7. Cells at every lifetime: finite support (`Nominal.lean`)

The other way to make room is a carrier whose cells live at every lifetime of a dense `L`, so that
`L`'s automorphisms move cells too, with no gap: cells by recursion over the finitely many
lifetimes in play, stored predicates finitely supported (nominal sets with ordered atoms).

* `FSCarrier L Loc Val Adm`: the layer equation over `L` in the union view (`CellU`'s with `L` for
  `Life`): cells `C` acted on by `L ≃o L`, a map `out` from cells to layers that is injective,
  lands in the well-formed layers, reaches each of them, and commutes with the action. A
  well-formed `mut` layer's predicate holds only in its stratum, at the cell's value and witness,
  and is supported by a finite `S` with `Adm β S`: `AnySupport` (nominal) or `SupportAbove` (only
  lifetimes at or above the cell's, as the predicates the relation stores are).
* `no_fsCarrier`: **no solution over an order with an infinite ascending chain** `a₀ < a₁ < ⋯`.
  The cells `Y k` at `a k` whose witness is one cell at `a (k+1)`, fixed by the automorphisms
  fixing `a k` and `a (k+1)`, receive the subsets of `Y (k+1)` injectively: `T` is stored as its
  closure under those automorphisms (`clo`), supported by `{a k, a (k+1)}`, and the witness pins
  `a (k+2)` (`Y_pin`), so the closure meets `Y (k+1)` in `T` alone (`mem_clo_iff`). Then
  `#Y k ≥ 2^#Y (k+1)`, a descending sequence of cardinals. The stored predicate holds at cells
  whose witness sits at any of the infinitely many lifetimes above `a (k+1)` an automorphism
  fixing `a k`, `a (k+1)` reaches.
* `no_fsCarrier_of_dense`, `no_fsCarrier_withTopRat`, `no_fsCarrier_withTopRat_above`: none over a
  dense order with two points, in the nominal reading or with supports above the cell.
* `fsCarrier_life`, `fsCarrier_lifeAny`, `fsCarrier_lifeAbove`: over `Life`, whose only
  automorphism is the identity, Core's cells are one, so the notion is the paper's model.

Finite support does not replace recursion down `⊏`: the obstruction is `Cantor.lean`'s, with the
stored predicates confined to what a cell at a lifetime and the one above it can see. It is an
obstruction to the full layer equation, `out` reaching every well-formed layer: a carrier storing a
restricted class of predicates, finite carriers glued along embeddings, and a carrier whose strata
are kept apart from the lifetimes (`Positioned.lean`, *Re-lending*) are not ruled out.

## 8. The FL map

What each rule of `fundamentalC` (`Core/Fundamental.lean`) reads in the lifetime order, and what
its compatibility proof needs when `δ` and the `∀` move to `L`. Re-proved here: `allI`, `allE`,
`withbor2`. The rest is the reading of the existing proofs, not re-proved.

| rules | read in `L` | transfer |
|---|---|---|
| `var`, `unitI`, `tensorI`, `sumI₁₂`, `thunkF`, `thunkV`, `ret`, `bind`, `force`, `lam`, `app`, `withI`, `proj₁₂`, `topI`, `unitE`, `tensorE`, `sumE`, `zeroE`, `bangThunkF/V`, `bangE`, `copyBang`, `forgetBang`, `lolliE`, `ofRet`, `roll`, `unroll`, `nuIn`, `nuOut`, `unfoldN`, `foldOwn`, `foldReuse` | nothing; `δ` is passed through; `U`'s Kripke order `Ext` compares slots | unchanged, `δ` re-typed |
| `alloc`, `free`, `swap`, `lit`, `hostOp`, `arrNew`, `arrFree`, `arrSize`, `arrReplace`, `countFold`, `countTry`, `boundedFix` | nothing | unchanged |
| `effSub`, `effPerform`, `effRaise`, `effLet`, `effThen`, `effHandle` | nothing: operation types are closed in lifetimes | unchanged |
| `allI` | `∀` over `L`, `⟦Δ⟧` | **re-proved**, Core's proof step for step: `allI_compatD` |
| `allE` | `∀` at `@aδ`; `Δ ⊨ @a ⊏ @b` | **re-proved**: `allE_compatD`, through `CTyEqD.instLife` and `cD_tyEq` (Core's `CTyEq.instLife` with `interpD`). Its premise is Core's own `LifeCtx.EntailsLt` over `ℕ`, carried to `L` by `entailsLtD_of_entailsLt`: a reading's values are finitely many, and re-read by rank (`rankIn`) in `ℕᵒᵈ` they keep `⊤`, `⊔`, `⊓` and the strict order |
| `allEV` | `allE` under `U` | transfers as `allE` does (`U` is built over `L`) |
| `immSub`, `mutSub` | `α ⊑ ι b`, antitone in `α`; `Δ ⊨ @a ⊑ @b` | transfers; the premise by `entailsLeD_of_entailsLe` (proved) |
| `boxI`, `boxE` | `[α]` through `ι`; 6.60 (`vC_outlives`) | transfers: 6.60's induction reads the order of `L` and `ι`'s monotonicity |
| `copy`, `forgetImm`, `forgetMut`, `forgetUnk`, `arrLen`, `arrGet`, `arrCopy`, `arrForget`, `sliceGetM`, `sliceLenM`, `sliceSplitI/M`, `sliceEmptyI/M`, `sliceReplaceM`, `sliceSwapM` | the `Imm`/`Mut` clauses through `ι`; `Imm`'s coherence `CohE` compares the type at `δ` with a record's `(T, δ)` | transfers once records carry `LSubD L` (`FrameRec.δ`) and the typed world's 6.64 premises (`vShape`) read `L` through `ι`: a re-indexing of `FrameRecords`, `World` and the shapes |
| `withbor2` | the callback's `∀` at a fresh lifetime; 6.60 at the side condition; `U` | **re-proved**: `withbor2_compatD` (at `WithTop ℚ`: `withbor2_compatD_rat`), Core's proof step for step. Core instantiates the callback at the lifetime `α` of 6.65's `И`, a slot; here at `ι α`, with `И`'s bound taken at a slot whose position is below `@(⊓Δ)δ` (`fresh_bound`); the borrow and the result's `[−]` at `ι α` are the model's at `α` (`ptoMutD_slot`, `outlivesD_slot`); 6.65 itself is the model's (`wpTS_M_frameG`: `wpTS_M_frameX` with the payload predicate abstracted); 6.60 non-strict over `L` reads the side condition (`vD_outlivesLe`), its premise carried by `definedD_of_defines`. **Needs a slot below every lifetime of `L`** (`ratSlots_unbounded` at `WithTop ℚ`) |
| `withbor1/3`, `withload`, `withswap`, their unwinding forms, `sliceBorrowM/I` (and `U`), `foldImm` | the callback's `∀` at a fresh lifetime | transfers as `withbor2` does; the `Imm` lends (6.64, 6.150) also need the record re-indexing above. The frames, their `↓`-strata and the (c) places stay on the slots, untouched |
| `adequacyC`, `theorem32` | `δ = ∅` | unchanged |

The re-proved lemmas are statements about Core's rules only at fragment types: outside
`FragV`/`FragC` the relation is `False`, and there they hold for that reason alone.

**New mathematics: none for FL.** The work is the port of the relation layer (the 282
relation-level (a) places and what rests on them), the record and typed-world re-indexing, the
fresh-slot hypothesis, and the premise transfers (proved: `entailsLtD_of_entailsLt`,
`entailsLeD_of_entailsLe`, `definedD_of_defines`).


## Law 2

**No move that carries stored predicates to their image (`θ.relRU`) preserves the relation, on any
carrier tried.** On Core's carrier ProbeD1's witnesses and `not_segShiftInv_noAll`; on the two-order
design `not_reslotInvC` and `reslot_fails_cD'`, and position moves cannot put the region beneath the
resumer's lends (`placement_keeps_order`); a carrier with cells at every lifetime of a dense order
storing every finitely supported predicate does not exist (`no_fsCarrier`). The re-slotting
refutations share one mechanism: a moved `mut` cell stores the image of its predicate, and the
relation at the moved reading admits cells at the slots the move leaves free, which the image
refuses (`ofS_relS_ne_vD_mb`). The slots are rigid (`carrier_rigid`): a re-slotting other than the
identity is not onto (`exists_gap`), so every such move leaves free slots.

**So Law 2 re-makes the region's lends; it does not move them.** Ended at the stop and made afresh
at the fresh lifetime, each `mut` cell stores `𝒱⟦T⟧` at the new reading, which is what a moved cell
lacks: at the borrow of a borrow the re-made configuration is related where the moved one is not
(`remake_not_move`), and at every first-order type at every depth (*Re-lending*, `relend_fov`).

**Where the room is read.** Re-making the region beneath the resumer's lends opens room between the
lifetimes at and above the cut and the region's cells. Core's `∀` clause reads that room: at
`L = Life` it holds at a cell made at the slot adjacent to its bound and fails at the same cell made
one slot lower (`coreAllAdjacentD`, ProbeD1's `coreAllAdjacent`). Over a dense `L` the `∀` clause
does not: it does not tell cells below its bound apart (`dense_same_order_type`), and room opened by
moving positions is invisible (`segShift_iff`). The relation's quantifiers over resources read it on
every `L`: a cell sits at a slot, the slots are discrete (`carrier_covBy`), and a type can need a
slot strictly between two lifetimes (`not_reflect_boxMM`); through the argument of a `⊸` this
breaks re-lending at `U` (`not_relend_kU`, at every re-lending other than the identity on every `L`,
and in Core). Density of the reading removes room from the `∀` clause; the relation's quantifiers
over resources read room at every `L` (`not_reflect_boxMM`).

**What carries Law 2 at `U` is where the closure came from.** The refuting closure is related only
because its argument type is empty at the reading; a term the fundamental property relates is
related at every reading in `⟦Δ⟧`, and re-lends at every type once its captured context does
(`semD_relend`); in Core every derivable term over a first-order context re-lends
(`core_relend_derivable`), on Core's own carrier. κ's frames are not such a term: their relation
comes from the run that suspended them, and relating them at the fresh lifetime is what remains
(*What is open*).

## Re-lending: an invariant at any depth (`Relend*.lean`, `Positioned.lean`)

The question: nesting depth is order, so a fix for `Mut 'a (Mut 'b 1)` has to be the same at
`Mut 'a (Mut 'b (Mut 'c 1))`; Law 2 needs one property, defined once, closed under every type
former by one induction, that makes re-lending valid. The hypothesis tested: stored predicates are
**order-parametric** — they read only the order of the lifetimes in their support, so they survive
every order-preserving re-lending.

**The answer.** Depth is not where it fails: re-made, the region's cells re-lend at every
first-order type at every depth, by one induction, at every lifetime order and on Core's own
carrier. Order-parametricity is false, already at a first-order type, at every re-lending other than
the identity, on every lifetime order and in Core: the relation reads **room**, whether a slot lies
between two lifetimes, because a cell sits at a slot and the slots are discrete. Through the
argument of a `⊸` the failure of reflection becomes a failure of re-lending at `U`, inside a closure
and inside a stored continuation's type, at a closure that stores no predicate at all. What makes
re-lending valid at `U` is that the closure is a term the fundamental property relates: every term
Core's typing derives re-lends at every type. That is a fact about how a configuration was built,
not a property of the predicates its cells store.

**Re-lending** (`Relend.lean`). `Relend ι`: a re-slotting `θ : Restrat.Emb c` of the slots below
the cut and a reading move `ψ` that keeps the order and agrees with it on the slots
(`ψ (ι s) = ι (θ s)`). `θ` may put the region below any given lifetimes (`Restrat.Emb.shift_fresh`),
so "beneath the resumer's list" is one choice of it; at `WithTop ℚ` probe 1's shift is one
(`ratRelend`), at `Life` the re-slotting itself (`lifeRelend`). The region's cells are **re-made**
(`RemakeC`, `RemakeO`, `RemakeR`): same location, kind and value, the slot moved by `θ`, the witness
re-made cell by cell, the stored predicate whatever the relation at the moved reading asks for.
`RemakeR` re-makes every cell of a resource, not only the region's: a cell at or above the cut
keeps its slot (`θ` fixes it), and its re-make may change only the predicate it stores.

**1. The invariant.**

* `RelendV ι A`: at every re-lending, every configuration related at `A` has a re-make related at
  the moved reading, with the records re-slotted. A `mut` cell storing `𝒱⟦A⟧` can be re-made when
  its payload satisfies it; `relend_mut` isolates the two obligations at any payload: the payload's
  values re-lend, and its stratification (the payload lies in the cell's stratum) is carried to the
  moved reading.
* `OrderParamV ι A`, the hypothesis as stated: `RelendV ι A` and its converse, every configuration
  related at the moved reading being the re-make of one related at the reading.
* Not vacuous: `RelendV` holds at every first-order type (`relendV_of_fov`) and fails at `kU`
  (`not_relendV_kU`); `OrderParamV` fails at `boxMM` (`not_orderParamV_boxMM`).
* Conservativity, in Core (`L = Life`, the identity placement): Core's relation `vC` re-lends at
  every first-order type at every configuration (`core_relend_fov`), so at every configuration a
  kernel program builds; every term Core's typing derives, closed by a first-order context, re-lends
  at every computation type (`core_relend_derivable`, through `fundamentalC`). Not checked: a
  configuration whose closures are not terms the fundamental property relates, κ's frames mid-run
  among them.

**2. Closure.**

* `1`, `⊗`, `Ref`, `[@a]`, `Mut`, nested to any depth: **proved**, by one induction
  (`relend_fov`). At `Mut` the witness re-lends by the induction hypothesis and the stratification
  is carried by `strat_relend`: where a payload's top-level `mut` cells may sit is read by lifetime
  comparisons only (`lbV`, `cells_of_vD`, `lbV_relend`), and a top-level cell can be lowered to any
  slot those comparisons admit (`lower_vD`). No split on depth or on a witness; `FOV` is the grammar
  of the first-order formers.
* `U`: **fails**, machine-checked (`not_relendV_kU`), at every lifetime order, placement and
  re-lending other than the identity, at every cut (`not_relendV_kU_everyCut`), at `WithTop ℚ`
  (`not_relendV_kU_rat`) and in Core (`core_not_relend_kU`, `core_not_relend_kU_everyCut`), at
  `kU = U ([@'a] (Mut 'a (Mut 'b 1)) ⊸ F (Mut 'a (Mut 'a 1)))`, a type with no `∀` and no `Imm`.
  The kill criterion is met at this step; no patch was tried.
* `⊸`: the same failure at the computation level (`RelendC`, `not_relendC_kC`). `∀` and `F`: not
  derived. At `∀` one re-make has to serve every instance of the quantifier; at `F` the `wpTS`
  frames at the moved reading have to be sent back, and a frame holding a cell at a slot the
  re-slotting frees is the re-make of nothing (`Restrat`'s `frame_outside_image`, for images). No
  obstruction verified at either.
* `Imm` is outside the fragment (`vD` is `False` there) and is not addressed.

**Why `U` fails: room** (`RelendRoom.lean`). `[@'a] (Mut 'a (Mut 'b 1))` (`boxMM`) needs its outer
cell strictly above `@'a` (the `[−]`) and strictly below the inner cell (the `Mut` clause's
stratification): a slot strictly between `@'a` and `@'b`. With `'a` at a slot and `'b` at the slot
just above it, nothing is related (`vD_boxMM_empty`); with a slot between them, a borrow of a borrow
is, and is a typed world (`vD_boxMM_room`, `tw_rhoMM`). A re-lending other than the identity fixes
a slot and moves the slot just below it lower (`exists_adjGap`), so it opens such a slot: `boxMM` is
empty at the reading and inhabited at the moved reading (`not_reflect_boxMM`). A closure of `kU` is
then related at the reading because its argument type has no value there (`vD_kU_vacuous`); at the
moved reading the argument is there and `F (Mut 'a (Mut 'a 1))` has no value (`vD_mm0_empty`,
`not_cD_kC`). The closure's resource is empty: it stores no predicate, so no invariant of stored
predicates excludes it. Every order that carries the layer equation and has no least element has a
lifetime just below each lifetime (`carrier_covBy`), so a carrier whose cells sit at their lifetimes
has the adjacent pair the witness uses.

**What carries re-lending at `U`** (`RelendFL.lean`). The fundamental property relates a term at
every reading in `⟦Δ⟧`, and a re-lending keeps `⟦Δ⟧` (`modelsD_relend`,
`Restrat.Emb.models_mapN_iff`). So a term it relates re-lends at every computation type — `U`, `⊸`,
`∀`, `F` — once its captured context does (`semD_relend`); a first-order context does
(`relend_gDenD`, `semD_relend_fov`); in Core, `core_relend_derivable`. The refuting closure is no
such term: a typable `λ` of type `kU` would be related at the moved reading, where its result type
has no value. A captured closure re-lends by the same argument when it is itself such a term over a
context that re-lends; at Core's relation that hereditary version is `htv_relend`
(`experiments/Law2/Law2/Hereditary.lean`), over every lifetime order it is not built.

**3. Consequence, at the instances** (`RelendDepth.lean`).

* Depth three, `Mut 'a (Mut 'b (Mut 'c 1))`: a borrow of a borrow of a borrow, re-made, is related
  at the moved reading at `mmm` and at `F mmm` (`relend_mmm`, an instance of `relend_fov`); moved it
  is not, at every re-slotting other than the identity (`move_not_remake_mmm`): the moved outer cell
  stores the image of `𝒱⟦Mut 'b (Mut 'c 1)⟧`, and at the moved reading that predicate holds at a
  borrow of a borrow whose outer cell sits at a slot the move frees (`ofS_relS_ne_of_gap`,
  `no_preimage`).
* A nested borrow inside a closure: the identity closure at `U (mmm ⊸ F mmm)` re-lends
  (`relend_idClosure_mmm`; `vD_idClosure`: related at every reading); the closure of `kU` does not
  (`not_relend_kU`).
* A closure capturing a borrow of a borrow of a borrow: `λ_. return x` closed by a value of `mmm`
  re-lends at `U (F mmm)` at every re-making (`closure_captures_mmm`,
  `experiments/Law2/Law2/Instances.lean`), from `core_relend_derivable` at Core's relation
  (`relend_derivable` there): Core's typing derives the thunk over the first-order context `x : mmm`.
* Inside a stored continuation's type: `kMut = Mut 'a ([@'a] kU)`, a lent cell holding the closure
  of `kU`, is related at the reading, and no re-make of it is related at the moved one
  (`not_relend_kMut`).
* At every cut: each positive statement holds at every re-lending, and each refutation at every
  segment shift by `k > 0` at every cut.
* The typed world: the configurations the refutations run `wpTS` at are typed worlds (`tw_rhoMM`);
  a re-make of a typed world holding no `imm` cell is a typed world (`tw_remake`,
  `experiments/Law2/Law2/World.lean`: each re-made cell is the end of its lend and the lend made
  afresh, `TW.mutUnfold` then `TW.mutFold`).

**4. The carrier.** For the first-order part the two-order design suffices, and so does Core's own
carrier (`core_relend_fov`, `core_relend_derivable` are at `L = Life`). For `U` pointwise no
lifetime order suffices: `not_relendV_kU` holds at every `L` and placement that admit a re-lending
other than the identity, because the cells sit at slots. A carrier with no room keeps the lifetime
and the stratum apart (`Positioned.lean`): a cell carries a position in any linear order `L` and a
stratum in a reverse-well-founded index only the recursion reads (`PCell`, `PCell_eq`). It exists
over every `L`, dense ones included, and sidesteps `no_fsCarrier`, whose descending cardinals run
along an ascending chain of lifetimes used as strata. The automorphisms of `L` act on it, moving
positions and keeping strata, and the action is a bijection (`pact`, `pact_bijective`): the image of
a stored predicate is its whole transport, where on the two-order design a re-slotting leaves slots
free (`exists_gap`). Not derived: whether Core's relation ports to it. Its `Mut` clause would store
`𝒱⟦A⟧` cut down to the cell's stratum, and a store into a lent place would have to show the stored
value's cells lie in that stratum, which positions do not determine.

**5. The FL map.** At a first-order payload no compatibility lemma has anything to add: every
predicate the relation stores there satisfies the invariant (`relendV_of_fov`), and the borrow
constants' cells (6.65's, `wpTS_M_frameG`, in `withbor2_compatD` and §8's other borrow rows) store
exactly those. At a payload containing `U` no compatibility lemma can show it of the predicate it
stores: `not_relend_kMut` is a lent cell the relation relates whose stored predicate fails it. What
holds there is a property of the stored value — a closure the fundamental property relates — which
the `lam` and `thunk` rules produce and `semD_relend` carries; `relend_mut` says what the cell's
re-make then needs: the value re-lends, and the stratification is carried, which a borrow constant
gives when its cell sits below a lifetime bounding the payload (`withbor2_compatD`'s slot below
`@bδ`, with `VOutlivesLe Δ b A`). New mathematics: none for first-order types or for terms the
fundamental property relates (both proved); for κ's frames mid-run, whose relation is not an
instance of the fundamental property, re-lending needs an argument this probe does not have — a
relation re-lendable by construction at `U` (OQ-8's second option), or a simulation of the suspended
run at the fresh lifetime.

## What is open

**Relating κ at the fresh lifetime.** κ's frames, with the region's lends ended at the stop and
re-made at a fresh lifetime beneath the resumer's list, are related there when κ is a term the
fundamental property relates over a first-order context (`core_relend_derivable`). κ mid-run is not
such a term; whether its frames are related at the fresh lifetime, through the `∀` and `И` of the
borrow rules or otherwise: not derived, no obstruction verified. The pointwise route fails at `U`
(`not_relend_kU`, `not_relend_kMut`).

**Arising.** The Lean refutations — of moves (§5, *Law 2*), of order-parametricity and of
re-lending at `U` (*Re-lending*) — do not depend on arising: each exhibits a configuration of the
relation at every lifetime order. Their consequence for Law 2 does. Whether a borrow of a borrow
arises inside a suspended region, whether a closure related only because its argument type is empty
arises (no typable `λ` is: it would be related at the moved reading, where its result type has no
value), and whether a `∀` that holds by adjacency arises (`coreAllAdjacentD`) are not checked.

**Re-lending at `∀` and `F`; re-made typed worlds; captured closures.** At Core's relation
(`L = Life`), `experiments/Law2` derives: `∀` and `F` for terms Core's typing derives and for typed
segments over hereditarily typed contexts (`relend_all`, `relend_ret`: the fundamental property is
taken at the moved reading, so no instance and no frame is sent back), a re-make of a typed world
holding no `imm` cell is a typed world (`tw_remake`), and the hereditary re-lending of captured
closures (`htv_relend`). Not derived: `RelendC` at `∀` and at `F` pointwise, at every configuration
the relation relates (one re-make for every instance; the `wpTS` frames sent back from the moved
reading), re-making an `imm` cell, and any of these over a dense `L`.

**The positioned carrier's relation.** Whether Core's relation and the fundamental property port to
`PCell`, with the `Mut` clause's stored predicate cut down to the cell's stratum: not derived.

**Where the bridge holds.** It fails at `Mut 'a (Mut 'b 1)`. On which smaller fragment it holds
is not determined; at `U` it would need `Restrat`'s `WpNatural`, which is open.

**Syntactic stored predicates.** A carrier storing types and readings in place of predicates is not
attempted; a cell would have to carry `𝒱⟦T⟧` at its witness, and `𝒱⟦T⟧` reads every cell.

**The rest of the relation over `L`.** Built here: `1`, `⊗`, `U`, `Ref`, `[@a]`, `Mut`, `F`,
`⊸`, `⊤`, `∀`, with Core's records and typed world. Not built: the other formers' clauses
(`⊕`, `0`, `!`, `Imm`, `μ`, `[L]`, `I32`, `Unk`, `&`, `ν`, rows), records over `L`, and the
compatibility lemmas of §8 other than `allI`, `allE` and `withbor2`.

## Files

| file | content |
|---|---|
| `DenseCarrier/Cantor.lean` | the layer equation over any linear order; `carrier_iff`, `no_carrier_of_dense`, `carrier_rigid` |
| `DenseCarrier/Carrier.lean` | `Slots`, `LSubD`, `interpD`, `atLifeD`, `LtLifeD`, `ModelsD`, `EntailsLtD` |
| `DenseCarrier/Relation.lean` | `ptoMutD`, `OutlivesD`, `boxD`, `vD`, `cD`, `SemD` |
| `DenseCarrier/Faithful.lean` | `vD_id`, `cD_id`: Core at `L = Life` |
| `DenseCarrier/Equivariance.lean` | `vD_map`, `cD_map`, `semD_map` |
| `DenseCarrier/Gap.lean` | `holdsD`, `failsD`, the gap test |
| `DenseCarrier/Rat.lean` | `WithTop ℚ`: `ratSlots`, `shiftQ`, `plIso`, `exists_aut_agree` |
| `DenseCarrier/Shift.lean` | moving the slots' positions: `segShift_iff`, `segShiftFailsAtEveryCutD` |
| `DenseCarrier/FL.lean` | `allI_compatD`, `allE_compatD`, the premise transfers, the fresh lifetime through `ι` |
| `DenseCarrier/Borrow.lean` | `withbor2_compatD`; `wpTS_M_frameG`, `vD_outlivesLe`, `vD_local` |
| `DenseCarrier/Reslot.lean` | re-slotting: `not_reslotInvC`, `reslotFailsAtEveryCut`, `not_bridgeV`, `not_denseThawTop`, `core_reslot_fails`; no slot in the gap |
| `DenseCarrier/Nominal.lean` | `FSCarrier`, `no_fsCarrier`, `fsCarrier_life` |
| `DenseCarrier/Relend.lean` | `Relend`, `RemakeR`, the invariant `RelendV`; `relend_mut`, `strat_relend`, `relend_fov`, `relendV_of_fov` |
| `DenseCarrier/RelendRoom.lean` | room: `not_reflect_boxMM`, `not_orderParamV_boxMM`, `not_relendC_kC`, `not_relend_kU`, `not_relend_kMut`, `not_relendV_kU_everyCut`, `core_not_relend_kU` |
| `DenseCarrier/RelendFL.lean` | `semD_relend`, `semD_relend_fov`, `core_relend_fov`, `core_relend_derivable` |
| `DenseCarrier/RelendDepth.lean` | depth three: `relend_mmm`, `move_not_remake_mmm`; `relend_idClosure_mmm` |
| `DenseCarrier/Positioned.lean` | `carrier_covBy`; the positioned carrier `PCell`, `pact_bijective` |
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

