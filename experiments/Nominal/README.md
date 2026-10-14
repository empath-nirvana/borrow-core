# Nominal: lifetimes as atoms with parents

Build with `lake build Nominal`. There is no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`,
`unsafe` or `implemented_by`, and every declaration's axioms are within
`[propext, Classical.choice, Quot.sound]` (`lake env lean experiments/Nominal/scripts/Axioms.lean`).
The library does not import this directory. It imports Core's syntax and type-level definitions
(`VTy`, `CTy`, `Expr`, `forceE`, `RefPos`, `MutPos`, `VFree`, `immReborrow`), `PMap` and the machine
(`BoLo.Steps`, `ARun`), and builds its own carrier, model, records and typed world.

## The question

Problem B (`research/effects/src/tier2-problems.md`) is decided as *close and re-make*: while
stored, a self-borrowing package `∃'x. (own c, contents typed in 'x)` holds no live borrow, and
opening it re-makes the borrow at a fresh lifetime. Probes 3–6 re-made it *positionally*, beneath
the resumer's lifetimes, which gives `x′` parents `x` did not have. That is not an automorphism,
and the relation fails pointwise on vacuous values (`DenseCarrier`'s `core_not_relend_kU`); the
positional route needs history bookkeeping per feature.

The hypothesis tested: **nominal lifetimes**. Lifetimes are atoms, each with a finite set of
parents; outlives is the ancestor order. `x′` is re-made with the **same parents** as `x`, the
swap `x ↔ x′` is an automorphism of the order, and **one equivariance lemma** replaces the
bookkeeping, with stratification and the measure unchanged.

## The outcome

**On the fragment built here, it holds.** The kill criterion is not met: no failure of
equivariance or of the corollary was found, and both are proved.

1. **The carrier exists over a partial order, and it is not rigid.** Cells stratified by ancestry
   exist over every partial order with no infinite ascending chain, and only over those
   (`isCarrier`, `carrier_iff`). The free order of atoms with parents is one, and it has
   automorphisms other than the identity (`swapLft_ne_refl`), where every chain carrying the cells
   has none (`DenseCarrier`'s `carrier_rigid`).
2. **The hereditary swap is an order automorphism** (`Atom.swapIso`, `swapLft`), and every order
   automorphism acts on cells and resources as a **bijection** whose stored predicates are carried
   to their whole transport (`relU_symm_relU`, `img_eq`). The image move refuted on Core's carrier
   (`not_reslotInvC`, `mut_not_natural`) failed because the move was not onto; this one is.
3. **The relation is equivariant under every order automorphism**, at `1`, `⊗`, `U`, `Ref`, `[@a]`,
   `Imm`, `Mut`, `F`, `⊸`, `⊤`, `∀`, by one induction on types, over a model equivariant operation
   by operation, `wp` included: at the printed relation (`vN_map`, `cN_map`), and at Core's
   clauses with records — `Ext` at `U`, `ls₀` at `Mut` and `Imm`, `CohE` at `Imm` — over Core's own
   `wp`, `wpTS` at tagged typed worlds (`vR_map_wpTS`, `cR_map_wpTS`): a typed world moved by an
   automorphism is a typed world (`TWN_act`), and `wpTS` is carried (`wpTSN_equiv`).
4. **Re-opening is a corollary** (`reopen`, `reopen_iff`, `reopen_swap`): opening at a fresh atom
   with `x`'s parents relates exactly what opening at `x` related, at every type, `U` and `⊸`
   included, and at Core's own `wp` (`reopenR_wpTS`). The hypotheses are freshness, discharged for
   owned packages (`reopen_fresh`); there is no history or derivation hypothesis.
5. **The probe-3 witness is preserved by the same-parents re-make and broken by the
   extra-parents one** (`kU_convention`; at Core's own relation and `wp`, the refuting run at a
   typed world: `kUW_convention`), and the extra-parents re-make is not an automorphism
   (`no_automorphism_extra_parents`). Moving a borrow of a borrow by the swap *is* re-making it
   (`move_eq_remake`). The scheduler: owned packages store under every `Mut 'q`
   (`closed_inStratum`); a package that captured a borrow at `s` stores under `Mut 'q` exactly
   when `s ⊐ q` (`vN_store_captured_iff`).

What is built is Core's clauses at the fragment's types, records, typed world and `wpTS` included,
on the nominal carrier; the fundamental property over it is not (*What is not built*).

## 1. Atoms with parents (`Atoms.lean`, `Carrier.lean`)

**The order.** `Atom.mk ps t`: parents `ps` (read as a set) and a tag. `a < b` when `b` is a strict
ancestor of `a` (`Atom.Below`, a chain of parent edges): `b` strictly outlives `a`. It is a partial
order (`Atom.instPartialOrder`) with no infinite ascending chain (`WellFoundedGT Atom`: an ancestor
is a strict subterm). Lifetimes are `Lft ≜ WithTop Atom`; `⊤` is static.

**Fresh atoms.** `Atom.fresh S avoid` has parents exactly `S` and occurs in no atom of `avoid`
(`fresh_not_le`). Every finite set of lifetimes has a common strict lower bound
(`exists_lt_all`), and the lifetimes strictly above a fresh child of `a` are exactly those at or
above `a` (`freshChild_lt_iff`).

**The cell model**, over any partial order `L` with `⊤` and `WellFoundedGT L`. Strata are indexed by
finite sets: `Res_T` is the resources whose cells strictly outlive every member of `T`.

    Cell_S ≜ own(Val) + imm(Imm_S) + mut(Mut_S)
    Imm_S  ≜ {(ᾱ, v, ρ : Res_ᾱ) ∣ ᾱ ≠ ∅, every member of ᾱ strictly outlives every member of S}
    Mut_S  ≜ {(β, v, ρ : Res_{β}, P̂ : Val → SProp_{β}) ∣ β strictly outlives every member of S, P̂(v)(ρ)}

The recursion is `WellFounded.fix` on `Above` ("nonempty, and every member strictly outlives every
member of `S`"), well-founded because `L` has no infinite ascending chain (`above_wf`). `Cell_eq`
is the cell equation, `isCarrier` its solution. Conversely an infinite ascending chain leaves no
solution (`no_carrier_of_strictMono`, the Cantor argument of `DenseCarrier`'s `Cantor.lean` with
set-indexed strata), so `carrier_iff`. The union `CellU`, `InStratum`, and the passage between
`Res_S` and the union are `Paper/S5_Model`'s; a cell is determined by its data (`CellU.ext_data`).

**`[α]P` splits in two.**

| reading | definition | where it belongs | here |
|---|---|---|---|
| (a) every cell strictly outlives `α` | `boxS`, `ResU.InStratum {α}` | a `mut` cell's witness; the `Mut` clause's payload (`ptoMutN`); `[TR]` 6.65's side condition (payload in `Res_β`); 6.60 | `ptoMutN`, `CellU.mutOf` |
| (b) no cell is at or beneath `α` | `boxE`, `ResU.Survives α` | ending a borrow: `[TR]` 6.64's and 6.65's postconditions; the type `[@a] T`; closing a package | `vN` at `[@a]`, `Pkg.CloseOK` |

(a) implies (b) (`CellU.survives_of_inStratum`); on cells comparable with `α` they agree
(`CellU.survives_iff_inStratum`), so on a chain they are one (`boxE_eq_boxS_of_chain`). In the free
order they differ: a cell at `x′`, a sibling of `x`, survives the end of `x` and is not in `Res_{x}`
(`split_is_real`).

## 2. The hereditary swap (`Atoms.lean`, `Action.lean`)

**The swap.** For `x`, `x′` with the same parents (`Atom.SameParents`), `Atom.swap x x′` exchanges
them and re-parents every descendant (`mk ps t ↦ mk (swap ps) t`). It fixes every atom in which
neither occurs (`swap_fix`), in particular every ancestor of `x` (`swap_fix_of_lt`); it is an
involution (`swap_swap`) and preserves parent edges both ways (`parent_swap_iff`), hence the order
both ways (`below_swap_iff`): **an order automorphism** (`swapIso`; on lifetimes `swapLft`, `⊤`
fixed, `swapLft_x`).

**The action on cells**, for every order automorphism `π` (`Action.lean`):

* strata `S ↦ π S` (`mapS`, `above_mapS`); `relC π S : Cell_S → Cell_{πS}` by the recursion that
  builds `Cell`; `relU π` on the union, `relRU π` on resources;
* every lifetime moved, every witness moved (`wit_relU`), lifetimes moved (`lts_relU`), stored
  predicate carried to its image `π·P̂(v)(ρ′) ≜ ∃ρ. ρ′ = π·ρ ∧ P̂(v)(ρ)` (`relP`, `pu_relU`),
  stratum membership and survival carried (`inStratum_relU`, `survives_relU`).

**Natural, unlike the image move refuted before.** `π⁻¹` undoes `π` (`relU_symm_relU`,
`relU_relU_symm`; bijections `actU`, `actR`), so the image is the whole transport
`π·P̂ = P̂ ∘ π⁻¹` (`img_apply`, `img_eq`). `Restrat`'s `θ.relRU` was the image along an embedding of a
chain that is not onto, so a moved cell refused resources at the slots the move left free
(`not_reslotInvC`, `mut_not_natural`). Here nothing is left free. The witness of that refutation,
a borrow of a borrow, moved by the swap, is related at the moved reading and **equals** the borrow
of a borrow made afresh at `x′` (`mm_swap_related`, `move_eq_remake`): under the nominal
convention, the move is the re-make.

## 3. Equivariance (`Model*.lean`, `Relation.lean`, `Equivariance.lean`, `Records.lean`, `CoreRelation.lean`, `TypedWorld*.lean`)

**The model** is `Paper/S5_Model`'s on the new carrier: `▶◀`, `●`, `○`, `◐`, `ρ∣ι`, `⨀`, the walks
`ex` and `ag`, `⦇ρ⦈`, `✓`, `⟦ρ⟧`, `#`, `↭` (guarded), `ρ∣own = ∅`, `⌜−⌝`, `⋆`, `─⋆`, `∃`, `ℓ ↦ v`, and
the printed `wp` over `BoLo.Steps`. Changes where the print uses a chain: `imm` witnesses in
`Res_ᾱ`; lifetime sets united as sets; `○`'s clause `mut(α ⊓ β, …)` only for comparable `α`, `β`, at
the shorter; `↭`'s `mut` clause keyed by the stored predicate read on the union.

Every operation is carried by `π` (`compS_relU`, `compR_relU`, `exW_relRU`, `agW_relRU`,
`flat_relRU`, …) and, since `π⁻¹` undoes it, invariant (`compS_relRU_iff`, `hash_relRU_iff`,
`lower_relRU_iff`, `updV_relRU_iff`, `noOwn_relRU_iff`). The propositions commute with the
transport `P ↦ P ∘ π⁻¹` (`sepN_relRU_iff`, `wandN_relRU_iff`, `exN_relRU_iff`, `pureN_relRU_iff`,
`ptoOwnN_relRU_iff`), and so does `wp` (`wpN_relRU_iff`): its frame quantifier is re-indexed by
`π`, which is onto. `wp` is not vacuous (`wpN_val_empty`, `cN_ret_unit`).

**The record-free relation** `vN b A δ v`, `cN C δ e` (`Relation.lean`): Core's clauses without
the record layer, over the printed `wp`, with these changes:

| Core | here | why |
|---|---|---|
| `δ : LSub` (values `ℕ`), `Life.interp` | `δ : LSubN L`, `interpN` | lifetimes are `L`'s |
| `@(a ⊔ b)δ`, `@(a ⊓ b)δ` as an argument (`atLife`) | the longer / shorter when comparable, else undefined | `⊔`, `⊓` need not exist |
| `α ⊏ @cδ` as a bound (`LtLife`, at `∀` and in `⟦Δ⟧`) | `LtLifeN`: beneath every lifetime of a `⊓`, beneath one of a `⊔` | `⊓Δ` need not exist; where `@cδ` is defined it is Core's (`ltLifeN_iff_of_interp`), and on a chain it is defined (`interpN_some_of_chain`) |
| `∀ α : Life` | `∀ α : L` | — |
| `[α]P`: `ρ ∈ Res_α` | reading (b), `boxE` | `[@a] T` is what survives the end of `@a`; on a chain it is `ρ ∈ Res_α` |
| `ptoMutS`: `α ⊑ b`, payload `⊆ Res_b` | `ptoMutN`: `α ≤ b`, payload `⊆ Res_{b}`, reading (a) | strata set-indexed |
| `ptoImmS`: `α ⊑ ⊓β̄` | `ptoImmN`: `α ≤ m` for every `m ∈ β̄` | `⊓β̄` need not exist |
| records `ls`, `Ext` at `U`, `ls₀` at `Mut` and `Imm`, `CohE` at `Imm`, `wpTS` | none in `vN`; all of them in `vR`, over a `wp` parameter, `wpTS` included | `vN` is the printed relation; `vR` is Core's clauses |
| `η`, `⊕`, `0`, `!`, `Unk`, `μ`, `ν`, `&`, `[L]`, `I32`, rows | not in the fragment (`False`) | — |

The observable view of an `Imm` payload (`b = false`, `U` read as `True`) is Core's.

**`vN_map`, `cN_map`: `𝒱⟦A⟧(π·δ)(v)(π·ρ) ↔ 𝒱⟦A⟧δ(v)(ρ)` and `𝒞⟦C⟧(π·δ)(e)(π·ρ) ↔ 𝒞⟦C⟧δ(e)(ρ)`,
for every order automorphism `π`, every reading, value, term and resource.** One mutual induction
on types; each clause is a lemma of the model:

| clause | by |
|---|---|
| `1`, `⊗`, `Ref` | `pureN_relRU_iff`, `sepN_relRU_iff`, `exN_relRU_iff`, `ptoOwnN_relRU_iff` |
| `[@a]` | `atLifeN_map` (`interpN_map`), `boxE_relRU_iff` (`survives_relRU`) |
| `Mut` | `ptoMutN_relRU_iff`: the moved cell stores the image of `𝒱⟦A⟧δ`, which is `𝒱⟦A⟧(π·δ)` by the induction hypothesis because the image is the whole transport (`img_eq_of`) |
| `Imm` | `ptoImmN_relRU_iff`, the payload in the observable view |
| `U` | the hypothesis at the computation type |
| `F` | `wpN_relRU_iff` |
| `⊸` | `wandN_relRU_iff` |
| `∀` | the quantifier over `L` re-indexed by `π` (onto), `ltLifeN_map` |

`semN_map_iff`: the semantic judgment is invariant (`modelsN_map`, `gDenN_map`).

**Core's clauses with records** (`Records.lean`, `CoreRelation.lean`). Core's record layer on the
nominal carrier: records `⟨ℓ, v, R, T, δ⟩` with their frame lifetimes (`FrameRecN`, `SRecN`), chain
positions over Core's `RefPos` (`ChainN`), relevance (`RelN`), `KeepsN`, `CellInN`, the Kripke order
`ExtN`, coherence `CohN`/`CohEN`, type equality modulo readings `TyEqN`/`CTyEqN`. Where Core
compares a cell's lifetime with a lifetime, the comparison is read on the cell's lifetime set:
`@ψ ⊑ b` (`CellIn`) as "some member is at or beneath `b`", `x ⊐ ⊓β̄` (`ls₀` at an `imm` cell) as
"`x` strictly outlives some member" — both Core's on a chain. `vR W`, `cR W` are Core's clauses
(`vCE none`, `cC`) at the fragment, `W : WpOpN L` the `wp`.

An automorphism moves a record's resource, reading and tag (`FrameRecN.act`, `SRecN.act`); the
record layer is invariant (`chainN_act_iff`, `relN_act_iff`, `extN_act_iff`, `tyEqN_map`,
`cohEN_act_iff`). **`vR_map`, `cR_map`: `𝒱⟦A⟧(π·ls)(π·δ)(v)(π·ρ) ↔ 𝒱⟦A⟧(ls)δ(v)(ρ)` whenever `W`
is carried by `π` (`WpEquiv`)**, by the same induction, the `U` clause re-indexing `Ext`'s list,
`Mut` and `Imm` their `ls₀` (`ptoMutR_act_iff`, `ptoImmR_act_iff`). The printed `wp`, threading the
list unchanged, is carried by every `π` (`wpLift_equiv`, `vR_map_wpLift`).

**Core's own `wp`** (`TypedWorld.lean`, `TypedWorldEquiv.lean`). `Core/World.lean`'s `vShape`, `TW`,
`Tagged` and `wpTS`, with the lineage (`GPos`, `SubRec`, `LinPath`, `Desc`, `LinLoc`,
`FrameLife`) and `reb_α` (`ResU.RebAt`, `ResU.Reb`), at the fragment's types (`vShapeN`, `TWN`,
`TaggedN`, `wpTSN`); a cell Core names by `immOf`/`mutOf` with proof arguments is named by its
data. Every `TW` constructor's premises are moved by `π`: `vShape` (`vShapeN_map`), the lineage
(`descN_act_iff`, `descRN_act_iff`, `linLocN_act_iff`, `frameLifeN_act_iff`), `reb_α`
(`rebN_act`), `StratumLe` (`stratumLeN_act_iff`), `ρ/ℓ`, `dom`, `≤`, `ρ∣dom(σ)`, `ρ∣own,mut`; so
**a typed world moved by `π` is a typed world** (`TWN_act`, `TWN_act_iff`), `Tagged` is invariant
(`taggedN_act_iff`), and **`wpTS` is carried by every order automorphism** (`wpTSN_equiv`):
Core's relation over its own `wp` is equivariant (`vR_map_wpTS`, `cR_map_wpTS`).

## 4. Closing as a corollary (`Package.lean`)

* `Pkg L`: an owned place `c` holding `u` (payload resource `σu`) and contents `w` (resource `ρw`).
* `Pkg.Closed`: the stored resource, `c ↦ own(u) ● σu ● ρw`; no borrow is live.
* `Pkg.Opens P p y ρ`: `c` lent at `y`, the lent cell `mut(y, u, σu, P)`, beside the contents; the
  contents are read at `δ['x ↦ y]`.
* `Pkg.CloseOK p y`: ending `y` leaves the contents intact (reading (b)).
* `Pkg.FixedBy π P p`: `π` fixes `σu`, `ρw` and the stored predicate.

**The corollary.** `reopen` (and `reopenC` at computation types): for every order automorphism `π`
that fixes the package and the reading `δ` of the other variables, the opening at `y` moved by `π`
is an opening at `π y` (`Pkg.opens_relRU`), and it is related at `δ['x ↦ π y]` exactly when the
opening at `y` is related at `δ['x ↦ y]`. `reopen_iff`: some opening at `π y` is related iff some
opening at `y` is. The proof is `vN_map` at `π` and nothing else.

**At a fresh atom with the same parents.** `reopen_swap`: `π` is the swap `x ↔ x′`; its hypotheses
are that `x` and `x′` occur in no lifetime `δ` reads (`LSubN.Avoids`, met by fresh atoms:
`fresh_avoids`) and that the swap fixes the package. The latter holds for owned packages
(`fixedBy_of_ownOnly`) and for captured borrows at lifetimes the swap fixes storing relation
instances at readings it fixes (`relU_mutOf_fix`, `img_vN_fix`). `reopen_fresh`: at
`x′ = fresh x.ps avoid`, for an owned package, only `δ` avoiding `x` remains. `Pkg.closeOK_iff`:
closing is allowed at `π y` iff at `y`. `exists_iff_forall_fresh`: some fresh atom with parents `S`
opens the package to a related configuration iff every fresh one does (the И quantifier).

`reopenR` is the corollary at Core's clauses with records, for an automorphism fixing the record
list as well and carrying the `wp`; `reopenR_wpTS` at Core's own `wp`.

The hypotheses are freshness, the nominal form of "`x′` is fresh". None mentions how the package
was built, and the statement holds at every type, closures included: no hypothesis that the
contents are a term the fundamental property relates (which `DenseCarrier`'s `semD_relend`
needed).

## 5. Witnesses (`Witnesses.lean`)

Atoms (`W.q`, `W.x`, …): `q` beneath `⊤`; `x`, `x′`, `r` beneath `q`; `x″` beneath `q` and `r`.
`x′` is the same-parents re-make of `x`; `x″` the extra-parents one.

**(a) `kU = U([@'a](Mut 'a (Mut 'b 1)) ⊸ F mm0)`, `mm0 = Mut 'a (Mut 'a 1)`.** `mm0` has no value
(`vN_mm0_empty`). At `'a ↦ x`, `'b ↦ q` no lifetime lies strictly between `x` and `q`
(`no_between_x_q`), the argument type is empty (`vN_boxMM_empty_x`), and the closure with no
resource is related (`kU_related_x`). The same-parents re-make preserves the relation at `kU` at
every resource (`kU_swap`, an instance of `vN_map`), so the closure is related at `x′`
(`kU_related_x'`).

**The `Imm 'x (Imm 'r U)` closure.** In this relation `Imm 'x (Imm 'r (U C))` is inhabited at
every reading, `r` an ancestor of `x` or not, by a valid resource (`vN_immImm_inhabited`,
`immImmRes_valid`): an `imm` payload carries no stratification condition, and an inner `imm` cell
at `{⊤}` lies in the stratum of any outer cell. So the premise "vacuously related at `x`, the
domain is empty" does not hold for `Imm` here: the closure over it returning `mm0` is related at
none of `x`, `x′`, `x″` (`kI_related_none`). The premise holds for the `Mut` analogue:
`Mut 'x (Mut 'r 1)` is empty when `r` is not a strict ancestor of `x` (`vN_mutMut_empty`), so
`kV = U(Mut 'x (Mut 'r 1) ⊸ F mm0)` is related at `x` (`kV_related_x`) and at `x′` (`kV_swap`,
`kV_related_x'`).

**(b) The extra-parents re-make fails.** At `x″` the argument types are inhabited by valid
borrows of borrows (`vN_boxMM_x''`, `mmCell_valid`; for `kV`, outer cell at `x″`, inner at `r`), and
`F mm0` has no value, so the same closure with the same empty resource is not related
(`kU_not_related_x''`, `kV_not_related_x''`). `kU_convention` states (a) and (b) together, and
`kUR_convention` the same at Core's clauses with records and the printed `wp` (`CoreWitnesses.lean`:
the argument type is empty at every record list, `vR_boxMM_empty`), and **`kUW_convention` at Core's
clauses over `wpTS`** (`CoreWitnessesTW.lean`): the refuting run at `x″` is taken at a typed world,
the borrow of a borrow built from `∅` by `alloc` and `mutFold` (`tw_mm`, as Core's `tw_nested`). No order automorphism fixing
`q` sends `x` to `x″` (`no_automorphism_extra_parents`): the convention, not the carrier, is what
decides.

**(c) The scheduler.** A closed package whose resources are owned — a task that borrowed only its
own local, `S = ∅` — lies in every stratum (`closed_inStratum`), so every family of them meets the
`Mut` clause's stratification at every lifetime (`closed_family_stratified`); `Mut 'q (Ref 1)` is
inhabited at every `q` (`vN_store_owned`). A package that captured a borrow at `s`, of type
`Ref 1 ⊗ Mut 's 1`, can be stored under `Mut 'q` exactly when `q < s` (`vN_store_captured_iff`):
Rust's `T: 'q`.

**The self-borrow.** The minimal package (`c` owns `()`, the contents are the borrow of `c`),
opened at `x`, is related at `Mut 'x 1` (`selfBorrow_related`), and re-opened at `x′` too
(`selfBorrow_reopen`, from `reopen_swap` with every hypothesis discharged). At a closure type: the
package whose contents are `λ_. c`, a closure over the borrow of its own place, is related at
`U (F (Mut 'x 1))` when opened (`genPkg_related`: forcing it runs one `β` step to the borrow, a
valid run), and `reopen_swap` carries it to `x′` (`genPkg_reopen`).

## 6. Core port map

Where Core reads the chain, and how each restates over parents. "Built" means the restatement is
in this library; "fact proved" means the replacement fact is proved and its users are not ported;
"not ported" means only the restatement is given.

| Core reads the chain at | where | over parents | status |
|---|---|---|---|
| strata indexed by one lifetime; `imm` witness in `Res_{⊔ᾱ}`, stratum test `⊓ᾱ ⊐ α` | `Paper/S5_Model` (`Cell`, `ImmU`, `LSet`, `CellU.InStratum`) | strata indexed by finite sets; `Res_ᾱ`: strictly above every member; `⊓ᾱ ⊐ α`: every member above `α` | built (`Carrier.lean`) |
| `@ψ = ⊓ᾱ` for an `imm` cell; `α ⊑ ⊓β̄` in `ptoImm` | `CellU.at`, `ptoImmS`, `CellIn` | the set `ᾱ`; `α ⊑` every member | built (`CellU.lts`, `ptoImmN`) |
| `ᾱ₁ ∪ ᾱ₂` with `⊓`, `⊔` recomputed in `●` | `LSet.union`, `CellU.CompS` | set union | built |
| `○` clause (3), `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`: two `mut` cells agreeing in `ag` | `CellU.CompR.mutMut`, and its users in `Support/Model` (`Composition`, `Update`, `Outlives`, `Reborrow`, `Surgery`, …) | comparable `α`, `β`: at the shorter (built); incomparable: `mut` cells would carry lifetime sets, as `imm` cells do, `Res_ᾱ` and "dies when any member ends" | restricted to comparable; the set form not built |
| `@ρ = ⊓` over the cells (`ResU.at`, `AtLife`, `atOn`) | `fresh_frame` (6.112)'s bound `a ⊓ β`, `withbor*_compatX`'s `a₂ ⊓ m`, `ResU.exists_stratum` | the finite set of the cells' lifetimes; `α ⊏ @ρ` is `ρ ∈ Res_{α}`, already universal over cells (`[TR]` p. 32's reading, adjudication §C.25) | not ported |
| `[α]P ≜ @ρ ⊐ α` | `box`, `Outlives`; 6.60 (`vC_outlives`), 6.64, 6.65, `boxI`/`boxE` | (a) for strata, `Mut` payloads, 6.65's side condition, 6.60; (b) for 6.64's and 6.65's postconditions and `[@a] T` | both defined; the relation uses (b) at `[@a]`, (a) at `Mut`; the frame rules not ported |
| `И P̂ ≜ ∃β. ∀α ⊏ β. [α]P̂(α)` | 6.64, 6.65, 6.112, every borrow rule | `∃` finite `B`. `∀α` beneath every member of `B`; a witness is a fresh atom with parents `B` | fact proved (`exists_lt_all`); `И` not ported |
| `⊓Δ`, the bound `'x ⊏ @(⊓Δ)` of `withbor` and `withload` | `LifeCtx.meetOfDom`, `axWithbor*Ty`, `withbor*_compatX`, `withload` | "beneath every lifetime of `Δ`" | built (`LtLifeN`, `ModelsN`; Core's where `@(⊓Δ)δ` is defined: `ltLifeN_iff_of_interp`) |
| `↓α` as "some lifetime strictly shorter" (`exists_shorter`, `exists_fresh`, 6.65's `A := b₀ ⊓ ↓(γ ⊓ β)`) | `Support/Model/ReborrowRule.lean`, `Core/Wp.lean`, `Core/FrameRules.lean`, `Core/EffBorrow.lean`, … | a fresh atom beneath the finitely many lifetimes in play | fact proved (`exists_lt_all`) |
| `↓α` with "nothing strictly between `↓a` and `a`" (`Life.le_of_down_lt`, `Life.not_lt_of_down_lt`): `⊒ α` written `Res_{↓α}` | `ResU.six27`, `ResU.six52_*`, `Support/Model/Outlives.lean`, and the 214 declarations on them (`DenseCarrier` census class (c)) | `↓a` is a fresh child of `a`: `c < x ↔ a ≤ x` | fact proved (`freshChild_lt_iff`); users not ported |
| `P ⊨ ∃α. [α]P` ("every resource lies in a stratum", `Res_{↓@ρ}`) | `ResU.exists_stratum` | a fresh atom beneath every cell's lifetimes | fact proved (`exists_lt_all`) |
| `@(a ⊔ b)δ`, `@(a ⊓ b)δ` as an argument | `Life.interp`, `atLife` | defined on comparable pairs | built (`interpN`) |
| `Δ ⊨ @a ⊏ @b`, `Δ ⊨ @a ⊑ @b`, `Δ ⊨ @a` | `LifeCtx.EntailsLt/Le/Defines`; `allE`, `immSub`, `mutSub`, borrow rules | over `⟦Δ⟧` read by `ModelsN`; a `Δ` records parents | not ported |
| records' tags `x.2 ⊐ b`, `ls₀ = {x ∈ ls ∣ x.2 ⊐ b}` (`x.2 ⊐ ⊓β̄` at `imm`), `Ext`, `CellIn ρ b` (`@ψ ⊑ b`) | `Core/Relation`, `Core/Wp`, `Core/FrameRecords` | comparisons on the cell's lifetime set: `x.2 ⊐ ⊓β̄` as "strictly outlives some member", `@ψ ⊑ b` as "some member at or beneath `b`" | built (`Records.lean`, `CoreRelation.lean`) |
| `StratumLe W β` (`⊒ β`: `∀β′ ⊏ β`), `TW.reb`'s `β` | `Core/World.lean` | `∀β′ ⊏ β` over the partial order; equivalently `W ∈ Res_{c}` for `c` a fresh child of `β` (`freshChild_lt_iff`) | built (`StratumLeN`) |
| `reb_α`'s `imm({α}, …)` and `t ⊆ s` | `ResU.RebAt`, `ResU.Reb` | `{α}` a singleton set; `t ⊆ s` of finite sets | built (`TypedWorld.lean`) |
| `min`/`max` lemmas at `Life` (`LSet.union`, `Life.meet_assoc`, `cellCompS_inStratum`, …) | census class (a), 14 places | set union; `∀` over a set | not ported |

The pattern: a single lifetime that the chain supplies as a `⊓` or `⊔` of finitely many becomes the
finite set itself, read with `∀` (beneath every member) or `∃`; a lifetime the chain supplies "just
below" becomes a fresh atom with the given parents.

## What it means for problem B

* **On this fragment the nominal convention passes where the positional one failed.** With `x′`
  given `x`'s parents, re-opening relates exactly what opening related, as a corollary of one
  equivariance theorem proved by induction on types; a new type former adds one case to that
  induction. This holds at Core's own clauses and `wp` (`vR_map_wpTS`, `reopenR_wpTS`). With extra
  parents, the probe-3 witness fails as before, there too (`kUW_convention`), and no automorphism
  is available.
* **The measure and stratification are unchanged.** The carrier is still built by well-founded
  recursion on strata ordered by ancestry, with no step-indexing; a `Mut` cell's payload still
  lies in its stratum (reading (a)), which is what makes owned packages storable anywhere and
  packages with captured borrows storable only under `Mut 'q` with `S ⊐ 'q`.
* **The re-make needs no separate construction.** Moving the opened package by the swap is
  re-making its borrow at `x′` (`move_eq_remake`), including the stored predicates.
* **`DenseCarrier`'s open item, relating `κ` at the fresh lifetime, is `reopen` at `κ`'s type.**
  The positional route needed `κ` to be a term the fundamental property relates (`semD_relend`)
  and failed pointwise at `U` (`not_relend_kU`); under the nominal convention a stored package —
  its contents a closure or a suspended computation — is related at `x′` whenever it was at `x`,
  at every configuration the swap fixes.
* **The relation has to read lifetime expressions as bounds** (`⊓Δ` as "beneath every lifetime of
  `Δ`") and `[α]` in two ways; both are natural and agree with Core on chains.

## What is not built

* **Types outside the fragment.** `⊕`, `0`, `!`, `Unk`, `μ`, `ν`, `&`, `[L]`, `I32`, effect rows and
  the type-variable environment are not in the relation, nor in `vShape` (so `TW` holds records
  only at the fragment's types).
* **The fundamental property and adequacy over the nominal carrier**, and every compatibility
  lemma: not attempted. The port map says what each chain use becomes.
* **Faithfulness at a chain.** Each clause agrees with Core's on a chain (`ltLifeN_iff_of_interp`,
  `interpN_some_of_chain`, `boxE_eq_boxS_of_chain`), but the carrier over set-indexed strata is not
  shown isomorphic to Core's at a chain.
* **`mut` cells at incomparable lifetimes in `○`**: undefined here; the lifetime-set form is not
  built.
* **The package as a type former** with typing rules and compatibility lemmas: only the semantic
  package (`Pkg`) and its opening.
* **Arising.** Whether Core's typing rules out the `imm` cell at `⊤` that inhabits
  `Imm 'x (Imm 'r U)` is not checked.

## Files

| file | content |
|---|---|
| `Nominal/Atoms.lean` | `Atom`, the ancestor order, `Lft`, `fresh`, `swap`, `swapIso`, `swapLft`, `exists_lt_all`, `freshChild_lt_iff` |
| `Nominal/Carrier.lean` | `Above`, `Cell`, `Cell_eq`, `isCarrier`, `carrier_iff`, the union, `ext_data`, `boxS`, `boxE` |
| `Nominal/Action.lean` | `relC`, `relU`, `relRU`, `img`; data moved; `relU_symm_relU`, `img_eq`, `relU_mutOf` |
| `Nominal/Model.lean` | `●`, `○`, the walks, `⦇ρ⦈`, `✓`, `⟦ρ⟧`, `#`, `↭`, `⋆`, `─⋆`, `wpN` |
| `Nominal/ModelEquiv.lean` | every operation carried and invariant; `wpN_relRU_iff` |
| `Nominal/Relation.lean` | `LSubN`, `interpN`, `LtLifeN`, `ModelsN`, `ptoMutN`, `ptoImmN`, `vN`, `cN`, `SemN` |
| `Nominal/Equivariance.lean` | `vN_map`, `cN_map`, `semN_map_iff` |
| `Nominal/Records.lean` | `FrameRecN`, `SRecN`, `ChainN`, `RelN`, `ExtN`, `CohEN`, `TyEqN`; the action on records; `extN_act_iff`, `cohEN_act_iff` |
| `Nominal/CoreRelation.lean` | `WpOpN`, `ptoMutR`, `ptoImmR`, `vR`, `cR`; `vR_map`, `cR_map`; `wpLift`, `wpLift_equiv` |
| `Nominal/CoreWitnesses.lean` | `reopenR`; `kUR_convention` |
| `Nominal/TypedWorld.lean` | `vShapeN`, `ResU.Reb`, the lineage, `TWN`, `TaggedN`, `wpTSN` |
| `Nominal/TypedWorldEquiv.lean` | `TWN_act`, `taggedN_act_iff`, `wpTSN_equiv`, `vR_map_wpTS` |
| `Nominal/CoreWitnessesTW.lean` | `reopenR_wpTS`, `tw_mm`, `kUW_convention` |
| `Nominal/Facts.lean` | small resources, walks of one cell, `valid_mut_mut`, `valid_imm_imm`, `OwnOnly`, the readings on a chain |
| `Nominal/Package.lean` | `Pkg`, `reopen`, `reopen_iff`, `reopen_swap`, `reopen_fresh`, `exists_iff_forall_fresh` |
| `Nominal/Witnesses.lean` | `kU_convention`, `kV_*`, `kI_related_none`, the scheduler, `move_eq_remake`, `genPkg_reopen`, `split_is_real` |
| `scripts/Axioms.lean` | every declaration's axioms |
