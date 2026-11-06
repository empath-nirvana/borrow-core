# #791: location typing per lend, for step 7 of `withbor3_compatX` on the chain

Branch `rule-791`. The world is in the library (`Core/Chain/SI/LocTy.lean`); the interpretation
over it is `Core/Chain/Goal791N.lean`; `Core/Chain/LocTypeSketch.lean` keeps L2 (c)'s
configuration. Background: `scope-791-rule.md` §7. State after #825 (U1, U2): §9; after #826 (U3):
§10.

Kernel target: the location typing the chain's semantic interpretation reads, so that step 7 of
Core's `withbor3_compatX` (`Core/Compatibility.lean:1151`; inside it `Core/FrameRules.lean:620`,
`ptoMutX_write (Q := Qs)`) has a chain counterpart: the anti-frame's reseal of the returned content
into the cell's own entry.

## 1. The problem

Core's anti-frame writes the returned content back into the cell's unchanged stored predicate
`Qs`. On the chain the stored predicate is a member `F j` of a family and the content comes back
in the lower member `F k`, so the reseal is a predicate change. `↭` admits that change only where
the location typing types the cell (`PredStep`, `hF : Φ ℓ = some ⟨β, F⟩` in `erwp_M_antiFrame`),
and the interpretation never gives `Φ ℓ`: at `Φ ℓ = none` no `MutStep` reseals
(`Shape791N.reseal_untyped`). Reading `Φ ℓ` in the `Mut` clause per location fails at a reborrow,
whose `Φ.set ℓ α Fi` overwrites the source's entry (`Shape791N.coreShape_not_reborrow`).

## 2. The proposed definition

### 2.1 The world: keyed by location and lend lifetime

```
LocTy ≜ (ℓ : Loc) → (b : Life) → Option (Nat → Val → SPropS Loc Val b)      -- SI/LocTy.lean
```

`Θ ℓ b` is the payload family of the `mut` cell lent at `ℓ` at `b`. The key is the lend, as in
Core, where a record is `SRec = FrameRec × Life` (`Core/FrameRecords.lean:159`), one per lend.

- **A lend** at `(ℓ, α)` is `Θ.add ℓ α F`. It replaces `Φ.set`, and every other key is
  kept (`add_keep`). The source's `(ℓ, β)` is one of the kept keys.
- **Freshness.** A lend's lifetime is chosen strictly shorter-lived than every key present
  (`LocTy.Fresh`). Such a lifetime exists below any bound when `Θ` is bounded
  (`exists_fresh`), and a lend keeps `Θ` bounded (`fresh_add`). Every chain lend already
  chooses its lifetime (`ResU.exists_stratum`, `Life.down` in `withbor2S_compat`), and shorter
  is always admissible: `Res_α` and `Res_{↓α}` grow, and `MFPost`'s `ρ′ ∈ Res_α` gets weaker.
- **Stratified families.** The family stored at `(ℓ, a)` reads the world only above `a`
  (`famL a P Θ = P (Θ.above a)`). That is Core's `ls₀` in `ptoMutS`
  (`Core/Relation.lean:44`): the records strictly longer-lived than the cell. A fresh lend adds
  nothing above any key present (`above_add`). So a family stored at a lend stays the
  payload's family read at the current world (`fam_add_self`), and no recursive world is needed.
  The lifetime is the stratum, as the level is in AAV 2002 (§7).
- **The Kripke order** is `LocTy.ExtA`: entries are only added, and nothing is added
  above a key present. A fresh lend is one step of it (`extA_add`), and it is transitive
  (`extA_trans`).

### 2.2 How the relation reads it: the view

The relation keeps its per-location `LocFam`. At a run, each location's live `mut` cell sits at a
single lifetime `c ℓ`, and the run is at the **view**:

```
Θ.view c ℓ ≜ (Θ ℓ b).map ⟨b, ·⟩   where c ℓ = some b;   none where c ℓ = none
```

- `Φ.set` at a lend is the view of `Θ.add`: `(Θ.add ℓ α F).view (c[ℓ ↦ α]) = (Θ.view c).set ℓ α F`
  (`view_add`). So `rwp_M_frame`, `erwp_M_frameF`, `erwp_withbor3` and the other lend
  frames, all stated at `Φ.set`, are already this design's lends, seen from their run.
- **`PredStep`/`MutStep`/`UpdN`/`EndOKG`/`rwpG`/`erwp` are unchanged.** They read
  `Θ.view c ℓ`, which is `Θ ℓ (c ℓ)`. A consistent view (below) gives each cell its own lifetime,
  so `PredStep` at a cell at `b` reads the entry `(ℓ, b)`, its lend's.
- **Consistency.** `ConsistentX c ρ`: every `mut` cell of `ρ`'s *exclusive walk* `ex(ρ)` is at
  `c ℓ` (`SI/LocTy.lean`). A run keeps it on the resource it returns (`erwp_consistent`), a
  composite has it when its operands do (`consistentX_compS`), an operand when the composite does
  (`consistentX_left`), and a held `mut` cell is at its view lifetime (`consistentX_get`, the
  anti-frame's `c ℓ = β`). The first reading, `Consistent c ρ` over the whole flattening, is kept
  by `↭` on the whole resource (`consistent_of_updN`) and not by the part a run returns (§9,
  `flat_part_config`).
- `Θ.Down → (Θ.view c).Down` (`view_down`).

### 2.3 The interpretation's clauses

- **`Mut @a A`** is Core's shape (`mutL`): a location whose cell at `a = @aδ` holds the
  member `j ≥ k` of `famL a 𝒱⟦A⟧ Θ`, together with `Θ ℓ a = some (famL a 𝒱⟦A⟧ Θ)`.
- **`U C`**: `C` at every extension `Θ′` along `LocTy.ExtR Θ Θ′ ρ` (`ρ` the thunk's resource;
  §10) with `Θ′.OK` and every view `c′` consistent with the thunk's resource. `vThunk` with
  `Covers` has the right idea but the wrong strength: it asks for some family, where consistency
  plus the `Mut` clause name the payload's family.
- **`⊸`** quantifies over extensions `Θ′` along `ExtR` at the function's resource (`OK`) and views
  `c′` consistent with the argument's and the function's composite; **`SemJN`** over worlds `Θ`
  with `Θ.OK` and views consistent with the context's resource. The relation's `Φ` is
  `Θ.view c`.
- **`F A`, `F_Σ R`, `tabN`, `finN`** are `erwp` at `Θ.view c`, as now at `Φ`.

## 3. The lemmas the port needs

The "not built" entries are as scoped; §9 has what #825 built.

All proved results below are in `Core/Chain/SI/LocTy.lean` (L2 (c) in
`Core/Chain/LocTypeSketch.lean`), registered in `Core/Chain.lean` and in `scripts/AxiomCheck.lean`. Axioms are within `propext`, `Classical.choice`, `Quot.sound`.

**(L1) The anti-frame's reseal at the original entry. Proved.**

- `reseal_at_entry`. Take `Θ.Ext Θ′`, `c ℓ = some β`, `DownFam β (famL β P Θ)`, and
  `mutL β P Θ n (loc ℓ) ρ`. Then `ρ = ℓ ↦ mut(β, w, χ, famL β P Θ j)` with `n ≤ j`, and
  `Θ′.view c ℓ = some ⟨β, famL β P Θ⟩` (the anti-frame's `hF`, at `Θ` and at the reborrow's
  world). For every `m ≤ k` and every content `(w′, σ′) ∈ famL β P Θ k`, the reseal
  `mut(…, F j) → mut(β, w′, σ′, F k)` is a `MutStep` at `Θ′.view c` at `m`. The resealed cell is
  again `mutL β P Θ k (loc ℓ)`. That is Core's step 13: the cell is a `Mut` value again.
- `erwp_antiFrame_view` is the existing `erwp_M_antiFrame` (`SI/AntiStopN.lean:257`)
  applied at `Θ.view c`, with `hF` supplied by the `Mut` value. Nothing in the relation changes.
- `reborrow_view`: for a fresh `α`, `Θ.Ext (Θ.add ℓ α Fi)`, `Θ.add ℓ α Fi ℓ β = Θ ℓ β`,
  and the reborrow world's view is `(Θ.view c).set ℓ α Fi`, the typing `erwp_withbor3` runs its
  callback at.

**(L2) A reborrow adds an entry and keeps what was typed. Proved.**

- `ext_add`: a fresh lend is an extension. `add_keep`: the source's entry is kept.
- `mutL_add`: for every payload `P`, a `mutL a P` value at `Θ` is one at `Θ.add ℓ₀ α F`
  for fresh `α`.
- `mutL_extA`: `Mut` values are stable along the Kripke order `ExtA`.
- `coreShapeL_reborrow`: `coreShape_not_reborrow`'s own configuration, per lend. With
  `ℓ_b ≠ ℓ, ℓ₂` and `α < b < β`, the value `Mut @b (Mut @β 1)` at `ℓ_b` (holding nothing at `ℓ`)
  is one of Core's shape at `Wc` and at `Wc.add ℓ α F`, for every `F`. Per location it is not
  (`Shape791N`). Every hypothesis is discharged; `Wc_fresh` shows `α` is fresh there.

**(L3) What steps 4, 6, 8, 11 and 13 read besides.**

| Step | Needs | State |
|---|---|---|
| 4 (`vC_local`) | a value at the lend's world, in the lend's stratum, is one at the world without it | `mutL_of_add`, proved at `Mut`; `vN_local` at every type: **not built** |
| 4, 11 (`U` along `Ext`) | `vN` stable along `ExtA` | at `Mut`: `mutL_extA`; at every type (`vN_extA`): **not built** |
| 6 (`hunif`) | `𝒱⟦T₁⟧ ⊆ Res_β` from `Δ ⊢ T₁ ⊒ @a` | `vN_outlives` exists (`Goal791N`); the conjunct in the `Mut` clause: **not built** |
| 7 | L1 | proved |
| 8 (`MutFrame` at the fresh `α`) | the lend's borrow is a value at the new world; the view is `Φ.set` | `lend_mutL`, `fam_add_self`, `view_add`, proved; anti-frame across layered cancel runs (`erwp_M_antiFrameC` at `tabR`): **not built** (as `scope-791-rule.md` §7.1, unchanged by this design) |
| 9 (fresh lifetime) | a fresh `α` below `⊓Δδ` and the content's stratum | `exists_fresh`, `fresh_add`, proved; `Θ.Bounded` must be a premise of `ConstN`/`SemJN` |
| 11 (callback at the reborrow) | `Θ.ExtA (Θ.add ℓ α Fi)` and the callback's view consistent | `extA_add`, proved; consistency of `c[ℓ ↦ α]` with the callback's resource: **not built** |
| all | a run from a consistent resource ends with the returned resource consistent | `consistent_of_updN` covers `π`; that the returned `ρ′ ⊆ π` keeps its flat `mut` cells' lifetimes (`FlatAt` of a `CompS` part): **not built** |

## 4. Blast radius

Counts are from `git grep` on this branch. 56 files under `Core/` mention `LocFam`, and 59 files
under `Core/Chain/` mention `Φ` (2219 occurrences). `PredStep`/`MutStep`/`UpdMutN` appear in 9
files, 39 of their uses in `SI/UpdN.lean`. Typed lookups `… = some ⟨…⟩` appear in 18 files,
about 31 sites. `Φ.set` appears in 20 files, about 100 sites.

**With the view (recommended): the relation is untouched.**

| Module | Reads | Change |
|---|---|---|
| `SI/*` (all of them, the relation and its frames) | `LocFam` as a parameter | none: not restated, not re-proved. `erwp_M_antiFrame`, `erwp_withbor3`, `erwp_M_frameF`, `rwp_M_frame` are used as they stand. |
| `PoolN` (400), `PoolSpawnN` (462) | relation only (0 uses of the interpretation) | none |
| `Hardest791N` (1073) | relation only (0 uses of `vN`/`cN`; 12 `Φ.set`) | none. **`hardestCase791` and `hardestCase791C` survive unchanged.** |
| `Goal791N` (681; 79 uses) | defines `vN`/`cN`/`tabN`/`finN`/`SemJN`/`ConstN`/… | **restated**: the world `Θ` and a view replace `Φ`; `Mut` takes Core's shape; `U` is Kripke along `ExtA`. The laws (`vN_down`, `cN_down`, `vN_congr`, `cN_extΦ` → along `ExtA`, `vN_outlives`, `bridgeN`, `goal791Sched_of`) are re-proved, mostly mechanically. `vN_extA` and `vN_local` are new. Most of the file is touched. |
| `Lend791N` (361; 17 uses) | `tabN_*`, `cbRelease_sem`, `answer_not_inStratum` | restated at `Θ` and re-proved mechanically. `erwp_M_frameCR`, `rwp_mono_le` and `rwp_of_erwp_empty` (relation-level) are unchanged. |
| `Cancel791N` (729; 59 uses) | `tabR`/`finR` and the `tabN` twins, `withbor2S_compat`, `constN_w2` | `withbor2S_compat`/`constN_w2` restated (`ConstN` changes), re-proved with the lend at a fresh `α` and `view_add`. Lemmas over `tabR`/`tabN` get the world argument and are re-proved mechanically. `erwp_M_frame_cancelRunCR`, `erwp_ubind_cancelRunCR` and `erwp_ubindClaimRT` take the table as a parameter and are unchanged. **The `Cancel791N` results survive**: the relation-level ones as they are, `withbor2S_compat`/`constN_w2` re-proved at the new interpretation. |
| `Shape791N` (281) | `reseal_untyped` reads `vN` | restated at the new `vN` (its content, `Φ ℓ = none` forcing the predicate, is unchanged). `coreShape_not_reborrow` uses its own `mutC` and is unchanged. |

Roughly 1,800 lines restated or re-proved, all of them interpretation-level.

**With the key moved into the relation (fallback, §5 E).** `PredStep` takes the cell's lifetime,
and `LocFam` becomes `LocTy` throughout. Every one of the 56 `LocFam` files re-elaborates. The
roughly 31 typed lookups and roughly 100 `Φ.set` sites are rewritten. `UpdN.lean`'s
`PredStep`/`MutStep` lemmas are restated, and `six28N`/`updVN_frame` re-proved. Statements change
only in the type of `Φ` and the lookup form; most proofs pass `Φ` through.
`hardestCase791`/`hardestCase791C` are re-proved (19 `Φ.set`, 3 lookups). Order of magnitude:
every `SI` module touched, most mechanically.

## 5. The alternatives compared

- **A. Per-lend keys, read through the view (recommended).** It closes step 7 by L1, with the
  existing anti-frame. It answers `coreShape_not_reborrow` by L2. It needs no recursive world,
  because of the lifetime stratification and freshness, and it leaves the one relation alone
  (structure.md §3). It costs a world, a view and a consistency invariant in the interpretation
  (§3, L3 rows not built).
- **B. Later-guarded cell predicates (Iris).** In Iris an invariant stores a fixed `P` under `▷`;
  the step index is the ambient uniform predicate's, so closing at a lower index re-proves `▷P`
  and changes nothing stored. On the chain the counterpart is a cell storing its family, not a
  member, with `↭`'s `mut` clause fixing that family. The resealed content is then read at the
  index left, which makes the reseal Core's `ptoMutX_write (Q := Qs)` exactly.
  - Cost: `CellU`'s predicate type, `ResU` composition and validity, flattening and `Lower` all
    change, in `Paper`/`Support`'s model, under every `SI` module and the transcription. That is
    a model change, not a relation change, and far larger than A or E.
  - It does not answer `coreShape_not_reborrow` by itself. Iris answers that by naming
    invariants per allocation (fresh `ι`), which is A's key. The `▷` resolves the recursion of
    `P` mentioning invariants, which the lifetime stratification already resolves here.
  - Not recommended.
- **C. Top-level typing over a `Φ`-free content semantics** (`scope-791-rule.md` route C). `Mut`
  reads `Φ ℓ = (a, 𝒱⟦A⟧)` with `𝒱` `Φ`-free inside cells. It closes step 7 for `w3`'s argument.
  A `Mut` read out of a cell or a `Ref` is untyped, so it cannot be opened again: the fundamental
  property loses load of a `Ref (Mut …)`, swap, and the inner borrow of `Mut @β (Mut @γ X)`.
  structure.md §11 forbids a restriction not shown to lose nothing. Not recommended.
- **D. A named assertion of the reseal.** The user ruled it out.
- **E. Per-lend keys inside the relation** (`PredStep Θ n ℓ ψ.at`). This is A without the view.
  It needs no consistency invariant, because the cell's own lifetime selects the entry. Its blast
  radius is §4's second paragraph. It is the fallback if the view's consistency fails (kill
  criterion K3).

**Recommendation: A.** The evidence:

- L1 is proved, and its relation half is the existing `erwp_M_antiFrame`.
- L2 is proved at every payload (`mutL_add`, `mutL_extA`), including the configuration that
  defeats the per-location typing.
- `Φ.set` is the view of the per-lend lend (`view_add`), so no relation lemma is restated.

## 6. Build plan

Each unit lands on the PR branch; the order is the list order.

1. **U1: the world in the library** (`Core/Chain/SI/LocTy.lean`, the sketch's definitions
   promoted).
   - Done when: `LocTy`, `add`, `above`, `Fresh`/`Bounded`, `ExtA`, `view`, `Consistent` are
     defined.
   - `view_add`, `extA_add`/`extA_trans`, `exists_fresh`/`fresh_add` are proved.
   - `erwp_consistent` is proved: a run at `Θ.view c` from a resource consistent with `c` meets
     its postcondition at a resource consistent with `c`. This covers the returned part of `π`,
     the missing L3 row.
2. **U2: the interpretation over `Θ`** (`Goal791N` restated).
   - Done when: `vN` with `Mut` in Core's shape, `U` Kripke along `ExtA` at consistent views, and
     `⊸`/`SemJN` at consistent views are defined.
   - `vN_down`, `vN_extA`, `vN_local` (along a fresh lend, values in its stratum), `cN_extA`,
     `vN_congr`, `vN_outlives`, `bridgeN` and `goal791Sched_of` are proved, as today's laws.
3. **U3: `w2` on the new interpretation.**
   - Done when: `withbor2S_compat` holds with today's premises, the lend at a fresh `α`
     (`exists_fresh`) and the callback at `Θ.add` (`view_add`), and so does `constN_w2`.
4. **U4: `w3`, the hardest case, kept in.**
   - Done when: `withbor3S_compat`/`constN_w3 : FundamentalN → ConstN (.w3 …)` holds with only
     the typing rule's premises, by Core's 13 steps.
   - Step 7 is `erwp_antiFrame_view`; step 6 is the `hunif` conjunct; step 8 is the anti-frame
     across layered cancel runs (`erwp_M_antiFrameC` at `tabR`, built in this unit).
5. **U5: `wF`.**
   - Done when: `constN_wF` holds with only its rule's premises. `wl` waits on the `Imm`
     records/`CohE` decision (`scope-791-rule.md` §5) and is not in this plan.

**Kill criteria** (each is a Lean configuration, not a failed proof attempt):

- **K1.** A `Mut` argument at a consistent view that `erwp_antiFrame_view` cannot open: a
  consistent `c` with `c ℓ ≠` the argument's lifetime. This would mean the view is the wrong
  bridge, and E is the route.
- **K2.** A `U C` value valid at `Θ` and not at a fresh extension: `vN_extA` false at `U`. This
  would mean `ExtA` is the wrong order, and Core's resource-relative `Ext` is needed (open
  question 1).
- **K3.** A run from a consistent resource whose returned resource has a flat `mut` cell at a
  lifetime other than `c ℓ`. This would mean `erwp_consistent` is false and the view cannot
  carry the typing; E is the route.
- **K4.** A `mut` lend whose rule fixes its lifetime, so that no fresh `α` is admissible. This
  would mean freshness is wrong, the key must be a lend name, and the design is reopened.

## 7. Literature, and the mechanism taken from each

- **Ahmed, *Semantics of Types for Mutable State*** (PhD thesis, Princeton 2004). The
  step-indexed store typing `Ψ` as a Kripke world: a location's type, approximated to the index,
  fixed for the location's life; worlds only extended, at fresh locations. Taken: the world is
  extended only at fresh keys, and an entry's family never changes. The key differs: in ML a
  location is allocated once, so per location is per allocation. In BoLo a location is lent many
  times, and the allocation unit is the lend, so the key is `(ℓ, lifetime of the lend)`.
- **Ahmed, Appel, Virga, "A Stratified Semantics of General References Embeddable in Higher-Order
  Logic"** (LICS 2002). Store typings stratified by level: a type at one level reads only store
  typings over types of lower level, which breaks the circularity without a recursive world.
  Taken: `famL a P Θ` reads `Θ` only strictly above `a`, with the lifetime as the level. My
  reading of the paper's exact formulation is from memory and is not checked here.
- **Birkedal, Reus, Schwinghammer, Støvring, Thamsborg, Yang, "Step-indexed Kripke models over
  recursive worlds"** (POPL 2011). Worlds as the solution of a recursive equation in ultrametric
  spaces, `W ≅ Loc ⇀_fin (½·W → UPred(Val))`: entries are world-dependent and the contraction
  makes them well defined. Taken: the finiteness of worlds, as `Bounded`/`Fresh`. Not taken: the
  contraction. The stratification gives well-definedness instead, which is why the sketch's
  entries are fixed functions.
- **Iris: the later modality and invariants** (Jung, Krebbers, Jourdan, Bizjak, Birkedal, Dreyer,
  JFP 2018). Invariants are allocated under fresh names in a world that only grows, with contents
  stored as `ag(next P)`, opened to `▷P` and closed by re-establishing `▷P`. Taken: per-allocation
  naming (A's key). The `▷` closing rule is alternative B (§5), not taken.
- **Core's records** (`Core/FrameRecords.lean:159`, `:172`; `Core/Relation.lean:44`):
  - `SRec = FrameRec × Life` is one record per lend.
  - `ptoMutS` stores `P ls₀`, with `ls₀` the records strictly longer-lived than the cell.
  - `Ext ls ls′ ρ` keeps exactly the records above every borrow of `ρ`.
  - Taken: the key, the "read above the cell" stratification (`famL`), and `ExtA` as the
    world-relative form of `Ext`.

## 8. Open questions, and their answers (#825)

1. **`U`'s order: world-relative `ExtA` or Core's resource-relative `Ext`.** *Answer: `ExtA`
   cannot be `U`'s order if locality (`vC_local`, step 4) is to hold at `U`; that is Core's
   resource-relative `Ext`.* Kill criterion K2 as written (a `U C` value valid at a world and not
   at a fresh extension) is not met: `U` is Kripke along `ExtA` and `ExtA` is transitive, so
   `vN_extA` holds at `U` and at every other former. Locality fails at `U`
   (`Core/Chain/LocalU791.lean`, `u_not_local`, every hypothesis discharged): the thunk
   `λx. () ()` of type `U(Mut @b 1 ⊸ F 1)`, holding nothing, is valid at `∅ + (ℓ, α) ↦ F` with
   `α < b`, because no `ExtA`-extension of that world adds a key above `α`, so no `Mut @b 1`
   argument exists (`thunk_at_lend`); it is not valid at `∅`, whose extension
   `∅ + (ℓ′, b) ↦ 𝒱⟦1⟧` holds the argument `ℓ′ ↦ mut(b, (), ∅, 𝒱⟦1⟧)`, on which the thunk is
   stuck (`thunk_not_at_empty`). Under Core's `Ext ls ls′ ρ`, which constrains only the records
   above the borrows of `ρ` (none, at `∅`), this thunk is not a value at the lend's world either.
   Changing `U`'s order is a design change: **decision for the user**. *Decided (#826): Core's
   resource-relative order, §10.* `LocalU791.lean` is removed with the `ExtA` clause; the
   configuration is at commit `728b51d7`.
2. **`erwp_consistent`.** *Answer: holds, on the exclusive walk.* `erwp_consistent`
   (`SI/LocTy.lean`): a run at any `LocFam` from a resource with `ConsistentX c` returns, at every
   value or stop it reaches, a resource with `ConsistentX c`. The proof follows a returned
   exclusive `mut` cell into the post-configuration's flattening, back across `↭` by `UpdMutN`'s
   second clause, and, where `↭` finds it in the aliasable walk, to its `imm` ancestor
   (`AgW.nonimm_beneath_imm`), which `↭` keeps (`upd_ag_imm_wit_factorI`, the `imm` clause
   alone): the ancestor puts the location in the post-configuration's aliasable walk, where the
   exclusive cell cannot be. *On the whole flattening it does not hold of the returned part*
   (`Core/Chain/ConsistentFlat791.lean`, `flat_part_config`): `ρ′ = m ↦ imm(t, (), ℓ ↦ mut(a, …))`
   and `ρp = ℓ ↦ imm(s, (), ∅)`; in `ρ = ρ′ ● ρp` the two meet at `ℓ` as `mut ○ imm = imm`
   (`CellU.CompR.mutImm`), so `⦇ρ⦈` has no `mut` cell and the empty view is consistent with it;
   `⦇ρ′⦈` has `ℓ ↦ mut(a, …)`. `ρ ↭ ρ`, `ρp` owns nothing, and the zero-step run of `()` from `ρ`
   returning `ρ′` is an `erwp` run (`erwp_val_split`). This is K3's configuration for the first
   reading; a frame (`TWNC`) at which `ρ` is a run's start is not built (it is an `imm` frame of a
   `Mut` value with an `imm` reborrow of the borrowed cell). The exclusive-walk reading is what
   the anti-frame needs (a held `Mut` argument is a top-level cell, `consistentX_get`), and is the
   one the interpretation uses. The change of reading is recorded here for the user to confirm.
3. **`Θ.Bounded` as a premise.** *Answer: it is a premise, of every world the interpretation is
   read at, and nothing upstream supplies an unbounded world.* `LocTy.OK Θ = Θ.Down ∧ Θ.Bounded`
   is a premise of `SemJN` and `ConstN`, and `U` and `⊸` quantify only `OK` extensions (`ExtA`
   adds keys freely, so boundedness is asked at each extension rather than carried by the
   order). `BridgeN` quantifies `OK` worlds and `bridgeN` uses the empty one (`LocTy.empty_ok`);
   `Goal791SchedN` takes `Θ.OK` as a premise. `PoolN`/`PoolSpawnN` (`poolSchedAdequacyN`) are
   relation-level, at any `LocFam`, and read no world. A lend keeps a world bounded
   (`LocTy.fresh_add`).
4. **`Imm`** (`wl`) reads `CohE` and records. Not addressed: the `Imm` payload is read at `Θ`
   (`vN`'s `imm` clause), and `PredStep` does not read `imm` cells.

Unspent: `DownFam β (famL β P Θ)` in `reseal_at_entry` is supplied in the port by `vN_fam_down`.
The uniqueness result used is `UpdMutN`'s lifetime agreement (`MutStep`'s `ψ.at = ψ′.at`), in
`consistent_of_updN` and `consistentX_of_updN`; the functionality results used are
`ExS.functional`, `ExR.functional`, `AgW.functional`, `ResU.CompR.functional`. Not used:
`vThunk`/`Covers`, which consistency replaces.

## 9. State after #825 (U1, U2)

All in `scripts/AxiomCheck.lean`; axioms within `propext`, `Classical.choice`, `Quot.sound`.

**U1, the world in the library** (`Core/Chain/SI/LocTy.lean`): `LocTy`, `LocTy.add`, `.above`,
`.Fresh`, `.Bounded`, `.OK`, `.ExtA`, `.view`, `.empty`; `famL`, `mutL`; `ConsistentX` (and
`Consistent`); `LocTy.view_add`, `LocTy.extA_add`, `LocTy.extA_trans`, `LocTy.exists_fresh`,
`LocTy.fresh_add`, `LocTy.view_ext`, `LocTy.view_empty`; L1 `reseal_at_entry`,
`erwp_antiFrame_view`, `reborrow_view`; L2 `mutL_add`, `mutL_extA`, `mutL_of_add`,
`fam_add_self`, `lend_mutL`; `consistentX_of_updN`, `rwpG_consistentX`, `rwp_consistentXV`,
`erwp_consistent`, `consistentX_compS`, `consistentX_left`/`_right`, `consistentX_get`.

**U2, the interpretation over the world** (`Core/Chain/Goal791N.lean`): `vN`, `cN`, `tabN`,
`finN`, `retN`, `gN`, `SemJN`, `rowTabN`, `ConstN`, `BridgeN`, `Goal791SchedN` restated at
`(Θ, c)`.

| Law | Proved at | Left out, and why |
|---|---|---|
| `vN_down`, `cN_down`, `tabN_down`, `finN_down`, `retN_down` | every former | — |
| `vN_extA` | every former | — |
| `cN_extA` | `F A`, `⊸`, `&`, `⊤`, `∀`, `ν` (`noEffSpine`) | `F_Σ R`: the continuation was proved to accept the table's answers at `Θ`, and the table at `Θ′` hands them back at `Θ′`. I have not derived a counterexample and have not verified that any obstruction is real. |
| `vN_local` (along a lend at `α`, resource in `Res_α`) | every former but `U` (`uFree`) | `U`: false under `ExtA`, `u_not_local` (§8 Q1) |
| `vN_outlives` | every former `VOutlives` has | — |
| `vN_congr`/`cN_congr`, `cN_effOf`, `vN_fam_down` | every former | — |
| `bridgeN`, `goal791Sched_of` | re-proved | — |

`Lend791N` restated: `tabN_effOf_some`, `tabN_effOf_twin` (now at one world, two views),
`tabN_lendOKCR`, `fin_claim` (at `Θ.view c`, from the claim's consistency, through
`rwp_consistentXV`), `cbRelease_sem`, `answer_not_inStratum`; `suspend_closingOp` moved there.
`Shape791N.reseal_untyped` is restated at the per-location `Mut` clause it is about
(`mutCellPL`). Unchanged: `hardestCase791`/`hardestCase791C`, `poolSchedAdequacyN`,
`erwp_adequacy`, and every relation definition.

**Out of the build until #826:** `Core/Chain/Cancel791N.lean` (`withbor2S_compat`, `constN_w2`,
`tabR`/`finR`, `erwp_M_frame_cancelRunCR`, `erwp_ubind_cancelRunCR`, `erwp_ubindClaimRT`), whose
statements read the interpretation before the world; the source is kept and its import is
commented in `Core/Chain.lean`.

**What #826 (U3) needs from this:**
- the callback runs at `Θ.add ℓ α (famL α 𝒱⟦A⟧ Θ)` and the view `setLife c ℓ α`, which is
  `(Θ.view c).set ℓ α _` (`LocTy.view_add`), with `α` fresh below the bound (`LocTy.exists_fresh`,
  from `Θ.OK`) and the extended world `OK` (`LocTy.down_add`, `LocTy.fresh_add`); the callback's
  `Mut @α` argument is `lend_mutL`, and its view is consistent with the argument and the context
  (`consistentX_compS`, with `setLife` at `ℓ`);
- the lender's and the callback's tables are at different worlds, so `tabN_effOf_twin` (one world)
  does not apply as it stands: their entries' `PA`/`PB` differ (`vN o.A δ Θ` against
  `vN o.A δ (Θ.add …)`). Where the operation types are in the lend's stratum, `vN_local` and
  `vN_extA` relate them, except at `U` (§8 Q1);
- the callback's result `[@x] B` returned to the lender at `Θ` needs `vN_local`, which is open at
  `U` (Q1): the decision on `U`'s order comes first;
- `withbor2S_compat`'s premises otherwise as today.

## 10. State after #826 (U3)

All in `scripts/AxiomCheck.lean`; axioms within `propext`, `Classical.choice`, `Quot.sound`. No
relation definition changed (`erwp`, `rwpG`, `EndOKG`, `UpdN`, `PredStep`, `MutStep`, `LocFam`).

**`U` and `⊸` along Core's resource-relative order** (`SI/LocTy.lean`):

```
LocTy.ExtR Θ Θ′ ρ ≜ ∀ ℓ a F, Θ ℓ a = some F → CellIn ρ a → Θ′ ℓ a = some F ∧ Θ′.above a = Θ.above a
```

`CellIn ρ a` is Core's (`Core/FrameRecords.lean`): a borrow cell of `ρ` no longer-lived than `a`.
It is Core's `Ext ls ls′ ρ` read on the per-lend world: the keys a value with resource `ρ` reads
(its cells' keys, and the keys above them that their families read) are kept, and nothing is
added above them. Two differences from Core's clause, both from the world's shape:

- the key at a `mut` cell's own lifetime is kept (`CellIn` is `⊑`). Core's cell stores its
  predicate; here the `Mut` clause reads it at the key (`mutL`);
- agreement is asked only above the lifetimes of keys present, not above every `b` with
  `CellIn ρ b`. A key may be added above a borrow cell of `ρ` and below every relevant key.
  This is what makes `ExtA` an `ExtR` at every resource (`LocTy.ExtA.extR`). I have not built a
  configuration showing that agreement above every such `b` would break `vN_extA` at `U`.

Laws: `extR_refl`, `ExtR.trans`, `ExtR.left`/`right`/`mono`, `ExtA.extR`; `extR_of_add` (the
world without a lend at `α` is an extension at a resource in `Res_α`; Core's `ext_drop`);
`extR_above`; `mutL_extR`.

**The interpretation** (`Goal791N.lean`): `vN`'s `U` clause and `cN`'s `⊸` clause read `ExtR` at
the thunk's or function's resource. Laws:

| Law | Proved at | Notes |
|---|---|---|
| `vN_extR` | every former | Core's `vC_local`; one structural recursion, no `cN` case |
| `vN_extA` | every former | from `vN_extR` and `ExtA.extR` |
| `vN_local` | every former, `U` included | from `vN_extR` and `extR_of_add`; `uFree` is gone |
| `cN_extA` | as before (`noEffSpine`) | `⊸` by `ExtA.extR` and `ExtR.trans`; `F_Σ R` below |
| `vN_down`, `cN_down`, `vN_congr`, `vN_outlives`, `cN_effOf` | unchanged | |
| `bridgeN`, `goal791Sched_of` | re-checked | unchanged proofs |

New: `vN_top` (a type outliving every lifetime has values in the top stratum), `vN_add_eq` (such a
type's `𝒱⟦·⟧` is the same at the world with a fresh lend), `vN_above` (a stored family is the
payload at the world on content in the cell's stratum).

**Consistency** (`SI/LocTy.lean`): `consistentX_setLife`, `exS_none_of_part`,
`consistentX_single_mut`, `consistentX_of_top` (a resource in the top stratum is consistent with
every view: an operation's answer, when the row's types outlive every lifetime).

**`withbor2S_compat`, `constN_w2`** (`Cancel791N.lean`, back in the build): the lend at `α` fresh
for `Θ` (`exists_fresh` from `Θ.OK`) and below the bound, `σ₀`'s stratum and the callback's; the
callback at `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ` (`OK` by `down_add`, `fresh_add`) and the view
`setLife c ℓ α`, the relation's `Φ.set` (`view_add`); its argument `lend_mutL`, consistent by
`consistentX_compS`, `consistentX_single_mut` and `consistentX_setLife` (the source's parts miss
`ℓ` in their exclusive walks, `exS_none_of_part`, from the start's validity, `erwp_of_valid`). The
callback's result returns to `Θ` by `vN_local`; the content handed back by `vN_above`.
Premises: `withbor2U`'s with `Row.Suspend` (`hA`, `hB`, `hS`, `hdc`) and `hd`, `d`'s semantic
judgment. No `hSF`, no `hSB`.

- `tabR`/`finR` take the world and view; `tab_lookupN`/`tab_lookupR`, `tabR_tabN_twin`,
  `tabR_tabR_twin`, `tabN_lendOKCR_C` restated. `tabN_tabR_twin` relates the callback's table at
  `Θ + (ℓ, α)` and the lender's at `Θ` (`hΘ`, supplied by `vN_add_eq` from `CTy.SuspendC`'s
  outliving clauses): the generalisation of `tabN_effOf_twin` across the two worlds.
- `tabR_can` takes `Θ.Fresh α`; `erwp_M_frame_cancelRunCR`, `erwp_M_frameCR` unchanged.
  `erwp_ubind_cancelRunCR`, `erwp_ubindClaimRT`: the same proofs at `Φ = Θ.view c`, the tables
  at `(Θ, c)`.
- **The claim's consistency.** `fin_claim` runs `d ℓ` and applies `d`'s thunk at a view
  consistent with the claim, so the claim must be consistent with `c`. The relation-level frame
  lemmas do not carry consistency. `erwp_claimX`/`erwp_cancelRun_claimX` carry it: from a
  consistent start, a run's returned resources are consistent (`rwpG_consistentXV`), a stop's
  continuation resumes from its consistent share and an answer in the top stratum, a cancel run by
  the induction on cancel depth. The lender's table becomes `tabR (claimX Rc c)`.

**`cN_extA` at `F_Σ R`: not derived.** It needs each layer's answer, read at `Θ′`, to be one at
`Θ` (the continuation was proved to accept answers at `Θ`), and likewise for the cancel rows'
tables, which `ExtA` does not give in general. Where every answer type outlives every lifetime,
answers are in the top stratum and read no key, so `vN_extR` relates `Θ` and `Θ′` both ways; that
case additionally needs an `erwp` lemma over tables whose payloads grow and answers agree, not
built. I have not derived a counterexample at a general answer type and have not verified that any
obstruction is real.

**What #827 (U4, `w3`) needs from this:** the lend at a fresh `α` and the callback at
`Θ + (ℓ, α)` exactly as here; the source `Mut @a A` argument opened at `c ℓ = β`
(`consistentX_get`, then `erwp_antiFrame_view`/`reseal_at_entry`); its key `(ℓ, β)` kept by the
reborrow (`reborrow_view`); `erwp_claimX`'s consistency reasoning for the anti-frame's cancel runs;
step 8's anti-frame across layered cancel runs (`erwp_M_antiFrameC` at `tabR`), not built.
