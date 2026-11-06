# #791: location typing per lend, for step 7 of `withbor3_compatX` on the chain

Branch `rule-791`. Scope unit; the Lean is `Core/Chain/LocTypeSketch.lean` (standalone
definitions, no existing definition or theorem changed). Background: `scope-791-rule.md` §7.

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
LocTy ≜ (ℓ : Loc) → (b : Life) → Option (Nat → Val → SPropS Loc Val b)      -- LocTypeSketch.lean:67
```

`Θ ℓ b` is the payload family of the `mut` cell lent at `ℓ` at `b`. The key is the lend, as in
Core, where a record is `SRec = FrameRec × Life` (`Core/FrameRecords.lean:159`), one per lend.

- **A lend** at `(ℓ, α)` is `Θ.add ℓ α F` (`:79`). It replaces `Φ.set`, and every other key is
  kept (`add_keep`, `:90`). The source's `(ℓ, β)` is one of the kept keys.
- **Freshness.** A lend's lifetime is chosen strictly shorter-lived than every key present
  (`LocTy.Fresh`, `:76`). Such a lifetime exists below any bound when `Θ` is bounded
  (`exists_fresh`, `:144`), and a lend keeps `Θ` bounded (`fresh_add`). Every chain lend already
  chooses its lifetime (`ResU.exists_stratum`, `Life.down` in `withbor2S_compat`), and shorter
  is always admissible: `Res_α` and `Res_{↓α}` grow, and `MFPost`'s `ρ′ ∈ Res_α` gets weaker.
- **Stratified families.** The family stored at `(ℓ, a)` reads the world only above `a`
  (`famL a P Θ = P (Θ.above a)`, `:163`). That is Core's `ls₀` in `ptoMutS`
  (`Core/Relation.lean:44`): the records strictly longer-lived than the cell. A fresh lend adds
  nothing above any key present (`above_add`, `:111`). So a family stored at a lend stays the
  payload's family read at the current world (`fam_add_self`), and no recursive world is needed.
  The lifetime is the stratum, as the level is in AAV 2002 (§7).
- **The Kripke order** is `LocTy.ExtA` (`:197`): entries are only added, and nothing is added
  above a key present. A fresh lend is one step of it (`extA_add`), and it is transitive
  (`extA_trans`).

### 2.2 How the relation reads it: the view

The relation keeps its per-location `LocFam`. At a run, each location's live `mut` cell sits at a
single lifetime `c ℓ`, and the run is at the **view** (`:252`):

```
Θ.view c ℓ ≜ (Θ ℓ b).map ⟨b, ·⟩   where c ℓ = some b;   none where c ℓ = none
```

- `Φ.set` at a lend is the view of `Θ.add`: `(Θ.add ℓ α F).view (c[ℓ ↦ α]) = (Θ.view c).set ℓ α F`
  (`view_add`, `:278`). So `rwp_M_frame`, `erwp_M_frameF`, `erwp_withbor3` and the other lend
  frames, all stated at `Φ.set`, are already this design's lends, seen from their run.
- **`PredStep`/`MutStep`/`UpdN`/`EndOKG`/`rwpG`/`erwp` are unchanged.** They read
  `Θ.view c ℓ`, which is `Θ ℓ (c ℓ)`. A consistent view (below) gives each cell its own lifetime,
  so `PredStep` at a cell at `b` reads the entry `(ℓ, b)`, its lend's.
- **Consistency.** `Consistent c ρ`: every `mut` cell of `ρ`'s flattening is at `c ℓ` (`:292`).
  `↭` keeps it, because `UpdMutN`'s second clause gives each `mut` cell after a step a `mut` cell
  before it at the same lifetime (`consistent_of_updN`, `:297`).
- `Θ.Down → (Θ.view c).Down` (`view_down`).

### 2.3 The interpretation's clauses

- **`Mut @a A`** is Core's shape (`mutL`, `:168`): a location whose cell at `a = @aδ` holds the
  member `j ≥ k` of `famL a 𝒱⟦A⟧ Θ`, together with `Θ ℓ a = some (famL a 𝒱⟦A⟧ Θ)`.
- **`U C`**: `C` at every `ExtA`-extension `Θ′` and every view `c′` consistent with the thunk's
  resource. `vThunk` with `Covers` has the right idea but the wrong strength: it asks for some
  family, where consistency plus the `Mut` clause name the payload's family.
- **`⊸`** and **`SemJN`** quantify over `(Θ, c)` with `c` consistent with the argument's and the
  context's resource. The relation's `Φ` is `Θ.view c`.
- **`F A`, `F_Σ R`, `tabN`, `finN`** are `erwp` at `Θ.view c`, as now at `Φ`.

## 3. The lemmas the port needs

All proved results below are in `Core/Chain/LocTypeSketch.lean`, registered in `Core/Chain.lean`
and in `scripts/AxiomCheck.lean`. Axioms are within `propext`, `Classical.choice`, `Quot.sound`.

**(L1) The anti-frame's reseal at the original entry. Proved.**

- `reseal_at_entry` (`:318`). Take `Θ.Ext Θ′`, `c ℓ = some β`, `DownFam β (famL β P Θ)`, and
  `mutL β P Θ n (loc ℓ) ρ`. Then `ρ = ℓ ↦ mut(β, w, χ, famL β P Θ j)` with `n ≤ j`, and
  `Θ′.view c ℓ = some ⟨β, famL β P Θ⟩` (the anti-frame's `hF`, at `Θ` and at the reborrow's
  world). For every `m ≤ k` and every content `(w′, σ′) ∈ famL β P Θ k`, the reseal
  `mut(…, F j) → mut(β, w′, σ′, F k)` is a `MutStep` at `Θ′.view c` at `m`. The resealed cell is
  again `mutL β P Θ k (loc ℓ)`. That is Core's step 13: the cell is a `Mut` value again.
- `erwp_antiFrame_view` (`:346`) is the existing `erwp_M_antiFrame` (`SI/AntiStopN.lean:257`)
  applied at `Θ.view c`, with `hF` supplied by the `Mut` value. Nothing in the relation changes.
- `reborrow_view` (`:365`): for a fresh `α`, `Θ.Ext (Θ.add ℓ α Fi)`, `Θ.add ℓ α Fi ℓ β = Θ ℓ β`,
  and the reborrow world's view is `(Θ.view c).set ℓ α Fi`, the typing `erwp_withbor3` runs its
  callback at.

**(L2) A reborrow adds an entry and keeps what was typed. Proved.**

- `ext_add` (`:100`): a fresh lend is an extension. `add_keep`: the source's entry is kept.
- `mutL_add` (`:187`): for every payload `P`, a `mutL a P` value at `Θ` is one at `Θ.add ℓ₀ α F`
  for fresh `α`.
- `mutL_extA` (`:212`): `Mut` values are stable along the Kripke order `ExtA`.
- `coreShapeL_reborrow` (`:411`): `coreShape_not_reborrow`'s own configuration, per lend. With
  `ℓ_b ≠ ℓ, ℓ₂` and `α < b < β`, the value `Mut @b (Mut @β 1)` at `ℓ_b` (holding nothing at `ℓ`)
  is one of Core's shape at `Wc` and at `Wc.add ℓ α F`, for every `F`. Per location it is not
  (`Shape791N`). Every hypothesis is discharged; `Wc_fresh` shows `α` is fresh there.

**(L3) What steps 4, 6, 8, 11 and 13 read besides.**

| Step | Needs | State |
|---|---|---|
| 4 (`vC_local`) | a value at the lend's world, in the lend's stratum, is one at the world without it | `mutL_of_add` (`:225`), proved at `Mut`; `vN_local` at every type: **not built** |
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

## 8. Open questions

1. **`U`'s order: world-relative `ExtA` or Core's resource-relative `Ext`.** A thunk returned out
   of a lend's callback was proved at extensions of the callback's world. The lender forces it at
   extensions of its own world, which need not extend the callback's, since the lend's key may
   later be re-used with another family. Core's `Ext` answers this: the thunk's resource is in
   the lend's stratum, so the lend's key is below every borrow it holds. Not built; kill
   criterion K2 decides it.
2. **`erwp_consistent`** (U1's done-when): whether a `CompS` part's flat `mut` cells are the
   whole's at the same lifetime. I have not derived it and have not verified that any obstruction
   is real.
3. **`Θ.Bounded` as a premise** of `ConstN`/`SemJN`/`Goal791SchedN`. `bridgeN` and the pool's
   adequacy are at the empty world, which is bounded. That nothing upstream supplies an unbounded
   world has not been checked across `PoolN`'s statements.
4. **`Imm`** (`wl`) reads `CohE` and records. Whether `imm` lends need entries in `Θ` is not
   addressed: `PredStep` does not read `imm` cells.

Unspent: `DownFam β (famL β P Θ)` in `reseal_at_entry` is supplied in the port by `vN_down`. The
uniqueness result used is `UpdMutN`'s lifetime agreement (`MutStep`'s `ψ.at = ψ′.at`), in
`consistent_of_updN`. Not used: `vThunk`/`Covers`, which the design replaces with consistency.
