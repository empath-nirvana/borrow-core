# Restrat: re-stratification as naturality (#253)

L14.4 (O5) of `docs/effects-tr/14-stored-continuations.md` (PR #252), stated as naturality.
Every semantic definition is examined for invariance under **re-stratifications**:
`Emb c` is a strictly monotone map on `Life = ℕᵒᵈ` that is the identity at and above the cut
`c`. Such a map is an order embedding and not a symmetry.

Build with `lake build Restrat`. It uses only the standard axioms and has no `sorry`.

## 1. Audit of lifetime arithmetic (`Audit.lean`)

The audit is machine-checked. A `run_meta` scan over every constant of `Paper`, `Support` and
`Core` looks for anything that computes a lifetime rather than compares two: `Life.down`,
`OrderDual.toDual`/`ofDual`, or an algebraic instance on `αᵒᵈ`. The build fails if the result
changes.

**Decisive question: does any definition relate an outer lifetime to an inner one by `↓`
rather than by `<`?** No. No definition of the relation, the model, the typed world or `Core`
computes a lifetime.

| site | what it is | class |
|---|---|---|
| `Paper/S5_Model/Definitions.lean` `Life.down` | `↓α ≜ α + 1`, as printed; read by no other definition | the definition itself |
| `Paper/S5_Model/Definitions.lean` `Cell` | `ofDual` is the termination measure of the stratum recursion | not a lifetime computation |
| `Paper/S6_2…` `Life.down_sqsubset` (6.63) | `↓α ⊏ α` | existential: some strictly shorter lifetime |
| `Paper/S6_3…:94, 270`; `Paper/S6_5…:146–154, 359`; `Support/Model/Strata.lean`; `Support/Model/ReborrowRule.lean`; `Support/TypedWorld/FrameRules.lean:77, 363`; `Core/FrameRules.lean:77, 363`; `Core/EffWp.lean:94, 380`; `Core/SliceFrames.lean:174, 332` (`wpG_*_frameList._f`) | `↓γ`, `↓(γ ⊓ β)`, `↓@ρ`, `b₀ ⊓ ↓γ` as the witness of `∃A ⊏ γ` | existential |
| `Support/TypedWorld/Wp.lean:170`, `Core/Wp.lean:170` | `toDual(Σ + 1)`, a lifetime below a finite list ([TR] 6.112) | existential |
| `Support/Model/Outlives.lean` (`not_at_lt_of_inStratum_down`, `wit_inStratum_of_down`, `le_of_down_lt`, `not_lt_of_down_lt`, `flat_inStratum_at`, `updV_outlives_at`), `ResU.reb_inStratum_down`, `ResU.Sub.inStratum`, `ExW`/`AgW.inStratum_at` | hypotheses or conclusions `ρ ∈ Res_{↓α}`, `↓a ⊏ b` | non-strict `α ⊑ @ψ`: `inStratum_down_iff`, proved here |
| `Core/Slices.lean:96–220`, `Core/EffBorrow.lean:310–772`, `Core/Compatibility.lean:1063` | a strict-stratum lemma used at `↓β` to get a non-strict side condition | non-strict, in proofs |
| `Support/Lifetimes/*` `+ 1` | bounds on lifetime *variables* (`freshOfL`, `varBound`, `lifeBound`, `lsubRangeBound`) | syntactic, not lifetimes |
| `ViewWitness.ρ₁/ρ₂`, `SplitExample`, `inner`, `RebExample` | worked examples at numeral lifetimes | examples |

## 2. Re-stratifications (`Injection.lean`)

`Emb c` is defined with `f`, `StrictMono f`, and `∀x ⊒ c. f x = x`. Proved:

- `f` preserves `⊤`, `⊓` and `⊔`.
- `f x ⊑ x`, and below the cut stays below the cut.
- `Emb.shift c k` moves every lifetime below `c` down by `k`.
  - It commutes with `↓` strictly inside the moved interval (`shift_down`).
  - It does not commute at the cut (`shift_down_cut`), so "preserves `↓` at the cut" cannot be
    satisfied by any non-identity shift.
  - It places the moved interval below any point (`shift_fresh`).

At the lifetime level, `@a(f∘δ) = f(@aδ)` (`interp_mapN`), `⟦Δ⟧` is invariant
(`models_mapN_iff`), and so is `α ⊏ @bδ` (`ltLife_mapN_iff`).

## 3. Naturality, per definition

`Agree P′ P ≜ ∀ρ. P′(e·ρ) ↔ P(ρ)`. The action `relC`/`relU`/`relRU` moves every lifetime of
every cell at every depth, by the stratum recursion that builds `Cell`. It moves a `mut` cell's
invariant to its image. It is injective (`relU_injective`) and is the identity on `Res_c`
(`relRU_of_inStratum`).

| definition | status | Lean |
|---|---|---|
| strata `Cell_α`, `Res_α`; `@ψ` | natural | `inStratum_relU`, `at_relU` |
| `@ρ` | natural | `atLife_iff`, `at_relRU` |
| `imm(…)`, `mut(…)` | natural; the invariant moves to its image | `relU_immOf`, `relU_mutOf` |
| `▶◀`, `●`, `⋈`, `○` | preserved, reflected, and closed under moved operands | `compatS_iff`, `compS_fwd/bwd`, `compatR_iff`, `compR_fwd/bwd` |
| `ρ₁ ◐ ρ₂`, `⨀`, `≤`, `ρ∣ι`, `ℓ ↦ ψ`, `ρ/ℓ` | natural | `comp_iff`, `bigComp_iff`, `resLe_iff`, `relRU_restrict`, … |
| `ex(ρ)`, `ag(ρ)`, `⦇ρ⦈`, `⦇ρ⦈(ℓ)` | natural; the walk of a moved resource is moved | `exW_fwd/bwd`, `agW_fwd/bwd`, `flat_iff`, `flatAt_iff` |
| `✓`, `⟦ρ⟧`, `#`, `↭` (both readings), `ρ⁺∣own = ∅` | natural | `valid_iff`, `lower_iff`, `hash_iff`, `upd_iff`, `updV_iff`, `noOwn_iff` |
| `reb_α`, `↺_α` | natural; a member of `reb_{eα}(e·ρ)` is moved | `reb_iff`, `reb_image`, `agree_reborrow` |
| `⌜p⌝`, `emp`, `∧`, `∨`, `⇒`, `∀`, `∃`, `!`, `⋆`, `[α]` | natural | `agree_*` |
| `─⋆` | natural when its argument holds only at moved resources | `agree_wand` |
| `ℓ ↦ v`, `ℓ ↦ Imm α P̂` | natural | `agree_ptoOwn`, `agree_ptoImm` |
| `ℓ ↦ Mut α P̂` | natural with `P̂` moved to its image, and only with it | `agree_ptoMut` |
| `И P̂` | backward at every `e`; forward at cofinal `e`, which every shift is | `fresh_bwd`, `fresh_fwd`, `shift_cofinal` |
| `𝒱⟦T⟧` | **not natural** (see §4) | `not_vDenNatural` |
| `wp` | **open** (see §4) | `WpNatural` |

## 4. What is not natural, and what is open

**`𝒱⟦Mut 'a (Imm 'b 1)⟧` is not natural** (`MutCounterexample.lean`). Take
`e = shift ⊤ 1` (`n ↦ n + 1` below `⊤`), `δ = ['a ↦ 3, 'b ↦ 1]`, and
`ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)`. Then:

- `𝒱⟦T⟧_δ(ℓ)(ρ₀)` holds.
- `𝒱⟦T⟧_{e∘δ}(ℓ)(e·ρ₀)` fails.

The cause is `ptoMut`'s equality `ofS Q = P̂`. The moved cell stores the image of
`𝒱⟦Imm 'b 1⟧_δ`. But `𝒱⟦Imm 'b 1⟧_{e∘δ}` also holds at an `imm` cell at lifetime `1`, which is
in the gap that every non-identity re-stratification leaves between its cut and the moved
interval.

The witness uses only that `e` leaves a gap. I have not checked whether every non-identity
`e` admits such a witness, and I have found no hypothesis on `e` alone that repairs it. Two
hypotheses on the cell do repair it:

- **Not moving the cell.** A `mut` cell whose stratum is above the cut is fixed by every `e`
  (`relRU_of_inStratum`).
- **Freeze, then re-lend.** D14.4's `Freeze` ghost-ends every internal `mut` cell into an `own`
  cell before the move. The re-lend at resume then builds the cell afresh with `𝒱⟦T⟧_{δ′}`.

Whether `ρ₀` arises at a run is not checked. The refutation is of naturality stated over all
resources.

**`wp` is open.** I have not derived `WpNatural`, and I have not verified that any obstruction
to it is real. The induction stops at `wp`'s `∀ρ_f # ρ`: at a moved resource, a frame need not
be moved (`frame_outside_image`), so the hypothesis about moved resources does not reach it.
That is a fact about the proof method, not about `wp`. The same holds for the leaked part
`ρ⁺`, which may hide a cell at a gap lifetime behind `○`'s `mut ∘ mut` clause. A route would
normalise such cells to moved lifetimes; it is not attempted here.

## 5. The segment corollary (`Segment.lean`)

- **`vDen_all_iff`.** `𝒱⟦∀'x ⊏ @b. T⟧_δ` reads the extent `α` only through `α ⊏ @bδ` and
  `δ['x ↦ α]`. With the audit, nothing reads `'h = ↓o`.
- **`restrat_segment`.** Let `Core.SemC Δ Γ M C` hold, take a cut `c`, a point `p` and
  `δ ∈ ⟦Δ⟧`. Then the shift `e = shift c p` gives an assignment `e∘δ` that:
  - is in `⟦Δ⟧`;
  - agrees with `δ` at every outer variable;
  - puts every inner variable strictly below `p`;
  - fixes every resource in `Res_c`.

  The segment's `cC` holds at `e∘δ` for every typed world, closing substitution and resource.

The running state of a segment is not transported (§4). The ghost end of a suspended frame
(L14.4's second ingredient) is not proved here.

## Precedent reused

The `π` of `relabel_reb` and `ResU.Reb` became the moved `π` of `reb_iff`. `relRes`'s cell-wise
map became the recursive `relU`. `relabel_obs`'s induction over types is not reused, because the
`Mut` clause fails (§4).
