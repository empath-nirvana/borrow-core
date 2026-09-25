# Scope: deep freeze held at the top level (option B)

This is a scoping note. It changes no code. It asks whether changing how frozen data is
*represented* would let `↭` accept a same-lifetime interior view, and what that would cost.
Each claim is marked as either machine-checked (with where), read off a definition (with
file:line), or **not derived, not verified**.

Background: `experiments/FrameEnd` located the obstruction at `↭` itself.
`FrameEnd.Views.imm_view_rejected` (`experiments/FrameEnd/FrameEnd/Views.lean:76`) shows that a
run starting at `ℓ ↦ imm(s, v, m ↦ own(u))` cannot end at a resource holding an `imm` cell at
`m`. The reason is that `⦇start⦈(m) = own(u)`, and `UpdImm`
(`Paper/S5_Model/Definitions.lean:1718`) asks both flattenings to hold the same `imm` cells.
`mut_view_rejected` (`Views.lean:92`) is the `Mut` analogue, through `UpdMut` (`:1724`).

The obstruction is about the **start** of the run. A view the start does not already carry in
its flattening can never appear. So option B has to put the view into the resource the borrow
hands over, from the moment the frame is entered.

---

## 1. The representation change

The vocabulary is `[TR]` p. 4–5, as transcribed in `Paper/S5_Model/Definitions.lean`:

- cells `own(v)`, `imm(ᾱ, v, ρ)`, `mut(β, v, ρ, P̂)` (`CellU`, `:237`);
- `▶◀`/`●`, which agree and merge `imm` cells only (`:1130`, `:1139`);
- `○`, whose clause (5) absorbs `own(v)` or `mut(β, v, ρ, P̂)` into an `imm` cell over the same
  value (`immOwn` `:1537`, `immMut` `:1543`);
- `⦇ρ⦈ = ex(ρ)_● ● ag(ρ)` (`:1677`), where `ag` walks an `imm` cell's witness with `○`
  (`AgWitsI`, `:1663`);
- `reb_α` (`ResU.Reb` `:1249`, `RebAt` `:1199`).

Today 6.64's entry (`TW.immFrame`, `Support/TypedWorld/World.lean:68`) replaces the owner's
`ℓ ↦ own(v) ● ρv` with the single cell `ℓᵢ = ℓ ↦ imm({α}, v, ρv)`.

**All three candidates are `reb_α` images of the owner, at different partitions.** This follows
from unfolding row 5.28 and was not checked in Lean. The printed `ℓᵢ` is the coarsest element
of `reb_α(ℓ ↦ own(v) ● ρv)`: take `dom(ρ′) = {ℓ}` and `π(ℓ) = ℓ ↦ own(v) ● ρv`, so the witness
is `π(ℓ)/ℓ = ρv`. The candidates below differ in how fine the partition is, and in whether the
coarse cell is kept alongside the fine one.

### (i) Flat freeze: witnesses emptied, cells lifted

The frame hands over `ℓ ↦ imm({α}, v, ∅) ● ρ_img`. Here `ρ_img` is `reb_α(ρv)` at the finest
partition: every `own(u)` becomes `imm({α}, u, ∅)`. Every `mut(β, u, χ, P̂)` becomes
`imm({α}, u, χ)`, and its witness stays nested, because `reb_α`'s `mut` clause requires
`dom(π(ℓ)) = {ℓ}`. This is survey option (d), Charguéraud–Pottier.

- **The view.** It is a `●`-factor of the start, so `↭` accepts it (`UpdV.refl`). The view is
  not produced: it was handed over.
- **6.38's restore.** Nothing in the returned cells pins `ρv` any more. `imm(α, u, χ)` forgets a
  `mut` cell's `β` and `P̂`. The restore would have to come from the frame's record at the
  meta level. 6.29 (the frame cell comes back *with its witness*), 6.38 and 6.39 all argue
  through that witness, and each would need a real re-proof.
- **Row 5.30 changes.** `ptoImm` (`:1328`) evaluates `P̂` on the witness. With an empty witness,
  `ℓ ↦ Imm α P̂` has to be restated over the lifted siblings. Every reader of an `imm` witness
  changes with it: 6.150, 6.52–6.59, and the typed world's escrow (`LeInvW`).
- **Linearity on the owner.** Kept in principle. The views are `imm`, so `ρ⁺∣own = ∅` lets them
  be dropped, and the restore comes from the record. But the record is now the only copy of
  `ρv`.

### (ii) Keep the witness, add the image beside it ("both")

The frame hands over `ℓᵢ ● ρ_img`. `ℓᵢ = ℓ ↦ imm({α}, v, ρv)` is exactly the printed cell, and
`ρ_img` is a `reb_α(ρv)` image with the partition type-directed, as `[TR]` 6.131 (↺V₁) chooses
it. For `Ref A ⊗ Ref B` that gives `π(ℓ₁) = ℓ₁ ↦ own(u₁) ● ρ_A` and `π(ℓ₂) = …`. The partition
is applied again inside each view's witness down to the leaves, so a nested `Ref (Ref A)`
has a view at every level. Each view keeps its own sub-witness, which is what `ptoImm` needs
for `Imm 'a A`.

- **Validity comes from `○` clause (5).** At `m ∈ dom(ρv)`, `ag(ℓᵢ)` gives `own(u)` and
  `ρ_img` gives `imm({α}, u, π(m)/m)`, and `imm ○ own = imm`. At the level of one image this
  is `[TR]` 6.55's corollary taken at `β = α`, and the library lemma is already stated for
  every `β` (checked, §4).
- **The machine sees the same heap.** This is 6.58 (left) at `β = α` (checked, §4).
- **6.38's restore.** It becomes two printed steps, both taken at the frame's lifetime:
  1. 6.52 subtracts the image, giving `ρ⁺ = (ρ⁺ ⊟ ρ_img) ● ρ_img`.
  2. 6.59 moves `↭` from `ρ_ctx ● ℓᵢ ● ρ_img` to `ρ_ctx ● ℓᵢ`. This is the same surgery 6.150
     performs at a fresh `β`.

  Printed 6.38 and 6.39 then apply unchanged to `ρ⁺ ⊟ ρ_img`. `experiments/FrameEnd` already
  has the typed-world exit this needs: `TW.immEnd` subtracts `c∣dom(R∣own,mut)` for
  `c ∈ reb_{⊔s}(R)` (`experiments/FrameEnd/FrameEnd/World.lean:115–119`). FrameEnd only ever
  used it with `c = ∅` (`FrameRules.lean:356`, `frame_image_empty` `:68`).
- **Row 5.30, `↭`, `●`, `⦇·⦈` and `wp` are unchanged.** What changes is the value relation's
  `Imm` clause (row 4.8, `vX … .imm`, `Support/TypedWorld/Relation.lean:91`). It must carry the
  image. The view has to be in the run's *own* resource `ρ`, because `wpTS` checks `ρ ↭ ρ′ ● ρ⁺`
  on `ρ` alone (`World.lean:138`). A copy of the image sitting in the frame `ρ_f` does not
  count.
- **Linearity on the owner: kept.** The views are `imm` and can be forgotten in `ρ⁺`. The
  restore comes from `ℓᵢ`'s own witness `ρv`, as the survey's §3 pattern requires.

### (iii) One level: only what `reb_α`'s `π` gives in one step

(iii) is (ii) without the recursion: `ρ_img ∈ reb_α(ρv)` once, which is exactly what `TW.reb`
at `β = α` adds. `experiments/Relaxed` and `FrameEnd` already allow that, with `TW.reb`'s
premise weakened to `StratumLe` (`FrameEnd/World.lean:53`, `:91`). In the typed world,
`immFrame` followed by `reb r (β := α)` is therefore already a path of FrameEnd's `TW`.

- It gives L1 for `Imm 'a (Ref A ⊗ Ref B)` → `Imm 'a A` when `A` needs no image of its own.
- It does not give a second-level projection out of `Imm 'a A` where `A = Ref A′`.
- Restore, validity and linearity are the same as in (ii).

(iii) is the cheapest candidate and the right thing to probe first.

**Survey option (c), "the partition stored in the `imm` cell",** is (ii) on a different
carrier. The partition's content is the image, and (ii) stores it as cells, which `▶◀` and `○`
already handle. Storing it inside `ImmU` would change `CellU` (`:215`) and every lemma over
cells. It is not pursued separately.

**Recommendation among the candidates: (ii), probed first as (iii).** (i) changes every reader
of an `imm` witness, and nothing in this note shows it buys more views than (ii).

---

## 2. Blast radius, for (ii)/(iii)

Sizes are line spans in the current tree. "Mechanical" means the proof text carries over with a
changed hypothesis. "Real" means a new argument is needed.

| Result | Where | Size | Class | Why |
|---|---|---|---|---|
| `↭`, `●`, `○`, `⦇·⦈`, `reb_α`, `wp` (rows 5.13–5.33) | `Paper/S5_Model/Definitions.lean:1130–1772` | — | **unchanged** | (ii) changes only what the frame hands over |
| bind: 6.48 `updV_frame`, 6.49 `UpdV.trans` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean:2189–2400` | ~210 | **unchanged** | `↭` unchanged, and every run is composed as before |
| 6.29 `six29`, 6.34 `six34` | `:745–1114` | ~370 | **unchanged** | applied after the image is removed, at the printed `ℓᵢ` |
| 6.38 `six38` (+ `Support/Model/Surgery.lean`), 6.39 `six39` | `:1149–1790` | ~640 | **unchanged**, plus a new 6.38-with-image lemma in front | the new lemma is 6.52≤ and 6.59≤ followed by `six38` |
| 6.52 `six52_H1`, `six52_sub_inStratum`, `six52` | `:2477–2695` | ~220 | **mechanical** (H1: checked), **real** (second conclusion) | `@ρₑ ⊐ α` becomes `ρₑ ∈ Res_{↓α}`, because the frame cell is at `α`. H1 goes through (§4). `@(ρ⁺ ⊟ ρ_reb) ⊐ α` is false as stated, because `ρ⁺` holds `ℓᵢ`, so it weakens to `↓α` except at `ℓ`. Not derived |
| 6.53–6.58 | `:2707–3140` | ~430 | **unchanged** | stated for every `β`. 6.55 and 6.58 are used at `β = α` as they stand (§4) |
| 6.59 `six59` and `reb_frame_*` | `:3146–3606` | ~460 | **real**, localized | `hsb : ρ_b ∈ Res_β` and `χ ∈ Res_β` are false when `ρ_b` and `χ` hold `ℓᵢ`. The closing step's use localizes to `dom(ρ_reb)` (checked, §4). Discharging the localized premise is not derived |
| 6.64 `wp_I_frame` / `wpTS_I_frameX` | `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean:79–253`; `Support/TypedWorld/FrameRules.lean:56–343` | ~175 + ~290 | **real** | entry hands over `ℓᵢ ● ρ_img`; exit passes `c = ρ_img` to FrameEnd's `immEnd` and discharges `↭` with the new 6.38. `frame_image_empty` no longer applies |
| 6.65/6.66 (Mut frame, anti-frame) | `FrameRules.lean:344–710` | ~370 | **unchanged** | no `Mut` image (see §3) |
| 6.131 `reborrow_vDen` / `reborrow_vShape`, `image_vX_of_shape` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`; `Support/TypedWorld/ReborrowShapes.lean:34`; `RelationFacts.lean:1482` | 730 + 140 + part of 1497 | **mechanical** at the `Imm` case (reb keeps `imm` cells, so the image is kept); **real** if 6.150 must produce deep images | |
| 6.150 `wp_reborrow` / `wpTS_reborrow` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean:1172–1325`; `Support/TypedWorld/Reborrow.lean:228–386` | ~150 + ~160 | **real** under (ii), **mechanical** under (iii) | with row 4.8 carrying an image, the `Imm 'b` views that 6.150 hands out must carry their own `β`-images, which means an iterated `reb_β`. Under (iii) the one-level image is what `reb_β` already builds |
| Row 4.8, `vX … .imm` / `ptoImmS` | `Support/TypedWorld/Relation.lean:49`, `:91` | small def; 42 uses (`Compatibility` 14, `Invariant` 15, `RelationFacts` 6, …) | **real** | the value relation carries the image |
| Records, `CohE`/`Coh` | `Relation.lean:55`; `Records.lean:92` | small | **unchanged** | `Coh` already accepts a chain position of a frame record (`experiments/Projection` README) |
| `FrameLife` | `Records.lean:160` | 8 uses in `Wp.lean` and others | **mechanical** | `FrameLife.2` must be non-strict (`⊑`). `experiments/Relaxed` already did this and FP held |
| `NestLife` | `Support/TypedWorld/Invariant.lean:742` | ~15 uses | **unknown** under (ii), **unchanged** under (iii) | a nested view at the same `α` as its parent violates the strict nesting `NestLife` asks for (`experiments/Projection` README, pointer 1) |
| `TW` / `TI` / `LeInvW` / `linLife` | `World.lean:63`; `Invariant.lean:1730`, `:1787`; `Wp.lean` | 2783 + 844 | **mechanical** from FrameEnd | FrameEnd already has `reb` at `β = α` (`StratumLe`), `immEnd` with `c`, `ti_sub` (`FrameEnd/Invariant.lean:2673`), `ti_endReb` (`:2506`) and `linLife_sub` (`FrameEnd/Wp.lean:328`) |
| FP (`fundamental`, `*_compatX`) | `Paper/S6_8_FundamentalProperty/Lemmas.lean:59`; `Support/TypedWorld/Compatibility.lean` | 1837 + 1336 | **mechanical** except the `Imm`-producing cases (`withload`, `withbor`, 6.64/6.150 callers) | cases that produce an `Imm` value must build its image |

---

## 3. Does it plausibly deliver?

### L1, a same-lifetime `Imm` view: plausible under (ii)/(iii)

- `↭` accepts the view by construction.
- Entry validity and the heap are existing lemmas at `β = α`.
- 6.52's H1 and 6.59's closing step survive the frame cell sitting at `α`, with the
  localizations in §4.

**Where it could first fail**, in order:

1. **The localized 6.59 premise.** At the frame configuration, every `imm` cell of `ag(L)` and
   of `ag(R)` at a location of `ρ_reb` must be `⊐ α`. Here `L = ρ_img∣imm ● ρ_ctx ● ℓᵢ` and
   `R = ρ′ ● (ρ⁺ ⊟ ρ_img)`. At those locations `ℓᵢ` contributes `own`/`mut`, not `imm`, and
   `ρ_ctx` has nothing there (it is `# ρv ● ℓ ↦ own(v)`). So the premise looks vacuous there.
   **Not derived, not verified.**
2. **6.52's second conclusion** at `↓α` except at `ℓ`, as it feeds 6.59's `hχβ`.
   **Not derived.**
3. **Row 4.8 carrying the image, together with 6.150.** This is the largest real re-proof.
   Under (ii), the `NestLife` interaction is also here. **Not derived.**

### L3, a lens-style `Mut` view: not by this route

(ii) works for `Imm` only because `○` clause (5) lets an `imm` view agree with an `own` cell
that sits under another cell's witness. The exclusive walk `ex(−)_●` has no agreement
clause. **Machine-checked** (`mut_lens_beside_parent_invalid`, §4): if `ρw(m) = own(u)`, then
`ℓ ↦ mut(b, v, ρw, P̂) ● m ↦ mut(b₁, u₁, χ₁, P̂₁)` is not `✓`, at any `b₁` and `P̂₁`.

So a `mut` view cannot sit beside its parent. The other shape would be a nested lend: the
parent's witness holds `m ↦ mut(…)` in place of `own`. That shape fails first at the parent's
refinement `P̂(v)(ρw)`. With `P̂ = 𝒱⟦Ref A ⊗ Ref B⟧`, `Ref`'s clause needs `ptoOwn` at `m`
(`Relation.lean:89`). Making `P̂` accept a lend changes `Mut`'s relation, which is a different
option. **Not derived, not verified.**

### L2: no

Two `mut` views at the same `α` each hit the checked clash above.

---

## 4. The decisive probe

The question: at the resource-algebra level, with no typed world and no FP, does handing over
`ℓᵢ ● ρ_img` let `↭` accept the view, while 6.38's restore and bind's frame preservation
survive?

**What was run.** Two scratch files, not committed, each checked with `lake env lean` against
the library:

- `/private/tmp/claude-501/-Users-johnthompson-repos-borrow-lang/8e4045bd-7129-41e8-acf7-6b8f9fa81f6a/scratchpad/deepfreeze/Probe.lean`
- `/private/tmp/claude-501/-Users-johnthompson-repos-borrow-lang/8e4045bd-7129-41e8-acf7-6b8f9fa81f6a/scratchpad/deepfreeze/MutProbe.lean`

These live in a session scratch directory and may not persist; the table records their statements.

Every result below has `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.

| Name | Statement | How |
|---|---|---|
| `entry_valid` | `ρ_img ∈ reb_α(ρv)` → `ρ_img # ℓ ↦ imm({α}, v, ρv)`, under 6.55's added hypotheses (`EscrowAgree`, `AgW ρ_img A`) | `ResU.six55_self` at `β = α` (`Lemmas.lean:2817`) |
| `entry_heap` | `⟦ρ_img ● ρ_b ● ℓᵢ⟧ = ⟦ρ_b ● ℓᵢ⟧` | `ResU.six58_left` at `β = α` (`:3018`) |
| `view_accepted` | a valid start that splits as `view ● rest` updates to itself | `UpdV.refl` |
| `six52_H1_frame` | 6.52's H1 with `ρₑ ∈ Res_{↓α}` in place of `Res_α`, so the context may hold the frame cell at `α` | proof text of `ResU.six52_H1` (`:2491`) with its one `mono` step removed. That step was the only use of the strict premise |
| `reb_frame_absImm_local` | 6.59's closing step, with `L ∈ Res_β` replaced by "`imm` cells of `ag(L)` at locations of `ρ_reb` are in `Res_β`" | proof text of `ResU.reb_frame_absImm` (`:3146`), with the stratum fact moved into the one branch that uses it |
| `mut_lens_beside_parent_invalid` | `ρw(m) = own(u)` → `¬✓(ℓ ↦ mut(b, v, ρw, P̂) ● m ↦ mut(b₁, u₁, χ₁, P̂₁))` | `xpath_ex` and `ExS.get_of_ne_imm` give two different cells of `ex(−)_●` at `m` |

**Result.**

- The entry side of (ii)/(iii) costs nothing: the library's 6.55 and 6.58 are already stated
  for every `β`.
- The exit side does not need the strict stratum. In 6.52's H1 it was needed only for
  `↓α`; in 6.59's closing step it was needed only on `dom(ρ_reb)`.
- This does not yet prove the frame-end lemma, and it does not show that none of the other
  uses of the strict premise matters.

**Next step (the decisive one).** Build `six38_img`:

> `ρ_ctx # ρv ● ℓ ↦ own(v)`, `@ρ_ctx ⊐ α`, `@ρ′ ⊐ α`, `ρ⁺∣own = ∅`,
> `ρ_img ∈ reb_α(ρv)`, and `ρ_ctx ● ℓᵢ ● ρ_img ↭ ρ′ ● ρ⁺`
> ⊢ `ρ′ ● (ρ⁺ ⊟ ρ_img)/ℓ # ρv ● ℓ ↦ own(v)`.

It is assembled from four pieces:

1. `six52` at `↓α` except at `ℓ`;
2. `six59_frame`: `six59` with `ρ_b = ρ_ctx ● ℓᵢ`, threading `reb_frame_absImm_local` through
   `reb_frame_ag_le`/`_eq`, `six59_ag_eq` and the two `…Keep` residuals, and discharging the
   localized premise;
3. printed `six38` at `ρ⁺ ⊟ ρ_img`;
4. `six39` unchanged for the outer `↭`.

Bind needs no probe, because `↭` and `●` are untouched.

- **Estimated size:** about 500 lines, mostly adapted copies of `Lemmas.lean:2491–3606`.
- **If `six38_img` elaborates**, L1 is reduced to typed-world plumbing plus row 4.8.
- **If the localized premise cannot be discharged**, the configuration that stops it should be
  built in Lean before any conclusion is drawn.

---

## 5. Recommendation

Pursue (ii), and probe it first as (iii). The frame keeps the printed `ℓ ↦ imm({α}, v, ρv)` and
additionally hands over its `reb_α` image at the frame's own lifetime. At the exit, 6.52 and
6.59 subtract the image, which is the reborrow's own surgery, run at `α`. No model definition
changes, and the owner's restore still comes from the frame's witness.

The first work item is the RA-level `six38_img` in §4. Drop L3 (and L2) from this line: the
"both" representation is machine-checked to fail for `mut`.

**Main risk:** row 4.8 has to carry the image. That forces 6.150 to hand out views with their
own images (an iterated `reb_β`), and under (ii) it collides with `NestLife`'s strict nesting.
That part of the blast radius is the largest and the least understood.
