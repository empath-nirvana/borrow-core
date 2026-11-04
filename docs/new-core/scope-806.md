# Scope: a run may give up an `imm` view copy held outside it (#806), along the walks

Part of #771; needed before #789's compatibility step. Branch `updx-806` (stretch stack, on
`si-782`). This is revision 2. The user chose option C (compare walks, `[TR]` 6.48's ancestor
technique) after the flattening-pointwise relation `UpdXW` failed its frame step. No proof work
until this is reviewed.

**Evidence kept.**
- `Support/Model/Tree/World/UpdXW.lean`: the pointwise relation `UpdXW`, its composition (`XOptW.trans`), and `not_xoptWFrameAt`, which refutes `xopt_comp`'s route at it.
- `docs/new-core/scope-806/Clause.lean`: `twp_refuses_last_copy` and `twp_refuses_lendEnd_live_copy`. Both are proved, and neither reads `UpdX`.
- `Core/TreeConsume.lean` (#793).

All `#print axioms` are ⊆ [propext, Classical.choice, Quot.sound].

**Kernel target.** `EndT`'s start/end relation becomes `UpdA` (§1), which reads a `mut` cell through the `imm` cell it sits beneath. Under it these must hold:
- `UpdA.frame` and `UpdA.trans`;
- T1–T4 as approved;
- `not_xoptWFrameAt`'s configuration admitted;
- `twp_refuses_lendEnd_live_copy` and `twp_refuses_last_copy` still true;
- `twp_lendEnd`, `twp_lendOpen` and `twp_update`'s premise unchanged.

## 0. Why per-location failed, and what the printed proof does instead

`not_xoptWFrameAt` is the failure. A run gives up `x = imm(…)` at `ℓ` while the framed part's flattening holds `y = mut(…)` at `ℓ`. `⦇·⦈` composes the two (`imm ○ mut = imm`, `○` clause (5)), so the composite start reads `x` and the composite end reads `y`. No relation between the two cells at `ℓ` alone accepts that.

`[TR]` 6.48's proof never compares the `○`-composites at `ℓ` alone. It is transcribed at `Support/Model/Tree/Port/Six48.lean`, `updV_frame`.
- It splits `⦇ρ₁ ● ρⱼ⦈ = ex(ρ₁)_● ● ex(ρⱼ)_● ● (ag(ρ₁) ○ ag(ρⱼ))` (6.20, 6.18).
- In the aliasable case, it accounts for a `mut` cell of `ag(ρ₂)` **by the `imm` cell it sits beneath**: `ag(ρ₂)(ℓ′) = imm(_, _, ρ′)` with `ℓ ∈ dom(⦇ρ′⦈_○)`. The update pins the ancestor, so the cell beneath travels with it (`ResUT.upd_ag_nonimm_transfer`, `upd_ag_mut_eq`, `upd_ag_eq_of_ne_own`).

`[TR]` 6.59's closing sentence uses the same technique: it absorbs a walk by absorbing the walk's `imm` cells and their ancestors' witnesses (`AgWT.absorb_of_ancestors`, `AgWT.AbsImm`, `AgWT.AbsAnc`, `Port/ClosingSentence.lean`).

In `y`'s case the ancestor is the framed part's `imm` cell above `y`, which the run never touched. The end's `y` is accounted for by that ancestor.

## 1. The new relation

**What a walk is at the tree world, and which existing definitions give it.** The walks are the carrier's own:

| Object | Definition | File |
|---|---|---|
| exclusive walk `ex(ρ)_●`, `ex(ρ)_○` | `ExST`, `ExRT` (`G.ExW` at `●`/`○`) | `Tree/CarrierRes.lean:400–403` |
| aliasable walk `ag(ρ)` | `AgWT` (`G.AgW`: the top `imm` cells, the `ag` of `mut` witnesses, and `ex_○ ○ ag` of `imm` witnesses) | `Tree/CarrierRes.lean:406` |
| `⦇ρ⦈ = ex(ρ)_● ● ag(ρ)` | `ResUT.Flat` | `CarrierRes.lean` (row 5.22) |
| a cell of the aliasable walk beneath an `imm` ancestor | `AgWT.nonimm_beneath_imm` | `Tree/Port/AgBeneath.lean:17` |
| an ancestor's witness walk is a `○`-factor | `AgWT.flat_imm_wit_le`, `ResUT.flat_imm_wit_factor` | `Tree/Port/Ancestors.lean:239, 332` |
| the ancestor carried by an update | `ResUT.upd_ag_imm_wit_factor` | `Ancestors.lean:344` |
| absorption through ancestors | `AgWT.absorb_of_ancestors`, `AbsImm`, `AbsAnc` | `Port/ClosingSentence.lean:548–583` |

The tree has no `Path`/`Anc` predicate over cells; the ancestor relation is the existential shape that `AgWT.nonimm_beneath_imm` returns. `FrzT`/`InDomT` (`World/ExtF.lean`) and `CellAt` (`World/Coherent.lean`) are predicates on locations or cells at depth in the resource tree, and `HoldsMut` (`World/Codes.lean:76`) reaches every witness. None of these is the walk. §5 uses `CellAt` and `HoldsMut` (R3, R7).

**What is new** is in `Support/Model/Tree/World/UpdA.lean`. It elaborates: `#check @UpdA` and `#check @Beneath` pass, and `UpdX.toA` and `UpdXW.toA` are proved.

```lean
/-- `ξ` sits beneath the `imm` cell `ζ` at `m` of `σ`, at `n`: `ζ`'s witness's `⦇−⦈_○`
(`ex(χ)_○ ○ ag(χ)`) carries `ξ` at `n`. The shape `AgWT.nonimm_beneath_imm` returns. -/
def Beneath (σ : TRes K) (m : BoCa.Loc) (ζ : TCell K) (n : BoCa.Loc) (ξ : TCell K) : Prop :=
  σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧
    ∃ ev av p, ExRT ζ.wit ev ∧ AgWT ζ.wit av ∧ ResUT.CompR ev av p ∧ p.get n = some ξ

def XOptA (Θ : LocTy) (E E' : BoCa.Loc → Prop) (σ : TRes K) (σ' τw : TRes K') (l : BoCa.Loc) :
    Prop :=
  (∀ ψ, σ.get l = some ψ → ψ.kind ≠ Kind.own → ¬ E l → ¬ E' l ∧
    ((∃ ψ', σ'.get l = some ψ' ∧ XCell Θ ψ ψ') ∨                    -- kept
     (∃ χ, τw.get l = some χ ∧ CellAbs Θ ψ χ) ∨                     -- an `imm` cell given up
     (ψ.kind = Kind.mut ∧ ∃ m ζ χ, ¬ E m ∧ Beneath σ m ζ l ψ ∧       -- a `mut` cell leaving
        τw.get m = some χ ∧ CellAbs Θ ζ χ))) ∧                       --   with its ancestor
  (∀ ψ', σ'.get l = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' l → ¬ E l ∧
    ((∃ ψ, σ.get l = some ψ ∧ (XCell Θ ψ ψ' ∨ CellSub Θ ψ ψ')) ∨     -- from the start's cell
     (ψ'.kind = Kind.mut ∧ ∃ m ζ ξ, Beneath σ m ζ l ξ ∧ XCell Θ ξ ψ')))  -- from beneath an ancestor

def UpdA (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' fρ' : TRes K') : Prop :=
  ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
    ∀ l, XOptA Θ E E' σ σ' τw l
```

`CellAbs` and `CellSub` are the ones in `UpdXW.lean` (approved D-2, D-3).

The two new disjuncts are the ancestor technique. They read `σ` at an ancestor location `m ≠ l` and the ancestor's witness walk, so `XOptA` is not a function of the three cells at `l`.

The end-side `mut` disjunct requires the cell to have sat beneath a **start** ancestor, that is, provenance in `ρ`. This is what separates it from option B (any `mut` cell where the start read `imm`): a run cannot produce a `mut` cell that was not in its start's walk.

In `EndT`, `UpdX (sem w′.Θ) (recMask O₀) (recMask O′) ρ₀ ρ′` becomes `UpdA (sem w′.Θ) (recMask O₀) (recMask O′) ρ₀ ρ′ fρ′`. Nothing else in `EndT` changes.

## 2. `UpdX` itself

`UpdX` does **not** move to the walk form.
- **Why it can stay:** `UpdX` is the relation every segment-start update builds: `twp_update`'s premise, `twp_lendOpen`, `twp_lendEnd`, the heap rules, `UpdX.of_rr`. None of those gives a cell up, and `UpdX.toA` lifts `UpdX` to `UpdA`.
- **`UpdX.frame`'s proof survives:** its current proof (D5's pointwise route through `xopt_comp`) is unchanged. With no cell given up, `not_xoptWFrameAt`'s failing case cannot arise: `XOpt` keeps `x`, so the composite end reads `x ○ y′ = x`.
- **D5 is now forced for `UpdA.frame`:** D5 recommended proving the frame step along `Port/Six48`'s route (walk split, then ancestor) rather than pointwise. For `UpdA.frame` that is now required. Whether to re-prove `UpdX.frame` the same way, so that D5 closes, is design choice C-2.

## 3. Results to re-prove

| File | Result | Statement changes? |
|---|---|---|
| `World/UpdA.lean` (new) | `UpdA.frame`, `UpdA.trans`, `UpdX.transA` (a plain `UpdX`, then `UpdA`), `UpdA.widen`, `UpdA.congr`, `UpdA.inv`, `InvKept.transA`, `Beneath.compS_left/right`, `Beneath.rr`, `Beneath.flat_get` (the ancestor's contents are in `⦇ρ⦈`), `UpdX.toA` (done) | new |
| `World/UpdX.lean`, `UpdXInv.lean`, `UpdXMasks.lean` | everything | no |
| `World/UpdXW.lean` | kept as evidence; `EndT` does not read it | — |
| `World/StepKeep.lean` | `fdEsc_of_updX` → `fdEsc_of_updA` | **yes** (approved): `hu : UpdA … ρ ρ′ fρ′` |
| `Core/TreeWp.lean` | `EndT` | **yes** (approved) |
| same | `endT_inv` | **yes** (approved): its conclusion exposes the clause, which becomes `XOptA` with `∃ τw, Flat fρ′ τw`. `XInv` is unchanged (it reads pairs of `mut` cells at one location) |
| same | `twp_here` (`UpdX.toA`), `twp_bind` (`UpdA.trans`, `InvKept.transA`), `twp_frame` and `twp_frame_w` (`UpdA.frame`), `twp_extend` and `twp_update` (`UpdX.transA`) | no |
| `Core/TreeHeap.lean` (:287, :337, :463, :536) | the heap rules | no |
| `Core/TreeStepKeep.lean` | `StepKeepsFdEsc`, `StepKeepsFdEscNoUpd` (defs), `stepKeepsFdEsc` | **yes** (approved): the defs quote `EndT` |
| `Core/TreePool.lean` (:168, :211), `Core/TreeHandle.lean` (:123) | the pool frame; bind through the handler | no |
| `Core/TreeLend.lean` | `twp_lendOpen`, `twp_lendEnd` | **no** |
| `Core/TreeResume`, `TreeSched*`, `TreePool*`, `TreeRelay*`, `TreeCactus`, `TreeHeadlines` | — | no (they read `EndT` only through the rules) |
| `Core/TreeConsume.lean` | `updX_consume_view_false` stays (it is about `UpdX`). `twp_refuses_consume_view(_at)`, `twp_frame_callee_refused` and `twp_child_refused` are **retired**, replaced by T1–T3 | — |
| same | the rest | no |

`twp_frame`'s statement does not change. `UpdA.frame` takes `MutOne` of the end world as a hypothesis, and `twp_frame` reads that off the end's `RecInv` (`TWNT.mutOne`), as it already does for `InvKept.frame`.

## 4. `not_xoptWFrameAt`'s configuration through `UpdA`, by hand; the hardest case

**The configuration at resources.** One carrier, empty masks.
- The run's part is `a = ℓ ↦ x`, with `x = imm(s, v, χ₀)`.
- The framed part is `c = n ↦ ζ`, with `ζ = imm(t, u, χ)`, `χ = ℓ ↦ y`, and `y = mut(b, v, χ₀, P)`. `y` has the same value and witness as `x`, as `○` clause (5) requires.
- The frame is `ρf = ℓ ↦ x`, a copy of the run's view.
- The run gives `x` up: `a′ = ∅` and `c′ = c`.

The walks and flattenings:
- `ac = a ● c` has `ex(ac) = ∅`, because both tops are `imm`.
- `ag(ac)` is the top `imm` cells `{ℓ ↦ x, n ↦ ζ}` composed (`○`) with `ζ`'s witness walk `ex(χ)_○ ○ ag(χ) = ℓ ↦ y`. So `⦇ac⦈ = {ℓ ↦ x ○ y = x, n ↦ ζ}`.
- `⦇ac′⦈ = ⦇c⦈ = {ℓ ↦ y, n ↦ ζ}`.
- The end world is `fρ′ = ρf ● c`, with `⦇fρ′⦈ = {ℓ ↦ x ○ y = x, n ↦ ζ}`.

Checking each side:
- **Start side at `ℓ`:** `x` (`imm`, unmasked) is not kept, because `⦇ac′⦈(ℓ) = y`. But `⦇fρ′⦈(ℓ) = x` absorbs it (`CellAbs x x`). ✓ by the second disjunct.
- **Start side at `n`:** `ζ` is kept (`XCell ζ ζ`). ✓
- **End side at `ℓ`:** no start cell at `ℓ` relates to `y` (`mut`), because `⦇ac⦈(ℓ) = x` is `imm`. But `Beneath ⦇ac⦈ n ζ ℓ y` holds (`ζ` is at `n` and its witness walk carries `y` at `ℓ`), and `XCell y y` holds. ✓ by the ancestor disjunct.
- **End side at `n`:** `ζ` comes from `ζ`. ✓

So `UpdA ∅ ∅ ac ac′ fρ′` holds where `UpdXW` and `UpdX` fail. The inner run (`a → a′`, beside the frame `ρf ● c`) meets `UpdA` at `ℓ` by the absorbed disjunct; no ancestor is needed there.

**The hardest case (T4), restated.** A lend of `ℓ` at `α` ends after one copy was given up while another task still holds a live copy.
- **T4a (the given-up copy leaves nothing):** `twp_consume_view_framed` (T1) runs from `Z`, and the world is unchanged (`consume_view_world`). Under `UpdA`, a copy given up over a `mut` cell takes nothing else with it. The cells beneath it belong to the ancestor, and they leave only together with an absorbed ancestor (the start-side `mut` disjunct reads `CellAbs` at `m`).
- **T4b (no end while a live copy is held):** `twp_refuses_lendEnd_live_copy`. It is proved, and it reads `▶◀` at the end world, not `↭`. It is re-checked under `UpdA`.
- **T4c:** `twp_lendEnd_after_framed_consume`, as in revision 1. First T2 (the callee gives its copy up under the lender's frame), then `twp_lendEnd`, unchanged, once the live holder has returned its copy (`hF : NoneAt (· = ℓ)` on the frame).

T1–T3 are as approved (D-1: frame conditions strengthened by `HoldsView`), and are stated for every configuration. `twp_refuses_last_copy` stays: it reads `RecInv`, not `↭`.

## 5. Risks, ranked

| # | Risk | Lean check |
|---|---|---|
| R1 | **`UpdA.frame`.** Proved along `updV_frame`: `Flat.split` gives `ex(a ● c)` and `ag(a ● c)` from the parts, with 6.36's three-way disjointness (`ExST.immFree`). New obligations: **(a)** a `Beneath` in `⦇a⦈` or `⦇c⦈` lifts to `⦇a ● c⦈`, because the ancestor's composite has the same witness (`○` of an `imm` cell keeps it, `CellUT.CompR.wit_eq`); **(b)** an end `mut` cell of `ag(c′)` has a `c′`-ancestor (`AgWT.nonimm_beneath_imm`), which is the re-reading of a `c`-ancestor (`RR` on witnesses, `Flat.rrLs` at the witness); **(c)** `MutOne` at the end world makes the end `mut` cell at `l` a single contribution, so the `mut ○ mut` clause of `○` with mixed provenance does not arise | not checked |
| R2 | **Masks in the absorbed branches** (`UpdA.trans`, and `¬ E′ l` in the two disjuncts where a cell leaves). `XOptW.trans` is proved with the mask as an explicit obligation `hw`. At resources this needs "a run does not gain a record masking a location where the world's flattening reads `imm`": opening a lend there needs `own`, which `▶◀` refuses, and an escrow's exclusive part is the same | partly: `XOptW.trans` (`UpdXW.lean:117`) is proved with `hw`; the resource lemma is not checked |
| R3 | **`InvKept.transA`.** A start `mut` cell that left with its ancestor has no middle cell to chain through. Its code is kept because the world still holds it beneath the absorber: `HoldsMut` reaches every witness (`Codes.lean:76`), and `TWd.Ext` carries `AgreeOn` of the frame | not checked |
| R4 | **World growth for `UpdA.trans`.** The end world must absorb every `imm` cell the middle world absorbed: the frame part through re-reading (`LsSim`), the run part by segment 2's clause. The ancestor disjuncts compose through this, since an absorbed ancestor stays absorbed | not checked |
| R5 | **`fdEsc_of_updA`.** An end `mut` cell from beneath a start ancestor is in `⦇ρ⦈` at `l` (`flat_imm_wit_factor` makes the witness walk a `○`-factor of `ag`). So `FdEsc`'s "the start holds nothing there" still refutes it | not checked |
| R6 | **T1 under `UpdA`.** `Z ● v` with `Z` holding a `mut` cell beneath an ancestor at `ℓ` (the same cells as `not_xoptWFrameAt`): the ancestor disjunct covers it | not checked |
| R7 | **`endT_inv`.** `XInv` reads pairs of `mut` cells at one location. An end `mut` cell from beneath an ancestor faces an `imm` start cell there, so `XInv` is vacuous at it. Row 5.27's `P̂` for that cell is the code at `l`, kept by `AgreeOn` (as in R3) | not checked |
| R8 | `CactusInvT`, `TWNT`, `RecInv` and `TaggedT` do not read `↭` | checked by grep (revision 1); not by a build |

**Size.**
- `UpdA.lean`: 900–1400 lines. R1 is the bulk. `updV_frame` is about 200 lines at the unmasked relation with no cell given up; the ancestor lift and the re-reading add the rest.
- `StepKeep` and the Core sites: 100–200 lines.
- T1–T4: 300–500 lines.
- In all, about 1300–2100 lines.

## 6. Not doing

- **Per-location splits.** No proof of `UpdA.frame` or `UpdA.trans` through a lemma about the three cells at `l` (`xopt_comp`'s shape); `not_xoptWFrameAt` shows that route fails. Case splits follow `updV_frame`'s (the walk split and its three domains), not new splits on cell kinds.
- **Option B.** No end case "`mut` where the start read `imm`" without a start ancestor.
- **Hypotheses on `twp_frame`**, and no statement change outside `EndT`, `endT_inv`, `fdEsc_of_updX` and `StepKeepsFdEsc`.
- **Restoring ρ⁺.**
- **Giving up `mut` views.** A `mut` cell leaves only together with an `imm` ancestor.
- **Changing D15.**
- **Weakening `twp_lendEnd`.**
- **T1–T4 proved only at fixed configurations.**
- **Changing `UpdX`** or `twp_update`'s premise.
- **The reachability check** (whether `TWNT` excludes an `imm` view over a `mut` cell): not done, per the user.

## 7. Kill criterion and the stated-exclusion fallback

**Kill.** Design (b) along the walks is dead if either of these is shown by a Lean configuration with every hypothesis discharged:
- `UpdA.frame` or `UpdA.trans` is false under `MutOne` and validity of the worlds involved (both composites admitted ends, their composite not);
- T4b is false under `UpdA`.

**Fallback (stated exclusion).** If `UpdA` covers everything except some class:
- T1–T3 stay theorems.
- The class is excluded by an explicit hypothesis on the frame condition or on the resource. The hypothesis is decidable (a recursion over the finite resource tree, `CellAt`) and is never a list of programs:

```lean
/-- No `mut` cell at `l` at any depth of `ρ`. Decided by recursion on `ρ`'s cells and witnesses. -/
def NoMutAt (l : BoCa.Loc) (ρ : TRes K) : Prop :=
  ∀ ψ, CellAt ρ l ψ → ψ.kind ≠ Kind.mut
```

- It goes on T1's `Z` and on the frame condition (`∀ w ρf, F w ρf → NoMutAt ℓ ρf`).
- It is shown satisfiable at the #793 configuration, and the excluded class is refuted outside it by a configuration.
- It is not a hypothesis on `twp_frame` (§6), and it does not stand in for an unproved lemma.

## Design choices for the user

- **C-1.** The ancestor disjuncts read the ancestor from the **start's** flattening (provenance in the run's start), not from the end world's. Reading the world would also admit a `mut` cell beneath another task's ancestor, which is weaker.
- **C-2.** Either re-prove `UpdX.frame` along the walks too (closes D5; about 150 more lines), or leave its pointwise proof (it is sound and not on `EndT`'s path).
- **C-3.** For `UpdA.frame`, either take `MutOne` of the end world as a hypothesis (proposed; it is already in `RecInv`), or handle `mut ○ mut` with mixed provenance by a third ancestor case.

## Appendix: R1 (`UpdA.frame`) proof plan, worked before building

This was worked by hand against the carrier's lemmas; none of it is built yet. Two facts the plan needs go beyond revision 2's text.

1. **`MutOne` of the start composite as well as the end world.** At a location where both `⦇a⦈` and `⦇c⦈` read a `mut` cell, the start composite is `mut ○ mut`. It is the end's re-read cell only if the two operands are one cell, which is what `MutOne` gives (`AgW.mutIn`, `flat_mut_cellAt`). `twp_frame` has `RecInv` at the start too (`TWNT.mutOne`), so no statement changes. This is the start-side half of C-3.
2. **A `mut`-keeping form of `AgWT.nonimm_beneath_imm`.** `Beneath`'s end-side disjunct asks `XCell ξ ψ′` of the cell `ξ` beneath the ancestor. `nonimm_beneath_imm` gives only `ξ.wit = φ.wit`, `ξ.erase = φ.erase` and `ξ.kind ≠ imm`, so `ξ` may be an `own` contribution under a `mut` walk cell. The variant states that, under `MutUniq (CellAt ρ)`, a `mut` cell `φ` of `ag(ρ)` sits beneath an `imm` ancestor whose witness walk carries `φ` itself. It is the same `G.AgW.rec` induction, with `MutKeep` at each `○` (`mutKeep_compR`), and is about 120 lines.

**The cases**, following `updV_frame`'s split on the fixed part `c`, which is re-read. `o = ⦇ac⦈(l)`, `o′ = ⦇ac′⦈(l)`.
- **Start side, an `imm` cell:** always the absorbed disjunct. Each `imm` part of `o` is absorbed by the end world. The run's part is absorbed through the inner clause (kept into `⦇ac′⦈ ⊆ ⦇fρ′⦈`, or absorbed). The framed part is absorbed by being re-read into `⦇c′⦈ ⊆ ⦇fρ′⦈`. A union lemma over `lsc` then absorbs `o`.
- **Start side, a `mut` cell:**
  - If the framed part has nothing or `own` at `l`, the inner clause decides. When the cell leaves with its ancestor, `Beneath` lifts from `⦇a⦈` to `⦇ac⦈`: the composite at `m` keeps the ancestor's witness. The end world absorbs the lifted ancestor by the same union lemma.
  - If the framed part is `mut`, start `MutOne` makes `o` that cell, and end `MutOne` makes `o′` its re-reading.
- **End side, an `imm` cell:** `CellSub`. The run's `imm` part comes from the inner end side, and the framed part is re-read.
- **End side, a `mut` cell:**
  - If the cell is the framed part's: when `⦇a⦈(l)` is `imm` (the `not_xoptWFrameAt` case), validity puts the framed `mut` cell in `ag(c)`, not `ex(c)` (an `ex` `mut` cell is not `▶◀` with an `imm` cell). Fact 2 then gives its ancestor in `ag(c)`. The ancestor is `⦇c⦈`'s cell at `m` (`ag_eq_flat_at_imm`) and lifts to `⦇ac⦈`.
  - If it is the run's part, the inner clause decides.

**Masks.** `¬E′` comes from the framed part through `hn`, or from the inner clause through the run's part.

## Appendix: status after R1, and the next step

**Built** (`Support/Model/Tree/World/UpdAFrame.lean`, axioms ⊆ [propext, Classical.choice, Quot.sound], entries in `scripts/AxiomCheck.lean`):
- Fact 2, `AgW.mut_beneath` (:100): under `MutOne W` and `CellAt ρ ⊆ CellAt W` at `mut` cells, every `mut` cell of `ag(ρ)` has `Beneath ag(ρ) m ζ n φ` with `φ` itself in the ancestor's walk. `nonimm_beneath_imm`'s `G.AgW.rec`, the motives carrying `MutIn (CellAt ρ)` so that `mutKeep_compR` follows the cell into the operand that carries it (`compR_mut_source`, `bigCompR_mut_source`).
- The `lsc` lemmas: `ImmLe`, `CellUT.CompR.immLe_left/right`, `imm_operand`, `imm_ls_le`; `cellAbs_compR` and `cellSub_compR` (an `imm` composite absorbed by, or absorbing, through each `imm` operand); `Beneath.lift`/`lift_right`.
- R1, `UpdA.frame` (:388). Hypotheses: the inner `UpdA`, `RR c c′`, `a ● c = ac`, `a′ ● c′ = ac′`, `✓ac`, `f′ ● ac′ = fw` (the end composite is a part of the end world), `NoneAt (MaskDiff E E′) c′`, `MutOne W` with `ac`'s `mut` cells in `W`, `MutOne W′` with `ac′`'s in `W′`. At `twp_frame` these are `hc₀`, `hρ′`, `cov_valid hc hI`, `hfρ′`, `g₁₀.of_compS_right`, `TWNT.mutOne hRi.1` with `hc`, `TWNT.mutOne g₆.1` with `hfρ′`. The cases are the appendix's above; the `not_xoptWFrameAt` configuration is the end-side branch "frame `mut`, run `imm`": the frame's cell is shown to be in `ag(c)` (an `ex(c)_●` cell cannot be `▶◀` with the run's `imm` cell, `Flat.split_factors`), then `AgW.mut_beneath`.

**Not derived: `UpdA.trans` (step 4).** I have not derived it and have not verified that any obstruction is real. The step that does not follow: the second segment's **end-side** ancestor disjunct gives `Beneath σ′ m ζ′ l ξ′` with no mask condition at `m`. When `¬E′ m`, the first segment's end side at `m` gives a start cell `ζ₀` with `RR ζ₀.wit ζ′.wit`, the walks re-read (`ExW.lsSim`/`AgW.lsSim`), and `Beneath σ m ζ₀ l ξ₀` with `XCell ξ₀ ψ″` follows. When `E′ m` (the middle ancestor is at a lent or escrow location of the run's own record), the first segment says nothing at `m`, and no start ancestor is produced. The start-side ancestor disjunct carries `¬E m`, so it composes; the end-side one does not.

Routes, none tried:
1. Re-anchor to an inner ancestor. If `ξ′` lies in `ex(ζ′.wit)_○` and `m ∈ recMask` because `m = p.le` with `ζ′.wit = p.R`, then `l ∈ ExDom p.R ⊆ E′`, against `¬E′ l`. Otherwise `ξ′` is in `ag(ζ′.wit)`, and `AgW.mut_beneath` inside the witness gives a strictly deeper ancestor; induct on depth until an unmasked one. Needs a resource fact discharged at `twp_bind` from `RecInv`: the flattening's `imm` cell at a record's lent location has the record's escrow as witness, and the case `m ∈ ExDom p.R` with an `imm` cell there is handled. Not checked.
2. Use the end world instead of the middle ancestor. When `ψ″` is in `ex(ρ″)`, `⦇fw″⦈(l) = ψ″` (`ex`/`ag` disjoint), which refutes the absorbed branch at `σ′(l)`. When it is in `ag(ρ″)`, `AgW.mut_beneath` at the end gives an end ancestor, but it may be masked by `E″`: the same question one segment later.
3. Add `¬E m` to the end-side disjunct. This breaks R1 where the frame's ancestor sits at a location masked on both sides (a frame copy of the run's lend cell). That would need route 1's re-anchoring inside `UpdA.frame` instead.

The mask obligation `XOptW.trans` names (R2) is dischargeable at `twp_bind` as planned: an `imm` cell of the middle world at `l` is the run's (the second segment's start side gives `¬E″ l`) or the frame's (`k₁₀`, `NoneAt (MaskDiff …) ρf₂`, gives `¬E″ l`). `UpdA.trans` also needs `MutOne` at the start (a middle `mut` cell leaving with its ancestor must be the start's cell beneath the start ancestor); `twp_bind` has it (`hR`).

**Then:** step 5 (`EndT` reads `UpdA`; `twp_frame`/`twp_frame_w` call `UpdA.frame` with the arguments above; `twp_here`, `twp_extend`, `twp_update` via `UpdX.toA`/an `UpdX.transA`), T1–T4, step 6, C-2 (`UpdX.frame` along the walks: `UpdA.frame`'s proof with the absorbed branches unused).

### Route 1 (chosen by the coordinator): progress and the next step

**Built** (`World/UpdAFrame.lean`):
- `ImmMaskClosed E ρ`: wherever a masked location holds an `imm` cell at any depth of `ρ`, every location of that cell's witness's `ex(−)_○` is masked.
- `AgW.mut_beneath_unmasked`: under `MutOne` and `ImmMaskClosed E ρ`, an unmasked `mut` cell of `ag(ρ)` sits beneath an **unmasked** `imm` cell of `ag(ρ)` whose walk carries it. It is the re-anchoring by induction on depth, as one `G.AgW.rec`: at a masked top `imm` cell, closure keeps the cell out of the exclusive walk, so it is in the witness's aliasable walk and the induction hypothesis applies.
- `RecMaskClosed : Prop` (elaborates): `RecInv w fρ ps ls → ρf ● ρ = fρ → SplitT ps O psF → ImmMaskClosed (recMask O) ρ`. It is stated and **not proved**.
- `ImmMaskClosed.nil`: the #793 configurations own no record (`O = []`), so the mask is empty and closed there.

**`UpdA.trans`, once `RecMaskClosed` holds.**
- **Side condition.** It takes `ImmMaskClosed E′ ρ′` at the middle resource. `twp_bind` discharges it from `g₆ : RecInv w₁ fρ₁ ps₁ ls₁`, `g₄`, `g₅`.
- **Hard case.** The second segment's end-side disjunct `Beneath σ′ m ζ′ l ξ′` is replaced by an unmasked one:
  - The cell `ξ′` is in `ag(ρ′)`, by `flat_imm_wit_factor` at `σ′(m)`, the cell exactly by `compR_mut_source`.
  - `AgW.mut_beneath_unmasked` gives an ancestor `m₂` with `¬E′ m₂`.
  - The first segment's end side at `m₂` gives `σ(m₂) = ζ₀` with `RR ζ₀.wit ζ₂.wit`.
  - The walks of `ζ₀.wit` re-read forward (`ExW.lsSim`, `AgW.lsSim`, and `lsRSim_comp` at `○`). `ExRT`/`AgWT`/`CompR` functionality identifies them with `ζ₂`'s, which gives `Beneath σ m₂ ζ₀ l ξ₀` with `XCell ξ₀ ψ″`.
- **Other obligations.** The start side needs start `MutOne` (`hR` at `twp_bind`). R2's mask obligation is discharged from `k₁₀`.

**Proving `RecMaskClosed`: the cases, by `TWNT` induction on the world.** Two locations can be masked:
1. **`y = p.le`.** Claim: every `imm` cell at depth at `p.le` has witness `p.R`. Then `ex(p.R)_○ ⊆ ExDom p.R` (a lemma `ExDom.of_exRT` is needed, as `ExDom.of_exST` exists for `●`).
   - At `immFrame`, validity leaves no other cell at `p.le`: a top `own` in `ex(W)_●` is not `▶◀` with any walk cell.
   - Later copies come from reborrow images of an outer escrow holding the lend cell. `reb_cell` gives an `imm` image over an `imm` source cell the source cell's witness, so the image's witness is `p.R`.
2. **`y ∈ ExDom p.R`, with an `imm` cell at `y` at depth.**
   - A reborrow image of `p.R` itself puts at `y` an `imm` cell over a piece `q ≤ p.R`, and `ExDom q ⊆ ExDom p.R` (to prove).
   - **The case not reconciled:** a `rebDeep` image over `w₀`, the witness of an `imm` cell at `l₀` reached by `ChainT` inside `p.R`. Its pieces' exclusive locations are in `dom w₀`, which `ExDom p.R` does not reach (`ExDom` descends only through `mut` witnesses). Whether `TWNT`/validity excludes `y ∈ ExDom p.R ∩ dom w₀` is not checked.
   - If that case is real, the closure should be stated at the walks rather than at `CellAt`. The induction only meets `imm` cells of `ρ` at the top and in `imm` witnesses, which is exactly `AgW.rec`'s `consI` case. The weaker closure is `ImmMaskClosed` restricted to cells reached through `imm` witnesses from a masked top cell. Before the `TWNT` proof, check whether that weaker form is what case 2 needs.
   - If it fails, the coordinator's instruction applies: build the configuration with every hypothesis discharged and stop.

**Order after that:** `UpdA.trans`; step 5; T1–T4; step 6; C-2; SPEC §62 and the D4/D5 rows. `scripts/check-judgments.sh` predates #798 on this branch, so it is skipped until the port onto `tree-core`.
