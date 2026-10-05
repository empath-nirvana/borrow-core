# WorldW — open lends handed across a stop (OQ-9 (a), OQ-3): design

**World of every result here: the W-draft `(ρ, ls, σ)`, with the closing obligation `τ` an index
beside it.** Nothing is proved yet. The draft definitions live in this experiment only; `Core/`
and every other experiment are untouched. A result here holds at the W-draft. It is not a result
at Core's relation (`σ = []`). It is not a result at Unit 3's `W` either, because this experiment
defines no relation at `W` (§1.10). GhostEnd (`experiments/GhostEnd`) is OQ-9 (b)'s evidence. It
is read, imported for `TabAt`, `tabAt_updV`, `ownerI`, `owner`, `viewP` and `wpG_box`, and never
redone.

**Scope.** The question is OQ-9 (a) for every printed frame a stop can hand on: `[TR]` 6.64,
6.65, 6.66, and a 6.150 record. It is asked on every path the continuation can take (resume,
cancel, drop), at a row that mixes them. It is also asked for a handler between two lenders, on
the resume, cancel and drop paths. That case is asked without a handler extent (OQ-3 (b)), and
with the rule a handler extent adds (OQ-3 (a)). The work is split into stages (§9). Each stage is
self-contained, has one deliverable and an exit rule, and the next stage starts from its outcome.

**Outside this unit, and why.**
- **OQ-57** (can `τ` be read off `W`?). The plan batches it with OQ-44, 46, 58 and 8 (plan, Order
  step 2.3). Its settling statement compares `ewpW` with a second fixed point. A probe limited to
  one draft relation cannot define that fixed point (FINDING-3, §8).
- **A semantic separation of OQ-3 (a) from (b).** The draft's `σ` is unordered, and the relation
  reads it only through the 6.64 selection. The extent appears only in (a)'s rule and in the body's
  table, and the relation does not enforce the rule's nesting obligation. So no end-to-end
  statement about a program's run can tell (a) from (b) in this draft (FINDING-2, §8). What the
  unit states instead (§3.4):
  - (a)'s rule obligation at the configuration;
  - where the extent acts at a stop;
  - what D-ORD (OQ-8) adds.
- **Operations whose argument or answer holds a borrow cell** (`ClosedOps`, §1.8).
- **Unrestricted continuations holding entries** (`NoUnr`, §1.6). Batch 3 owns that decision.

Sources read for this design:
- **Core:** `Core/EffDefs.lean`; `Core/EffWp.lean` (the three `wpG` frames, `wpG_bind`,
  `ewp_abortive`, `ewpTS_*_frameU`); `Core/EffRules.lean` (`ewp_handle`, `KapRel`, `ewp_ccatch`,
  `cancel_then`, `ewp_frame_then`, `VTy.Drop`); `Core/EffBorrow.lean` (`withborUE`, `ewp_unwind`,
  `ewp_box_end`, `withbor3U_compatX`); `Core/Compatibility.lean` (`withbor3_compatX`, 6.174);
  `Core/Fundamental.lean` (`effHandle`); `Core/World.lean` (`TW`, `Tagged`);
  `Core/FrameRecords.lean` (`Rel`, `Keeps`, `Ext`); `Core/Invariant.lean` (`TI`);
  `Core/Reborrow.lean` (`RebChooseTW`, `rebChooseTW_top`, `rebChooseTW_deep`, `tagged_rebEnd`);
  `Core/Compatibility.lean:134` (`rebChooseTW_pin`); `Core/Relation.lean` (`ptoMutS`, `ptoImmS`).
- **Paper:**
  - `Paper/S5_Model/Definitions.lean`: 5.20 `ExW`, 5.21 `AgW`, 5.22 `Flat`, `Hash`, `UpdImm`,
    `UpdMut`, `UpdV`, `FlatAt`, `InStratum`;
  - `Paper/S6_2_NonStandardLemmas/Definitions.lean`: `ResU.Sub`, `ResU.SubKeep`;
  - `Paper/S6_2_NonStandardLemmas/Lemmas.lean`: `six24`, `six28`, `flat_mut_own_agree_off`.
- **GhostEnd:** README, `Freeze`, `Relend`, `ImmLend`, `Frames`, `Nested`, `Drop`, `Chain`,
  `Table`, `Body`, `StackStep`.
- **`[TR]`:** printed statements and proofs of 6.24–6.29, 6.34, 6.38–6.43, Definition 6.2,
  6.45–6.50, Definition 6.3, 6.52–6.60, 6.62–6.66, 6.104, 6.108–6.112 and 6.146–6.150.
- **Docs:** `docs/effects-state/` (brief, 01, 02, 05a, 06) and the coarse plan. The draft spec's
  `05-model.md` (D-W, D-ORD, D-WPG, D-STOP, `ClosingInW`, T-FRAME, §12) and `99-open-questions.md`
  (OQ-3, 8, 9, 10, 44, 56, 57, 58) were read as questions, not as authority.

---

## 0. The question, and what a probe of it must not be

Under OQ-9 (a), a stop does not end the lends opened inside the run. A `[TR]` 6.64 frame, a 6.65
lend, a 6.66 anti-frame or a 6.150 record stays open. It is handed to the table with the
continuation. The question is whether every path the continuation can take closes it:

- **resume**: the continuation runs to the borrower's return, and the lender's exit closes the
  entry there;
- **cancel**: `[cancel]` unwinds the continuation to the lender's `ubind`. The entry must be
  closed there, before `[finalise-cancel]` gives the owner to the finaliser;
- **drop**: a later abortive operation of the same row unwinds through the lender's `ubind`;
- **between lenders**: a handler sits between two lenders and resumes, cancels or drops a
  continuation that holds the inner lend. This is asked with a handler extent (OQ-3 (a)) and
  without one (OQ-3 (b)).

OQ-9 (b) ends each lend at the stop and re-lends it at a fresh lifetime on resume. It is proved at
today's stop for:
- 6.65 (`ewpTS_M_frameR`, `withborR_compat`);
- 6.64 (`ewpTS_I_frameR`, `imm_spans_yield`);
- 6.66 (`ewpTS_M_antiFrameR`);
- the nested `withbor3` shape (`nested_relend`, `nested_spans_yield`);
- the cancel path (`spans_two_affine_yields`).

It is the comparison point.

A probe of (a) is none of the following, because each can be proved without (a):

1. **An end-to-end statement about a concrete borrower.** The relativised stop admits `τ′ = []`.
   A prover may end the lend at the stop and re-lend a borrower it can re-derive, which is (b).
   Every probe below takes the lend's borrower as an abstract premise at a fixed lifetime, whose
   continuation needs the view. Ending the lend at a stop is then not available.
2. **A statement at `σ = []`** (Core's `wpG`/`ewpTS`). T1 holds there by definition.
3. **A frame lemma whose borrower is re-lendable** (`RelendI`, `Relend`, `OpenS`). That is (b).
4. **A table with one kind of operation only.** A linear-resuming-only table makes `owedW`
   vacuous. An abortive-only table cannot have a continuation that crossed a resuming stop. The
   deliverables are stated at a table that mixes linear, affine and abortive operations (§3.1).
5. **A between-lenders statement that assumes the inner continuation closes its lend**, for
   example by taking `KapRelW … [e₂] κ` as a premise. The probe derives that `KapRelW` from the
   inner borrower's `ewpW` through the frame lemma and the handler's `[op]` case (§3.4).
6. **A statement whose obstruction lies in our own definitions rather than in (a).** These are:
   - our Kripke order (`Ext`, `ptoMutS`'s frozen list);
   - our `TW` constructors (`TW.rebEnd`'s stratum premise);
   - our closure (`Close`'s anti step, which chooses a split).

   The probes are split so that such an obstruction shows up separately:
   - §2 F-CLOSE, for the closure;
   - §3.1 `YoungerThan`, and §3.4 `…Out` against `…OutStable`, for the frozen list;
   - §3.3 the exit's typing, for `TW.rebEnd`.

---

## 1. The draft definitions

All of these live in `WorldW/Defs.lean`, namespace `WorldW`. They are built over:
- Core's `WRes`, `WProp`, `TW`, `Tagged`, `FrameRec`, `SRec`, `Rel`, `Keeps`, `Ext`, `OpEnt`,
  `OpTab`, `vC`, `ptoOwn`, `ptoImmS` and `ptoMutS`;
- Paper's `ResU.SubKeep` (`⊟`).

### 1.1 The entries

```lean
/-- An open entry: a lend open across a stop, or a handler marker. Lists of entries are innermost
first, in context order. -/
inductive OEnt where
  /-- [TR] 6.64: an open Imm frame, as `TW.immFrame` recorded it. `r.1 = ⟨ℓ, v, R, T, δ⟩` is in
  `ps`, its lineage is in `rsOf ls`, and `r.2 = α` is its lifetime, the tag of its records. -/
  | imm (r : SRec)
  /-- [TR] 6.65: an open Mut lend of the place `l` at the lifetime `α`, its payload read at
  `𝒱⟦T⟧δ`. It has no `ps` record: `TW.mutFold` keeps `ps`. -/
  | mut (l : Loc) (α : Life) (T : VTy) (δ : LSub)
  /-- [TR] 6.66: an open anti-frame on `l`. The cell `mut(β, v, ρ_P̂, P̂)` is unfolded to
  `own(v) ● ρ_P̂` for the body. The borrower's view was `Mut α 𝒱⟦T⟧δ`, with `α ⊑ β`. -/
  | anti (l : Loc) (α β : Life) (T : VTy) (δ : LSub) (P : Val → SPropS Loc Val β)
  /-- [TR] 6.150: an open reborrow of the view `l ↦ imm(s, w, σR)` at `β`, whose image is
  `χ ∈ reb_β(σR)`. -/
  | reb (l : Loc) (s : LSet) (w : Val) (σR : WRes) (hs : σR.InStratum s.join) (β : Life) (χ : WRes)
  /-- A handler site of the name `n`, with its extent under OQ-3 (a). The handler lemmas push it
  onto their body's stack. -/
  | hnd (n : UInt32) (h : Option Life)
```

Helpers:
- **Kind tests.**
  - `OEnt.isLend` holds of every kind except `hnd`.
  - `isImm`, `isMut`, `isAnti` and `isReb` test the kind.
  - `isMutAt l` holds of a `mut` entry at the place `l`; `IsAntiAt m` of an `anti` entry at `m`.
  - `OEnt.isHnd n` is a `Bool`. `OEnt` has no decidable equality, because `anti` carries a
    predicate.
- **Lifetimes.**
  - `OEnt.life? : OEnt → Option Life` is `r.2`, `α`, `α`, `β`, or `none` for `hnd`.
  - `OEnt.ordLife?` is `life?`, and `h` for `hnd n (some h)`. It is the order D-ORD would read
    (§3.4).
  - `OEnt.rebLife?` is `β` for a `reb` entry and `none` otherwise.
- **Records.**
  - `immRecs τ` is the 6.64 records of `τ`.
  - `LinOf e x`, for `e = imm (p, α)`, says that `x` is a record of `p`'s lineage tagged `α`, that
    is `DescR p x.1 ∧ x.2 = α`. For any other kind it is `False`.
- **Cells.** `CellU.ImmAt ψ γ` holds when `ψ` is an `imm` cell whose lifetime set holds `γ`:
  `∃ s, ψ.lsOf = some s ∧ s.mem γ`.
- **Footprints.** `OEnt.Consumes`, with its key type `OKey`, is in §2 (`holds_exclusive`).

What each entry records:

| kind | records | already in the world? |
|---|---|---|
| 6.64 frame | the record `p` and its lifetime `α` | yes: `p ∈ ps` (`TW.immFrame`), and `(p, α)` with its lineage in `ls` (`Tagged`). The entry is a selection, not new data (OQ-44's point (2)). |
| 6.65 lend | place, lifetime, payload type | no `ps` record. The world holds `mut(α, v″, χ, Q̂)` at `l`. F2 (§2) checks that the relativised `↭` puts every open 6.65 lend in `τ′`. |
| 6.66 anti-frame | place, the view's lifetime `α`, the cell's lifetime `β` and predicate `P̂`, payload type | the world holds `own(v) ● ρ_P̂` at `l` (`TW.mutUnfold`). `β` and `P̂` are what `↭` asks the refolded cell to keep (`UpdMut` fixes lifetime and predicate). |
| 6.150 record | the view `l ↦ imm(s, w, σR)`, the lifetime `β`, the image `χ` | `TW.reb` keeps `ps`. The image's cells `χ∣dom(σR∣mut,own)`, at `β`, are in the world. |

### 1.2 The exits as resource surgery

```lean
/-- 6.66's refold, without the pin: the unfolded `own(v) ● ρ_P̂` at `l` becomes
`mut(β, v, ρ_P̂, P̂)`, which needs `P̂(v)(ρ_P̂)` (H20–H25, 6.24, 6.28). `ρP` is the split. -/
def CloseEAnti (l : Loc) (β : Life) (P : Val → SPropS Loc Val β) (ρP π π' : WRes) : Prop :=
  ∃ (v : Val) (h : ρP.InStratum β) (hw : P v ⟨ρP, h⟩) (X rest : WRes),
    ResU.CompS (ResU.single l (CellU.ownOf v)) ρP X ∧ ResU.CompS X rest π ∧
    ResU.CompS (ResU.single l (CellU.mutOf β v ρP h P hw)) rest π' ∧ ResU.Valid π'

/-- The pin on an anti step. `ρP` holds no top-level `imm` cell at the lifetime of a `reb` entry
that closes after this step and before the next `mut` entry on `l`. That `mut` entry would unfold
`ρP` back to the top level. -/
def AntiPin (l : Loc) (τ : List OEnt) (ρP : WRes) : Prop :=
  ∀ e ∈ τ.takeWhile (fun e => !e.isMutAt l), ∀ β', e.rebLife? = some β' →
    ∀ m ψ, ρP.get m = some ψ → ¬ CellU.ImmAt ψ β'

/-- `π′` is `π` with `e`'s lender exit applied. `τ` lists the entries closed after `e`; only
the anti step reads it. -/
def CloseE (τ : List OEnt) : OEnt → WRes → WRes → Prop
  /- 6.64 (6.38/6.39): the view `imm({α}, v, R)` becomes `ℓ ↦ own(v) ● R`, and the result is
  valid. That is 6.38's G1, `π/ℓ # ρ_v ● ℓ ↦ own(v)`: composition and `✓` of the flattening. -/
  | .imm (p, α), π, π' => ∃ (h : p.R.InStratum (LSet.singleton α).join) (X : WRes),
      π.get p.le = some (CellU.immOf (LSet.singleton α) p.v p.R h) ∧
      ResU.CompS (ResU.single p.le (CellU.ownOf p.v)) p.R X ∧ ResU.CompS (π.del p.le) X π' ∧
      ResU.Valid π'
  /- 6.65 (6.27/6.28): `mut(α, v″, χ, Q̂)` becomes `ℓ ↦ own(v″) ● χ`. -/
  | .mut l α _ _, π, π' => ∃ (v : Val) (χ : WRes) (h : χ.InStratum α)
        (Q : Val → SPropS Loc Val α) (hw : Q v ⟨χ, h⟩) (X : WRes),
      π.get l = some (CellU.mutOf α v χ h Q hw) ∧
      ResU.CompS (ResU.single l (CellU.ownOf v)) χ X ∧ ResU.CompS (π.del l) X π' ∧ ResU.Valid π'
  /- 6.66: the refold, pinned. -/
  | .anti l _ β _ _ P, π, π' => ∃ ρP, AntiPin l τ ρP ∧ CloseEAnti l β P ρP π π'
  /- 6.150 (6.52, 6.59): the image's cells at `β` are a part of `π` (6.52's split,
  `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`), and they are subtracted, `π ⊟ χ∣dom(σR∣mut,own)` (Definition 6.3
  as printed, `ResU.SubKeep`). Without the first conjunct `⊟` would accept an absent image and
  subtract nothing. -/
  | .reb _ _ _ σR _ _ χ, π, π' => ResU.Le (χ.restrictDom σR.exclPart) π ∧
      ResU.SubKeep π (χ.restrictDom σR.exclPart) π' ∧ ResU.Valid π'
  | .hnd _ _, π, π' => π' = π

/-- The first `τ₁.length` steps of closing `τ₁ ++ τ₂`, innermost first. Each step's pin also reads
`τ₂`. -/
inductive ClosePre : List OEnt → List OEnt → WRes → WRes → Prop
  | nil (τ₂ : List OEnt) (π : WRes) : ClosePre [] τ₂ π π
  | cons {e : OEnt} {τ τ₂ : List OEnt} {π π₁ π' : WRes} :
      CloseE (τ ++ τ₂) e π π₁ → ClosePre τ τ₂ π₁ π' → ClosePre (e :: τ) τ₂ π π'

/-- Close the entries innermost first. This is the order the continuation closes them in. -/
abbrev Close (τ : List OEnt) : WRes → WRes → Prop := ClosePre τ []

/-- `ρ` can close `τ` by itself: everything the exits read is in `ρ`. -/
def Holds (τ : List OEnt) (ρ : WRes) : Prop := ∃ ρc, Close τ ρ ρc
```

`close_append : Close (τ₁ ++ τ₂) π π′ ↔ ∃ π₁, ClosePre τ₁ τ₂ π π₁ ∧ Close τ₂ π₁ π′` is the
bookkeeping lemma every split uses.

**Closure choice.** The 6.64, 6.65 and 6.150 steps are functions of their input:
- `ResU.CompS.functional` (`Support/Model/Composition.lean:213`);
- `CellU.mutOf_at` and the cell's injectivity (`Support/Model/CellFacts.lean:60`);
- `ResU.SubKeep.functional` (`Support/Model/Subtraction.lean:325`).

The anti step chooses the split `ρ_P̂`. What that choice can and cannot change:

- **It cannot move a cell out of the flattening.** `ResU.flat_mut_own_agree_off`
  (`Paper/S6_2_NonStandardLemmas/Lemmas.lean:679`) is the comparison in 6.28's printed proof. It
  holds for every split `(rest, ρ_P̂)`: the flattening of `rest ● ℓ ↦ mut(β, v, ρ_P̂, P̂)` agrees
  with that of `rest ● ρ_P̂ ● ℓ ↦ own(v)` at every location but `ℓ`.
  - The reason is 5.20 and 5.21. The exclusive walk includes `ex(ρ_P̂)`, so the `own` and `mut`
    cells of `ρ_P̂` are in it. The aliasable walk includes `ag(ρ_P̂)`.
  - So a cell the refold moves into `ρ_P̂` keeps its place, kind, lifetime and predicate in `⦇·⦈`.
    A top-level `mut` cell taken into `ρ_P̂` is still in `⦇ρc⦈`, and `UpdMut` still fixes its
    lifetime and predicate.
- **It can hide an `imm` copy from a later subtraction.** `imm` cells split idempotently (6.43).
  So the refold can put a copy of an `imm` cell into `ρ_P̂` while the top level keeps one.
  - Suppose the copy is a 6.150 image cell of a `reb` entry closed later in the chain. That
    entry's exit is Definition 6.3's `⊟`, which subtracts only the top-level copy. The copy in
    `ℓ`'s witness survives into `⦇πc⦈`.
  - Two closures of one resource then differ under `UpdImm` at that location.
  - Absorbing anything else does no harm. Either `⦇·⦈` is unchanged, or a later step becomes
    undefined: a later 6.64, 6.65 or 6.66 exit needs its cell at the top level. A 6.64 exit that
    leaves a copy of its view in a witness gives an invalid result, and `CloseE`'s `✓` conjunct
    excludes it.
  - `UnpinnedIncoherent` (§2) states this at a concrete resource. It is about our `Close`, not
    about (a).
- **The pin removes that case.** `AntiPin` forbids `ρ_P̂` any top-level `imm` cell at the
  lifetime of a `reb` entry closed after the anti step. The pin stops at the next `mut` entry on
  the anti's place, because that entry's exit unfolds `ρ_P̂` back to the top level before any
  later step.
  - **Where the pin is harmless.** Take a `reb` closed after the anti, with lifetime `β′` below the
    anti's cell lifetime `β`. Then `ρ_P̂ ∈ Res_β` cannot hold the `reb`'s image cells anyway
    (`pin_harmless`, under `OblWf`, §1.8).
  - **Where it would bite.** The pin would remove a legitimate split only for a `reb` older than
    the anti's cell, with the cell's lend outside `τ`. That is a cell younger than a reborrow, lent
    outside the run that holds the reborrow. It needs a younger `mut` view passed into that run,
    and `ClosedOps` excludes that.
  - That `OblWf` holds at every arising stop is a reading (§7, reading 7), checked at the instances.
- **Coherence.** With the pin, `close_flat_agree` and `close_upd_coherent` (§2) are expected to
  hold at every resource, with no premise. Conjunct (37) then does not depend on which closures a
  run picks (`upd_choice_free`). No later stage starts before they are proved (§9).

`Close` is in context order, not lifetime order; §3.4 shows the two differ between lenders.

**One place, two entries.** `withbor3` (6.174, `withbor3_compatX` / `withbor3U_compatX`) runs
6.66, then 6.65, on the same place. Inside a borrower holding `Mut α₀` at `ℓ`:
- 6.66 opens `anti ℓ α₀ β T δ P̂`, where `β ⊒ α₀` is the cell's lifetime;
- 6.65 then lends the unfolded content at a fresh `α`.
  - The entry takes `α` below every lifetime of `W`, the anti entry's `α₀` and `β` included
    (`relend_below_anti`, §2).
  - The printed H4 picks "some `α ⊏ γ ⊓ β`", and any smaller `α` is such a lifetime. So the order
    comes from the printed И freshness, spent at the entry.
  - The bound `∀'x ⊏ ⊓Δ` of `withbor3`'s callback type is the surface reason for the same order.

At a stop inside the callback the entries are `[…, mut ℓ α T δ, anti ℓ α₀ β T δ P̂, …]`. `Close`
handles them in that order:
1. `mut(α, v″, χ, Q̂) ↦ own(v″) ● χ`;
2. then `own(v″) ● χ ↦ mut(β, v″, χ, P̂)`, which needs `P̂(v″)(χ)`.

The reverse order is undefined: the anti exit needs an `own` cell at `ℓ`, and the cell there is
`mut`. `close_relend_anti` (§2) states both directions.

### 1.3 The σ-component of `#`

```lean
/-- `ρf` is compatible with every closure of `ρ` by `τ`, and inert under it: closing the composite
is closing the part. This is the lender's virtual ownership as a component of `#` at `W`. -/
def CompatW (τ : List OEnt) (ρf ρ : WRes) : Prop :=
  ∀ ρc, Close τ ρ ρc → ResU.Hash ρf ρc ∧
    ∀ X, ResU.CompS ρf ρ X → ∃ Xc, Close τ X Xc ∧ ResU.CompS ρf ρc Xc
```

**Where it comes from.** It is not a free-standing guard. Several printed proofs carry a
hypothesis that the rest of the resource is compatible with the *owned* form of the lent place:
- 6.29, 6.38 and 6.39 have H1, `ρ # ρ_v ● ℓ ↦ own(v)`;
- 6.39 also has H2, `ρ′ # ℓ ↦ own(v) ● ρ_v`;
- 6.64 has H14, `ρ_f # ρ_ℓ ● ρ_P̂(v)`, which feeds H30's 6.15 at the exit.

In the printed 6.64 the inner run's frame meets H14 because it was the lender's frame at the
entry. Under (a) the exit happens in a later run, whose frame is a different frame: the
resumer's frame. For the printed exit to apply there, that frame must still meet H14. `CompatW`
is H14 carried by the world, for every entry a later run closes.

**What it excludes.** `#` is `▸◂` plus `✓` of the flattening (5.26), so `CompatW` excludes copies
of an entry's view at the flattening:
- a top-level copy at `p.le`;
- a copy nested in another cell's witness, as in F0's configuration (§2, §5);
- an `imm` copy of a payload cell, for example a `TW.reb` view at `β` of `p.R`;
- for a 6.150 record, a copy of an image cell outside the share. The inert half rejects this
  one: `⊟` on the composite would subtract the copy as well.

At `τ = []`, `Close [] ρ ρc ↔ ρc = ρ`, so `CompatW [] ρf ρ ↔ ResU.Hash ρf ρ`. By
`close_upd_coherent` the closures `CompatW` ranges over are `↭`-related to one another.

**Where it bites** (F1, §2). At `mut` and `anti` entries `CompatW` is `Hash`, by 6.24. That
lemma is an iff between the `mut` cell and its unfolded `own(v) ● ρ_v`. At `imm` entries 6.34 is
one-directional, and at `reb` entries `⊟` subtracts only what the composite holds. So `CompatW`
is a real restriction at `imm` and `reb` entries only. §2 F0 shows it is necessary at `imm`
entries, at an arising configuration.

### 1.4 The two stacks: `τ` and `σ`

- **`τ`** is the closing obligation. It lists the entries the run must close by the time it
  returns a value. It is empty except for a resumed continuation, a cancel run, or a clause
  that holds `κ`.
- **`σ`** is the stack of entries open around the run and held by outer runs, innermost first,
  with handler markers. It is GhostEnd's `LStack` with the lifetimes folded into the entries
  (D-W).

**The plan's names.** The plan says Unit 3's `↭` is "read relative to the closure of `σ′`". There,
`σ′` is the entries a stop leaves open and hands on: this design's `τ′`. This design's `σ` is the
stack outside them. It is not closed in (37), so outer views stay verbatim under `↭`.

How they move:
- **A lend's entry lemma** runs its borrower at `e :: σ`.
- **A handler lemma** runs the body at `hnd n h :: σ`.
- **The split bind** (§4.2) runs an inner sub-computation at `τ₂ ++ σ` when the obligation `τ₂`
  stays with the outer context.

**`τ′` and `σ′` at a stop.** A stop leaves `σ` unchanged. The stopped term sits under `τ′ ++ σ`.
The frame lemma that lifts a borrower's stop to its lender re-indexes it: the borrower's
`(τ′_b, e :: σ)` becomes the lender's `(τ′_b ++ [e], σ)`. The handler of `n` receives the stop
at `σ_hnd`, the stack outside its marker. Its clause runs at `(τ′, σ_hnd)`, and `κ`'s run
at `(τ′, extra ++ σ_hnd)` for every `extra`. For example, the clause may call `κ` inside a lend
of its own.

**`σ` is unordered here, and read only through the 6.64 selection.**
- `σ` is in context order. The draft imposes no lifetime order on it: D-ORD's `Wf` is not
  imposed.
- `wpGW` reads `σ` only through D-WPG's selection premise, `∀ p ∈ immRecs σ, p ∈ ps`. A larger `σ`
  restricts the frame quantifier further. So `ewpW τ σ ⊨ ewpW τ σ′` whenever
  `immRecs σ ⊆ immRecs σ′` (`ewpW_σmono`, §4.2).

Consequences:
- `KapRelW`'s quantifier over `extra` costs nothing. OQ-8's question of where a quantifier over
  `σ`-extensions sits does not arise in this unit. A relation at `W` that reads `σ` (`TabAt`,
  D-REL) would make it arise.
- The obstruction OQ-3's box names cannot arise in this draft. A handler between lenders has no
  place in a lifetime-ordered `σ` (GhostEnd's `AllCross`, `StackStep.lean:182`). Every
  between-lenders result here is for an unordered `σ`, so it is conditional on D-ORD (OQ-8); §3.4
  states what D-ORD would add.
- The lemmas push entries along a configuration's run, and that run fixes `σ`'s order. Nobody
  writes `σ` down by hand.

### 1.5 The relativised stop

`wpGW τ σ ls e Q` is `wpG` (`Core/EffDefs.lean:27-40`) for a run that holds the obligation `τ`
under `σ`. Conjunct by conjunct:

| `wpG` | `wpGW τ σ` | why |
|---|---|---|
| frame: `ResU.Hash ρf ρ` | verbatim, and `CompatW τ ρf ρ` | the σ-component of `#` (§1.3). At `τ = []` it is `Hash`. |
| frame: `TW fρ ps (rsOf ls)`, `Tagged fρ ps ls` | `TW fρ (immRecs τ ++ ps) (rsOf ls)`, `Tagged …`, and `∀ p ∈ immRecs σ, p ∈ ps` | the frames the run holds are open at its start. `σ`'s frames are among the others (D-WPG). |
| run, memories, `#` | verbatim | |
| (37) `ρ ↭ π` | `Close τ ρ ρc ∧ Close τ′ π πc ∧ ρc ↭ πc` | read relative to the closures of `τ` and `τ′` (the plan's `σ′` is `τ′`, §1.4). The outer `σ` is not closed. At `τ = τ′ = []` it is `ρ ↭ π`. Which closures a run picks does not matter (`upd_choice_free`, §2). It owes 6.48 (framing) and 6.49 (transitivity) through `Close` (§4.2). |
| (38) `NoOwn ρp` | kept | leak freedom |
| (39) `TW fρ'p ps' (rsOf ls')`, `Tagged` | kept | arising |
| (40) `ps′ ≡ ps ∧ ls′ ≡ ls` | `StopW` below | (40) is T1, and the plan removes it. `StopW` is OQ-10 option (a)'s replacement: a value clause, a stop clause, a freshness clause and two `CompatW` clauses. |
| `Q ls′ t ρ′` | `Q τ′ ls′ t ρ′` | the table learns which entries stay open |

```lean
/-- The stop condition at `W`. The run started at `immRecs τ ++ ps`, holding `τ`.
* at a value: nothing stays open; `τ`'s frames leave the frame list and their lineages leave the
  record list (`[TR]` p. 6's `wp`: every frame the run held or opened is closed);
* at any other term: the open 6.64 frames are `immRecs τ′` with the outer ones; the list keeps its
  records except those of `τ`'s closed entries, and gains only `τ′`'s; a 6.64 entry the run opened
  is younger than every record present at both ends; the frame and the leftover are compatible
  with the closure (§1.3).
Every clause is about membership. A frame list that repeats a record of `τ` is harmless: closing
the entry removes every copy (`TW.immEnd`), and the clause subtracts `immRecs τ` instead of
asking for disjointness. -/
def StopW (τ : List OEnt) (ps ps' : List FrameRec) (ls ls' : List SRec) (t : Expr)
    (τ' : List OEnt) (ρf ρp ρ' π : WRes) : Prop :=
  ((∃ v : Val, t = .val v) →
      τ' = [] ∧ (∀ p, p ∈ ps' ↔ (p ∈ ps ∧ p ∉ immRecs τ)) ∧
      (∀ x, x ∈ ls' ↔ (x ∈ ls ∧ ∀ e ∈ τ, ¬ LinOf e x))) ∧
  ((¬ ∃ v : Val, t = .val v) →
      (∀ p, p ∈ ps' ↔ (p ∈ immRecs τ' ∨ (p ∈ ps ∧ p ∉ immRecs τ))) ∧
      (∀ x, x ∈ ls' ↔ ((x ∈ ls ∧ ∀ e ∈ τ, e ∉ τ' → ¬ LinOf e x) ∨ ∃ e ∈ τ', LinOf e x)) ∧
      (∀ q, OEnt.imm q ∈ τ' → OEnt.imm q ∉ τ → ∀ x ∈ ls, x ∈ ls' → q.2 ⊏ x.2) ∧
      CompatW τ' ρf π ∧ CompatW τ' ρp ρ')

def wpGW (τ σ : List OEnt) (ls : List SRec) (e : Expr)
    (Q : List OEnt → List SRec → Expr → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → CompatW τ ρf ρ →
    ResU.CompS ρf ρ fρ → TW fρ (immRecs τ ++ ps) (rsOf ls) → Tagged fρ (immRecs τ ++ ps) ls →
    (∀ p ∈ immRecs σ, p ∈ ps) →
    ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π ρc πc : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec) (τ' : List OEnt),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧ ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      (∃ k', ARun A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ Close τ ρ ρc ∧ Close τ' π πc ∧ ResU.UpdV ρc πc ∧
      NoOwn ρp ∧ TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      StopW τ ps ps' ls ls' t τ' ρf ρp ρ' π ∧ Q τ' ls' t ρ'
```

**Kernel definition changes this draft makes.** Each needs a SPEC entry (E-W) before kernel
work. The plan already records that the stop condition is one (Unit 3; BRIEF §5).
1. **The frame quantifier.** It gains `CompatW τ ρf ρ`, the σ-component of `#`, and the
   selection premise `∀ p ∈ immRecs σ, p ∈ ps`.
2. **Conjunct (37).** It is read relative to `Close`, with the anti step pinned (§1.2).
3. **`StopW` in place of (40).** It has:
   - the value clause;
   - the stop clause;
   - the freshness clause;
   - `CompatW τ′ ρf π`;
   - `CompatW τ′ ρp ρ′`.
4. **The table's checks at a stop.** These are `Holds τ′ ρk` and `CompatW τ′ ρa ρk` (§1.6).
5. **Under OQ-3 (a) only.** `extTabW` and `ExtentOK` at `[handle]` (§1.6, §3.4).

Four conjuncts of `StopW` are not in D-STOP and need saying:

- **`CompatW τ′ ρf π`** is a guarantee about the frame the run was handed. For an entry the run
  opened, it is the entry lemma's H14, kept by 6.38 at the stop. For an inherited entry, it comes
  from `CompatW τ ρf ρ` and the hand-on step (§4.3 (iii)). A resumer's frame inherits it
  (`compat_at_stop`, §2).
- **`CompatW τ′ ρp ρ′`** keeps copies of an open entry's view out of the leftover. The leftover
  joins the next run's frame, and a copy there would block the exit (§2 F0). A view a borrower
  drops is moved into `ρ′` instead (`imm` cells compose idempotently, 6.43), and 6.149 carries it
  as dead weight.
- **The freshness conjunct** is what `exists_fresh` gives every entry lemma: a lifetime below
  every tag present. It keeps `YoungerThan` (§1.8) along a frame lemma's induction (§2,
  `younger_preserved`).
- **The value clause removes `τ`'s records from the list.** Core's 6.64 exit does the same with
  `ext_drop` (`Core/FrameRules.lean:302`).

### 1.6 Tables and `ewp` at `W`

```lean
/-- A continuation: `Φ τ σ ls e`, the run of `e` holding `τ` under `σ`. -/
abbrev ContW := List OEnt → List OEnt → List SRec → Expr → WProp
/-- A table: the stopped run's stack, the list, the entries `τ′` the stop left open, the stopped
term, and the continuations owed. -/
abbrev TableW := List OEnt → List SRec → List OEnt → Expr → ContW → WProp

def ewpStepW (Tb : TableW) (Q : List SRec → Val → WProp) (P : ContW) : ContW :=
  fun τ σ ls e => wpGW τ σ ls e (fun τ' ls' t ρ =>
    (∃ v : Val, t = .val v ∧ τ' = [] ∧ Q ls' v ρ) ∨ Tb σ ls' τ' t P ρ)

/-- The least fixed point, in `Prop`, as `ewpTS` (`Core/EffDefs.lean:73`). -/
def ewpW (τ σ : List OEnt) (ls : List SRec) (e : Expr) (Tb : TableW)
    (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ P : ContW, (∀ τ σ ls e ρ, ewpStepW Tb Q P τ σ ls e ρ → P τ σ ls e ρ) → P τ σ ls e ρ

/-- A cancel run ends at the cancel with nothing open. -/
def cancelTabW (T : OpTab) (N : List UInt32) : TableW := fun _ ls τ' t _ ρ =>
  τ' = [] ∧ cancelTab T N ls t (fun _ _ _ => False) ρ

/-- `Table.withFr` at `W`: the stop also hands back the frame `Fr`. -/
def withOwnerW (Tb : TableW) (Fr : List SRec → WProp) : TableW :=
  fun σ ls τ' t Φ => Tb σ ls τ' t Φ ⋆ Fr ls

def owedW (Tc : List UInt32 → TableW) (n : UInt32) (σ : List OEnt) (ls : List SRec)
    (τ : List OEnt) (K : Kont) : WProp := fun ρ =>
  ∀ N : List UInt32, n ∈ N → (∀ m ∈ K.hndNames, m ∈ N) →
    ewpW τ σ ls (K.plug (raiseE (.val (cancelVal N none)))) (Tc N) (fun _ _ _ => False) ρ

def shareW (Tc : List UInt32 → TableW) (en : OpEnt) (n : UInt32) (σ : List OEnt)
    (ls : List SRec) (τ' : List OEnt) (K : Kont) (Φ : ContW) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty ∧ τ' = []) ∧                       -- assumption, owned by batch 3
  ∀ ls', Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆ Φ τ' σ ls' (K.plug (.val w))) ρ) ∧
    (en.q ≠ .lin → owedW Tc n σ ls' τ' K ρ)

/-- The protocol table of `T` at `W`. A stop that closes the entry hands back the frame `Fr`.
`Fr` is `emp` for a borrower's own table, and the lender's place in a frame lemma's
conclusion. -/
def opTabW (T : OpTab) (Fr : List SRec → WProp) : TableW := fun σ ls τ' t Φ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
          T n i = some en ∧ en.abort = false⌝ ⋆
        fun ρ => ∃ ρa ρk, ResU.CompS ρa ρk ρ ∧ en.PA ls v ρa ∧
          shareW (fun N => withOwnerW (cancelTabW T N) Fr) en n σ ls τ' K Φ ρk ∧
          Holds τ' ρk ∧ CompatW τ' ρa ρk)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true ∧ τ' = []⌝ ⋆
          (((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ) ⋆ Fr ls))

abbrev opTableW (T : OpTab) : TableW := opTabW T (fun _ => emp)

/-- OQ-3 (a): the table of a handled body at the handler's extent `h`. Every lend a stop hands to
the handler was opened below `h`: an `anti` entry opens no lifetime, and may unfold a view from
outside. The stop's resource is in `Res_h` once the entries are closed. That is 6.147 read
relative to `Close`; GhostEnd's `wpG_box`/`frozen_above_extent` are its form at today's stop. -/
def extTabW (h : Life) (Tb : TableW) : TableW := fun σ ls τ' t Φ ρ =>
  (∀ e ∈ τ', e.isAnti = false → ∀ β, e.life? = some β → β ⊏ h) ∧
  (∀ ρc, Close τ' ρ ρc → ρc.InStratum h) ∧ Tb σ ls τ' t Φ ρ

/-- The relation of `κ` at an operation's entry. `κ` holds `τ`. It may be called under any
extension of the handler's stack, at every extension of the list, when the re-entry condition
`re` holds at the call. `re` is `fun _ _ _ => True` without a handler extent (OQ-3 (b)), and
`ExtentOK h τ` when the reinstalled handler re-enters at the extent `h` (OQ-3 (a), §3.4). -/
def KapRelW (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt)
    (re : List OEnt → List SRec → WRes → Prop) (σ : List OEnt) (ls : List SRec)
    (τ : List OEnt) (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty ∧ τ = []) ∧                         -- assumption, owned by batch 3
  ∀ (extra : List OEnt) (ls' : List SRec), Ext ls ls' ρ →
    (∀ w : Val, (en.PB ls' w ─⋆ fun ρ' => re (extra ++ σ) ls' ρ' →
      ewpW τ (extra ++ σ) ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))
        (opTableW Tout) Qout ρ') ρ) ∧
    (en.q ≠ .lin → re (extra ++ σ) ls' ρ →
      ewpW τ (extra ++ σ) ls' (.app κ.1 (.val (Val.inj₂ .unit))) (opTableW Tout)
        (fun _ v => ⌜v = Val.unit⌝) ρ)

abbrev KapRelWB (Tout : OpTab) (Qout : List SRec → Val → WProp) (en : OpEnt) :=
  KapRelW Tout Qout en (fun _ _ _ => True)
```

**The checks at a stop** (`opTabW`'s perform clause):
- **`Holds τ′ ρk`.** The continuation's share can close its entries by itself. This keeps every
  entry's cells in the share. For a 6.66 entry these are the unfolded `own` cell and its payload.
  `ClosedOps` allows `PA` to carry `own` cells, so without this check a stop could hand a lent
  place's owned cell to the handler.
- **`CompatW τ′ ρa ρk`.** The argument is compatible with the closure and inert under it.

The answer `PB` needs no check of its own. Under `ClosedOps` it holds only `own` cells, and an
`own` cell at an entry's place, or at a place of a 6.64 payload, makes `ρk ● PB` invalid (6.41,
6.42; 6.35 at the flattening). The `ewpW` it is handed to is then vacuous. The leftover is checked
by `StopW` (`CompatW τ′ ρp ρ′`). §2 `holds_exclusive` derives exclusivity at a stop from `Holds`.

**At an abortive entry and in `cancelTabW`, `τ′ = []`.** A raise reaches the table only after
every `ubind` in its context has caught it (`Kont.Catches` holds at every `ubind`,
`Paper/S3_Dynamics/Definitions.lean:397`). So every lender between the raise and the table has
already closed its entry.

**Unrestricted continuations.** `shareW` and `KapRelW` have a conjunct `en.q = .unr → … τ′ = []`:
an unrestricted continuation holds no entry.
- This is **an assumption of the draft, owned by batch 3** (plan step 2.3: whether a `!` value or
  an unrestricted continuation may hold an entry of `σ`).
- No conclusion of this unit depends on it. Every deliverable is stated at a table with no `unr`
  operation (`NoUnr`, §1.8), so the conjunct is vacuous wherever a deliverable reads it.
- The report states that the results say nothing about `unr` continuations holding entries.

**`τ` moves:**
- a stop hands `τ′` to the table (`StopW`, `Q τ′`);
- the table hands it to the continuation (`Φ τ′ σ`, `owedW … τ′`);
- `[op]` hands it to the clause, because the clause holds `κ`. `ewp_handle_W` (§3.4) gives the
  clause `(PA ⋆ KapRelWB … σ_hnd ls τ′ κ)`, and asks for `ewpW τ′ σ_hnd … (c (v, κ))`.

**Linearity of a `κ` that holds entries.** The stop condition does not force a clause to resume
or cancel `κ`.
- **What the relation admits.** A clause's run holding `τ′ = [e₂]` can reach a value without
  running `κ`.
  - It closes `e₂` by the printed exit as resource reasoning: 6.38 at its final resource, and
    `TW.immEnd`.
  - It keeps `ℓ₂ ↦ own(v₂)` in its answer. `NoOwn` keeps the cell out of the leftover, so the
    answer is where it goes.
  - That needs a postcondition that accepts the cell. `dropKappa_by_surgery` (§2) states this for
    the clause `λp. ()`.
- **What prevents it in programs.**
  - Typing: `U C` is not `VTy.Drop` (`Core/EffRules.lean:815`), so `[let]` cannot weaken `κ`.
  - Tight postconditions: a top-level postcondition such as adequacy's `()` with an empty resource
    cannot absorb an owned inner place.
- **Where the probes stand.** The between-lenders clauses (§3.4) are concrete code that calls or
  cancels `κ`. Their runs execute `L₂`'s code whatever `Q` is, so the probes keep `Q` general, the
  stronger statement.
- **Where it is not settled here.** A clause read only through a relation (T-FP at `W`) gets its
  linearity from typing, not from this relation. That is recorded with FINDING-1.

### 1.7 The open-entry invariant

A continuation that holds an open entry starts from a resource the entry made, in a state every
stop re-establishes:

```lean
/-- `e` is open over `ρ`, and the continuation also holds its inner entries `τi`. -/
def OpenInv (τi : List OEnt) (ls : List SRec) : OEnt → WRes → Prop
  /- 6.64: after closing `τi`, `ρ` agrees with the lend table at `(p.le, α)` (`GhostEnd.TabAt`:
  every borrow cell `⊒ α`, every one off `p.le` strictly above). The exit is defined (G1), and the
  payload is in `𝒱⟦T⟧` at the current list. -/
  | .imm (p, α), ρ => ∃ ρi ρe, ClosePre τi [.imm (p, α)] ρ ρi ∧ GhostEnd.TabAt p.le α ρi ∧
      CloseE [] (.imm (p, α)) ρi ρe ∧ vC true p.T ls p.δ p.v p.R
  /- 6.65: after closing `τi`, `ρ` holds the lend's own cell `mut(α, …)` at `l` as `ptoMutS`
  reads it at the current list, and the rest is strictly above `α`. -/
  | .mut l α T δ, ρ => ∃ ρi ρv ρr, ClosePre τi [.mut l α T δ] ρ ρi ∧ ResU.CompS ρv ρr ρi ∧
      ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρv ∧
      (∃ v χ h Q hw, ρv = ResU.single l (CellU.mutOf α v χ h Q hw)) ∧ ρr.InStratum α
  /- 6.66: after closing `τi`, refolding at `l` gives back the borrower's view
  `ℓ ↦ Mut α 𝒱⟦T⟧δ` as `ptoMutS` reads it at the current list. -/
  | .anti l α β T δ P, ρ => ∃ ρi ρm ρv ρr, ClosePre τi [.anti l α β T δ P] ρ ρi ∧
      CloseE [] (.anti l α β T δ P) ρi ρm ∧
      ResU.CompS ρv ρr ρm ∧ ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρv ∧
      ∃ v χ h hw, ρv = ResU.single l (CellU.mutOf β v χ h P hw)
  | .reb .., _ => False      -- 6.150's view sits beside the borrower: `OpenInvReb`
  | .hnd .., _ => True

/-- 6.150: the continuation holds the view `ρ_i = l ↦ imm(s, w, σR)` beside `X`, the borrower's
resource. After closing `τi` (with the reborrow still to close), `X` holds the image:
* `χ ∈ reb_β(σR)` (H16);
* subtracting the image's cells at `β` (Definition 6.3's `⊟`) leaves `Xr`, of which the image is
  the rest (6.52's split at the entry);
* `Xr` is strictly above `β` (H15, and 6.52's `@(ρ⁺ ⊟ ρ_reb) ⊐ β`);
* `X` is compatible with the view (H18–H20, 6.55). -/
def OpenInvReb (τi : List OEnt) (l : Loc) (s : LSet) (w : Val) (σR : WRes)
    (hs : σR.InStratum s.join) (β : Life) (χ : WRes) (X : WRes) : Prop :=
  ResU.Reb β σR χ ∧
  ∃ Xc Xr, ClosePre τi [.reb l s w σR hs β χ] X Xc ∧
    ResU.SubKeep Xc (χ.restrictDom σR.exclPart) Xr ∧
    ResU.CompS Xr (χ.restrictDom σR.exclPart) Xc ∧
    Xr.InStratum β ∧
    ResU.Hash (ResU.single l (CellU.immOf s w σR hs)) Xc
```

Each conjunct is something the printed entry provides and a printed lemma keeps:

| conjunct | at the entry (`[TR]`) | kept at a stop by |
|---|---|---|
| `TabAt` (6.64), rest above `α` (6.65) | H10/H11 | 6.50 (`GhostEnd.tabAt_updV`) on the relativised `↭`: the borrow cells of the flattening keep their lifetimes, and new entries' cells are closed away |
| the image is a part of `Xc`, and `Xc ⊟ image` is above `β` (6.150) | H15, H16 | 6.52 at each stop's closed resource, whose hypotheses are the borrower's run's `↭` and the two strata; 6.50 for the strata |
| exit defined | H12, 6.34 / 6.24; 6.66 H8 | 6.38 at the stop (6.64); 6.24 (6.65, 6.66) |
| `X # ρ_i` (6.150) | H18–H20, 6.55 | 6.55 at the stop's image, and 6.48 for the rest |
| payload in `𝒱⟦T⟧` at the list | H8; 6.66 H6 | `vC_local` along the share's `Ext` (records strictly longer-lived than a borrow cell of the share are frozen). Along a stop's own list change it needs `YoungerThan` (§1.8): closing a younger entry removes only records tagged below `α`. |
| the 6.65/6.66 cell as `ptoMutS` reads it | `ptoMutX_create`; 6.66 H5 | `Ext` at a resource holding the cell keeps `ls∣⊐b`. Under `YoungerThan`, so does a stop's own change of list. |

**The lineage in the list is not carried.** Each unfolding supplies it from its frame premise:
- `TW fρ (immRecs τ ++ ps) (rsOf ls)` puts every record of `p`'s lineage in `rsOf ls`. That is
  `TI`'s lineage closure of the frame list (`Core/Invariant.lean`).
- `Tagged` with `frameLife_eq` fixes each record's tag at `α`.

A resumer's list `ls′` meets the same premise when the continuation's `ewpW` is unfolded there. So
nothing about the lineage has to survive `Ext`. `Ext` keeps only records relevant to the share
(`Core/FrameRecords.lean:156`), and `p`'s sub-records tagged `α` need not be relevant to it.

**No "`α` tags only `p`" conjunct.** The exit's `frameLife_back` step asks that the record
tagging each `x` of the exit list is not `p`. It follows from `StopW`'s value clause.
1. `x ∈ ls′` gives `¬ LinOf e x`.
2. Suppose `Tagged`'s witness for `x` were `p`. Then `DescR p x.1`.
3. `frameLife_eq` gives `x.2 = α`.
4. So `LinOf e x`, a contradiction.

`openInv_entry` (one per kind, §4) is the entry establishing `OpenInv`. That is what makes it an
invariant, not an assumption.

### 1.8 Table and payload conditions

```lean
/-- R-CLOSEDOP (OQ-56 (a)): arguments and answers own every cell they hold and borrow none
(D-TABLEOK (3)–(4)). -/
def ClosedOps (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → ∀ ls v ρ (α : Life),
    (en.PA ls v ρ → ρ.InStratum α) ∧ (en.PB ls v ρ → ρ.InStratum α)
/-- No operation's continuation is unrestricted: batch 3 decides whether such a continuation may
hold an entry (§1.6). -/
def NoUnr (T : OpTab) : Prop := ∀ n i en, T n i = some en → en.q ≠ .unr
/-- The operations of `n` resume, at the qualifier `q`. -/
def OpAt (T : OpTab) (n : UInt32) (q : Qual) : Prop :=
  ∀ i en, T n i = some en → en.abort = false ∧ en.q = q
-- with Core's `OpTab.Local`; no deliverable takes `LinResume` or `OpTab.AbortOnly`

/-- The lifetime order the pin assumes (§1.2): a `reb` entry closed after an `anti` entry, before
the next `mut` entry on the anti's place, is below the anti's cell lifetime. -/
def OblWf (τ : List OEnt) : Prop :=
  ∀ i (hi : i < τ.length) l α β T δ P, τ[i] = .anti l α β T δ P →
    ∀ e ∈ (τ.drop (i + 1)).takeWhile (fun e => !e.isMutAt l), ∀ β', e.rebLife? = some β' → β' ⊏ β

/-- The 6.64 entries of `τ` are younger than `α`: a borrower's own entries, opened inside a lend
at `α`. Not the case for an entry the borrower holds through a continuation it resumes (§3.4). -/
def YoungerThan (τ : List OEnt) (α : Life) : Prop := ∀ q, OEnt.imm q ∈ τ → q.2 ⊏ α

/-- The payload's relation does not read the record list. -/
def ListStable (T : VTy) (δ : LSub) : Prop := ∀ ls ls' w ρ, vC true T ls δ w ρ ↔ vC true T ls' δ w ρ

def exitI (p : FrameRec) (α : Life) (Q : List SRec → Val → WProp) : List SRec → Val → WProp :=
  fun ls v => box α (ptoOwn p.le p.v ─⋆ (vC true p.T ls p.δ p.v ─⋆ Q ls v))
def exitM (l : Loc) (α : Life) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp) :
    List SRec → Val → WProp :=
  fun ls v => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ Q ls v))
/-- 6.66's postcondition: the content handed back, then the view taken. -/
def antiPost (l : Loc) (α : Life) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp) :
    List SRec → Val → WProp :=
  fun ls v => ex fun w => ptoOwn l w ⋆ vC true T ls δ w ⋆
    (ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆ Q ls v)
def viewM (l : Loc) (α : Life) (T : VTy) (δ : LSub) : List SRec → WProp :=
  fun ls => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ)
def QExt (Q : List SRec → Val → WProp) : Prop :=
  ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q ls₁ w ρ → Q ls₂ w ρ
```

`QExt` is Core's added hypothesis `hQ` of 6.64 (`Core/FrameRules.lean:60`). It is not printed.

**`ClosedOps` is scoped, as the unrestricted-continuation conjunct is.** No result of this unit
covers an operation whose argument or answer holds a borrow cell:
- lifetime-polymorphic operations (OQ-56 (b));
- operation types that mention the site's lifetimes (OQ-56 (c));
- the lifetime-open operation types the kernel admits today at a handler outside a borrow
  callback. `effPerform` requires no closed operation type; only `Row.Unwind` and `EffLeaf` do
  (BRIEF §3.8; OQ-35).

It is also what a handler extent would constrain: what crosses a stop to the handler. So the one
place this unit looks past `ClosedOps` is §3.4's argument variant, `ArgBelowExtent` and
`ArgAboveExtent`. Those are stated at the resource level and need no `ClosedOps`. The report
repeats this scope.

### 1.9 Conservativity: Core is the `τ = σ = []` instance

```lean
theorem wpGW_nil : wpGW [] [] ls e (fun τ' ls' t ρ => τ' = [] ∧ Q ls' t ρ) ρ ↔ wpG ls e Q ρ
theorem ewpTS_ewpW : ewpTS ls e (opTable T) Q ρ → ewpW [] σ ls e (opTableW T) Q ρ
```

- **`wpGW_nil`** holds by unfolding.
  - At `τ = τ′ = []`, `Close` is the identity: there is no anti step to pin.
  - `CompatW []` is `Hash`, and the selection premise is vacuous.
  - `StopW` is conjunct (40): `p ∉ immRecs []` always holds.
- **`ewpTS_ewpW`** is induction on `ewpTS`, with `wpGW_nil` at each unfolding and
  `σ`-monotonicity.
  - At a stop, `Holds [] ρk` is trivial, and `CompatW [] ρa ρk` is `Hash ρa ρk`, from the
    validity of the stop's world.
  - `contShare ⊨ shareW … []` follows by the induction hypothesis, and `cancelOwed ⊨ owedW … []`
    by the same induction at `cancelTab`.

Every Core result is therefore a result about `ewpW []` whose stops hand nothing open. The
converse is T1 for tier-1 programs, which is Unit 3's.

### 1.10 What the draft leaves out, and what that costs

- **The relation at `W`.** There is no `𝒱` at `W`.
  - Every probe's borrowers and continuations are abstract `ewpW` premises.
  - Every other piece of code (`c₃`, `d₃`) is read through Core's `vC` and lifted by
    `ewpTS_ewpW`.
  - OQ-58 and OQ-8 are therefore not exercised.
- **What that costs.** `CompatW` must hold of whatever frame a resumer calls `κ` at.
  - For a resumer given by code this is a resource argument (§2: `closed_compatW`,
    `compat_at_stop`, `compat_resume`).
  - For a resumer read only through a relation, it is a property of the relation at `W`. That is
    FINDING-1 (§8).
- **The order of `σ`.** D-ORD is not imposed (§1.4). OQ-3's separation is therefore out of reach of
  a semantic statement here (FINDING-2).
- **OQ-46** (the world a stored payload is read at) is not touched: payloads are read at `ls`.
- **Borrowing operation types (OQ-56 (b), (c)).** They are not tested (§1.8). The tier-2 programs
  that motivate them include an asynchronous read into a lent buffer, and a generator yielding
  views of its own buffer (the draft spec's 01 §5.3). They are outside every probe, as is a lifetime-open operation
  type at a handler outside a borrow callback (OQ-35).
- **No new relation family.** `wpGW`/`ewpW` is the one draft wp.
  - `OpenInv`, `OpenInvReb`, `Holds`, `CompatW`, `ExtentOK`, `RebExitW` and `OblWf` are
    predicates on resources, lists and lifetimes.
  - `extTabW` and `opTabW` are tables.
  - `KapRelW` is one definition with a re-entry parameter.

---

## 2. Definition checks, before any probe (`WorldW/Checks.lean`)

### F-CLOSE: the closure does not depend on the anti step's choice

Run first. No later stage uses `Defs.lean` until `close_upd_coherent` is proved (§9).

```lean
/-- One anti step changes `⦇·⦈` at its place only, whatever split it chose: `ResU.flat_mut_own_agree_off`
(`Paper/S6_2_NonStandardLemmas/Lemmas.lean:679`) read at `CloseEAnti`. -/
theorem closeE_anti_flat {l : Loc} {β : Life} {P : Val → SPropS Loc Val β} {ρP π π' F G : WRes} :
    CloseEAnti l β P ρP π π' → ResU.Flat π' F → ResU.Flat π G →
    (∀ m, m ≠ l → F.get m = G.get m) ∧
    ∃ v χ h hw, F.get l = some (CellU.mutOf β v χ h P hw) ∧ G.get l = some (CellU.ownOf v)

/-- Two closures of one resource by one list have the same flattening off the anti entries'
places, and at an anti entry's place both carry `mut(β, v, _, P̂)` for the same `β`, `v`, `P̂`. -/
theorem close_flat_agree {τ : List OEnt} {π π₁ π₂ F₁ F₂ : WRes} :
    Close τ π π₁ → Close τ π π₂ → ResU.Flat π₁ F₁ → ResU.Flat π₂ F₂ →
    (∀ m, (∀ e ∈ τ, ¬ e.IsAntiAt m) → F₁.get m = F₂.get m) ∧
    (∀ l α β T δ P, OEnt.anti l α β T δ P ∈ τ → ∃ v,
      (∃ χ h hw, F₁.get l = some (CellU.mutOf β v χ h P hw)) ∧
      (∃ χ h hw, F₂.get l = some (CellU.mutOf β v χ h P hw)))

theorem close_upd_coherent {τ : List OEnt} {π π₁ π₂ : WRes} (hv : ResU.Valid π) :
    Close τ π π₁ → Close τ π π₂ → ResU.UpdV π₁ π₂

/-- (37) holds at one pair of closures iff it holds at every pair (6.49 and the symmetry of `↭`). -/
theorem upd_choice_free {τ τ' : List OEnt} {ρ π ρc πc ρc' πc' : WRes} :
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    Close τ ρ ρc' → Close τ' π πc' → ResU.UpdV ρc' πc'

/-- Where the lifetimes are in the order arising obligations have, the pin removes no split. -/
theorem pin_harmless {l : Loc} {α β : Life} {T : VTy} {δ : LSub} {P : Val → SPropS Loc Val β}
    {τ : List OEnt} {ρP : WRes} (hw : OblWf (.anti l α β T δ P :: τ)) (hs : ρP.InStratum β) :
    AntiPin l τ ρP

/-- Why the pin exists (about our `Close`, not about (a)). Without it, the anti step of
`[anti l …, reb … β′ χ]` with `β ⊏ β′` has two results on one resource: in one the refold's
witness holds a copy of an image cell at `β′`. The `reb` step's `⊟` does not reach that copy, so
the two closures are not `↭`-related. Stated at a concrete resource. -/
def UnpinnedIncoherent : Prop :=
  ∃ (l : Loc) (β β' : Life) (P : Val → SPropS Loc Val β) (rb : OEnt) (π ρP₁ ρP₂ π₁ π₂ π₁' π₂' : WRes),
    rb.rebLife? = some β' ∧ β ⊏ β' ∧
    CloseEAnti l β P ρP₁ π π₁ ∧ CloseEAnti l β P ρP₂ π π₂ ∧
    CloseE [] rb π₁ π₁' ∧ CloseE [] rb π₂ π₂' ∧ ¬ ResU.UpdV π₁' π₂'
```

- **The proof of `close_flat_agree`** is induction on the chain, with `closeE_anti_flat` at each
  anti step.
  - Every later step reads only top-level cells. A cell an anti step absorbed is not at the top
    level, so that step either does not apply or gives an invalid result.
  - The pin keeps image copies out of the witnesses, where `⊟` would miss them.
  - A `mut` entry on the anti's place unfolds the witness back to the top level. The two chains
    then hold one resource again.
- **The absorbed-view configuration** is the instance at which it is checked.
  - A borrower of `L′` holds `mut@l′` at `α′`. Inside it, `l` is lent at `β ⊏ α′`. A callback
    runs `withbor3` on `l` while holding `mut@l′`.
  - At a stop inside, the anti step on `l` may take `mut@l′` into `ρ_P̂`, since its lifetime is
    above `β`.
  - `⦇·⦈(l′)` is the same `mut(α′, …, Q̂′)` cell in both closures (`closeE_anti_flat`).
  - `TW` lets a run change `l′`'s predicate only by `mutUnfold` and `mutFold` at `l′`. Those are an
    `anti` entry and a relend on `l′`. If they are open, they are in `τ′`, and their closures
    restore `(α′, Q̂′)` before `UpdMut` compares. If they have closed, 6.66's exit refolded `l′`
    at its own `(α′, Q̂′)`.
- **Decision rule.** Suppose `close_flat_agree` fails at a chain. The failing pair of steps names a
  further absorption. The pin is extended to it before anything else. If no pin works, (37) is
  restated in option (i)'s form, with its own 6.48 and 6.49 checks:
  - verbatim `UpdImm`/`UpdMut` off the footprints of `τ ∪ τ′`;
  - closures compared only at those footprints.

**Corrections made while building stage A** (`WorldW/Checks.lean`; both are about our `Close`,
neither is about (a)):

1. **`close_flat_agree`'s second conjunct was mis-stated.** It claimed `mut(β, v, _, P̂)` at the
   place of *every* anti entry of `τ`. A later 6.65 entry at the same place unfolds the refolded
   cell again: in the nested `withbor3` list `[mut ℓ α, anti ℓ α₀ α₀ …, mut ℓ α₀]` both closures
   end with `own` at `ℓ`. The statement as built is at the anti entries that no later 6.65 entry
   at their place follows (`PendingAt`), and its first conjunct is strengthened to every place
   that is not pending. The design's first conjunct is `close_flat_agree_off_anti`, proved.
2. **`CloseE`'s 6.150 step now asks `ResU.Reb β σR χ`** (the printed H16), beside `Le`, `⊟` and
   `✓`. Without it the image `χ∣dom(σR∣mut,own)` may hold `imm` cells at a lifetime `γ ≠ β`, which
   `AntiPin` does not cover (it forbids only cells at the entry's `β`). Then two closures of one
   resource differ: take `[anti l …, reb … β χ]` with `χ` holding `imm({γ}, u, R)` at `m`, one
   split taking a copy of the top-level `imm({γ})` at `m` and one not; `⊟` removes only the
   top-level copy, so `⦇·⦈(m)` keeps `γ` in one closure and not in the other, and `UpdImm` fails.
   With `Reb`, every image cell is `imm({β}, …)` (`reb_img_single`), and the pin covers it. The
   configuration needs a non-reborrow image, so it does not arise; it measures our `Close` only.
   `close_upd_coherent` is proved with this correction, at every resource, with no other premise.

**How `close_upd_coherent` is proved** (`WorldW/Refold.lean`, `WorldW/Coherence.lean`). Two
chains over one list are walked together. At every point both states are refolds of one unfolded
resource `U`, by refold lists of one shape (place, lifetime, predicate) and possibly different
splits (`close_pair`). A 6.64 or 6.65 step away from the pending places lifts through the refolds
to one step on `U` (`refolds_replace`: the step's `own` cell excludes every split at its place,
6.24); a 6.65 step at a pending place undoes that refold (`refolds_unfold`); a 6.150 step lifts to
`U ⊟ image` (`refolds_sub`, where the pin is spent); an anti step appends a refold. The shape list
at the end is a function of `τ` (`pendAfter`). A refold changes `⦇·⦈` at its own place only
(`refolds_flat`, from `closeE_anti_flat`), so the two ends agree off the pending places and carry
`mut(β, v, _, P̂)` with one `β`, `v`, `P̂` at them. `↭` follows; `upd_choice_free` is it with 6.49.

### F0: the frame quantifier at an open 6.64 entry, at the resource level

**What `↭` does not force.** `UpdV` constrains only `imm ⇔ imm` and `mut ⇔ mut` cells of the
flattening (5.27). It never constrains `own`. So with the verbatim frame quantifier, a frame
holding a copy of an open view is admitted, and the printed exit cannot be completed at it. F0
states this at the resources, with no second `wp`:

```lean
/-- F0, at the nested-copy configuration (§5). The frame `ρf` holds a copy of the open view,
nested in another cell's witness.
* `ρf` passes the verbatim frame premise: `#`, `TW` and `Tagged` hold, and the selection premise
  is met.
* `CompatW` excludes `ρf`.
* No resource that owns the lent place is compatible with `ρf`. -/
def FrameCopyBlocksExit : Prop :=
  ∃ (p : FrameRec) (α : Life) (ρf ρ fρ : WRes) (ps : List FrameRec) (ls : List SRec),
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    TW fρ (p :: ps) (rsOf ls) ∧ Tagged fρ (p :: ps) ls ∧
    OpenInv [] ls (.imm (p, α)) ρ ∧
    ¬ CompatW [.imm (p, α)] ρf ρ ∧
    ∀ ρ', (ptoOwn p.le p.v ⋆ fun _ => True) ρ' → ¬ ResU.Hash ρ' ρf
```

- **What it shows about every frame lemma.** The value case of each frame lemma builds a final
  resource that owns the place. That is 6.38's G1: the exit returns `ℓ ↦ own(v) ● R` to the
  lender, and `NoOwn` keeps the `own` cell out of the leftover.
  - At `ρf`, such a resource is not compatible with the frame (last conjunct). So the printed exit
    cannot be applied at that frame.
  - `CompatW` is what keeps `ρf` out of the quantifier.
- **What it does not show.** At a postcondition that does not return the place (`Q = True`), a run
  can "close" the entry by dropping its view. The frame's copy keeps the heap matching. So F0 is a
  statement about the printed route, which always returns the place. It is not a statement about
  every postcondition.
- **Proof.** The flattening of `ρf ● ρ′` would hold `own` and an `imm` cell at `p.le`, so it is
  undefined. No `TW` inversion is used. The configuration's `TW` and `Tagged` come from its
  history (§5), and `OpenInv` from `openInv_entry`.
- **Decision rule.** If F0 resists proof, re-examine the configuration. It is never a reason to
  drop the conjunct.

### F1: where `CompatW` is `Hash`

```lean
theorem compatW_iff_hash {τ : List OEnt} (hτ : ∀ e ∈ τ, e.isMut ∨ e.isAnti ∨ ¬ e.isLend)
    {ρf ρ : WRes} (hh : Holds τ ρ) : CompatW τ ρf ρ ↔ ResU.Hash ρf ρ
```

This is 6.24, applied once per entry: for every `ρ`, `ρ # ℓ ↦ mut(α, v, ρ_v, P̂)` iff
`ρ # ρ_v ● ℓ ↦ own(v)`. That covers frames holding `imm` copies of payload cells as well. The cell
at `ℓ` is exclusive in both forms (6.41, 6.42), so the closure of the composite is the frame
composed with the closure of the part, and the inert half follows. The σ-component of `#`
restricts frames only at `imm` and `reb` entries.

The exclusivity check at a stop is a separate matter, and it bites hardest at `anti` entries. It
is `Holds τ′ ρk` in `opTabW`. `ClosedOps` lets `PA` carry the anti entry's `own` cell and its
payload. `Holds` keeps them in the share.

### F2: the relativised `↭` records every open entry (OQ-44)

```lean
/-- At a 6.65 lend: a `mut` cell of `π` at `(α, Q̂)` that `⦇ρc⦈` lacks is closed by a `mut`
entry of `τ′` at `l` and `α`. -/
theorem entryRecorded_mut {τ τ' : List OEnt} {ρ ρc π πc : WRes} {l : Loc} {α : Life}
    {Q : Val → SPropS Loc Val α} {v : Val} {χ : WRes} {h : χ.InStratum α} {hw : Q v ⟨χ, h⟩} :
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    (∀ v' χ' h' hw', ¬ ρc.FlatAt l (CellU.mutOf α v' χ' h' Q hw')) →
    π.get l = some (CellU.mutOf α v χ h Q hw) → ∃ T δ, OEnt.mut l α T δ ∈ τ'

/-- At an `imm` component: a top-level `imm` cell of `π` whose lifetime set holds `γ`, at a place
where no `imm` cell of `⦇ρc⦈` has `γ`, is consumed by an entry of `τ′` (a 6.64 entry at `γ`, or a
`reb` entry whose image is at `γ`). -/
theorem entryRecorded_imm {τ τ' : List OEnt} {ρ ρc π πc : WRes} {l : Loc} {γ : Life}
    {s : LSet} {v : Val} {R : WRes} {h : R.InStratum s.join} :
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    π.get l = some (CellU.immOf s v R h) → s.mem γ →
    (∀ s' v' R' h', ρc.FlatAt l (CellU.immOf s' v' R' h') → ¬ s'.mem γ) →
    ∃ e ∈ τ', e.Consumes l (.immAt γ)

/-- At a 6.66 anti-frame: an `own` cell of `π` at a place where `⦇ρc⦈` has `mut(β, …, P̂)` is
refolded by an `anti` entry of `τ′` at `l`, `β` and `P̂`. -/
theorem entryRecorded_anti {τ τ' : List OEnt} {ρ ρc π πc : WRes} {l : Loc} {β : Life}
    {P : Val → SPropS Loc Val β} {v : Val} :
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    (∃ v' χ' h' hw', ρc.FlatAt l (CellU.mutOf β v' χ' h' P hw')) →
    π.get l = some (CellU.ownOf v) → ∃ α T δ, OEnt.anti l α β T δ P ∈ τ'
```

- **Why each holds.** Suppose no entry of the named kind is in `τ′`. Then the cell stays in
  `⦇πc⦈` with its kind, lifetime and predicate:
  - a 6.64, 6.65 or 6.66 step consumes only its own top-level cell;
  - Definition 6.3's `⊟` keeps `own` and `mut` cells (`ρ∣own,mut ● ρ″`);
  - a cell an anti step absorbs stays in `⦇·⦈` (`closeE_anti_flat`);
  - the pin keeps image copies out of witnesses.

  `UpdMut` or `UpdImm` then fails against `⦇ρc⦈`, a contradiction.
- **No lifetime premise.** An anti step may absorb the cell when its lifetime is above the anti's
  `β`, but absorption does not remove it from the flattening. If that step does not close in Lean,
  the premise F2 would need is `∀ e ∈ τ′, e.isAnti → ¬ e.β ⊏ γ`: no anti entry could absorb the
  cell by stratum. That premise would be a finding about `Close`, not about (a).
- **Instance.** `entryRecorded_mut` is checked at the absorbed-view configuration of F-CLOSE.
- **What it answers.** OQ-44's `MutLendRecorded`, from conjunct (37) alone, with no `TW`
  constructor: OQ-44 (a)'s entries suffice.
- **Built** (`WorldW/Checks.lean`): `entryRecorded_mut`, proved at every resource with no lifetime
  premise, through `close_pair`'s invariant (the steps keep the unfolded resource's `mut` cells,
  and no refold sits at a place holding one). `entryRecorded_imm` and `entryRecorded_anti` are not
  stated.

### The other checks

**`close_relend_anti`.** Two entries on one place, and their order:
- If `π.get l = mutOf α v χ …` and `P̂(v)(χ)` hold, then
  `Close [mut l α T δ, anti l α₀ β T δ P̂] π (π.del l ● mutOf β v χ P̂)`.
- `¬ CloseE τ (anti …) π _` whenever `π.get l` is a `mut` cell.

**`holds_exclusive`**: exclusivity at a stop (plan, Unit 3), stated by what each exit consumes.

```lean
/-- What an exit consumes at a location: the unfolded `own` cell, a `mut` cell at a lifetime, or
the component of an `imm` cell at one lifetime. -/
inductive OKey | own | mutAt (γ : Life) | immAt (γ : Life)

def OEnt.Consumes : OEnt → Loc → OKey → Prop
  | .imm (p, α), m, k => m = p.le ∧ k = .immAt α
  | .mut l α _ _, m, k => m = l ∧ k = .mutAt α
  | .anti l _ _ _ _ _, m, k => m = l ∧ k = .own
  | .reb _ _ _ σR _ β χ, m, k => ((χ.restrictDom σR.exclPart).get m).isSome ∧ k = .immAt β
  | .hnd .., _, _ => False

/-- `e` consumes an exclusive key (`own` or `mutAt`) at `m`: a `mut` or `anti` entry at `m`. -/
def OEnt.ConsumesExcl (m : Loc) : OEnt → Bool
  | .mut l _ _ _ => l == m
  | .anti l _ _ _ _ _ => l == m
  | _ => false

/-- (i) No two entries of `τ` consume the same pair. -/
theorem holds_injective {τ : List OEnt} {ρ : WRes} (hv : ResU.Valid ρ) (hh : Holds τ ρ) :
    ∀ i j (hi : i < τ.length) (hj : j < τ.length), i ≠ j →
      ∀ m k, τ[i].Consumes m k → τ[j].Consumes m k → False

/-- (ii) At one location, the entries consuming an exclusive key (`own` or `mutAt`) form one
alternating chain in `τ`'s order: after `mut l α` comes an `anti l _ β …`, and after
`anti l _ β …` comes `mut l β` (the refold's lifetime is the outer lend's, by `mutOf_at`). -/
def ChainStep : OEnt → OEnt → Prop
  | .mut l _ _ _, .anti l' _ _ _ _ _ => l = l'
  | .anti l _ β _ _ _, .mut l' β' _ _ => l = l' ∧ β = β'
  | _, _ => False

theorem holds_chain {τ : List OEnt} {ρ : WRes} (hv : ResU.Valid ρ) (hh : Holds τ ρ) (m : Loc) :
    List.IsChain ChainStep (τ.filter (fun e => e.ConsumesExcl m))
```

- **The cases, read off (i) and (ii).**
  - Entries at different places close disjoint cells.
  - A 6.64 view and a 6.150 image never share a key. The image lies at the exclusive locations of
    the reborrowed view's witness, and the view sits at its own place.
  - Several `reb` entries may consume image cells at one location, each at its own lifetime:
    sibling reborrows of one view, aliasing `imm` cells.
  - A `reb` of a 6.64 entry's view closes before that entry. The 6.64 exit puts the payload's
    exclusive cells at the top level, where the image cells still are. So the reverse order gives
    an invalid result, which `CloseE` excludes.
- **The lifetime nesting is not a resource fact.** The inner `mut` of the `withbor3` chain lies
  below the anti's refold lifetime. That comes from the 6.65 entry's choice:
  `relend_below_anti` is a conjunct of the 6.65 entry lemma (§4.2). Inside a body whose stack holds
  `anti l α₀ β …`, the entry takes its `α` below `β` and `α₀`.
- **Instances** (§3.5). Each proves or refutes the statement at a `TW` history.
  - **`withbor1` then `withload`.** A 6.64 frame on `ℓ`, then a reborrow of its view, gives
    `[reb ℓ {α} v R … β χ, imm (p, α)]` with `p.le = ℓ`. It arises in `TW` (`immFrame`, then `reb`
    at the record's cell). `Holds` holds in that order. The consumed pairs are distinct: `(m, β)`
    for `m ∈ dom(R∣mut,own)`, and `(ℓ, α)`. The reverse order fails `Holds`.
  - **Two reborrows of one view** before the frame's exit: `[reb₁ β₁, reb₂ β₂, imm (p, α)]`.
  - **The nested `withbor3`** of §3.2: `[mut ℓ α, anti ℓ α₀ α₀ …, mut ℓ α₀]`.
- **Scope.** Unit 3 proves the theorem once over its relation. Here it is the structural half,
  with these instances.

**Correction 3 (made while building; `WorldW/Checks.lean`).** (i) contradicts (ii) once the
alternating chain at a location has two anti entries: both consume `(ℓ, own)`. A doubly nested
`withbor3` (a `withbor3` on the relend of another) closes exactly such a list,
`[mut ℓ α₂, anti ℓ α₁ α₁ …, mut ℓ α₁, anti ℓ α₀ α₀ …]`. `not_holdsInjective` refutes (i) as stated
at that list, closed at a single valid `mut` cell. Without a lifetime premise (i) also fails at the
`mutAt` keys (`[mut l α, anti l _ α …, mut l α]`), which is the nesting the entry lemmas supply
(`relend_below_anti`), not a resource fact. So (i) is to be read at the `imm` keys only, and
exclusivity at the exclusive keys is (ii)'s alternation together with the entry lemmas' lifetime
nesting. Neither corrected statement is proved here.

**`close_frame`.** If `CompatW τ R ρ`, then closing `ρ ● R` is closing `ρ`, composed with `R`.
This is the inert half of §1.3. `wpGW_frame` and the split bind need it.

**`closed_compatW`.** A resource of closed data is compatible with the closure, and inert under
it:
`(∀ α, R.InStratum α) → ResU.Hash R ρ → Holds τ ρ → CompatW τ R ρ`.
The proof is 6.38's flattening argument for `imm` entries, 6.24 for `mut`/`anti` entries, and
6.53/6.55 for `reb` entries.

**`compat_at_stop` and `compat_resume`.** The continuation's frame at a resume is whatever is
outside its resource when it is called. That is in general not the stop's frame. The stop's pieces
are one component of it, and the resumer's own resources are the other:

```lean
/-- At a stop, the stopped world's pieces a resumer's frame inherits — the stop's frame, its
leftover and the argument — are compatible with the closure of the share and inert under it. -/
theorem compat_at_stop {τ τ' : List OEnt} {ps ps' : List FrameRec} {ls ls' : List SRec} {t : Expr}
    {ρf ρp ρ' π ρa ρk : WRes}
    (hs : StopW τ ps ps' ls ls' t τ' ρf ρp ρ' π) (ht : ¬ ∃ v, t = .val v)
    (hπ : ResU.CompS ρ' ρp π) (hk : ResU.CompS ρa ρk ρ') (hak : CompatW τ' ρa ρk) (hh : Holds τ' ρk) :
    ∃ ρs, (∃ ρpa, ResU.CompS ρp ρa ρpa ∧ ResU.CompS ρf ρpa ρs) ∧ CompatW τ' ρs ρk

/-- A resumer's frame `ρs ● ρo`: the stop's pieces and the resumer's own resources. -/
theorem compat_resume {τ' : List OEnt} {ρs ρo ρk ρsk ρso : WRes}
    (hsk : ResU.CompS ρs ρk ρsk) (hso : ResU.CompS ρs ρo ρso)
    (hs : CompatW τ' ρs ρk) (ho : CompatW τ' ρo ρsk) : CompatW τ' ρso ρk
```

- **Correction 4 (made while building).** `compat_at_stop`'s conclusion builds `ρs = ρf ● (ρp ● ρa)`,
  which needs the composite of the frame with the stop resource. `StopW` does not assert it (its
  `CompatW τ′ ρf π` is about the closures of `π`). The built statement takes `∃ X, ρf ● π = X` as a
  premise; at a run of `wpGW` it is the final configuration `fρ'p`.
- **The second premise is per resumer.**
  - **A resumer given by code.** Its own resources are closed data (`closed_compatW`), fresh
    places, or lends of its own places (a direct argument, as for `L₃`'s view at `ℓ₃` in §3.4).
  - **A resumer read only through a relation.** That is FINDING-1.
- **In every probe's Guarantee.** This conditionality is repeated there (§3.1–§3.4).

**`younger_preserved`.** `StopW`'s freshness conjunct gives `YoungerThan τ′_b α` at every stop of
a borrower that runs under `imm (p, α) :: σ` from a `YoungerThan τi α` start.

**`dropKappa_by_surgery`.** The stop condition does not force a clause to run `κ` (§1.6):

```lean
/-- A clause that drops `κ` closes `κ`'s entry by the printed exit as resource reasoning, and keeps
the owned place, at a postcondition that accepts it. -/
theorem dropKappa_by_surgery {p : FrameRec} {α : Life} {σ : List OEnt} {ls : List SRec}
    {T : OpTab} {ρ : WRes} (hh : Holds [.imm (p, α)] ρ) :
    ewpW [.imm (p, α)] σ ls (.app (.val unitClause) (.val (Val.pair Val.unit Val.unit)))
      (opTableW T) (fun _ _ ρ' => (ptoOwn p.le p.v ⋆ fun _ => True) ρ') ρ
-- `unitClause = λp. ()`
```

The proof runs one β-step and stops at the value with `π := ρc`. The steps:
- `TW.immEnd` types the post-world. Its validity is `CompatW`'s `Hash ρf ρc`.
- The heap is unchanged: closing preserves the erasure (6.26, 6.8).
- `StopW`'s value clause holds with `immEnd`'s lists.

---

## 3. The probes

Every probe is a `def … : Prop`, proved or refuted with every hypothesis discharged. Each comes
with an instance that discharges every hypothesis (§3.5), so none is vacuous. A probe that does not
close is reported as unfinished. The report names the step that would not follow and the printed
lemma it names.

### 3.1 `OpenFrame64` and `OpenFrame65`: one lender, a row that mixes resume, cancel and drop

```lean
/-- OQ-9 (a), [TR] 6.64, at a row that mixes linear, affine and abortive operations.
* A run holds the open frame `e = imm (p, α)` and the entries `τi` its borrower holds.
* Its borrower `b` is given at the fixed `α`.
* Conclusions: `e` closes by 6.64's exit when `b` returns. At a resuming stop `e` is handed on,
  open: the share demands the resume at every answer and, at an affine operation, the cancel run
  (`owedW`). At an abortive stop `e` closes there. At a cancel's end the cancel run closes `e`.
  At the last two, the owner is handed back beside the stop for the lender's finaliser.
* The borrower may hold 6.66 and 6.150 entries of its own: `τi` ranges over every kind.
  `YoungerThan`: the 6.64 entries it holds were opened inside the lend. -/
def OpenFrame64 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (p : FrameRec) (α : Life) (Q : List SRec → Val → WProp), QExt Q →
  ∀ (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.imm (p, α)) ρ →
    ewpW τi (.imm (p, α) :: σ) ls b (opTableW T) (exitI p α Q) ρ →
    ewpW (τi ++ [.imm (p, α)]) σ ls b (opTabW T (GhostEnd.ownerI p.le p.v p.T p.δ)) Q ρ

/-- The same for a [TR] 6.65 lend. -/
def OpenFrame65 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : Loc) (α : Life) (S : VTy) (δ : LSub) (Q : List SRec → Val → WProp)
    (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ
```

The proof is by induction on the borrower's `ewpW` (§4.3). Its cases are stated as lemmas, and
each is the frame lemma at one end of an unfolding:

- **`openFrameResume64`: hand-on at a perform stop.** The borrower's `shareW τ′_b` becomes the
  conclusion's `shareW (τ′_b ++ [e])`, with the frame left lent. Its cancel conjunct is
  `openFrameCancel64` applied to the borrower's `owedW`.
- **`openFrameCancel64`: exit at a cancel's end.** Statement:
  `OpenInv τi ls e ρ → ewpW τi (e :: σ) ls (K.plug (raise cancel)) (cancelTabW T N) ⊥ ρ →
  ewpW (τi ++ [e]) σ ls (K.plug (raise cancel)) (withOwnerW (cancelTabW T N) ownerI) ⊥ ρ`.
  The cancel table is abortive, so this is one `wpGW`.
- **`openFrameDrop64`: exit at an abortive stop.** The borrower's `raise` reaches the frame with
  `τ′_b = []`. Its own lenders' `ubind`s have caught it on the way.
- **`openFrameVal64`: exit at the borrower's return.**

The 6.65 lemmas have the same names, with `65`.

- **Why it is the real question.** The premise is the borrower's own `ewpW` at `τi`, under `e`.
  - It does not close `e`, and its continuations are again the borrower at the same `α`. There is
    no fresh lifetime to re-lend at. So the conclusion can be met only by carrying `e` open through
    every resuming stop.
  - `e` is then closed at whichever end the continuation reaches: a return, a later abortive stop,
    or a cancel. That end is reached from a continuation's start, across an earlier resuming stop.
    That is the configuration OQ-9 names.
  - `τi` lets the borrower hold entries of its own, so the statement is the inductive one.
- **Guarantee.**
  - *What it gives.* The lender gets the place back (`ℓ ↦ own(v) ⋆ 𝒱⟦T⟧(v)`) with nothing left
    pointing at `α`, on every path: no use after free, and lifetimes respected. A cancelled or
    dropped continuation leaves the owner for the finaliser exactly once, in LIFO order: leak
    freedom and finalisation. For 6.65, the place's cell comes back exactly once: exclusive mutable
    borrows.
  - *On what conditions.* `ClosedOps` (no argument or answer holds a borrow cell) and `NoUnr`.
    Every resumer must also call `κ` at a frame meeting `CompatW`. A resumer given by code
    discharges that (`compat_at_stop`, `compat_resume`); a resumer read through a relation is
    FINDING-1.
- **If it fails.** The failing case names the path. The failing step names the printed lemma whose
  hypothesis the continuation cannot supply: 6.29/6.38 at a start without the box, for 6.64; 6.27
  for 6.65. If only the cancel or drop lemma fails, (a) is out for rows with that kind of
  operation, and the report says so.

### 3.2 `OpenFrame66`, and the nested `withbor3` shape

```lean
/-- OQ-9 (a), [TR] 6.66, at a mixed row. A run holds the open anti-frame
`e = anti l α β S δ P̂`: the cell at `l` unfolded to `own(v) ● ρ_P̂` for the body `b`. `e` closes
by 6.66's refold when `b` returns, is handed on, unfolded, at a resuming stop, and is refolded at
an abortive stop and at a cancel's end, the view `ℓ ↦ Mut α` handed back beside them. -/
def OpenFrame66 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : Loc) (α β : Life) (S : VTy) (δ : LSub) (P : Val → SPropS Loc Val β)
    (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.anti l α β S δ P) ρ →
    ewpW τi (.anti l α β S δ P :: σ) ls b (opTableW T) (antiPost l α S δ Q) ρ →
    ewpW (τi ++ [.anti l α β S δ P]) σ ls b (opTabW T (viewM l α S δ)) Q ρ
```

- **What it adds.** 6.66's exit is a refold, not an end. At an abortive stop and at a cancel's end
  the table gets the refolded view, as `withbor3U_compatX` does at today's stop
  (`Table.withFr` with `vP (.mut a A)`). At a perform stop the unfolded `own` cell stays in the
  share (`Holds`), and the handler never receives it.
- **The composition `withbor3` needs** is `OpenFrame66` around `OpenFrame65`, with two entries on
  one place.
  - The 6.65 entry's `OpenInv` is read after closing the borrower's own entries.
  - The anti entry's `OpenInv` is read after closing the relend too, so its `τi` contains the `mut`
    entry.
  - `close_relend_anti` orders them, and `relend_below_anti` (from the 6.65 entry's freshness)
    nests their lifetimes.
- **The nested instance** (§3.5) puts `withbor3` inside a 6.65 borrower whose inner callback
  yields. At the yield three entries are open on one place:
  `[mut ℓ α, anti ℓ α₀ α₀ …, mut ℓ α₀]`.
- **Comparison point:** `nested_spans_yield` (GhostEnd, (b)).
  - At the stop, (b) ghost-ends the inner lend, refolds, and ghost-ends the outer lend. At the
    resume it re-lends the outer, unfolds, and re-lends the inner below it.
  - Under (a) nothing is ended. The three entries are handed on, and closed in context order when
    the callbacks return.
- **Guarantee.** As §3.1's, with the view handed back instead of the owner. The same conditions
  apply: `ClosedOps`, `NoUnr`, and `CompatW` at the resumer's frame (FINDING-1 for a resumer read
  through a relation).
- **If it fails.** A failure at the refold names 6.28. A failure at `Holds` names the point where
  `ClosedOps` lets an argument carry the owned cell. That is reported as a route around borrowing
  that our table check does not exclude. It is not patched.
- **Found while building: the refold at a stop** (`WorldW/HandOn.lean`). A stop that hands the anti
  entry on must close it in (37)'s `Close τ′ π πc`, and closing it refolds the place, which needs
  `P̂` of the content *at the stop*. `anti_handOn_needs_invariant` (proved): if the place holds
  `own(w)` at the top of the stop's resource and `P̂(w)` holds of no resource, no closure of the stop
  by any `τ′` is `↭`-related to the start's closure. `OpenFrame66`'s premise, the body's `ewpW`,
  may not exclude such a stop at the resource level, but `π` is existential in `wpGW`, so this does
  not show that `OpenFrame66` fails. I have not derived `OpenFrame66`, and I have not verified that
  any obstruction to it is real. No body, `ewpW` or `TW` history has been built. OQ-9 (b)'s `AntiRelend` (GhostEnd,
  `Frames.lean:68`) asks the body to hand back `ℓ ↦ w ⋆ 𝒱⟦T⟧(w)` at every stop. Whether (a) for 6.66 needs the same invariant at the stop is not derived. The alternatives are a
  premise of `AntiRelend`'s kind on `OpenFrame66`, or a (37) that reads an open anti entry's place by
  the entry's own `(β, P̂)` without refolding it. Both change a definition here; neither is made.

### 3.3 `OpenRecord150`: a reborrow handed on at a stop

```lean
/-- `RebChooseTW`'s exit clause (`Core/Reborrow.lean:124-128`) at the exit worlds a run under
`StopW` can reach.
* Core's premises `(∀ p, p ∈ ps' ↔ p ∈ ps) → (∀ x, x ∈ ls' ↔ x ∈ ls)` are T1's list equalities.
  They are replaced by `Keeps (rsOf ls) (rsOf ls') ρ_i`: the records relevant to the reborrowed
  view are still in the list.
* `Keeps` is what both list changes a continuation meets preserve: `Ext` along a resume (its
  first conjunct, at a share holding the view), and `StopW` along the borrower's own stops (only
  the lineages of closed `imm` entries leave, and the view's frame is not among them).
* `W''.InStratum β` is kept. The exit is typed by `TW.rebEnd`, whose premise it is. -/
def RebExitW (ls : List SRec) (l : Loc) (s : LSet) (w : Val) (σR : WRes)
    (hs : σR.InStratum s.join) (β : Life) (χ : WRes) : Prop :=
  ∀ (ps' : List FrameRec) (ls' : List SRec) (Wp W'' : WRes),
    Keeps (rsOf ls) (rsOf ls') (ResU.single l (CellU.immOf s w σR hs)) →
    TW Wp ps' (rsOf ls') → Tagged Wp ps' ls' →
    (∃ (s' : LSet) (hs' : σR.InStratum s'.join), W''.get l = some (CellU.immOf s' w σR hs')) →
    ResU.CompS W'' (χ.restrictDom σR.exclPart) Wp → W''.InStratum β →
    TW W'' ps' (rsOf ls') ∧ Tagged W'' ps' ls'

/-- `RebChooseTW` (`Core/Reborrow.lean:112`) with `RebExitW` as its exit clause. The entry clauses
are Core's verbatim. -/
def RebChooseTWW (ls : List SRec) (l : Loc) (R : Val → WRes → Prop) (P₀ P : Life → Val → WProp) :
    Prop :=
  ∀ (W F χ₀ σ : WRes) (ps : List FrameRec) (β : Life) (w : Val) (s : LSet)
    (hs : σ.InStratum s.join),
    TW W ps (rsOf ls) → Tagged W ps ls → W.InStratum β →
    ResU.CompS (ResU.single l (CellU.immOf s w σ hs)) F W → R w σ →
    ResU.Reb β σ χ₀ → P₀ β w χ₀ →
    ∃ χ, ResU.Reb β σ χ ∧ P β w χ ∧ (∃ A, AgW χ A) ∧
      (∀ a, AgW F a → EscrowAgree σ χ a) ∧
      (∀ a, AgW (ResU.single l (CellU.immOf s w σ hs)) a → EscrowAgree σ χ a) ∧
      (∀ W', ResU.CompS W χ W' → ResU.Valid W' → TW W' ps (rsOf ls) ∧ Tagged W' ps ls) ∧
      RebExitW ls l s w σ hs β χ

/-- OQ-9 (a), [TR] 6.150, at a mixed row. A run holds the view `ρ_i = l ↦ imm(s, w, σR)` beside
the resource `X` of its borrower `b`, which holds the open reborrow `e = reb l s w σR hs β χ`.
`e` closes by 6.150's exit when `b` returns: the image subtracted from the leftover and the view
kept (H24–H33: 6.52, 6.58, 6.59, `TW.rebEnd`). It is handed on at a resuming stop and closed at
an abortive stop and at a cancel's end, with the view handed back for the finaliser. -/
def OpenRecord150 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : Loc) (s : LSet) (w : Val) (σR : WRes) (hs : σR.InStratum s.join) (β : Life) (χ : WRes)
    (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ X : WRes),
    YoungerThan τi β → RebExitW ls l s w σR hs β χ →
    ResU.CompS (ResU.single l (CellU.immOf s w σR hs)) X ρ →
    OpenInvReb τi l s w σR hs β χ X →
    ewpW τi (.reb l s w σR hs β χ :: σ) ls b (opTableW T) (fun ls v => box β (Q ls v)) X →
    ewpW (τi ++ [.reb l s w σR hs β χ]) σ ls b
      (opTabW T (fun _ ρ' => ρ' = ResU.single l (CellU.immOf s w σR hs))) Q ρ
```

**The chooser's dischargers, at `W`.** The plan lists re-establishing Core's dischargers at `W` as
a Unit 3 obligation. They are stage E's deliverable:
- **`rebChooseTW_top_W`**, at a record's cell. Its hypotheses are `rebChooseTW_top`'s:
  `r ∈ rsOf ls`, `AgreeOn r.T δ' r.δ` and `¬ VFree x r.T`. It concludes `RebChooseTWW` at the
  same `R`, `P₀`, `P`.
  - The entry part is `rebChooseTW_top`'s proof verbatim (`rebChooseO_top_tw`,
    `image_vC_of_shape`, `TW.reb`, `tagged_reb`).
  - The exit part is `TW.rebEnd` and `tagged_rebEnd`. Its `r ∈ rsOf ls′` comes from `Keeps`:
    `Rel r ρ_i` holds because `ρ_i` has the `imm` cell at `r.le`.
- **`rebChooseTW_deep_W`**, at a chain view. The same, with `rebChooseTW_deep`'s entry part.
  `Rel r ρ_i` holds by `Rel`'s chain disjunct, and the exit is `TW.rebEndDeep`.
- **`rebChooseTW_pin_W`**: `rebChooseTW_pin` (`Core/Compatibility.lean:134`) with
  `RebChooseTWW`. It passes the exit clause through unchanged.
- Each is proved for every exit world `RebExitW` quantifies over. So `OpenRecord150`'s premise
  `RebExitW` is discharged by a theorem, not assumed.
- **`keeps_of_ext` and `keeps_of_stopW`** carry `Keeps` from the entry's list to the exit's:
  - `Ext ls ls′ ρk` with `ρ_i ≤ ρk` gives `Keeps` (`Ext`'s first conjunct);
  - `StopW` under `YoungerThan τi β` keeps every record tagged above `β`, and the view's records
    are.

`Keeps` is transitive, so the exit's list meets `RebExitW`'s premise after any number of resumes.

- **The hand-on is 6.59 as printed, with a chosen split.**
  - The split is `ρ′ := ∅`, `ρ⁺ :=` the whole stop resource.
  - Then H(`@ρ′ ⊐ β`) is trivial, and H(`@ρ_b ⊐ β`) is `OpenInvReb`'s `Xr ∈ Res_β`. The conclusion
    subtracts the image from everything.
  - The borrower's run is taken with the view in its frame, as 6.150's inner run is (frame
    `ρ_i ● ρ_f`). So the premise's `↭` is without the view, and 6.59 adds it on both sides.
  - 6.52 gives the split of the leftover at the exit. No lemma beyond the printed ones is needed.
    6.59's last step accounts for an image cell by its immutable ancestor, and that is the step the
    hand-on reuses.
- **Borrower class.** With `OEnt.reb`, the borrowers of §3.1 and §3.2 may hold reborrows open at
  a stop. Their `τi` ranges over every kind, and their proofs read a `reb` entry only through
  `Close τi`.
- **The step to watch** is the exit's typing.
  - **The two premises.** `RebExitW` keeps `W''.InStratum β`. That is `TW.rebEnd`'s premise
    `W′.InStratum β` (`Core/World.lean:157`): the whole exit world in `Res_β`. The printed exit
    needs only the run's own resources above `β`: H15 `@ρ_b ⊐ β`, H29 `@ρ_Q ⊐ β`, and 6.52's
    `@(ρ⁺ ⊟ ρ_reb) ⊐ β`.
  - **What (a) adds.** Under (a), a resumer may open a lend younger than `β` around the resume. The
    exit world then holds a cell below `β`, and `RebExitW` says nothing about that world.
  - **The younger-lend configuration** (§3.5, §5) is where this is tested. Every hypothesis of
    `OpenRecord150` is discharged there:
    - `RebExitW` by `rebChooseTW_top_W`, vacuously at exit worlds outside `Res_β`;
    - `OpenInvReb` by the 6.150 entry.

    `OpenRecord150`'s conclusion there needs the exit world typed. No `TW` constructor other than
    `rebEnd` ends a reborrow, and `RebExitW` does not apply.
  - **How a stop there is reported.** If the generic proof stops at that step, the report checks
    whether another `TW` history types that exit world, and if none does, the report is reading 6
    (§7): a finding about our `TW.rebEnd` and our chooser. Both are `[about ours]`. It is not
    about (a), and it is not about the printed 6.150.
- **If it fails elsewhere.** The step names 6.52, 6.58 or 6.59.
- **Guarantee.** As §3.1's: the view comes back and nothing remains at `β`, on every path. The same
  conditions apply: `ClosedOps`, `NoUnr`, and `CompatW` at the resumer's frame (FINDING-1).

### 3.4 A handler between two lenders

**The configuration.**
- **`L₁`**, the outer lender: a 6.64 frame `e₁` on `ℓ₁ : Ref 1`, variable `'x₁` at `α₁`.
- **`H`**, inside `L₁`: a handler of `n`. Its row `Tin` has `n : 1 ↠ 1`, resuming.
- **`L₂`**, inside `H`: the inner lender, a 6.64 frame `e₂` on `ℓ₂ : Ref 1`. Its borrower `b₂` is
  **abstract**: the 6.64 entry premise at every fresh `α₂`, its run an `ewpW` at `opTableW Tin`
  under `e₂`. Its continuation after a stop is therefore at the fixed `α₂`.
- **A stop of `n` inside `L₂`.** It crosses `L₂` and not `L₁`, so it is at intermediate depth.

Under (a), the stop hands `[e₂]` (with `b₂`'s own entries) to `H`, and `e₁` stays open in the
handler's `σ`. `H`'s clause runs as follows:
1. it allocates `ℓ₃ : Ref (T₃ x₁)`;
2. it lends `ℓ₃` mutably (6.65, by `withborU d₃`);
3. inside that lend it resumes, or cancels, `κ`, then runs `c₃` on the view;
4. it frees `ℓ₃`, and answers.

The three paths:

| path | `Tin`, `Tout` | the clause |
|---|---|---|
| resume | `n` linear; `Tout` empty | `betweenClause d₃ c₃`: `κ (inj₁ ()) ()` inside `L₃`. The clause answers with `κ`'s answer. |
| cancel | `n` affine; `Tout` empty | `betweenClauseCancel d₃ c₃ k₀`: `κ (inj₂ ())` inside `L₃`. The cancel run unwinds `L₂` there. The clause answers with `k₀ ()`, since a cancelled `κ` gives none. |
| drop | `n` linear and an abortive `f : 1 ↠ 0`, which `H` forwards; `Tout = {f}` | `betweenClause d₃ c₃`. After the resume inside `L₃`, `b₂`'s continuation may raise `f`. The raise unwinds `e₂`, then `e₃`, then `e₁`. |

```
betweenClause d₃ c₃ =
  λp. let (_, κ) = p in let r = alloc (inj₁ ()) in
      let q = withborU d₃ r (λ_. λm. let a = κ (inj₁ ()) () in c₃ m ; a) in
      let (r′, a) = q in d₃ r′ ; a
betweenClauseCancel d₃ c₃ k₀ =
  λp. let (_, κ) = p in let r = alloc (inj₁ ()) in
      let q = withborU d₃ r (λ_. λm. κ (inj₂ ()) ; let a = k₀ () in c₃ m ; a) in
      let (r′, a) = q in d₃ r′ ; a
betweenClauses d₃ c₃          = the clause tuple with `betweenClause d₃ c₃` at index 0 (`clauseAt _ 0`)
betweenClausesCancel d₃ c₃ k₀ = the same with `betweenClauseCancel d₃ c₃ k₀`
T₃ ∈ { λ_. 1 ⊕ 1 ,  λx₁. 1 ⊕ Imm 'x₁ 1 }     -- list-stable; reads the record list
```

The answer `a` leaves `L₃`'s callback, so it must lie above `α₃` (6.65's borrower postcondition is
boxed at `α₃`). It does: it is in `L₁`'s borrower postcondition `exitI p₁ α₁ Q`, which is boxed at
`α₁`, and `α₃ ⊏ α₂ ⊏ α₁`.

**`σ` is unordered here, and that limits what this section can say about OQ-3** (§1.4).
- **Where the draft relation stops.** OQ-3's box names the obstruction: a handler between two
  lenders has no place in a lifetime-ordered `σ` (`AllCross`, `StackStep.lean:182`). In this
  draft:
  - `σ` is context-ordered;
  - `wpGW` reads `σ` only through the 6.64 selection;
  - `ewpW` is `σ`-monotone.

  So the obstruction cannot arise. Every result of the (b) arm below answers OQ-3 (b) for an
  unordered `σ` only.
- **What D-ORD would add** (OQ-8): `ResumeOutOfOrder`, below. Inside `L₃`, `κ`'s run holds `e₂`
  under `e₃`, with `α₃ ⊏ α₂`. D-WPG's readers take the stack `τ ++ σ`. Read there, that stack is
  out of nesting order, under (a) and under (b).

**The handler lemma, at every obligation.**

```lean
theorem ewp_handle_W (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (hr hs : Val)
    (Qin Qout : List SRec → Val → WProp)
    (hret : ∀ σ ls v ρ, Qin ls v ρ → ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ τ' σ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ KapRelWB Tout Qout en σ ls τ' κ) ρ →
        ewpW τ' σ ls (.app (.val c) (.pair (.val v) κ.1)) (opTableW Tout) Qout ρ) ∧
      (en.abort = true → ∀ σ ls v ρ, en.PA ls v ρ →
        ewpW [] σ ls (.app (.val c) (.val v)) (opTableW Tout) Qout ρ)) :
    ∀ {τb σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes},
      ewpW τb (.hnd n none :: σ) ls e (opTableW Tin) Qin ρ →
      ewpW τb σ ls (hndE (hndVal n hr hs) e) (opTableW Tout) Qout ρ
```

- **What `τb` is.** It is the entries the handled expression must close by its value. In the
  lemma chain, `τb` holds only entries whose lenders lie inside the handled expression:
  - at the handler's own entry, `τb = []`;
  - at `κ`'s re-entry, `τb = τ′`. There `κ`'s run is `hndE H (K₁.plug w)` holding `τ′ = [e₂]`,
    and `L₂` sits inside the handler.
- **An entry whose lender lies outside the handler** is never in `τb`. The split bind carries it
  outside, or the enclosing frame lemma holds it. In the probes, `L₁`'s frame lemma wraps the
  borrower `hnd H (L₂ b₂)`.
- **Why "at every obligation" matters.** `KapRelWB`'s resume conjunct is an `ewpW τ′` of exactly
  the reinstalled term. The induction predicate is the body's `ewpW` at
  `(τb, hnd n none :: σ)`, at every `τb`, so the induction hypothesis supplies it.

**The clause step is a lemma, not the probe.** It is stated at the postcondition the probes pass,
`L₁`'s borrower postcondition `exitI p₁ α₁ Q`:

```lean
/-- The clause, resumed path: given `κ` holding `[e₂]` at the handler's outer stack `e₁ :: σ`. -/
theorem ClauseBetween {T₃ : LifeVar → VTy} {Tout : OpTab} {en : OpEnt} {p₁ p₂ : FrameRec}
    {α₁ α₂ : Life} {x₁ : LifeVar} {δ : LSub} {Q : List SRec → Val → WProp} {c₃ : Val} {d₃ : Expr}
    {σ : List OEnt} {ls : List SRec} {v κ : Val} {ρ : WRes}
    (hen : en.abort = false ∧ en.q = .lin)
    (hPA : ∀ ls w ρ', en.PA ls w ρ' → ρ' = PMap.empty) (hPB : ∀ ls w ρ', en.PB ls w ρ' → ρ' = PMap.empty)
    (hd₃ : FinW d₃ (T₃ x₁) δ) (hc₃ : C3Sem c₃ (T₃ x₁) δ Tout) (hx₁ : δ.find? x₁ = some α₁) :
    (en.PA ls v ⋆ KapRelWB Tout (exitI p₁ α₁ Q) en (.imm (p₁, α₁) :: σ) ls [.imm (p₂, α₂)] κ) ρ →
    ewpW [.imm (p₂, α₂)] (.imm (p₁, α₁) :: σ) ls
      (.app (.val (betweenClause d₃ c₃)) (.pair (.val v) κ.1)) (opTableW Tout) (exitI p₁ α₁ Q) ρ
```

`ClauseBetweenCancel` is the same at `en.q = .aff`, with `betweenClauseCancel d₃ c₃ k₀` and the
premise `FallbackW k₀ Tout (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q)` (below). `ClauseBetweenA h` is
`ClauseBetween` with `κ` at `KapRelW … (fun σ′ ls′ ρ′ => ExtentOK h [e₂] σ′ ls′ ρ′) …` in place of
`KapRelWB`.
- Each is used by its probe, with `κ`'s relation supplied by the handler lemma's `[op]` case from
  the body's `ewpW`.
- The body's `ewpW` is `L₂`'s entry form: `openInv_entry` for 6.64, then `OpenFrame64` at
  `τi = []`.
- Nothing assumes that `κ` closes `e₂`.

**The 6.65 step out of lifetime order.** Inside the clause, `L₃`'s 6.65 entry runs its callback
holding `κ`'s entries `τi = [e₂]`. Those entries are **older** than `L₃` (checkpoint 2). That is
the one place `YoungerThan` fails, so this step has its own statements:

```lean
/-- `OpenFrame65` without `YoungerThan`: the borrower holds entries older than the lend (a
continuation it resumes or cancels), at a payload type whose relation does not read the record
list. -/
def OpenFrame65OutStable : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : Loc) (α : Life) (S : VTy) (δ : LSub), ListStable S δ →
  ∀ (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ

/-- The same at every payload type. -/
def OpenFrame65Out : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : Loc) (α : Life) (S : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ
```

Their cases are named as §3.1's, with `65Out`: `openFrameResume65Out`, `openFrameCancel65Out`,
`openFrameDrop65Out` and `openFrameVal65Out`. The cancel and drop paths of this configuration use
the last three. No configuration here needs a 6.64 frame with older entries: `L₁`'s borrower holds
none, and `L₂`'s own entries are younger than `α₂`. So no `OpenFrame64Out` is stated.

**The pieces the probes read.**

```lean
/-- `c₃`, run on a `Mut` view of a place, as Core's relation reads the view at the list it runs
at. For a typed `c₃`, `fundamentalC` and `ewpTS_ewpW` give it. -/
def C3Sem (c₃ : Val) (S : VTy) (δ : LSub) (T : OpTab) : Prop :=
  ∀ (ℓ₃ : Loc) (α : Life) (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    ptoMutS ℓ₃ α ls (fun ls₀ => vC true S ls₀ δ) ρ →
    ewpW [] σ ls (.app (.val c₃) (.val (.loc ℓ₃))) (opTableW T)
      (fun _ v ρ' => v = Val.unit ∧ ρ'.InStratum α) ρ

/-- `d : Ref S ⊸ 1` frees the source (`fin_run`'s premise). -/
def FinW (d : Expr) (S : VTy) (δ : LSub) : Prop :=
  closedAt 0 d = true ∧ ∀ ls, wpTS ls d (fun ls'' => vP (.lolli (.ref S) .unit) ls'' δ) PMap.empty

/-- The inner borrower, abstract: 6.64's entry premise at `ℓ₂ : Ref 1`, for every fresh `α₂`
(`wpG_I_frameX`'s premise at `W`). Its run is an `ewpW` at `opTableW Tin`, under the new entry
and `σ`, ending in the borrower postcondition `exitI p₂ α₂ Qb`. -/
def InnerBorrower (Tin : OpTab) (ℓ₂ : Loc) (v₂ b₂ : Val) (δ : LSub) (σ : List OEnt)
    (Qb : List SRec → Val → WProp) (ls : List SRec) : WProp :=
  fresh fun α₂ ρ => ∀ ls', AddAt ls ls' α₂ →
    (∃ r ∈ rsOf ls', r.le = ℓ₂ ∧ r.T = .unit ∧ r.δ = δ) →
    (ptoImmS ℓ₂ α₂ ls' (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpW [] (.imm (⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩, α₂) :: σ) ls'
        (.app (.app (.val b₂) (.val .unit)) (.val (.loc ℓ₂))) (opTableW Tin)
        (exitI ⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩ α₂ Qb)) ρ

/-- The same under OQ-3 (a): the body runs under the marker `hnd n (some h)`, its stops are read
at `extTabW h`, and the entry takes `α₂` below `h`. -/
def InnerBorrowerExt (h : Life) (Tin : OpTab) (n : UInt32) (ℓ₂ : Loc) (v₂ b₂ : Val) (δ : LSub)
    (σ : List OEnt) (Qb : List SRec → Val → WProp) (ls : List SRec) : WProp :=
  fresh fun α₂ ρ => α₂ ⊏ h → ∀ ls', AddAt ls ls' α₂ →
    (∃ r ∈ rsOf ls', r.le = ℓ₂ ∧ r.T = .unit ∧ r.δ = δ) →
    (ptoImmS ℓ₂ α₂ ls' (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpW [] (.imm (⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩, α₂) :: .hnd n (some h) :: σ) ls'
        (.app (.app (.val b₂) (.val .unit)) (.val (.loc ℓ₂))) (extTabW h (opTableW Tin))
        (exitI ⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩ α₂ Qb)) ρ

/-- The body's answer: the pair `withborUE d₂` returns, the place `ℓ₂` owned beside the inner
borrower's answer in `Qb`. This is GhostEnd's `finPost` (`experiments/GhostEnd/GhostEnd/Chain.lean:52`)
with the answer read through `Qb` instead of a type. -/
def finPostW (ℓ₂ : Loc) (δ : LSub) (Qb : List SRec → Val → WProp) : List SRec → Val → WProp :=
  fun ls v => ex fun u => ⌜v = Val.pair (.loc ℓ₂) u⌝ ⋆ (GhostEnd.owner ℓ₂ .unit δ ls ⋆ Qb ls u)

/-- The return clause: from the body's answer, `hr` answers in `L₁`'s borrower postcondition. -/
def HretW (hr : Val) (ℓ₂ : Loc) (δ : LSub) (Qb : List SRec → Val → WProp) (Tout : OpTab)
    (σ : List OEnt) (Qout : List SRec → Val → WProp) : Prop :=
  ∀ ls v ρ, finPostW ℓ₂ δ Qb ls v ρ →
    ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ

/-- `n : 1 ↠ 1`: its argument and answer hold nothing. The clauses discard the argument. -/
def UnitOp (T : OpTab) (n : UInt32) : Prop :=
  ∀ i en ls w ρ', T n i = some en →
    (en.PA ls w ρ' → ρ' = PMap.empty) ∧ (en.PB ls w ρ' → ρ' = PMap.empty)

/-- The cancelling clause's own answer: `k₀ ()`, from nothing, in the handler's outer
postcondition. -/
def FallbackW (k₀ : Val) (Tout : OpTab) (σ : List OEnt) (Qout : List SRec → Val → WProp) : Prop :=
  ∀ ls, ewpW [] σ ls (.app (.val k₀) (.val .unit)) (opTableW Tout) Qout PMap.empty

/-- The premises every between-lenders statement shares. `L₁`'s frame `e₁ = imm (p₁, α₁)` is open
over `ρ`; the handled expression owns `ℓ₂` and holds the abstract inner borrower. -/
def BetweenPremises (Tin Tout : OpTab) (n : UInt32) (T₃ : LifeVar → VTy) (p₁ : FrameRec)
    (α₁ : Life) (x₁ : LifeVar) (δ : LSub) (Q Qb : List SRec → Val → WProp) (ℓ₂ : Loc)
    (v₂ b₂ c₃ hr : Val) (d₂ d₃ : Expr) (σ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  n ≠ 0 ∧ (∀ m i, m ≠ n → Tin m i = Tout m i) ∧
  ClosedOps Tin ∧ Tin.Local ∧ NoUnr Tin ∧ UnitOp Tin n ∧ QExt Q ∧
  δ.find? x₁ = some α₁ ∧ FinW d₂ .unit δ ∧ FinW d₃ (T₃ x₁) δ ∧ C3Sem c₃ (T₃ x₁) δ Tout ∧
  HretW hr ℓ₂ δ Qb Tout (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q) ∧
  OpenInv [] ls (.imm (p₁, α₁)) ρ ∧
  (ptoImmS p₁.le α₁ ls (fun ls₀ => vC true p₁.T ls₀ p₁.δ) ⋆
    GhostEnd.ownerI ℓ₂ v₂ .unit δ ls ⋆
    InnerBorrower Tin ℓ₂ v₂ b₂ δ (.hnd n none :: .imm (p₁, α₁) :: σ) Qb ls) ρ
```

**The probes, OQ-3 (b): no extent.** In each one, `L₁`'s run starts with `e₁` open: `L₁`'s frame
lemma around the handled expression, at the payload type `T₃`. `e₁` is in the conclusion's
obligation.

```lean
/-- The resume path. -/
def HandlerBetweenLendersB (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n : UInt32) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar) (δ : LSub)
    (Q Qb : List SRec → Val → WProp) (ℓ₂ : Loc) (v₂ b₂ c₃ hr : Val) (d₂ d₃ : Expr)
    (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    OpAt Tin n .lin →
    BetweenPremises Tin OpTab.empty n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClauses d₃ c₃))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW OpTab.empty (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ

/-- The cancel path: `n` affine, and the clause cancels `κ` inside `L₃`, then answers by `k₀`. -/
def HandlerBetweenLendersBCancel (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n : UInt32) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar) (δ : LSub)
    (Q Qb : List SRec → Val → WProp) (ℓ₂ : Loc) (v₂ b₂ c₃ hr k₀ : Val) (d₂ d₃ : Expr)
    (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    OpAt Tin n .aff → FallbackW k₀ OpTab.empty (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q) →
    BetweenPremises Tin OpTab.empty n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClausesCancel d₃ c₃ k₀))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW OpTab.empty (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ

/-- The drop path: an abortive `f` that `H` forwards. Raised from `b₂`'s continuation after the
resume inside `L₃`, it unwinds `e₂`, then `e₃`, then `e₁`. -/
def HandlerBetweenLendersBDrop (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n f : UInt32) (enf : OpEnt) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar)
    (δ : LSub) (Q Qb : List SRec → Val → WProp) (ℓ₂ : Loc) (v₂ b₂ c₃ hr : Val) (d₂ d₃ : Expr)
    (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    f ≠ n → f ≠ 0 → enf.abort = true → OpAt Tin n .lin →
    BetweenPremises Tin (OpTab.ext f 0 enf OpTab.empty) n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr
      d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClauses d₃ c₃))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW (OpTab.ext f 0 enf OpTab.empty) (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ
```

Each is instantiated at both payload types: `T₃ := λ_. 1 ⊕ 1` and `T₃ := λx₁. 1 ⊕ Imm 'x₁ 1`.

**The OQ-3 (a) arm: the rule an extent adds, with its obligations.** Under (a) every handler
site opens a stratum, as a borrow does. A borrow's lifetime is chosen at its entry, below what the
borrower holds and inside the lends around it. The reinstalled handler in `κ` is a handler site
too, so it has the same obligation at each call of `κ`:

```lean
/-- 6.112 at a handler entry, read relative to the entries the entered expression holds (as
`extTabW` reads a stop): the closed resource is in `Res_h`, and every tag of the list outside
those entries' lineages is above `h`. -/
def ExtentRes (h : Life) (τ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  (∀ ρc, Close τ ρ ρc → ρc.InStratum h) ∧ (∀ x ∈ ls, (∀ e ∈ τ, ¬ LinOf e x) → h ⊏ x.2)

/-- The site is nested inside every lend and handler extent around it, as a borrow's lifetime is
(D-ORD (3), read at the handler). -/
def ExtentNest (h : Life) (σ : List OEnt) : Prop :=
  ∀ e ∈ σ, ∀ β, e.ordLife? = some β → h ⊏ β

def ExtentOK (h : Life) (τ σ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  ExtentRes h τ ls ρ ∧ ExtentNest h σ

/-- OQ-3 (a)'s `[handle]`: the site opens `h`, chosen at the entry (`ExtentOK`), and the body's
stops are read at `extTabW h`. The reinstalled handler in `κ` re-enters at `h`, so `κ` is handed to
the clause with the re-entry obligation `ExtentOK h τ′` at each call. -/
theorem ewp_handle_W_ext (h : Life) (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (hr hs : Val)
    (Qin Qout : List SRec → Val → WProp)
    (hret : ∀ σ ls v ρ, Qin ls v ρ → ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ τ' σ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ KapRelW Tout Qout en (fun σ' ls' ρ' => ExtentOK h τ' σ' ls' ρ') σ ls τ' κ) ρ →
        ewpW τ' σ ls (.app (.val c) (.pair (.val v) κ.1)) (opTableW Tout) Qout ρ) ∧
      (en.abort = true → ∀ σ ls v ρ, en.PA ls v ρ →
        ewpW [] σ ls (.app (.val c) (.val v)) (opTableW Tout) Qout ρ)) :
    ∀ {τb σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes}, ExtentOK h τb σ ls ρ →
      ewpW τb (.hnd n (some h) :: σ) ls e (extTabW h (opTableW Tin)) Qin ρ →
      ewpW τb σ ls (hndE (hndVal n hr hs) e) (opTableW Tout) Qout ρ
```

- **Where the obligations are used.**
  - *At an entry.* The induction predicate holds at every `σ` and resource where `ExtentOK h`
    holds. A re-entry's `ExtentOK`, the premise of `KapRelW`'s `re`, is what lets the induction
    hypothesis be applied at the call.
  - *At the clause.* `ClauseBetweenA` is `ClauseBetween` with `κ` at
    `KapRelW … (ExtentOK h [e₂]) …`. Its proof must discharge `ExtentOK h [e₂] (e₃ :: e₁ :: σ)` at
    the call of `κ` inside `L₃`.
- **(a) is not (b) with hypotheses added.** In (a)'s rule the clause receives less: a `κ` whose
  relation carries the re-entry obligation. The statements below can fail where (b) holds. Whether
  the draft relation enforces that obligation is a separate question, answered after them
  (`extentObligation_bypassed`).

```lean
/-- OQ-3 (a), the reinstalled handler re-entering at the extent `h` its first entry chose. At the
call of `κ` inside `L₃`:
* `κ`'s share holds `e₂` (`Holds`), and `L₃`'s callback captures that share. So 6.65's H11 for
  `L₃` (`@ρ_b ⊐ α₃`) puts `α₃` below `α₂`;
* the first stop handed `e₂` under `extTabW h`, which puts `α₂` below `h`.
The re-entry's nesting conjunct then fails. -/
def ReentryInheritA : Prop :=
  ∀ (h α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : Loc) (S₃ : VTy) (δ : LSub) (σ : List OEnt)
    (ls : List SRec) (ρk ρb ρκ : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →           -- L₃'s H11
    α₂ ⊏ h →                                                                -- extTabW h, first stop
    ¬ ExtentOK h [.imm (p₂, α₂)] (.mut ℓ₃ α₃ S₃ δ :: σ) ls ρκ

/-- OQ-3 (a), the reinstalled handler opening a fresh extent `h′` at each call, as a new site does.
At the call inside `L₃`, any `h′` meeting the re-entry obligation is below `α₃`, hence below
`α₂`. The second stop of the two-stop program hands `e₂` again, and `extTabW h′`'s first conjunct
fails there. -/
def ReentryFreshA : Prop :=
  ∀ (h' α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : Loc) (S₃ : VTy) (δ : LSub) (σ : List OEnt)
    (ls : List SRec) (ρk ρb ρκ : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →
    ExtentOK h' [.imm (p₂, α₂)] (.mut ℓ₃ α₃ S₃ δ :: σ) ls ρκ →
    ¬ (α₂ ⊏ h')
```

- **What these two statements are.** Each is a short lifetime argument. What carries the weight is
  that every premise is the configuration's own:
  - `h` is the first entry's choice by 6.112, below `α₁`;
  - `α₂` is `L₂`'s entry choice inside the body, below `h`. That is `InnerBorrowerExt`'s `α₂ ⊏ h`,
    which `extTabW h` requires of a lend the stop hands on;
  - `α₃` is `L₃`'s entry choice, forced below `α₂` by H11.

  The instances (§3.5) discharge every premise from the configuration's history.
- **The readings, to be checked** (§7, reading 5).
  - If `ReentryInheritA` is proved, (a) with an inherited extent rejects resuming `κ` inside `L₃`
    at all.
  - If `ReentryFreshA` is proved, (a) with a fresh extent per call accepts one resume. It rejects a
    `κ` that stops again while holding `e₂`, resumed inside a lend younger than `e₂`.
  - Either way (a) imposes, by its own rule, a restriction of the kind OQ-3 (b) names as R-MID.

The draft relation does not enforce these obligations, and the extent's stop check is not what
rejects an argument. These are the statements that make that precise:

```lean
/-- In this draft `ExtentOK`'s nesting conjunct constrains (a)'s rule, not the relation: a `κ`
re-entered under the full obligation at the handler's own stack is `κ` under the resource-and-list
part alone at every extension, by `ewpW_σmono`. -/
theorem extentObligation_bypassed {h : Life} {Tout : OpTab} {Qout : List SRec → Val → WProp}
    {en : OpEnt} {σ : List OEnt} {ls : List SRec} {τ : List OEnt} {κ : Val} {ρ : WRes}
    (hn : ExtentNest h σ) :
    KapRelW Tout Qout en (fun σ' ls' ρ' => ExtentOK h τ σ' ls' ρ') σ ls τ κ ρ →
    KapRelW Tout Qout en (fun _ ls' ρ' => ExtentRes h τ ls' ρ') σ ls τ κ ρ

/-- Under D-ORD (OQ-8), read on the stack the resumed term sits under (`τ ++ σ`, which D-WPG's
readers take). Inside `L₃`, `κ`'s run holds `e₂` above `e₃`, out of nesting order. That holds under
OQ-3 (b), where the marker carries no lifetime, and under (a), where the marker's extent lies
between them. -/
def ResumeOutOfOrder : Prop :=
  ∀ (n : UInt32) (mk : Option Life) (α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : Loc) (S₃ : VTy)
    (δ : LSub) (σ : List OEnt) (ρk ρb : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →
    ¬ List.IsChain (· < ·)
        (([.imm (p₂, α₂), .hnd n mk, .mut ℓ₃ α₃ S₃ δ] ++ σ).filterMap OEnt.ordLife?)

/-- Where the extent acts at a stop, past `ClosedOps`. An argument holding a copy of `κ`'s entry's
view, below `h`, is rejected by the table's `CompatW`, the check both options share. `extTabW h`
admits it, because closing the whole stop resource closes the copy with the view. -/
def ArgBelowExtent : Prop :=
  ∀ (h α₂ : Life) (p₂ : FrameRec) (hR : p₂.R.InStratum (LSet.singleton α₂).join)
    (ρk ρ : WRes),
    α₂ ⊏ h → Holds [.imm (p₂, α₂)] ρk → (∀ ρc, Close [.imm (p₂, α₂)] ρk ρc → ρc.InStratum h) →
    ResU.CompS (ResU.single p₂.le (CellU.immOf (LSet.singleton α₂) p₂.v p₂.R hR)) ρk ρ →
    ¬ CompatW [.imm (p₂, α₂)]
        (ResU.single p₂.le (CellU.immOf (LSet.singleton α₂) p₂.v p₂.R hR)) ρk ∧
      (∀ ρc, Close [.imm (p₂, α₂)] ρ ρc → ρc.InStratum h)

/-- An argument holding a copy of `L₁`'s view, above `h`, at a place `e₂`'s exit does not touch,
is admitted by both. -/
def ArgAboveExtent : Prop :=
  ∀ (h α₁ α₂ : Life) (p₁ p₂ : FrameRec) (hR : p₁.R.InStratum (LSet.singleton α₁).join)
    (ρk ρ : WRes),
    h ⊏ α₁ → p₁.le ≠ p₂.le → Holds [.imm (p₂, α₂)] ρk →
    (∀ ρc, Close [.imm (p₂, α₂)] ρk ρc → ρc.InStratum h ∧
      ResU.Hash (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρc) →
    ResU.CompS (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρk ρ →
    CompatW [.imm (p₂, α₂)]
        (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρk ∧
      (∀ ρc, Close [.imm (p₂, α₂)] ρ ρc → ρc.InStratum h)
```

- **What these say, if proved.**
  - **The relation does not enforce (a)'s nesting.** By `extentObligation_bypassed`, a clause can
    use `κ` inside `L₃` through the resource-and-list part of the obligation. That part holds
    there: `L₃` is a 6.65 lend and leaves no tagged record. So in this draft the semantic content of
    `ClauseBetweenA` is `ClauseBetween`'s, and `ReentryInheritA` constrains (a)'s rule only.
  - **Where the list would see it.** An enclosing 6.64 frame does leave a tagged record. So
    `ExtentRes`'s tag conjunct would see that frame in the list. A 6.65 lend is visible only in
    `σ`, which ties this to OQ-44's point (1).
  - **At a stop.** `ArgBelowExtent` and `ArgAboveExtent` say the extent's check rejects nothing
    `CompatW` admits, at this configuration's stop. A copy of a view below `h` is the one way an
    argument can carry a cell below `h` there. It needs an operation type that holds a borrow, which
    is outside `ClosedOps` (§1.8).
  - **Under D-ORD.** `ResumeOutOfOrder` says D-ORD rejects the resume inside `L₃` under both
    options.
- **What this section does not claim.** It does not claim that (a) and (b) agree. It states, in
  Lean, where each can be told apart: at (a)'s rule, and at D-ORD. It states that the draft
  relation cannot tell them apart. That is FINDING-2.

**OQ-3 (a)'s second reading is not tested here.** OQ-3's box also reads (a) as "control handlers
are borrows the same way answering handlers are". An answering handler lends its state to the
body (`handle_is_shift`), so every stop to it would end that lend by 6.65's exit.
- That exit boxes the stop's share at `h`. Under OQ-9 (a) the share holds the cells of the entries
  it hands on, below `h`.
- So the reading needs 6.65's exit at a stop with its box read relative to `Close`
  (`StateLendExitRel`). That is an extension of the printed exit, whose box is at the borrower's
  return.
- Stating and attempting it is a unit of its own. This unit says nothing about it.

**Checkpoints, in the order a proof meets them.**

1. **`CompatW` at the resume.** `KapRelWB`'s resume is an `ewpW [e₂]`. Its frame must be
   compatible with `e₂`'s closure. That frame is `ρs ● ρo` (`compat_resume`):
   - `ρs`: the stop's frame and leftover, and `PA` (`compat_at_stop`);
   - `ρo`: the clause's own resources. These are `ℓ₃`'s `own` cell, now in `L₃`'s escrow, and
     `L₃`'s view at `ℓ₃`, a fresh place that `e₂`'s closure does not touch.

   Each is checked directly. A clause read only through a relation is FINDING-1.
2. **The clause's lend is inside `κ`'s.** `L₃`'s callback captures `κ`, whose share holds `e₂`'s
   view at `α₂`.
   - The printed 6.65 H11 forces `α₃ ⊏ α₂`, and so does Core's `ptoMutX_create` `hfresh`.
   - So `κ`'s run ends `e₂`, the older lend, while `L₃`, the younger, is open. On the cancel path,
     the cancel run ends it. On the drop path, the unwinding ends it.
   - `L₃`'s entry runs its callback with `τi = [e₂]`. That is `OpenFrame65Out`'s case.
3. **After `e₂` closes.** On the resume path, `κ`'s value removes `e₂`'s records from the list
   (`StopW`). On the cancel path, the cancel run does. On the drop path, `L₂`'s `ubind` does.
   - `L₃`'s `OpenInv`, and `C3Sem` on the resume and cancel paths, both need
     `ptoMutS ℓ₃ α₃ ls′ P` at the new list. `ptoMutS` demands `ofS Q = P ls₀′`, with `Q` frozen at
     `ls₀ ∋` `e₂`'s records.
   - At the list-stable `T₃`, `P` is constant, and `OpenFrame65OutStable` re-establishes it.
   - At the list-reading `T₃`, `CohE` at `p₂.le` gives `P ls₀ ≠ P ls₀′` as predicates. This is the
     diagnostic below, stated at the configuration's arising world. Its distinguishing input need
     not arise, so a refutation of it measures our `ptoMutS`'s predicate equality, not (a).

   ```lean
   def MutViewSurvivesOlderClose (T₃ : LifeVar → VTy) : Prop :=
     ∀ (ℓ₃ : Loc) (α₃ : Life) (x₁ : LifeVar) (δ : LSub) (p₂ : FrameRec) (α₂ : Life)
       (ls ls' : List SRec) (ρ : WRes),
       (∀ x, x ∈ ls' ↔ (x ∈ ls ∧ ¬ LinOf (.imm (p₂, α₂)) x)) →
       ptoMutS ℓ₃ α₃ ls (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ →
       ptoMutS ℓ₃ α₃ ls' (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ
   ```
   **Built** (`WorldW/Diag.lean`): `mutViewSurvives_stable` proves the diagnostic at `λ_. 1 ⊕ 1`;
   `not_mutViewSurvives_reads` refutes it at `λx₁. 1 ⊕ Imm 'x₁ 1`, at an input with the older
   record in the list and a view of its place (not built from a `TW` history). So the
   list-reading probes would stop here, at our frozen list, as this checkpoint predicts.
4. **`L₃`'s exit.** 6.65's H35 reads the content at the exit list (`vC_local` along
   `Ext ls₀ ls″ χ`). With `χ` the content `inj₁ ()`, this holds. On the drop path the exit is at
   the abortive stop (`openFrameDrop65Out`). It closes `e₃` after `e₂`: context order, the reverse
   of lifetime order.

- **Why it is the real question.** It is the configuration OQ-3 and R-MID name, at `W`, on all
  three paths.
  - The inner lend is open across the stop. It is resumed or cancelled by a handler that has a lend
    of its own, or dropped through that lend.
  - `b₂` is abstract, so the inner lend cannot be ended at the stop.
  - `KapRelWB` comes from the body.
  - `c₃` is abstract and read through Core's relation. So the proof cannot step around the
    relation with a hand argument about one concrete write.
- **Guarantee, at an unordered `σ`.**
  - *What it gives.* Lifetimes are respected on every path. The Kripke reading of the relation
    (`Ext`, `docs/adjudications.md` §12.72) is kept along every run. No handler receives the owned
    cell of a lent place (`Holds`).
  - *On what conditions.* `ClosedOps`, `NoUnr`, and `CompatW` at the resumer's frame. This
    section's clauses are given by code, so `compat_at_stop` and `compat_resume` discharge it; a
    clause read through a relation is FINDING-1.
  - *What holds by assumption.* No handler holds a view of the inner lend past its end: that holds
    by `ClosedOps` (no argument or answer holds a borrow cell). It is not a check this unit tests.
    The argument variant tests only where the extent's check acts.
- **How a failure is reported.** An obstruction is reported only in two forms:
  - a refutation of `HandlerBetweenLendersB*` at an arising world with an arising input;
  - a refutation of a statement whose hypotheses are a TW-arising configuration, with `C3Sem`
    discharged by `fundamentalC` on a concrete `c₃`.

  Suppose the list-stable probes close and the list-reading probes stop at checkpoint 3. The
  report is then a finding about our frozen list (`ptoMutS`, `Ext`'s second conjunct, both
  `[about ours]`). It lists the user's options in this order:
  - revise our frozen list, so that closing an older frame while a younger cell exists is an
    `Ext` step at that cell;
  - OQ-9 (b) between lenders, where the re-lend at `α₂′ ⊏ α₃` restores lifetime order;
  - the named restriction R-MID.
- **Comparison point.** Under (b), the same configuration has no checkpoint 3.
  - At the stop `e₂` ends, so its records are gone before `L₃` opens, and `L₃`'s `ls₀` never holds
    them.
  - Inside `L₃`, the re-lent `e₂′` is at `α₂′ ⊏ α₃`, outside `L₃`'s `ls₀`.
  - GhostEnd has no Lean for (b) between lenders either: `AllCross` excludes it
    (`StackStep.lean:182`, #278).

### 3.5 Non-vacuity: the instances

Each instance discharges every hypothesis from a `TW` history (§5). They are in
`WorldW/Instances/`.

- **F-CLOSE.**
  - The absorbed-view configuration, with the two closures of its stop: `mut@l′` in `ρ_P̂`, and
    not.
  - `UnpinnedIncoherent`'s resource `[anti l …, reb … β′ χ]` with `β ⊏ β′`. It is about our
    `Close`, and it need not arise.
- **F0**: the nested-copy configuration of §5.
- **`holds_exclusive`**: `withbor1` then `withload`; two reborrows of one view; the nested
  `withbor3`.
- **`dropKappa_by_surgery`**: at the between-lenders first stop's share, with the postcondition
  that accepts the place.
- **`OpenFrame64` and `OpenFrame65`**, each from the entry (`openInv_entry`):
  - **resume**: the borrower `yield; return ()` at `{yield : I32 ↠ 1}`;
  - **resume, then cancel**: the borrower `yield; yield; return ()` at `{yield : I32 ↠^aff 1}`.
    The handler resumes the first stop and cancels the second, so the cancel run meets the frame
    handed across the first, resuming stop. This is `spans_two_affine_yields`'s program, at `W`
    and under (a);
  - **resume, then drop**: the borrower `yield; raise fail ()` at
    `{yield : I32 ↠ 1, fail : 1 ↠ 0}`. The abortive stop meets the frame handed across the
    resuming stop;
  - **`τi ≠ []`**: the borrower `withborU d′ ℓ′ (λ_. λm′. yield; return ()) ; return ()`. The inner
    lend spans the yield, so `τ′ = [e′, e]` at the stop, and the resumption exercises `τi = [e′]`
    under `YoungerThan`.
- **`OpenFrame66`**:
  - the body `yield; return ()` holding the unfolded content;
  - the nested `withbor3` instance of §3.2. It is a 6.65 lender on `ℓ`, whose borrower reborrows
    its view by `withbor3`, and whose inner callback yields once. Three entries are open on one
    place at the yield.
- **`OpenRecord150`**: a reborrow callback yielding once with the reborrow open, in the shape of
  `withbor_reborrow_spans_yield`, at `W`. `RebExitW` is discharged there by `rebChooseTW_top_W`.
- **The younger-lend configuration** is a test of `OpenRecord150`, not an instance of it (§3.3):
  a handler clause opening a 6.65 lend around `κ`'s resume, while `κ` holds the reborrow.
- **`OpenFrame65OutStable` / `OpenFrame65Out`**: the out-of-order case `τi = [e₂]` at `L₃`'s
  entry, on the resume, cancel and drop paths. Each is discharged from the between-lenders history
  at both payload types.
- **`HandlerBetweenLendersB`, `…Cancel`, `…Drop`**, each at both payload types, with:
  - `b₂ = perform n; return ()` for the resume and cancel paths;
  - `b₂ = perform n; raise (f, ())` for the drop path;
  - `c₃ = λm. m := inj₁ (); ()`, `d₂ = d₃ = free`, and `hr = λ(r′, u). d₂ r′; u`;
  - on the cancel path, `k₀ = λ_. ()`, with `Q` the postcondition `L₁`'s exit hands the owned
    `ℓ₁` and `()` to.
- **The OQ-3 (a) arm.**
  - `ReentryInheritA`'s premises come from the resume path's history, with `InnerBorrowerExt` for
    `L₂`'s entry under the extent.
  - `ReentryFreshA`'s come from the two-stop program `b₂ = perform n; perform n; return ()`, at its
    second stop.
  - `ResumeOutOfOrder`'s come from the same histories, and so does `extentObligation_bypassed`'s
    premise `ExtentNest h (e₁ :: σ)`, from the first entry's choice `h ⊏ α₁`.
- **`ArgBelowExtent` and `ArgAboveExtent`**: at the first stop, with the argument a copy of `e₂`'s
  view and a copy of `e₁`'s view respectively.

### 3.6 What the probes compose into

At a row that mixes linear, affine and abortive operations:
- `OpenFrame64`, `OpenFrame65`, `OpenFrame66` and `OpenRecord150` are the continuation halves of
  T-FRAME at `W`, under (a);
- with the four entry lemmas (§4) they are T-FRAME;
- `withbor1` is the 6.64 one, `withbor2` the 6.65 one, and `withload` the 6.150 one;
- `withbor3` is `OpenFrame66` around `OpenFrame65`, with two entries on one place
  (`close_relend_anti`).

Between lenders, the frame lemmas compose with `ewp_handle_W` through `OpenFrame65Out`, on the
resume, cancel and drop paths. This composition holds without restriction only if
`OpenFrame65Out` does, and that depends on the outcome of checkpoint 3. Every such composition is
at an unordered `σ` (§1.4).

---

## 4. Plan of proof

### 4.1 The split (a) makes and (b) does not

Core's `wpG_I_frameX`/`wpG_M_frameX` never inspect the final term (`Core/EffWp.lean:12-15`). So
under (b) the printed proof is applied whole at every unfolding, at a value and at a stop alike.
That is GhostEnd's `ewpTS_I_frameR`: no case on the final term. Under (a) this cannot be done:

- **The exit** is applied at the borrower's return, or at an abortive stop or a cancel's end. For
  6.64 it is H19–H36. For 6.65 it is H24–H35. For 6.66 it is H20–H26. For 6.150 it is H24–H33.
  It is **not** applied at a resuming stop.
- **At a resuming stop** the entry is handed on. Only the lemmas that give the relativised `↭`
  are applied, with `TabAt` in place of the boxes.

So under (a) the printed proof is used in two halves at different unfoldings: the entry at the
first, the exit at the last.
- A value/stop split is introduced inside the frame proof. The paper does not make it (CLAUDE.md
  §6).
- Its stop case incurs obligations the printed proof never does: `TabAt` in place of the box,
  `Holds`, `CompatW`, and `StopW`'s freshness.
- This is not a shorter route: every printed step is taken.
- Under (b) the invention sits in the relation instead (the re-lendable borrower,
  `RelendI`/`vRL*`), which is not printed either.

Both are stated in the report.

### 4.2 Lemmas at `W` the probes rest on (`WorldW/Wp.lean`)

- **`ewpW_ind`, `ewpW_fold`, `ewpW_unfold`, `ewpW_mono`, `opTabW_mono`, `ewpW_σmono`.** These are
  `ewp`'s proofs with `τ` and `σ` threaded (`Core/EffWp.lean:748-806`).
- **`wpGW_bind_split`:**
  `wpGW τ₁ (τ₂ ++ σ) ls e (λ τ′ ls′ t. wpGW (τ′ ++ τ₂) σ ls′ (K.plug t) Q) ⊨ wpGW (τ₁ ++ τ₂) σ ls (K.plug e) Q`.
  The obligation `τ₂` stays with `K`. `τ₂ = []` is `wpG_bind` (`Core/EffWp.lean:878`), and
  `τ₁ = []` runs a sub-computation that closes nothing.
  - Conjunct (37) is composed through `Close` and `close_append`. `τ₂`'s entries are closed on
    both sides of the inner run's `↭`, by:
    - 6.39 with H1/H2 from `CompatW` (`imm`);
    - 6.28 (`mut`, `anti`);
    - 6.59 with the split `ρ′ := ∅` (`reb`).
  - **6.48** (`updV_frame`) then frames the first run's leftover into the second run's `↭`.
  - **6.49** (`ResU.UpdV.trans`) chains the two runs. The intermediate resource is closed twice:
    by the first run's stop, at `τ′ ++ τ₂`, and by the second run's start, at the same list.
    `close_upd_coherent` relates the two closures, so the chain does not depend on which closures
    each run picked.
  - The inner frame's `CompatW τ₁` comes from the outer frame's `CompatW (τ₁ ++ τ₂)` by 6.34:
    compatible with the more-closed form implies compatible with the less-closed form.
- **`wpGW_frame`** frames out an `R` with `CompatW τ R ρ`, by `close_frame`. Also
  `wpGW_garbage`, `wpGW_here` and `wpGW_step`, as in Core.
- **`ewpW_I_forget`/`ewpW_M_forget`**: **6.149**/**6.148**, lifted by induction. A view is carried
  through each unfolding, kept in the share at a stop, and left in the leftover at a value. This
  is how `CompatW τ′ ρp ρ′` is met.
- **`wpGW_box_rel`**: **6.147** at `wpGW`, relative to `Close`. `↭` keeps strata (**6.50**), so if
  the closure of the start is in `Res_h`, so is the closure of every final resource. Its form at
  today's stop is GhostEnd's `wpG_box`. It gives `extTabW`'s second conjunct from a body that
  starts in `Res_h`.
- **The entry lemmas** (`openInv_entry` and the ghost step):
  `wpGW [e] σ ls e Q ρ_lent ⊨ wpGW [] σ ls e Q ρ_owned` when `Close [e] ρ_lent = ρ_owned`. The
  frame's world comes from the entry's `TW` constructor. One per kind:
  - **6.64:** H1–H18: 6.112, 6.104, 6.34/6.10/6.11/6.15, H4, `TW.immFrame`;
  - **6.65:** H1–H17 with `ptoMutX_create`, spending `P̂ ⊨ [β]P̂`, and `TW.mutFold`;
  - **6.66:** H1–H9 with 6.24 and `TW.mutUnfold`;
  - **6.150:** H1–H23 with 6.55, `RebChooseTWW`'s entry clause and `TW.reb`.

  **Freshness at the entry.** The 6.64 and 6.65 entries take `α` below the И bound and below every
  lifetime of `W`:
  - the resource and the tags, as H4 does;
  - `σ`'s entries;
  - under OQ-3 (a), the extent of each marker in `σ`.

  H4 picks "some `α ⊏ γ`" (6.64) or "some `α ⊏ γ ⊓ β`" (6.65), and any smaller `α` is such a
  lifetime. The entry lemma's conclusion records the choice:
  `∀ e ∈ σ, ∀ γ, e.ordLife? = some γ → α ⊏ γ`. That conjunct is `relend_below_anti` inside a
  6.66 body, and `α₂ ⊏ h` inside a handler body under (a).

  Together with §3's statements, the entry lemmas are T-FRAME at `W`.
- **`ewp_handle_W`**: `ewp_handle` (`Core/EffRules.lean:615`) with the body at `hnd n none :: σ`,
  at every `τb`.
  - The `[op]` case hands `(τ′, σ)` to the clause.
  - `KapRelWB` is built from the share by `ewp_kappa_resume`/`ewp_kappa_cancel` and `ewp_ccatch`
    at `W`, and by `σ`-monotonicity.
  - The induction predicate is the body's `ewpW` at `(τb, hnd n none :: σ)`, for every `τb`.
- **`ewp_handle_W_ext h`**: the same, with these changes.
  - The body runs at `extTabW h (opTableW Tin)` under `hnd n (some h) :: σ`.
  - The induction predicate holds at every stack and resource where `ExtentOK h` holds.
  - The `[op]` case hands the clause `KapRelW … (ExtentOK h τ′)`. A call's `ExtentOK` is the premise
    under which the induction hypothesis re-enters the handler at `h`.
  - Stops of the body meet `extTabW h` by `wpGW_box_rel` and the entries' freshness below `h`.
- **`ewp_then_owner_W`**: GhostEnd's `ewp_then_owner` at `W`: a `ubind` around a callback whose
  stops hand back the owner. It uses `cancel_then` at `W`. With the frame lemmas it composes
  `withborU`.

### 4.3 6.64, continuation form

The proof is by induction on the borrower's `ewpW` (`ewpW_ind`), with the predicate

`X τ σ ls e ρ := ∀ τi, τ = τi → σ = e₀ :: σ₀ → YoungerThan τi α → OpenInv τi ls e₀ ρ →
ewpW (τi ++ [e₀]) σ₀ ls e (opTabW T ownerI) Q ρ`.

At each unfolding, the borrower's `wpGW τi (e₀ :: σ₀)` is instantiated at the lender's frame. Its
`CompatW τi` follows from `CompatW (τi ++ [e₀])` by 6.34, and the frame list is
`immRecs τi ++ (p :: ps)`. The lineage of `p` in the list, with tag `α`, comes from that frame
premise (§1.7).

The borrower's closures are pinned against its own later entries (`Close τi`); the lender's
against `τi ++ [e₀]` (`ClosePre τi [e₀]`). A closure that meets the longer pin meets the shorter
one. In the other direction, `pin_harmless` lets the lender take the borrower's closures as its
own, wherever `OblWf (τi ++ [e₀])` holds (reading 7). By `upd_choice_free` the borrower's `↭`
holds at those closures too.

- **Value (the borrower returns): 6.64's exit, H19–H36, as `wpG_I_frameX` writes it.**
  - **6.29**: the view is at the top level of `π`. Its H1 is `CompatW`'s instance at `e₀`, and its
    H3 is `TabAt`, in place of H11.
  - **6.38**: G1, with H3 from `TabAt` and H4 from `exitI`'s box.
  - **6.26 + 6.8**: the memories.
  - **6.39**: `Close (τi ++ [e₀]) ρ ↭ π/ℓ ● ℓ ↦ own(v) ● R`.
  - `TW.immEnd`.
  - `frameLife_back` for `Tagged`. Its `q ≠ p` step comes from the value clause (§1.7).
  - `ext_drop` with `QExt`, to bring `Q` to the list without `e₀`'s records.
- **Resuming stop: hand on, no exit.**
  - (i) If the borrower left its view in the leftover, move it into `ρ′`. `imm` cells compose
    idempotently, and `ewpW_I_forget` makes the continuation accept it.
  - (ii) **6.50** (`GhostEnd.tabAt_updV`) on the borrower's relativised `↭`:
    `TabAt (Close τi ρ) ⊨ TabAt (Close τ′ π)`.
  - (iii) **6.38** at the stop, with the split view ↦ `ρ⁺`, rest ↦ `ρ′`. Its H1 is `CompatW` at the
    start, its H3 is `TabAt` at the start, and its H4 is `TabAt` at the end, off `ℓ`. This gives
    G1: `e₀`'s exit is defined at the stop, and the frame is compatible with it (`StopW`'s
    `CompatW`).
  - (iv) **6.39** with the view on both sides:
    `Close (τi ++ [e₀]) ρ ↭ Close (τ′ ++ [e₀]) π`.
  - (v) `StopW`: `ps′ = immRecs (τ′ ++ [e₀]) ∪ (ps ∖ immRecs τi)`. The new entries are below `α`, so
    freshness holds and so does `YoungerThan τ′ α`. Both `CompatW`s hold.
  - (vi) The table. The borrower's `shareW τ′` gives the lender's `shareW (τ′ ++ [e₀])` by the
    induction hypothesis.
    - Its cancel conjunct is `openFrameCancel64` on the borrower's `owedW`.
    - The answer is closed (`ClosedOps`), so `share ● ans` keeps `TabAt`.
    - The payload's `vC` is carried by the share's `Ext`.
    - `Holds (τ′ ++ [e₀])` holds because the view is in the share.
- **Abortive stop and cancel's end:** §4.4.

### 4.4 Cancel and drop (6.64)

Both ends are abortive (`cancelTabW`; `opTabW`'s raise clause owes nothing), so each is one
`wpGW`. The exit is applied at them with no case split.

- **Cancel.** At the cancel's end, split the final resource.
  - The error's resource (`errOk`, which is `emp` at `none`) goes to `ρ′`.
  - Everything else, the view and the abandoned context, goes to `ρ⁺`.
  - Then apply 6.29, 6.38 (H4: `ρ′ ∈ Res_α`), 6.39 and `TW.immEnd`, with the owner beside the stop
    (`withOwnerW`).
- **Drop.** This is `ewp_end`/`ewp_box_end`'s argument (`Core/EffBorrow.lean:97, 118`).
  - The argument is closed, so it is in `Res_α`, and the abandoned continuation joins `ρ⁺`
    (`wpGW_garbage`).
  - The exit is the same, and the owner is handed beside the stop.

### 4.5 6.65

The structure is the same, with 6.65's lemmas:

- **6.27**: the cell is at the top level, with H11 replaced by the rest-above-`α` conjunct;
- **6.24**: the closure is defined, with no stratum hypothesis. `CompatW` is `Hash` (F1);
- **6.25 + 6.8**: the memories;
- **6.28** (an iff): the relativised `↭`, at the exit and at a hand-on stop alike;
- `TW.mutUnfold`;
- H35's payload, read off the frozen predicate (`vC_local`). Under `YoungerThan`, `ls∣⊐b` is
  unchanged by the stop's list change.

The hand-on needs no 6.38: the exclusivity of the `mut` cell (6.42) does the work that 6.38's
domain argument does for `imm`. **6.112** and H4 are in the entry only (§4.2). The premise
`P̂ ⊨ [β]P̂` is spent there (`ptoMutX_create`'s `hunif`).

For the `…Out` statements, the stop's list change may remove records `⊐ b`.
- In `…OutStable`, `ptoMutS` is re-established with `ls₀′ := ls′∣⊐b`, because `P` is constant
  (`ListStable`).
- In `…Out` that step is where our frozen list bites (checkpoint 3).
- Their cancel and drop cases apply the exit at the cancel's end and at the abortive stop, as §4.4
  does for 6.64.

### 4.6 6.66

- **Exit (value, abortive stop, cancel's end):** H20–H26.
  - The body hands back `ℓ ↦ v″ ⋆ P̂(v″)` and takes the view.
  - `ρ″_m = ℓ ↦ mut(β, v″, ρ_P̂(v″), P̂)` is formed. 6.24 gives the compatibility block.
  - **6.25 + 6.8** give the memories, and **6.28** gives `↭`.
  - `TW.mutFold` types the world. `ptoMutX_write` writes the content into the unchanged stored
    predicate, as `wpG_M_antiFrameX` does.
  - At an abortive stop or a cancel's end, the refolded view is handed beside the stop.
- **Hand-on:** **6.28** on both sides refolds the unfolded content in `Close`. The `own` cell and
  its payload stay in the share (`Holds`), and no `TW` step is taken. The refold's split meets
  `AntiPin` by `pin_harmless` where `OblWf` holds.
- **Two entries on one place:** `close_relend_anti`. The 6.65 entry inside closes first, and its
  exit's `own(v″) ● χ` is the anti exit's input.

### 4.7 6.150

- **Exit:** H24–H33.
  - **6.52** splits the leftover as `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`.
  - **6.58** gives the memories and **6.59** gives `↭`. The view goes into the leftover.
  - `TW.rebEnd` at the exit world comes from `RebExitW`, whose `Keeps` premise holds along the
    run: `keeps_of_ext` at each resume, `keeps_of_stopW` at each of the borrower's stops.
  - `tagged_rebEnd` gives `Tagged`.
- **Hand-on:** **6.59** with `ρ′ := ∅`, `ρ⁺ :=` the stop's resource (§3.3). The borrower's run has
  the view in its frame. `OpenInvReb`'s `Xr ∈ Res_β` supplies 6.59's `@ρ_b ⊐ β`, and no `TW` step
  is taken.
- **The step to watch:** `RebExitW`'s stratum premise, at an exit world that holds a cell below
  `β` (reading 6).

### 4.8 Between lenders

1. `L₁`'s run is its frame lemma around the borrower `hnd H (L₂ b₂)` at `(τ = [], e₁ :: σ)`: that
   is `OpenFrame64` at `τi = []`, from `OpenInv [] e₁`. That borrower's `ewpW` comes from
   `ewp_handle_W`.
2. The body `L₂ b₂` is the 6.64 entry lemma, then `OpenFrame64`. Its stops of `n` hand `[e₂]`.
3. The `[op]` case gives the clause `(PA ⋆ KapRelWB … (e₁ :: σ) ls [e₂] κ)`. Apply
   `ClauseBetween` (resume, drop) or `ClauseBetweenCancel` (cancel):
   - `alloc`, then `withborUE_beta`;
   - the 6.65 entry lemma for `L₃` at `wpGW [e₂] (e₁ :: σ)`, whose callback holds `τi = [e₂]`
     (checkpoint 2);
   - `OpenFrame65OutStable` or `OpenFrame65Out` for `L₃`'s callback;
   - inside the callback, `KapRelWB`'s resume (or cancel) at `extra = [e₃]`, with checkpoint 1's
     frame;
   - `C3Sem` at the list after `e₂` closes (checkpoint 3);
   - `L₃`'s exit (checkpoint 4);
   - `ewp_then_owner_W` for the finaliser path;
   - `d₃ r′`, and the clause answers with `a`: `κ`'s answer (resume, drop), or `k₀ ()`'s
     (cancel, by `FallbackW`).
4. `hr` returns, the handler returns, and `L₁`'s exit closes `e₁`. On the drop path the raise of
   `f` reaches `Tout` after `L₁`'s `openFrameDrop64`, with `ℓ₁`'s owner beside the stop.

**The OQ-3 (a) arm.**
- `ewp_handle_W_ext` is `ewp_handle_W`'s proof with `extTabW` forwarded and `ExtentOK` threaded.
- `ReentryInheritA` and `ReentryFreshA` are lifetime arguments: `⊏` is strict, so neither
  `h ⊏ α₃ ⊏ α₂ ⊏ h` (inherited extent) nor `h′ ⊏ α₃ ⊏ α₂ ⊏ h′` (fresh extent) can hold. Their
  premises are discharged at the configuration.
- `extentObligation_bypassed` is `ewpW_σmono` at `extra = []`.
- `ResumeOutOfOrder` is the same strict-order argument on the stack's lifetimes.
- `ArgBelowExtent` and `ArgAboveExtent` are resource arguments.
  - Below `h`: after closing `e₂`, `p₂.le` is `own` and the copy is `imm`, so `#` fails; the whole
    stop resource holds one merged `imm` cell at `p₂.le`, which the closure consumes.
  - Above `h`: the copy of `e₁`'s view is untouched by `e₂`'s closure.

Order of attack:
1. the list-stable resume probe (it has none of our frozen list in it, so its outcome is about (a)
   between lenders alone);
2. the list-stable cancel and drop probes;
3. the list-reading probes, whose only new step is checkpoint 3;
4. the (a) arm;
5. the argument variant.

---

## 5. Arising: what a counterexample must pass

A refutation steers nothing until its witness arises in `TW` (`Core/World.lean:110`). For each
probe:

- **`OpenFrame*`.** The world is reached from `TW.empty` by:
  - `TW.alloc` of `ℓ` (and of `R`'s cells);
  - the entry's constructor, each lifetime chosen as §4.2's entries choose it:
    - `TW.immFrame` for 6.64;
    - `TW.mutFold` for 6.65;
    - `TW.mutUnfold`, of a cell a `TW.mutFold` made, for 6.66;
    - `TW.reb` at a record's cell, for 6.150;
  - the borrower's own operations;
  - at each earlier stop, only operations of other runs that keep `CompatW`: the handler's
    clause allocating, or opening frames of its own places.

  `OpenInv` must be **derived** from that history (`openInv_entry`, then 6.50 at each run). It is
  never assumed of a configuration built directly. `OpenInv` is the frame lemma's invariant, not
  an arising test. A counterexample that assumes it of an unreached resource measures nothing.
  The configuration must also be one the machine reaches: an `ARun` from the program's start.
- **F0: the nested-copy configuration.**
  1. `TW.empty`, then `alloc ℓ`.
  2. `TW.immFrame` for `e` at `α`, giving `ℓ ↦ imm({α}, v, R)`.
  3. `alloc ℓ′ ↦ own(loc ℓ)`.
  4. `TW.immFrame` on `ℓ′` with `R′ = ℓ ↦ imm({α}, v, R)` at `β`, the split `X ● Z` keeping the
     top-level view in `Z`. `TW.immFrame` has no freshness or ordering premise.
  5. Split `ρf = ℓ′ ↦ imm({β}, loc ℓ, R′)`, with `ρ` holding the top-level view.

  Then `ResU.Hash ρf ρ`, `TW` and `Tagged` hold, with `ℓ′`'s record in `ps`. There is no top-level
  cell at `ℓ` in `ρf`, but `ρf.FlatAt ℓ (imm …)` holds. This world arises.
- **F-CLOSE: the absorbed-view configuration.** `alloc l′`; `mutFold` (`L′`, `α′`); `alloc l`;
  `mutFold` (`l` lent at `β ⊏ α′`); `mutUnfold` (the anti on `l`); `mutFold` (the relend at
  `α ⊏ β`); the stop.
- **Between lenders** (and `OpenFrame65Out*`, `MutViewSurvivesOlderClose`, the (a) arm):
  1. `TW.empty`, `alloc ℓ₁`, `immFrame` (`L₁`, `α₁`).
  2. `alloc ℓ₂`, `immFrame` (`L₂`, `α₂ ⊏ α₁`; under the (a) arm, `α₂ ⊏ h ⊏ α₁`).
  3. The stop.
  4. `alloc ℓ₃`, `mutFold` (`L₃`, `α₃ ⊏ α₂`).
  5. Then one of the three paths:
     - **resume**: the resume, then **`TW.immEnd` at `p₂` while `L₃`'s cell exists**, `free ℓ₂`;
     - **cancel**: the cancel run, `TW.immEnd` at `p₂` at the cancel's end, `free ℓ₂`, `ccatch`;
     - **drop**: the resume, the raise of `f`, `TW.immEnd` at `p₂`, `free ℓ₂`, then `L₃`'s exit
       (`TW.mutUnfold` at `ℓ₃`), `free ℓ₃`, then `L₁`'s exit.

     `TW.immEnd` has no ordering premise, so each of these is a `TW` world. The `Tagged` and
     `FrameLife` facts after it are checked, not assumed.
  6. For `ReentryFreshA`, the second stop of the two-stop program, before step 5.

  The distinguishing input of the diagnostic need not arise. `ptoMutS` demands equality of
  predicates, so the diagnostic is about our relation's definition at an arising world.
- **Nested `withbor3`.** `alloc ℓ`, `mutFold` (outer, `α₀`), `mutUnfold` (anti), `mutFold`
  (relend, `α ⊏ α₀`), the yield, and the closings in context order.
- **6.150's younger-lend test.** `immFrame` (record); `reb` (`β`); the stop; a resumer's `mutFold`
  at `α₃ ⊏ β`; the resume; the borrower's return.
  - `TW.rebEnd`'s `W′.InStratum β`, and `RebExitW`'s, fail at that world.
  - Whether another history types the exit world is part of the reading.
- **Direction.** `TW` is the arising test. `TabAt`, `Holds`, `CompatW` and `ExtentOK` appear here
  as invariants, definitional conjuncts or rule premises. They are never guards on a refutation.
  An over-approximate guard proves soundly and refutes unsoundly (memory
  `arising-tests-are-directional`).

---

## 6. Report lists (CLAUDE.md §5)

- **Printed hypotheses the lifts must spend:**
  - **6.64/6.65's И freshness of `α`** (H4, via 6.112). It is spent at the entry only, taken below
    every lifetime of `W` (§4.2). That choice gives `withbor3`'s nesting (`relend_below_anti`) and,
    under (a), `α₂ ⊏ h`. The continuation forms fix `α`. Under (b) it is spent again at every
    resumption.
  - **6.65's H11** (`@ρ_b ⊐ α`). At `L₃`'s entry it is what puts `α₃` below `α₂` (checkpoint 2;
    the premises of `ReentryInheritA`, `ReentryFreshA` and `ResumeOutOfOrder`).
  - **6.65's `P̂ ⊨ [β]P̂`**: in the entry only.
  - **6.150's `RebEscrow` and its И freshness of `β`**: in the entry. Core's version is the chooser
    `RebChooseTW`, and here it is `RebChooseTWW`.
  - **6.150's local strata at the exit**: H15, H29 and 6.52's `@ρ_e, @ρ′ ⊐ β`. `RebExitW` keeps
    `TW.rebEnd`'s global `W″ ∈ Res_β` instead (reading 6).
  - **Core's added `hQ`** (`QExt`): at 6.64's exit.
- **Uniqueness and functionality results.**
  - Used:
    - `ResU.CompS.functional`, throughout and for the functional exits in `close_flat_agree`;
    - `ResU.SubKeep.functional`, at 6.150's exit and in `close_flat_agree`;
    - `CellU.mutOf_at` and the cell's injectivity, at the `mut` exit and in `holds_chain`.
  - Not used:
    - `head_det_eff` (`Core/Steps.lean:596`) and `AStep1.deterministic` (`Core/Demonic.lean:117`);
    - `ResU.Lower.functional` beyond the binds' use;
    - `TI`'s uniqueness of open frames at a location (`Core/Invariant.lean:1838`). `StopW`
      subtracts `immRecs τ` instead of asking for disjointness.

    None of these is expected to be needed: the probes reason about resources, not traces.
- **Printed lemmas in the run-up that are untranscribed:**
  - 6.40 (`ℓ ↦ own(v₁) # ρ ⟺ ℓ ↦ own(v₂) # ρ`) is `untranscribed` (`Paper/INDEX.md:63`).
    - None of 6.64–6.66's or 6.150's printed proofs cites it.
    - The 6.65 and 6.66 exits return `own(v″)` with `v″ ≠ v`. If closability there needs 6.40 rather
      than 6.24, that is the first thing to transcribe.
  - Every other lemma cited in §4 is `proved` in `Paper/INDEX.md` (6.52 `variant`; 6.58/6.59
    `proved*`).
  - `flat_mut_own_agree_off` is `[about ours]`: the two displays of 6.28's printed proof,
    compared. It is proved.
- **Hypotheses and conjuncts added to the draft:**
  - **`CompatW`**: the printed H1 of 6.29/6.38/6.39 and 6.64's H14, carried by the world (§1.3).
    - It is a real restriction at `imm` and `reb` entries only (F1). F0 makes it necessary at
      `imm` entries, at the resource level.
    - It is the closest thing here to `the-frame-narrowing-was-the-misstatement`. The difference:
      at `τ = []` the quantifier is verbatim (`wpGW_nil`), and where it restricts, the printed exit
      carries the same hypothesis.
    - That every resumer discharges it is `compat_at_stop` and `compat_resume`, plus FINDING-1;
  - **`Holds τ′ ρk` and `CompatW τ′ ρa ρk`** in the table: the exclusivity check at a stop;
  - **`StopW`'s freshness conjunct**, and **`YoungerThan`** in the main statements. The `…Out`
    statements drop `YoungerThan`;
  - **`AntiPin`**: our definition, to make `Close` coherent. `pin_harmless` shows it removes no
    split where `OblWf` holds. That `OblWf` holds at arising stops is reading 7;
  - **`RebExitW`'s `Keeps`**, in place of T1's list equalities in Core's chooser;
  - **`ExtentOK`**, under OQ-3 (a) only: (a)'s rule obligation at a handler entry;
  - **`ClosedOps`** (R-CLOSEDOP), as D-TABLEOK (3)–(4). It is scoped as the unrestricted conjunct
    is: no result covers an operation whose argument or answer holds a borrow cell;
  - **`OpenInv`/`OpenInvReb`**: derived (§1.7);
  - **the unrestricted-continuation conjunct**: an assumption owned by batch 3, used by no
    conclusion (§1.6).

---

## 7. Readings to be checked (not claims)

None of these is derived. Each names the statement that checks it. I have not verified that any
obstruction is real.

1. **The σ-component of `#` restricts frames only at `imm` and `reb` entries.** `imm` cells
   duplicate (6.43), while `mut` cells and an `anti` entry's unfolded content are exclusive (6.24,
   6.41, 6.42). It is not true that a 6.65 entry needs no check at a stop:
   - inside a 6.66 body the cell is `own`, and `ClosedOps` lets an argument carry it;
   - so `Holds τ′ ρk` is needed at every stop that hands an `anti` entry on;
   - for a `mut` entry, `Holds` keeps its cell in the share rather than in the leftover.

   Checked by F0, F1 and `holds_exclusive`.
2. **`TabAt` (6.50) takes the place of the box at a hand-on stop.** Every hand-on step is a printed
   lemma at a chosen split:
   - 6.29, 6.38 with view ↦ `ρ⁺`, and 6.39, for `imm`;
   - 6.27 and 6.28 for `mut`;
   - 6.28 for `anti`;
   - 6.52 and 6.59 with `ρ′ := ∅`, `ρ⁺ :=` the stop's resource, for `reb`.

   Checked inside the `OpenFrame*` proofs.
3. **The relativised `↭` records every open entry, with no lifetime premise.** OQ-44's
   `MutLendRecorded` follows with no `TW` constructor. Checked by F2, at the absorbed-view
   configuration.
4. **Under `YoungerThan`, closing `τi` never removes a record the entry's cell freezes.** It never
   removes one its payload reads either. Without `YoungerThan`, our frozen list is LIFO by
   lifetime: `ptoMutS`'s `ofS Q = P ls₀`, and `Ext`'s second conjunct. Checked by
   `OpenFrame65OutStable` against `OpenFrame65Out`, on the resume, cancel and drop paths, and by
   the diagnostic `MutViewSurvivesOlderClose`.
5. **OQ-3: the draft cannot tell (a) from (b); (a)'s own rule rejects part of the configuration;
   D-ORD rejects it under both.**
   - (a)'s rule obligation fails at `κ`'s call inside `L₃`:
     - with an inherited extent, at once (`ReentryInheritA`);
     - with a fresh extent, at the second stop (`ReentryFreshA`).
   - The draft relation does not enforce that obligation (`extentObligation_bypassed`), because
     `σ` is read lifetime-blind.
   - At a stop, the extent's check rejects nothing `CompatW` admits (`ArgBelowExtent`,
     `ArgAboveExtent`).
   - Under D-ORD, (b) also places `e₂` inside `e₃` out of order (`ResumeOutOfOrder`).

   So whether a handler between two lenders may resume, cancel or drop `κ` inside a younger lend is
   decided by OQ-8's D-ORD and OQ-3 together. This draft does not decide it. Checked by the
   statements named.
6. **`TW.rebEnd`'s `W′ ∈ Res_β` and Core's H11 variant are LIFO-shaped.** Core's variant takes
   `β` below the world. `RebExitW` keeps that premise.
   - Under (a), a resumer's younger lend around the resume may block 6.150's exit typing.
   - Both are ours, `[about ours]`.
   - Checked at `OpenRecord150`'s younger-lend test (§3.3).
7. **`Close` is coherent under the pin, and the pin is harmless at arising stops.** Two closures of
   one resource are `↭`-related (`close_upd_coherent`). `OblWf` holds of every obligation a stop
   hands on in an arising configuration under `ClosedOps`. Checked by F-CLOSE and at every
   instance's stop.
8. **(a) introduces a value/stop split inside the frame proof that (b) does not** (§4.1). This is
   a cost in fidelity to the printed technique, to be weighed against (b)'s re-lendable relation.

---

## 8. Findings for the user

**FINDING-1: under (a), the relation at `W` has to carry the σ-component of `#`.**

This is not an obstruction to (a). It names where (a)'s cost lands. It follows from the
definitions above:
- the continuation's `ewpW` is quantified over frames that meet `CompatW` for the entries it holds;
- every resumer must therefore call `κ` at such a frame;
- that frame is the stop's pieces and the resumer's own resources (`compat_resume`).

F0 is its Lean: at an arising world, a frame holding a copy of the view passes the verbatim frame
premise, and no resource owning the lent place is compatible with it. So the printed exit cannot
be completed there, and `TW` cannot exclude that frame.

| resumer | how `CompatW` is discharged |
|---|---|
| given by code | resources: `compat_at_stop` for the stop's pieces; `compat_resume` with `closed_compatW`, fresh places and a direct argument for its own lends (the between-lenders clause) |
| a clause read only through a relation (a generic clause, T-FP at `W`) | a property of the relation at `W`: the values a clause holds besides `κ` are compatible with the closure of `κ`'s entries. The same clause gets `κ`'s linearity from typing (§1.6), not from this relation. |

The second row is a constraint on D-REL at `W`, which this experiment does not define (§1.10).
It is beyond the one draft relation. It is recorded here and not patched.

**The checkable part** is `closed_compatW`: closed data is compatible, and the kernel types
`[handle]`'s clauses at `!` over closed operation types. What remains for the relation:
- values of open type a clause builds from its own lends;
- the absence of any route by which a clause obtains a copy of a view out of `κ`'s share.

A clause's proof can split an `imm` copy off `κ`'s share (6.43). A frame holding that copy fails
`CompatW`, so a proof that takes the split cannot call `κ`. For a clause given by code, the prover
does not take it. For a clause read through a relation, the relation must not produce it.

**The comparison with (b).** Under (b) the relation carries re-lendability instead
(`RelendableS`, the `vRL*` line). Both options put a cost into the relation at `W`, and they are
different costs.

**FINDING-2: telling OQ-3 (a) from (b) needs a relation that reads `σ`'s lifetimes.**

This follows from the definitions above. Its Lean is `extentObligation_bypassed`,
`ReentryInheritA`, `ReentryFreshA` and `ResumeOutOfOrder`, all to be proved (§3.4).
- **Why the draft cannot.** `wpGW` reads `σ` only through the 6.64 selection, and `ewpW` is
  `σ`-monotone (§1.4). So any condition on the stack at which `κ` is called is undone by calling
  `κ` at the handler's own stack and extending.
- **What survives.**
  - (a)'s nesting obligation survives only as a premise of (a)'s own rule.
  - Against an enclosing 6.64 frame it can also be read through the list, since the frame leaves
    a tagged record.
  - Against an enclosing 6.65 lend it cannot: a 6.65 lend leaves no record (OQ-44's point (1)).
- **The question needs a mechanism beyond the one draft relation.** It needs D-ORD on the stack the
  resumed term sits under (OQ-8), or a relation that reads `σ`'s lifetimes (D-REL's `TabAt` at
  `W`). With D-ORD, (b) rejects the configuration as well (`ResumeOutOfOrder`).
- **The user's choice, if the statements are proved.** It is between:
  - (a) or (b) together with D-ORD, which both reject resuming `κ` inside a younger lend;
  - leaving `σ` unordered, which admits it under (b) if `HandlerBetweenLendersB` and its cancel
    and drop forms hold;
  - a re-lend at the resume, which is OQ-9 (b).

**FINDING-3 (for batch 3): OQ-57's settling statement needs a second fixed point.**

OQ-57's box settles by `ClosingInW` (05 §4). It compares `ewpW` with `ewpC`, "D-EWP with no `τ`
index, reading the obligation off the entries' `closer` field".
- **If `ewpC` is defined independently**, it is a second fixed point beside `ewpW`. A probe limited
  to one draft relation cannot define it.
- **If it is defined as `ewpW` at a decoded index**, `ClosingInW` is decode ∘ encode and tests
  nothing.

So OQ-57 is not settled by this unit; the plan batches it in step 2.3 anyway. What this design
learned, for that batch:
- **A marker statement at the handler's `[op]` step measures nothing.** The frame lemmas push `τ′`
  directly above the handler's marker, so there the obligation is the marker reading by
  construction.
- **An extent reading has to be bound to a configuration.** It is stated at a configuration's own
  stop, with `h` the handler lemma's choice and the stack as the proof builds it, not over
  hand-written stacks. The two-stop between-lenders program's second stop is such a stop.
- **At frame-lemma level, the full stack does not determine the obligation.** `OpenFrame64`'s
  premise and conclusion index one stop by one full stack (`[] ++ e :: σ` and `[e] ++ σ`) with
  different obligations. So no reading of the full stack alone recovers `τ` there, whether by
  markers or by extents. A `closer` field distinguishes the two only by recording which view a
  statement takes. That is the index, carried in `σ`.
- **What remains is a specification question.** Whether a per-entry `closer` field counts as "`W`
  carries it" for 00 §0.2 item 1 is a question for the specification, not for a probe.

Readings 4 and 6 (§7) would become findings of FINDING-1's kind if their checking statements stop
where they name. In that case the fix lies in Core's `[about ours]` definitions (`Ext`, `ptoMutS`,
`TW.rebEnd`), outside this draft. Until then they are readings.

---

## 9. Stages, layout and order

```
experiments/WorldW/
  DESIGN.md
  WorldW.lean                 root: imports the modules below
  WorldW/Defs.lean            §1
  WorldW/Nil.lean             §1.9: wpGW_nil, ewpTS_ewpW
  WorldW/Checks.lean          §2
  WorldW/Wp.lean              §4.2
  WorldW/Frame64.lean         OpenFrame64 and its lemmas; the 6.64 entry
  WorldW/Frame65.lean         OpenFrame65, OpenFrame65OutStable, OpenFrame65Out; the 6.65 entry
  WorldW/Between.lean         ewp_handle_W, ClauseBetween(Cancel), HandlerBetweenLendersB(…),
                              the (a) arm, the argument variant
  WorldW/Diag.lean            MutViewSurvivesOlderClose (a diagnostic; draws no conclusion alone)
  WorldW/Record150.lean       RebExitW, RebChooseTWW and its dischargers, OpenRecord150; the 6.150 entry
  WorldW/Frame66.lean         OpenFrame66; the 6.66 entry; close_relend_anti's use
  WorldW/Instances/*.lean     §3.5, one file per stage
```

The lakefile entry, added with the first Lean file:

```toml
[[lean_lib]]
name = "WorldW"
srcDir = "experiments/WorldW"
roots = ["WorldW"]
```

It imports `Core` and `GhostEnd` (for `TabAt`, `tabAt_updV`, `ownerI`, `owner`, `viewP`,
`wpG_box`). Build with `lake build WorldW`, or one module at a time.

**Stages, riskiest first.** Each stage ends with its deliverable proved, refuted with every
hypothesis discharged, or reported unfinished at a named step. The next stage starts only from
that outcome.

| stage | deliverable | exit rule |
|---|---|---|
| A. Definitions and checks | `Defs`, `Nil`, and `Checks`. F-CLOSE comes first: `closeE_anti_flat`, `close_flat_agree`, `close_upd_coherent`, `upd_choice_free`, `pin_harmless`, `UnpinnedIncoherent`. Then F0, F1, F2, `holds_injective`, `holds_chain` with their instances, `close_relend_anti`, `close_frame`, `closed_compatW`, `compat_at_stop`, `compat_resume`, `younger_preserved`, `dropKappa_by_surgery`. | no later stage starts until `close_upd_coherent` is proved. If `close_flat_agree` fails, the pin is extended at the failing pair, or (37) is restated in option (i)'s form, before anything else. If F0 resists proof, re-examine its configuration (§2). |
| B. 6.64 at a mixed row | `Wp` with the entry lemmas' freshness conjunct, the 6.64 entry, `OpenFrame64` with its four lemmas, and instances: resume; resume then cancel; resume then drop; `τi ≠ []` | the failing path and printed lemma, if any |
| C1. 6.65 | `OpenFrame65`, `OpenFrame65OutStable` and `OpenFrame65Out`, each with its resume, cancel, drop and value lemmas; `relend_below_anti`; instances | as B. A stop of `…Out` alone at the frozen list is reading 4, not a failure of (a) |
| D. Between lenders | `ewp_handle_W`, `ClauseBetween`, `ClauseBetweenCancel`, `HandlerBetweenLendersB`, `…Cancel` and `…Drop` at both payload types; the (a) arm: `ExtentOK`, `ewp_handle_W_ext`, `ReentryInheritA`, `ReentryFreshA`, `extentObligation_bypassed`, `ResumeOutOfOrder`; `ArgBelowExtent`, `ArgAboveExtent`; the diagnostic; instances | §3.4's reporting rule |
| E. 6.150 | `RebExitW`, `RebChooseTWW`, `rebChooseTW_top_W`, `rebChooseTW_deep_W`, `rebChooseTW_pin_W`, `keeps_of_ext`, `keeps_of_stopW`, `OpenRecord150`, instances, and the younger-lend test | a stop at `RebExitW`'s stratum premise is reading 6 |
| C2. 6.66 | `OpenFrame66`, the nested `withbor3` instance, comparison with `nested_spans_yield` | a failure at `Holds` is reported as a route around borrowing, not patched |

**Why this order.**
- D comes right after the single-lender frames it rests on: 6.64 for `L₁` and `L₂`, 6.65 for `L₃`.
  Between lenders is the riskiest question after them.
- E comes before C2 because the question names a 6.150 record, while 6.66 enters only through
  `withbor3`.
- C2 and E reuse the step lemmas of B and C1, and none of D's configuration. The anti step's
  definition is stage A's.

An unproved step during the work is an enumerated `sorry`. None remains in a delivered
statement's proof. A probe that does not close is reported as unfinished, with the step that would
not follow and the printed lemma it names.
