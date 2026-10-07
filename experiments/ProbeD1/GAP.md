# ProbeD1: the instantiation's gap at `∀` — `TyEqInst` at every type, and the position-`∀`

This is the design for the gap `BINDER.md` §11.2 left: `TyEqInst` is proved only at `CoreStable`
types, because "the induction stops at the `∀` clause where lifetimes fall in the instantiation's
gap". It follows the direction given with the task (quantify over positions of the finite order of
lifetimes in play, not over all of ℕ) and reports what that direction meets when it is made exact.

The statements are in `ProbeD1/Gap.lean`: definitions and `def … : Prop` only, no proofs. The one
thing proved now is the justification §3c asks for, Core's `∀` reading the room between
lifetimes, in `ProbeD1/GapWitness.lean`. `lake build ProbeD1` builds both. There is no `sorry`,
`axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`, and the witness's
theorems have `#print axioms` within `[propext, Classical.choice, Quot.sound]`. Nothing in `Core/`,
`Paper/` or any printed definition changes.

**Status words**, as in `BINDER.md`: *proved* is a theorem; *refuted* a theorem proving the
negation; *not derived* means neither, with no obstruction verified; *not attempted* means no
proof was tried; *[unchecked]* marks a claim argued in prose and not in Lean. Reading tags:
*[read]* (I read the source), *[relayed]* (from a secondary source or standard knowledge, not
re-read here), *[unverified]*.

---

## 0. On one page

- **Where it stops** (§1.1). `tyEq_inst` (`BinderRows.lean:485`) recurses on the type and rules
  out `U` (`:514`, `hc.elim`). At a thunk `TyEq` is `CTyEq` (`Core/FrameRecords.lean:203`), whose
  `∀` clause (`:219`) asks every `α : Life`. At a fixed instantiation `ι` the hypothesis reaches
  only `α' = ι.life1 α`, through `Inst.sub_extend` (`BinderInst.lean:209`), and
  `Restrat.Emb.shift c k` leaves `k` lifetimes below `c` with no preimage. `TyEqGapStep` names the
  missing step.
- **Two different objects read the gap** (§1.2). `TyEq` is a conjunction of equalities
  `@aδ = @a′δ′` under an unbounded `∀`. The relation's `∀` (`Core/Relation.lean:161`, and `cRLJ`'s)
  is bounded strictly (`LtLife`) and its body compares the bound variable non-strictly with a cell
  (`ptoMutS`'s `α ⊑ b`, `:46`; `ptoImmS`'s `α ⊑ s.meet`, `:53`).
- **The relation reads the room. Proved** (§3c, `GapWitness.lean`). At `∀'0 ⊏ ⊤. F (Mut '0 1)`
  and `Λ. return ℓ₀`, Core's clause holds at a `mut` cell at `1`, adjacent to `⊤`, and fails at
  every `mut` cell at `2` with an empty witness (`adj_fails`, `coreAllAdjacent`). The image of the
  first under `shift ⊤ 1` is one of them (`coreAllNotNatural`). The correction given with the task
  is right about the relation: invariance under an embedding that opens a gap is false for it, not
  merely unproved.
- **`TyEq` does not read the room** [unchecked] (§2). An equality on a chain is decided threshold
  by threshold, and a lifetime term commutes with the two-point collapse at a threshold. So `TyEq`
  holds at every pair whose threshold patterns are those of `TyEq` pairs. At `∀` the source
  lifetime is chosen per threshold, `⊤` or one below it, which always exists. The factorisation
  the task rules out asks one source lifetime for all thresholds at once, and that is what
  adjacency blocks. This gives `TyEqInst` at every type, and `TyEqRoomBlind`: invariance under
  every order embedding fixing `⊤`. No relation changes.
- **What that unlocks** (§2.3, §4). The `CoreStable` restriction on `Mut` and `Imm` payloads goes:
  `CohEInstOB`, `ViewSlotInstOB`, `RelendJValueK`, `Statement0UThawFreeKJ`. The partial result
  widens from `CtxThawFree` to `CtxThawFreeK`, where only `μ` and `fam` slots are excluded (R1).
- **The thaw never asks the relation's `∀` to be invariant** (§1.3). Computation types occur in
  value types only under `U`. W's `U` clause quantifies over every instantiation itself
  (`RelendJ`), and every cut below the stack's cut is opened by one (`InstRealisesCut`). So the
  `∀` inside a `U` value is already read at every position an admissible embedding can open. For
  everything under `U`, **W's `U` clause is the position-`∀`** (§3.4).
- **The position-`∀`, made exact, has two readings** (§3.2).
  - (A) `CutAllC` reads every cut of the whole order in play, realised by renaming the
    configuration. It needs retained cells renamed, the transport Restrat refutes at a `Mut` cell
    (`mut_not_natural`). It makes agreement with Core at `σ = []` one-way: `not_coreAllImpCutAll`
    is proved. That puts OQ-58 into outcome (c) at the types whose `∀` body compares the bound
    variable with a cell, and the remedy there would redefine Core's printed `∀`.
  - (B) `AllPosJ` reads every cut below the stack's cut, realised by an instantiation (W's own
    re-lend). It is invariant under admissible embeddings by transport (`AllPosJTransport`), and
    it is Core's clause at `σ = []` in both directions (`AllPosJNil`).
- **Recommendation** (§3.4): keep `cRLJ`'s `∀` as it is. No statement carries a computation across
  an instantiation outside `U`. Putting (B) at `cRLJ`'s `∀` would make `∀I` owe the context's thaw,
  and with it R1. `AllPosJ` is stated for the day a statement needs it.
- **R1 is where the relation's `∀` bites** (§4). Core reads a `μ` slot's thunks with Core's `U`
  and ℕ-`∀`, so the thaw meets §3c's mechanism there (`NotMuSlotThawCore`; stated, not attempted).
  The route stays `BINDER.md` §5.4's: W reads `μ` and `fam` itself, so a thunk inside is W's `U`,
  which reads every internal position by construction.
- **Core's `∀` is printed** (§3.5): [TR] p. 4 row 4.5 and [CONF] p. 415:12, over `Life ≜ ℕ`
  ([TR] p. 4, [CONF] Fig. 11). A dense carrier would also break the well-founded stratification
  that defines `Cell` (§5). It is recorded, not taken.

---

## 1. Diagnosis

### 1.1 Where the induction stops

`TyEqInst` (`Binder.lean:723`) is the statement at every type:

```lean
def TyEqInst : Prop :=
  ∀ (A B : VTy) (s s' : LSub) (ι : Inst), TyEq A s B s' → TyEq A (ι.sub s) B (ι.sub s')
```

`tyEq_inst` (`BinderRows.lean:485`) proves it under `CoreStable A` by structural recursion on `A`.
Its `.thunk _` arm is `hc.elim` (`:514`). Without the restriction the arm reduces, for
`B = .thunk C'`, to `CTyEq C s C' s' → CTyEq C (ι.sub s) C' (ι.sub s')`. `CTyEq`'s `∀` clause is
`Core/FrameRecords.lean:219–220`:

```lean
  | .all x b C, δ, .all x' b' C', δ' =>
      b.interp δ = b'.interp δ' ∧ ∀ α : Life, CTyEq C (δ.extend x α) C' (δ'.extend x' α)
```

- The first conjunct goes through `Inst.interp_sub` (`BinderInst.lean:227`).
- The second needs `CTyEq C ((ι.sub s).extend x α') C' ((ι.sub s').extend x' α')` at every `α'`.
  The induction hypothesis at `ι` gives it at `ι.sub (s.extend x α)`, which is
  `(ι.sub s).extend x (ι.life1 α)` by `Inst.sub_extend` (`BinderInst.lean:209`). So it covers
  `α' ∈ Set.range ι.life1` only.
- For `ι = Inst.ofEmb (Restrat.Emb.shift c k)` the range misses the `k` lifetimes just below `c`
  (`Restrat.Emb.shift_apply_lt`). At `c = ⊤`, `k = 1` the missing lifetime is `1`
  (`Restrat.MutCounterexample.gap`).
- `BINDER.md` §3.6 anticipated the way out: "It needs that a comparison of `interp` values is one
  of lattice polynomials in the bound variables, fixed by its values on `ℕ` [unchecked]". §2 makes
  that exact.

`Gap.lean` names the step:

```lean
def InGap (ι : Inst) (a : Life) : Prop := ∀ b, ι.life1 b ≠ a

def TyEqGapStep : Prop :=
  ∀ (C C' : CTy) (x x' : LifeVar) (s s' : LSub) (ι : Inst),
    (∀ α : Life, CTyEq C ((ι.sub s).extend x (ι.life1 α)) C' ((ι.sub s').extend x' (ι.life1 α))) →
    ∀ α' : Life, CTyEq C ((ι.sub s).extend x α') C' ((ι.sub s').extend x' α')
```

With `TyEqGapStep`, `tyEq_inst`'s recursion extends to `U` (the mutual `CTyEq` arm closes at `∀`),
`μ` and `fam` (whose `TyEq` clauses are structural). Every lemma that reads `CoreStable` through
`tyEq_inst` then loses it:
- `cohE_inst` (`BinderRows.lean:554`) reads `hT` only at `tyEq_inst`;
- `vC_mut_bound` (`:660`) and `vC_imm_bound` (`:690`) read it at `tyEq_inst`, and `vC_imm_bound`
  also at `vC_true_eq_false` (`:519`), which `vO_obs` (`Core/RelationFacts.lean:330`) replaces;
- `vC_imm_retained` (`:639`), through `cohE_inst`;
- `viewSlotInstCS` (`BinderRisk.lean:266`), `relendJ_mut` (`:760`) and `relendJ_imm` (`:816`);
- through them `ThawFree`'s last clause (`Binder.lean:751`) and `CtxThawFree`.

### 1.2 Two objects read the gap

**`TyEq`** (`Core/FrameRecords.lean:195–227`, `[about ours]`). Its clauses are:
- syntactic equalities (`w = w'`, `k = k'`, `n = n'`);
- equalities of lifetime terms, `a.interp δ = a'.interp δ'`, at `box`, `imm`, `mut` and the
  bound of `∀`;
- conjunctions;
- one unbounded `∀ α : Life`.

Unfolded along a type, `CTyEq C δ C' δ'` is a universally quantified conjunction of equalities
between lattice terms (`Life ::= 'a ∣ ⊤ ∣ ⊔ ∣ ⊓`, [TR] p. 1; `interp` gives `⊔ = min`,
`⊓ = max` on ℕ, `Paper/S2_Statics/Definitions.lean`).

**The relation's `∀`.** Core's clause (`Core/Relation.lean:161–162`):

```lean
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cC C ls (δ.extend x α) (.app e (.val .unit))) ρ
```

- The bound is strict: `LtLife δ c α` is `α ⊏ @cδ`.
- The body's lifetime atoms include non-strict comparisons with the cells of the resource:
  `ptoMutS`'s `α ⊑ b` (`:46`) and `ptoImmS`'s `α ⊑ s.meet` (`:53`).
- `cRLJ`'s `∀` clause (`BinderJ.lean:117`) has the same shape at the stack's reading.

A strict bound with a non-strict body reads adjacency. `∀α ⊏ c. α ⊑ b` holds exactly when no
lifetime lies strictly between `b` and `c`. On ℕ that is true when `b = ↓c`, the lifetime just
below `c`, and an embedding that pulls the two apart makes it false. §3c proves this at Core's
clause.

`TyEq` has no atom of that kind. An equation between lattice terms over a chain is decided by its
two-valued patterns: `u = u'` iff for every threshold `t`, `u` and `u'` are on the same side of
`t`. The pattern of a lifetime strictly between two adjacent ones is, at each threshold, the
pattern of one of them. So `TyEq` cannot tell whether the room exists (§2).

### 1.3 Which one the thaw reads

The thaw (`relendJ_value`, `BinderRows.lean:983`) is an induction on **value** types:
- at `U` it is by construction: `RelendJ`'s quantifier over instantiations composes
  (`relendJ_thunk`, `:956`; `instComp`);
- at `⊗`, `⊕`, `!` and `Ref` it is structural, and at a box it reads the bound;
- at `Mut` and `Imm` leaves it reads `TyEq` at a bound place (the view is handed back and read up to
  `TyEq`) and `PayExt` at a retained one;
- data leaves hold nothing.

Computation types occur in value types only under `U` (`Core/Types.lean:45–75`: `thunk` is the
only `VTy` former with a `CTy` argument). So the relation's `∀` is never reached by the thaw's
induction: it sits under `U`, which is by construction. The `∀` is reached only through `TyEq`,
which recurses through `U` structurally.

At **computation** types no instantiation lemma is available, and none is needed:
- `F`'s clause is `wpTS`, whose naturality Restrat leaves open (`Restrat.Open.WpNatural`);
- `⊸` reads its argument contravariantly.

So an "invariance by induction on types, `∀` by transport" meets its `∀` step only at computation
types, where it is blocked earlier, at `F` and `⊸`. W never carries a computation across an
instantiation except inside `U` (and inside the share, statement 2's, which quantifies over
re-lends by construction too).

### 1.4 What follows

- The gap as stated (`TyEqInst`) closes without changing any relation, by an argument about `TyEq`
  alone (§2).
- The direction given with the task is the right notion for the **relation** (§3). Made exact, its
  realisable reading (B) is the quantifier W's `U` clause already has, so at value types W reads
  every internal position by construction.
- Where the relation's ℕ-`∀` still matters is R1, through Core's relation at `μ` and `fam` (§4).

---

## 2. `TyEq` reads no room: `TyEqInst` at every type

### 2.1 The argument [unchecked]

Lifetimes are carried as naturals (`LSub` stores `ℕ`): `⊤ = 0`, larger is shorter, `⊔ = min`,
`⊓ = max`.

1. **The collapse.** `collapseN t n = if n ≤ t then 0 else 1`. It is monotone on ℕ and fixes `0`.
   So it commutes with `min`, `max` and `⊤`, and with `find?`
   (`Restrat.LSub.find?_mapN`): `a.interp (mapN (collapseN t) δ) = (a.interp δ).map (collapseN t)`
   (`InterpCollapse`).
2. **Equality by thresholds.** For `o o' : Option ℕ`, if every collapse equates them then
   `o = o'` (`EqOfCollapse`). If both are `some` and `m < n`, the collapse at `m` sends `m` to `0`
   and `n` to `1`; `none` against `some` differs at every collapse.
3. **Covers.** A family `S` of reading pairs covers `(s₂, s₂')` if for every threshold `t₂` some
   `(s₁, s₁') ∈ S` and some `t₁` collapse, variable by variable, as `(s₂, s₂')` does at `t₂`
   (`TyCover`). The member may change with `t₂`.
4. **The cover lemma** (`TyEqOfCover`). If every member of `S` is a `TyEq` pair and `S` covers
   `(s₂, s₂')`, then `(s₂, s₂')` is one. By induction on the type, mutually over `VTy` and `CTy`:
   - **An equation `@a s₂ = @a' s₂'`.** By step 2 it suffices that each collapse at `t₂` equates
     the two sides. By step 1 the left side is `@a (collapse t₂ ∘ s₂)`. By the cover and
     `interp_congr` that is `@a (collapse t₁ ∘ s₁)`, which is the collapse at `t₁` of `@a s₁`. The
     member's own equation and the same steps backwards give the right side.
   - **A syntactic atom** (`w = w'`, `n = n'`, `k = k'`) holds at any member; the cover at `t₂ = 0`
     gives one.
   - **A conjunction**: componentwise, with the same family.
   - **`∀`.** The bound's equation is an equation. For the body take
     `S' = {(s₁.extend x α, s₁'.extend x' α) ∣ (s₁, s₁') ∈ S, α : Life}`; its members are `CTyEq`
     pairs because `S`'s are. `S'` covers `(s₂.extend x β, s₂'.extend x' β)` for every `β`. At
     `t₂`, take `(s₁, s₁', t₁)` from `S`'s cover, and `α := ⊤` if `β ≤ t₂`, else `α := t₁ + 1`.
     Then `collapse t₁ α = collapse t₂ β`, and every other variable collapses as before.
5. **Instantiations are covers** (`CoverInst`). Let `θ` be strictly monotone with `θ 0 = 0` (every
   `Restrat.Emb c`; `θ n ≥ n`). At `t₂`, let `t₁` be the largest `n` with `θ n ≤ t₂`. It exists:
   `θ 0 = 0 ≤ t₂`, and `n ≤ θ n ≤ t₂` bounds it. Then `θ m ≤ t₂ ↔ m ≤ t₁`, so
   `collapse t₂ ∘ θ = collapse t₁`. With `S = {(s, s')}` this gives **`TyEqInst` at every type**.
   With `t₁ := θ t₂` the converse cover holds as well, which gives **`TyEqRoomBlind`**: `TyEq` is
   invariant, both ways, under every embedding fixing `⊤`.
6. **The gap step** (`CoverGap`). The image family `{((ι s).extend x (ι α), …) ∣ α}` covers
   `((ι s).extend x α', …)`. At `t₂` take `t₁ := t₂` and `α := ⊤` or `α := t₂ + 1`, since
   `ι(t₂ + 1) ≥ t₂ + 1`. With step 4 this is `TyEqGapStep`.

**Why the factorisation fails and the cover does not.** The factorisation asks for one source
lifetime that stands, relative to *every* lifetime in play at once, where the gap lifetime stands.
When the source points are adjacent there is none. The cover asks, per threshold, for a source
lifetime with the gap lifetime's **two-valued** pattern. Above a threshold `⊤` always works.
Below it, any lifetime shorter than the threshold works, and there are infinitely many: the same
fact [TR] 6.64 and 6.65 use at H4, "for any lifetime, the set of lifetimes shorter than it is
infinite" [read]. An equation is decided by its per-threshold patterns. A relation clause with a
strict bound and a non-strict body is not (§3c).

**A check outside Lean.** A brute-force search over random equality-only formulas with up to
three bound variables, readings in `{0, 1, 2}` and shifts that open gaps found no formula true at
the source and false at the image, in 22,637 cases true at the source. The same search
distinguishes the relation-shaped formula `∀α ⊏ ⊤. α ⊑ 1` at once. This is evidence, not a proof.

### 2.2 The Lean plan

All statements are in `Gap.lean` §2. In order:
1. `InterpCollapse`, by induction on `Lifetime.Life`, with `Monotone.map_min`/`map_max` at
   `collapseN t`.
2. `EqOfCollapse`, by cases.
3. `TyEqOfCover`, a `mutual` theorem over `VTy`/`CTy`, following `TyEq`'s and `CTyEq`'s clauses as
   `tyEq_trans` (`Core/ShapeMu.lean:562`) does. The `∀` arm generalises the family. Nothing else
   is generalised.
4. `CoverInst` and `CoverGap`: arithmetic on `Restrat.Emb.toNat` (`toNat_strictMono`,
   `toNat_zero`).
5. `TyEqInst` (Binder.lean's statement, at every type), `TyEqGapStep` and `TyEqRoomBlind` as
   corollaries.

No printed proof governs `TyEq`: it is ours (`[about ours]`), so there is no printed route to
follow. The technique built is the threshold cover. It is reusable for any predicate on readings
built from equalities of lifetime terms under an unbounded `∀`. It does not apply to `Δ.Models`
(strict), which is invariant anyway because it has no `∀` (`Restrat.Emb.models_mapN_iff`).

### 2.3 What it unlocks

Each step below is the existing proof with `tyEq_inst ι T hT` replaced by `TyEqInst`, and
`vC_true_eq_false` replaced by `vO_obs` with `vC_tyEq`:

- **`CohEInstOB`**: `cohE_inst` at every type, `OuterBelowTop` kept (`not_cohEInst` refutes the case
  at `⊤`).
- **`ViewSlotInstOB`**: `ViewSlotInstCS` at every slot type. At `Mut` the handed view stores
  `𝒱⟦e.T⟧` at the instantiated reading, `TyEq`-equal to the slot's payload there (`vC_tyEq`), and
  its support transfers the same way. At `Imm` the handed view's full payload gives the slot's
  observable one (`vO_obs`), and the coherence record moves (`CohEInstOB`). The dropped cell's
  stored invariant is never read, so `mut_not_natural` is not met.
- **`relendJ_mut`, `relendJ_imm` at every payload type.** The retained branches already read only
  `PayExt` (`vC_mut_retained` has no `CoreStable`; `vC_imm_retained` reads it only through
  `cohE_inst`).
- **`ThawFreeK`** (`Gap.lean`). It is `ThawFree` with the last clause `A => CoreStable A` replaced
  by `_ => True`, so `Mut` and `Imm` are admitted at every payload, `μ`, `fam` and thunks inside
  payloads included. `μ` and `fam` *slots* stay excluded.
- **`RelendJValueK`, `CtxRelendsThawFreeKJ`, `Statement0UThawFreeKJ .binder0`**: the thaw, the four
  `U` rows and `ThawInstJ` at `CtxThawFreeK` contexts.

---

## 3. The position-`∀` at W

### 3.1 Lifetimes in play, positions, admissible embeddings

- **In play** at an index `(δ, σ, αs, ls)` and a resource `ρ`:
  - the reading's values, the lends, and the records' frame lifetimes and readings (`IdxReads`,
    `Binder.lean`);
  - the cells' lifetimes at every depth.

  A finite set, since a resource is finite at every depth (`Paper/S5_Model`, G1).
- **Positions.** Relative to a finite chain `L` of `n` lifetimes there are `n` points and `n + 1`
  cuts. Over `(ℚ, <)` these are exactly the `2n + 1` orbits of `ℚ^(<n) × ℚ` (BKL Ex. 10.12 [read]).
  `SamePos L f α α'` says `α` stands among `L` as `α'` stands among `f(L)`.
- **Realisability in ℕᵒᵈ.**
  - The cut below everything is always realisable (H4).
  - The cut above everything is realisable iff `⊤ ∉ L`.
  - A cut between consecutive `a ⊏ b` is realisable iff `ofDual a ≥ ofDual b + 2`.
- **Admissible embeddings** are the instantiations `InstAt αs ι` (`Binder.lean:345`): the identity,
  or a `Restrat.Emb c` at the stack's cut `c = cutOf αs`.
  - They fix every lifetime at or above `c` (external) and move the internal ones down, strictly
    monotonically.
  - They act on positions bijectively, as the cut-map `(lo, hi) ↦ (θ lo, θ hi)`.
  - They can make an unrealisable cut below `c` realisable. They never change a cut above `c`.

### 3.2 Two readings

**(A) Every cut of the whole order, by renaming the configuration** (`CutAllC`, `Gap.lean`):

```lean
def CutAllC (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) : WProp := fun ρ =>
  ∀ φ : Restrat.Emb (⊤ : Life),
    cC C (ls.map (Targets.srecRestrat φ)) (Restrat.LSub.mapN φ.toNat δ) e (φ.relRU ρ)
```

At `C = ∀'x ⊏ c. C'` it reads `C'` at every position of the order in play, external lifetimes
included: every cut is opened by some `φ`. The realisation renames the resource. `relRU` moves
every cell, and moves a `mut` cell's stored predicate to its image (`Restrat.Emb.relU_mutOf`,
`relP`). At a `Mut` leaf that is the transport `Restrat.MutCounterexample.mut_not_natural` refutes:
the image of `𝒱⟦Imm 'b 1⟧_δ` is not `𝒱⟦Imm 'b 1⟧` at the moved reading, which also holds at a cell
in the gap. So under (A) a `∀I` row must carry its context to a renamed configuration, and a `Mut`
slot there is that witness. [unchecked: `NotVCNaturalCore`, the Core form, is stated in
`Binder.lean` and not proved.] W has no operation that renames a retained cell; its re-lend fixes
everything at or above the cut and hands the views back.

**(B) Every cut below the stack's cut, by instantiation** (`AllPosJ`, `Gap.lean`):

```lean
def AllPosJ (δ : LSub) (σ : LStack) (c : Lifetime.Life)
    (P : LSub → List Life → List SRec → Life → WProp) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ => ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → RecsOutside (ι.life αs) (ι.recs ls) →
      (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) (ι.recs ls) ─⋆
        fun ρ' => ∀ α, (⌜LtLife (extS (ι.sub δ) σ (ι.life αs)) c α⌝ ─⋆
          P (ι.sub δ) (ι.life αs) (ι.recs ls) α) ρ') ρz
```

- **The split** is `RelendJ`'s: the views at the stack's places, and a retained part strictly above
  the outermost lend, which every instantiation fixes. Under the guard (`TabAtS`, `PlaceViewsL`)
  every resource splits this way.
- **The realisation** is an instantiation `ι` with the views handed back at the instantiated stack.
  That is the configuration W's re-lend reaches (`GuardInst` gives the table and views there), a
  world extension. Nothing is asked of the source beyond what it is: no source-side stretch.
- **The bound is a cut constraint.** It is read at the instantiated reading,
  `@c(ι δ) = ι(@cδ)` (`Inst.interp_sub`), so "below the bound" moves with the bound's position
  (`Inst.ltLife_sub_iff` at image points).
- **The records** are moved exactly (`ι.recs ls`), with no extension, so that at `σ = []` the
  clause is Core's (§3b).
- **At `binder0`**, `cRLJ`'s first `∀` conjunct would become
  `AllPosJ δ σ c (fun δ' αs' ls' α => guardPV (extS (δ'.extend x α) σ αs') σ αs' ls'
  (cRL… σ (δ'.extend x α) C αs' ls' (.app e (.val .unit)))) αs ls ρ`, with the own-lend conjunct
  unchanged.

### 3.3 Invariance under admissible embeddings: `∀` by transport

The auxiliary lemmas (statements in `Gap.lean` §3):

- **`InstRealisesCut`**: a fresh lifetime realises a cut below the stack's cut. Let `lo < hi ≤ c` be
  consecutive in `L`. Take `θ := (Restrat.Emb.shift hi 1)` lifted to `Emb c` (`embLift`, since
  `hi ≤ c`), and `α := ↓hi`, the lifetime just below `hi`. Every `a ≤ lo` moves to
  `ofDual a + 1 ≥ ofDual hi + 2 > ofDual α`. Every `a ≥ hi` is fixed, with
  `ofDual a ≤ ofDual hi < ofDual α`. So `α` stands at the cut `(θ lo, θ hi)` among `θ(L)`. A cut
  above `c` is opened by no instantiation.
- **Embeddings act on cuts**: `θ` strictly monotone sends the cut `(lo, hi)` of `L` to the cut
  `(θ lo, θ hi)` of `θ(L)`, and points to points (`SamePos L θ`). The cut-map is a bijection
  between the positions of `L` and those of `θ(L)`.
- **`AllPosJTransport`**: `AllPosJ` at an index gives `AllPosJ` at every instantiation of it, the
  views handed back. A cut of the instantiated index is the image of a cut of the index, and its
  realisation there, an instantiation `ι₁` of `ι₀`'s stack, is a realisation at the composite
  `ι₁ ∘ ι₀` (`instComp`: `ι.sub δ = ι₁.sub (ι₀.sub δ)`, `ι.life1 = ι₁.life1 ∘ ι₀.life1`,
  `ι.recs = ι₁.recs ∘ ι₀.recs`). The retained part `ρz` lies above `ι₀`'s outermost lend because it
  lies above the original one and `ι₀` lowers it. This is the "`∀` by transport" step, and it
  holds for every body `P`.
- **`AllPosJSelf`**: at the identity instantiation, with the views handed back as they were,
  `AllPosJ` gives the ℕ-`∀` at the stack itself. The `∀E` row reads this.

At value types the invariance is the thaw (`RelendJValueK`), §2.3. At computation types it is
available only at `∀`, by transport, and only if (B) is adopted. `F` and `⊸` stay as §1.3 says.

### 3.4 W's `U` clause is reading (B); whether to put (B) at `cRLJ`'s `∀`

**W's `U` clause already reads every internal position.** `RelendJ` (`BinderJ.lean:53`) asks a `U`
value's body at every instantiation of the stack, with the views handed back. At
`C = ∀'x ⊏ c. C'` the body's ℕ-`∀` is then read at every instantiated reading. Together that is
`AllPosJ`'s "∀ ι, ∀ α", with `RelendJ`'s extension of the records added. By `InstRealisesCut`
every cut below the stack's cut is opened by some instantiation. So the `∀` inside every W `U`
value is read at every position an admissible embedding can open. Transplant §3c's closure into W
at a `U` slot, at a stack whose outermost lend holds the cell and is adjacent to the bound (as in
`MuSlotIndex`, with the `μ` removed). It is then **not** a W `U` value: `RelendJ` asks its body at
the instantiation that opens the cut, where it fails [unchecked; the arithmetic is `adj_fails`'s].

**Adopting (B) at `cRLJ`'s own `∀`:**
- **What it buys.** Invariance of a top-level `∀`-computation under instantiations
  (`AllPosJTransport`). No statement in ProbeD1 reads it: the thaw transports values; a
  computation is transported only inside `U`, or inside the share, which quantifies over re-lends
  itself.
- **What it costs.** `∀I` (`AllIRow`, `Statement1.lean:144`) must give the body at every
  instantiation. It calls its premise at the instantiated index, with the context carried there by
  the context's thaw (`CtxRelendableAtJ`). Today it needs no thaw; its own-lend conjunct needs
  `MonoOwnG`, a different fact. So `∀I` would inherit the thaw's partiality, R1 included, as the
  `U` rows have.
- **Recommendation.** Keep `cRLJ`'s `∀` unchanged. Adopt (B) when a statement needs a computation
  at `∀` carried across an instantiation outside `U`. Candidates are statement 2's share at a
  resume, if its continuation clause is stated per index rather than per re-lend, and `cbpv`'s or
  `binder`'s `FutInst` (`BINDER.md` §5.6) [unchecked]. `AllPosJ` and its three lemmas are stated
  for that.

### 3.5 Core's `∀` is printed

- [TR] p. 4 prints `𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())` [read, page image]. [CONF]
  p. 415:12 prints it with `δ['a ↦ α]` and as `∀α. ⌜α ⊏ bδ⌝ −★ …` [read].
- `Life` is printed as `(ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)` ([TR] p. 4, §5 [read]; [CONF] Fig. 11,
  with "a semi-bounded lattice of natural numbers", p. 415:12 [read]).
- `Paper/S4_LogicalRelation/Definitions.lean` row 4.5 transcribes it, `[repair]` for
  `δ['a ↦ α]` and the guarded form. Core's `cC` at `.all` is its CBPV form.
- Neither is edited here. Every change in this design lives in ProbeD1's draft relation, and §2's
  route changes no definition at all.

### 3b. Agreement with Core at `σ = []`

- **Under (B): both directions.** `AllPosJNil`: the empty stack has no cut, so `InstAt [] ι` forces
  `ι = none`, `vwSL` at `[]` is `∅`, and the clause is Core's.
- **Under (A): one direction.** (A) ⇒ Core by the identity renaming (`CutAllNilSound`). Core ⇒ (A)
  is **refuted**: `not_coreAllImpCutAll` (`GapWitness.lean`). At `ℓ₀ ↦ mut(1, (), ∅, 𝒱⟦1⟧)` Core's
  clause holds, and at the renaming `shift ⊤ 1`, which opens the cut between `⊤` and the cell, it
  fails. This compares the `∀` clauses themselves; a W relation built with (A) is not defined, and
  its other clauses at `σ = []` would be `vRLJ`'s.
- **The converse at typable types**: a derivable term is related at both once FL holds at each.
  Nothing more is available now.

**Every downstream use of agreement.** All are stated at W₀'s `vRL`/`cRL` (`Statement0.lean`); none
is restated at `vRLJ` yet.

| use | direction it reads | under (A) | under (B) |
|---|---|---|---|
| `NilSoundRet` (`Statement0.lean:95`; proved, `Bridge.lean:133`; in `Statement0Shared`) | W ⇒ Core at `F_Σ A`, `A` data | unaffected: a data answer reads no `∀`; the operation types are read by Core's `vC` in `rowTab` | unaffected |
| Targets' `AdequateRetAt` (`Targets/B/Guarantees.lean:71`) | through `NilSoundRet` | unaffected | unaffected |
| Targets' `AdequateDriveAt` (`Guarantees.lean:79`) | W's computation at a thunk answer `U(Loop_Σ)` at `σ = []`; a W ⇒ Core route is not stated in ProbeD1 | the direction (A) keeps | `σ = []` is Core's |
| `NilSoundV`, `NilSoundC` (`:154`, `:161`) | W ⇒ Core at every type; `NilSoundC` at `A ⊸ C` reads Core ⇒ W at `A` | new failure sites at argument types with a `∀` under `U` whose body compares the bound variable with a cell [unchecked beyond the witness's type] | no new site |
| `NilAgreesU`, `NilAgrees` (`:167`, `:173`) | both | the Core ⇒ W half fails at the witness's type: `not_coreAllImpCutAll`, once W's `∀` at `σ = []` is read as `CutAllC` [unchecked identification]; DESIGN §6.3 exempts `NilAgrees` from the arising check | no new site |

DESIGN §4.3 already expects outcome (c) at callback types: Core redefined, a kernel change with a
SPEC entry. (A) would add the types whose `∀` body compares the bound variable with a cell, and the
redefinition would have to change Core's `∀`, the printed clause's transcription. (B) adds
nothing.

Independently of the `∀`: `vRLJ`'s `KeepsT` already narrows W's `U` at `σ = []` against Core's `U`,
since the body is owed only at extensions that keep the relevant records with their tags. Whether
W ⇒ Core survives it at `U` is not derived [unchecked].

### 3c. The witness: Core's ℕ-`∀` reads the room (proved)

`GapWitness.lean`, statements in `Gap.lean`:

```lean
abbrev adjC : CTy := .all 0 .top (.ret (.mut (.var 0) .unit))   -- ∀'0 ⊏ ⊤. F (Mut '0 1)
abbrev adjE : Expr := .val (.lam (.val (Val.loc 0)))             -- Λ. return ℓ₀
def CoreAllAdjacent : Prop :=
  cC adjC [] adjδ adjE (innerView 0 (lifeN 1)) ∧ ¬ cC adjC [] adjδ adjE (innerView 0 (lifeN 2))
def CoreAllNotNatural : Prop :=
  ∃ C ls δ e ρ, cC C ls δ e ρ ∧
    ¬ cC C (ls.map (Targets.srecRestrat adjθ)) (Restrat.LSub.mapN adjθ.toNat δ) e (adjθ.relRU ρ)
def NotCoreAllImpCutAll : Prop := ¬ ∀ C ls δ e ρ, cC C ls δ e ρ → CutAllC C ls δ e ρ
```

**Proved** (`coreAllAdjacent`, `coreAllNotNatural`, `not_coreAllImpCutAll`):

- **`adj_holds`.** At `ℓ₀ ↦ mut(1, (), ∅, 𝒱⟦1⟧)` (GhostEnd's `innerView 0 1`), every `α ⊏ ⊤` is
  `⊑ 1`. The proof is `wpTS_lolli`, `wpTS_val`, and `innerView_ptoMutS` at a lower index.
- **`adj_fails`.** At any single `mut` cell at `2` with an empty witness the clause fails. The
  steps:
  1. Instantiate the clause at `α = 1`.
  2. Run its `wpTS` at the empty frame, in the cell's own `TW` world (`alloc`, then `mutFold`),
     under `Alloc.leastFree`.
  3. The answer's cell is a top-level `mut` cell of a part of the valid post-resource, so it is in
     the flattening there (`pvLocal`).
  4. `↭`'s `mut` clause (`ResU.UpdMut`) carries it back to the start's flattening, which is the
     cell itself (`flat_single_mut_empty`, `ResU.Flat.functional`). So it is at lifetime `2`.
  5. The answer's `ptoMutS` asks `1 ⊑ 2`, which is false.
- **`adj_relRU`.** `shift ⊤ 1` carries the cell at `1` to such a cell (`relRU_single`,
  `relU_mutOf`, `relRU_empty`).

**What it shows.**
- The two configurations have one order type, `⊤ ⊐ 1` and `⊤ ⊐ 2`, related by an order embedding
  fixing `⊤`. Core's relation tells them apart, so it is not invariant under that embedding.
- The full position-`∀` is strictly stronger than Core's `∀` at `σ = []` (§3b).
- `TyEq` behaves otherwise: `TyEqRoomBlind` (§2).

**The arising check.**
- The witness refutes none of the probe's targets. It refutes two comparisons:
  - "Core's relation is invariant under every embedding fixing `⊤`", which no one states;
  - "Core's `∀` implies reading (A)", which is a statement about two definitions. Like
    `NilAgrees` (DESIGN §6.3), that is decided by any inhabitant.
- So DESIGN §11's arising check does not bear on it.
- For the record: the cell's world is a `TW` world (`tw_single_mut_empty`). The value `Λ. return ℓ₀`
  at `∀'0 ⊏ ⊤. F (Mut '0 1)` over a lend of `ℓ₀` is not claimed derivable [unchecked]: `Mut 'a 1`
  to `Mut '0 1` needs `'0 ⊑ 'a`, which `'0 ⊏ ⊤` does not give unless `'a` is `⊤`.
- Any refutation of a *target* by this mechanism, such as `NotMuSlotThawCore` (§4), needs the
  arising check before it counts.

---

## 4. The remaining cases

| case | what it needs | expected |
|---|---|---|
| `Mut` payload at a bound place (the stored predicate) | the handed view stores `𝒱⟦e.T⟧` at the instantiated reading; the slot asks `𝒱⟦T⟧` there; `TyEqInst` and `vC_tyEq` equate them, and the support transfers the same way | to follow from §2 |
| `Imm` payload at a bound place | the observable payload from the full one (`vO_obs`), `TyEqInst`, the coherence record moved (`CohEInstOB`) | to follow from §2 |
| `Mut`/`Imm` retained | `RetainedPay` (`PayExt`): the payload is read at fixed lifetimes, so `vC_congr` equates the relations at every list, the stored predicate and its support included; `Imm`'s `CohE` by `CohEInstOB` | to follow (the `Mut` case is proved at every payload already); `RetainedPay` is still owed by the rows that make such values (`BINDER.md` §11.4) |
| thunks (`U` slots) | by construction (`relendJ_thunk`, `instComp`) | proved |
| thunks inside `Mut`/`Imm` payloads | at a bound place the payload is re-read up to `TyEq`; retained, by `PayExt` | to follow, through the two rows above; no relation is transported |
| `μ`, `fam` slots (R1) | Core's relation, handed the slot whole: its `U` inside is Core's, read at the instantiated reading with Core's ℕ-`∀` | **not expected through Core**; see below |

**R1 through Core.** `Gap.lean` §4 states the configuration and the expected failure:

```lean
abbrev muAdjTy : VTy := .mu (.thunk adjC)                 -- μX. U(∀'0 ⊏ ⊤. F (Mut '0 1))
abbrev muEnt : LEnt := ⟨0, 1, .unit, .mut, fun _ => true⟩  -- a 6.65 entry lending ℓ₀
def MuSlotIndex : Prop := …   -- the thaw's hypotheses at [muEnt], [1], the view at ℓ₀, the slot
def NotMuSlotThawCore : Prop := ¬ CtxRelendableAtJ .binder0 LifeCtx.empty muΓ
```

- The stack `[muEnt]` at `1` has cut `⊤`, and the entry's view at `ℓ₀` is the slot's closure's
  resource. Core's `∀` inside the slot holds there by adjacency (`adj_holds`'s arithmetic).
- At the instantiation `shift ⊤ 1` the view is handed back at `2`, and the slot fails
  (`adj_fails`'s).
- Not attempted. It would refute a statement of ours (`CtxRelendsAllJ` at a `μ` slot) at a
  configuration not shown to arise, so it would count against the Core route only after the
  arising check.
- What it would show is the reason `BINDER.md` §5.4 already gives the route: **W reads `μ` and
  `fam` itself.** A thunk inside is then W's `U`, which reads every internal position by
  construction (§3.4), and `MuSlotIndex`'s closure is not a W value to begin with.

**The knock-on.**
- **The `U` rows (`BinderJ.lean`)**: `Statement0UThawFreeKJ .binder0` at `CtxThawFreeK` contexts
  (§2.3). `Statement0UFullJ` still waits on R1.
- **Statement 0**: `binder0`'s own `MonoV`, `MonoG` and `MonoOwnG` are unaffected and still not
  derived. `cbpv` and `binder` owe `BINDER.md` §5.6's list as before. OQ-8 is unaffected.
- **`ThawFreeScope`** (`BINDER.md` §5.2): typing reaches a `μ` slot inside a lend, so R1 remains a
  guarantee gap, now the only one in the thaw.

---

## 5. The literature, and the dense carrier

- **Order atoms are `(ℚ, <)`** [read]. BKL (Bojańczyk, Klin, Lasota, *Automata theory in nominal
  sets*, LMCS 10(3:4), 2014; arXiv:1402.0897):
  - Ex. 2.3: the total order symmetry is `ℚ` with its monotone bijections.
  - Ex. 2.5: `ℚ²` has three orbits.
  - Ex. 4.6: a finitely supported subset of `ℚ` is a finite Boolean combination of intervals.
  - Cor. 9.5: the symmetry admits least supports. The proof's key step is that the orbit of `c`
    under the stabiliser of a finite `E` is the whole open interval between `c`'s neighbours in
    `E`, which is density.
  - Thm. 10.3: a Fraïssé limit is homogeneous (every finite partial isomorphism extends to an
    automorphism).
  - Ex. 10.4: `(ℚ, <)` is the Fraïssé limit of finite total orders.
  - Ex. 10.12: `ℚ^(<n) × ℚ` has `2n + 1` orbits, the positions of a new point relative to `n`
    ordered ones.

  Pitts, *Nominal Techniques*, ACM SIGLOG News 3(1), 2016, §9 "Different symmetries" [read]: the
  linear-order symmetry identifies the names with `ℚ` and takes the order-preserving permutations.
  It is one instance of the Fraïssé pattern. Whether such symmetries have name abstraction like
  Nom's "remains to be investigated". Pitts, *Nominal Sets* (CUP 2013): nominal sets are the
  Schanuel topos, sheaves on `FinSet_mono^op` with the atomic topology [relayed, nLab "Schanuel
  topos"]. Its treatment of ordered atoms is [unverified].
- **Homogeneity is what makes a quantifier over atoms a quantifier over positions.** Over `(ℚ, <)`,
  an equivariant property of `(x̄, z)` depends only on the orbit, that is the position of `z`
  relative to `x̄`. Every position is realised, and any two realisations are related by an
  automorphism fixing `x̄`. So `∀z ∈ ℚ` is `∀` over the `2n + 1` positions. `(ℕ, <)` is not
  homogeneous: its automorphism group is trivial, and a one-point extension type over a finite
  subset need not be realised over it (there is no room between `n` and `n + 1`). So `∀z ∈ ℕ` is
  `∀` over the positions realisable at the given configuration, which is §1.2's adjacency.
  Embeddings form a monoid, not a group, so the group-based theory gives nothing directly for ℕ.
  That is why the probe works with `Restrat.Emb` and transport.
- **Kripke models over finite linear orders** [relayed]. Worlds are finite linear orders, the
  order is order embeddings, and `∀` over a new element at a world ranges over every one-point
  extension in every later world: every position. With the atomic topology the sheaves on
  `FinLinOrd^op` are the continuous `Aut(ℚ, <)`-sets. Caramello's theorem gives
  `Sh(f.p.T-mod^op, J_at) ≃ Cont(Aut(M))` for a theory with amalgamation and joint embedding and
  its homogeneous model `M` (arXiv:0805.2778, Thm. 2.9 [relayed, through a summary]); its instance
  at linear orders is `M = (ℚ, <)`. Reading (B) is this Kripke `∀` restricted to the part of the
  world admissible embeddings may extend, the internal lifetimes. Reading (A) is the unrestricted
  one, and its accessibility would have to rename retained cells (§3.2).
- **Why `TyEq` needs none of this.** `TyEq` is universal–equational over the lattice `(ℕ, min, max,
  0)`. The two-element lattice generates the variety of distributive lattices (Birkhoff
  [relayed]), and a chain's lattice homomorphisms to `2` are its threshold maps. A universal
  conjunction of equations is preserved by them and reflected jointly, which is §2's cover. The
  relation's `∀` is not universal–equational (strict bound, non-strict body, wands, `∃` over
  resources), so it reads the room.
- **The dense carrier: recorded, not taken.** `Life := ℚ≥0` with `⊑ ≜ ≥`, `⊤ = 0` would make the
  ℕ-`∀` homogeneous. It keeps `↓α ≜ α + 1` ([TR] p. 5) and H4. Two reasons it is not taken:
  - **It changes a printed definition**: `Life` at [TR] p. 4 and [CONF] Fig. 11, where [CONF]
    p. 415:12 says the lattice is of natural numbers.
  - **It breaks the stratification that defines `Cell`.** `Cell` is defined by well-founded
    recursion on lifetimes with the measure `OrderDual.ofDual` on ℕ
    (`Paper/S5_Model/Definitions.lean:186–187`; `MutF.hβ`, "`β ⊐ α`; this makes the recursion
    well-founded"; [CONF] p. 415:20, "a very different measure"). A `mut` cell at `α` stores
    `P̂ : Val → SProp_β` with `β ⊐ α`. In a dense chain with a top, every `α` has an infinite
    strictly ascending chain below `⊤`, so the recursion upward is not well-founded. Solving it
    would need a fixed point the rules exclude (no step-indexing) [unchecked as a Lean statement].
  - Density belongs in the accessibility, not in the carrier, which is the Kripke reading above:
    worlds stay finite and the stratification stays as printed.

---

## 6. Lean statements, success and failure, the arising check

### 6.1 The statements

All are in `ProbeD1/Gap.lean`, which elaborates. Proved now (`GapWitness.lean`):
`coreAllAdjacent`, `coreAllNotNatural`, `not_coreAllImpCutAll`, with `adj_holds`, `adj_fails`,
`adj_fails'`, `adj_fails_relRU`, `adj_relRU`, `flat_single_mut_empty`, `tw_single_mut_empty` and
`ptoMutS_innerView_le`.

| § | statement | status |
|---|---|---|
| 1 | `InGap`, `TyEqGapStep` | stated |
| 2 | `collapseN`, `InterpCollapse`, `EqOfCollapse`, `TyCover`, `TyEqOfCover`, `CoverInst`, `CoverGap`, `TyEqRoomBlind`; `TyEqInst` (`Binder.lean`) at every type | stated, not attempted |
| 2 | `CohEInstOB`, `ViewSlotInstOB`, `ThawFreeK`, `CtxThawFreeK`, `RelendJValueK`, `CtxRelendsThawFreeKJ`, `ThunkFRowKJ`, `ThunkVRowKJ`, `BangThunkFRowKJ`, `BangThunkVRowKJ`, `Statement0UThawFreeKJ` | stated, not attempted |
| 3 | `SamePos`, `InstRealisesCut`, `AllPosJ`, `AllPosJNil`, `AllPosJSelf`, `AllPosJTransport` | stated, not attempted |
| 3 | `CutAllC`, `CutAllNilSound` | stated, not attempted |
| 3c | `CoreAllAdjacent`, `CoreAllNotNatural`, `NotCoreAllImpCutAll` | **proved** |
| 4 | `muAdjTy`, `muEnt`, `muΓ`, `muγ`, `MuSlotIndex`, `NotMuSlotThawCore` | stated, not attempted |

### 6.2 Success

1. **The gap closes**: `InterpCollapse`, `EqOfCollapse`, `TyEqOfCover`, `CoverInst`, `CoverGap`
   proved. Hence `TyEqInst` at every type, `TyEqGapStep` and `TyEqRoomBlind`.
2. **The leaves at every payload**: `CohEInstOB`, `ViewSlotInstOB`, `RelendJValueK`, and
   `Statement0UThawFreeKJ .binder0`, each by the existing proof with `TyEqInst` and `vO_obs` in
   place of `tyEq_inst` and `vC_true_eq_false`. `relendJ_mut` and `relendJ_imm` lose `CoreStable`.
3. **If (B) is adopted** (§3.4): `InstRealisesCut`, `AllPosJNil`, `AllPosJSelf` and
   `AllPosJTransport` proved, and `AllIRow` re-proved with the context's thaw.
4. **(A)'s cost on record**: `CutAllNilSound` proved. `not_coreAllImpCutAll` is done.

Success at 1–2 settles the gap `BINDER.md` §11.2 names. It leaves R1 as the thaw's only guarantee
gap, and decides nothing about OQ-8.

### 6.3 Failure

- **A refutation of `TyEqOfCover`, `CoverInst` or `TyEqInst`** at some type. `TyEq` is a definition
  of ours, and these are statements about it, not about what a program reaches. So a refutation at
  any readings decides them, with no arising check, as for `NilAgrees`. It would be a fact about
  §2.1's argument, and the report names the clause where it fails. No failure is expected: the
  argument, and the brute-force check of §2.1.
- **A step of §2.3 that does not go through mechanically**: the report names the lemma and the
  type.
- **None of these is a failure of type (a), (b) or (d)** (synthesis §11). No guard beside `TW`, no
  second relation family, and no second quantifier is added. `AllPosJ`, if adopted, generalises the
  `∀` clause the way `RelendJ` generalised the `U` clause's re-lend, at the same clause.

### 6.4 The arising check

- **§3c's witness**: none needed. It refutes no target, and the comparison it decides is between
  definitions (§3c).
- **`NotMuSlotThawCore`**, if proved: a refutation of `CtxRelendsAllJ` at a `μ` slot, a statement
  of ours. It counts against the Core route for R1 only with DESIGN §11's check, a closed program
  whose run reaches the stack `[muEnt]` with such a closure in a `μ` slot. The closure is not
  claimed derivable [unchecked], while typing does reach `μ` slots inside a lend (`ThawFreeScope`).
  Until then it is evidence for `BINDER.md` §5.4's route, not an obstruction.
- **Any refutation built later by §3c's mechanism** follows the same rule: the configuration, the
  closed program and its run, or it decides nothing.

### 6.5 Order of work

1. §2.2's five steps, then §2.3's re-proofs. Mechanical after `TyEqOfCover`.
2. R1's route (W reads `μ` and `fam`), designed in its own unit. `NotMuSlotThawCore` only if that
   design needs the Core route ruled out.
3. (B) at `cRLJ`'s `∀` only when a statement asks for it (§3.4).

---

## 7. Report lists

- **Printed objects read**:
  - [TR] p. 4: §4's `∀` row and §5's `Life`, from the page image;
  - [TR] p. 5: `↓α ≜ α + 1`;
  - [TR] 6.64's and 6.65's H4 and 6.150's H11: "for any lifetime, the set of lifetimes shorter than
    it is infinite";
  - [CONF] Fig. 11, p. 415:12 (the `∀` clause with `δ['a ↦ α]`), and p. 415:20 (the measure).
- **Printed hypotheses unspent**: none is spent here. §2's cover reads H4's infinitely many shorter
  lifetimes informally; no lemma is cited.
- **Uniqueness and functionality results.** Used in the witness: `ResU.Flat.functional`,
  `ResU.CompS.functional`, `CellU.mutOf_at`, `Option.some.inj`. Not used: the machine's
  determinism (the refutation reads `↭`, not the run).
- **Printed lemmas in the run-up that are untranscribed**: none read here.
- **Hypotheses added**: none. The widened statements drop `CoreStable` and keep `OuterBelowTop`,
  which `not_cohEInst` requires.
