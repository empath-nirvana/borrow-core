# ProbeD1: the freeze binder at W — PlaceViews and the lifetime instantiation

**What this is.** The design of the unit after statement 0 of the D1 tractability probe (`DESIGN.md`,
`README.md`). Statement 0 stopped at the `U` introductions. Every placement owes them for two shared
reasons (DESIGN §15.3, §15.6): the context's thaw (Q1, the configuration `k`) and `Δ`'s models at a
re-lend (Q2, `q2_reached`). This unit reads both through the user's framing: "freeze is a binder over
internal locations, lifetimes and instances; resume and placement instantiate it". It fixes the two
halves of the binder that statement 0 needs:
- the location half: a place the stack lends is bound, and a borrow cell there, at any depth, is the
  binder's view (PlaceViews);
- the lifetime half: the re-lend at a resume instantiates every internal lifetime, preserving their
  order, and moves the records the frozen computation made with them.

It fixes the Lean statements, the revision of W's clauses they enter, the proof plan, the arising check
for `mut_not_natural`, what success and failure look like, and what each outcome means for D1, OQ-8
and the fallback.

**The Lean.** Two files hold this design's definitions and its `def … : Prop` statements, and
`lake build ProbeD1` elaborates both. They have no proof, and no `sorry`, `axiom`, `native_decide`,
`opaque`, `partial`, `unsafe` or `implemented_by`.
- `ProbeD1/Binder.lean`: the relation-independent definitions and statements (items 1–3), and the
  revised world pieces: `OwnOKI`, `OwnPushI`, `FutOKI`, `FutStepI`, `FutI`, `FutQI` (§2.1), and the
  revised arising set `ArisesI` with its lends `LendMutI`, `LendImmI` (§1.4).
- `ProbeD1/BinderW.lean`: the revised relation `vRLI`, `cRLI`, `effRetI`, `gRLI` and judgement
  `SemSI` (§5.1), and item 4's statements at it (§5.2).

The revised definitions carry the suffix `I` and sit beside W₀'s, so no proof of W₀ breaks. When the
revision lands (§6 step 2) they replace W₀'s in `World.lean`, `Relation.lean`, `Sem.lean` and
`Arising.lean`, and W₀'s proofs are redone. Every statement of this design is stated at the revised
definitions: the item-4 target that elaborates is the one §5.2 describes. Two statements read W₀'s
transitions on purpose: `PVWLendMut` and `PVWLendImm` take `LendMut` and `LendImm`, which `LendMutI` and
`LendImmI` imply, so they are the stronger forms and serve `ArisesI`'s induction. The lemmas the proof
plan names on the way are not statements of the design; §6 lists them as lemmas to be built.

**Worlds.** [W] is this probe's relation as §5.1 revises it (`BinderW.lean`). [W₀] is the relation
as built (`Relation.lean` at `b7c1a32`). [Core σ=[]] and [GE] are as in DESIGN.md. A result at one is
not a result at another.

**Rules this design keeps.** DESIGN.md's, unchanged:
- Nothing breaks the borrow calculus. No printed BoLo definition and nothing in `Core/` changes; the
  changes are to ProbeD1's draft W.
- The paper is not wrong. Every refutation the probe can produce is of a statement of ours.
- An obstruction is an elaborating `def … : Prop` whose negation is proved at a configuration that
  arises (DESIGN §11), with the closed program exhibited. Over-approximate arising is sound for proving
  and unsound for refuting. A statement refuted at a configuration not shown to arise is a fact about
  that statement and evidence at most; it decides nothing (§4).
- One relation at W; the placements are candidates for it. No relation family beside it. No
  step-indexing. Multi-shot is ignored.

---

## 0. On one page

| item | Lean (`ProbeD1.…`; `Binder.lean`, item 4 and the revised relation in `BinderW.lean`) | what it settles |
|---|---|---|
| 1. PlaceViews | in W: `PlaceViewsL` (the guard, at every depth), `PlaceViewsAt` (its top-level part), `CohS` (leaves), `vwEW`/`vwSW`/`vwSL` (views), `OwnOKI.placeFree`, `OwnPushI`'s `ViewAt`, `FutOKI.placesFree` (§5.1); the guard's run invariant, the local bundle `PVLBundle` = `PVLNil`, `PVLParts`, `PVLUpd`, `PVLRuns`, `PVLStart`, `PVLEnd`, `PVLHide`, `GuardInst`, `PVLFut`, `PVLResume`; the arising check of `k`, `PlaceViewsW` with `PVWNil`, `PVWUpd`, `PVWRun`, `PVWLendMut`, `PVWLendImm`, `PVWHide`, `ArisesInv`, `PVArises`, `PVLocal`, `KNotInArises`, `KSlotNotW`, `KNotViewAt` | Q1: what keeps `k` out of a run, and whether the guard carrying it is `TW`'s run invariant |
| 2. the lifetime binder | `cutOf`, `Inst`, `InstAt`, `Internal`, `InternalVar`, `OuterBelowTop`, `BoundBelowV`, `InternalOfBound`, `OwnPushBelowTop`, `InstModels`, `ReLendModelsI`, `Q2Inst`; the readings: `boundBefore`, `SubOutside`, `SubFresh`, `BoundInside`, `InternalBoundInside`, `SubOutsideInst`, `SubOutsidePush`, `SubOutsideExtend`, `SharedReadFixed`; the records: `Inst.recs`, `RecsOutside`, `RecsInsideOwn`, `LendFresh`, `RecsOutsideArises`, `RecsInsideOwnArises`, `RecsOutsideInst`, `RecFixed`, `RecUpTo`, `KeepsS`, `KeepsSComp`, `MovedRecPremises`; freshness: `IdxReads`, `InstFresh`, `InstFreshExists`, `freshI`, `FreshFrameI`; the clause: `RelendI` (and `RelendUI`, next unit); bookkeeping: `InstReLend`, `ExtSInst`, `EmbLift`, `InstComp`, `ExtInst`, `StackJInst`, `ShareReLendInst`; equivariance: `TyEqInst`, `CohEInst`, `ViewSlotInst`, `MutPayloadInst` (stored predicate and support), `InstEquivLeaf`, `ViewTypeCoincidence`; beyond the partial result: `InstEquivLeafAll`, `MutPayloadInstAll` | Q2: `Δ`'s models at every instantiation the clause ranges over; what the instantiation moves, and that it is only what the frozen computation made; the records' action; the equivariance the relation owes |
| 3. the known risk | `Targets.NotVDenNaturalArises`, `InternalPayloadArises`, `MutWitnessThaws`, `MutWitnessThawsInhabited`; beside them `NotVCNaturalCore`, `NotVCNaturalCoreRefutes` | whether `mut_not_natural`'s witness arises, and whether it bears on an order-preserving instantiation |
| 4. the `U` introductions retried | the revised W: `vRLI`, `cRLI`, `gRLI`, `SemSI`; target `Statement0UFull` (statement 0's four rows at `SemSI`: `ThunkFRowI` …, `CtxRelendsAll`, `ThawInst`); partial `Statement0UThawFree` (`CtxThawFree`, `ThawFree`, `CoreStable`, `CtxRelendsThawFree`, `ThunkFRowTF` …); its scope `ThawFreeScope`; `CtxRelendableAtI` | the four rows at `binder0` over instantiations; statement 0 and OQ-8 reconsidered |

**The decisions.**
- **PlaceViews enters W in four places.**
  - The guard: `PlaceViewsL`, beside `TabAtS`, at every depth of the local resource. A run can bring a
    cell nested in a `mut` witness to the top, so the top-level form is not what the transitions keep.
  - The views the `U` clause drops and hands back: `vwSL`, the views with their nested cells.
  - The leaves: `CohS` at `Mut` and `Imm` at a stack place. This is the type tie the guard cannot see.
  - The own lend: `OwnOKI.placeFree`, and `OwnPushI` at a callback-shaped type.
- **The guard rests on the local bundle.** `PVLBundle` has one fact per transition of W's semantics
  and per configuration the relation quantifies over, as statement 1's table facts do for `TabAtS`.
  A fact refuted at a configuration that arises is failure (b). The world form (`PlaceViewsW`,
  `PVArises`) only shows that `k` is not in the revised arising set, so that a refutation at `k`
  cannot pass DESIGN §11.
- **The re-lend becomes an instantiation.** It is a re-stratification `Restrat.Emb c` at the stack's
  cut. It acts on the reading substitution, the lend lifetimes, and the records whose frame lifetime
  is below the cut. No resource is transported, and the views are handed afresh at the instantiated
  reading.
- **It moves only what the frozen computation made.** Two index invariants, both from the lends'
  freshness ([TR] 6.64's and 6.65's choice of the lend, H4), make every lifetime it moves the frozen
  computation's own:
  - every variable bound before a lend is read above it (`SubOutside`, from the own lend's
    `SubFresh`), so an internal variable was bound inside the outermost lend
    (`InternalBoundInside`);
  - every record outliving a lend reads only lifetimes outliving it (`RecsOutside`, from
    `LendFresh`), so a record left alone is coherent at the instantiated reading.
- **The list handed after it keeps the records the dropped views are coherent with** (`KeepsS`),
  beside `Ext` at the retained part, up to what the relation does not read of a record (`RecUpTo`).
- **`binder0`'s `U` clause becomes `RelendI` in this unit.** `cbpv` and `binder` keep `RelendU` until
  the next unit (§5.6).
- **The item-4 target is statement 0's four rows at the revised W**, with the thaw at every context
  (`Statement0UFull`, at `SemSI` in `BinderW.lean`). The rows at `CtxThawFree` contexts are the
  partial result, guarantee gap R1 (`μ`, `fam`) open.

**The order** (§6). First the relation-independent facts: they are cheap, and they decide whether the
rest is worth building. Among them the local bundle's run facts, the largest unknown. Then the revision
of W, with the re-proofs. Then the rows.

---

## 1. The last unit's two needs, read through the binder

### 1.1 What statement 0 left

- **Q1, the context's thaw.** At `binder0` the `U` rows hold given `CtxRelendableAt` at the row's
  context.
  - It fails at `k` (`not_ctxRelendableAt_k`). `k` is a `mut` entry lending place `0` with payload type
    `Unk`, and a context slot `r : Mut '0 1` holding a cell at `0` that stores `𝒱⟦1⟧`.
  - `binder0`'s own `∀` and `⊸` clauses reach `k` from a typed closed term (`k_reached`), and its world
    is a `TW` world.
  - What keeps `k` out of a run is a lend-step invariant, `PlaceViews`, that neither the guard nor the
    own lend carries (`not_placeViews_k`, `lendMut_placeView`).
- **Q2, `Δ`'s models at a re-lend.** The rows need every re-lend of the stack to model `Δ`
  (`ReLendModels`).
  - It fails at a configuration typing reaches (`q2_reached`): `Λ'0. Λ'1 ⊏ '0. thunk (return ())`,
    where re-lending `'0` to `'1`'s lifetime breaks `'1 ⊏ '0`.
  - `BoundsStackFree` is sufficient for it, and does not hold there.

### 1.2 The binder reading

A `U` value at a stack is a frozen computation, as a stopped continuation is. Its stack's entries are
lends made around it. Their places, their lifetimes, and the lifetimes below them are the frozen
computation's own.
- **Bound locations.** A place the stack lends belongs to the binder. The only borrow cell there, at
  any depth, is the lend's view, at the lend's payload type and lifetime. `k` is a value at a bound
  place that is not the binder's view: the location half is not enforced (Q1).
- **Bound lifetimes.** The lifetimes at or below the stack's outermost lend are the frozen
  computation's (§3.1). The re-lend that the `U` clause and the share quantify over moves the stack's
  own lifetimes and leaves everything else where it was. So a variable instantiated inside a lend,
  below a lend variable, keeps its old lifetime while the lend's moves below it (Q2).
- **Resume instantiates.** A resume picks fresh lifetimes below the resumer's ([TR] 6.112's `И`). It
  must move every bound lifetime together, preserving every order among them and to the unbound ones.
  A re-stratification below a cut (`Restrat.Emb`) does exactly that, and Restrat proves that `⟦Δ⟧` is
  invariant under it (`Restrat.Emb.models_mapN_iff`).
- **A strictly monotone map on `ℕ` that moves one lifetime moves every shorter one.** So the bound
  lifetimes are a down-set: everything at or below the outermost lend. That is the binder reading only
  if every lifetime there that the index reads was made inside the frozen computation. Each place the
  index reads a lifetime is covered by an invariant (§3.1, §3.2):
  - the lend lifetimes are the stack's own;
  - a variable bound before a lend is read above it (`SubOutside`), so a variable read at or below
    the outermost lend was bound inside it (`InternalBoundInside`). It comes from the own lend's
    freshness below the reading (`SubFresh`);
  - a record outliving a lend reads only lifetimes outliving it (`RecsOutside`), and a record at or
    below the outermost lend is the lineage of one of the stack's 6.64 entries (`RecsInsideOwn`).
    They come from the lends' freshness below the records (`LendFresh`).

  The licence for each freshness is the lend's choice in [TR] 6.65's proof, H4: "Let α be some
  lifetime where α ⊏ γ ⊓ β. Such an α always exists because for any lifetime, the set of lifetimes
  shorter than it is infinite." 6.64's H4 is the same at `α ⊏ β`. The `И` both proofs unfold
  ("∃ γ. ∀ α ⊏ γ") admits every `α` below the bound, so the lend may be taken below any further
  finite set.
  - Without `SubOutside` the down-set can hold a variable bound outside the frozen computation, and
    the instantiation would move it. That is not a binder's instantiation, and a resumer reading
    that variable would disagree with the continuation (§3.1).

### 1.3 Four further gaps the same reading names

These are in [W₀]. Each is closed by a definition in §2–§3. Each is unchecked unless a Lean name is
given.
- **(a) The views read their payload at `δ`.** GhostEnd's `vwE δ e` reads `e.T` at the clause's `δ`.
  `extS` overrides `δ` at the stack's variables, so a payload type that mentions a stack variable is
  read at a stale or missing lifetime. W's views read the payload at the stack's reading
  (`vwEW (extS δ σ αs) e`).
- **(b) A view's cell may outlive its entry.** `viewP` admits a cell at any `b ⊒ α`.
  - So a slot typed `Mut 'f T`, with `'f` an outer stack variable, can hold an inner entry's view whose
    cell is at `α_f`.
  - After a re-lend, the entry's fresh view is at the entry's own lifetime, which no longer meets
    `'f`.
  - In a run the cell is at exactly the entry's lifetime: 6.65's `ρm = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`,
    which `↭` keeps. W's views, its guard and its leaves ask for the exact lifetime (`AtExactly`: a
    `mut` cell's lifetime, and every lifetime of an `imm` cell's set).
- **(c) The guard sees cells, not types.** A cell at a bound place being the entry's view says nothing
  about the type a slot holds it at, beyond the cell's stored invariant.
  - Two payload types can give one invariant at a reading, and different ones once an instantiation
    spreads two adjacent lifetimes apart. `ViewTypeCoincidence` states it, to be proved at `Imm 'w 1`
    against `[@'v](Imm 'u 1)` with `'v` just below `'w`.
  - A slot holding the view at the second type then cannot be re-established from the entry's fresh
    view.
  - So the type tie belongs at the leaf (`CohS`), where Core already has it for `imm` cells: `CohE`
    ties an `imm` cell's payload type to its 6.64 record, up to `TyEq`.
  - [TR] 6.117 (M-inv) says a `Mut` view depends only on the extension of its invariant. That holds at
    one reading. The instantiation changes the reading, which is why the extension does not suffice
    here.
- **(d) Records carry internal lifetimes.** A 6.64 entry's record (its `FrameRec` substitution and its
  frame lifetime) is read by Core's `Imm` leaf (`CohE`) and by `ptoImmS`'s record list. At the world,
  `TW … (rsOf ls)` and `Tagged` compare the record list with the world's records by equality.
  - The stack's own 6.64 records are below the cut, and a resume rebuilds them at the instantiated
    reading. The instantiation moves exactly those (`Inst.recs`), so an `Imm` slot coherent with one
    stays coherent.
  - Every other record is left as it is, since the world at a resume holds it unchanged. A slot
    coherent with it stays coherent because the record reads only lifetimes the instantiation fixes
    (`RecsOutside`, `CohEInst`, §3.2).

### 1.4 What changes in W

| W₀ | W | why |
|---|---|---|
| `guardW σ αs P` (`TabAtS`) | `guardPV s σ αs ls P` (`TabAtS ∧ PlaceViewsL s σ αs ls`) | Q1: the guard's views at every depth; the full payload of an `imm` view (§2.1) |
| leaves `Mut a T`, `Imm a T` at Core's `vC` | `vC … ∧ CohS σ αs (extS δ σ αs) A v` | (b), (c): the exact lifetime and the type tie at a bound place |
| `binder0`'s `U` clause, GhostEnd's `RelendableS` | `RelendI`: views `vwSL`, an instantiation in place of a re-lend, the list extended after it, keeping the records the dropped views are coherent with (`KeepsS`) and `RecsOutside` | Q2, (a), (d); `KeepsS` because `Ext` at the retained part does not keep the stack's own records |
| `OwnOK` | `OwnOKI`: adds `placeFree : ∀ ψ, ¬ DeepAt ρ e.l ψ` | the lent place's owner is with the lender, so no cell of the callback's resource is at that place at any depth; keeps `MonoOwnG` across `CohS`, and `PVLStart` |
| `OwnPush` | `OwnPushI`: `OwnOKI`, and `∀ A D, C' = .arr A D → ViewAt x e A` | the own lend is the lend the instance names: at a callback-shaped type its kind and payload are the view's |
| `cRL`'s `∀` clause, the own lend | asks `RecsOutside (α :: αs') ls'` and `SubFresh δ α` of the pushed lend | the own lend is fresh below the records and the reading ([TR] 6.65's H4), as a real lend is |
| `FutOK` | `FutOKI`: adds `placesFree : ∀ e ∈ τ, ∀ ψ, ¬ DeepAt ρ e.l ψ`; `FutStepI`, `FutI`, `FutQI` at it | keeps `MonoV`'s leaf case across `CohS`, and `PVLFut` |
| `SemS`'s index | `SemSI`: adds `RecsOutside αs ls`, `SubOutside σ αs δ` and `PlaceViewsL (extS δ σ αs) σ αs ls ρ` | the records' and the readings' invariants; the guard at the judgement's resource |
| `LendMut`, `LendImm`, `Arises` (`Arising.lean`) | `LendMutI`, `LendImmI`: add `LendFresh c.ls α`; `ArisesI` at them | the lend below the records' lifetimes ([TR] 6.64's and 6.65's H4): the source of `RecsOutside` and `RecsInsideOwn` at the arising set |
| `cbpv`/`binder`'s `RelendU` | unchanged in this unit; `RelendUI` in the next (§5.6) | keeps their proved facts while `binder0` is retried |

None of these is a printed definition, and none is in `Core/`. In Lean each revised definition is
W₀'s name with the suffix `I`, in `Binder.lean` or `BinderW.lean`. The guard, the leaves' `CohS`,
`RelendI` and the invariants have no W₀ counterpart and keep their names.

---

## 2. PlaceViews in W (item 1)

### 2.1 The definitions

```lean
def innerAt (σ : LStack) (αs : List Life) (l : BoCa.Loc) : Option (LEnt × Life) :=
  (σ.zip αs).find? fun p => decide (p.1.l = l)

inductive DeepAt : WRes → BoCa.Loc → CellU BoCa.Loc Val → Prop     -- at the top, or in any witness
  | top {ρ l ψ} : ρ.get l = some ψ → DeepAt ρ l ψ
  | wit {ρ m l φ ψ} : ρ.get m = some φ → DeepAt φ.wit l ψ → DeepAt ρ l ψ

inductive ExAt : WRes → BoCa.Loc → CellU BoCa.Loc Val → Prop       -- under no `imm` ancestor
  | top {ρ l ψ} : ρ.get l = some ψ → ExAt ρ l ψ
  | wit {ρ m l φ ψ} : ρ.get m = some φ → φ.kind = Kind.mut → ExAt φ.wit l ψ → ExAt ρ l ψ

def AtExactly (α : Life) (ψ : CellU BoCa.Loc Val) : Prop :=
  ψ.at = α ∧ ∀ t, ψ.lsOf = some t → ∀ y, t.mem y → y = α

def vwEW (s : LSub) (e : LEnt) (d : Bool) (α : Life) (ls : List SRec) : WProp := fun ρ =>
  vwE s e d α ls ρ ∧ ∀ ψ, ρ.get e.l = some ψ → AtExactly α ψ

def vwSW (s : LSub) : List BoCa.Loc → LStack → List Bool → List Life → List SRec → WProp
  | _, [], [], [], _ => emp
  | seen, e :: σ, d :: ds, α :: αs, ls =>
      vwEW s e (vis seen e d) α ls ⋆ vwSW s (e.l :: seen) σ ds αs ls
  | _, _, _, _, _ => fun _ => False

/-- The top-level part: what the thaw reads. -/
def PlaceViewsAt (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind ≠ Kind.own →
    ∀ (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ)

/-- W's guard conjunct. -/
def PlaceViewsL (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  (∀ l ψ, ExAt ρ l ψ → ψ.kind ≠ Kind.own →
    ∀ e α, innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ)) ∧
  ∀ l ψ, DeepAt ρ l ψ → ψ.kind ≠ Kind.own → l ∈ σ.map LEnt.l →
    ∃ e α, (e, α) ∈ σ.zip αs ∧ e.l = l ∧ vwEW s e true α ls (ResU.single l ψ)

def vwSL (s : LSub) (σ : LStack) (ds : List Bool) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ => vwSW s [] σ ds αs ls ρ ∧ PlaceViewsL s σ αs ls ρ

def guardPV (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (P : WProp) : WProp :=
  fun ρ => TabAtS σ αs ρ → PlaceViewsL s σ αs ls ρ → P ρ

def CohKind (s : LSub) (e : LEnt) : VTy → Prop
  | .mut _ T => (match e.k with | .mut => True | .imm _ => False) ∧ TyEq T s e.T s
  | .imm _ T => (match e.k with | .mut => False | .imm _ => True) ∧ TyEq T s e.T s
  | _ => False

def CohS (σ : LStack) (αs : List Life) (s : LSub) (A : VTy) (v : Val) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), v = .loc l → innerAt σ αs l = some (e, α) →
    CohKind s e A ∧ ∀ ψ, ρ.get l = some ψ → ψ.at = α

/-- The arising check's form: a shape, read off the world's flattening. -/
def PlaceViewsW (σ : LStack) (αs : List Life) (fρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) →
    ∀ ψ : CellU BoCa.Loc Val, fρ.FlatAt l ψ →
      (e.k = .mut → ψ.kind = Kind.mut → ψ.at = α ∧
        ∃ (δ' : LSub) (ls₀ : List SRec), mutPred ψ = fun v => vC true e.T ls₀ δ' v) ∧
      (∀ u, e.k = .imm u → ψ.kind = Kind.imm → ψ.at = α ∧ ψ.erase = u)
```

The own lend and a future's step, revised (`Binder.lean`; they replace `World.lean`'s when the
revision lands):

```lean
structure OwnOKI (δ : LSub) (σ : LStack) (αs : List Life) (e : LEnt) (a : Life) (ρ : WRes) :
    Prop extends OwnOK δ σ αs e a ρ where      -- chain, below, var, place, pay
  placeFree : ∀ ψ, ¬ DeepAt ρ e.l ψ

def ViewAt (x : LifeVar) (e : LEnt) : VTy → Prop
  | .mut (.var y) T => y = x ∧ (match e.k with | .mut => True | .imm _ => False) ∧ e.T = T
  | .imm (.var y) T => y = x ∧ (match e.k with | .mut => False | .imm _ => True) ∧ e.T = T
  | _ => True

def OwnPushI (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ e.x = x ∧
    x ∉ CTy.binders C' ∧ OwnOKI δ s.1 s.2 e a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    ∀ A D, C' = .arr A D → ViewAt x e A

structure FutOKI (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack)
    (αt : List Life) (ρ : WRes) : Prop extends FutOK δ σ αs k τ αt ρ where
  placesFree : ∀ e ∈ τ, ∀ ψ, ¬ DeepAt ρ e.l ψ
-- `FutStepI`, `FutI`, `FutQI`: `FutStep`, `Fut`, `FutQ` at `FutOKI`
```

**Where `ViewAt` excludes the own lend.** `ViewAt` is `True` at an argument type that is not a `Mut`
or `Imm` of a variable. At `Mut 'y T` or `Imm 'y T` with `y` not the binder, or at the other kind,
it is `False`, so `OwnPushI` admits no own lend at `∀'x. Mut 'y T ⊸ D` and its like, and the `∀`
clause's own conjunct is vacuous there. This is a restriction, and it is meant: only a borrow
constant's callback gets an own lend, and its argument is the binder's view.
- The consumers of the own conjunct read it at the binder's view. `CallbackExtMut` and
  `CallbackExtImm` take `∀'y. Mut 'y T ⊸ D` and `∀'y. Imm 'y T ⊸ D` with `e.x = y`, `e.k` of the
  view's kind and, revised, `e.T = T` (§5.5). `k_reached` reads `kC = ∀'0. Mut '0 1 ⊸ …`.
  `ThawFreeScope` reads `scopeC = ∀'0. Mut '0 1 ⊸ …` at `qEnt`, whose payload is `1`.
- The one borrow constant whose callback type can meet the exclusion is `withload`. Its callback
  takes `Imm̲ 'b T₁`, and at `T₁ = Imm 'z S` that is `Imm 'z S` with `'z` not the binder. Whether
  `withload` pushes an entry at all is statement 2's `SpanLoadRow` "entry-kind finding" (§5.4 R2).
  If it does, `ViewAt` is revisited there [unchecked].

**Five forms, each with one role.**
- **`PlaceViewsL`, the guard.** It is local, at the clause's reading `s = extS δ σ αs` and list `ls`,
  and it reaches every depth.
  - A borrow cell under no `imm` ancestor at a bound place is the innermost lending entry's view: of
    the entry's kind, exactly at its lifetime, with payload `𝒱⟦e.T⟧` at `s`.
  - A borrow cell under an `imm` ancestor at a bound place is the view of some entry lending the
    place. A 6.64 frame can freeze an outer entry's view while an inner entry lends the place again
    (§5.4 R2), and the frozen copy cannot be brought back out while the frame is open.
  - Why the depth [unchecked]. A cell nested in a `mut` witness reaches the top by a run, for example a
    write through `Mut 'y (Mut 'x S)` that moves the inner reference out of `y`'s payload. Before the
    run that cell is constrained only by Core's payload relation (`ptoMutS`: some `b ⊒ α_x`, the
    invariant `𝒱⟦S⟧`). So the top-level form at the start says nothing of the cell at the top at the
    end, and is not what the transitions keep.
- **`PlaceViewsAt`, its top-level part** (`PVLTop`): what the thaw reads.
- **`vwSL`, the views the `U` clause drops and hands back,** with their nested cells. A handed view's
  payload is read by Core's relation, which does not see the stack, so the nested part is asked of
  the view itself. That is what makes the guard hold at the instantiated composite (`GuardInst`).
- **`CohS`, the leaf's.** A value of type `Mut a T` or `Imm a T` located at a bound place has the
  entry's kind, a payload type `TyEq` to the entry's at the reading, and its cell at the entry's exact
  lifetime.
- **`PlaceViewsW`, the world's.** A shape at some reading: the arising check of `k` (§2.5), and
  nothing else.

**The `imm` payload stays in the guard.** `PlaceViewsL` asks of a 6.64 view its full payload,
`𝒱⟦e.T⟧(u)(R)` at the reading (`vwE`'s `ptoImmS` at `vC true`); a slot reads only the observable one
(Core's `Imm` leaf at `vCE false`). The payload is a property of the cell's value and witness, read at
the reading and at the list's records longer-lived than the cell. So each transition keeps it, and
the bundle's facts state it (§2.3):
- `↭`'s `imm` clause keeps the cell whole: lifetime set, value and witness;
- a part's copy of an `imm` cell has the composite's value and witness (`●` on `imm` cells);
- `Ext` keeps every record longer-lived than a cell of the resource;
- at a lend's start the view is the lend row's to supply, as `TabStart` takes its view. 6.64's
  `ρi = ℓ ↦ imm({α}, v, ρ_P̂(v))` comes with `ρ_P̂(v) ∈ P̂(v)` from the lender's owner `ℓ ↦ v ⋆ P̂(v)`.

`LendImm` records only `vShape`, which is why `PlaceViewsW` does not ask the payload. That form is the
arising check, not the guard.

### 2.2 How each enters W

The revised clauses are in §5.1 (`BinderW.lean`). In short:
- every `guardW` becomes `guardPV` at the clause's reading and list;
- `vRLI`'s `.mut` and `.imm` leaves conjoin `CohS`;
- `SemSI`'s index adds `RecsOutside αs ls`, `SubOutside σ αs δ`, and `PlaceViewsL` after `TabAtS`;
- the `∀` clause's own lend reads `OwnPushI`, and asks `RecsOutside` at the pushed stack and
  `SubFresh δ α`;
- `binder0`'s `U` clause is `RelendI` (§3.4), whose views are `vwSL`.

At `σ = []` `innerAt` is `none` and no place is bound, so `CohS` and `PlaceViewsL` are vacuous, and so
are `RecsOutside` and `SubOutside`. W's leaves are Core's there. `NilSoundRet` is unaffected.

### 2.3 The guard's run invariant: the local bundle

```lean
def PVLNil : Prop := ∀ (s : LSub) (ls : List SRec) (ρ : WRes), PlaceViewsL s [] [] ls ρ

def PVLParts : Prop :=
  ∀ s σ αs ls (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    (PlaceViewsL s σ αs ls ρ ↔ PlaceViewsL s σ αs ls ρ₁ ∧ PlaceViewsL s σ αs ls ρ₂)

def PVLUpd : Prop :=
  ∀ s σ αs ls (ρ π : WRes), StackOK σ αs → PlaceViewsL s σ αs ls ρ → ResU.UpdV ρ π →
    PlaceViewsL s σ αs ls π

def PVLRuns : Prop :=
  ∀ s σ αs ls (e : Expr) (Q : List SRec → Expr → WProp) (ρ : WRes), StackOK σ αs →
    PlaceViewsL s σ αs ls ρ → wpG ls e Q ρ →
      wpG ls e (fun ls' t ρ' => PlaceViewsL s σ αs ls' ρ' ∧ Q ls' t ρ') ρ

def PVLStart : Prop :=
  ∀ (s s' : LSub) σ αs ls (e : LEnt) (α : Life) (ρ a R : WRes), StackOK σ αs →
    List.IsChain (· < ·) (α :: αs) → e.l ∉ σ.map LEnt.l →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s σ αs ls ρ → (∀ ψ, ¬ DeepAt ρ e.l ψ) →
    vwEW s' e true α ls a → PlaceViewsL s' (e :: σ) (α :: αs) ls a →
    ResU.CompS ρ a R → PlaceViewsL s' (e :: σ) (α :: αs) ls R

def PVLEnd : Prop :=
  ∀ (s s' : LSub) σ αs ls (e : LEnt) (α : Life) (ρ' a R : WRes), StackOK (e :: σ) (α :: αs) →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s' (e :: σ) (α :: αs) ls ρ' → (∀ ψ, ¬ DeepAt ρ' e.l ψ) →
    PlaceViewsL s σ αs ls a → ResU.CompS ρ' a R → PlaceViewsL s σ αs ls R

def PVLHide : Prop :=
  ∀ (N : UInt32 → Bool) s σ αs ls ρ, PlaceViewsL s σ αs ls ρ → PlaceViewsL s (hideS N σ) αs ls ρ

def GuardInst : Prop :=          -- the instantiation (§3.6)
  ∀ δ σ ds αs ls ls' (ρz ρn ρ ρv R : WRes) (ι : Inst),
    StackOK σ αs → InstAt αs ι → stratS αs ρz → vwSL (extS δ σ αs) σ ds αs ls ρn →
    ResU.CompS ρz ρn ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ρv → ResU.CompS ρz ρv R →
    TabAtS σ (ι.life αs) R ∧ PlaceViewsL (extS (ι.sub δ) σ (ι.life αs)) σ (ι.life αs) ls' R

def PVLFut : Prop :=
  ∀ δ σ σ' αs αs' ls ls' ρ, StackOK σ αs → FutI δ ρ (σ, αs) (σ', αs') → Ext ls ls' ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → PlaceViewsL (extS δ σ' αs') σ' αs' ls' ρ

def PVLResume : Prop :=
  ∀ s σi σo ds αi αo ls (ρz ρv ρa R R' : WRes),
    StackOK (σi ++ σo) (αi ++ αo) → stratS (αi ++ αo) ρz →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls ρz → vwSW s [] σi ds αi ls ρv →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls ρv → PlaceViewsL s σo αo ls ρa →
    (∀ e ∈ σi, ∀ ψ, ¬ DeepAt ρa e.l ψ) → ResU.CompS ρz ρv R → ResU.CompS R ρa R' →
    PlaceViewsL s (σi ++ σo) (αi ++ αo) ls R'

def PVLBundle : Prop :=
  PVLNil ∧ PVLParts ∧ PVLUpd ∧ PVLRuns ∧ PVLStart ∧ PVLEnd ∧ PVLHide ∧ GuardInst ∧ PVLFut ∧
    PVLResume
```

**This is what the guard's claim rests on**, as statement 1's `TabNil` … `TabResume` are for `TabAtS`
(DESIGN §5.2). One fact per transition of W's semantics: the nil index, a part, a run (`PVLUpd`, with
`PVLRuns` its `wpG` form), a lend's start (`PVLStart`) and end (`PVLEnd`), a handler. And one per
configuration the relation quantifies over: an instantiation (`GuardInst`), a future (`PVLFut`), the
resume composite (`PVLResume`). Proved, they make `PlaceViewsL` the stack's run invariant, read from
`TW`'s runs transition by transition.

**The lend's end.** When a callback returns, the stack pops its entry: the view goes back to the
lender, the owner is restored, and the callback's result resource rejoins the outer context.
`PVLEnd` is the guard at the outer stack for that resource. Its hypotheses are what the end gives:
- the callback's result has the guard's views at the pushed stack;
- it holds no cell at the lent place at any depth, the view having been handed back;
- what the lender gets back, the owner (an `own` cell, which the guard does not read) and the
  payload, has the guard's views at the outer stack.

Who reads it: the borrow constants' rows, which pop (statement 2's `SpanW1Row`, `SpanW2Row`). Their
continuation is called at `SemSI`, whose index asks the guard of the post-lend resource. No row of this
unit pops: `CallbackExtMut` and `CallbackExtImm` conclude at the pushed stack, and a run at a stack
(`PVLRuns`) keeps the guard across any lend opened and closed inside it. Statement 1's table facts
have no end fact either. Its table analog is statement 2's to state beside the spans rows.

**Failure.** A fact of the bundle refuted at a configuration that arises (DESIGN §11) is failure (b):
the guard is beside `TW`. A fact not derived leaves the guard's justification open. It is reported
with the step it stopped at, and no claim that the guard is `TW`'s is made.

**`PVArises` is not this.** It is about the world form, at the arising set, whose direction is not
established. DESIGN §5.2: "A set not shown to contain every configuration that arises cannot carry a
claim about all of them." It justifies `KNotInArises` and nothing about the guard (§2.5).

### 2.4 The bundle's proof plan, and the printed technique each step spends

- **`PVLNil`**: `innerAt [] [] = none`, and `[]` lends no place.
- **`PVLParts`.**
  - A `mut` cell of a part is the whole's (`ResU.CompS.get_left_of_ne_imm`).
  - An `imm` cell of the whole at a place is the parts' copies composed, `imm(s₁ ∪ s₂, v, R)` at one
    value and witness. So each copy is exactly at `α` when the composite is (`AtExactly` asks every
    lifetime of the set), and the payload, read at the value and witness and at the records above the
    cell's shortest lifetime, is the same.
  - A cell nested in a part's cell is nested in the whole's cell at that place: a `mut` cell is the
    whole's, and an `imm` composite keeps the witness.
- **`PVLUpd`: [TR] 6.48's technique at the local part.** 6.48's proof accounts for a `mut` cell of the
  aliasable walk by its immutable ancestor (`ResU.upd_ag_eq_of_ne_own`, `ResU.upd_ag_mut_eq`,
  `Support/Model/Ancestors.lean`). The same accounting is this proof, and this is where the brief's
  "spend 6.48's mut clause" lands for the guard:
  - **A `mut` cell of `π` under no `imm` ancestor** (`ExAt`) is in `ex(π)`, where a `mut` cell
    composes with nothing, so it is `⦇π⦈`'s cell at its place. `↭`'s `mut` clause gives `⦇ρ⦈` a cell
    there at the same lifetime and stored invariant.
    - If `⦇ρ⦈`'s cell there were the `○` of copies under `imm` ancestors, `↭`'s `imm` clause would keep
      those ancestors whole in `π`, and `π`'s `ex` cell would meet their copies at the place: `π` would
      not be valid.
    - So it is a cell of `ρ` under no `imm` ancestor, which `PlaceViewsL` at `ρ` makes the innermost
      entry's view.
  - **A cell of `π` under an `imm` ancestor.** Its outermost `imm` ancestor is `⦇π⦈`'s cell at the
    ancestor's place, and `↭`'s `imm` clause gives it in `⦇ρ⦈` with the same witness. So the cell is
    nested in `ρ` at the same place, under the same ancestor, and `PlaceViewsL` at `ρ` gives it.
  - **An `imm` cell at a bound place.** `↭`'s `imm` clause keeps the flattening's composite (lifetime
    set, value, witness). So every copy in `π` has the view's value and witness and a set inside
    `{α}`.
  - **`○` at one stored invariant.** Where `⦇ρ⦈` composes copies of one view under `imm` ancestors,
    `mut ○ mut` is `mut(α ⊓ α, v, ρ, P̂ ∧ P̂)`, which is the view's cell.

  These are 6.48's cases: `ex` cells by `↭`'s `mut` clause, `ag` cells through their `imm` ancestor.
  No case split of ours is added.

  [unchecked] `StackOK` does not ask the stack's places distinct, so `PVLUpd` quantifies over stacks
  in which an inner `mut` entry lends again a place an outer 6.64 entry froze. No real lend makes one,
  since a 6.65 lend needs the place's owner and 6.64 has turned it into an `imm` cell. If the build
  meets such a stack, the hypothesis that excludes it is read off how lends are made, stated, and its
  scope checked. It is not a reason to split cases.
- **`PVLRuns`.** `wpG`'s run-end conjunct gives `ρ ↭ ρ' ● ρp`; then `PVLUpd`, and `PVLParts` at the
  run's local part `ρ'`. `ls'` has `ls`'s members, and the views read the list only through the
  members longer-lived than the cell (`ptoMutS`, `ptoImmS`).
- **`PVLStart`: 6.65's and 6.64's openings.**
  - The view is the lend row's: 6.65's `ρm` at exactly `α` storing `𝒱⟦T⟧` (`lendMut_placeView` at the
    world), or 6.64's `ρi = ℓ ↦ imm({α}, v, ρ_P̂(v))`, with its nested cells at the stack's places the
    lender's (`PlaceViewsL` at the lender's resource, by `PVLParts`).
  - `ρ` holds no cell at `e.l` at any depth: `OwnOKI.placeFree`, because the lender's
    owner was there.
  - The old entries' views read the same at `s'`, since their payload types do not mention the
    pushed variable.
  - `innerAt` changes only at `e.l`.
- **`PVLEnd`: 6.65's and 6.64's closings**, `PVLStart` read backwards.
  - `innerAt (e :: σ) (α :: αs)` and `innerAt σ αs` agree off `e.l`, and the result holds no cell at
    `e.l`. So every cell of the result at one of `σ`'s places is a view of an entry of `σ`, read at
    `s'`, which agrees with `s` at those entries' payload types.
  - The lender's part has the guard at `σ`, and `PVLParts`'s argument joins the two.
  - At `e.l` the restored owner is `own`, which the guard does not read.
- **`PVLHide`**: `hideS` changes only `cross`, which neither `innerAt` nor `vwEW` reads.
- **`GuardInst`.**
  - The table: `tabRelend`'s argument at the re-lend `ι.life αs`.
  - The views: `ρz` holds no borrow cell at a bound place at any depth. Such a cell is a view at an
    internal lifetime, while `ρz ∈ Res_o` and every nested cell lies above its parent.
  - `ρv`'s cells are `vwSL`'s, and an `imm` composite at a place is the fresh view's, since `ρz` holds
    none there.
- **`PVLFut`.**
  - The inserted places hold no cell of `ρ` at any depth (`FutOKI.placesFree`).
  - The old entries' payload types read the same (`extS_find_fut`), and `innerAt` at the old places is
    unchanged.
  - `Ext` keeps the records longer-lived than every top-level cell of `ρ`, and a nested cell lies
    above its parent.
- **`PVLResume`**: `GuardInst`'s argument for `ρz ● ρv`. `ρa`'s cells at `σo`'s places are views by
  `PlaceViewsL` at `σo`, and it has none at `σi`'s.

Model lemmas to be built on the way: `ResU.ExAt_flat` (an `ExAt` cell is `⦇ρ⦈`'s at a valid `ρ`) and
the ancestor read-back (a cell under an `imm` ancestor of `π` is one of `ρ` when `↭` keeps the
ancestor), both from `ResU.Flat.split` and the `ExS`/`AgW` constructors.

### 2.5 The arising check of `k`: PlaceViews at the world

The brief's arising check asks whether `k` can be an obstruction. A refutation is an obstruction
only at a configuration of the arising set with its program exhibited (DESIGN §11), so the question
is whether `k` is in that set: the revised one, `ArisesI`, whose lends carry `LendFresh`. The world
form answers it. It does not answer whether `k` arises: `ArisesI`, like `Arises`, is meant to
under-approximate what arises, which is not established, and it has no transition for a lend's end.
"`k` is not in `ArisesI`" is in the proving direction, and a universal negative over what arises
would need an over-approximation.

```lean
def PVWNil : Prop := ∀ W : WRes, PlaceViewsW [] [] W
def PVWUpd : Prop :=
  ∀ σ αs (W W' : WRes), PlaceViewsW σ αs W → ResU.UpdV W W' → PlaceViewsW σ αs W'
def PVWRun : Prop :=
  ∀ (c c' : Cfg) (e t : Expr), ResU.Hash c.ρf c.ρ → ResU.CompS c.ρf c.ρ c.fρ →
    PlaceViewsW c.σ c.αs c.fρ → RunEnd c e c' t → PlaceViewsW c'.σ c'.αs c'.fρ
def PVWLendMut : Prop :=
  ∀ (c c' : Cfg) (e : LEnt), ResU.Valid c.fρ → PlaceViewsW c.σ c.αs c.fρ → LendMut c c' e →
    PlaceViewsW c'.σ c'.αs c'.fρ
def PVWLendImm : Prop := …   -- the same at `LendImm`
def PVWHide : Prop :=
  ∀ N σ αs W, PlaceViewsW σ αs W → PlaceViewsW (hideS N σ) αs W
def ArisesInv : Prop :=
  ∀ c : Cfg, ArisesI c → ResU.Hash c.ρf c.ρ ∧ ResU.CompS c.ρf c.ρ c.fρ ∧ ResU.Valid c.fρ
def PVArises : Prop := ∀ c : Cfg, ArisesI c → PlaceViewsW c.σ c.αs c.fρ
def PVLocal : Prop :=
  ∀ (fρ ρf ρ : WRes), ResU.Valid fρ → ResU.CompS ρf ρ fρ →
    ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.mut → fρ.FlatAt l ψ
def KNotInArises : Prop := ∀ c : Cfg, ArisesI c → c.σ = kσ → c.αs = [kα] → c.ρ ≠ kρ
```

**The plan.**
- **`PVWUpd`: `↭`'s clauses** ([TR] p. 5, row 18; `ResU.UpdV`). At a `mut` cell of `⦇W'⦈` at a bound
  place, `ResU.UpdMut` read backwards gives a `mut` cell of `⦇W⦈` there with the same lifetime and
  stored invariant, and `mutPred` reads only that (`mutPred_mutOf`). At an `imm` cell, `ResU.UpdImm`
  gives the identical cell. `↭` and `PlaceViewsW` are both stated at the flattening.
- **`PVWRun`: [TR] 6.48**, `BoLo.updV_frame` (`TR.lemma_6_48`), then `PVWUpd`.
  - `RunEnd` gives `c.ρ ↭ π` with `π = c'.ρ ● ρp`, and, by associativity, `c'.fρ = c.ρf ● π`: the
    garbage `ρp` joins the frame (`ResU.CompS c.ρf ρp c'.ρf`).
  - 6.48 at `ρ₁ = c.ρf`, `ρ₂ = c.ρ`, `ρ₃ = π` gives `c.fρ ↭ c'.fρ`. Its hypotheses are `c.ρf # c.ρ`
    (`ArisesInv`) and `c.ρf # π` (from `✓c'.fρ`).
- **`PVWLendMut`: 6.65's opening** (`lendMut_placeView`), with the exact lifetime added.
  - The cell `LendMut` folds is `mutOf α v ρp hstr P hw`, at exactly `α`, and its invariant is the
    entry's view.
  - At `e.l`, `⦇c.fρ⦈` held `own(v)` in `ex`, and validity leaves no other cell there, because `own`
    composes with nothing under `●`. So `⦇c'.fρ⦈(e.l)` is the new view.
  - Elsewhere a `mutFold` changes the flattening only at the folded place:
    `ex(ℓ ↦ mut(_, _, ρp, _)) = ℓ ↦ mut(…) ● ex(ρp)` and `ag(…) = ag(ρp)`, against
    `ex(ℓ ↦ own ● ρp) = ℓ ↦ own ● ex(ρp)` and `ag = ag(ρp)` (`flat_fold_mut_ne`, to be built).
- **`PVWLendImm`: 6.64's opening**, likewise. The new cell is `immOf {α} v R h`. Elsewhere the payload's
  `ex` cells move under the `imm` cell into `ag`; at a bound place their flattening cell is unchanged,
  because validity leaves no other contribution there (`flat_fold_imm_ne`, to be built).
- **`PVWHide`** and **`PVWNil`** are immediate.
- **`ArisesInv`** and **`PVArises`** by induction on `ArisesI`, the recursor's `ArisesVI`/`ArisesCtxI`
  motives `True`. One case per constructor:
  - `nil`: `PVWNil`, and `TW`'s validity;
  - `run`: `PVWRun`;
  - `part`: `fρ` is unchanged, and so is the stack, so `PlaceViewsW` carries over as it stands. For
    `ArisesInv`, the new frame `ρf'` is `c.ρf ● ρ₂`, and `ρf' # ρ₁` is the constructor's premise;
  - `lendMut`, `lendImm`: `PVWLendMut`, `PVWLendImm`, through `LendMutI → LendMut` and
    `LendImmI → LendImm`;
  - `hide`: `PVWHide`.
- **`PVLocal`.** `ex` of a part is a `●`-factor of `ex` of the world (6.20, 6.18), and a `mut` cell
  composes with nothing. For an `imm` cell this fails, since the world composes copies.
- **`KNotInArises`** from `PVArises`, `ArisesInv` and `PVLocal` at `kCell`, then `not_placeViews_k`'s
  argument: `mutPred kCell = 𝒱⟦1⟧ ≠ 𝒱⟦Unk⟧ ls₀ δ'` at `loc 0`.

**Its role.** `PVArises` and `KNotInArises` say that `k` is not in `ArisesI`, so
`not_ctxRelendableAt_k` cannot pass DESIGN §11 and cannot be an obstruction. They say nothing about
whether `k` arises, and they do not justify the guard (§2.3).

### 2.6 Why the leaf as well as the guard

- A guard sees resources. `PlaceViewsL` makes a bound place's cell the entry's view, so `k`'s argument
  fails the guard at the `⊸` clause (`not_placeViews_k`).
- It cannot make the slot holding that cell typed as the entry's payload. `ViewTypeCoincidence` is the
  machine check of that limit. Core faces the same limit for `imm` cells, and its answer is at the leaf:
  `CohE` in the `Imm` clause ties the payload type to a 6.64 record up to `TyEq`.
- `CohS` is the same tie for the stack's entries, the 6.65 records Core does not keep (OQ-44). `TyEq`
  compares lifetimes by their readings. An instantiation applied to both readings keeps it
  (`TyEqInst`), which is what makes the thaw's re-establishment syntactic rather than extensional
  (`ViewSlotInst`).
- **The exact lifetime** is asked in three places. The views give it. The guard asks it of each cell,
  which for `imm` may be a composite of several slots' copies. The leaf asks it of each slot's own
  cell, which is what re-establishes the slot after an instantiation.

### 2.7 `k` under W

```lean
def KSlotNotW : Prop :=
  ∀ δ : LSub, ¬ CohS kσ [kα] (extS δ kσ [kα]) (.mut (.var 0) .unit) (.loc 0) kρ
def KNotViewAt : Prop := ¬ ViewAt 0 kEnt (.mut (.var 0) .unit)
```

- `KSlotNotW`: `k`'s argument `r = loc 0 : Mut '0 1` fails `CohS`, which asks `TyEq 1 Unk`. So it is
  not related at W's `Mut` leaf, and `k_reached`'s third conjunct (`k_slot`) is false at W. The build's
  `k_slot_not_W` is `KSlotNotW` through the revised leaf.
- `KNotViewAt`: under `OwnPushI`, the own lend at `kC = ∀'0 ⊏ ⊤. Mut '0 1 ⊸ …` has payload `1`. So
  `k`'s entry, with payload `Unk`, is not an own lend there.
- The relation-independent facts about `k` stay (`k_world_TW`, `k_world_tagged`, `kρ_get`,
  `not_placeViews_k`).
- `KNotInArises` is the arising answer to Q1: `k` is not in `ArisesI`, so `not_ctxRelendableAt_k`
  cannot pass DESIGN §11. It is not a claim that `k` does not arise (§2.5). The refutation
  `not_ctxRelendable_binder0` was a fact about [W₀]'s statement, and the revision is the fix it pointed
  at.

---

## 3. The lifetime binder (item 2)

### 3.1 Internal lifetimes

```lean
def cutOf (αs : List Life) : Option Life :=
  αs.getLast?.map fun o => OrderDual.toDual (OrderDual.ofDual o - 1)

def Internal (αs : List Life) (a : Life) : Prop := ∃ c ∈ cutOf αs, a < c
def InternalVar (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar) : Prop :=
  ∃ m, (extS δ σ αs).find? y = some m ∧ Internal αs (OrderDual.toDual m)
def OuterBelowTop (αs : List Life) : Prop := ∀ o ∈ αs.getLast?, o < ⊤

mutual
inductive BoundBelowV (Δ : LifeCtx) (σ : LStack) : LifeVar → Prop
  | stack {y} : y ∈ σ.map LEnt.x → BoundBelowV Δ σ y
  | bound {y u} : y ∉ σ.map LEnt.x → Δ.find? y = some u → BoundBelowL Δ σ u → BoundBelowV Δ σ y
inductive BoundBelowL (Δ : LifeCtx) (σ : LStack) : Lifetime.Life → Prop
  | var {z} : BoundBelowV Δ σ z → BoundBelowL Δ σ (.var z)
  | meetL {a b} : BoundBelowL Δ σ a → BoundBelowL Δ σ (.meet a b)
  | meetR {a b} : BoundBelowL Δ σ b → BoundBelowL Δ σ (.meet a b)
  | join {a b} : BoundBelowL Δ σ a → BoundBelowL Δ σ b → BoundBelowL Δ σ (.join a b)
end

def InternalOfBound : Prop :=
  ∀ Δ δ σ αs y, StackOK σ αs → OuterBelowTop αs → Δ.Models (extS δ σ αs) → BoundBelowV Δ σ y →
    InternalVar δ σ αs y
def OwnPushBelowTop : Prop := ∀ δ C ρ s e a, OwnPushI δ C ρ s e a → a < ⊤

-- the readings: a variable bound before a lend is read above it
def boundBefore (x : LifeVar) (δ : LSub) : List (LifeVar × ℕ) :=   -- bound before `x`'s newest binding
  (δ.entries.dropWhile fun p => p.1 != x).drop 1
def SubOutside (σ : LStack) (αs : List Life) (δ : LSub) : Prop :=
  ∀ (e : LEnt) (a : Life), (e, a) ∈ σ.zip αs → ∀ p ∈ boundBefore e.x δ, a < OrderDual.toDual p.2
def SubFresh (δ : LSub) (α : Life) : Prop := ∀ p ∈ δ.entries, α < OrderDual.toDual p.2
def BoundInside (δ : LSub) (σ : LStack) (y : LifeVar) : Prop :=
  y ∈ σ.map LEnt.x ∨
    ∀ eo ∈ σ.getLast?, y ∈ (δ.entries.takeWhile fun p => p.1 != eo.x).map Prod.fst
def InternalBoundInside : Prop :=
  ∀ δ σ αs y, StackOK σ αs → SubOutside σ αs δ → InternalVar δ σ αs y → BoundInside δ σ y

def SubOutsideInst : Prop :=
  ∀ σ αs δ (ι : Inst), SubOutside σ αs δ → SubOutside σ (ι.life αs) (ι.sub δ)
def SubOutsidePush : Prop :=
  ∀ σ αs δ (e : LEnt) α, e.x ∉ σ.map LEnt.x → SubOutside σ αs δ → SubFresh δ α →
    SubOutside (e :: σ) (α :: αs) (δ.extend e.x α)
def SubOutsideExtend : Prop :=
  ∀ σ αs δ x α, x ∉ σ.map LEnt.x → SubOutside σ αs δ → SubOutside σ αs (δ.extend x α)
def SharedReadFixed : Prop :=
  ∀ σi σo αi αo δ (ci : Life) (θ : Restrat.Emb ci) (eo : LEnt), αi.length = σi.length →
    cutOf αi = some ci → σi.getLast? = some eo → SubOutside (σi ++ σo) (αi ++ αo) δ →
    ∀ p ∈ boundBefore eo.x δ, θ (OrderDual.toDual p.2) = OrderDual.toDual p.2
```

**"Internal", made precise.**
- **The semantic definition is the one the clause uses.** A lifetime is internal to a stack when it is
  strictly below the stack's cut, so an instantiation at the cut may move it and fixes every other
  one. A variable is internal when the stack's reading sends it to an internal lifetime. The empty
  stack has no cut and nothing internal.
  - Below `⊤` the cut is the lifetime just above the outermost lend, and "internal" is "at or below
    the outermost lend".
  - When the outermost lend is `⊤`, the truncated `ofDual o - 1` gives the cut `⊤` itself. Then the
    outermost lend is not internal: every instantiation fixes it, and `Internal` is everything strictly
    below `⊤`. `OwnPushI`'s bound excludes this for every own lend (`OwnPushBelowTop`:
    `a ⊏ @c ⊑ ⊤`). A `LendMut` at `⊤` needs its payload and callback resource empty; nothing here
    excludes it, and nothing needs to.
- **The task's description is `BoundBelowV`**: the stack's variables, and the variables of `Δ` whose
  bound reaches below one. The bound may reach through `⊓`, the shorter of two, by one operand. Through
  `⊔`, the longer, it needs both, because `'y ⊏ 'x ⊔ 'u` puts `'y` below the longer of the two only.
- **`InternalOfBound`.** At an index that models `Δ`, at a stack whose outermost lend is below `⊤`,
  every `BoundBelowV` variable is internal. The proof is by mutual induction, with `Models` giving
  `δ(y) ⊏ u(δ)`, and `SLife.meet = max`, `SLife.join = min` on `ℕ`.
- **The semantic set alone can hold a variable bound outside.** Nothing in `Internal` looks at where
  a variable was bound. An example: an unbounded `'a` instantiated at `5`, then an own lend pushed at
  `3`. The cut is `2`, so `'a` is internal, though the frozen computation did not bind it. Every
  instantiation other than the identity moves it, since a strictly monotone map that moves the lend
  moves every shorter lifetime. Without an invariant on the reading, nothing excludes this: the
  `∀` clause instantiates `'a` at any lifetime below its bound, and the own lend is asked to be below
  the innermost lend, the resource and the records, not below the reading.
  - That is not a binder's instantiation: a binder leaves its free variables alone.
  - It is not free at the share (§3.7). The resumer keeps reading `'a` at `δ('a)`, the continuation
    at `θ(δ('a))`. An answer typed at `'a` would be given at the weaker lower bound `θ(δ('a))` and
    owed at `δ('a)`.
- **The readings' invariant (`SubOutside`).** For each of the stack's lends `(e, a)`, every binding of
  `δ` made before `e`'s variable was bound is read strictly above `a`.
  - "Before" is read off the association list: `extend` conses at the front, so the bindings made
    before `e.x`'s newest one are those after it (`boundBefore`). The own lend binds its variable in
    `δ` (`δ.extend x α`), so its push marks the place. An entry whose variable `δ` does not bind,
    such as a future's (`FutOKI.vars_sub` puts it outside `δ`), has no binding before it, and the
    invariant says nothing of it. Futures are the next unit's (§5.6 item 2).
  - **Sourced at the own push** (`SubOutsidePush`): the `∀` clause asks the pushed lend `SubFresh δ α`,
    below every value of the reading, and the bindings before the new variable are exactly `δ`'s.
    [TR] 6.65's H4 licenses the choice (§1.2).
  - **Kept** by an instantiation (`SubOutsideInst`, one strictly monotone map on both sides), and by a
    binding of a variable new to the stack, which comes after every lend (`SubOutsideExtend`). Which
    hypothesis keeps a `∀` binder off the stack's variables is read off `StackJ`, `BindersLow` and
    `FutAvoids` when the `∀` rows are built [unchecked].
  - **An index hypothesis of `SemSI`** (§5.1), vacuous at `σ = []`. It holds at `k_index` and at
    `q2_reached`'s index: at `kδ = ⟨[]⟩` nothing is bound, and at `qδ` nothing is bound before `'0`.
- **`InternalBoundInside`: with it, the semantic set is the frozen computation's.** At an index
  keeping `SubOutside`, an internal variable is a stack variable or was bound after the outermost
  lend (`BoundInside`). The proof: a variable off the stack is read at its newest binding; if that
  binding were before the outermost entry's, `SubOutside` would put its reading above the outermost
  lend, at or above the cut. So the variables the instantiation moves lie between the two
  descriptions:
  - `BoundBelowV` ⊆ `InternalVar` (`InternalOfBound`, at a model of `Δ`, the outermost lend below `⊤`);
  - `InternalVar` ⊆ `BoundInside` (`InternalBoundInside`, at `SubOutside`).

  Neither inclusion is an equality. A variable bound inside with an unconstrained bound may be read
  below the cut, outside `BoundBelowV`. One bound inside may be read above the cut, and then every
  instantiation fixes it.
- **Why the clause uses the semantic set.**
  - The relation does not know `Δ`, and need not. An instantiation preserves every order among all
    lifetimes (`Restrat.Emb.lt_iff`), so `⟦Δ⟧` is invariant for every `Δ` (`models_mapN_iff`).
  - Moving a variable that is internal but not `BoundBelowV` therefore costs nothing at the models. At
    an index keeping `SubOutside` such a variable was bound inside, for example by an unbounded `∀`
    instantiated after the push, below the lend.
  - At the leaves it costs nothing either: a retained resource is above the cut (§3.6), and the views
    are rebuilt.
  - At the records it costs nothing, given `RecsOutside` (§3.2): a record left alone reads only
    lifetimes the instantiation fixes, and a moved record is moved with the reading.
  - At the share it costs nothing, given `SubOutside`: the resumer's variables were bound before the
    ghost-ended entries, so the share's instantiation fixes them (`SharedReadFixed`, §3.7).

### 3.2 The instantiation, and the records

```lean
abbrev Inst := Option (Σ c : Life, Restrat.Emb c)

namespace Inst
def life1 : Inst → Life → Life   | none => fun a => a | some ⟨_, θ⟩ => θ
def life (ι : Inst) (αs : List Life) : List Life := αs.map ι.life1
def sub : Inst → LSub → LSub     | none => fun δ => δ | some ⟨_, θ⟩ => Restrat.LSub.mapN θ.toNat
def recs : Inst → List SRec → List SRec
  | none, ls => ls
  | some ⟨c, θ⟩, ls => ls.map fun x =>
      if x.2 < c then (⟨x.1.le, x.1.v, x.1.R, x.1.T, Restrat.LSub.mapN θ.toNat x.1.δ⟩, θ x.2)
      else x
def ofEmb {c : Life} (θ : Restrat.Emb c) : Inst := some ⟨c, θ⟩
end Inst

def InstAt (αs : List Life) (ι : Inst) : Prop :=
  ∀ (c : Life) (θ : Restrat.Emb c), ι = some ⟨c, θ⟩ → cutOf αs = some c

def RecsOutside (αs : List Life) (ls : List SRec) : Prop :=
  ∀ a ∈ αs, ∀ x ∈ ls, a < x.2 → ∀ p ∈ x.1.δ.entries, a < OrderDual.toDual p.2
def RecsInsideOwn (σ : LStack) (αs : List Life) (ls : List SRec) : Prop :=
  ∀ x ∈ ls, (∃ o ∈ αs.getLast?, x.2 ≤ o) →
    ∃ e ∈ σ, ∃ u, e.k = .imm u ∧ ∃ r ∈ rsOf ls, r.le = e.l ∧ DescR r x.1
def LendFresh (ls : List SRec) (α : Life) : Prop :=
  ∀ x ∈ ls, α < x.2 ∧ ∀ p ∈ x.1.δ.entries, α < OrderDual.toDual p.2

def LendMutI (c c' : Cfg) (e : LEnt) : Prop := LendMut c c' e ∧ ∀ α ∈ c'.αs.head?, LendFresh c.ls α
def LendImmI (c c' : Cfg) (e : LEnt) : Prop := LendImm c c' e ∧ ∀ α ∈ c'.αs.head?, LendFresh c.ls α
-- `ArisesI`, `ArisesVI`, `ArisesCtxI`: `Arises`, `ArisesV`, `ArisesCtx` with their lends at these

def RecsOutsideArises : Prop := ∀ c : Cfg, ArisesI c → RecsOutside c.αs c.ls
def RecsInsideOwnArises : Prop := ∀ c : Cfg, ArisesI c → RecsInsideOwn c.σ c.αs c.ls
def RecsOutsideInst : Prop :=
  ∀ αs ls (ι : Inst), InstAt αs ι → RecsOutside αs ls → RecsOutside (ι.life αs) (ι.recs ls)
```

- **What it is.** The identity, or a re-stratification `θ : Restrat.Emb c` at the stack's cut. `θ` is
  strictly monotone on all of `Life` (`Emb.strictMono`), lowering (`Emb.le_self`), and the identity at
  and above `c` (`Emb.fix`). So it preserves every `⊏` among internal lifetimes and from internal to
  external ones (`Emb.lt_iff`), and moves no external lifetime.
- **What it acts on.** The index only:
  - the reading substitution (`θ ∘ δ`);
  - the lend lifetimes;
  - the records whose frame lifetime is below the cut: their substitution and frame lifetime.
- **The records' action, settled.** `Inst.recs` moves a record exactly when its frame lifetime is
  below the cut, and leaves every other record as it is: tag, substitution and witness. `Emb.fix`
  alone would fix such a record's tag but not its substitution, which is a full `LSub` that may hold
  internal values. The world at a resume holds those records unchanged, and `TW … (rsOf ls)` and
  `Tagged` (through `DescR`'s `SubRec`) compare records by equality. So a record must be either left
  alone or rebuilt, and the action follows that line:
  - **Left alone:** a record at or above the cut, which the frozen computation did not make.
    `RecsOutside` makes it read only lifetimes the instantiation fixes, so an `Imm` slot coherent with
    it stays coherent at the instantiated reading (`CohEInst`), and the retained part's records are
    unchanged (`RecFixed`, §3.6).
  - **Rebuilt:** a record below the cut, which `RecsInsideOwn` makes the lineage of one of the stack's
    6.64 entries. A real re-lend at a resume re-opens that entry's frame over the payload the lender
    holds, at the instantiated reading and lifetime (§3.7). At the index `Inst.recs` keeps the record's
    witness and moves only its substitution and frame lifetime.
  - **The kept witness is the index's, not always the world's.** The re-opened frame's witness is
    the payload at the resume. It can differ from the kept one in two ways:
    - **Its borrow cells.** A 6.64 frame's payload can hold the view of another of the stack's
      entries, frozen under the frame's `imm` cell (§2.1; §5.4 R2 is one such shape). Its witness then
      holds that view at the old internal lifetime and reading. The resume re-lends that entry afresh,
      so the re-opened witness holds the view rebuilt at the instantiated one, and `TW.immFrame`'s and
      `Tagged`'s premises are met by the rebuilt record, not by `Inst.recs`'s. The relation reads a
      record's witness only through its `own` cells (`Coh`'s and `Rel`'s `Chain`). So the clause
      compares records up to their witnesses' borrow cells (`RecUpTo`, in `KeepsS`, §3.4), and the
      world's rebuilt record serves where the index's is asked.
    - **Its `own` cells.** Between the stop and the resume the lender holds the owner, `ℓ ↦ v ⋆ P̂(v)`.
      A 6.64 entry's kind `imm v` fixes the value at `ℓ` and asks the payload back in `𝒱⟦T⟧(v)`; it
      does not fix the payload's cells. A handler that writes inside the payload re-opens the frame
      over different `own` cells, and then the world's record is not `RecUpTo` the moved one. Whether
      the share can then supply `KeepsS`, or the clause must compare less, is statement 2's to decide
      [unchecked].

    `MovedRecPremises` states what the moved record meets on its own: `TW.immFrame`'s per-record
    premises (`AdmWf`, `vShape`, the witness's stratum) at the instantiated reading and lifetime, its
    witness kept. They read the reading and the lifetime only through lower bounds, which the
    instantiation lowers. So when the witness holds no frozen copy of a view and the lender has not
    changed the payload, the moved record is one a re-opening makes. The world the frame re-opens in,
    and `Tagged`'s `FrameLife` there, are statement 2's records fact (§3.7).
- **Where the index invariants come from: the lends' freshness.** [TR] 6.64's and 6.65's proofs choose
  the lend below a bound (H4, "Such an α always exists because for any lifetime, the set of lifetimes
  shorter than it is infinite"), and the `И` they unfold admits every lifetime below it. So a lend may
  be taken below any finite set: below the records' frame lifetimes and readings (`LendFresh`), and
  below the reading's values (`SubFresh`, §3.1).
  - Then every record outliving a lend was made before it and reads only lifetimes outliving it
    (`RecsOutside`), and every variable bound before a lend is read above it (`SubOutside`).
  - A record made inside a lend is shorter-lived than it, and at or below the outermost lend the only
    records are those the stack's own 6.64 lends made (`RecsInsideOwn`).
  - Runs keep the list's members.
  - `RecsOutsideArises` and `RecsInsideOwnArises` are read at the revised arising set `ArisesI`, whose
    `LendMutI` and `LendImmI` carry `LendFresh` (§1.4). At the current `LendMut`, which puts the lend
    below the callback's resource only, an `Arises.nil` record reading a short lifetime can sit below
    a later, longer lend. `RecsOutside` at that configuration is not expected to hold, and the
    revision is what excludes it. A configuration carries no reading substitution, so `SubOutside`
    has no arising-set form: it is the relation's index invariant only.
  - At the relation, `RecsOutside` and `SubOutside` are index hypotheses of `SemSI` (§5.1). An
    instantiation keeps them (`RecsOutsideInst`, `SubOutsideInst`). The own lend asks `RecsOutside`
    at the pushed stack and `SubFresh` of the pushed lend. `RelendI` asks `RecsOutside` of the list a
    consumer extends to.
- **What it does not act on: resources.** A `U` value's retained part is strictly above the outermost
  lend (`stratS`), hence at or above the cut, and `θ` fixes every such cell (`Restrat.relRU_of_inStratum`,
  at the non-strict boundary). The views are dropped and handed afresh at the instantiated reading.
  This is Restrat's own repair of `mut_not_natural`: "Freeze, then re-lend… The re-lend at resume then
  builds the cell afresh with `𝒱⟦T⟧_{δ′}`." It is why the instantiation never forms the image of a
  view's invariant (§4.3).
- **The lowering is non-strict in the `U` clause.** `Inst.life` is a `ReLend` of the stack
  (`InstReLend`), the identity included, so `[force]` reads the clause at `none`. The share's re-lend
  is strict on the ghost-ended entries (`openFS`'s `Forall₂ (· < ·)`). Its instantiation is at the
  ended part's cut, and as an instantiation of the whole stack it is the same map on lifetimes and
  readings, and, under `RecsOutside`, on records (`EmbLift`, `ShareReLendInst`, §3.5).

### 3.3 Freshness at a resume

```lean
def IdxReads (δ : LSub) (αs : List Life) (ls : List SRec) (a : Life) : Prop :=
  a ∈ αs ∨ (∃ p ∈ δ.entries, a = OrderDual.toDual p.2) ∨
    ∃ x ∈ ls, a = x.2 ∨ ∃ p ∈ x.1.δ.entries, a = OrderDual.toDual p.2

def InstFresh (R : WRes) (δ : LSub) (αs : List Life) (ls : List SRec) : Inst → Prop
  | none => True
  | some ⟨c, θ⟩ => ∀ a, a < c → R.InStratum (θ a) ∧ ∀ b, IdxReads δ αs ls b → θ a < b

def InstFreshExists : Prop :=
  ∀ αs (R : WRes) (δ : LSub) (αsR : List Life) (lsR : List SRec) (c : Life),
    cutOf αs = some c → ∃ θ : Restrat.Emb c, InstFresh R δ αsR lsR (Inst.ofEmb θ)

def freshI (c : Life) (Q : Restrat.Emb c → WProp) : WProp := fun ρ =>
  ∃ β : Life, ∀ θ : Restrat.Emb c, (∀ a, a < c → θ a < β) →
    Q θ ρ ∧ ∀ a, a < c → ρ.InStratum (θ a)
def FreshFrameI : Prop :=
  ∀ c (P : WProp) (Q : Restrat.Emb c → WProp) (ρ : WRes), (P ⋆ freshI c Q) ρ →
    freshI c (fun θ => (fun ρ₁ => P ρ₁ ∧ ∀ a, a < c → ρ₁.InStratum (θ a)) ⋆ Q θ) ρ
```

- **What freshness is, and against what.** A resume instantiates the continuation's internal lifetimes
  strictly below the resumer's resource `R`, and below every lifetime the resumer's index reads: its
  lend lifetimes, its reading's codomain, and its records' frame lifetimes and readings (`IdxReads`, a
  finite set). This is what the resume composite needs:
  - the composite stack's chain, with the moved lend lifetimes below the resumer's innermost lend;
  - the internal readings fresh relative to the resumer's reading;
  - `RecsOutside` at the composite, the resumer's records outliving every moved lend;
  - `SubOutside` at the composite, the resumer's bindings, made before the moved entries, read above
    every moved lend.
  A cell of `R` alone would not give these when a resumer's view is not in `R` (a drop flag false) or
  a resumer variable has no cell.
- **`InstFreshExists`** is arithmetic: `Restrat.Emb.shift c k` with `k` past the largest `ℕ`-value of
  the finite set, and `Restrat.Emb.shift_fresh`. It spends none of [TR] 6.108–6.112.
- **6.112 at a block (`freshI`, `FreshFrameI`), ours.** The printed `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` binds
  one lifetime. A resume binds a block, so `freshI` quantifies over the instantiations whose moved
  lifetimes lie below the bound.
  - `FreshFrameI` is 6.112's `P ⋆ Иα. Q(α) ⊨ Иα. ([α] P ⋆ Q(α))` at a block, and its planned proof is
    `fresh_frame`'s step by step: the bound `@ρ_P ⊓ β_Q`, by the printed chain 6.101, 6.99, 6.100,
    6.111.
  - It is the technique the share (statement 2) reaches for at a resume, with `InstFreshExists`
    supplying a `θ` below the bound. Neither is spent in this unit.
- **Where freshness is used: the share** (statement 2, §3.7). The `U` clause quantifies over every
  instantiation at the cut, fresh or not, as GhostEnd's quantifies over every re-lend. Freshness is the
  resume's choice, not the clause's condition.

### 3.4 The `U` clause over instantiations

```lean
def RecUpTo (x x' : SRec) : Prop :=      -- `x` as the relation reads it
  x'.1.le = x.1.le ∧ x'.1.v = x.1.v ∧ x'.1.T = x.1.T ∧ x'.1.δ = x.1.δ ∧ x'.2 = x.2 ∧
    ∀ l u, x'.1.R.get l = some (CellU.ownOf u) ↔ x.1.R.get l = some (CellU.ownOf u)
def KeepsS (ls ls' : List SRec) (ρ : WRes) : Prop :=
  ∀ x ∈ ls, Rel x.1 ρ → ∃ x' ∈ ls', RecUpTo x x'

def RelendI (δ : LSub) (σ : LStack) (P : LSub → List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz → KeepsS (ι.recs ls) ls' ρn →
      RecsOutside (ι.life αs) ls' →
      (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ─⋆
        P (ι.sub δ) (ι.life αs) ls') ρz

def KeepsSComp : Prop :=      -- the composite's list keeps the composite's views' records
  ∀ s s' σ ds αs αs' ls lsv ls₁ ls₂ (ρn ρv : WRes) (ι₁ ι₂ : Inst),
    vwSL s σ ds αs ls ρn → vwSL s' σ ds αs' lsv ρv →
    KeepsS (ι₁.recs ls) ls₁ ρn → KeepsS (ι₂.recs ls₁) ls₂ ρv → KeepsS (ι₂.recs (ι₁.recs ls)) ls₂ ρn
```

- **What changes from `RelendableS`.**
  - The re-lend `∀ αs', ReLend αs' αs` becomes `∀ ι, InstAt αs ι`.
  - `P` takes the instantiated reading. The thunk's own type `C` is read at `ι.sub δ`, as the stack's
    variables in it are read at `ι.life αs`.
  - The views are W's at every depth (`vwSL`), at the instantiated reading.
  - The list extension comes after the instantiation. It keeps the records the dropped views are
    coherent with (`KeepsS`), and `RecsOutside`.
- **Why the extension comes after.** A record added after the instantiation need not be the image of
  one before it, since `θ`'s image has gaps. So "extend, then instantiate" would not compose. With
  "instantiate, then extend", an instantiation of an instantiated value is one of the original
  (`InstComp`), and its extension one of the original's (`ExtInst`, then `Ext.trans`; `KeepsSComp`).
  At `ι = none` this is GhostEnd's clause, the views, the records' invariant and `KeepsS` apart.
- **Why the extension keeps the views' records (`KeepsS`).** `Ext` keeps a record only when it is
  relevant to the resource `Ext` is taken at (`Keeps`, through `Rel`: an `imm` cell there at the
  record's place or at a chain position of it), or longer-lived than one of that resource's cells.
  Taken at `ρz`, it does not keep the stack's own 6.64 records, which are relevant only to the
  dropped views. Without `KeepsS` the clause failed at an index a 6.64 callback holding its view
  reaches:
  - `σ = [b]`, an `imm` entry at the place `m` and lifetime `α`; `Γ = [slot : Imm 'b 1]`; `ρ` is `b`'s
    view; `ls` holds `b`'s record. The split is `ρn = ρ`, `ρz = ∅`.
  - At `ι = none` and `ls' = []`, `Ext ls [] ∅` holds vacuously and `RecsOutside αs []` trivially, and
    the handed view `vwEW … [] ρv` is satisfiable (`imm({α}, (), ∅)`).
  - But `gRLI` at `[]` needs Core's `Imm` leaf `CohE (rsOf []) m …`, which is false. So
    `CtxRelendableAtI` failed there, and `CtxRelendsAll .binder0` could not have been proved as
    defined.

  `KeepsS (ι.recs ls) ls' ρn` excludes `ls' = []` there: `b`'s record is relevant to `ρn`. It is
  `Ext`'s `Keeps` read at the dropped views. With `Ext` at `ρz`, the clause keeps every record
  relevant to the resource the thunk holds, as Core's own `U` clause does with `Ext` at the whole
  resource; `Ext`'s second clause, the records longer-lived than a cell kept exactly, stays at `ρz`.
  It asks the records up to what the relation does not read of them (`RecUpTo`): the world's
  re-opened record at a resume may hold rebuilt borrow cells in its witness (§3.2).
- **Every consumer supplies it.**
  - `[force]`: `ι = none` and `ls' = ls`, so `KeepsS ls ls ρn` holds with `x' = x`.
  - The composite (the thaw of a `U` slot inside another instantiation, `ThawInst`): `KeepsSComp`.
    `Rel` reads a record's place, value, payload type and witness's `own` cells, which neither
    `Inst.recs` nor `RecUpTo` changes. And the handed views `ρv` have `imm` cells at the places where
    `ρn` has them, the same entries and drop flags. So a record of the composite's list relevant to
    `ρn` is kept by the first extension, moved by the second instantiation, still relevant to `ρv`,
    and kept by the second extension.
  - The share (statement 2): its list holds the re-opened frames' records, which are the moved ones
    up to `RecUpTo` when the lender has not changed the payload's `own` cells (§3.2). What it owes is
    named in §3.7.
- **`RelendUI`** (`Binder.lean`) is the same with `RelendU`'s futures after the instantiation, at
  `FutQI`, and its own lend at `OwnPushI`, asked `RecsOutside` at the pushed stack and `SubFresh` as
  the `∀` clause's own lend is. It is the next unit's (§5.6).

### 3.5 `Δ`'s models at an instantiation, and what the narrowing costs

```lean
def InstModels : Prop :=
  ∀ Δ δ σ αs (ι : Inst), Δ.Models (extS δ σ αs) → Δ.Models (extS (ι.sub δ) σ (ι.life αs))
def ReLendModelsI (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) : Prop :=
  ∀ ι, InstAt αs ι → Δ.Models (extS (ι.sub δ) σ (ι.life αs))
def Q2Inst : Prop := ReLendModelsI mΔ qδ [qEnt] [kα]

def EmbLift : Prop :=
  ∀ (c c' : Life) (θ : Restrat.Emb c'), c' ≤ c → ∃ θ' : Restrat.Emb c, ∀ x, θ' x = θ x
def ShareReLendInst : Prop :=
  ∀ (αi αo : List Life) (ls : List SRec) (ci : Life) (θ : Restrat.Emb ci), cutOf αi = some ci →
    List.IsChain (· < ·) (αi ++ αo) → RecsOutside (αi ++ αo) ls →
    ∃ ι : Inst, InstAt (αi ++ αo) ι ∧ ι.life (αi ++ αo) = (Inst.ofEmb θ).life αi ++ αo ∧
      (∀ δ, ι.sub δ = (Inst.ofEmb θ).sub δ) ∧ ι.recs ls = (Inst.ofEmb θ).recs ls
```

- **`InstModels`** is `ExtSInst` (`extS (ι.sub δ) σ (ι.life αs) = ι.sub (extS δ σ αs)`, by induction on
  `σ` with `Restrat.LSub.mapN_extend` and `Emb.toNat_toDual`) followed by
  `Restrat.Emb.models_mapN_iff`. There is no condition on `Δ`'s bounds, so `BoundsStackFree` and
  `reLendModels_of_boundsStackFree` are not needed. `ReLendModelsI` is its instance at the clause's
  instantiations, and it is what the rows read.
- **`Q2Inst`** is `InstModels` at `q2_reached`'s models. At `[qEnt]`, `cutOf [kα] = some ⊤`. Every
  re-stratification below `⊤` lowers `'0 ↦ 1` and `'1 ↦ 2` together and keeps `'1 ⊏ '0`. The re-lend
  `q2_reached` exhibits (`'0 ↦ 2`, `'1 ↦ 2`) is not an instantiation, since `θ` is a function: `'1` and
  `'0` sit at different lifetimes and must land at different ones.
- **What the narrowing costs.** The `U` clause now ranges over fewer re-lends than [W₀]'s (not every
  `ReLend` extends to a strictly monotone `θ`, because `ℕ` has gaps), over views at every depth, and
  over list extensions keeping the views' records and `RecsOutside`. The clause gets weaker, so the
  introductions get easier, and the burden moves to the clause's consumers. Each consumer's
  obligation is a statement:
  - `[force]`: the identity, `ι = none`, at the index's own list and views.
  - The thaw of a `U` slot inside another instantiation: the composite (`InstComp`, with `EmbLift` to
    put the second map at the first's cut; `ExtInst` and `KeepsSComp` for the list).
  - The share's re-lend at a resume (statement 2): the resume chooses the instantiation, fresh
    (`InstFreshExists`), at the ghost-ended part's cut. As an instantiation of the continuation's
    whole stack it is one `RelendI` covers (`ShareReLendInst`). The views it hands are the real
    re-lend's, and its list is the resumer's world's records with the re-opened frames' ones;
    `RecsOutside` holds there by `InstFresh` against the resumer's records (`RecsOutsideInst` for the
    moved part), and `KeepsS` by the re-opened records (§3.4). It moves none of the resumer's
    variables (`SharedReadFixed`). What statement 2 must restate is named in §3.7.
  - `cbpv`'s own lend at `U` and the futures (next unit): in `RelendUI` they come after the
    instantiation and quantify over every lifetime there, so no image is asked of them. Their own
    cost is `FutInst` (§5.6 item 2).

### 3.6 The equivariance the relation owes

What the thaw needs of the relation at an instantiation comes in three parts. Nothing here asks
naturality under transport.

```lean
def TyEqInst : Prop :=
  ∀ (A B : VTy) (s s' : LSub) (ι : Inst), TyEq A s B s' → TyEq A (ι.sub s) B (ι.sub s')
def CohEInst : Prop :=
  ∀ αs ls (m : BoCa.Loc) (A : VTy) (s : LSub) (c : Life) (θ : Restrat.Emb c), cutOf αs = some c →
    RecsOutside αs ls → CohE (rsOf ls) m A s →
    CohE (rsOf ((Inst.ofEmb θ).recs ls)) m A ((Inst.ofEmb θ).sub s)
def RecFixed (c : Life) (x : SRec) : Prop :=
  c ≤ x.2 ∧ ∀ p ∈ x.1.δ.entries, c ≤ OrderDual.toDual p.2
def MutPayloadInst : Prop :=
  ∀ (T : VTy) (ls₀ : List SRec) (s : LSub) (b c : Life) (θ : Restrat.Emb c), CoreStable T →
    c ≤ b → (∀ x ∈ ls₀, RecFixed c x) → (∀ ls' u σ', vC true T ls' s u σ' → σ'.InStratum b) →
    (∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls₀) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
      vC true T ls₀ s u σ') ∧                                          -- the stored predicate
    ∀ ls' u σ', vC true T ls' (Inst.sub (Inst.ofEmb θ) s) u σ' → σ'.InStratum b   -- its support
def InstEquivLeaf : Prop :=
  ∀ A (b : Bool) αs ls s v ρ (c : Life) (θ : Restrat.Emb c), cutOf αs = some c →
    RecsOutside αs ls → CoreStable A → StratumLe ρ c → vCE none b A ls s v ρ →
    vCE none b A (Inst.recs (Inst.ofEmb θ) ls) (Inst.sub (Inst.ofEmb θ) s) v ρ
def ViewSlotInst : Prop :=
  ∀ σ αs s ls ls' A l e α (ρ ρv : WRes) (ι : Inst),
    innerAt σ αs l = some (e, α) → InstAt αs ι → RecsOutside αs ls → KeepsS (ι.recs ls) ls' ρ →
    vC true A ls s (.loc l) ρ → CohS σ αs s A (.loc l) ρ →
    vwEW (ι.sub s) e true (ι.life1 α) ls' ρv →
    vC true A ls' (ι.sub s) (.loc l) ρv ∧ CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv
```

- **By construction, for `U` slots.** A `U` value's clause at the instantiated index is the original
  clause at the composite instantiation:
  - `InstComp`: lift the second `Emb` to the first's cut (`EmbLift`), then `Restrat.Emb.comp`
    (`Targets/I/Binder.lean`). The records compose too: a record below the first cut lands below the
    second, and a record at or above the first is at or above the second.
  - `ExtInst`: `Ext`'s `Keeps` reads no substitution (`Rel` reads `le`, `v`, `R`, `T`), and the
    records above a cell of a fixed resource are at or above the cut, hence left alone.
  - `KeepsSComp`: the views' records, kept along the composite (§3.4).
  - `RecsOutside` at the composite is the one the consumer supplies.
- **Views, rebuilt (`ViewSlotInst`).** A slot holding a bound place's view is re-established from the
  view handed at the instantiation:
  - `TyEqInst` (by induction on `TyEq`/`CTyEq`; lifetimes are compared by `interp`, and
    `Restrat.Emb.interp_mapN` applies). At `CTyEq`'s `∀` clause the hypothesis covers the instances
    in `θ`'s image only, and an instance in a gap of `θ` is not one. It needs that a comparison of
    `interp` values is one of lattice polynomials in the bound variables, fixed by its values on `ℕ`
    [unchecked];
  - `vC_tyEq` (`Core/RelationFacts.lean`);
  - the exact lifetime with `θ` monotone;
  - at `Imm`, the slot's coherence record moved (`CohEInst`, at `InstAt` and `RecsOutside`) and in
    `ls'`: the record is relevant to the slot's `imm` cell, at its place or at a chain position of it,
    so `KeepsS` keeps it up to `RecUpTo`, which keeps what `Coh` reads. Then `ptoImmS_mono` with the
    full view implying the observable one (`vC_obs_of_full`, to be built). At `Mut` no record is read:
    the handed view's stored predicate is `𝒱⟦e.T⟧` at the instantiated reading, `TyEq` to the slot's.

  The dropped cell's stored invariant is never read.
- **Coherence (`CohEInst`).** Against a moved record by `TyEqInst`, the record's substitution moved
  with the reading. Against a record left alone by `RecsOutside`: the record reads only lifetimes at or
  above the cut, so the slot's type, `TyEq` to it, reads those positions at lifetimes `θ` fixes
  (`tyEq_fixed`, to be built).
- **Retained leaves (`InstEquivLeaf`, `MutPayloadInst`).** At a type Core reads without a thunk
  (`CoreStable`), at a resource the instantiation fixes, Core's relation holds at the instantiated
  reading and records. By induction on the type:
  - box: the reading only lowers, and the resource is above it;
  - `Imm`: `CohEInst`; `ptoImmS`'s list is the records longer-lived than the cell, which are at or
    above the cut and left alone; the payload by induction, the witness being fixed and above the cell;
  - data: immediate;
  - `Mut`: `MutPayloadInst`, both conjuncts, the crux.

  A retained `mut` cell is above the cut, `c ≤ b`. Core's `ptoMutS` (`Core/Relation.lean`) asks two
  things of it at the instantiated reading, and `MutPayloadInst` states both:
  - **The stored predicate**, `ofS Q = P ls₀` with `P = fun ls₀ => vC true T ls₀ (θ s)` and `ls₀` the
    records longer-lived than `b`. Those `RecsOutside` makes `RecFixed`, so `Inst.recs` leaves them
    alone, `θ.recs ls₀ = ls₀`, and only the reading moves. The first conjunct, the `↔` at `ls₀`, gives
    it.
  - **Its support**, `∀ ls' u σ', P ls' u σ' → σ'.InStratum b`, at every list. The `↔` at a `RecFixed`
    list does not give it. An arbitrary `ls'` can carry records whose substitutions sit in `θ`'s gap,
    and `CohE` and `TyEq` read those substitutions. A coherence that no record supplies at `s` can be
    supplied at `θ s`, which makes satisfiable, at a cell below `b`, an `Imm` leaf that was
    unsatisfiable. This is where `mut_not_natural`'s mechanism would show up at an instantiation, and
    the second conjunct states it.

  With both, `InstEquivLeaf`'s `Mut` case follows: the same cell, with `atLife (θ s) a ⊑ atLife s a ⊑ b`.
  The argument for both [unchecked]:
  - every lifetime Core's relation reads at a `CoreStable` type is a lower bound on a cell (`Imm`,
    `Mut`, `[@a]`);
  - support in `Res_b` at `s`, at every list, forces every satisfiable such bound at an internal
    reading to be dominated by one at or above the cut. That includes the lists whose records supply
    the coherence at an internal reading, so a coherence `θ` makes available at `θ s` was available
    at `s` for some list;
  - lowering the internal readings then changes no satisfiable constraint.

  The proof carries "the subterm's relation is supported" down the induction, with satisfiability
  invariant under `θ`, because no constraint is an upper bound. This is exactly `mut_not_natural`'s
  shape at an instantiation. If either conjunct fails, §7 says what follows.
- **Where it stops: `μ`, `fam`, and thunks in payloads.** W hands `μ` and `fam` to Core's relation
  whole, and Core's `U` clause reads its argument contravariantly. At an instantiated reading, a closure
  inside a `μ` value, or stored in a `Mut` payload, owes its behaviour at arguments with cells below the
  old lifetimes, which the original does not give. That is the naturality of `wp` at a moved argument,
  which Restrat leaves open (`WpNatural`). The statements without `CoreStable` are stated and **not
  derived**; they are not excluded by hypothesis:

  ```lean
  def InstEquivLeafAll : Prop := …   -- InstEquivLeaf without `CoreStable A`
  def MutPayloadInstAll : Prop := …  -- MutPayloadInst without `CoreStable T`, both conjuncts; at
                                     -- `T = U C`, the `Mut (U C)` leaf at an instantiation
  ```

  The build attempts both and reports the step each stops at. Their discharge is W reading `μ` and
  `fam` itself, so that a `U` inside is W's clause (§5.4 R1).
- **The bookkeeping the rows read**:
  - `InstReLend`: `Emb.le_self`, `Emb.strictMono`;
  - `StackJInst`: `Restrat.Emb.ltLife_mapN_iff` with `ExtSInst`;
  - `RecsOutsideInst`: a moved record and a moved lend move together; a record left alone outlives
    every moved lend, which `θ` lowers;
  - `SubOutsideInst`: `mapN` keeps the association list's order and maps every value by `θ`, which
    is strictly monotone;
  - `GuardInst` (§2.3, §2.4);
  - `ArisesInv`.

**Its relation to `FreezeBinderLife`.** `Targets.FreezeBinderLife` states the binder's lifetime half as
forward transport along `Restrat.Emb`: the index, the resource (`θ.relRU`), the records (witness
included, `srecRestrat`) and the predicates together. W asks something different:
- it acts at resources the instantiation fixes, plus views rebuilt;
- it moves only the records below the cut, and keeps their witnesses.

Transport does not imply it, because the views are rebuilt rather than transported. `NotVCNaturalCore`
(§4.3), if proved, refutes `FreezeBinderLife` at `coreW` as Targets states it. That is a fact about
that statement and evidence about the form T3's lifetime half should take; it is not an obstruction,
and it decides nothing for OQ-8 until DESIGN §11 passes. The form here is the one the ghost-end re-lend
realises. This bears on the target, not on the probe's statements.

### 3.7 The share (statement 2's, recorded)

- **The same Q2 meets GhostEnd's `OpenS`.** `openFS` re-lends the ghost-ended entries
  (`∀ αi', Forall₂ (· < ·) αi' αi → …`) with `δ` fixed. A stop inside `Λ'1 ⊏ '0` within a lend of `'0`
  that ghost-ends `'0` owes its continuation at a re-lend breaking `'1 ⊏ '0` [unchecked].
- **The fix.** The share's re-lend becomes an instantiation at the ghost-ended part's cut: strict on
  the ended entries, fixing the kept part (which is above that cut), with W's views (`vwSL`) and the
  records below that cut moved. The resume picks it fresh (`InstFreshExists`, under `FreshFrameI`'s
  bound), and it is one `RelendI` covers (`ShareReLendInst`).
- **The resumer's variables are fixed.** The resumer reads the variables bound before the handler at
  its own reading `δ`. The continuation's reading binds them too, before the ended entries were
  pushed, so `SubOutside` reads them above the ended part's outermost lend, at or above its cut, and
  the share's instantiation fixes them (`SharedReadFixed`). So the continuation's answer type, read
  at `θ ∘ δ`, reads a shared variable at the resumer's lifetime, and an answer given there is the
  answer owed. Without `SubOutside` this fails (§3.1), and the share's rows would owe an answer at a
  weaker lower bound than the one they are given.
- **The records at the resume.** The ghost end ends the ended entries' 6.64 frames, and the re-lend
  re-opens them at the instantiated reading and lifetimes. By `RecsInsideOwn`, the records below the
  ended part's cut are exactly those frames' lineages. Statement 2's records fact, the analog of
  `TabResume`, is that the resumed world is a tagged `TW` world at a list `ls'` that meets what the
  clause asks of the list the share hands (§3.4):
  - `Ext (ι.recs ls) ls' ρz`: the records the instantiation leaves alone that the retained part reads
    are in the world unchanged;
  - `KeepsS (ι.recs ls) ls' ρn`: for every record relevant to the dropped views, the re-opened one
    up to `RecUpTo`;
  - `RecsOutside` at the composite stack, by `InstFresh`.

  Its parts:
  - **The re-opened frames' premises.** A moved record meets `TW.immFrame`'s per-record premises at
    the instantiated reading and lifetime with its witness kept (`MovedRecPremises`). When the witness
    holds no frozen copy of a view and the lender has not changed the payload, the kept witness is the
    re-opened one.
  - **A witness holding a frozen copy of a view** (§3.2; §5.4 R2 is one such shape). The re-opened
    witness holds the copy rebuilt. `TW.immFrame` and `Tagged` are met by the rebuilt record, and
    `RecUpTo` relates it to the moved one.
  - **A payload whose `own` cells the lender changed** between the stop and the resume. Then the
    re-opened record is not `RecUpTo` the moved one, and the share cannot supply `KeepsS` as stated.
    Statement 2 decides whether such a resume reaches a captured `U` value whose views are coherent
    with that record, or the clause compares less [unchecked].

  The fact is written with statement 2's resume composite (the world, its frames and its list, built
  by the re-lend's lends), which this unit does not construct.
- **`TabResume`'s analog** is `PVLResume` for the views, the table at the fresh instantiation, and the
  records fact above.
- Statement 2 restates `OpenS` and `OpenSF` this way before its rows. Nothing here builds it.

---

## 4. The known risk: `mut_not_natural` (item 3)

### 4.1 The witness and what it refutes

`Restrat.MutCounterexample.mut_not_natural`:
- `e = Emb.shift ⊤ 1`;
- `T = Mut 'a (Imm 'b 1)`;
- `δ = ['a ↦ 3, 'b ↦ 1]`;
- `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)`.

`𝒱⟦T⟧_δ(ℓ)(ρ₀)` holds, and `𝒱⟦T⟧_{e∘δ}(ℓ)(e·ρ₀)` fails. It refutes naturality of the paper's `𝒱⟦·⟧`
under the transport `e·` of a resource whose `mut` cell lies below the cut, over all resources. It says
nothing about a resource the map fixes, or a view rebuilt rather than transported. DESIGN §10 planned
this check as statement 7; this unit brings it forward.

### 4.2 Does the witness arise?

**At Core σ=[] (`Targets.NotVDenNaturalArises`).** It asks whether Restrat's `ρ₀`, which stores the
paper's `𝒱⟦Imm 'b 1⟧_δ` (`MutCounterexample.Q`), is a part of a tagged `TW` world. Unchecked; the build
proves or refutes it.

**What each outcome says about arising.** `TW.mutFold` takes any stored predicate, with no typing
premise (`Core/World.lean`). So a proof shows only that `ρ₀` is a part of some `TW` world: a world
`TW`'s constructors build, not one a run of a program produces. It is not arising in DESIGN §11's
sense, and it cannot carry a refutation. Only the negative outcome is informative: a `ρ₀` that is a
part of no tagged `TW` world is a part of no world that arises, since every world at Core's nil index
is one. The reachability question is `InternalPayloadArises`'s below, or `NotVCNaturalCore`'s with
the program and its run exhibited (DESIGN §11). The `TW` history, constructor by constructor:
1. `TW.empty`.
2. `TW.alloc`: `ℓ′ ↦ own(())`.
3. `TW.immFrame` at `ℓ′`: `T = 1`, `α = L 1`, `R = ∅`. `AdmWf 1 δ` holds, since `1` has no free
   variable. `vShape 1 δ () ∅` holds, and `ds = []`. The world becomes `ℓ′ ↦ imm({L 1}, (), ∅)`, with
   the record `r′ = ⟨ℓ′, (), ∅, 1, δ⟩` in `ps` and `rs`.
4. `TW.alloc`: `ℓ ↦ own(loc ℓ′)`, at a location the lowering leaves free.
5. `TW.mutFold` at `ℓ`, the payload `ρ = ℓ′ ↦ imm({L 1}, (), ∅)`, `b = L 2`, `P = MutCounterexample.Q`,
   `hw = MutCounterexample.hw`. `mutFold` asks no typing premise. The world is `ρ₀` exactly.

Then `Tagged ρ₀ [r′] [(r′, L 1)]`:
- `FrameLife`'s first clause: `ag(ρ₀)`'s `imm` cell at `ℓ′` has lifetime set `{L 1}`;
- its second clause is vacuous, since `r′.R = ∅` has no lineage location.

Take `fρ = ρ₀`, `ρf = ∅`. If the history goes through, the report records that `ρ₀` is a part of a
`TW` world and no more. If a premise fails (`Tagged` reading `ag` through the `mut` witness is the
step to watch), the report says which, and whether every history fails there. A `ρ₀` that is a part of
no `TW` world does not arise at Core's world, as the README suspected, and it bears on nothing.

The same history with step 5's `P` the Core relation `𝒱⟦Imm 'b 1⟧` at `(r′'s list, δ)` gives the world
`NotVCNaturalCore` (§4.3) asks for. Restrat's `Q` is the paper's relation, which Core's `Imm` leaf does
not equal: Core's asks `CohE`.

**At W, both lends on the stack (`InternalPayloadArises`).**

```lean
def InternalPayloadArises : Prop :=
  ∃ (c : Cfg) (x b : LEnt) (u : Val) (δ : LSub) (ψ ψb : CellU BoCa.Loc Val) (ρf' : WRes),
    ArisesI c ∧ c.σ = [x, b] ∧ c.αs = [lifeN 2, lifeN 1] ∧ x.k = .mut ∧ b.k = .imm u ∧
    x.T = .imm (.var b.x) .unit ∧ c.ρ.get x.l = some ψ ∧
    vwEW (extS δ c.σ c.αs) x true (lifeN 2) c.ls (ResU.single x.l ψ) ∧
    ψ.wit.get b.l = some ψb ∧ ψb.kind = Kind.imm ∧ ψb.at = lifeN 1 ∧
    ArisesVI (c.at ρf' (ResU.single x.l ψ)) (.loc x.l) (viewTy x)
```

It pins the witness's shape: the lifetimes `[2, 1]`; `x`'s cell storing `𝒱⟦Imm 'b 1⟧` at the stack's
reading, which reads `'b` at `b`'s lifetime through `extS`; `b`'s `imm` cell at `1` inside `x`'s
witness; and `x`'s place a value of the revised arising set at `Mut 'x (Imm 'b 1)`. The `ArisesI` path:
1. `ArisesI.nil` at a world holding `ℓ′ ↦ own(())`.
2. `ArisesI.lendImm` at `ℓ′`: entry `b`, kind `imm ()`, payload `1`, lifetime `L 1`, the record added.
3. `ArisesI.run` of `alloc i`, where `i`'s value is `b`'s view (`ArisesVI.view` at `Imm 'b 1`), ending
   with `ℓ ↦ own(loc ℓ′) ● ℓ′ ↦ imm({L 1})`.
4. `ArisesI.lendMut` at `ℓ`: entry `x`, payload `Imm 'b 1`, lifetime `L 2`, below `b`'s record's frame
   lifetime and readings (`LendMutI`'s `LendFresh`).
5. `ArisesVI.view` at `x`'s lend: `loc ℓ` at `viewTy x`.

The cell is `vwE (extS δ σ αs) x true (L 2) ls`: Core's `𝒱⟦Imm 'b 1⟧` at the stack's reading, which holds
at `ℓ′ ↦ imm({L 1})` with `b`'s record (`CohE`). The closed program is
`withbor1 (alloc ()) (Λ'b. λi. withbor2 (alloc i) (Λ'x. λm. …))` under `ProbeRules`.

This is the refuting direction's set, and its under-approximation is not established (DESIGN §11).
The path is evidence that the shape is reachable. It refutes nothing, and none of this unit's
conclusions rests on it.

### 4.3 Does it apply to an order-preserving instantiation of internal lifetimes?

**No, by construction, and the build checks the instance (`MutWitnessThaws`).**

```lean
abbrev mwX : LEnt := ⟨0, 0, .imm (.var 1) .unit, .mut, fun _ => true⟩
abbrev mwB : LEnt := ⟨1, 1, .unit, .imm .unit, fun _ => true⟩
abbrev mwσ : LStack := [mwX, mwB]
abbrev mwαs : List Life := [lifeN 2, lifeN 1]
abbrev mwTy : VTy := .mut (.var 0) (.imm (.var 1) .unit)
abbrev mwι : Inst := Inst.ofEmb (Restrat.Emb.shift ⊤ 1)

def MutWitnessThaws : Prop :=
  InstAt mwαs mwι ∧
  ∀ δ ls ls' (ρ ρv : WRes), RecsOutside mwαs ls → KeepsS (mwι.recs ls) ls' ρ →
    vC true mwTy ls (extS δ mwσ mwαs) (.loc mwX.l) ρ →
    CohS mwσ mwαs (extS δ mwσ mwαs) mwTy (.loc mwX.l) ρ →
    vwEW (mwι.sub (extS δ mwσ mwαs)) mwX true (mwι.life1 (lifeN 2)) ls' ρv →
    vC true mwTy ls' (mwι.sub (extS δ mwσ mwαs)) (.loc mwX.l) ρv ∧
      CohS mwσ (mwι.life mwαs) (mwι.sub (extS δ mwσ mwαs)) mwTy (.loc mwX.l) ρv

def MutWitnessThawsInhabited : Prop :=
  ∃ (c : Cfg) δ (ψ ψb : CellU BoCa.Loc Val) ls' (ρv : WRes),
    ArisesI c ∧ c.σ = mwσ ∧ c.αs = mwαs ∧ c.ρ.get mwX.l = some ψ ∧
    ψ.wit.get mwB.l = some ψb ∧ ψb.kind = Kind.imm ∧ ψb.at = lifeN 1 ∧
    RecsOutside mwαs c.ls ∧ KeepsS (mwι.recs c.ls) ls' (ResU.single mwX.l ψ) ∧
    vC true mwTy c.ls (extS δ mwσ mwαs) (.loc mwX.l) (ResU.single mwX.l ψ) ∧
    CohS mwσ mwαs (extS δ mwσ mwαs) mwTy (.loc mwX.l) (ResU.single mwX.l ψ) ∧
    vwEW (mwι.sub (extS δ mwσ mwαs)) mwX true (mwι.life1 (lifeN 2)) ls' ρv
```

- At the stack `[x, b]` at `[L 2, L 1]`, `cutOf = some ⊤`. So `Restrat.Emb.shift ⊤ 1`, the witness's own
  `e`, is an instantiation of that stack (`MutWitnessThaws`'s first conjunct).
- The slot `m : Mut 'x (Imm 'b 1)` holds `x`'s view. Under `RelendI` that view is in the dropped part
  `ρn`: it is at a bound place, at its entry's internal lifetime, and `ρz` is above the outermost lend.
- At `e`, the view handed is `vwEW (e ∘ s) x true (e (L 2)) ls'`: a cell built afresh with
  `𝒱⟦Imm 'b 1⟧` at the instantiated reading.
- `ViewSlotInst` at these values re-establishes `m` from it, by `TyEq` and the exact lifetime; that is
  `MutWitnessThaws`'s second conjunct. At `Mut` no record is read, so its `KeepsS` is vacuous here
  (the slot's cell is `mut`, and `Rel` asks an `imm` cell).
- **Its hypotheses are met (`MutWitnessThawsInhabited`).** A universal implication whose hypotheses
  could not be met would hold vacuously and decide nothing. `MutWitnessThawsInhabited` meets them at a
  configuration of `ArisesI` with `InternalPayloadArises`'s shape at `mwσ`:
  - the list is the configuration's, `ls = c.ls`, holding `b`'s record at `L 1`;
  - the slot's resource is `x`'s cell there, at `L 2`, its witness holding `b`'s `imm` cell at `L 1`;
  - `ls' = mwι.recs c.ls`, holding `b`'s record moved to `L 2`;
  - `ρv` is a cell at `L 3` storing `𝒱⟦Imm 'b 1⟧` at the instantiated reading, over an `imm` cell at
    `L 2` coherent with the moved record.

  The path is §4.2's at `x = mwX`, `b = mwB`. Like that path, it is evidence of reachability in the
  refuting direction's set, used here only to show `MutWitnessThaws` not vacuous.
- The image of the old invariant, the thing `mut_not_natural` is about, is never formed.

**The retained part never meets it.**
- A `U` value's retained cells are strictly above the outermost lend, hence at or above the cut, and `θ`
  fixes them (`Restrat.relRU_of_inStratum`).
- A `mut` cell there has a supported payload, and re-reading that payload at the instantiated reading
  is `MutPayloadInst`: the witness's question without the move. Both of its conjuncts are asked: the
  stored predicate at the records longer-lived than the cell, and its support at every list, where
  records in `θ`'s gap can supply a coherence the original reading lacked (§3.6).
- If the witness were retained, its cell at `2` and its payload's `1` would both be above the cut,
  since the outermost lend would be at or below `3`. The instantiation would fix both.

**Transport, beside (`NotVCNaturalCore`, `NotVCNaturalCoreRefutes`).**

```lean
def NotVCNaturalCore : Prop :=
  ∃ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec) (T : VTy) (δ : LSub) (v : Val),
    (Targets.coreW).Fam fρ ps (ls, ()) ∧ ResU.CompS ρf ρ fρ ∧ vC true T ls δ v ρ ∧
    ¬ vC true T (ls.map (Targets.srecRestrat (Restrat.Emb.shift ⊤ 1)))
      (Restrat.LSub.mapN (Restrat.Emb.shift ⊤ 1).toNat δ) v ((Restrat.Emb.shift ⊤ 1).relRU ρ)
def NotVCNaturalCoreRefutes : Prop :=
  NotVCNaturalCore → ∀ a : Targets.StkAct Targets.coreW, ¬ Targets.FreezeBinderLife Targets.coreW a
```

- One `Prop` ties it together: the resource is a part of a tagged `TW` world (`coreW.Fam`), Core's
  relation holds there, and it fails once the resource, the reading and the records are moved as
  `FreezeBinderLife`'s `val` clause moves them. `NotVCNaturalCoreRefutes` is that clause's negation at
  `coreW`, for every action on `coreW`'s stacks.
- The witness is `mut_not_natural`'s at Core's `vC`, its world §4.2's history with Core's stored
  predicate. The inner `Imm` leaf's `CohE` needs `r′` in the list, and the gap argument is unchanged.
- **What it decides.** Proved, it refutes `FreezeBinderLife` at `coreW` as Targets states it: a fact
  about that statement, since the statement is guarded by `Fam` and the configuration meets that
  guard. It is evidence, not an obstruction, against OQ-8 option 1 (naturality). It decides nothing
  for option 1 until DESIGN §11 passes: the value arising at that world, the program and its run
  exhibited. That check is not written here.
- It bears on no placement of the probe.

### 4.4 What each outcome means

The second column reads the view slot from `ViewSlotInst` (with `MutWitnessThaws` and
`MutWitnessThawsInhabited` at the witness) and the retained part from `InstEquivLeaf`, whose `Mut`
case needs both conjuncts of `MutPayloadInst`, the stored predicate and its support.

| `NotVDenNaturalArises` | the view slot; the retained part (`InstEquivLeaf`) | reading |
|---|---|---|
| proved | both proved | `ρ₀` is a part of a `TW` world. `mutFold`'s predicate is unconstrained, so that is not arising in DESIGN §11's sense, and it carries no refutation. D1's instantiation is unaffected: the view cell is rebuilt, and a retained one is fixed. `NotVCNaturalCore`, if proved, refutes `FreezeBinderLife` as stated. The reachability question is `InternalPayloadArises`'s at W; for option 1 it is DESIGN §11's full check of `NotVCNaturalCore`'s value at its world, the program and its run exhibited, and only that decides option 1. |
| either | `InstEquivLeaf` not derived at `Mut`: a conjunct of `MutPayloadInst` refuted | Build the refuting `T`, `s`, `b`, `c` (for the support conjunct, the list `ls'` too) and run DESIGN §11's arising check on a retained cell with such a payload. If it arises, a retained `Mut` leaf is not stable under instantiation. D1's lifetime half then needs the retained part re-lent too, not fixed, which is D3's carried-lend shape (§8). If it does not arise, it is a fact about `MutPayloadInst`'s statement, and the guard needs the conjunct that excludes it. |
| refuted (`ρ₀` is a part of no `TW` world) | both proved | `ρ₀` does not arise at Core's world. `mut_not_natural` is a fact about Restrat's statement only, as the README suspected, and nothing follows for D1 or option 1. |

---

## 5. The `U` introductions retried (item 4)

### 5.1 The revised W

In `BinderW.lean`, under the suffix `I` beside W₀ (header):

```lean
mutual
def vRLI (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLI p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendI δ σ (fun δ' αs' ls' => cRLI p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  …                                   -- ⊗, ⊕, !, [@a], Ref as in W₀, at `vRLI`
  | σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.mut a T) v ρ
  | σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.imm a T) v ρ
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
def cRLI (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  …                                   -- F, F_Σ, &, ⊤, ν as in W₀, at `cRLI`, `effRetI`
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRLI p σ' δ A αs' ls' v ─⋆
            guardPV (extS δ σ' αs') σ' αs' ls' (cRLI p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ' αs') σ' αs' ls'
            (cRLI p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPushI δ (.all x c C) ρ (σ', αs') en α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (en :: σ') (α :: αs')) (en :: σ') (α :: αs') ls'
            (cRLI p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
end

def SemSI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLI p σ δ αs ls Γ γ ρ →
    cRLI p σ δ (jdgCty j) αs ls (substAll γ e) ρ
```

The block stays one `mutual` definition, structural on the type, and elaborates. The two new leaf
cases come before the default. `OwnOKI`, `OwnPushI` and `FutOKI` are as in §2.1; `LendMutI` and
`LendImmI` add `LendFresh c.ls α` at the pushed lifetime. The stop's share (`F_Σ`) is W₀'s; statement
2 restates it (§3.7). When the revision lands, the `I` definitions replace W₀'s, and `DeepAt`, `ExAt`,
`guardPV`, `PlaceViewsL`, `CohS`, `vwSL`, `RecsOutside`, `SubOutside`, `SubFresh`, `KeepsS` and
`RelendI` move from `Binder.lean` to `World.lean` and `Relation.lean`, and `LendFresh` to
`Arising.lean`.

### 5.2 The statements

```lean
def CtxRelendableAtI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ δ σ αs ls γ ρ, StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → RecsOutside αs ls →
    SubOutside σ αs δ → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLI p σ δ αs ls Γ γ ρ → RelendI δ σ (fun δ' αs' ls' => gRLI p σ δ' αs' ls' Γ γ) αs ls ρ

def ThawInst (p : Placement) : Prop :=
  ∀ σ δ C αs ls f ρ, StackOK σ αs → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLI p σ δ (.thunk C) αs ls f ρ →
    RelendI δ σ (fun δ' αs' ls' => vRLI p σ δ' (.thunk C) αs' ls' f) αs ls ρ

-- the target: statement 0's four rows at `SemSI` (`ThunkFRowI` is `ThunkFRow` at `SemSI`, …)
def ThunkFRowI (p : Placement) : Prop :=
  ∀ Δ Γ M A, SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
def ThunkVRowI (p : Placement) : Prop := …       -- `ThunkVRow` at `SemSI`
def BangThunkFRowI (p : Placement) : Prop := …   -- `BangThunkFRow` at `SemSI`
def BangThunkVRowI (p : Placement) : Prop := …   -- `BangThunkVRow` at `SemSI`
def CtxRelendsAll (p : Placement) : Prop := ∀ Δ Γ, CtxRelendableAtI p Δ Γ
def Statement0UFull (p : Placement) : Prop :=
  ThawInst p ∧ CtxRelendsAll p ∧ ThunkFRowI p ∧ ThunkVRowI p ∧ BangThunkFRowI p ∧ BangThunkVRowI p

-- the partial result
def CtxRelendsThawFree (p : Placement) : Prop := ∀ Δ Γ, CtxThawFree Γ → CtxRelendableAtI p Δ Γ
def ThunkFRowTF (p : Placement) : Prop :=
  ∀ Δ Γ M A, CtxThawFree Γ → SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
def ThunkVRowTF (p : Placement) : Prop := …      -- `thunkV`, with `C.isRet = false`, `OwnHyg`
def BangThunkFRowTF (p : Placement) : Prop := …  -- `bangThunkF`, with `Persistent Γ`
def BangThunkVRowTF (p : Placement) : Prop := …  -- `bangThunkV`, with `Persistent Γ`, `OwnHyg`
def Statement0UThawFree (p : Placement) : Prop :=
  ThawInst p ∧ CtxRelendsThawFree p ∧ ThunkFRowTF p ∧ ThunkVRowTF p ∧ BangThunkFRowTF p ∧
    BangThunkVRowTF p

-- its scope
abbrev listTy : VTy := .mu (.sum .unit (.tvar 0))
abbrev scopeC : CTy :=
  .all 0 .top (.arr (.mut (.var 0) .unit)
    (.arr listTy (.ret (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy))))))
abbrev scopeΓ : Ctx VTy := [⟨listTy, true⟩, ⟨.mut (.var 0) .unit, true⟩, ⟨.unit, false⟩]
def ThawFreeScope : Prop :=
  CDerives LifeCtx.empty []
      (.val (.lam (.val (.lam (.val (.lam (.val (.lam (.pair (.var 2) (.var 1)))))))))) (.comp scopeC) ∧
    CDerives kΔ scopeΓ (.val (.lam (.pair (.var 2) (.var 1))))
      (.val (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy)))) ∧
    OwnPushI kδ scopeC PMap.empty ([], []) qEnt kα ∧ ¬ CtxThawFree scopeΓ
```

- **The target is statement 0's own rows** (`ThunkFRow`, `ThunkVRow`, `BangThunkFRow`,
  `BangThunkVRow`, `Statement0.lean`), read at the revised W: `ThunkFRowI` … are the same statements
  at `SemSI`, and they elaborate in `BinderW.lean`. With the thaw at every context,
  `Statement0UFull .binder0` is item 4's success.
- **The partial result** adds `CtxThawFree Γ`: every live slot's type is `ThawFree`. That excludes `μ`
  and `fam` slots, and, through `CoreStable`, thunks inside `Mut` and `Imm` payloads. Those are exactly
  the slots where the instantiation meets Core's contravariant `U` clause. The hypothesis is a
  guarantee gap of `BindersLow`'s kind: FL at W proved under it says nothing about a thunk over such a
  slot inside a lend.
- **`ThawFreeScope`**: the gap is real. The closed term `Λ'0. λm. λxs. thunk (return (m, xs))` is
  derived; read at `[]`, `binder0`'s `∀` clause pushes the own lend of `'0` (as `k_reached` reads it),
  and the `U` introduction then sits at `scopeΓ`, inside the lend, with a live `μ` slot beside the
  lend's view. This is reached by typing, not by a run, which is the evidence a scope statement needs:
  FL quantifies over derivations. `CtxThawFree` stays a named, scoped hypothesis. Its non-vacuity at
  the programs is to be checked: `genSelf`'s state and `reconB′`'s payloads are `Flag` [unchecked].
- **The rows conclude at `SemSI`, not `SemSR`.** `ReLendModels` is gone from the index: Q2 is met by
  the instantiation, not assumed.

### 5.3 The proof plan

**`thunkF_U_binder0I`** (then `ThunkFRowI .binder0`, and its `TF` form), following
`thunkF_U_binder0`, step by step:
1. Unfold `vRLI` at `U` at `binder0`: `guardPV`, then `RelendI`. The guard's hypotheses `TabAtS` and
   `PlaceViewsL` at `ρ` are the index's.
2. `CtxRelendableAtI` at the row's context gives the split `(ds, ρz, ρn)` and the thaw `H`.
3. For `ι` (`InstAt αs ι`), `ls'` (`Ext (ι.recs ls) ls' ρz`, `KeepsS (ι.recs ls) ls' ρn`,
   `RecsOutside (ι.life αs) ls'`), and views `ρv` at the instantiated stack (`vwSL`) with
   `τ = ρz ● ρv`: call the premise `SemSI` at `(ι.sub δ, σ, ι.life αs, ls', () :: γ, τ)`. Its
   hypotheses:
   - `BindersLow` and `Scoped`: the row's, unchanged;
   - `StackOK`: `InstReLend`;
   - `StackJ`: `StackJInst`;
   - `SubDom`: `mapN` keeps keys (`Restrat.LSub.find?_mapN`);
   - `Models`: `InstModels`;
   - `RecsOutside`: the clause's, on `ls'`;
   - `SubOutside`: the index's, by `SubOutsideInst`;
   - `TabAtS` and `PlaceViewsL`: `GuardInst`;
   - the context: `H`, at the same `ι`, `ls'` and `ρv`. `H`'s clause asks `KeepsS` at its own split's
     views, which is the row's split, so the row's `KeepsS` is passed on as it stands.
4. Close with `wpTS_step` at the `β`-step, as now.

`thunkV` is the same, at `forceE_of_not_ret`. The `!` rows are the same at `ρ = ∅`, by
`gSepRL_persistent`.

**`CtxRelendsAll .binder0`, the thaw.**
1. **Split.** `ρn` is every top-level non-`own` cell of the context's resource at a bound place.
   `PlaceViewsL` makes each one a W view of its entry, with its nested cells (`vwSL` at `ds`: true where
   the context holds the entry's view, shadowing as `vwS`). `ρz` is the rest.
   - `stratS αs ρz` holds: `TabAtS`'s second conjunct for cells off the stack's places; `own` cells are
     `⊤`.
2. **Per slot**, by W's clause on the slot's type:
   - `U`: by construction, at the composite (`InstComp`, `ExtInst`, `KeepsSComp`).
   - `⊗`, `⊕`, `!`, `Ref`: componentwise.
   - `[@a]`: the box's reading and the views' exact lifetimes move together under `θ`, which is strictly
     monotone.
   - `Mut`/`Imm` at a bound place: `ViewSlotInst`, fed by `CohS` (type, exact lifetime), the index's
     `RecsOutside`, the clause's `InstAt`, and `KeepsS` at the slot's cell. That comes from the clause's
     `KeepsS (ι.recs ls) ls' ρn`: the slot's cell is a part of `ρn`, and an `imm` cell of a part makes
     `ρn`'s cell at that place `imm`, so a record relevant to the slot's cell is relevant to `ρn`. For
     `Imm`, the full payload comes from `PlaceViewsL` at the composite cell, since the slot reads only
     the observable one.
   - `Mut`/`Imm` off the stack's places, and data: `InstEquivLeaf` at the retained resource, with
     `CohEInst` inside, at the list `ι.recs ls`; then Core's relation along `Ext (ι.recs ls) ls' ρz`
     to `ls'`, the records a retained `imm` cell is coherent with being relevant to `ρz`. `CohS` is
     vacuous there, and the place stays unbound, since `ι` does not touch `σ`.
   - **`μ`, `fam`, and the leaves `CoreStable` excludes: `InstEquivLeafAll`.** This is the step where
     the target and the partial result part. If `InstEquivLeafAll` is not derived, the thaw is proved
     at `CtxThawFree` contexts only (`CtxRelendsThawFree`), and the report names the type and the
     step.
3. **Across slots** (`relendI_sep`, the stacked `relendable_sep`, to be built):
   - at most one slot holds a `mut` view (`dropC_disj`);
   - an `imm` view held by several slots is one composite cell, dropped once, and the fresh view is
     split back by [TR] 6.116 (I-dup) and 6.43, since `imm(s) ● imm(s) = imm(s)`.

**`ThawInst .binder0`**: `RelendI` at the composite instantiation (`InstComp`, `ExtInst`,
`KeepsSComp`), as `thawRelend` and `relendableS_thunkA` do at a re-lend. The instantiated value's split
is `ρz` and the handed views `ρv`, and the views' records it is asked to keep are the ones the first
extension kept.

### 5.4 What is not covered, and how it would be

- **R1. `μ` and `fam` slots, and thunks in payloads** (`InstEquivLeafAll`, `MutPayloadInstAll`).
  - Route: W reads `μ` (least fixed point over W's own clauses, as `vCE` does over Core's) and `fam`
    itself. A `U` inside is then W's clause, instantiated by construction, and a view inside is
    `CohS`-checked.
  - A cheaper first step: admit `μ`/`fam` whose body is `CoreStable`. `InstEquivLeaf` then needs only
    `vC_mu_ind` at a fixed resource.
  - A thunk stored in a `Mut` payload stays Core's either way, since 6.65's `P̂` is `𝒱⟦T⟧` at Core's
    relation. `MutPayloadInstAll` at `U C` is the question there.
- **R2. An `imm` reborrow's entry (`withload`) with the outer view still held.** `vwS`'s shadowing
  hands only the innermost entry's view at a place, while an `imm` copy of the outer one is duplicable.
  `PlaceViewsL` admits the outer view frozen under the frame's `imm` cell, the only place it can be
  while the inner entry is open. Statement 2's `SpanLoadRow` "entry-kind finding" decides whether
  `withload` pushes an entry. Neither program holds an outer copy across a `withload`.
- **R3. The share.** §3.7.

### 5.5 Statement 0's other facts at the revised W

| fact | at W | how |
|---|---|---|
| `statement0Shared` | re-proved | `FutPart` with `placesFree` (a part holds fewer cells, at any depth); `NilSoundRet` with `CohS`, `PlaceViewsL`, `RecsOutside` and `SubOutside` vacuous at `[]`; the rest unchanged |
| `ForceRow` | re-proved | `binder0`: `RelendI` at `none` and `ls' = ls`, the split's views handed back, the index's `RecsOutside`, `KeepsS ls ls ρn` with `x' = x`; `cbpv`/`binder` unchanged |
| `ThawRelend` | `binder0`: `ThawInst`; others unchanged | composition |
| `CallbackExtMut`/`Imm` | re-proved with hypotheses added | `e.T = T` (the argument's `CohS`), `placeFree` (`OwnOKI`), `PlaceViewsL` at `e :: σ` beside `TabAtS` (the lend's view, exact, its nested cells the lender's), `RecsOutside (α :: αs) ls` (the lend fresh below the records), `SubFresh δ α` (the lend fresh below the reading, [TR] 6.65's H4): each a property of the borrow constant's real lend |
| `MonoV`, `MonoG`, `MonoOwnG` at `cbpv`/`binder` | re-proved | the leaf case: `CohS` along a future, since `placesFree` keeps the value's place unbound and existing places' entries and lifetimes are unchanged; the guard's views at a future (`PVLFut`); `ownPush_futStep` with `placeFree` |
| `MonoV`, `MonoG`, `MonoOwnG` at `binder0` | not derived, as before | the `U` clause still ranges over the stack itself; `MonoC binder0`. Along `Ext` alone, a `U` value's `KeepsS` asks records of the original list that `Ext ls ls' ρ` keeps when they are relevant to the views `ρ` holds, which is where the argument would look [unchecked] |
| `thunkFRow_binder0_at` … (at `SemSR`) | superseded | by `ThunkFRowI .binder0` at `SemSI` (target) or `ThunkFRowTF .binder0` (partial) |
| `k_slot`, `k_gRL`, `k_index`, `k_reached`, `k_thunk_not_vRL`, `not_ctxRelendable*` | statements about [W₀] | restated by `KSlotNotW`, `KNotViewAt` (§2.7); the relation-independent `k` facts kept; the [W₀] outcome stays recorded in DESIGN §15.6 |

### 5.6 Statement 0 and OQ-8, reconsidered

**What this unit can decide, and what it cannot.**
- **If `Statement0UFull .binder0` is proved, the two needs DESIGN §15.3 named as shared are met** at
  every context. They were the context's thaw and the models at a re-lend. They are met by changes to
  our definitions: PlaceViews in the guard, the views, the leaves and the own lend; the records' and
  the readings' invariants; the views' records kept by the clause's extension; and the re-lend as an
  instantiation.
  - Under the stop rule's shared-reason clause (DESIGN §12.3) they were findings about our definitions.
  - Statement 0 at `binder0` still stops at `MonoV`/`MonoG`/`MonoOwnG`, not derived, for `binder0`'s own
    reason. So `binder0` does not proceed to statement 1.
- **If only `Statement0UThawFree .binder0` is proved**, the result is partial: the needs are met at
  `CtxThawFree` contexts, guarantee gap R1 is open, and `ThawFreeScope` shows that typing reaches
  contexts outside it. Under the top rule (the borrow guarantees for every program) a result with a
  guarantee gap is partial, and no placement decision rests on it.
- **OQ-8 stays undecided.** W is neither decided nor provisional. The comparison now rests on each
  placement's own needs.
- **What `cbpv` and `binder` still owe in the `U` rows** (the next unit; each is a named statement
  there, none built here):
  1. **`RelendUI` in place of `RelendU`.** The same instantiation, then the futures.
  2. **`MonoV` along a future at `RelendUI`, which needs `FutInst`:** an instantiation of a future is a
     future of an instantiation. [unchecked] At a future that inserts outside the outermost lend
     (depth `|σ|`), the new cut is higher. An instantiation there may move values the original's cut
     fixed. The candidate fix is a `FutOKI` field putting the inserted lifetimes below every external
     lifetime in play, the reading's values bound before the insertion depth among them (the lend's
     choice below a finite set, as `LendFresh`, `SubFresh` and `InstFresh` take it). Then no reading or
     record lies in the band between the old cut and the new, `RecsOutside` holds at the new stack, and
     the new instantiation truncated at the old cut is one of the original (`Restrat.Emb` truncated
     stays strictly monotone and lowering). The clauses that quantify over an `Ext`-extension
     (`binder`'s `⊸` and `∀`, `RelendUI`) ask `RecsOutside` and `KeepsS` of it, as `RelendI` does.
     - A future's inserted variables are new to the reading (`FutOK.vars_sub`), so `SubOutside` says
       nothing of them (§3.1), and a variable bound before an insertion is not marked as bound before
       it. The field must therefore state the inserted lifetimes' freshness against the reading
       itself, and the next unit names the invariant that carries it [unchecked].
  3. **The context at a future of the instantiated stack: `MonoGPart`**, `MonoG` with the future taken
     at the part above the outermost lend. At the whole resource, `FutOK.below` fails once an insertion
     at depth `k > 0` puts its lifetimes above the re-lent views (DESIGN §15.3).
  4. **The premise at a future that inserts a name other than `NsVar`.** `StackJ` must admit it with a
     hygiene the row can discharge, or the renaming lemma (DESIGN §2.2, *Names*).
  5. **At `cbpv`, `CallbackExt*` when the bound mentions the binder** (`callbackExtMut_cbpv_of`'s
     restriction).
- **What would decide OQ-8.** Two things, together:
  - `Statement0 cbpv` proved at the revised W with the `U` rows at every context. That needs R1
    discharged (W reads `μ` and `fam` itself, and `InstEquivLeafAll` follows), or a `def … : Prop`
    proved that shows the gap absent. Rows proved only at `CtxThawFree` contexts decide nothing.
  - Then the probe proceeds at `cbpv` to statements 1–6 and the programs. If `cbpv` survives
    (`Survives`), W = `cbpv` is decided, since rank 0 has no placement before it (DESIGN §3). That is
    OQ-8 option 2, and D1 meets "interactions only at cuts", with the own lend's cost at `U` (DESIGN
    §4.4). A refutation passing DESIGN §11 at `cbpv` moves the question to `binder`.
- **Failure (d)** in either reading: neither the instantiation nor `CohS` adds a way to reach another
  stack.
  - The instantiation generalises the `U` clause's existing re-lend at the same clause. It is not a
    second quantifier.
  - `CohS` reads the index, as Core's `CohE` reads the records. `RecsOutside` and `SubOutside` read
    the index too, and `KeepsS` restricts the list the clause already quantifies over.

---

## 6. Order of work and the build

Unknowns first. Each step names the decision it feeds.

1. **The relation-independent facts.** No change to W is needed for any of these.
   1. Bookkeeping over `Restrat.Emb`: `ExtSInst`, `InstModels`, `Q2Inst`, `InstReLend`, `EmbLift`,
      `InstComp`, `RecsOutsideInst`, `ShareReLendInst`, `StackJInst`, `TyEqInst`, `InternalOfBound`,
      `OwnPushBelowTop`, `InstFreshExists`. The readings: `SubOutsideInst`, `SubOutsidePush`,
      `SubOutsideExtend`, `InternalBoundInside`, `SharedReadFixed`. The list: `KeepsSComp`. A failure
      is a finding about these definitions.
   2. **The guard's run facts: `PVLParts`, `PVLUpd`, `PVLRuns`**, with the model lemmas
      `ResU.ExAt_flat` and the ancestor read-back. This is the largest unknown. If one is refuted at an
      arising configuration, it is failure (b): stop and report.
   3. `ViewTypeCoincidence`. It confirms that the guard alone cannot carry the type tie (§2.6). If it
      is refuted, `CohS`'s type conjunct is not needed for (c), only for `imm` coherence, and §5.1
      keeps it for that.
   4. `CohEInst` (with `tyEq_fixed`), `ViewSlotInst` at `Mut` then at `Imm` (with `vC_obs_of_full`),
      then `MutWitnessThaws` and `MutWitnessThawsInhabited`.
   5. `NotVDenNaturalArises`, the `TW` history of §4.2.
   6. **`MutPayloadInst`, both conjuncts, then `InstEquivLeaf`.** This is the crux of the retained
      part, and the support conjunct is where `mut_not_natural`'s mechanism would show. If either
      conjunct is refuted, stop the rows, and run DESIGN §11 on the refuting configuration (§4.4).
      Then attempt `InstEquivLeafAll` and `MutPayloadInstAll` and record the step each stops at.
   7. The rest of the local bundle: `PVLNil`, `PVLStart`, `PVLEnd`, `PVLHide`, `GuardInst`, `PVLFut`,
      `PVLResume`.
   8. The arising check of `k`: `PVWNil`, `PVWUpd`, `PVWHide`, `flat_fold_mut_ne`, `flat_fold_imm_ne`,
      then `PVWLendMut`, `PVWLendImm`, `PVWRun`, `ArisesInv`, `PVArises`, `PVLocal`, `KNotInArises`,
      `KSlotNotW`, `KNotViewAt`.
   9. The records at the arising set: `RecsOutsideArises`, `RecsInsideOwnArises` at `ArisesI`, with
      `lendMut_placeView` re-proved at `LendMutI`; `MovedRecPremises`.
   10. Beside: `InternalPayloadArises`, `NotVCNaturalCore`, `NotVCNaturalCoreRefutes`,
       `ThawFreeScope`.
2. **The revision of W** (§5.1): the `I` definitions replace W₀'s in `World.lean`, `Relation.lean`,
   `Sem.lean` and `Arising.lean`.
   - Re-prove §5.5's facts.
   - Every statement that takes the guard's `TabAtS σ αs ρ` as a hypothesis takes
     `PlaceViewsL (extS δ σ αs) σ αs ls ρ` beside it, and `RecsOutside αs ls` and `SubOutside σ αs δ`
     where it reads `SemS`'s index: `MonoV`, `MonoG`, `MonoOwnG`, `MonoC`, `MonoHide`, `ThawRelend`,
     `CallbackExt*`. `BelowExcluded` reads `guardPV`. Statement 1's per-transition facts take the local
     bundle's beside theirs when statement 1 is reached.
   - Move `Binder.lean`'s and `BinderW.lean`'s W-level definitions into the files they belong to.
3. **The rows**: `GuardInst`, `ExtInst`, then `relendI_sep` and the thaw (`CtxRelendsAll .binder0`, or
   `CtxRelendsThawFree .binder0` if `InstEquivLeafAll` is not derived), then `ThawInst .binder0` and the
   four rows. That gives `Statement0UFull .binder0`, or the partial `Statement0UThawFree .binder0`. The
   rows can be proved at `BinderW.lean`'s statements before step 2 lands, since those are the target.
4. **Report**: README, CHECKPOINT and DESIGN §15 updated with the outcome; this file's §5.6 list as the
   next unit's brief.

**Lemmas to be built** (named in the plan; not statements of the design): `relendI_sep`,
`flat_fold_mut_ne`, `flat_fold_imm_ne`, `ResU.ExAt_flat`, the ancestor read-back, `vC_obs_of_full`,
`tyEq_fixed`. The guard at a future, which the plan called `placeViewsAt_fut`, is now the stated
`PVLFut`.

**The build.** Iterate with `lake build ProbeD1.<Module>`, and run `lake build ProbeD1` at milestones.
- Every theorem's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.
- No `sorry` or `axiom` lands. An unproved step in progress is an enumerated `sorry` in a scratch file,
  never committed.
- No `Core/` edit. Work on `targets`; never push.

---

## 7. Success and failure

**Item 1 (PlaceViews).**
- **Success**: `PVLBundle` proved, so the guard's views are the stack's run invariant, read from `TW`'s
  runs transition by transition; and the arising check proved: `PVArises`, `KNotInArises`,
  `KSlotNotW`, `KNotViewAt`. `PVArises` justifies `KNotInArises`: `k` is not in `ArisesI`, so
  `not_ctxRelendableAt_k` cannot pass DESIGN §11, and Q1's refutation was a fact about [W₀]. It does
  not say that `k` does not arise, and it does not justify the guard.
- **Partial**: the arising check proved, a fact of `PVLBundle` not derived. The guard's justification
  stays open. Report the fact and the step it stopped at. Item 4's rows read the guard as a hypothesis
  and may still be proved, but no claim that the guard is `TW`'s is made.
- **Failure (b)**: a fact of `PVLBundle` refuted at a configuration that arises (DESIGN §11). The guard
  is beside `TW`. Stop and report.
- **The arising check fails**: a transition of `ArisesI` does not keep `PlaceViewsW`. Then
  `KNotInArises` is not established. If the configuration that breaks it passes DESIGN §11, a cell at a
  bound place that is not the view arises, and the guard excludes a configuration that arises: failure
  (b), as for a refuted fact of the bundle. Report the transition.

**Item 2 (the lifetime binder).**
- **Success**: `InstModels`, `Q2Inst`, `InternalOfBound`, `OwnPushBelowTop`, `InstFreshExists`, the
  bookkeeping (`EmbLift`, `InstComp`, `RecsOutsideInst`, `ShareReLendInst`, `KeepsSComp` among it),
  the readings (`SubOutsideInst`, `SubOutsidePush`, `SubOutsideExtend`, `InternalBoundInside`,
  `SharedReadFixed`), `TyEqInst`, `CohEInst`, `ViewSlotInst`, `MutPayloadInst` (both conjuncts) and
  `InstEquivLeaf` proved, and the records' invariants at the revised arising set
  (`RecsOutsideArises`, `RecsInsideOwnArises`). Then Q2 is met at every instantiation the clause
  ranges over; what it moves is only what the frozen computation made, the resumer's variables
  fixed; the records' action is consistent with the world at a resume up to the cases §3.7 leaves to
  statement 2; and the relation's equivariance is what §3.6 states.
- **Failure**: `MutPayloadInst` (either conjunct) or `InstEquivLeaf` refuted.
  - If the refuting configuration passes DESIGN §11, it is failure (a) for the `U` rows at `binder0`.
  - If not, it is a fact about the statement, and the guard needs the conjunct that excludes it. Name
    the conjunct, and check that the transitions keep it (§4.4).
- **The records' invariant refuted at the revised arising set.** Then a record the instantiation
  leaves alone can read an internal lifetime at a configuration that arises, and the records' action
  of §3.2 does not hold together. Report the configuration and the transition, and revisit
  `LendFresh`.
- **A readings fact refuted** (`SubOutsidePush`, `SubOutsideInst`, `SubOutsideExtend`,
  `InternalBoundInside`, `SharedReadFixed`). These are about our definitions; a refutation is a finding
  about `SubOutside` or `boundBefore`, reported with the configuration.

**Item 3 (the known risk).** §4.4's table.
- `MutWitnessThaws` and `MutWitnessThawsInhabited` proved: at the witness, the instantiation
  re-establishes the slot and never forms the image of the witness's invariant, at hypotheses a
  configuration of `InternalPayloadArises`'s shape meets.
- `NotVDenNaturalArises` proved: `ρ₀` is a part of a `TW` world. `mutFold`'s predicate is
  unconstrained, so that is not arising in DESIGN §11's sense; the reachability question is
  `InternalPayloadArises`'s, or `NotVCNaturalCore`'s with a program exhibited. Refuted: `ρ₀` is a
  part of no `TW` world, and so of no world that arises at Core's nil index.
- `NotVCNaturalCore` and `NotVCNaturalCoreRefutes` proved: `FreezeBinderLife` at `coreW` is refuted as
  Targets states it, a fact about that statement. It is evidence about OQ-8 option 1, not an obstruction,
  until DESIGN §11 passes.

**Item 4 (the rows).**
- **Success**: `Statement0UFull .binder0` proved, the thaw at every context, with §5.5's re-proofs.
- **Partial**:
  - `Statement0UThawFree .binder0` proved, with `InstEquivLeafAll` or `MutPayloadInstAll` not derived:
    "partial: guarantee gap R1 (`μ`, `fam`, thunks in payloads) open". Report the step each stopped at.
  - Or the rows proved given `CtxRelendableAtI`, with the thaw not derived at some `ThawFree` slot type.
    Report the type and the step.
- **Failure**:
  - (a) a row refuted at an arising configuration (DESIGN §11);
  - (b) a guard beside `TW`, or a second relation family;
  - (d) a clause changed to reach another stack by other means.

A statement neither proved nor refuted is reported as "not derived, no obstruction verified", with the
step it stopped at.

---

## 8. What each outcome means for D1, OQ-8 and the fallback

- **All four items succeed, item 4 at `Statement0UFull`.**
  - Both of statement 0's shared needs are met at every context, by changes to our definitions. Each was
    named by the binder reading: a bound place's cell is the binder's view, and a resume instantiates
    every bound lifetime, preserving order, with the records the frozen computation made.
  - D1's ghost-end route has its lifetime half: an instantiation that transports no resource, rebuilds
    the views, moves only what the frozen computation made (its lends, the variables it bound, its
    records) and leaves the others alone, and keeps every `⟦Δ⟧`.
  - D1's tractability then rests on the per-placement needs §5.6 lists, which are not shared.
  - OQ-8 is undecided until `cbpv`'s rows are retried. Nothing here is evidence for D3 or D0, and
    nothing is evidence against them.
- **Item 4 only partial (`Statement0UThawFree`).**
  - The shared needs are met at `CtxThawFree` contexts only. R1 is open, and `ThawFreeScope` shows that
    typing reaches contexts outside the result.
  - Nothing follows for OQ-8, and D1's lifetime half is established only for frozen computations
    holding no `μ`, `fam`, or thunk in a payload. The next step is R1, before any placement is decided.
- **`InstEquivLeaf` fails at `Mut` at an arising configuration**, a conjunct of `MutPayloadInst`
  refuted there: the stored predicate, or its support at a list whose records sit in `θ`'s gap.
  - A retained `mut` cell's payload is not stable under the instantiation. So the frozen part cannot be
    left in place while its lifetimes move.
  - The binder's lifetime half then has to re-lend more than the views, and the retained part stops
    being fixed. D3's carried lends avoid the question: the closure keeps its lifetime across the stop,
    and nothing is instantiated [unchecked].
  - This is evidence for D3 against D1's re-lend. It is not by itself the machine-checked failure that
    triggers the fallback. That needs a row of `Probe p` refuted at an arising configuration
    (DESIGN §12.2 (a)) at every placement whose statement 0 holds.
- **The guard's views are not kept by a transition (failure (b)).**
  - The probe stops. The guard cannot be W's run invariant read from `TW`'s runs.
  - D1's route needs another way to exclude `k`, and the report says which transition failed.
  - The fallback order stands: D3, then D0. D3 keeps lends open across stops, so its views persist and a
    PlaceViews-like coherence would be needed there too [unchecked].
- **The rows refuted at an arising configuration (failure (a)).**
  - The `U` introductions are refuted at `binder0`.
  - With `cbpv` and `binder` still owing theirs, this decides nothing for OQ-8 yet. It decides `binder0`
    against itself, and a placement before W counts only by such a refutation (DESIGN §3).
- **`mut_not_natural`.** Whichever way §4.4's table falls, D1's instantiation does not ask naturality:
  views are rebuilt, and retained cells are fixed. Whether a retained cell stays related at the
  instantiated reading is `InstEquivLeaf`'s, with both conjuncts of `MutPayloadInst`, not
  `MutPayloadInst`'s stored predicate alone. `NotVCNaturalCore`, proved, refutes
  `FreezeBinderLife` at `coreW` as Targets states it. That is a fact about that statement and evidence
  about T3's lifetime half and OQ-8 option 1. It is not an obstruction, and it decides nothing for
  option 1 until DESIGN §11 passes: the value arising at that world, the program and its run exhibited.
  It bears on the target structure, not on D1's rank.

---

## 9. Report lists (CLAUDE.md §5)

**Printed hypotheses the routes spend.**
- [TR] 6.48 (`updV_frame`), at `PVWRun`. Its proof's technique, a `mut` cell of the aliasable walk
  accounted for by its immutable ancestor, at `PVLUpd`, the guard's run fact (§2.4).
- `↭`'s `mut` and `imm` clauses ([TR] p. 5, row 18), at `PVLUpd` and `PVWUpd`.
- 6.65's and 6.64's opening cells (`ρm = ℓ ↦ mut(α, …)`, `ρi = ℓ ↦ imm({α}, …)`), at `PVLStart`,
  `PVWLendMut`/`Imm` and the exact lifetime.
- 6.65's and 6.64's closings (the view handed back, the owner restored), at `PVLEnd`.
- 6.116 (I-dup) and 6.43, at the thaw's composition of `imm` views.
- 6.117 (M-inv): only to say why extensional equality of invariants does not survive an instantiation
  (§1.3 (c)); it is not used as a step.
- 6.65's and 6.64's choice of the lend (H4: "Such an α always exists because for any lifetime, the set
  of lifetimes shorter than it is infinite"), with the `И` they unfold: the licence for `LendFresh`
  and `SubFresh` to take the lend below a finite set. It is the printed step at which a real lend
  meets them, read at `CallbackExt*`; it is not a lemma spent.

**Still unspent**, since no row that reads them is in this unit:
- 6.108–6.112 (`И`-mono, `И`l, `И`r, `И`⋆, `И`f). `InstFreshExists`'s proof is arithmetic and spends
  none of them. They are spent at `FreshFrameI` and the resume, in statement 2. `InstFresh` reads 6.112's
  `И` for the licence to take a lifetime below a finite set; that is a reading of the `И`, not a step
  that spends a lemma.
- 6.65's `P̂ ⊧ [β] P̂`;
- 6.64's `AdmWf` and `hQ` at a resuming table;
- 6.66's premises;
- 6.150's H11 and H16;
- 6.149;
- 6.50 for the table (`TabUpd`);
- 6.62.

**Uniqueness and functionality results.**
- Expected to be used:
  - `ResU.Flat.functional` (one flattening cell per place, in `PVLUpd` and `PlaceViewsW`);
  - `ResU.CompS.functional`;
  - `CellU.compS_immOf` (an `imm` composite keeps value and witness, in `PVLParts`);
  - `CellU.mutOf_inj`, `CellU.mutOf_at`, `mutPred_mutOf`;
  - `Restrat.Emb.injective` (a record list's instantiation is injective);
  - `dropC_disj` (one `mut` view per place across slots).
- Not expected: the machine's determinism (`AStep1.deterministic`). The location half of the binder
  (T3's `FreezeBinderLoc`) is where it would enter.

**Printed lemmas in the run-up that are untranscribed.**
- None of those this unit reads: 6.48 and 6.49 are transcribed (`TR.lemma_6_48`, `TR.lemma_6_49`), and
  6.108–6.112 are (`TR.lemma_6_108` … `TR.lemma_6_112`).
- The block form of 6.112 (`freshI`, `FreshFrameI`) is ours, stated here and not built.
- As before: [TR] 6.150 at a resuming table, and the stacked folds at `ResumeAff` tables
  (DESIGN §15.5).

**Hypotheses added, and their scope.**
- **`CohS` at W's `Mut`/`Imm` leaves.** It comes from the lend's view type: withbor's callback receives
  `Mut 'x T` with `T` the lend's payload. It is the 6.65 analog of Core's `CohE`. At `σ = []` it is
  vacuous.
- **`PlaceViewsL` in the guard and `vwSL` for the views.** The binder's location half. The local bundle
  is its justification (§2.3), and failure (b) is what refutes it.
- **`OwnOKI.placeFree`, `FutOKI.placesFree`, at every depth.** The lent place is the lender's: a real
  lend's callback holds no cell there, and a future's inserted lend is the resumer's. Every real lend
  meets both.
- **`OwnPushI`'s `ViewAt`.** The own lend at a callback-shaped type is the view's lend. It is `True` at
  an argument type that is not a `Mut` or `Imm` of a variable. At a `Mut` or `Imm` of a variable other
  than the binder, or of the other kind, it is `False`, and no own lend is admitted there. That is a
  restriction, and §2.1 checks its consumers: `CallbackExt*`, `k_reached` and `ThawFreeScope` read the
  own conjunct at the binder's view, and the one borrow constant whose callback type can meet the
  exclusion is `withload` at `T₁ = Imm 'z S`, whose entry is R2's question.
- **`RecsOutside` at `SemSI`'s index, the own lend and `RelendI`'s extension; `LendFresh` at
  `LendMutI` and `LendImmI`.** Every real lend can meet `LendFresh`: 6.64's and 6.65's H4 choose the
  lend below a bound, and the `И` admits every lifetime below it, so the proof may take one below the
  finite set of the records' lifetimes. Non-vacuous: it holds at every index with no record, `k_index`
  and `q2_reached`'s among them, and at `InternalPayloadArises`'s configuration with `b`'s record read
  at the empty substitution [unchecked].
- **`SubOutside` at `SemSI`'s index; `SubFresh` at the own lend.** The same licence, below the finite
  set of the reading's values. A real lend meets `SubFresh`, since the borrow constant's row chooses
  the lend after the reading is fixed. Non-vacuous: `SubOutside` holds at every index whose reading
  binds nothing before a stack variable's binding, `k_index` (`kδ = ⟨[]⟩`) and `q2_reached`'s (`qδ`
  binds `'1` after `'0`) among them. Scope: it says nothing of an entry whose variable the reading
  does not bind, a future's (§5.6 item 2).
- **`KeepsS` at `RelendI`'s extension.** `Ext`'s `Keeps` read at the dropped views, up to `RecUpTo`.
  Every consumer of this unit supplies it (§3.4): `[force]` at `ls' = ls`, the composite by
  `KeepsSComp`. The share supplies it when the re-opened records are the moved ones up to
  `RecUpTo`; when the lender changed a payload's `own` cells between the stop and the resume, that is
  statement 2's to decide (§3.7).
- **`CallbackExt*`'s `e.T = T`, the views at `e :: σ`, `RecsOutside` at the pushed lend and
  `SubFresh δ α`.** Each is a property of the borrow constant's lend.
- **`CtxThawFree Γ` at the partial result's rows.** A guarantee gap: FL at W proved under it says
  nothing about a thunk over a `μ` or `fam` slot, or a thunk in a payload, inside a lend.
  `ThawFreeScope` shows typing reaches such a context. Its discharge is §5.4 R1. Non-vacuity at
  `genSelf` and `reconB′` is to be checked [unchecked].
- **`MutPayloadInst`'s hypotheses.** Support in `Res_b` at the original reading is `ptoMutS`'s own last
  conjunct, read at the retained cell. `RecFixed` is `RecsOutside` read at the records longer-lived
  than the cell, which are the ones `ptoMutS`'s stored predicate reads. Its conclusion asks the same
  support at the instantiated reading, at every list, which no hypothesis supplies.
- **`ViewSlotInst`'s `InstAt`, `RecsOutside` and `KeepsS`.** `CohEInst` needs the first two to move the
  slot's coherence record; `KeepsS` puts the moved record in `ls'`. The thaw supplies all three
  (§5.3).

---

## 10. The reviews' findings, answered

Each finding of each review of this design is answered here, in the review's order, with where the
text and the Lean answer it. Whether a revision answers its finding has not been checked by the
reviewer.

### 10.1 The first review

1. **Major: the guard carried `PlaceViewsAt` while the unit proved `PlaceViewsW`, and `PVArises` cannot
   justify a guard.** Answered: the guard is `PlaceViewsL`, local, at the clause's reading and list, at
   every depth (§2.1). Its justification is the local bundle `PVLBundle`, one fact per transition and
   per quantified configuration, parallel to statement 1's (§2.3), with its proof plan spending 6.48's
   technique locally (§2.4). Failure (b) is named per fact (§2.3, §7). The `imm` full payload stays in
   the guard, with the transitions that keep it (§2.1). `PVArises` and `KNotInArises` are the arising
   check of `k` only (§2.5, §7).
2. **Major: the rows were not retried at full strength.** Answered: the target is statement 0's rows at
   the revised W with the thaw at every context (`Statement0UFull`, §5.2). The `CtxThawFree` rows are the
   partial result (§5.6, §7, §8). The excluded cases are stated, not excluded (`InstEquivLeafAll`,
   `MutPayloadInstAll`, §3.6), and `ThawFreeScope` exhibits a context typing reaches inside a lend that
   the restriction excludes (§5.2).
3. **Major: conclusions in the refuting direction drawn from a witness not shown to arise.** Answered:
   §3.6, §4.3, §4.4 and §8 say "evidence, not an obstruction; it decides nothing until DESIGN §11
   passes". `NotVCNaturalCore` is restated at a `coreW.Fam` world (finding 13).
4. **Minor: `InternalPayloadArises` too weak.** Answered: it now pins the lifetimes, `x`'s view at the
   stack's reading, `b`'s `imm` cell in `x`'s witness, and an `ArisesV` of `x`'s view at `viewTy x`
   (§4.2). It is evidence only.
5. **Minor: names used as statements with no `Prop`.** Answered: `MutWitnessThaws`, `KSlotNotW` and
   `KNotViewAt` are stated (§2.7, §4.3). The remaining names are listed as lemmas to be built (§6), and
   the claim about `Binder.lean` says so (header).
6. **Minor: `cutOf` at an outermost lend of `⊤`.** Answered: `Internal` is defined through the cut
   (`a < c`), so it is exactly what an instantiation may move. `InternalOfBound` takes `OuterBelowTop`,
   which `OwnPushBelowTop` supplies for every own lend (§3.1).
7. **Minor: freshness only beneath `R`'s cells.** Answered: `InstFresh` is taken below `R` and every
   lifetime the resumer's index reads (`IdxReads`), and `InstFreshExists` is stated at that set (§3.3).
8. **Minor: the narrowing's cost was prose.** Answered: each consumer's obligation is named, among them
   `InstComp` with `EmbLift`, `InstFreshExists`, and `ShareReLendInst` for the share (§3.5).
9. **Minor: history in `Binder.lean`'s docstring.** Answered: the attribution and date are gone.
10. **Major: `Inst.recs` moved external records' substitutions, which no tagged `TW` world at a resume
    holds.** Answered: Option 1. `Inst.recs` moves exactly the records below the cut and leaves every
    other record as it is. `RecsOutside` (with `CohEInst`) keeps the slots coherent with a record left
    alone, and `RecsInsideOwn` makes the moved records the ones a resume rebuilds. Both come from
    `LendFresh` at the revised arising set `ArisesI` (`RecsOutsideArises`, `RecsInsideOwnArises`), and
    `RecsOutside` is an index hypothesis of `SemSI` (§1.3 (d), §3.2, §5.1). The sentence about `Emb.fix` is corrected:
    it fixes a record's tag, not its substitution (§3.2).
11. **Major: the `ThawFree` result was counted as success and could decide OQ-8.** Answered as finding 2.
    R1's discharge, or a proved `def` showing the gap absent, is a precondition of any "decided" (§5.6,
    §8).
12. **Minor: the guard's local form had no stated run invariant.** Answered as finding 1: §7 item 1 says
    `PVArises` justifies `KNotInArises` and not the guard, and the local bundle is stated in
    `Binder.lean`.
13. **Minor: `NotVCNaturalCore` not tied to a world, and §4.4 row 1 overstated.** Answered:
    `NotVCNaturalCore` is one `Prop` at a `coreW.Fam` world, moving records as `srecRestrat` does, with
    `NotVCNaturalCoreRefutes` the negation of `FreezeBinderLife`'s `val` clause at `coreW`. §4.4 row 1
    now says it refutes `FreezeBinderLife` as stated, and that option 1 is decided only with DESIGN §11's
    full check (§4.3, §4.4).
14. **Minor: 6.108–6.112 claimed as spent by an arithmetic proof.** Answered: they are listed as unspent
    in this unit (§9). The block form of 6.112 is stated (`freshI`, `FreshFrameI`), with its planned
    proof following `fresh_frame`'s printed chain, for statement 2 to reach for (§3.3).
15. **Minor: `cutOf` at an outermost lend of `⊤`, again.** Answered as finding 6. `OwnPushBelowTop`
    states the own lend below `⊤`, from `LtLife`; a `LendMut` at `⊤` is not excluded, and `Internal`'s
    definition through the cut keeps the docstring true there (§3.1).

### 10.2 The second review

1. **Major: the instantiation could move the reading of a variable bound outside the frozen
   computation.** Answered with the review's option (a). The own lend is fresh below the reading as
   well as the records: the `∀` clause asks `SubFresh δ α` of it, beside `RecsOutside` (§5.1). `SemSI`
   carries the index invariant `SubOutside`: for each lend, the bindings of `δ` made before its
   variable's are read above it (§3.1). It is sourced at the push (`SubOutsidePush`) and kept by an
   instantiation (`SubOutsideInst`) and by a binding new to the stack (`SubOutsideExtend`).
   - At such indices an internal variable was bound inside the outermost lend
     (`InternalBoundInside`): `BoundBelowV ⊆ InternalVar ⊆ BoundInside`. This is the inclusion the
     review asked for, not an equality: a variable bound inside may be read above the cut, and then
     every instantiation fixes it (§3.1).
   - §1.2's last bullet is rewritten: the down-set is the binder's because each place the index reads
     a lifetime is covered by an invariant. §3.1 now shows the external variable's example, says why
     the semantic set alone does not suffice, and gives the share's cost.
   - The share's obligation for an answer type at a shared variable is discharged by
     `SharedReadFixed`: the share's instantiation fixes every binding made before the ended part
     (§3.5, §3.7).
2. **Major: `MutPayloadInst` did not state the support conjunct at the instantiated reading.**
   Answered: `MutPayloadInst` and `MutPayloadInstAll` conclude both parts of Core's `ptoMutS`. The
   stored predicate is the `↔` at the `RecFixed` list. The support at the instantiated reading, at
   every list, is a second conjunct, the one where records in `θ`'s gap enter (§3.6). §4.4's table,
   §7 and §8 read the retained part from `InstEquivLeaf`, whose `Mut` case needs both conjuncts, and
   no longer from `MutPayloadInst` alone.
3. **Minor: "`k` does not arise".** Answered: §2.5, §2.7 and §7 say "`k` is not in `ArisesI`, so
   `not_ctxRelendableAt_k` cannot pass DESIGN §11", and that this is not a claim that `k` does not
   arise, since the set's under-approximation is not established and it has no lend-end transition.
   The statement is renamed `KNotInArises`. §2.5's plan covers every constructor of `ArisesI`, `part`
   among them, where `fρ` is unchanged.
4. **Minor: `MutWitnessThaws` could hold vacuously.** Answered: `MutWitnessThawsInhabited` states its
   hypotheses met at a configuration of `ArisesI` with `InternalPayloadArises`'s shape at `mwσ`: the
   configuration's list, the slot's resource `x`'s cell holding `b`'s `imm` cell at `1`, and a view
   handed at the instantiated reading (§4.3).
5. **Minor: item 4's statements elaborated against W₀.** Answered with the review's first option. The
   revised W lands in Lean beside W₀, under the suffix `I`: `OwnOKI`, `OwnPushI`, `FutOKI`, `FutI`,
   `LendMutI`, `LendImmI`, `ArisesI` in `Binder.lean`; `vRLI`, `cRLI`, `gRLI`, `SemSI` and item 4's
   statements (`ThunkFRowI` … `Statement0UFull`) in `BinderW.lean`. `lake build ProbeD1` elaborates
   them. The statement that elaborates is the target §5.2 describes, and no proof of W₀ breaks (header,
   §1.4, §5.1, §5.2).
6. **Minor: `ViewAt` is not vacuous at other types.** Answered: §2.1 and §9 say that `ViewAt` is
   `False` at a `Mut` or `Imm` of a variable other than the binder, or of the other kind, so the own lend
   is excluded there. §2.1 checks its consumers: `CallbackExt*`, `k_reached` and `ThawFreeScope` read the
   own conjunct at the binder's view, and the one borrow constant whose callback type can meet the
   exclusion is `withload` at `T₁ = Imm 'z S`. Whether `withload` pushes an entry at all is R2's
   question.
7. **Minor: the kept witness against the world's records.** Answered with the review's second option,
   and the part of the first that can be stated without statement 2's resume composite.
   - §3.2 now says explicitly that the kept witness may need its frozen view copies rebuilt, and that
     the world's re-opened record then differs from `Inst.recs`'s in its witness's borrow cells. The
     clause compares records up to those (`RecUpTo` in `KeepsS`), since the relation reads a witness
     only through its `own` cells.
   - `MovedRecPremises` states, as a `Prop`, that the moved record meets `TW.immFrame`'s per-record
     premises at the instantiated reading and lifetime, its witness kept.
   - The world-level part, a tagged `TW` world at the list the share hands, needs the resume
     composite, which this unit does not construct. §3.7 names what that list must meet (`Ext`,
     `KeepsS`, `RecsOutside`) and its cases. One of them is open: a payload whose `own` cells the
     lender changed between the stop and the resume [unchecked].
8. **Minor: no fact for a lend's end.** Answered: `PVLEnd`, the guard at the outer stack for the
   post-callback resource, given the views at the pushed stack, no cell at the lent place at any
   depth, and the lender's part (§2.3, §2.4), in `PVLBundle`. Its readers are the borrow constants'
   spans rows, which pop. `CallbackExt*` conclude at the pushed stack and do not pop, and a run keeps the
   guard across any lend opened and closed inside it (`PVLRuns`). The table's analog is statement 2's.
9. **Major: `RelendI`'s extension could drop the stack's own records.** Answered: `RelendI` and
   `RelendUI` ask `KeepsS (ι.recs ls) ls' ρn` beside `Ext (ι.recs ls) ls' ρz`. That is `Ext`'s `Keeps`
   read at the dropped views, which keeps the records the views are coherent with, up to `RecUpTo`
   (§3.4). It excludes the review's configuration (`ls' = []` at `b`'s view). Every consumer supplies
   it: `[force]` at `ls' = ls`; the composite by `KeepsSComp`, checked against `InstComp` and `ExtInst`
   (§3.4, §3.6); the share by the re-opened records (§3.7). `ViewSlotInst` takes `KeepsS` at the slot's
   cell in place of `ι.recs ls ⊆ ls'`. §5.3 says where it comes from: the clause's `KeepsS` at `ρn`,
   since a record relevant to a part's `imm` cell is relevant to `ρn`. `ViewSlotInst` also takes
   `InstAt` and `RecsOutside`, which `CohEInst` needs inside it.
10. **Major: `LendFresh` did not put a lend below the reading.** Answered as finding 1, with option
    (a): `SubFresh` at the own lend, `SubOutside` in the index. The licence cited is 6.65's H4 ("Such
    an α always exists because for any lifetime, the set of lifetimes shorter than it is infinite")
    and 6.64's, with the `И` they unfold. It replaces "6.112's `И`" for `LendFresh` and `SubFresh`
    (§1.2, §3.2, §9).
11. **Minor: `NotVDenNaturalArises` proved was read as "the witness's world arises".** Answered: §4.2,
    §4.4's first row and §7 say that a proof shows only that `ρ₀` is a part of a `TW` world, since
    `mutFold`'s predicate is unconstrained, and that this is not arising in DESIGN §11's sense. Only the
    negative outcome is informative. The reachability question is pointed at `InternalPayloadArises`,
    or `NotVCNaturalCore` with the program and its run exhibited. §4.3's conclusion does not depend on
    it.
12. **Minor: `MutPayloadInst` did not give `InstEquivLeaf`'s `Mut` case.** Answered as finding 2.

---

## 11. The build's outcome

The build is in eight files beside the design's two. `lake build ProbeD1` builds them; they have no
`sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`, and every
theorem's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `BinderInst.lean` | item 2's bookkeeping, readings, records and freshness |
| `BinderPV.lean` | the guard's local facts at a part, a lend's start and end, a handler, the resume; `GuardInst` |
| `BinderPVRun.lean` | the guard across `↭` and a run, at distinct places ([TR] 6.48's technique) |
| `BinderRefute.lean` | four of the design's statements refuted, each at a configuration not shown to arise |
| `BinderJ.lean` | the draft relation as the build revises it (`vRLJ`), and item 4's statements at it |
| `BinderRows.lean` | the thaw at every `ThawFree` slot type, `ThawInstJ`, the four `U` rows at `binder0` |
| `BinderArise.lean` | the arising check of `k`: PlaceViews at the world of every `ArisesI` configuration |
| `BinderRisk.lean` | item 3: the `TW` history, the view slot at the witness, `ViewTypeCoincidence` |

**The status words.** *Proved* is a theorem. *Refuted* is a theorem proving the statement's negation;
each refutation here is at a configuration not shown to arise, so it is a fact about our statement
and decides nothing by itself (DESIGN §11). *Not derived* means neither, with no obstruction
verified. *Not attempted* means no proof was tried.

### 11.1 Item 1: PlaceViews

**The local bundle.**
- Proved: `PVLNil` (`pvlNil`), `PVLParts` (`pvlParts`), `PVLStart` (`pvlStart`), `PVLEnd`
  (`pvlEnd`), `PVLHide` (`pvlHide`), `GuardInst` (`guardInst`), `PVLResume` (`pvlResume`), `PVLTop`
  (`pvlTop`).
- `PVLUpd` and `PVLRuns` are proved at a stack whose places are distinct (`PVLUpdN`, `pvlUpdN`;
  `PVLRunsN`, `pvlRunsN`). The places of every `ArisesI` stack are distinct, since each lend opens at
  a place new to the stack (`placesNodupArises`). So `PVLUpd` and `PVLRuns` hold at every stack
  `ArisesI` reaches (`pvlUpd_arises`, `pvlRuns_arises`).
- Not derived: `PVLUpd` and `PVLRuns` as stated, at a stack whose places may repeat. The case left is
  two `imm` entries lending one place. No configuration for it was built, and no obstruction is
  claimed. W's index (`StackOK`) asks distinct variables, not distinct places. Adding distinct places
  to the index is the step that would carry `pvlUpdN` to every index the relation reads; it is not
  made here.
- Not attempted: `PVLFut`. `binder0`'s clauses quantify over the stack itself (`FutQI false` is the
  identity), so `binder0` does not read it.
- So `PVLBundle` is not proved. The guard is the stack's run invariant at distinct places, which every
  `ArisesI` stack has; `PVLFut` is `cbpv`'s and `binder`'s.
- **The printed technique spent.** `pvlUpdN` follows [TR] 6.48's case analysis at the local part. A
  `mut` cell of the exclusive walk goes by `↭`'s `mut` clause; the case where the old flattening's
  `mut` cell sits beneath an `imm` ancestor is excluded by the ancestor transfer
  (`ResU.upd_ag_nonimm_transfer`, the step 6.48's proof spends at the aliasable walk). An `imm` cell
  goes by `↭`'s `imm` clause and the copies it is made of (`AgW.imm_mem_deep`).

**The arising check of `k`** (`BinderArise.lean`). All proved:
- `PVWNil`, `PVWHide`;
- `PVWUpd` (`pvwUpd`): `↭`'s `mut` clause read backwards keeps the lifetime and stored invariant,
  its `imm` clause the cell;
- `PVWRun` (`pvwRun`): [TR] 6.48 (`updV_frame`) at the frame, the local part and `π = ρ' ● ρp`, then
  `pvwUpd`;
- `PVWLendMut`, `PVWLendImm` (`pvwLendMut`, `pvwLendImm`). At the lent place the folded cell is the
  flattening there (`flatAt_fold_mut_self`, `flatAt_fold_imm_self`), at exactly the lend's lifetime,
  storing the entry's view or holding its value. Off the place the flattening is unchanged
  (`flatAt_fold_mut_ne`, `flatAt_fold_imm_ne`). At an `imm` fold, a payload cell of the exclusive walk
  moves under the `imm` cell into the aliasable walk, where validity before the fold leaves it the only
  contribution ([TR] 6.36, `ExS.immFree`; 6.32, `ExS.toExR`).
- `ArisesInv`, `PVArises` (`arisesInv`, `pvArises`), by induction on `ArisesI`;
- `PVLocal` (`pvLocal`), `KNotInArises` (`kNotInArises`), `KSlotNotW` (`kSlotNotW`),
  `KNotViewAt` (`kNotViewAt`).

`KNotInArises` says that `k` is not in `ArisesI`, so `not_ctxRelendableAt_k` cannot pass DESIGN §11.
It does not say that `k` does not arise: `ArisesI` is not shown to over-approximate what arises.

### 11.2 Item 2: the lifetime binder

**Proved.**
- The models: `InstModels` (`instModels`), and `ReLendModelsI` at every index from `Δ.Models`
  alone (`reLendModelsI_of`). This replaces `BoundsStackFree`; no condition on `Δ` is left.
  `Q2Inst` (`q2Inst`): `q2_reached`'s configuration is kept by every instantiation.
- The bookkeeping: `ExtSInst`, `InstReLend`, `EmbLift`, `InstComp`, `RecsOutsideInst`,
  `ShareReLendInst`, `StackJInst`, `InternalOfBound`, `OwnPushBelowTop`, `InstFreshExists`,
  `KeepsSComp`.
- The readings: `SubOutsideInst`, `SubOutsidePush`, `SubOutsideExtend`, `InternalBoundInside`,
  `SharedReadFixed`.
- `ViewTypeCoincidence` (`viewTypeCoincidence`): `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))` and `1 ⊕ 0` are
  one relation at `'x ↦ 1` and two at `'x ↦ 2`. So the guard alone does not carry the type tie, and
  `CohS` asks the types up to `TyEq`.
- `TyEqInst` at a type Core reads without a thunk (`tyEq_inst`).
- Coherence at the stack's own index (`cohE_inst`): `CohEInst` with `OuterBelowTop`, at a
  `CoreStable` type, the record kept up to `RecUpTo`. A record's reading moves with it below the cut
  and is fixed above it (`rec1_δ`, from `RecsOutside` and `OuterBelowTop`).
- `ViewSlotInst` at a `CoreStable` slot type with `OuterBelowTop` (`viewSlotInstCS`).

**Refuted** (`BinderRefute.lean`, each at a configuration not shown to arise).
- `ExtInst` (`not_extInst`). `Ext` keeps a relevant record without its tag, so an extension may hold
  it at a tag the instantiation leaves alone while the original holds it at one the instantiation
  moves. The design's composite, which `ThawInst` reads, rested on this step.
- `CohEInst` (`not_cohEInst`). At an outermost lend at `⊤` the cut is `⊤`, a record at `⊤` is left
  alone, and `RecsOutside` says nothing of it; its reading below `⊤` moves in the slot's reading.
- `MutPayloadInst` (`not_mutPayloadInst`), its support conjunct, and with it `InstEquivLeaf`
  (`not_instEquivLeaf`) and the forms at every type (`not_mutPayloadInstAll`,
  `not_instEquivLeafAll`). The payload `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))` at `'x ↦ 1` has no resource in
  its second branch. The shift `n ↦ n + 1` reads `'x` at `2`, and the gap at `1` makes room for one.
  So a payload supported in `Res_⊤` at the reading is not supported at the instantiated one. This is
  `mut_not_natural`'s mechanism at the retained part (§11.3).

**Not derived, no obstruction verified.** `TyEqInst` at every type: at `CTyEq`'s `∀` clause the
instantiated side quantifies over lifetimes in the instantiation's gap, where the hypothesis has no
instance, so the structural induction stops there. `ViewSlotInst` as stated, at every type and at an
outermost lend at `⊤`.

**Not attempted.** `MovedRecPremises`, `RecsOutsideArises`, `RecsInsideOwnArises`, `FreshFrameI`.
Their consumers are the share at a resume (statement 2) and the arising set's records. [unchecked]
For `RecsOutsideArises`, `LendImm` constrains the new list only through `rsOf` and `Tagged`, so an
old record may come back with another tag; whether `Tagged`'s `FrameLife` excludes that is the first
step to check.

### 11.3 Item 3: the known risk

**Whether `mut_not_natural`'s witness arises is still undetermined.** The `TW`-history check tells
nothing, because `TW.mutFold` accepts any predicate. The `ArisesI`-level check
(`InternalPayloadArises`, `MutWitnessThawsInhabited`) was not attempted. `NotVDenNaturalArises` keeps
the name the targets gave it; it is not an arising result.

- **`NotVDenNaturalArises` is proved** (`notVDenNaturalArises`). Restrat's `ρ₀` is a part of a tagged
  `TW` world, by §4.2's history (`nv_tw₁`, `nv_tw₂`, `nv_tw`, `nv_tagged`). `Tagged` reading `ag`
  through the `mut` witness goes through (`AgW.single_mut_inv`). The last step is `TW.mutFold`, which
  takes any stored predicate. So the proof shows only that `ρ₀` is a part of a world `TW`'s
  constructors build, not of one a run produces. It is not arising in DESIGN §11's sense, and it
  carries no refutation.
- **At the view slot the witness does not apply.** `MutWitnessThaws` is proved (`mutWitnessThaws`):
  at the witness's own map, the slot holding `x`'s view at `Mut '0 (Imm '1 1)` is re-established from
  the view handed at the instantiated reading. The image of the old stored invariant is never formed.
  The general case is `vC_mut_bound` and `vC_imm_bound`, which the thaw uses at every bound place.
  Its hypotheses are met at an exhibited configuration (`MutWitnessThawsMet`,
  `mutWitnessThaws_met`): `x`'s cell at `2` over `ℓ′ ↦ imm({1}, (), ∅)` and the handed view at `3`
  over `ℓ′ ↦ imm({2}, (), ∅)`, each coherent with `ℓ′`'s record. That configuration is not shown to
  arise. `MutWitnessThawsInhabited`, the same at `ArisesI`, is not attempted.
- **At the retained part the mechanism does apply, as a fact about our statement.**
  `not_mutPayloadInst` breaks the support conjunct of a retained `mut` cell whose payload type reads
  an internal lifetime. The configuration is not shown to arise, and DESIGN §11's check on a
  retained cell with such a payload was not run. So it is evidence and not an obstruction: D3 is not
  triggered, and D1's lifetime half is not refuted. The revised W excludes the case at the leaf
  (`RetainedPay`, §11.4), and the instantiation fixes a payload read at external lifetimes
  (`agree_of_payExt`).
- §4.4's table reads: `NotVDenNaturalArises` proved; the view slot proved; the retained part not
  derived at `Mut`, with a conjunct of `MutPayloadInst` refuted and its arising check not run. That
  is the table's second row, and the conjunct that excludes it sits at the leaf rather than the guard.
- **Not attempted.** `InternalPayloadArises`, `NotVCNaturalCore`, `NotVCNaturalCoreRefutes`.

### 11.4 Item 4: the `U` introductions at the revised W

**The design's targets are false as stated.** At `vRLI` (`BinderW.lean`), `CtxRelendsThawFree
binder0` fails (`not_ctxRelendsThawFree`), and with it `Statement0UThawFree binder0` and
`Statement0UFull binder0` (`not_statement0UThawFree`, `not_statement0UFull`). The context is one
`CtxThawFree` slot `m : Mut '0 (1 ⊕ Imm '0 (Imm '0 (Imm '0 1)))` holding a retained cell at `⊤`, at
the stack `[qEnt]` at `1`. It meets every hypothesis of `CtxRelendableAtI`, and it is not shown to
arise. These are facts about the design's statements.

**The revision** (`BinderJ.lean`). `vRLJ` is `vRLI` with three changes. Each answers one refuted step,
none changes a printed BoLo definition, and nothing in `Core/` changes. `vRLJ` replaces `vRLI` as the
one draft relation at W; `vRLI` stays only as the design's refuted statement, and W₀ stays as before.
- **`RelendJ`: the extension keeps the retained part's records with their tags** (`KeepsT`).
  It answers `not_extInst`. `KeepsT` composes along instantiations (`ext_inst_comp`).
- **A retained `Mut` or `Imm` leaf reads its payload type at external lifetimes only**
  (`RetainedPay`, `PayExt`). It answers `not_mutPayloadInst`. At a bound place it is vacuous.
- **`SemSJ`'s index has its outermost lend below `⊤`** (`OuterBelowTop`). It answers
  `not_cohEInst`.

**Proved: `Statement0UThawFreeJ binder0`** (`statement0UThawFreeJ`). These are the four `U` rows at
`SemSJ`, the context's thaw at every `CtxThawFree` context (`ctxRelendsThawFreeJ`), and
`ThawInstJ` (`thawInstJ`).
- **The thaw of a slot** (`relendJ_value`), by the slot type:
  - `⊗`, `⊕`, `!`, `ref`: by the clause's closure under `⋆` and its monotonicity (`relendJ_sep`,
    `relendJ_mono`). A `mut` view is in at most one part (`GhostEnd.vwE_disj`). Two `imm` views join
    into one cell (`GhostEnd.vwE_join`), and an `imm` view handed at an instantiation splits back into
    two copies of itself by [TR] 6.43 (`ResU.compS_single_imm`, at `compS_self_single_imm`), which is
    the model step of 6.116's `I-dup`;
  - a box: the handed views stay above the instantiated bound (`vwSW_outlives_inst`);
  - `U`: `relendJ_thunk`, the composite of two instantiations (`instComp`, `ext_inst_comp`,
    `keepsSComp`);
  - `Mut`, `Imm`, retained: the cell lies above the outermost lend by the table, so the records it
    reads are fixed (`mem_above_cell`), and its payload is read at external lifetimes
    (`vC_mut_retained`, `vC_imm_retained`);
  - `Mut`, `Imm`, at a bound place: the cell is the innermost entry's view (the guard's
    `PlaceViewsL`), dropped and handed back, the payload types one type up to the reading (`CohS`,
    `tyEq_inst`), and coherence moved with its record (`cohE_inst`) (`vC_mut_bound`,
    `vC_imm_bound`);
  - data leaves hold nothing.
- **The rows** (`thunkF_U_J`, `thunkV_U_J`). The body comes from the premise at each instantiation.
  The index's facts are carried by the instantiation (`StackOK.inst`, `outerBelowTop_inst`,
  `stackJInst`, `subDom_inst`, `instModels`, `subOutsideInst`), and the table and views by
  `guardInst`. No `ReLendModels` hypothesis is left: the rows supersede `thunkFRow_binder0_at` and its
  siblings, which took `SemSR`.

**Not derived.** `Statement0UFullJ binder0`: the thaw at a `μ` or `fam` slot (`CtxRelendsAllJ`), the
guarantee gap R1 of §5.4. `ThawFreeScope` (stated, not attempted here) is the design's witness that
typing reaches such a context.

**What the revision owes** (none of it proved here; each is the next unit's):
- `RetainedPay` at every row that introduces a `Mut` or `Imm` value. [unchecked] A retained cell was
  made outside the frozen computation, so its payload type reads the variables bound then, which
  `SubOutside` reads above every lend.
- `KeepsT` at every consumer of the `U` clause. `[force]` supplies it at the list itself; the share
  at a resume is statement 2's.
- `OuterBelowTop` at every row that pushes a lend. The own lend meets it (`ownPushBelowTop`); 6.64's
  and 6.65's lends are chosen below a lifetime (H4).
- Statement 0's other facts at `SemSJ` (§5.5's re-proofs), not redone at `vRLJ`.

### 11.5 Statement 0 and OQ-8, reconsidered

- **The two needs statement 0 named as shared are met at `binder0`, at the revised relation
  `vRLJ`, at `CtxThawFree` contexts, conditional on `RetainedPay`, `KeepsT` and `OuterBelowTop`,
  which are owed** (§11.4), by changes to our definitions. `RetainedPay` moves `mut_not_natural`'s
  retained-part case (§11.3) out of the thaw and into every row that introduces a `Mut` or `Imm`
  value; it does not settle it. Q1, the context's thaw: PlaceViews in the guard and the views, `CohS`
  and `RetainedPay` at the leaves, and `KeepsT` at the extension. Q2, `Δ`'s models at a re-lend: the
  re-lend as an order-preserving instantiation keeps every `Δ`'s models (`reLendModelsI_of`). Both were
  findings about our definitions, as DESIGN §12.3's shared-reason clause reads them.
- **The result is partial.** Guarantee gap R1 (`μ`, `fam`) is open, and typing reaches contexts
  outside `CtxThawFree`. Under the top rule a result with a guarantee gap is partial, and no placement
  decision rests on it.
- **`binder0` still stops at its own monotonicity** (`MonoV`, `MonoG`, `MonoOwnG`, not derived and
  not retried at `vRLJ`).
- **OQ-8 stays undecided.** `cbpv` and `binder` still owe §5.6's list: `RelendUI`, `FutInst`,
  `MonoGPart`, the premise at a future's names, and `CallbackExt*` at `cbpv`. The revision's
  `KeepsT`, `RetainedPay` and `OuterBelowTop` join that list at every placement.
- **No failure occurred.** Nothing was refuted at a configuration shown to arise (a). No guard beside
  `TW` and no second relation family was added (b): the guard's facts are the local bundle, proved at
  distinct places, and `vRLJ` replaces `vRLI`. No clause reaches another stack by a new means (d).
  The fallback is not triggered.

### 11.6 Report lists (CLAUDE.md §5)

**Printed hypotheses spent.**
- [TR] 6.48 (`updV_frame`) at `pvwRun`; its technique (a `mut` cell of the aliasable walk accounted
  for by its immutable ancestor) at `pvlUpdN`.
- `↭`'s `mut` and `imm` clauses ([TR] p. 5, row 18) at `pvwUpd` and `pvlUpdN`.
- 6.65's and 6.64's opening cells at `pvwLendMut`, `pvwLendImm` and `pvlStart`; their closings at
  `pvlEnd`.
- 6.43 (`ResU.compS_single_imm`) at `vwEW_split`, through `compS_self_single_imm`: 6.116's (`I-dup`)
  model step. `ptoImm_dup` (6.116 itself) is not invoked.
- 6.36 (`ExS.immFree`), 6.32 (`ExS.toExR`), and 6.18 and 6.20 (`ExS.split`, `AgW.split`) at the
  fold lemmas.

**Still unspent.** 6.108–6.112 (`FreshFrameI` not attempted); 6.65's `P̂ ⊧ [β] P̂`; 6.64's `AdmWf`
and `hQ` at a resuming table; 6.66's premises; 6.150's H11 and H16; 6.149; 6.50 for the table; 6.62.

**Uniqueness and functionality results.**
- Used: `ResU.Flat.functional`, `ResU.CompS.functional`, `CellU.CompS.functional`,
  `CellU.CompR.functional` (`comp_get_det`), `ExS.functional`, `ExR.functional`, `AgW.functional`,
  `zip_unique_l` (one entry per place at distinct places), the strict monotonicity of
  `Restrat.Emb` (`life1_lt_iff`).
- Not used: the machine's determinism.

**Printed lemmas in the run-up that are untranscribed.** None of those read here. The block form of
6.112 (`freshI`, `FreshFrameI`) is ours, stated and not built.

**Hypotheses added, and their scope.**
- `KeepsT` at `RelendJ`'s extension: `Ext`'s `Keeps` with the tags kept. Consumers: §11.4.
  Satisfiable: it holds when the extension is the list itself (`keepsT_refl`).
- `RetainedPay` at `vRLJ`'s `Mut` and `Imm` leaves. It holds at a payload type with no free variable
  (`retainedPay_of_closed`) and at a bound place (`retainedPay_of_bound`). It excludes `not_mutPayloadInst`'s configuration, and whether such a
  retained cell arises is not decided.
- `OuterBelowTop` at `SemSJ`'s index and `CtxRelendableAtJ`. It excludes `not_cohEInst`'s
  configuration. An instantiation keeps it (`outerBelowTop_inst`).
- Distinct places, at `PVLUpdN` and `PVLRunsN`: an invariant of `ArisesI` (`placesNodupArises`), not
  of W's index.
- `CtxThawFree` at the partial result: R1, as before.

---

## Unresolved: the four review findings, and their status

The four findings below were given with this unit. The revision `99e921f` answers each in §10.2, and
the build checked the answer against the Lean. Whether the answers meet the findings has not been
reviewed again.

1. **The instantiation can move external readings** (`SubOutside`, `LendFresh`). Answered in §10.2
   items 1 and 10: the own lend is fresh below the reading (`SubFresh`), and the index carries
   `SubOutside`. Status: the readings' facts are proved (`subOutsidePush`, `subOutsideInst`,
   `subOutsideExtend`, `internalBoundInside`, `sharedReadFixed`), and the rows use `subOutsideInst`.
   Open: that every row of `SemSJ` keeps `SubOutside`, beyond the four `U` rows.
2. **`MutPayloadInst` is missing its support conjunct.** Answered in §10.2 item 2: `MutPayloadInst`
   states both conjuncts. Status: the build refuted the support conjunct as stated
   (`not_mutPayloadInst`), at a configuration not shown to arise, and with it `InstEquivLeaf`
   (`not_instEquivLeaf`). The revised W excludes the case at the leaf (`RetainedPay`). Open: whether
   such a retained cell arises (DESIGN §11's check), and `RetainedPay` at every row that introduces a
   `Mut` or `Imm` value.
3. **`RelendI`'s `Ext` can drop the stack's own records** (needs `KeepsS`). Answered in §10.2 item 9:
   `RelendI` asks `KeepsS` at the dropped views. Status: `KeepsSComp` is proved (`keepsSComp`). The
   build found that `Ext`'s untagged `Keeps` at the retained part does not compose along two
   instantiations either (`not_extInst`), and `RelendJ` adds `KeepsT`. Open: the share's `KeepsS` and
   `KeepsT` at a resume (statement 2).
4. **`LendFresh` does not put a lend below the reading** (needs `SubFresh`; cite 6.65's H4).
   Answered in §10.2 item 10, as finding 1, with 6.65's H4 cited ("Such an α always exists because for
   any lifetime, the set of lifetimes shorter than it is infinite") and 6.64's. Status: `SubFresh` is
   in the `∀` clause and `SubOutsidePush` is proved. Open: `RecsOutsideArises` and
   `RecsInsideOwnArises` at `ArisesI` are not attempted.
