# ProbeD1: the freeze binder at W — PlaceViews and the lifetime instantiation

**What this is.** The design of the unit after statement 0 of the D1 tractability probe (`DESIGN.md`,
`README.md`). Statement 0 stopped at the `U` introductions. Every placement owes them for two shared
reasons (DESIGN §15.3, §15.6): the context's thaw (Q1, the configuration `k`) and `Δ`'s models at a
re-lend (Q2, `q2_reached`). This unit reads both through the user's framing: "freeze is a binder over
internal locations, lifetimes and instances; resume and placement instantiate it". It fixes the two
halves of the binder that statement 0 needs:
- the location half: a place the stack lends is bound, and a value there is the binder's view
  (PlaceViews);
- the lifetime half: the re-lend at a resume instantiates every internal lifetime, preserving their
  order.

It fixes the Lean statements, the revision of W's clauses they enter, the proof plan, the arising check
for `mut_not_natural`, what success and failure look like, and what each outcome means for D1, OQ-8
and the fallback.

**The Lean.** `ProbeD1/Binder.lean` holds every definition and `def … : Prop` of this design, and
`lake build ProbeD1` elaborates it. It has no proof, and no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`. The revised clauses of W (§5.1) are code blocks here. They
elaborate against `Binder.lean`; this was checked in a scratch copy, which is not committed, because
revising W breaks proofs of the current W that the build redoes (§6). Statements over `vRL`, `gRL` and
`SemS` are read at the revised W.

**Worlds.** [W] is this probe's relation as §5.1 revises it. [W₀] is the relation as built
(`Relation.lean` at `b7c1a32`). [Core σ=[]] and [GE] are as in DESIGN.md. A result at one is not a
result at another.

**Rules this design keeps.** DESIGN.md's, unchanged:
- Nothing breaks the borrow calculus. No printed BoLo definition and nothing in `Core/` changes; the
  changes are to ProbeD1's draft W.
- The paper is not wrong. Every refutation the probe can produce is of a statement of ours.
- An obstruction is an elaborating `def … : Prop` whose negation is proved at a configuration that
  arises (DESIGN §11), with the closed program exhibited. Over-approximate arising is sound for proving
  and unsound for refuting.
- One relation at W; the placements are candidates for it. No relation family beside it. No
  step-indexing. Multi-shot is ignored.

---

## 0. On one page

| item | Lean (`ProbeD1.…`, `Binder.lean`) | what it settles |
|---|---|---|
| 1. PlaceViews | the invariant `PlaceViewsW`; its preservation `PVWNil`, `PVWUpd`, `PVWRun`, `PVWLendMut`, `PVWLendImm`, `PVWHide`, `ArisesInv`, `PVArises`, `PVLocal`, `KNotArises`; in W, `PlaceViewsAt` (guard), `CohS` (leaves), `vwEW`/`vwSW` (views), `OwnOK.placeFree` and `OwnPush`'s view shape (§5.1) | Q1: whether `k` arises; what the guard and the leaves give the thaw |
| 2. the lifetime binder | `cutOf`, `Inst`, `InstAt`, `Internal`, `InternalVar`, `BoundBelowV`, `InternalOfBound`, `InstModels`, `ReLendModelsI`, `Q2Inst`, `InstFresh`, `InstFreshExists`, `RelendI` (and `RelendUI`, next unit); bookkeeping `InstReLend`, `ExtSInst`, `InstComp`, `ExtInst`, `StackJInst`, `GuardInst`; equivariance `TyEqInst`, `ViewSlotInst`, `MutPayloadInst`, `InstEquivLeaf`, `ViewTypeCoincidence` | Q2: `Δ`'s models at every re-lend the clause ranges over; the equivariance the relation owes |
| 3. the known risk | `Targets.NotVDenNaturalArises`, `InternalPayloadArises`, `ViewSlotInst` at the witness; beside them `NotVCNaturalCore` | whether `mut_not_natural`'s witness arises, and whether it bears on an order-preserving instantiation |
| 4. the `U` introductions retried | `CtxRelendableAtI`, `CtxThawFree`, `ThawFree`, `CoreStable`, `CtxRelendsThawFree`, `ThawInst`, `ThunkFRowTF`, `ThunkVRowTF`, `BangThunkFRowTF`, `BangThunkVRowTF`, `Statement0U` | the four rows at `binder0` over instantiations; statement 0 and OQ-8 reconsidered |

**The decisions.**
- **PlaceViews enters W in three places**, and its run invariant is stated at a fourth.
  - The guard: `PlaceViewsAt`, a resource-level conjunct beside `TabAtS`.
  - The leaves: `CohS` at `Mut` and `Imm` at a stack place. This is the type tie the guard cannot see.
  - The own lend: `OwnOK.placeFree`, and `OwnPush` at a callback-shaped type.
  - The run invariant is stated at a configuration's world (`PlaceViewsW`). There [TR] 6.48 and
    `↭`'s clauses carry it.
- **The re-lend becomes an instantiation.** It is a re-stratification `Restrat.Emb c` at the stack's
  cut, acting on the reading substitution, the lend lifetimes, and the records' substitutions and
  frame lifetimes. No resource is transported, and the views are handed afresh at the instantiated
  reading.
- **`binder0`'s `U` clause becomes `RelendI` in this unit.** `cbpv` and `binder` keep `RelendU` until
  the next unit (§5.6).

**The order** (§6). First the relation-independent facts: they are cheap, and they decide whether the
rest is worth building. Then the revision of W, with the re-proofs. Then the rows.

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
- **Bound locations.** A place the stack lends belongs to the binder. The only value there is the
  lend's view, at the lend's payload type and lifetime. `k` is a value at a bound place that is not the
  binder's view: the location half is not enforced (Q1).
- **Bound lifetimes.** The lifetimes at or below the stack's outermost lend are the frozen
  computation's (§3.1). The re-lend that the `U` clause and the share quantify over moves the stack's
  own lifetimes and leaves everything else where it was. So a variable instantiated inside a lend,
  below a lend variable, keeps its old lifetime while the lend's moves below it (Q2).
- **Resume instantiates.** A resume picks fresh lifetimes beneath the resumer's ([TR] 6.112). It must
  move every bound lifetime together, preserving every order among them and to the unbound ones. A
  re-stratification below a cut (`Restrat.Emb`) does exactly that, and Restrat proves that `⟦Δ⟧` is
  invariant under it (`Restrat.Emb.models_mapN_iff`).

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
    which `↭` keeps. W's views, its guard and its leaves ask for the exact lifetime.
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
  frame lifetime) is read by Core's `Imm` leaf (`CohE`) and by `ptoImmS`'s record list. An
  instantiation moves the records' substitutions and frame lifetimes with everything else
  (`Inst.recs`). Otherwise an `Imm` slot's coherence fails after it.

### 1.4 What changes in W

| W₀ | W | why |
|---|---|---|
| `guardW σ αs P` (`TabAtS`) | `guardPV s σ αs ls P` (`TabAtS ∧ PlaceViewsAt s σ αs ls`) | Q1: the resource-level half of PlaceViews; the full payload of an `imm` view (§5.3) |
| leaves `Mut a T`, `Imm a T` at Core's `vC` | `vC … ∧ CohS σ αs (extS δ σ αs) A v` | (b), (c): the exact lifetime and the type tie at a bound place |
| `binder0`'s `U` clause, GhostEnd's `RelendableS` | `RelendI` | Q2, (a), (d): an instantiation in place of a re-lend; W's views |
| `OwnOK` | adds `placeFree : ρ.get e.l = none` | the own lend's place is fresh to the callback, its owner being with the lender; keeps `MonoOwnG` across `CohS` |
| `OwnPush` | adds `∀ A D, C' = .arr A D → ViewAt x e A` | the own lend is the lend the instance names: at a callback-shaped type its kind and payload are the view's |
| `FutOK` | adds `placesFree : ∀ e ∈ τ, ρ.get e.l = none` | keeps `MonoV`'s leaf case across `CohS` |
| `SemS`'s index | adds `PlaceViewsAt (extS δ σ αs) σ αs ls ρ` | the guard at the judgement's resource |
| `cbpv`/`binder`'s `RelendU` | unchanged in this unit; `RelendUI` in the next (§5.6) | keeps their proved facts while `binder0` is retried |

None of these is a printed definition, and none is in `Core/`.

---

## 2. PlaceViews in W (item 1)

### 2.1 The definitions

```lean
/-- The innermost entry lending the place `l`, with its current lifetime. -/
def innerAt (σ : LStack) (αs : List Life) (l : BoCa.Loc) : Option (LEnt × Life) :=
  (σ.zip αs).find? fun p => decide (p.1.l = l)

/-- PlaceViews at a configuration, read off the world's flattening. -/
def PlaceViewsW (σ : LStack) (αs : List Life) (fρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) →
    ∀ ψ : CellU BoCa.Loc Val, fρ.FlatAt l ψ →
      (e.k = .mut → ψ.kind = Kind.mut → ψ.at = α ∧
        ∃ (δ' : LSub) (ls₀ : List SRec), mutPred ψ = fun v => vC true e.T ls₀ δ' v) ∧
      (∀ u, e.k = .imm u → ψ.kind = Kind.imm → ψ.at = α ∧ ψ.erase = u)

/-- W's view of one entry: GhostEnd's, read at the reading `s`, its cell at exactly `α`. -/
def vwEW (s : LSub) (e : LEnt) (d : Bool) (α : Life) (ls : List SRec) : WProp := fun ρ =>
  vwE s e d α ls ρ ∧ ∀ ψ, ρ.get e.l = some ψ → ψ.at = α

def vwSW (s : LSub) : List BoCa.Loc → LStack → List Bool → List Life → List SRec → WProp
  | _, [], [], [], _ => emp
  | seen, e :: σ, d :: ds, α :: αs, ls =>
      vwEW s e (vis seen e d) α ls ⋆ vwSW s (e.l :: seen) σ ds αs ls
  | _, _, _, _, _ => fun _ => False

/-- W's guard conjunct. -/
def PlaceViewsAt (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind ≠ Kind.own →
    ∀ (e : LEnt) (α : Life), innerAt σ αs l = some (e, α) → vwEW s e true α ls (ResU.single l ψ)

def guardPV (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (P : WProp) : WProp :=
  fun ρ => TabAtS σ αs ρ → PlaceViewsAt s σ αs ls ρ → P ρ

def CohKind (s : LSub) (e : LEnt) : VTy → Prop
  | .mut _ T => (match e.k with | .mut => True | .imm _ => False) ∧ TyEq T s e.T s
  | .imm _ T => (match e.k with | .mut => False | .imm _ => True) ∧ TyEq T s e.T s
  | _ => False

/-- A view at a bound place is the binder's view: the 6.65 analog of Core's `CohE`. -/
def CohS (σ : LStack) (αs : List Life) (s : LSub) (A : VTy) (v : Val) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (e : LEnt) (α : Life), v = .loc l → innerAt σ αs l = some (e, α) →
    CohKind s e A ∧ ∀ ψ, ρ.get l = some ψ → ψ.at = α
```

The own lend and a future's step, revised (they replace the definitions in `World.lean`):

```lean
structure OwnOK (δ : LSub) (σ : LStack) (αs : List Life) (e : LEnt) (a : Life) (ρ : WRes) :
    Prop where
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : e.x ∉ σ.map LEnt.x
  place : e.l ∉ σ.map LEnt.l
  placeFree : ρ.get e.l = none
  pay : ∀ y, VFree y e.T → (extS δ (e :: σ) (a :: αs)).find? y ≠ none

/-- A callback's view type at its binder `x`, against the entry the own lend pushes. -/
def ViewAt (x : LifeVar) (e : LEnt) : VTy → Prop
  | .mut (.var y) T => y = x ∧ (match e.k with | .mut => True | .imm _ => False) ∧ e.T = T
  | .imm (.var y) T => y = x ∧ (match e.k with | .mut => False | .imm _ => True) ∧ e.T = T
  | _ => True

def OwnPush (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ e.x = x ∧
    x ∉ CTy.binders C' ∧ OwnOK δ s.1 s.2 e a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    ∀ A D, C' = .arr A D → ViewAt x e A

-- `FutOK` gains one field:
  placesFree : ∀ e ∈ τ, ρ.get e.l = none
```

**Three levels, one invariant.**
- **`PlaceViewsW`** is the run invariant, at a configuration's world `fρ`, read off the flattening
  `⦇fρ⦈`. `Arises` keeps it (§2.3). It asks only the invariant's shape (`∃ δ' ls₀`), because a
  configuration does not carry the clause's reading.
- **`PlaceViewsAt`** is the guard's conjunct, on the local resource, at the clause's reading
  `s = extS δ σ αs`. Each top-level borrow cell at a bound place must be the entry's view exactly as
  W's views give it (`vwEW s e true α ls`):
  - of the entry's kind;
  - at the entry's exact lifetime;
  - with payload `𝒱⟦e.T⟧` at `s`. For an `imm` cell this is the payload at the program's relation,
    as 6.64's lend frames it.
- **`CohS`** is the leaf's. A value of type `Mut a T` or `Imm a T` located at a bound place has the
  entry's kind, a payload type `TyEq` to the entry's at the reading, and its cell at the entry's exact
  lifetime.

`PlaceViewsAt` is per cell and sees no type. `CohS` is per value and sees the type. The thaw needs
both:
- `CohS` for the type tie and the exact lifetime of each slot's cell (§1.3 (b), (c));
- `PlaceViewsAt` for the full payload of an `imm` view, which a slot reads only at the observable
  view (§5.3).

### 2.2 How each enters W

The revised clauses are in §5.1. In short:
- every `guardW` becomes `guardPV` at the clause's reading and list;
- `vRL`'s `.mut` and `.imm` leaves conjoin `CohS`;
- `SemS`'s index adds `PlaceViewsAt` after `TabAtS`;
- the `∀` clause's own lend reads the revised `OwnPush`.

At `σ = []` `innerAt` is `none`, so `CohS` and `PlaceViewsAt` are vacuous and W's leaves are Core's.
`NilSoundRet` is unaffected.

### 2.3 PlaceViews along `Arises`: the statements

```lean
def PVWNil : Prop := ∀ W : WRes, PlaceViewsW [] [] W

/-- `↭` keeps PlaceViews: its `mut` clause keeps a `mut` cell's lifetime and invariant at the
flattening, its `imm` clause keeps an `imm` cell. -/
def PVWUpd : Prop :=
  ∀ (σ : LStack) (αs : List Life) (W W' : WRes), PlaceViewsW σ αs W → ResU.UpdV W W' →
    PlaceViewsW σ αs W'

/-- A run keeps PlaceViews: [TR] 6.48 carries the run's `↭` on the local part to the world. -/
def PVWRun : Prop :=
  ∀ (c c' : Cfg) (e t : Expr), ResU.Hash c.ρf c.ρ → ResU.CompS c.ρf c.ρ c.fρ →
    PlaceViewsW c.σ c.αs c.fρ → RunEnd (ℍ := ℍ) c e c' t → PlaceViewsW c'.σ c'.αs c'.fρ

def PVWLendMut : Prop :=
  ∀ (c c' : Cfg) (e : LEnt), ResU.Valid c.fρ → PlaceViewsW c.σ c.αs c.fρ → LendMut c c' e →
    PlaceViewsW c'.σ c'.αs c'.fρ
def PVWLendImm : Prop := …   -- the same at `LendImm`
def PVWHide : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (W : WRes), PlaceViewsW σ αs W →
    PlaceViewsW (hideS N σ) αs W

def ArisesInv : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c →
    ResU.Hash c.ρf c.ρ ∧ ResU.CompS c.ρf c.ρ c.fρ ∧ ResU.Valid c.fρ

/-- PlaceViews holds at every configuration that arises. -/
def PVArises : Prop := ∀ c : Cfg, Arises (ℍ := ℍ) c → PlaceViewsW c.σ c.αs c.fρ

/-- A top-level `mut` cell of a part of a valid world is the world's cell at its place. -/
def PVLocal : Prop :=
  ∀ (fρ ρf ρ : WRes), ResU.Valid fρ → ResU.CompS ρf ρ fρ →
    ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind = Kind.mut →
      fρ.FlatAt l ψ

/-- `k` does not arise. -/
def KNotArises : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c → c.σ = kσ → c.αs = [kα] → c.ρ ≠ kρ
```

### 2.4 The proof plan, and the printed technique each step spends

- **`PVWUpd`: `↭`'s clauses** ([TR] p. 5, row 18; `ResU.UpdV`).
  - At a `mut` cell of `⦇W'⦈` at a bound place, `ResU.UpdMut` read backwards gives a `mut` cell of
    `⦇W⦈` there with the same lifetime and the same stored invariant `P̂`. PlaceViews at `W` gives the
    lifetime and the invariant's shape. `mutPred` reads only `P̂` (`mutPred_mutOf`).
  - At an `imm` cell, `ResU.UpdImm` gives the identical cell: its lifetime set, value and witness.
  - No case analysis of ours is needed. `↭` is stated at the flattening, and so is `PlaceViewsW`.
- **`PVWRun`: [TR] 6.48**, `BoLo.updV_frame` (`TR.lemma_6_48`), then `PVWUpd`.
  - `RunEnd` gives `c.ρ ↭ π` with `π = c'.ρ ● ρp`, and, by associativity, `c'.fρ = c.ρf ● π`: the
    garbage `ρp` joins the frame (`ResU.CompS c.ρf ρp c'.ρf`).
  - 6.48 at `ρ₁ = c.ρf`, `ρ₂ = c.ρ`, `ρ₃ = π` gives `c.fρ ↭ c'.fρ`. Its hypotheses are
    `c.ρf # c.ρ` (`ArisesInv`) and `c.ρf # π` (from `✓c'.fρ`).
  - This is the place the brief's "spend 6.48's mut clause" lands. 6.48's own proof accounts for a
    `mut` cell of the aliasable walk by its immutable ancestor (`ResU.upd_ag_eq_of_ne_own`,
    `ResU.upd_ag_mut_eq`, `Support/Model/Ancestors.lean`). That accounting is inside `updV_frame`, and
    its conclusion's `mut` clause is what `PVWUpd` reads.
- **`PVWLendMut`: 6.65's opening** (`lendMut_placeView`), with the exact lifetime added.
  - The cell `LendMut` folds is `mutOf α v ρp hstr P hw`, at exactly `α`, and its invariant is the
    entry's view (`vwE δ e true α c.ls`).
  - At `e.l`: in `⦇c.fρ⦈` the place held `own(v)` in `ex`. Validity of `c.fρ` leaves no other cell
    there, because `own` composes with nothing under `●` and `⦇·⦈` is `ex● ● ag`. So `⦇c'.fρ⦈(e.l)` is
    the new view.
  - At every other place, a `mutFold` changes the flattening only at the folded place:
    `ex(ℓ ↦ mut(_, _, ρp, _)) = ℓ ↦ mut(…) ● ex(ρp)` and `ag(…) = ag(ρp)`, against
    `ex(ℓ ↦ own ● ρp) = ℓ ↦ own ● ex(ρp)` and `ag = ag(ρp)` ([TR] p. 5's `ex` and `ag`). This is a
    model lemma (`flat_fold_mut_ne`), from `ResU.Flat.split` and the `ExS`/`AgW` constructors.
  - The innermost entry changes only at `e.l` (`e.l ∉ c.σ.map LEnt.l`).
- **`PVWLendImm`: 6.64's opening**, likewise.
  - The new cell is `immOf {α} v R h`: lifetime `{α}.meet = α`, value `v = u` where `e.k = .imm u`.
  - At other places, the payload's `ex` cells move under the `imm` cell into `ag` (`ex(R)_○`). At a
    bound place their flattening cell is unchanged, because validity of `c'.fρ` leaves no other
    contribution there (`flat_fold_imm_ne`).
- **`PVWHide`** is immediate: `hideS` changes only `cross`, and `PlaceViewsW` reads `l`, `k`, `T`.
  **`PVWNil`** is immediate: `innerAt [] [] = none`.
- **`ArisesInv`** is by induction on `Arises`. Each constructor carries its conjuncts: `nil` its
  hypotheses; `run` `RunEnd`'s compositions, with `TW` worlds valid; `part` its hypotheses; `lendMut`
  and `lendImm` theirs; `hide` the same world.
- **`PVArises`** is by induction on `Arises`, with the recursor's `ArisesV`/`ArisesCtx` motives `True`.
  The cases use `PVWNil`, `PVWRun` with `ArisesInv`, the unchanged world at `part`, `PVWLendMut`,
  `PVWLendImm` and `PVWHide`.
- **`PVLocal`.** `ex` of a part is a `●`-factor of `ex` of the world (6.20, 6.18). A `mut` cell
  composes with nothing under `●`, so it is the world's flattening cell at its place. For an `imm` cell
  this fails: the world composes copies, so the statement is for `mut` only.
- **`KNotArises`** follows from `PVArises`, `ArisesInv` and `PVLocal` at `kCell`, then
  `not_placeViews_k`'s argument: `mutPred kCell = 𝒱⟦1⟧ ≠ 𝒱⟦Unk⟧ ls₀ δ'`, at `loc 0`.

**Why the world, and what the local form will owe.**
- Stated on the local part, PlaceViews is not kept by a run unless it also covers cells nested in
  witnesses. Such a cell surfaces when its parent is unfolded (6.66).
- At the local part's flattening, a part's `mut` cell under an `imm` ancestor can be `○`-composed with
  another, giving `P̂ ∧ Q̂`. The whole's PlaceViews then does not give the part's.
- At the world neither arises: there are no parts, and 6.48 lifts the run.
- Statement 1's relation-level run invariant (`TabRuns`'s analog for the guard) reads only the local
  part. It will need the deep local form, and the case analysis 6.48's proof makes: `ex` cells by
  `↭`'s `mut` clause, `ag` cells through their `imm` ancestor, and `○` idempotent at one stored
  invariant. That is recorded for statement 1 (§5.6), not built here.

### 2.5 Why the leaf as well as the guard

- A guard sees resources. `PlaceViewsAt` makes a bound place's cell the entry's view, so `k`'s
  argument fails the guard at the `⊸` clause (`not_placeViews_k`).
- It cannot make the slot holding that cell typed as the entry's payload. `ViewTypeCoincidence` is the
  machine check of that limit. Core faces the same limit for `imm` cells, and its answer is at the leaf:
  `CohE` in the `Imm` clause ties the payload type to a 6.64 record up to `TyEq`.
- `CohS` is the same tie for the stack's entries, the 6.65 records Core does not keep (OQ-44). `TyEq`
  compares lifetimes by their readings. An instantiation applied to both readings keeps it
  (`TyEqInst`), which is what makes the thaw's re-establishment syntactic rather than extensional
  (`ViewSlotInst`).
- **The exact lifetime** is asked in three places. The views give it. The guard asks it of each
  top-level cell, which for `imm` may be a composite of several slots' copies. The leaf asks it of each
  slot's own cell, which is what re-establishes the slot after an instantiation.

### 2.6 `k` under W

- Under W, `k`'s argument `r = loc 0 : Mut '0 1` is not related at the pushed stack: `CohS` asks
  `TyEq 1 Unk`.
- With the revised `OwnPush`, the own lend at `kC = ∀'0 ⊏ ⊤. Mut '0 1 ⊸ …` has payload `1`. So `k`'s
  entry, with payload `Unk`, is not an own lend there.
- So `k_reached`'s third conjunct (`k_slot`) is false at W. The build restates it as `k_slot_not_W`,
  and keeps the relation-independent facts about `k` (`k_world_TW`, `k_world_tagged`, `kρ_get`,
  `not_placeViews_k`).
- `KNotArises` is the arising answer to Q1: `k` does not arise. The refutation `not_ctxRelendable_binder0`
  was a fact about [W₀]'s statement, and the revision is the fix it pointed at.

---

## 3. The lifetime binder (item 2)

### 3.1 Internal lifetimes

```lean
/-- The cut of a stack: the lifetime just above its outermost lend. -/
def cutOf (αs : List Life) : Option Life :=
  αs.getLast?.map fun o => OrderDual.toDual (OrderDual.ofDual o - 1)

def Internal (αs : List Life) (a : Life) : Prop := ∃ o ∈ αs.getLast?, a ≤ o
def InternalVar (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar) : Prop :=
  ∃ m, (extS δ σ αs).find? y = some m ∧ Internal αs (OrderDual.toDual m)

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
  ∀ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (y : LifeVar),
    StackOK σ αs → Δ.Models (extS δ σ αs) → BoundBelowV Δ σ y → InternalVar δ σ αs y
```

**"Internal", made precise.**
- **The semantic definition is the one the clause uses.** A lifetime is internal to a stack when it is
  at or below the outermost lend. A variable is internal when the stack's reading sends it to an
  internal lifetime. `cutOf` is the lifetime just above the outermost lend. An instantiation at it may
  move the internal lifetimes and fixes every other one. The empty stack has no cut and nothing
  internal.
- **The task's description is `BoundBelowV`**: the stack's variables, and the variables of `Δ` whose
  bound reaches below one. The bound may reach through `⊓`, the shorter of two, by one operand. Through
  `⊔`, the longer, it needs both, because `'y ⊏ 'x ⊔ 'u` puts `'y` below the longer of the two only.
- **`InternalOfBound`.** At an index that models `Δ`, every `BoundBelowV` variable is internal. The
  proof is by mutual induction, with `Models` giving `δ(y) ⊏ u(δ)`, and `SLife.meet = max`,
  `SLife.join = min` on `ℕ`.
- **Why the clause uses the semantic set.**
  - The relation does not know `Δ`, and need not. An instantiation preserves every order among all
    lifetimes (`Restrat.Emb.lt_iff`), so `⟦Δ⟧` is invariant for every `Δ` (`models_mapN_iff`).
  - Moving a variable that is internal but not `BoundBelowV` therefore costs nothing at the models.
    Such a variable is, for example, an unbounded `∀` instantiated below the lend.
  - At the leaves it costs nothing either: a retained resource is above the cut (§3.6), and the views
    are rebuilt.

### 3.2 The instantiation

```lean
abbrev Inst := Option (Σ c : Life, Restrat.Emb c)

namespace Inst
def life1 : Inst → Life → Life   | none => fun a => a | some ⟨_, θ⟩ => θ
def life (ι : Inst) (αs : List Life) : List Life := αs.map ι.life1
def sub : Inst → LSub → LSub     | none => fun δ => δ | some ⟨_, θ⟩ => Restrat.LSub.mapN θ.toNat
def recs (ι : Inst) (ls : List SRec) : List SRec :=
  ls.map fun x => (⟨x.1.le, x.1.v, x.1.R, x.1.T, ι.sub x.1.δ⟩, ι.life1 x.2)
def ofEmb {c : Life} (θ : Restrat.Emb c) : Inst := some ⟨c, θ⟩
end Inst

def InstAt (αs : List Life) (ι : Inst) : Prop :=
  ∀ (c : Life) (θ : Restrat.Emb c), ι = some ⟨c, θ⟩ → cutOf αs = some c
```

- **What it is.** The identity, or a re-stratification `θ : Restrat.Emb c` at the stack's cut. `θ` is
  strictly monotone on all of `Life` (`Emb.strictMono`), lowering (`Emb.le_self`), and the identity at
  and above `c` (`Emb.fix`). So it preserves every `⊏` among internal lifetimes and from internal to
  external ones (`Emb.lt_iff`), and moves no external lifetime.
- **What it acts on.** The index only:
  - the reading substitution (`θ ∘ δ`);
  - the lend lifetimes;
  - every record's substitution and frame lifetime.

  External records and external values are fixed by `Emb.fix`. A record's substitution is moved by
  the same `θ` as the reading, so `TyEq` and `AgreeOn` between a reading and a record's substitution
  survive (`TyEqInst`, and its `AgreeOn` form, which `CohE` reads).
- **What it does not act on: resources.** A `U` value's retained part is strictly above the outermost
  lend (`stratS`), hence at or above the cut, and `θ` fixes every such cell (`Restrat.relRU_of_inStratum`,
  at the non-strict boundary). The views are dropped and handed afresh at the instantiated reading.
  This is Restrat's own repair of `mut_not_natural`: "Freeze, then re-lend… The re-lend at resume then
  builds the cell afresh with `𝒱⟦T⟧_{δ′}`." It is why the instantiation never meets that witness (§4).
- **A record's witness is kept.** A real re-lend at a resume rebuilds a 6.64 entry's record over the
  same payload, since the owner is frozen in the lender's frame. Only its substitution and frame
  lifetime change.
- **The lowering is non-strict in the `U` clause.** `Inst.life` is a `ReLend` of the stack
  (`InstReLend`), the identity included, so `[force]` reads the clause at `none`. The share's re-lend
  is strict on the ghost-ended entries (`openFS`'s `Forall₂ (· < ·)`). Its instantiation is a
  re-stratification at the ended part's cut, which is also one at the stack's cut, since a lower cut's
  `Emb` fixes everything a higher cut's does.

### 3.3 Freshness at a resume ([TR] 6.108–6.112)

```lean
def InstFresh (R : WRes) : Inst → Prop
  | none => True
  | some ⟨c, θ⟩ => ∀ a, a < c → R.InStratum (θ a)

def InstFreshExists : Prop :=
  ∀ (αs : List Life) (R : WRes) (c : Life), cutOf αs = some c →
    ∃ θ : Restrat.Emb c, InstFresh R (Inst.ofEmb θ)
```

- **What it is.** A resume instantiates the continuation's internal lifetimes fresh, beneath every
  cell of the resumer's resource `R`. It is [TR] 6.112's `И` at a block of lifetimes.
- **`InstFreshExists`** is `Restrat.Emb.shift c k` with `k` at least the largest `ℕ`-value of `R`'s
  cells' lifetimes (`R` is finite) and `Restrat.Emb.shift_fresh`. It is the block form of 6.112's
  "`P ⋆ Иα. Q(α) ⊧ Иα. ([α] P ⋆ Q(α))`" with `P` the resumer's resource:
  - 6.111 (`И⋆`) combines the share's freshness with the frame's;
  - 6.108 (`И`-mono) and 6.109 (`Иl`) carry and discharge it at the resume.
- **Where it is used: the share** (statement 2, §3.7). The `U` clause quantifies over every
  instantiation at the cut, fresh or not, as GhostEnd's quantifies over every re-lend. Freshness is the
  user's choice, not the clause's condition.

### 3.4 The `U` clause over instantiations

```lean
def RelendI (δ : LSub) (σ : LStack) (P : LSub → List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSW (extS δ σ αs) [] σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz →
      (vwSW (extS (ι.sub δ) σ (ι.life αs)) [] σ ds (ι.life αs) ls' ─⋆
        P (ι.sub δ) (ι.life αs) ls') ρz
```

- **What changes from `RelendableS`.**
  - The re-lend `∀ αs', ReLend αs' αs` becomes `∀ ι, InstAt αs ι`.
  - `P` takes the instantiated reading. The thunk's own type `C` is read at `ι.sub δ`, as the stack's
    variables in it are read at `ι.life αs`.
  - The views are W's, at the instantiated reading.
  - The list extension comes after the instantiation.
- **Why the extension comes after.** A record added after the instantiation need not be the image of
  one before it, since `θ`'s image has gaps. So "extend, then instantiate" would not compose. With
  "instantiate, then extend", an instantiation of an instantiated value is one of the original
  (`InstComp`), and its extension one of the original's (`ExtInst`, then `Ext.trans`). At `ι = none`
  this is GhostEnd's clause, the views apart.
- **`RelendUI`** (`Binder.lean`) is the same with `RelendU`'s futures after the instantiation. It is
  the next unit's (§5.6).

### 3.5 `Δ`'s models at an instantiation (replacing `BoundsStackFree`)

```lean
def InstModels : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (ι : Inst),
    Δ.Models (extS δ σ αs) → Δ.Models (extS (ι.sub δ) σ (ι.life αs))

def ReLendModelsI (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) : Prop :=
  ∀ ι, InstAt αs ι → Δ.Models (extS (ι.sub δ) σ (ι.life αs))

def Q2Inst : Prop := ReLendModelsI mΔ qδ [qEnt] [kα]
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
- **What it costs.** The `U` clause ranges over fewer re-lends than [W₀]'s: not every `ReLend` extends
  to a strictly monotone `θ`, because `ℕ` has gaps. Its uses need only these:
  - `[force]` at the identity;
  - a resume at a shift (`InstFreshExists`);
  - the thaw of a `U` slot inside another instantiation, by composition (`InstComp`).

### 3.6 The equivariance the relation owes

What the thaw needs of the relation at an instantiation comes in three parts. Nothing here asks
naturality under transport.
- **By construction**, for `U` slots. A `U` value's clause at the instantiated index is the original
  clause at the composite instantiation:
  - `InstComp`: lift the second `Emb` to the first's cut, then `Restrat.Emb.comp` (`Targets/I/Binder.lean`);
  - `ExtInst`: `Ext`'s `Keeps` reads no substitution (`Rel` reads `le`, `v`, `R`, `T`), and the
    records above a cell of a fixed resource have tags at or above the cut.
- **Views, rebuilt (`ViewSlotInst`).** A slot holding a bound place's view is re-established from the
  view handed at the instantiation:
  - `TyEqInst` (by induction on `TyEq`/`CTyEq`; lifetimes are compared by `interp`, and
    `Restrat.Emb.interp_mapN` applies);
  - `vC_tyEq` (`Core/RelationFacts.lean`);
  - the exact lifetime with `θ` monotone;
  - at `Imm`, `CohE.tyEq` at the instantiated record, and `ptoImmS_mono` with the full view implying
    the observable one (a small lemma, `vC_obs_of_full`).

  The dropped cell's stored invariant is never read.
- **Retained leaves (`InstEquivLeaf`, `MutPayloadInst`).** At a type Core reads without a thunk
  (`CoreStable`), at a resource the instantiation fixes, Core's relation holds at the instantiated
  reading and records. By induction on the type:
  - box: the reading only lowers, and the resource is above it;
  - `Imm`: `CohE` at the instantiated record; `ptoImmS`'s list has the same members above the cell,
    the tags there being fixed; the payload by induction, the witness being fixed and above the cell;
  - data: immediate;
  - `Mut`: `MutPayloadInst`, the crux.

  ```lean
  def MutPayloadInst : Prop :=
    ∀ (T : VTy) (ls₀ : List SRec) (s : LSub) (b c : Life) (θ : Restrat.Emb c), CoreStable T →
      c ≤ b → (∀ ls' u σ', vC true T ls' s u σ' → σ'.InStratum b) →
      ∀ u σ', vC true T (Inst.recs (Inst.ofEmb θ) ls₀) (Inst.sub (Inst.ofEmb θ) s) u σ' ↔
        vC true T ls₀ s u σ'
  ```

  A retained `mut` cell is above the cut, `c ≤ b`, and `ptoMutS` asks its payload's relation supported
  in `Res_b`. The argument [unchecked]:
  - every lifetime Core's relation reads at a `CoreStable` type is a lower bound on a cell (`Imm`,
    `Mut`, `[@a]`);
  - support in `Res_b` forces every satisfiable such bound at an internal reading to be dominated by
    one at or above the cut;
  - lowering the internal readings then changes no satisfiable constraint.

  The proof carries "the subterm's relation is supported" down the induction, with satisfiability
  invariant under `θ`, because no constraint is an upper bound.

  This is exactly `mut_not_natural`'s shape at an instantiation. If it fails, §7 says what follows.
- **Where it stops: `μ` and `fam`.** W hands them to Core's relation whole, and Core's `U` clause reads
  its argument contravariantly. At an instantiated reading, a closure inside a `μ` value owes its
  behaviour at arguments with cells below the old lifetimes, which the original does not give. That is
  the naturality of `wp` at a moved argument, which Restrat leaves open (`WpNatural`). `ThawFree` therefore
  excludes `μ` and `fam` outside a thunk, and `CoreStable` excludes thunks inside `Mut` and `Imm`
  payloads. The discharge is W reading `μ` and `fam` itself, so that a `U` inside is W's clause (§5.4).
- **The bookkeeping the rows read**:
  - `InstReLend`: `Emb.le_self`, `Emb.strictMono`;
  - `StackJInst`: `Restrat.Emb.ltLife_mapN_iff` with `ExtSInst`;
  - `GuardInst`: `tabRelend`'s argument at the re-lend `ι.life αs`; and `PlaceViewsAt` at the
    composite, where `ρz` holds no `mut` cell at a bound place (such a cell is at its entry's internal
    lifetime, and `ρz` is above the outermost lend), and an `imm` composite's meet is the fresh view's;
  - `ArisesInv`.

**Its relation to `FreezeBinderLife`.** `Targets.FreezeBinderLife` states the binder's lifetime half
as forward transport along `Restrat.Emb`: the index, the resource (`θ.relRU`) and the predicates
together. What W needs is narrower in one way: it acts at resources the instantiation fixes, plus views
rebuilt. It is not implied by transport, because the views are not transported but rebuilt.
`NotVCNaturalCore` (§4) says transport fails at Core's relation. So T3's lifetime half, as Targets
states it, is the wrong form for D1. The form here is the one the ghost-end re-lend realises. This
bears on the target, not on the probe's statements.

### 3.7 The share (statement 2's, recorded)

- **The same Q2 meets GhostEnd's `OpenS`.** `openFS` re-lends the ghost-ended entries
  (`∀ αi', Forall₂ (· < ·) αi' αi → …`) with `δ` fixed. A stop inside `Λ'1 ⊏ '0` within a lend of `'0`
  that ghost-ends `'0` owes its continuation at a re-lend breaking `'1 ⊏ '0` [unchecked].
- **The fix.** The share's re-lend becomes an instantiation at the ghost-ended part's cut: strict on
  the ended entries, fixing the kept part (which is above that cut), with W's views and the records
  instantiated. The resume picks it fresh (`InstFreshExists`).
- **`TabResume`'s analog** is the composite's table and views at the fresh instantiation.
- Statement 2 restates `OpenS` and `OpenSF` this way before its rows. Nothing here builds it.

---

## 4. The known risk: `mut_not_natural` (item 3)

### 4.1 The witness and what it refutes

`Restrat.MutCounterexample.mut_not_natural`:
- `e = Emb.shift ⊤ 1`;
- `T = Mut 'a (Imm 'b 1)`;
- `δ = ['a ↦ 3, 'b ↦ 1]`;
- `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)`.

`𝒱⟦T⟧_δ(ℓ)(ρ₀)` holds, and `𝒱⟦T⟧_{e∘δ}(ℓ)(e·ρ₀)` fails. It refutes naturality of `𝒱⟦·⟧` under the
transport `e·` of a resource whose `mut` cell lies below the cut. It says nothing about a resource the
map fixes, or a view rebuilt rather than transported. DESIGN §10 planned this check as statement 7;
this unit brings it forward.

### 4.2 Does the witness arise?

**At Core σ=[] (`Targets.NotVDenNaturalArises`).** The expected outcome is that it arises. This is
unchecked, and the build proves or refutes it. The `TW` history, constructor by constructor:
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

Take `fρ = ρ₀`, `ρf = ∅`. If a premise fails (`Tagged` reading `ag` through the `mut` witness is the
step to watch), the report says which. Then the witness does not arise, as the README suspected, and
it bears on nothing.

**At W, both lends on the stack (`InternalPayloadArises`).** The shape the witness needs is a 6.65
entry whose payload mentions a 6.64 entry's variable, both internal at the stack's cut. The `Arises`
path:
1. `Arises.nil` at a world holding `ℓ′ ↦ own(())`.
2. `Arises.lendImm` at `ℓ′`: entry `b`, kind `imm ()`, payload `1`, lifetime `L 1`, the record added.
3. `Arises.run` of `alloc i`, where `i`'s value is `b`'s view (`ArisesV.view` at `Imm 'b 1`), ending
   with `ℓ ↦ own(loc ℓ′) ● ℓ′ ↦ imm({L 1})`.
4. `Arises.lendMut` at `ℓ`: entry `x`, payload `Imm 'b 1`, lifetime `L 2`.

The cell is `vwE δ x true (L 2) ls`, Core's `𝒱⟦Imm 'b 1⟧` at `δ`, which holds at `ℓ′ ↦ imm({L 1})` with
`b`'s record (`CohE`). The closed program is
`withbor1 (alloc ()) (Λ'b. λi. withbor2 (alloc i) (Λ'x. λm. …))` under `ProbeRules`.

The term-tracked reading DESIGN §11 asks of an obstruction is not needed here: this path is evidence
that the shape is reachable, not a refutation. The expected outcome is that it arises [unchecked].

### 4.3 Does it apply to an order-preserving instantiation of internal lifetimes?

**No, by construction, and the build checks the instance.**
- At `InternalPayloadArises`'s configuration the stack is `[x, b]` at `[L 2, L 1]`, so
  `cutOf = some ⊤`. Then `Restrat.Emb.shift ⊤ 1`, the witness's own `e`, is an instantiation of that
  stack (`InstAt`).
- The slot `m : Mut 'x (Imm 'b 1)` holds `x`'s view. Under `RelendI` that view is in the dropped part
  `ρn`: it is at a bound place, at its entry's internal lifetime, and `ρz` is above the outermost lend.
- At `e`, the view handed is `vwEW (e ∘ s) x true (e (L 2)) ls'`: a cell built afresh with
  `𝒱⟦Imm 'b 1⟧` at the instantiated reading.
- `ViewSlotInst` re-establishes `m` from it, by `TyEq` and the exact lifetime. The build proves this
  instance as `mutWitness_thaws`.
- The image of the old invariant, the thing `mut_not_natural` is about, is never formed.

**The retained part never meets it.**
- A `U` value's retained cells are strictly above the outermost lend, hence at or above the cut, and
  `θ` fixes them (`Restrat.relRU_of_inStratum`).
- A `mut` cell there has a supported payload, and re-reading that payload at the instantiated reading
  is `MutPayloadInst`: the witness's question without the move.
- If the witness were retained, its cell at `2` and its payload's `1` would both be above the cut,
  since the outermost lend would be at or below `3`. The instantiation would fix both.

**Transport is where it applies (`NotVCNaturalCore`, beside).** Transcribe `mut_not_natural` at Core's
`vC`. The inner `Imm` leaf's `CohE` needs `r′` in the list, and the gap argument is unchanged. That
gives Core's relation not natural under transport at a configuration whose world arises. It is
evidence against T3's lifetime half as `Targets.FreezeBinderLife` states it, and against OQ-8 option 1
(naturality).
- It decides option 1 only with DESIGN §11's full check: the value arising, and the program and its run
  exhibited. That reading is not written here.
- It bears on no placement of the probe.

### 4.4 What each outcome means

| `NotVDenNaturalArises` | `ViewSlotInst` and `MutPayloadInst` | reading |
|---|---|---|
| proved | proved | The witness arises, and D1's instantiation is unaffected by it: the cell is rebuilt, and a retained one is fixed. Transport (option 1, `FreezeBinderLife` as stated) is the form it refutes. |
| proved | `MutPayloadInst` refuted | Build the refuting `T`, `s`, `b`, `c` and run DESIGN §11's arising check on a retained cell with such a payload. If it arises, a retained `Mut` leaf is not stable under instantiation. D1's lifetime half then needs the retained part re-lent too, not fixed, which is D3's carried-lend shape (§8). If it does not arise, it is a fact about `MutPayloadInst`'s statement, and the guard needs the conjunct that excludes it. |
| refuted (a premise fails) | proved | The witness does not arise at Core's world. `mut_not_natural` is a fact about Restrat's statement only, as the README suspected, and nothing follows for D1 or option 1. |

---

## 5. The `U` introductions retried (item 4)

### 5.1 The revised W

```lean
mutual
def vRL (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRL p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendI δ σ (fun δ' αs' ls' => cRL p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  …                                   -- ⊗, ⊕, !, [@a], Ref as now
  | σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.mut a T) v ρ
  | σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.imm a T) v ρ
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
def cRL (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  …                                   -- F, F_Σ, &, ⊤, ν as now
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRL p σ' δ A αs' ls' v ─⋆
            guardPV (extS δ σ' αs') σ' αs' ls' (cRL p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ' αs') σ' αs' ls'
            (cRL p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPush δ (.all x c C) ρ (σ', αs') en α →
          guardPV (extS (δ.extend x α) (en :: σ') (α :: αs')) (en :: σ') (α :: αs') ls'
            (cRL p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
end

def SemS (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    TabAtS σ αs ρ → PlaceViewsAt (extS δ σ αs) σ αs ls ρ →
    gRL p σ δ αs ls Γ γ ρ → cRL p σ δ (jdgCty j) αs ls (substAll γ e) ρ
```

The block stays one `mutual` definition, structural on the type. The two new leaf cases come before
the default. `OwnOK`, `OwnPush` and `FutOK` are as in §2.1. `guardPV`, `PlaceViewsAt`, `CohS`,
`vwSW` and `RelendI` move from `Binder.lean` to `World.lean` and `Relation.lean` when the revision
lands.

### 5.2 The statements

```lean
def CtxRelendableAtI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → TabAtS σ αs ρ →
    PlaceViewsAt (extS δ σ αs) σ αs ls ρ → gRL p σ δ αs ls Γ γ ρ →
    RelendI δ σ (fun δ' αs' ls' => gRL p σ δ' αs' ls' Γ γ) αs ls ρ

def CtxRelendsThawFree (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFree Γ → CtxRelendableAtI p Δ Γ

def ThawInst (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ → PlaceViewsAt (extS δ σ αs) σ αs ls ρ →
    vRL p σ δ (.thunk C) αs ls f ρ →
    RelendI δ σ (fun δ' αs' ls' => vRL p σ δ' (.thunk C) αs' ls' f) αs ls ρ

def ThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
def ThunkVRowTF (p : Placement) : Prop := …      -- `thunkV`, with `C.isRet = false`, `OwnHyg`
def BangThunkFRowTF (p : Placement) : Prop := …  -- `bangThunkF`, with `Persistent Γ`
def BangThunkVRowTF (p : Placement) : Prop := …  -- `bangThunkV`, with `Persistent Γ`, `OwnHyg`

def Statement0U (p : Placement) : Prop :=
  ThawInst p ∧ CtxRelendsThawFree p ∧ ThunkFRowTF p ∧ ThunkVRowTF p ∧ BangThunkFRowTF p ∧
    BangThunkVRowTF p
```

- **The rows are statement 0's** (`ThunkFRow` …), with `CtxThawFree Γ` added: every live slot's type
  is `ThawFree`.
- **That hypothesis is a guarantee gap, stated, of `BindersLow`'s kind.** FL at W says nothing about a
  thunk over a `μ` or `fam` slot inside a lend. Its discharge is §5.4's. Both programs' contexts meet
  it: `genSelf`'s state is `Flag`, and `reconB′`'s payloads are `Flag`.
- **The rows conclude at `SemS`, not `SemSR`.** `ReLendModels` is gone from the index: Q2 is met by
  the instantiation, not assumed.

### 5.3 The proof plan

**`thunkF_U_binder0I`** (then `ThunkFRowTF .binder0`), following `thunkF_U_binder0`, step by step:
1. Unfold `vRL` at `U` at `binder0`: `guardPV`, then `RelendI`. The guard's hypotheses `TabAtS` and
   `PlaceViewsAt` at `ρ` are the index's.
2. `CtxRelendableAtI` at the row's context gives the split `(ds, ρz, ρn)` and the thaw `H`.
3. For `ι` (`InstAt αs ι`), `ls'` (`Ext (ι.recs ls) ls' ρz`), and views `ρv` at the instantiated stack
   with `τ = ρz ● ρv`: call the premise `SemS` at `(ι.sub δ, σ, ι.life αs, ls', () :: γ, τ)`. Its
   hypotheses:
   - `BindersLow` and `Scoped`: the row's, unchanged;
   - `StackOK`: `InstReLend`;
   - `StackJ`: `StackJInst`;
   - `SubDom`: `mapN` keeps keys (`Restrat.LSub.find?_mapN`);
   - `Models`: `InstModels`;
   - `TabAtS` and `PlaceViewsAt`: `GuardInst`;
   - the context: `H`.
4. Close with `wpTS_step` at the `β`-step, as now.

`thunkV` is the same, at `forceE_of_not_ret`. The `!` rows are the same at `ρ = ∅`, by
`gSepRL_persistent`.

**`CtxRelendsThawFree .binder0`, the thaw.**
1. **Split.** `ρn` is every top-level non-`own` cell of the context's resource at a bound place.
   `PlaceViewsAt` makes each one a W view of its entry (`vwSW` at `ds`: true where the context holds
   the entry's view, shadowing as `vwS`). `ρz` is the rest.
   - `stratS αs ρz` holds: `TabAtS`'s second conjunct for cells off the stack's places; `own` cells are
     `⊤`.
2. **Per slot**, by W's clause on the slot's type (`ThawFree`):
   - `U`: by construction, at the composite (`InstComp`, `ExtInst`).
   - `⊗`, `⊕`, `!`, `Ref`: componentwise.
   - `[@a]`: the box's reading and the views' exact lifetimes move together under `θ`, which is
     strictly monotone.
   - `Mut`/`Imm` at a bound place: `ViewSlotInst`, fed by `CohS` (type, exact lifetime). For `Imm`, the
     full payload comes from `PlaceViewsAt` at the composite cell, since the slot reads only the
     observable one.
   - `Mut`/`Imm` off the stack's places, and data: `InstEquivLeaf` at the retained resource. `CohS` is
     vacuous there, and the place stays unbound, since `ι` does not touch `σ`.
3. **Across slots** (`relendI_sep`, the stacked `relendable_sep`):
   - at most one slot holds a `mut` view (`dropC_disj`);
   - an `imm` view held by several slots is one composite cell, dropped once, and the fresh view is
     split back by [TR] 6.116 (I-dup) and 6.43, since `imm(s) ● imm(s) = imm(s)`.

**`ThawInst .binder0`**: `RelendI` at the composite instantiation (`InstComp`, `ExtInst`), as
`thawRelend` and `relendableS_thunkA` do at a re-lend.

### 5.4 What is not covered, and how it would be

- **R1. `μ` and `fam` slots** (`ThawFree`).
  - Route: W reads `μ` (least fixed point over W's own clauses, as `vCE` does over Core's) and `fam`
    itself. A `U` inside is then W's clause, instantiated by construction, and a view inside is
    `CohS`-checked.
  - A cheaper first step: admit `μ`/`fam` whose body is `CoreStable`. `InstEquivLeaf` then needs only
    `vC_mu_ind` at a fixed resource.
- **R2. An `imm` reborrow's entry (`withload`) with the outer view still held.** `vwS`'s shadowing
  hands only the innermost entry's view at a place, while an `imm` copy of the outer one is
  duplicable. Statement 2's `SpanLoadRow` "entry-kind finding" decides whether `withload` pushes an
  entry. Neither program holds an outer copy across a `withload`.
- **R3. The share.** §3.7.

### 5.5 Statement 0's other facts at the revised W

| fact | at W | how |
|---|---|---|
| `statement0Shared` | re-proved | `FutPart` with `placesFree` (a part holds fewer cells); `NilSoundRet` with `CohS`/`PlaceViewsAt` vacuous at `[]`; the rest unchanged |
| `ForceRow` | re-proved | `binder0`: `RelendI` at `none`, the split's views handed back; `cbpv`/`binder` unchanged |
| `ThawRelend` | `binder0`: `ThawInst`; others unchanged | composition |
| `CallbackExtMut`/`Imm` | re-proved with hypotheses added | `e.T = T` (the argument's `CohS`), `placeFree` (`OwnOK`), `PlaceViewsAt` at `e :: σ` beside `TabAtS` (the lend's view, exact): each a property of the borrow constant's real lend |
| `MonoV`, `MonoG`, `MonoOwnG` at `cbpv`/`binder` | re-proved | the leaf case: `CohS` along a future, since `placesFree` keeps the value's place unbound and existing places' entries and lifetimes are unchanged; the guard's views at a future likewise (`placeViewsAt_fut`); `ownPush_futStep` with `placeFree` |
| `MonoV`, `MonoG`, `MonoOwnG` at `binder0` | not derived, as before | the `U` clause still ranges over the stack itself; `MonoC binder0` |
| `thunkFRow_binder0_at` … (at `SemSR`) | superseded | by `ThunkFRowTF .binder0` at `SemS` |
| `k_slot`, `k_gRL`, `k_index`, `k_reached`, `k_thunk_not_vRL`, `not_ctxRelendable*` | statements about [W₀] | restated as `k_slot_not_W` (§2.6); the relation-independent `k` facts kept; the [W₀] outcome stays recorded in DESIGN §15.6 |

### 5.6 Statement 0 and OQ-8, reconsidered

**What this unit can decide, and what it cannot.**
- **If `Statement0U .binder0` is proved, the two needs DESIGN §15.3 named as shared are met.** They
  were the context's thaw and the models at a re-lend. They are met by changes to our definitions:
  PlaceViews in the guard, the leaves and the own lend, and the re-lend as an instantiation.
  - Under the stop rule's shared-reason clause (DESIGN §12.3) they were findings about our
    definitions, and they are now closed at the contexts `ThawFree` admits.
  - Statement 0 at `binder0` still stops at `MonoV`/`MonoG`/`MonoOwnG`, not derived, for `binder0`'s
    own reason. So `binder0` does not proceed to statement 1.
- **OQ-8 stays undecided.** W is neither decided nor provisional. The comparison now rests on each
  placement's own needs.
- **What `cbpv` and `binder` still owe in the `U` rows** (the next unit; each is a named statement
  there, none built here):
  1. **`RelendUI` in place of `RelendU`.** The same instantiation, then the futures.
  2. **`MonoV` along a future at `RelendUI`, which needs `FutInst`:** an instantiation of a future is
     a future of an instantiation. [unchecked] At a future that inserts outside the outermost lend
     (depth `|σ|`), the new cut is higher. An instantiation there may move values the original's cut
     fixed. The candidate fix is a `FutOK` field putting the inserted lifetimes below every external
     lifetime in play (6.112's `И` taken below the finite set). Then no reading or record lies in the
     band between the old cut and the new, and the new instantiation truncated at the old cut is one of
     the original (`Restrat.Emb` truncated stays strictly monotone and lowering).
  3. **The context at a future of the instantiated stack: `MonoGPart`**, `MonoG` with the future taken
     at the part above the outermost lend. At the whole resource, `FutOK.below` fails once an insertion
     at depth `k > 0` puts its lifetimes above the re-lent views (DESIGN §15.3).
  4. **The premise at a future that inserts a name other than `NsVar`.** `StackJ` must admit it with a
     hygiene the row can discharge, or the renaming lemma (DESIGN §2.2, *Names*).
  5. **At `cbpv`, `CallbackExt*` when the bound mentions the binder** (`callbackExtMut_cbpv_of`'s
     restriction).
- **What would decide OQ-8.** `Statement0 cbpv` proved at the revised W, with the rows at `ThawFree`
  contexts, lets the probe proceed at `cbpv` to statements 1–6 and the programs. If `cbpv` then
  survives (`Survives`), W = `cbpv` is decided, since rank 0 has no placement before it (DESIGN §3).
  That is OQ-8 option 2, and D1 meets "interactions only at cuts", with the own lend's cost at `U`
  (DESIGN §4.4). A refutation passing DESIGN §11 at `cbpv` moves the question to `binder`.
- **Failure (d)** in either reading: neither the instantiation nor `CohS` adds a way to reach another
  stack.
  - The instantiation generalises the `U` clause's existing re-lend at the same clause. It is not a
    second quantifier.
  - `CohS` reads the index, as Core's `CohE` reads the records.

---

## 6. Order of work and the build

Unknowns first. Each step names the decision it feeds.

1. **The relation-independent facts.** No change to W is needed for any of these.
   1. `ExtSInst`, `InstModels`, `Q2Inst`, `InstReLend`, `InstComp`, `StackJInst`, `TyEqInst`,
      `InternalOfBound`, `InstFreshExists`. This is bookkeeping over `Restrat.Emb`; a failure is a
      finding about these definitions.
   2. `ViewTypeCoincidence`. It confirms that the guard alone cannot carry the type tie (§2.5). If it
      is refuted, `CohS`'s type conjunct is not needed for (c), only for `imm` coherence, and §5.1
      keeps it for that.
   3. `ViewSlotInst`, at `Mut`, then at `Imm`.
   4. `NotVDenNaturalArises`, the `TW` history of §4.2.
   5. **`MutPayloadInst`, then `InstEquivLeaf`.** This is the crux of the retained part. If it is
      refuted, stop the rows, and run DESIGN §11 on the refuting configuration (§4.4).
   6. The PlaceViews facts: `PVWNil`, `PVWUpd`, `PVWHide`, the model lemmas `flat_fold_mut_ne` and
      `flat_fold_imm_ne`, then `PVWLendMut`, `PVWLendImm`, `PVWRun`, `ArisesInv`, `PVArises`,
      `PVLocal`, `KNotArises`. If a transition is not kept, it is failure (b); stop and report.
   7. `InternalPayloadArises`, `mutWitness_thaws`, and `NotVCNaturalCore` (beside).
2. **The revision of W** (§5.1), in `World.lean`, `Relation.lean` and `Sem.lean`.
   - Re-prove §5.5's facts.
   - Every statement that takes the guard's `TabAtS σ αs ρ` as a hypothesis takes
     `PlaceViewsAt (extS δ σ αs) σ αs ls ρ` beside it: `MonoV`, `MonoG`, `MonoOwnG`, `MonoC`,
     `MonoHide`, `ThawRelend`, `CallbackExt*`. `BelowExcluded` reads `guardPV`. Statement 1's
     per-transition facts gain their `PlaceViewsAt` analogs when statement 1 is reached (§2.4).
   - Restate `k_slot_not_W`.
   - Move `Binder.lean`'s W-level definitions into the files they belong to.
3. **The rows**: `GuardInst`, `ExtInst`, then `relendI_sep` and `CtxRelendsThawFree .binder0`, then
   `ThawInst .binder0` and the four `…TF .binder0` rows. That gives `Statement0U .binder0`.
4. **Report**: README, CHECKPOINT and DESIGN §15 updated with the outcome; this file's §5.6 list as the
   next unit's brief.

**The build.** Iterate with `lake build ProbeD1.<Module>`, and run `lake build ProbeD1` at milestones.
- Every theorem's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.
- No `sorry` or `axiom` lands. An unproved step in progress is an enumerated `sorry` in a scratch file,
  never committed.
- No `Core/` edit. Work on `targets`; never push.

---

## 7. Success and failure

**Item 1 (PlaceViews).**
- **Success**: `PVArises` and `KNotArises` proved, and `k_slot_not_W` at W. Then `k` does not arise,
  and Q1's refutation was a fact about [W₀].
- **Failure**: a transition of `Arises` does not keep `PlaceViewsW`, shown by a configuration with its
  hypotheses discharged. PlaceViews is then not W's run invariant, and a guard carrying it is beside
  `TW`: failure (b). Stop and report.

**Item 2 (the lifetime binder).**
- **Success**: `InstModels`, `Q2Inst`, `InternalOfBound`, `InstFreshExists`, the bookkeeping,
  `TyEqInst`, `ViewSlotInst`, `MutPayloadInst` and `InstEquivLeaf` proved. Then Q2 is met at every
  instantiation the clause ranges over, and the relation's equivariance is what §3.6 states.
- **Failure**: `MutPayloadInst` or `InstEquivLeaf` refuted.
  - If the refuting configuration passes DESIGN §11, it is failure (a) for the `U` rows at `binder0`.
  - If not, it is a fact about the statement, and the guard needs the conjunct that excludes it. Name
    the conjunct, and check that the transitions keep it (§4.4).

**Item 3 (the known risk).** §4.4's table.
- `ViewSlotInst` at the witness (`mutWitness_thaws`) is the success that matters for D1.
- `NotVDenNaturalArises` either way is a recorded fact.

**Item 4 (the rows).**
- **Success**: `Statement0U .binder0` proved, with §5.5's re-proofs.
- **Partial**: the rows proved given `CtxRelendableAtI`, with the thaw not derived at some `ThawFree`
  slot type. Report the type and the step it stopped at.
- **Failure**:
  - (a) a row refuted at an arising configuration (DESIGN §11);
  - (b) a guard beside `TW`, or a second relation family;
  - (d) a clause changed to reach another stack by other means.

A statement neither proved nor refuted is reported as "not derived, no obstruction verified", with the
step it stopped at.

---

## 8. What each outcome means for D1, OQ-8 and the fallback

- **All four items succeed.**
  - Both of statement 0's shared needs are met by changes to our definitions. Each was named by the
    binder reading: a bound place's value is the binder's view, and a resume instantiates every bound
    lifetime, preserving order.
  - D1's ghost-end route has its lifetime half: an instantiation that transports no resource,
    rebuilds the views, and keeps every `⟦Δ⟧`.
  - D1's tractability then rests on the per-placement needs §5.6 lists, which are not shared.
  - OQ-8 is undecided until `cbpv`'s rows are retried. Nothing here is evidence for D3 or D0, and
    nothing is evidence against them.
- **`MutPayloadInst` fails at an arising configuration.**
  - A retained `mut` cell's payload is not stable under the instantiation. So the frozen part cannot
    be left in place while its lifetimes move.
  - The binder's lifetime half then has to re-lend more than the views, and the retained part stops
    being fixed. D3's carried lends avoid the question: the closure keeps its lifetime across the
    stop, and nothing is instantiated [unchecked].
  - This is evidence for D3 against D1's re-lend. It is not by itself the machine-checked failure
    that triggers the fallback. That needs a row of `Probe p` refuted at an arising configuration
    (DESIGN §12.2 (a)) at every placement whose statement 0 holds.
- **PlaceViews is not kept by a transition (failure (b)).**
  - The probe stops. The guard cannot be W's run invariant read from `TW`'s runs.
  - D1's route needs another way to exclude `k`, and the report says which transition failed.
  - The fallback order stands: D3, then D0. D3 keeps lends open across stops, so its views persist
    and a PlaceViews-like coherence would be needed there too [unchecked].
- **The rows refuted at an arising configuration (failure (a)).**
  - The `U` introductions are refuted at `binder0`.
  - With `cbpv` and `binder` still owing theirs, this decides nothing for OQ-8 yet. It decides
    `binder0` against itself, and a placement before W counts only by such a refutation (DESIGN §3).
- **`mut_not_natural`.** Whichever way §4.4's table falls, D1's instantiation does not need
  naturality: views are rebuilt, and retained cells are fixed. What the witness can refute is transport
  — OQ-8 option 1, and T3's lifetime half as `FreezeBinderLife` states it. That bears on the target
  structure, not on D1's rank.

---

## 9. Report lists (CLAUDE.md §5)

**Printed hypotheses the routes spend.**
- [TR] 6.48 (`updV_frame`), at `PVWRun`, with its proof's accounting of a `mut` cell of the aliasable
  walk by its immutable ancestor inside it.
- `↭`'s `mut` and `imm` clauses ([TR] p. 5, row 18), at `PVWUpd`.
- 6.65's and 6.64's opening cells (`ρm = ℓ ↦ mut(α, …)`, `ρi = ℓ ↦ imm({α}, …)`), at
  `PVWLendMut`/`Imm` and the exact lifetime.
- 6.112 (`Иf`), with 6.108, 6.109 and 6.111, at `InstFreshExists` and the resume.
- 6.116 (I-dup) and 6.43, at the thaw's composition of `imm` views.
- 6.117 (M-inv): only to say why extensional equality of invariants does not survive an instantiation
  (§1.3 (c)); it is not used as a step.

**Still unspent**, since no row that reads them is in this unit:
- 6.65's `P̂ ⊧ [β] P̂`;
- 6.64's `AdmWf` and `hQ` at a resuming table;
- 6.66's premises;
- 6.150's H11 and H16;
- 6.149;
- 6.50 for the table (`TabUpd`);
- 6.62.

**Uniqueness and functionality results.**
- Expected to be used:
  - `ResU.Flat.functional` (one flattening cell per place in `PlaceViewsW`);
  - `ResU.CompS.functional`;
  - `CellU.mutOf_inj`, `CellU.mutOf_at`, `mutPred_mutOf`;
  - `Restrat.Emb.injective` (a record list's instantiation is injective);
  - `dropC_disj` (one `mut` view per place across slots).
- Not expected: the machine's determinism (`AStep1.deterministic`). The location half of the binder
  (T3's `FreezeBinderLoc`) is where it would enter.

**Printed lemmas in the run-up that are untranscribed.**
- None of those this unit reads: 6.48 and 6.49 are transcribed (`TR.lemma_6_48`,
  `TR.lemma_6_49`).
- The block form of 6.112 (a block of fresh lifetimes at once) is ours, built from 6.111 and 6.112.
- As before: [TR] 6.150 at a resuming table, and the stacked folds at `ResumeAff` tables
  (DESIGN §15.5).

**Hypotheses added, and their scope.**
- **`CohS` at W's `Mut`/`Imm` leaves.** It comes from the lend's view type: withbor's callback receives
  `Mut 'x T` with `T` the lend's payload. It is the 6.65 analog of Core's `CohE`. At `σ = []` it is
  vacuous.
- **`OwnOK.placeFree`, `FutOK.placesFree`.** The lent place is the lender's: a real lend's callback
  does not hold it, and a future's inserted lend is the resumer's. Every real lend meets both.
- **`OwnPush`'s `ViewAt`.** The own lend at a callback-shaped type is the view's lend. It is vacuous at
  other types.
- **`CallbackExt*`'s `e.T = T` and the views at `e :: σ`.** Each is a property of the borrow
  constant's lend.
- **`CtxThawFree Γ` at the four rows.** This is a guarantee gap: FL at W says nothing about a thunk
  over a `μ` or `fam` slot inside a lend. Its discharge is §5.4 R1. Both programs meet it.
- **`MutPayloadInst`'s support hypothesis.** It is `ptoMutS`'s own last conjunct, read at the retained
  cell.
