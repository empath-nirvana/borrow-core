# ProbeD1: the two-cell guard gap, the unroll row, the `∀I` row's open cases, `MonoHide` — the design

This is the design for the unit after the R1 unit (`R1MONO.md`, commit `5210cf1`). It plans four
items, in the order of §5, and states every target as a Lean `def … : Prop` with its route, the
lemmas it reuses, what counts as success or failure, and the arising check any counterexample must
pass. It contains no proofs.

The statements go in a new statements file `Nx.lean` (definitions and `def … : Prop` only). The
proofs go in `NxGuard.lean` (item 1a), `NxUnroll.lean` (item 2), `NxAllI.lean` (item 3) and
`NxHide.lean` (item 4). If item 1b runs, its revised relation and rows go in `NxBlock.lean` and
`NxBlockRows.lean`. Item 3 also edits three definitions of the one draft relation in `R1.lean`
(§3.1). Those are the unit's only edits to existing definitions, and the outcome must list them.

The rules are unchanged. Nothing breaks the borrow calculus, and no printed BoLo definition is
edited: only ProbeD1's draft relation, its guard, its index and its arising set may change. Nothing
in `Core/`, `Paper/`, `Support/`, `GhostEnd/` or `Targets/` is edited. The paper is not wrong. An
obstruction is reported only as an elaborating `def … : Prop` or as a configuration that arises
with every hypothesis discharged (DESIGN §11). There is no new relation family and no step index,
and multi-shot is ignored. Builds are targeted (`lake build ProbeD1`). There is no `sorry`, `axiom`,
`native_decide`, `opaque`, `partial`, `unsafe` or `implemented_by`, and every axiom set is within
`[propext, Classical.choice, Quot.sound]`.

---

## 0. On one page

**Item 1: the two-cell guard gap.** `loadGuardFails2` and `sliceGuardFails` are proved facts about
the guard. The missing step was the bridge from a real configuration to the two cells. While
designing, I found that the typed world already contains [TR] 6.150's entry as a constructor:
`TW.reb` (`Core/World.lean:122`) composes the reborrowed resource `cb ∈ reb_β(r.R)` into the world
at a record's `imm` cell. So the arising check is a `TW` history, as follows:
- allocate the owner of `Ref 1 ⊗ Ref 1` and its two cells;
- open the 6.64 lend (`LendImmI`, so the configuration is in `ArisesI` and the view is in `ArisesVI`);
- apply `TW.reb` at the lend's record.

`reb_β`'s `own` clause gives the two cells exactly at `β`. `loadGuardFails2` with `tabAtS_comp`
then shows that every own-lend push rejects them beside any closure resource. The old stack rejects
them too (they are below its innermost lend). Typing reaches the program
(`Λ'0. λp. withload p cb` inside `withbor (1)`). Slices get the same check.

If the gap is real, the fix is to the entry, not the table. A table that admits the cells would
leave cells at an internal lifetime that are neither a view nor above the cut. The thaw could then
only retain them, which breaks the cut, or transport them, which re-reads a stored invariant at a
moved reading. That is `mut_not_natural`'s mechanism, which the freeze binder exists to avoid. The
entry fix is a **block**: one lend of several places at one lifetime, under one binder. It is
represented with GhostEnd's `LEnt` unchanged, as consecutive entries sharing variable and lifetime.
Its cost is `StackOK`'s strict chain becoming a block chain (`StackOKB`), so every row at `binder0`
is re-proved at the revised relation. That work is scheduled last (§5).

**Item 2: `VRLMUnroll`.** This is a port of `Core/RelMu.lean`
(`vCE_some`, `vCE_rename`, `vCE_subst`, `vC_inst`, `vC_unfold`) to `vRLM`'s clauses, using the
already-proved `vRLM_mono_at` and `vRLM_roll`. The rows `RollRowM` and `UnrollRowM` follow at every
placement. The work is mechanical, and no counterexample is expected.

**Item 3: the `∀I` row's open cases.**
- *The binder-named index.* The restriction is that `StackJ`'s third kind carries `SubFresh δ`
  at the head (`StackJM`). Its only producer, `cbpv`'s `U` own push (`RelendUI`), already has it,
  and no `binder0` clause produces such an index. With it, `SubOutside` survives the binding
  (`SubOutsideExtendNamed`). `not_subOutsideExtendAny`'s witness violates the restriction.
- *A live `U` slot.* The design found why two of the three transports fail there. W's `∀` clause
  reads the whole base reading (`SubFresh δ α`), and its first conjunct admits instances that are
  new values, so extending the reading changes which own lends a `U` value's argument must serve.
  That is a contravariant change. Two edits make the reading invisible:
  - instances must be in scope (`InScope`), the way `∀E` instantiates at a lifetime term;
  - own lends must read only the type's variables (`OwnPushM`).

  A symmetric lemma (`VRLMReadEquiv`) then gives both reading transports (`CtxExtendMSAt`,
  `CtxShadowMSAt`) at every context.
- *The push (`MonoOwnGMAt`).* It is provable only at slots whose computation has no lifetime `∀`,
  no effect layer, no `ν`, and no argument that can hold a `U` or an owned cell (`PushStable`).
  Elsewhere the pushed view and the pushed lifetime are arguments the old clause never covered
  (`PushedViewOutsideOldGuard`), so `binder0`'s `U` clause, which has no own push, gives nothing
  there. That is DESIGN §4.3's expectation, now with its exact reach. It is recorded as not
  derived, with the program check.

**Item 4: `MonoHide` and the consumers.**
- `MonoHide` at `vRLM` is invisible when the hidden names cross no entry, or when no live type
  carries them. That covers both programs. The general case is expected to be not derived
  (DESIGN §4.3).
- The consumers check goes rule by rule over `RulesClosed` and the spanning rules. Its expected
  answer is that `AllIRowM` and `MonoExtM` are **not** all the consumers: `[handle]`'s
  `MonoHide` remains. Statement 4's `AllRMono` is `AllIRowM`'s transport at a `U(∀ρ…)` slot.
- Three owed rows are flagged that are not monotonicity: `VRLMUnroll` (item 2), the lifetime
  substitution `∀E` reads, and `effSub`.
- Only after the table is complete may a document say what statement 0 at `binder0` reduces to.

**Order.** (1a) → (2) → (3) → (4) → (1b) → docs. (2) and (3) are done whatever item 1 does (§5).

---

## 1. Item 1: the two-cell guard gap

### 1.1 What is proved, and the missing step

- `rebGuardFails` and `loadGuardFails`: the table rejects a reborrowed cell exactly at the own
  lend's lifetime `α`, at a place the pushed stack does not lend.
- `loadGuardFails2`: it rejects two such cells, at distinct places the old stack does not lend, at
  every pushed stack.
- `sliceGuardFails`: it rejects two slice elements.
- `RetainedPaySliceRow`: proved, but vacuous.

What the R1 review asked for (CHECKPOINT WARNING) is the step from a configuration that arises,
through the reborrow, to two top-level cells at the callback's guard, composed with the closure's
resource. It was asked for at `ArisesI` "ideally".

### 1.2 What "real" means here

Each of the following is a Lean fact, together with the arising set's own standard (DESIGN §11):
- **(a)** A configuration of `ArisesI` (the `TW` history and the transitions W's semantics makes)
  where the borrowed payload's `Imm` value arises (`ArisesVI.view`).
- **(b)** 6.150's step in `TW` (`TW.reb`) composes the reborrowed resource `cb` into a tagged `TW`
  world at that configuration.
- **(c)** `cb` holds an `imm` cell exactly at `β` at each of two distinct places, lent by no entry.
- **(d)** Beside every closure resource, the composite fails the table at the old stack, when `β`
  is below its innermost lend, and at every own-lend push at `β`. So both conjuncts of W's `∀`
  clause say nothing about the callback's run on that argument.
- **(e)** `withload`'s bound puts every instance below the lend, and typing reaches the program.

Both the stack `[e]` (non-spanning `withload` inside a lend) and the nil stack are checked. At the
nil stack the spanning `withload` (`SpanLoadRow`, resuming callback) must use the own push. The
push's own entry is not an `ArisesI` transition. (d) is therefore stated at every pushed stack, and
(b) is the world-level arising of what the callback holds.

### 1.3 The statements (item 1a)

```lean
/-- `Ref 1 ⊗ Ref 1`: a payload with two `Ref` leaves side by side. -/
abbrev pairTy : VTy := .tensor (.ref .unit) (.ref .unit)

/-- **The reborrow's two cells** ([TR] p. 5's `reb_β`, `own` clause): a reborrow at `β` of a
resource owning `l₁` and `l₂`, at which the reborrowed type's shape holds of the pair, holds an
`imm` cell exactly at `β` at both places (the shape needs both cells; `RebAt` fixes their kind
and lifetime). -/
def PairRebCells : Prop :=
  ∀ (R cb : WRes) (β : Life) (l₁ l₂ : BoCa.Loc) (x : LifeVar) (s : LSub),
    R.get l₁ = some (CellU.ownOf .unit) → R.get l₂ = some (CellU.ownOf .unit) →
    ResU.Reb β R cb →
    vShape (pairTy.immReborrow (.var x)) (s.extend x β) (.pair (.loc l₁) (.loc l₂)) cb →
    (∃ (χ₁ : WRes) (h₁ : χ₁.InStratum (LSet.singleton β).join),
        cb.get l₁ = some (CellU.immOf (LSet.singleton β) .unit χ₁ h₁)) ∧
    (∃ (χ₂ : WRes) (h₂ : χ₂.InStratum (LSet.singleton β).join),
        cb.get l₂ = some (CellU.immOf (LSet.singleton β) .unit χ₂ h₂))

/-- **The pair's reborrow arises inside a lend.** A configuration of the revised arising set whose
stack is one 6.64 entry named `'0` over an owner of `Ref 1 ⊗ Ref 1`, the entry's view arising there
at `Imm '0 (Ref 1 ⊗ Ref 1)`, its record among the open frames, the payload's two places distinct
and lent by no entry; and at some `β` at most every lifetime of the world, `TW.reb` at the record
composes a reborrowed resource into a tagged typed world. -/
def PairRebArisesLend : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
      (l₁ l₂ : BoCa.Loc) (x : LifeVar),
    ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧ e.T = pairTy ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' (ResU.single e.l ψ)) (.loc e.l) (viewTy e) ∧
    r ∈ c.ps ∧ r.le = e.l ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧ ¬ VFree x r.T ∧
    r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧ l₁ ≠ l₂ ∧
    l₁ ∉ c.σ.map LEnt.l ∧ l₂ ∉ c.σ.map LEnt.l ∧
    ∃ (β : Life) (cb fρ' : WRes), β < α ∧ StratumLe c.fρ β ∧ ResU.Reb β r.R cb ∧
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb ∧
      ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls

/-- **The pair's reborrow arises at the nil index** (the spanning row's case): a configuration of
the revised arising set at the empty stack whose world holds the owner's 6.64 frame, the frame's
`imm` cell in the local part, and the same `TW.reb` step. -/
def PairRebArisesNil : Prop :=
  ∃ (c : Cfg) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (x : LifeVar),
    ArisesI (ℍ := ℍ) c ∧ c.σ = [] ∧ c.αs = [] ∧ r ∈ c.ps ∧
    (∃ (s : LSet) (hs : r.R.InStratum s.join), c.ρ.get r.le = some (CellU.immOf s r.v r.R hs)) ∧
    r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧ ¬ VFree x r.T ∧
    r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧ l₁ ≠ l₂ ∧
    ∃ (β : Life) (cb fρ' : WRes), StratumLe c.fρ β ∧ ResU.Reb β r.R cb ∧
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb ∧
      ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls

/-- **Neither of W's `∀` conjuncts reads the reborrowed argument**: beside any resource of the
closure, two `imm` cells exactly at `β`, at distinct places the stack does not lend, fail the
table at the stack itself when `β` is below its innermost lend, and at every own-lend push at `β`
(`loadGuardFails2`, `tabAtS_comp`). -/
def PairCallbackGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (β : Life) (cb ρc ρ : WRes) (l₁ l₂ : BoCa.Loc),
    l₁ ≠ l₂ → l₁ ∉ σ.map LEnt.l → l₂ ∉ σ.map LEnt.l →
    (∃ (v₁ : Val) (χ₁ : WRes) (h₁ : χ₁.InStratum (LSet.singleton β).join),
        cb.get l₁ = some (CellU.immOf (LSet.singleton β) v₁ χ₁ h₁)) →
    (∃ (v₂ : Val) (χ₂ : WRes) (h₂ : χ₂.InStratum (LSet.singleton β).join),
        cb.get l₂ = some (CellU.immOf (LSet.singleton β) v₂ χ₂ h₂)) →
    ResU.CompS ρc cb ρ →
      (∀ h, αs.head? = some h → β < h → ¬ TabAtS σ αs ρ) ∧
      ∀ en : LEnt, StackOK (en :: σ) (β :: αs) → ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **`withload`'s bound reads below the lend**: inside a callback whose binder `'0` the stack reads
at `α`, every instance of `withload`'s `∀'x ⊏ ⊓Δ` (`Δ = '0 ⊏ ⊤`) is below `α`. So the first
conjunct is read only below the innermost lend. -/
def PairBoundBelow : Prop :=
  ∀ (δ : LSub) (e : LEnt) (α β : Life), e.x = 0 →
    LtLife (extS δ [e] [α]) ((LifeCtx.empty.extend 0 .top).meetOfDom) β → β < α

/-- **Typing reaches `withload` at the pair inside a lend**: under the lend's binder `'0`, the view
`p : Imm '0 (Ref 1 ⊗ Ref 1)` applied to `withload` with a callback, in the probe's rule set
(`probeRules_of_nu` from a `Targets.CDerivesNU` derivation, as `gdMtDerivable`). -/
def PairWithloadTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules (LifeCtx.empty.extend 0 .top) [⟨.imm (.var 0) pairTy, true⟩]
      (.app (.app withload (.var 0)) cb) (.comp (.ret B))

/-- **The two-cell gap is real at `withload`.** -/
def WithloadPairGapReal : Prop :=
  PairRebCells ∧ PairRebArisesLend (ℍ := ℍ) ∧ PairRebArisesNil (ℍ := ℍ) ∧
    PairCallbackGuardFails ∧ PairBoundBelow ∧ PairWithloadTyped
```

**Slices.** The family comes from an owned array. Inside a lend, the array's cells are in the
callback's resource at `LendMutI` or `LendImmI`, whose `ρc` is arbitrary above the lend. Two
6.64 frames at `β` (`TW.immFrame` at each element) give the `[Imm 'x 1]` family. The imm form is
used so that no `mutFold` with an arbitrary predicate enters; the guard reads only places and
lifetimes in any case.

```lean
/-- **A two-element slice's family arises inside a lend**: at a configuration of the revised arising
set with one entry named `'0`, the local part holds the owners of `ℓ` and `ℓ + 1`; two 6.64 frames
at `β` below the lend turn them into a family `ρs` of `imm` cells exactly at `β`, a part of a
tagged typed world; the stack lends neither place. -/
def SliceFamilyArises : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α β : Life) (ℓ : BoCa.Loc) (u₀ u₁ : Val) (X Z ρs W' : WRes)
      (ps' : List FrameRec) (ls' : List SRec),
    ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧ β < α ∧
    (∀ i < 2, ℓ + i ∉ c.σ.map LEnt.l) ∧
    ResU.CompS (ResU.single ℓ (CellU.ownOf u₀)) (ResU.single (ℓ + 1) (CellU.ownOf u₁)) X ∧
    ResU.CompS X Z c.fρ ∧ ResU.CompS ρs Z W' ∧
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) ∧
    TW W' ps' (rsOf ls') ∧ Tagged W' ps' ls'

/-- **Neither conjunct reads the family**: `sliceGuardFails` with `tabAtS_comp`, and the old stack's
first conjunct. -/
def SliceCallbackGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (β : Life) (ρs ρc ρ : WRes) (ℓ : BoCa.Loc),
    (∀ i < 2, ℓ + i ∉ σ.map LEnt.l) →
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) →
    ResU.CompS ρc ρs ρ →
      (∀ h, αs.head? = some h → β < h → ¬ TabAtS σ αs ρ) ∧
      ∀ en : LEnt, StackOK (en :: σ) (β :: αs) → ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **Typing reaches a slice borrow inside a lend** (`withbor` at `sliceBorrowITy`). -/
def SliceTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules (LifeCtx.empty.extend 0 .top) [⟨.array .unit, true⟩]
      (.app (.app withbor (.var 0)) cb) (.comp (.ret (.tensor (.array .unit) B)))

def SliceGapReal : Prop :=
  SliceFamilyArises (ℍ := ℍ) ∧ SliceCallbackGuardFails ∧ SliceTyped
```

The world-link conjuncts in `PairRebArises*` and `SliceFamilyArises` may be tightened while
proving. The conjuncts the guard argument reads must not be weakened: the cells exactly at `β`, the
two places distinct, the stack's places, and `β` below the lend.

### 1.4 The route and the lemmas reused

- **The world.** `TW.alloc` three times (owner, `l₁`, `l₂`), as `nv_tw₁` does. Then `TW.immFrame`
  at the owner, as `nv_tw₂` does. Its descendants are the sub-records of `R`'s owned cells, if
  `Desc` gives any: compute them, as `nv_not_desc` does. `Tagged` follows `nv_tagged`. The nil
  configuration is `ArisesI.nil`. `ArisesI.lendImm` needs `LendImmI`: `LendImm`'s fields,
  `LendFresh`, and `α < ⊤` (from H4, as `outerBelowTopArises` reads it). The view comes from
  `ArisesVI.view`.
- **The reborrow.** `TW.reb` needs:
  - `r ∈ rsOf c.ls`;
  - the world's `imm` cell at `r.le`;
  - `¬ VFree x r.T`;
  - `ResU.Reb β r.R cb`, with `π` given by the two singleton pieces;
  - `vShape` at `Imm '0 1 ⊗ Imm '0 1`;
  - `StratumLe c.fρ β` (choose `β` below every lifetime of the world);
  - `Valid` of the composite.
- **The cells.** `PairRebCells` comes from `ResU.RebAt`'s `own` clause at each place, with
  `l ∈ dom cb` from the shape's `ptoImm` at each leaf.
- **The guard.** `PairCallbackGuardFails` uses `tabAtS_comp` (`GhostEnd/Arising.lean:83`). The old
  stack fails the first conjunct (`InStratum (↓h)` at a cell at `β < h`). The push uses
  `loadGuardFails2`. `SliceCallbackGuardFails` uses `sliceGuardFails` the same way.
- **The bound.** `PairBoundBelow` uses `meetOfDomL` at one entry (`meet (var 0) top`) and
  `Life.interp`.
- **Typing.** `CDerivesNU.withload` (and `sliceBorrowI`), `lolliE`/`app`, and `probeRules_of_nu`.

### 1.5 Success and failure

- **Real** means `WithloadPairGapReal`, or `SliceGapReal`, is proved. Item 1b then runs, last
  (§5).
- **Not real.** A conjunct is false, or its proof needs a change to a definition. Then record which
  step and why:
  - `TW.reb`'s premises unmeetable at the configuration;
  - the shape forcing fewer than two cells;
  - the bound not below the lend;
  - the program not typable.

  Do not run item 1b, and say why in the outcome.
- **Wording.** "Real" is claimed only for what is proved. A configuration in `ArisesI` with a
  `TW.reb` world is the arising set's standard. It is not a closed program's execution, so it is
  evidence that the guard misses a real argument, and it refutes no row. No printed object is
  in question: the guard and the stack are ours.

### 1.6 Item 1b (only if real): the fix is a block

**Why not a table that admits the cells.** The thaw splits a value's resource into views at the
stack's places and a part strictly above the outermost lend. That part is the only part an
instantiation leaves alone, because the instantiation moves every internal lifetime. A cell exactly
at an internal lifetime, at a place no entry lends, can be neither. Retaining it breaks the
instantiated table: the cell stays at the old `β` while the lend moves. Handing back a moved copy
transports the cell's stored invariant to a moved reading. That is `mut_not_natural`'s mechanism,
and the freeze binder re-establishes views from the handed view instead (`ViewSlotInst`). It also
cannot cover a `Mut` slice, whose cells change under the lend. So the cells must be views: the
stack must lend their places.

**Why a block, and how.**
- GhostEnd's `LEnt` lends one place and cannot be edited: GhostEnd is another experiment, and
  `Targets` reads it.
- A lend of several places at one lifetime under one binder is therefore represented as
  **consecutive entries sharing variable, lifetime and lender's row**. Each entry lends one place
  with its own payload type and kind:
  - `withload`'s leaves are `⟨lᵢ, x, Sᵢ, imm vᵢ, cross⟩`;
  - a slice's elements are `⟨ℓ+i, x, A, mut, cross⟩` or `⟨ℓ+i, x, A, imm vᵢ, cross⟩`.
- `extS`, `TabAtS` (GhostEnd's), `innerAt`, `vwSW`, `PlaceViewsL` and the instantiation all read
  blocks unchanged.
- What changes:
  - `StackOK`'s strict chain and distinct variables;
  - the own lend, which pushes a block;
  - `StackJ`'s distinct variables;
  - the arising set, which gains the reborrow's and the slice's lends.

```lean
/-- `τ`'s entries all at the lifetime `a`. -/
abbrev blockL (τ : LStack) (a : Life) : List Life := τ.map fun _ => a

/-- **A stack in shape, blocks admitted**: one lifetime per entry, non-decreasing outward; two
entries share a variable exactly when they share a lifetime; a block's entries share their lender's
row. `StackOK` is the case with no block (`StackOKBOfOK`). -/
def StackOKB (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· ≤ ·) αs ∧
    (∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.1.x = q.1.x ↔ p.2 = q.2) ∧
    ∀ p ∈ σ.zip αs, ∀ q ∈ σ.zip αs, p.2 = q.2 → p.1.cross = q.1.cross

/-- **A borrow leaf of a type at `'x`**: a `Mut 'x S` (`true`) or `Imm 'x S` (`false`) position,
through the formers `vRLM` reads at one index (a closed `μ` by its unrolling). -/
inductive LeafTyAt (x : LifeVar) : VTy → Bool → VTy → Prop
  | mut (S : VTy) : LeafTyAt x (.mut (.var x) S) true S
  | imm (S : VTy) : LeafTyAt x (.imm (.var x) S) false S
  | tensorL {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.tensor A B) k S
  | tensorR {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x B k S → LeafTyAt x (.tensor A B) k S
  | sumL {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.sum A B) k S
  | sumR {A B : VTy} {k : Bool} {S : VTy} : LeafTyAt x B k S → LeafTyAt x (.sum A B) k S
  | bang {A : VTy} {k : Bool} {S : VTy} : LeafTyAt x A k S → LeafTyAt x (.bang A) k S
  | box {a : Lifetime.Life} {A : VTy} {k : Bool} {S : VTy} :
      LeafTyAt x A k S → LeafTyAt x (.box a A) k S
  | fam {L : VTy} {k : Bool} {S : VTy} : LeafTyAt x L k S → LeafTyAt x (.fam L) k S
  | mu {A : VTy} {k : Bool} {S : VTy} : (VTy.mu A).Cl 0 →
      LeafTyAt x (VTy.inst (.mu A) A) k S → LeafTyAt x (.mu A) k S

/-- **The block a callback's own lend pushes**: each entry is a leaf of the argument type at the
binder (kind and payload type); at an argument type with no leaf at the binder, one entry whose
payload type reads nothing. -/
def ViewAtB (x : LifeVar) (τ : LStack) (A : VTy) : Prop :=
  (∀ e ∈ τ, ∃ S, ((e.k = .mut ∧ LeafTyAt x A true S) ∨
      ((∃ u, e.k = .imm u) ∧ LeafTyAt x A false S)) ∧ e.T = S) ∨
  ((¬ ∃ k S, LeafTyAt x A k S) ∧ ∃ e, τ = [e] ∧ ∀ y, ¬ VFree y e.T)

/-- **A block's own lend**: entries named `x` sharing their row; the lifetime `a` below the stack
and the holder's resource (`И`); places distinct and new; at a block place the holder holds no
borrow cell and no cell outside an `imm` ancestor (a reborrow's parent payload, shared by the
closure, keeps its `own` cells frozen under its `imm` cell); payload types read by the extended
reading, by the type's variables or the stack's, never by `x`. -/
structure OwnOKB (δ : LSub) (σ : LStack) (αs : List Life) (x : LifeVar) (τ : LStack) (a : Life)
    (ρ : WRes) : Prop where
  ne : τ ≠ []
  named : ∀ e ∈ τ, e.x = x
  sameRow : ∀ e ∈ τ, ∀ e' ∈ τ, e.cross = e'.cross
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : x ∉ σ.map LEnt.x
  placesNodup : (τ.map LEnt.l).Nodup
  places : ∀ e ∈ τ, e.l ∉ σ.map LEnt.l
  placeFree : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ
  pay : ∀ e ∈ τ, ∀ y, VFree y e.T → (extS δ (τ ++ σ) (blockL τ a ++ αs)).find? y ≠ none
  selfFree : ∀ e ∈ τ, ¬ VFree x e.T

/-- **The own lend at the type `C`, a block.** -/
def OwnPushB (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (τ : LStack) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ x ∉ CTy.binders C' ∧
    OwnOKB δ s.1 s.2 x τ a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    (∀ e ∈ τ, ∀ y, VFree y e.T → CFree y C ∨ y ∈ s.1.map LEnt.x) ∧
    ∀ A D, C' = .arr A D → ViewAtB x τ A
```

**The revised relation `vRLMB`/`cRLMB`.** It is `vRLM` after item 3's edits (§3.1), with one
change: the `∀` clause's own-lend conjunct pushes a block. It is a revision that replaces `vRLM` as
the one draft relation once its gate rows are proved (convention of `vRLI → vRLJ → vRLM`). It is
written in `NxBlock.lean` so that `vRLM`'s results stay as the statements they were.

```lean
        (p.allOwn = true → ∀ (τ : LStack) (α : Life), OwnPushB δ (.all x c C) ρ (σ', αs') τ α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (τ ++ σ') (blockL τ α ++ αs')) (τ ++ σ')
            (blockL τ α ++ αs') ls'
            (cRLMB p (τ ++ σ') (δ.extend x α) C (blockL τ α ++ αs') ls' (.app e (.val .unit))) ρ)
```

`SemSMB` is `SemSM` (after §3.1) with `StackOKB` in place of `StackOK`, and `StackJB` in place of
`StackJM`. `StackJB` is `StackJM` without `(σ.map LEnt.x).Nodup`, which `StackOKB`'s variable
condition replaces. Its third kind admits every entry of the innermost block.

**The arising set's new lends** (`ArisesB` is `ArisesI` with two more transitions):
- `LendRebI c c' τ`: `TW.reb` at a record of `rsOf c.ls`. The world and the local part gain `cb`,
  and the stack gains `τ` at `β`. `τ`'s entries are the reborrowed leaves: `lᵢ`, `x`, payload `Sᵢ`
  from `LeafTyAt`, and kind `imm vᵢ`, with `vᵢ` the leaf's value in `r.R`. `β` is fresh below the
  records (`LendFresh`) and below `⊤`.
- `LendSliceI c c' τ`: `TW.immFrame` (or `TW.mutFold`) at each element, and the block pushed. The
  rest is as `LendImmI` (or `LendMutI`).

**The gate** (proved before any row is re-proved):

```lean
def StackOKBOfOK : Prop := ∀ (σ : LStack) (αs : List Life), StackOK σ αs → StackOKB σ αs

/-- `OwnPushM` (§3.1) at one entry is a block of one. -/
def OwnPushBOfM : Prop :=
  ∀ (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life),
    OwnPushM δ C ρ s e a → OwnPushB δ C ρ s [e] a

/-- **The block admits the reborrowed argument**: at a block push whose entries' views are the
argument's cells, beside a closure resource meeting the old guard, the composite meets the table
and the views at the pushed stack. With `PairRebArisesLend` it closes `PairCallbackGuardFails`'s
gap. -/
def PairGuardHoldsB : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (x : LifeVar) (β : Life)
    (τ : LStack) (cb ρc ρ : WRes),
    StackOKB σ αs → OwnOKB δ σ αs x τ β ρc → TabAtS σ αs ρc →
    PlaceViewsL (extS δ σ αs) σ αs ls ρc →
    (∀ e ∈ τ, ∃ ψ : CellU BoCa.Loc Val, cb.get e.l = some ψ ∧
      vwEW (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) e true β ls (ResU.single e.l ψ)) →
    (∀ l ψ, cb.get l = some ψ → l ∈ τ.map LEnt.l) → ResU.CompS ρc cb ρ →
    TabAtS (τ ++ σ) (blockL τ β ++ αs) ρ ∧
      PlaceViewsL (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) (τ ++ σ)
        (blockL τ β ++ αs) ls ρ

/-- **`PVLStart` at a block push**: the callback's resource, holding at a block place only `own`
cells frozen under an `imm` ancestor, joined to the block's views, has the guard's views at the
pushed stack. -/
def PVLStartB : Prop :=
  ∀ (s s' : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (τ : LStack) (α : Life)
    (ρ a R : WRes), StackOKB σ αs → List.IsChain (· < ·) (α :: αs) →
    (τ.map LEnt.l).Nodup → (∀ e ∈ τ, e.l ∉ σ.map LEnt.l) →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s σ αs ls ρ →
    (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) →
    vwSW s' [] τ (τ.map fun _ => true) (blockL τ α) ls a →
    PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls a →
    ResU.CompS ρ a R → PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls R

/-- An instantiation keeps a block stack in shape. -/
def InstStackOKB : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ι : Inst), InstAt αs ι → StackOKB σ αs → StackOKB σ (ι.life αs)
```

`PairGuardHoldsB` is stated for any block whose views are the argument's cells. The slice family is
its instance at the places `ℓ + i`, so no separate statement is needed.

One gate check concerns non-data payloads. W's `imm` view reads its payload at `vC true`
(GhostEnd's `vwE`), while a reborrowed leaf meets Core's `Imm` clause at `vC false` (the observable
view). At a data payload the two agree. At a payload with a thunk they do not. Record this as the
gate's open obligation: the views would read `imm` payloads at `vC false`, a further draft change,
and the user's to decide.

**The rows to re-prove at `vRLMB`, in order** (each is its `vRLM` statement with `StackOKB`,
`OwnPushB` and `SemSMB`):
1. `Statement0UFullMB`: the thaw (`RelendMValueE` at a block stack, `extS` lookup at a zip member
   by "same variable ⇒ same lifetime") and the four `U` rows.
2. `CallbackExtMutMB` and `CallbackExtImmMB`: the own-lend conjunct at `τ = [en]`
   (`OwnPushBOfM`).
3. `ForceRowMB` and `MonoExtMB`.
4. `MonoOwnGUFreeMBA`: the block push at contexts reaching no `U`. The leaves are as at one entry:
   no leaf of a context type is at a block place (`placeFree`).
5. The `∀I` row at the contexts item 3 covers (§3), at `vRLMB`.
6. `OuterBelowTopPushB`, `RetainedPayViewRowB`, and `RetainedPayLoadImmRowB`. The last is no longer
   vacuous at a payload with two leaves; prove it there.
7. `GuardInstB`, `PVLStartB`, `placesNodupArisesB`, `PVArisesB` (at the two new transitions) and
   `OuterBelowTopArisesB`.
8. `VRLMUnroll` at `vRLMB` (item 2's proof, re-run).

**Forward obligations, not this unit:**
- The share at `binder0` must re-lend a block together. GhostEnd's `openFS` quantifies over
  strictly fresh re-lends `Forall₂ (· < ·)` with a strict chain, which would split a block. Its
  replacement is the share over instantiations (`ShareReLendInst`'s direction).
- `InstReLend` (a strict-chain `ReLend`) fails at a block.
- Statement 2's `SpanLoadRow` at a payload with two leaves becomes attemptable.

### 1.7 Item 1b's stop rule

- The gate comes first. If `PairGuardHoldsB`, `StackOKBOfOK`, `OwnPushBOfM` or `PVLStartB` fails,
  stop item 1b, record the failing statement, and keep `vRLM` as the one draft relation.
- Re-prove the rows in the order above. Stop at the first row whose proof needs a definition change
  beyond those listed here (`StackOKB`, `LeafTyAt`, `ViewAtB`, `OwnOKB`, `OwnPushB`, the `∀`
  clause, `StackJB`, `SemSMB`, the two transitions). Record the frontier. `vRLMB` stays a candidate
  in its own files until rows 1–4 are proved.
- Never edit GhostEnd, `Targets`, `Core`, `Paper` or `Support`, and add no relation family beside
  the one draft relation.

---

## 2. Item 2: `VRLMUnroll`

### 2.1 The statements

`vRLM` now reads `μ` itself, so the unroll row needs `vRLM`'s analog of Core's substitution lemma.
The route is Core's `RelMu.lean` read at W's clauses. A candidate is a predicate at one index (one
stack, reading, lifetimes and list), so the environment a substitution moves into is indexed by
that index.

```lean
/-- The environment a substitution moves into, at one index (`substEnv`'s analog). -/
def substEnvW (p : Placement) (ρ : Nat → WEnt) (τ : Nat → VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec) : Nat → WEnt :=
  fun n => ⟨(τ n).subst (fun k => (ρ k).ty), vRLM (ℍ := ℍ) p (some ρ) σ δ (τ n) αs ls⟩

/-- **The environment of a closed type is the empty one read explicitly** (`vCE_some`'s analog). -/
def VRLMSome : Prop :=
  ∀ (p : Placement) (η : Option (Nat → WEnt)) (A : VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p η σ δ A αs ls = vRLM (ℍ := ℍ) p (some (wEnv η)) σ δ A αs ls

/-- **Renaming moves into the environment** (`vCE_rename`'s analog). -/
def VRLMRename : Prop :=
  ∀ (p : Placement) (A : VTy) (ρ : Nat → WEnt) (r : Nat → Nat) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p (some ρ) σ δ (A.rename r) αs ls = vRLM (ℍ := ℍ) p (some (ρ ∘ r)) σ δ A αs ls

/-- **Substitution moves into the environment** (`vCE_subst`'s analog). -/
def VRLMSubst : Prop :=
  ∀ (p : Placement) (A : VTy) (ρ : Nat → WEnt) (τ : Nat → VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p (some ρ) σ δ (A.subst τ) αs ls =
      vRLM (ℍ := ℍ) p (some (substEnvW p ρ τ σ δ αs ls)) σ δ A αs ls

/-- **The unrolling is the body at the `μ` itself** (`vC_inst`'s analog). -/
def VRLMInst : Prop :=
  ∀ (p : Placement) (A : VTy) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p none σ δ (VTy.inst (.mu A) A) αs ls =
      vRLM (ℍ := ℍ) p (some (VTy.scons ⟨.mu A, vRLM p none σ δ (.mu A) αs ls⟩ (wEnv none)))
        σ δ A αs ls

-- `VRLMUnroll` is stated in `R1.lean:253`; unchanged.

/-- **`roll` at W.** -/
def RollRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy), A.NoMut 0 → (VTy.mu A).Cl 0 →
    SemSM (ℍ := ℍ) p Δ Γ e (.val (VTy.inst (.mu A) A)) → SemSM (ℍ := ℍ) p Δ Γ e (.val (.mu A))

/-- **`unroll` at W.** -/
def UnrollRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy),
    SemSM (ℍ := ℍ) p Δ Γ e (.val (.mu A)) → SemSM (ℍ := ℍ) p Δ Γ e (.val (VTy.inst (.mu A) A))
```

### 2.2 The route

- **`VRLMSome`.** Induction on the type (`VTy.recV`), as `vCE_some`. At a leaf, `wClose none A = A
  = A.subst .tvar` (`VTy.subst_id`). At a variable, `wEnvP none n = (wEnv none n).P`. At `μ`,
  `wEnv (some η) = η`.
- **`VRLMRename` and `VRLMSubst`.** Induction on the type, as `vCE_rename` and `vCE_subst`, one case
  per clause of `vRLM`:
  - `U`: `VTy.subst` leaves `U C` alone, and `vRLM_thunk_env`.
  - `⊗`, `⊕`, `!`, `[@a]`, `Ref`, `[L]`: componentwise (`sepRange_mono'` at `[L]`).
  - `Mut` and `Imm`: `wClose` through `VTy.subst_subst`; `CohS` and `RetainedPay` read only the
    closed type.
  - A variable: by definition.
  - `μ`: `VTy.noMut_upS_iff`, `wClose` at `(.mu A).subst τ` by `subst_subst`, and the environment
    equation `substEnvW (scons ⟨_, P⟩ ρ) (upS τ) = scons ⟨_, P⟩ (substEnvW ρ τ)`. Its `succ` case
    is `VRLMRename` with `VTy.subst_rename`.
- **`VRLMInst`.** `VRLMSome`, then `VRLMSubst` at `scons (.mu A) .tvar` and `wEnv none`. The two
  environments agree at `0`, because `(.mu A).subst .tvar = .mu A`, and at `succ` (empty entries).
- **`VRLMUnroll`.**
  - (←) is `VRLMInst` with `vRLM_roll` (proved, `R1Thaw.lean`).
  - (→) is the least fixed point at the candidate `vRLM none (inst (.mu A) A)`. The body at it is
    inside it, by `vRLM_mono_at` at `0` from the roll direction. This is `vC_unfold`'s argument.
- **`RollRowM` and `UnrollRowM`.** `wpTS_mono` at `cRLM .ret`, with the index facts carried between
  the two types:
  - `BindersLow`, by the binders of `inst (.mu A) A` being those of `A`;
  - `Scoped`, by `vFree_subst`;
  - `StackJM`: the third kind does not apply at `.ret`, and the second kind's `¬ CFree` transfers
    because the free lifetime variables of the two types agree.

### 2.3 Success, failure, arising

- **Success**: `vRLMUnroll`, `rollRowM` and `unrollRowM` at every placement.
- **Failure**: a clause whose port does not go through. Record the clause; it blocks neither item 3
  nor item 4.
- **Arising**: no counterexample is expected. The statements are equations between two readings of
  one definition, and no refutation is planned.

---

## 3. Item 3: the `∀I` row's two open cases

### 3.1 The three edits to the draft relation (in place, `R1.lean`)

All three edit `vRLM`, `cRLM` and `SemSM`, nothing else. Each answers a step of the route below.
Before any other item-3 work, rebuild and fix the proofs they touch:
- `cRLM_step`'s `∀` case;
- `allIRowMNKAt0_of`;
- `gdAllIHoldsAtMt`;
- `callbackExt*M_own` (they now supply `OwnPushM`);
- the `U` rows (`SemSM`'s `StackJM`);
- `GdIndex` (`gdY.T = 1`, so the new conjuncts are immediate).

```lean
/-- **A lifetime in scope at a reading**: the value of one of its bindings. `∀E` instantiates at a
lifetime term, whose value below `⊤` is one of its variables' (`InScopeOfInterp`). -/
def InScope (s : LSub) (α : Life) : Prop := ∃ p ∈ s.entries, OrderDual.toDual p.2 = α

/-- **The own lend at `vRLM`**: `OwnPushI`, its payload type reading only the type's variables or the
stack's (`payLocal`), not the binder (`selfFree`). Every borrow constant's own lend meets it: its
payload type is the callback argument's (`ViewAt`), which the constant's side condition keeps free
of the binder (`hfree₁`). -/
def OwnPushM (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  OwnPushI δ C ρ s e a ∧ (∀ y, VFree y e.T → CFree y C ∨ y ∈ s.1.map LEnt.x) ∧ ¬ VFree e.x e.T

/-- **`StackJ` at `vRLM`**: an entry of the third kind (the innermost, new to `Δ`, named by the
type's outermost `∀`) was pushed fresh below the reading. Its only producer, `cbpv`'s `U` own push
(`RelendUI`'s own conjunct), asks `SubFresh`; no `binder0` clause produces such an entry. -/
def StackJM (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  StackJ σ αs δ Δ Γ C ∧
    ∀ e ∈ σ, Δ.find? e.x = none → σ.head? = some e → (∃ c C', C = .all e.x c C') →
      ∀ a ∈ αs.head?, SubFresh δ a
```

The edits themselves:
- **(E1)** In `cRLM`'s `∀` clause, the first conjunct's pure hypothesis
  `⌜LtLife (extS δ σ' αs') c α⌝` becomes `⌜LtLife (extS δ σ' αs') c α ∧ InScope (extS δ σ' αs') α⌝`.
- **(E2)** The own-lend conjunct's `OwnPushI` becomes `OwnPushM`.
- **(E3)** `SemSM`'s `StackJ` becomes `StackJM`.

What each edit costs and why it is right:
- **(E1)** removes nothing a row uses:
  - `∀E` instantiates at `⟦b⟧`, which is a variable's value. `InScopeOfInterp` below states this,
    and `LtLife` rules out `⊤`.
  - The borrow constants read the callback through the own-lend conjunct (`CallbackExt*M`).
  - The one change is that a constant at `σ = []` may no longer read its callback through the first
    conjunct at a fresh lifetime. It reads it at its own push, as statement 2 does.
  - A lifetime is then made only by a lend. That is the freeze binder's reading: a resume
    instantiates exactly the lifetimes the frozen computation made.
- **(E2)** keeps the own lend's payload type off variables the type does not read. Without it the
  set of admissible own lends depends on bindings the type ignores.
- **(E3)** is the restriction item 3 asks for at the named index (§3.2).

```lean
/-- `⟦b⟧` is the value of one of `b`'s variables, or `⊤`'s: a meet or a join of two values is one of
them. At an instance below a bound, `⊤` is excluded, so the instance is in scope. -/
def InScopeOfInterp : Prop :=
  ∀ (s : LSub) (b : Lifetime.Life) (m : ℕ),
    b.interp s = some m → InScope s (OrderDual.toDual m) ∨ m = Lifetime.SLife.top
```

### 3.2 The binder-named index

**The step.** At an index whose innermost entry `e` is named by the binder (`StackJ`'s third kind),
the first conjunct reads the premise at `δ.extend x α`. The premise's index needs
`SubOutside σ αs (δ.extend x α)`. At `e`, `boundBefore x (δ.extend x α)` is all of `δ`'s bindings,
so it needs all of them read above `e`'s lifetime. Nothing gave that, and
`not_subOutsideExtendAny`'s witness reads a binding below it. `StackJM` gives exactly that
(`SubFresh δ (head)`).

```lean
/-- **`SubOutside` along a binding of the innermost entry's variable**, the entry pushed fresh below
the reading. -/
def SubOutsideExtendNamed : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (e : LEnt) (α a : Life),
    (σ.map LEnt.x).Nodup → σ.head? = some e → αs.head? = some a → SubFresh δ a →
    SubOutside σ αs δ → SubOutside σ αs (δ.extend e.x α)

/-- **`[allI]` at one context, at every index.** -/
def AllIRowMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C))

/-- **The context at the reading extended at the innermost entry's variable**, which the stack
shadows. -/
def CtxExtendNamedMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    σ.head? = some e → InScope (extS δ σ αs) α → CtxFresh e.x Γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend e.x α) αs ls Γ γ ρ
```

**The route.**
- `allIRowMNKAt0_of`'s first-conjunct case runs as before, with these replacements:
  - `subOutsideExtend` by `SubOutsideExtendNamed`;
  - `stackJ_allExtend` by its named form (the entry is `Δ.extend x b`'s, so first kind);
  - `models_allExtend` by its named form (`x` is read at the head, below `b` by the third kind's
    `LtLife`).
- The own-lend conjunct is vacuous: `OwnOKI.var` asks `x ∉ σ.map LEnt.x`.
- At a context reaching no `U`, `CtxExtendNamedMAt` is `gRLM_reading_uFree`: the stack reads `e.x`
  either way.

**Target (3a).** `allIRowMUFree0 : ∀ Γ, (∀ s ∈ Γ, s.live = true → UFreeM s.ty) → AllIRowMAt
.binder0 Γ`, which removes the "stack does not name the binder" restriction of `allIRowMNKUFree0`.

**Why this restriction and not the other.** Dropping the third kind from `binder0`'s judgement is
also principled, because no `binder0` clause produces it. But `cbpv`'s `U` own push needs the third
kind and has `SubFresh` already. So the strengthened kind is right at every placement, and the
other choice would split `SemSM` by placement.

### 3.3 A live `U` slot: the reading transports

**Why `CtxExtendMAt` and `CtxShadowMAt` fail at a `U` slot.** The design found the reason, and it
is not stated in `R1MONO.md`:
- W's `∀` clause asks its own lend `SubFresh δ α`, which reads every binding of the base reading.
- Extending `δ` by `x ↦ α₀` with `α₀` a new value below the head restricts the own lends a `U`
  value's argument must serve, to those below `α₀`.
- In a contravariant position, the closure must then accept more arguments than it was related for.
- With (E1), `α₀` is already a value in scope. The two readings then have the same value set, and a
  lend fresh below one is fresh below the other.
- With (E2), the admissible own lends do not depend on bindings the type ignores.

The transport is then symmetric:

```lean
/-- **Two readings the relation cannot tell apart at a stack**: the stack's readings agree off `X`;
the base readings agree at every variable an entry's payload type reads (GhostEnd's share reads them
at the base reading); the values in scope agree; and a lend below the innermost is fresh below one
exactly when it is fresh below the other (at the empty stack, every lend). -/
def ReadEquiv (X : LifeVar → Prop) (σ : LStack) (αs : List Life) (δ₁ δ₂ : LSub) : Prop :=
  (∀ y, ¬ X y → (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y) ∧
  (∀ e ∈ σ, ∀ y, VFree y e.T → δ₁.find? y = δ₂.find? y) ∧
  (∀ α, InScope (extS δ₁ σ αs) α ↔ InScope (extS δ₂ σ αs) α) ∧
  ∀ a, (∀ h ∈ αs.head?, a < h) → (SubFresh δ₁ a ↔ SubFresh δ₂ a)

/-- **`vRLM` reads only what `ReadEquiv` fixes**, at every type, both ways, `X` avoiding the type's
free variables and binders, the environment's types and the entries' payload types. -/
def VRLMReadEquiv : Prop :=
  ∀ (A : VTy) (η : Option (Nat → WEnt)) (X : LifeVar → Prop) (σ : LStack) (δ₁ δ₂ : LSub)
    (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    (∀ y, X y → ¬ VFree y A ∧ y ∉ VTy.binders A ∧ ∀ n, ¬ VFree y (wEnv η n).ty) →
    (∀ y, X y → ∀ e ∈ σ, ¬ VFree y e.T) → StackOK σ αs → ReadEquiv X σ αs δ₁ δ₂ →
    (vRLM (ℍ := ℍ) .binder0 η σ δ₁ A αs ls v ρ ↔ vRLM (ℍ := ℍ) .binder0 η σ δ₂ A αs ls v ρ)

-- `CRLMReadEquiv` and `EffRetMReadEquiv`: the same at `cRLM` (`X` avoiding `CFree` and
-- `CTy.binders`) and `effRetM`, proved together with `VRLMReadEquiv`.

/-- **`CtxExtendMAt` at an instance in scope.** -/
def CtxExtendMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (x : LifeVar) (α : Life),
    StackOK σ αs → x ∉ σ.map LEnt.x → δ.find? x = none → StackPayAvoids x σ →
    InScope (extS δ σ αs) α →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend x α) αs ls Γ γ ρ

/-- **`CtxShadowMAt` with the facts the symmetric route reads**: the pushed stack in shape, and the
pushed entry's payload type not reading its own variable (`OwnPushM`'s `selfFree`), since
GhostEnd's share reads payload types at the base reading. `R1AllI.lean`'s `CtxShadowMAt` lacks
both. -/
def CtxShadowMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK (e :: σ) (α :: αs) → δ.find? e.x = none → ¬ VFree e.x e.T →
    StackPayAvoids e.x σ →
    (∀ s ∈ Γ, s.live = true → ¬ VFree e.x s.ty ∧ e.x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p (e :: σ) δ (α :: αs) ls Γ γ ρ →
      gRLM (ℍ := ℍ) p (e :: σ) (δ.extend e.x α) (α :: αs) ls Γ γ ρ
```

**The route.** `VRLMReadEquiv` is proved by induction on the type, mutual with `cRLM` and `effRetM`
(`relendMValueE`'s environment generalisation where `μ` needs it). `ReadEquiv` is kept by each of
the following:
- the first conjunct (both readings extended by `x' ↦ α'` in scope, so `x' ∉ X` because `X` avoids
  binders);
- the own push (both extended at the new head, `payLocal` keeping the new entry's payload off `X`);
- an instantiation (`θ` maps both readings' values alike; a value at or above the head maps above
  the new head);
- `⊸` (the symmetry);
- the share's base-reading reads (the second conjunct).

`CtxExtendMSAt` at every context then follows from `VRLMReadEquiv` with `X = {x}`.
`CtxShadowMSAt` at every context follows with `X = ∅`, using `selfFree` for the pushed entry's
payload. The new binding's value is a stack lifetime at or above the head, so `SubFresh` agrees
below it. `allIRowMNKAt0_of` is re-proved with `CtxExtendMSAt` and `CtxShadowMSAt` in place of
`CtxExtendMAt` and `CtxShadowMAt`. The row has both new hypotheses at the pushed index: `StackOK`
from `OwnOKI`, and `selfFree` from `OwnPushM`.

**Targets:** `ctxExtendMSAt_all : ∀ Γ, CtxExtendMSAt .binder0 Γ`, and
`ctxShadowMSAt_all : ∀ Γ, CtxShadowMSAt .binder0 Γ`.

### 3.4 A live `U` slot: the push

**Why `MonoOwnGMAt` does not follow in general.** At the pushed stack a `U` value's clause must serve
two kinds of argument the old clause never covered:
- arguments holding the pushed view, or a weakening of it;
- the pushed lifetime as an instance. Under (E1) it is in scope at the pushed stack and not at the
  old one.

The old clause's `⊸` obligation at such an argument is vacuous, because the composite fails the old
table:

```lean
/-- **The own push's view is outside the old guard**: beside any resource, a borrow cell exactly at
the pushed lifetime fails the old stack's table, so the old `⊸` clause says nothing about an
argument holding it. A fact about the clause, not an obstruction. -/
def PushedViewOutsideOldGuard : Prop :=
  ∀ (σ : LStack) (αs : List Life) (a : Life) (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) (ρc ρ : WRes),
    αs ≠ [] → List.IsChain (· < ·) (a :: αs) → ψ.kind ≠ Kind.own → ψ.at = a →
    ResU.CompS ρc (ResU.single l ψ) ρ → ¬ TabAtS σ αs ρ
```

So the push is provable from the relation only where no such argument or instance can reach the
slot's computation:

```lean
/-- A value type holding no owned cell (no `Ref`, at any depth W reads). -/
def RefFree : VTy → Prop
  | .ref _ => False
  | .tensor A B => RefFree A ∧ RefFree B
  | .sum A B => RefFree A ∧ RefFree B
  | .bang A => RefFree A
  | .box _ A => RefFree A
  | .mu A => RefFree A
  | .fam L => RefFree L
  | _ => True

mutual
/-- **A value type the own push carries by its clauses' shape.** -/
def PushStableV : VTy → Prop
  | .thunk C => PushStableC C
  | .tensor A B => PushStableV A ∧ PushStableV B
  | .sum A B => PushStableV A ∧ PushStableV B
  | .bang A => PushStableV A
  | .box _ A => PushStableV A
  | .ref A => PushStableV A
  | .mu A => PushStableV A
  | .fam L => PushStableV L
  | _ => True
/-- **A computation type the own push carries**: no lifetime `∀` (no deeper own lend, no instance
the push brings into scope), no effect layer (no stop whose depth the pushed entry changes), no
`ν`, and every argument reaching no `U` and holding no owned cell (no argument the old clause never
covered). -/
def PushStableC : CTy → Prop
  | .ret A => PushStableV A
  | .arr A C => UFreeM A ∧ RefFree A ∧ PushStableC C
  | .amp C D => PushStableC C ∧ PushStableC D
  | .top => True
  | .all _ _ _ => False
  | .nu _ => False
  | .eff _ _ _ _ _ _ => False
end

/-- **`MonoOwnGMAt` at a context whose live slots are push-stable.** -/
def MonoOwnGMAtPS (p : Placement) : Prop :=
  ∀ Γ : Ctx VTy, (∀ s ∈ Γ, s.live = true → PushStableV s.ty) → MonoOwnGMAt (ℍ := ℍ) p Γ
```

**The route.** This extends `monoOwnUFree_go` (`R1Mono.lean`) with the `U` case:
- **The split.** The pushed views are the old ones plus `e`'s with its flag off (`placeFree`). The
  part above the outermost lend is unchanged. At `σ = []` it is above `a` by `OwnOK.below`.
- **The instantiations.** An instantiation of `a :: αs` restricts to one of `αs` (same cut at
  `σ ≠ []`). At `σ = []` it fixes `δ`'s values, which are all above `a` (`SubFresh`).
- **The body.** It is carried by a computation-level push for `PushStableC`:
  - `.ret` is the value-level push. The answer's guard facts come from the run (`wpTS_tabAt`,
    `pvlRuns_arises`'s lemma at distinct places). The pushed place is held by the frame, so the
    answer holds no cell there.
  - `⊸` un-pushes the argument. A `UFreeM ∧ RefFree` argument at the pushed stack holds no borrow
    cell at `e.l`: no variable it reads is read at or below `a`, because the stack's are above the
    head and `δ`'s by `SubFresh`. It holds no owned cell at all. So it meets the old guard (drop
    `e`), the old clause applies, and the result is pushed back.
  - `&` is componentwise.

**Targets (3b).**
- `monoOwnGMAtPS : MonoOwnGMAtPS .binder0`.
- `allIRowMPS0 : ∀ Γ, (∀ s ∈ Γ, s.live = true → PushStableV s.ty) → AllIRowMAt .binder0 Γ`. This
  is the row at every push-stable context, at every index, from `allIRowMNKAt0_of`'s re-proof,
  §3.2 and §3.3.

### 3.5 What stays open, and the program check

- **Open.** `MonoOwnGMAt` at a `U` slot whose computation has any of the following:
  - a lifetime `∀` (a captured callback can be handed the pushed view at the instance `x ↦ a`);
  - an effect layer (a stop of a name in `e.cross` ghost-ends `e`, which the old clause never
    owed);
  - `ν`;
  - an argument reaching `U` or holding an owned cell.

  With it, `AllIRowM .binder0 = ∀ Γ, AllIRowMAt .binder0 Γ` is open at those contexts. It is
  recorded as not derived.
- **The arising check.** A refutation would need a closure produced by a typed program (in
  `ArisesVI`) that is related at `σ` and not at the push. A derivable closure meets the push by its
  own derivation, so none is expected (DESIGN §4.3). Report: "I have not derived `MonoOwnGMAt` at
  these slots and have not verified that any obstruction is real".
- **What it says about OQ-8.** It says nothing to decide, and it is evidence. The one future
  `binder0`'s `∀I` row needs is the own push, and `binder0`'s `U` clause does not quantify over it.
  A placement whose `U` clause takes the own push (`uOwn` without `uFut`) would give the push by
  construction. That is a candidate for OQ-8, not adopted here: it is a placement decision.
- **The program check** (by reading the terms, recorded in the outcome):
  - `genSelf`'s callback `cb genBody` (`Targets/I/Programs.lean:77`, `:199`) captures nothing, so
    its `∀I` context is empty and is covered by §3.2.
  - `reconB′` is not built. As DESIGN §9.2 shapes it, its callback would capture `retryR`
    (`!U(∀ρ ∌ exn. !U(…) → F ρ bool)`: a `U` argument and an effect layer). That slot is outside
    `PushStable`. Record the shape constraint for building `reconB′`: `retryR` is a closed value,
    so the term places it in the callback's body instead of its context, and the `∀I` context stays
    empty. Record the reason with the term (DESIGN §9.2's rule).

### 3.6 Success and failure

- **Success.** All of the following, with the statements of §3.1–§3.4:
  - (E1)–(E3) land, with the touched proofs re-proved;
  - `allIRowMUFree0`, `ctxExtendMSAt_all`, `ctxShadowMSAt_all`, `monoOwnGMAtPS` and `allIRowMPS0`
    are proved;
  - the open class and the program check are recorded.
- **Failure.**
  - If (E1)–(E3) break a proved result that needs more than the listed edits, revert them. Prove
    §3.2 at `vRLM` with `StackJM` alone. State §3.3's transports with `InScope` as a hypothesis, and
    the row as open at a `U` slot.
  - If `VRLMReadEquiv` fails at a clause, record the clause. `CtxExtendMSAt` and `CtxShadowMSAt`
    are then claimed only at the contexts where it holds.
- **What may be claimed.** "The `∀I` row holds at every push-stable context, at every index." It may
  not be claimed that statement 0 at `binder0` reduces to the `∀I` row; §4 decides what it reduces
  to.

---

## 4. Item 4: `MonoHide` at `vRLM`, and the consumers check

### 4.1 `MonoHide`

```lean
/-- **A value inside a handler of the names `N`, at `vRLM`.** -/
def MonoHideM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p none (hideS N σ) δ A αs ls v ρ

/-- **A context inside a handler of the names `N`** (`[handle]`'s transport). -/
def MonoHideGM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (hideS N σ) δ αs ls Γ γ ρ

/-- **Hiding names no entry's row holds changes nothing.** -/
def HideInvisible : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack), (∀ e ∈ σ, ∀ n, N n = true → e.cross n = false) →
    hideS N σ = σ

mutual
/-- **A value type carries the operation name `n`**: an effect layer of `n` under a `U`, through the
formers W reads itself (Core's leaves read no stack). -/
inductive CarriesV (n : UInt32) : VTy → Prop
  | thunk {C : CTy} : CarriesC n C → CarriesV n (.thunk C)
  | tensorL {A B : VTy} : CarriesV n A → CarriesV n (.tensor A B)
  | tensorR {A B : VTy} : CarriesV n B → CarriesV n (.tensor A B)
  | sumL {A B : VTy} : CarriesV n A → CarriesV n (.sum A B)
  | sumR {A B : VTy} : CarriesV n B → CarriesV n (.sum A B)
  | bang {A : VTy} : CarriesV n A → CarriesV n (.bang A)
  | box {a : Lifetime.Life} {A : VTy} : CarriesV n A → CarriesV n (.box a A)
  | ref {A : VTy} : CarriesV n A → CarriesV n (.ref A)
  | fam {L : VTy} : CarriesV n L → CarriesV n (.fam L)
  | mu {A : VTy} : CarriesV n A → CarriesV n (.mu A)
/-- **A computation type carries the operation name `n`.** -/
inductive CarriesC (n : UInt32) : CTy → Prop
  | eff {i : UInt32} {q : Qual} {A B : VTy} {C : CTy} : CarriesC n (.eff n i q A B C)
  | effIn {m i : UInt32} {q : Qual} {A B : VTy} {C : CTy} :
      CarriesC n C → CarriesC n (.eff m i q A B C)
  | ret {A : VTy} : CarriesV n A → CarriesC n (.ret A)
  | arrA {A : VTy} {C : CTy} : CarriesV n A → CarriesC n (.arr A C)
  | arrC {A : VTy} {C : CTy} : CarriesC n C → CarriesC n (.arr A C)
  | ampL {C D : CTy} : CarriesC n C → CarriesC n (.amp C D)
  | ampR {C D : CTy} : CarriesC n D → CarriesC n (.amp C D)
  | all {x : LifeVar} {c : Lifetime.Life} {C : CTy} : CarriesC n C → CarriesC n (.all x c C)
end

/-- **The relation reads an entry's row only at the names the type carries.** -/
def VRLMHideAvoid : Prop :=
  ∀ (p : Placement) (N : UInt32 → Bool) (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life)
    (ls : List SRec), (∀ n, N n = true → ¬ CarriesV n A) →
    vRLM (ℍ := ℍ) p none (hideS N σ) δ A αs ls = vRLM (ℍ := ℍ) p none σ δ A αs ls

/-- **`[handle]`'s context transport at `binder0`, where it is invisible**: the handled name crosses
no entry, or no live type carries it. -/
def MonoHideGMHandle0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (n : UInt32),
    ((∀ e ∈ σ, e.cross n = false) ∨ ∀ s ∈ Γ, s.live = true → ¬ CarriesV n s.ty) →
    gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ →
    gRLM (ℍ := ℍ) .binder0 (hideS (· == n) σ) δ αs ls Γ γ ρ
```

**The route.**
- `HideInvisible` is list extensionality: `cross n && !N n = cross n` when `N n` implies
  `¬ cross n`.
- `VRLMHideAvoid` is induction on the type, mutual with `cRLM`, at two stacks equal up to `cross`
  at `N`'s names. Pushes keep that relation (the same entry on both). `cross` is read only by
  GhostEnd's `depth` inside `tabK`. At a name `m` with `N m = false` the depth agrees. At a name
  `n ∈ N` the type's tables have no entry, because it does not carry `n`.
- `MonoHideGMHandle0` is the two cases slot by slot.

**The general case.** `MonoHideM .binder0` is expected to be not derived, for DESIGN §4.3's
reason. Hiding a crossing name moves a stop from depth `d ≥ 1` to `0`, and the share owes its
continuation at strict re-lends at `d` but at every `ReLend` at `0`. Do not attempt it beyond
stating it. A derivable value meets it by its own derivation, so no arising witness is expected.
Both programs' handlers hide names their lenders do not cross (`reconB′`'s callback row is `{wait}`,
`retry` hides `exn`), so `HideInvisible` covers them.

### 4.2 The consumers check

**The method.** Go rule by rule over the probe's rule set:
- `RulesClosed`'s rules (`Targets/Base/Typing.lean:831`);
- `Tier1SubNU`'s premise-free constants;
- the spanning rules `SpanRule1`, `SpanRule2` and `SpanRuleLoad`;
- statement 4's `RC_allRI` and `RC_allRE`.

For each, record the index change its compatibility row makes at `binder0` between its conclusion
and its premises, and the transport that change needs. Each entry cites the row's statement or the
proved lemma. The table goes into the outcome (`NEXT.md` §8). The expected table, to be checked,
not assumed:

| index change | rules | transport | status |
|---|---|---|---|
| none (same index, split resource) | `tensorI`, `sumI`, `ret`, `withI`, `proj`, `unitE`, `tensorE`, `sumE`, `zeroE`, `bangE`, `boxI`, `boxE`, `immSub`, `mutSub`, `lolliE`, `app`, `force`, `ofRet`, `lam` (`bindFut` false), `effPerform`, `effRaise`, `nuIn`, `nuOut`, the premise-free constants other than the borrow constants | none | — |
| list extended (`Ext`) | `bind`, `effLet`, `effThen`, a lend's end | `MonoExtM` | proved (`monoExtM0`) |
| re-lend at a resume or an instantiation | the `U` rows, `effLet` across a stop, the spanning rules | the thaw | proved (`statement0UFullM`) |
| own push, reading extension, shadow | `allI` | `MonoOwnGMAt`, `CtxExtendMSAt`, `CtxShadowMAt` | item 3 |
| own push of a row-polymorphic value | statement 4's `AllRMono` (`RC_allRE`) | `MonoOwnGMAt` at a `U(∀ρ…)` slot of `allI`'s context | inside item 3's `U`-slot case |
| hiding | `effHandle` | `MonoHideGM` | §4.1 |
| callback at its own push | the borrow constants (`withbor` (1)–(3), `withload`, `foldImm`, the slices), their unwinding forms (`withbor1U/2U/3U`, `withloadU`, `sliceBorrowMU/IU`), the spanning rules | `CallbackExt*M` (and item 1 at a block) | proved at one entry |

These are owed rows that are not monotonicity consumers. They are flagged, not decided:
- `roll` and `unroll`: item 2.
- `allE` and `allEV`: the lifetime substitution, `cRLM` at `C.instLife x b` read at
  `δ.extend x ⟦b⟧`. It is not stated at `vRLM`; `RetainedPayInstRow` is its `RetainedPay` part, at
  a `b` with no join.
- `effSub`: row subsumption at the `F_Σ` clause.

**The corrected conjunction**, which replaces `Statement0MAtConsumers0` in every claim:

```lean
/-- **Statement 0 at `binder0`, read at all its consumers**: beside monotonicity; the record order;
the `∀I` row (its context across the own push, to the binder's reading and the shadow; statement
4's `AllRMono` is this transport at a `U(∀ρ…)` slot); and `[handle]`'s context into the hidden
stack. -/
def Statement0MAtConsumers0Full : Prop :=
  Statement0MBesideMono0 (ℍ := ℍ) ∧ MonoExtM (ℍ := ℍ) .binder0 ∧ AllIRowM (ℍ := ℍ) .binder0 ∧
    MonoHideGM (ℍ := ℍ) .binder0
```

**Success and failure.**
- **Success.**
  - `hideInvisible`, `vRLMHideAvoid` and `monoHideGMHandle0` are proved.
  - The table is complete. Each row cites a statement, and each "none" entry is checked against
    the row's statement.
  - `Statement0MAtConsumers0Full` is stated, and `statement0MAtConsumers0_iff`'s docstring says it
    holds by the definition of our conjunction.
- **What may be claimed.** "Statement 0 at `binder0`, read at its consumers, is
  `Statement0MAtConsumers0Full`; its open parts are `AllIRowM` at the contexts §3.5 lists and
  `MonoHideGM` where the hidden name crosses an entry and a live type carries it." The claim
  "reduces to the `∀I` row" is withdrawn.

---

## 5. Order of work and the stop rule

1. **Item 1a** (`Nx.lean`, `NxGuard.lean`). It decides whether item 1b exists.
2. **Item 2** (`NxUnroll.lean`). Independent and mechanical.
3. **Item 3** (`NxAllI.lean`), in this order:
   - (E1)–(E3) in `R1.lean`, with the touched proofs re-proved;
   - §3.2;
   - §3.3;
   - §3.4;
   - §3.5's record.
4. **Item 4** (`NxHide.lean`, and the table).
5. **Item 1b** (`NxBlock.lean`, `NxBlockRows.lean`), only if 1a is real. It runs last because it
   changes the stack's representation, which every later proof reads. Run last, it is one revision
   that carries item 3's edits too, and (2)–(4) are already done whatever it does.
6. **Docs**:
   - this file's §8 (the outcome) and report lists;
   - README's file table;
   - DESIGN §15.10;
   - CHECKPOINT;
   - correcting the R1 unit's two major findings in README, DESIGN §15.9 and `R1MONO.md` §8 (the
     "exactly its `∀I` row" claim, with §4's table, and the `withload` gap's condition, with
     item 1a's result).

The orchestrator puts item 1 first. Only its arising check (1a) runs first. Its fix (1b) moves last
for the reason in step 5.

**The stop rule.**
- **If item 1's route fails** (1a not real, or 1b's gate failing), items (2) and (3) are still done.
  The order guarantees it. 1a's failure skips 1b, and 1b's failure leaves `vRLM` as the one draft
  relation.
- **Item 2** failing at a clause does not stop items 3 or 4.
- **Item 3.** If (E1)–(E3) cannot land within the listed edits, revert them and proceed as §3.6's
  failure branch.
- **Item 1b.** §1.7.
- **Everywhere.**
  - A refutation is a fact about our statement unless it passes DESIGN §11: a configuration in
    `ArisesI`, values in `ArisesVI`, and a closed derivable program.
  - A step that would need a new relation family, a step index, a second guard beside `TW`, or an
    edit outside ProbeD1 stops that item and is reported as a finding about the structure.
- Commit after each step, with the trailer lines. Never push and never touch `main`. Do not touch
  `~/repos/borrow-core-tier1`.

---

## 6. Files

| file | contents |
|---|---|
| `Nx.lean` | all of this unit's definitions and `def … : Prop` statements (items 1a, 2, 3, 4) |
| `R1.lean` (edited) | (E1) `InScope` in the `∀` clause, (E2) `OwnPushM` in the own-lend conjunct, (E3) `StackJM` in `SemSM`; `InScope`, `OwnPushM`, `StackJM` defined above `vRLM` |
| `NxGuard.lean` | item 1a's proofs |
| `NxUnroll.lean` | item 2's proofs |
| `NxAllI.lean` | item 3's proofs, and the re-proofs (E1)–(E3) require |
| `NxHide.lean` | item 4's proofs |
| `NxBlock.lean`, `NxBlockRows.lean` | item 1b: `vRLMB`/`cRLMB`/`SemSMB`, `ArisesB`, the gate, the rows |

`ProbeD1.lean` imports each new file.

---

## 7. Report lists (to fill in the outcome)

- **Printed objects read**:
  - [TR] 6.150 (`TW.reb`, `TW.rebEnd`, `wpG_reborrow`);
  - [TR] p. 5's `reb_α` (`ResU.RebAt`);
  - [TR] 6.175 (`withload_compatX`, its bound `⊓Δ`);
  - [TR] 6.64's and 6.65's H4 (the lends at the new transitions);
  - spec §9's slice borrows (`sliceBorrowITy`).
- **Printed hypotheses unspent**: list them per lemma.
- **Uniqueness and functionality results**: `ResU.CompS.functional`, `CellU.CompS.functional` and
  `RebAt`'s piece disjointness are expected; list which are used and which are not.
- **Printed lemmas in the run-up that are untranscribed**:
  - none expected for items 2–4;
  - for item 1b, the share's block re-lend (GhostEnd's `openFS` reads strict re-lends) is a
    forward obligation, not a printed lemma.
- **Hypotheses added and edits made**:
  - (E1)–(E3), each with its producers and consumers;
  - `PushStableV` as the push's domain;
  - item 1b's definitions, if it runs.
- **The technique built**: no printed proof governs W's draft relation. `VRLMSubst` is `vCE_subst`'s
  route at W's clauses. `VRLMReadEquiv` is a symmetric invariance, not a one-way transport, because
  `⊸` reads its argument contravariantly.

---

## 8. Outcome

To be written by the build.
