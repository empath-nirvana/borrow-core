# ProbeD1: the two-cell guard gap, the unroll row, the `∀I` row's open cases, `MonoHide` — the design

This is the design for the unit after the R1 unit (`R1MONO.md`, commit `5210cf1`). It plans four
items, in the order of §5, and states every target as a Lean `def … : Prop` with its route, the
lemmas it reuses, what counts as success or failure, and the arising check any counterexample must
pass. It contains no proofs. §8 answers the design review's findings.

The statements go in a new statements file `Nx.lean` (definitions and `def … : Prop` only). It
imports `R1AllI.lean`, and `Statement34.lean` for statement 4's open types. Items 1a's and 2's
statements are written first. Every statement that reads `InScope`, `OwnPushM` or `StackJM` (1a′'s,
item 3's, item 4's `AllRMonoM0`, item 1b's gate) is added at step 3.0, once (E1)–(E4) have landed in
`R1.lean`. The proofs go in `NxGuard.lean` (item 1a, then 1a′), `NxUnroll.lean` (item 2),
`NxAllI.lean` (item 3) and `NxHide.lean` (item 4). If item 1b runs, its revised relation and rows go
in `NxBlock.lean` and `NxBlockRows.lean`.

Every Lean block in this file elaborates against the built ProbeD1 at `5210cf1`, with (E1)–(E3)'s
three definitions given beside the blocks that read them [checked outside the build: a scratch file,
not committed]. The exception is §1.6's `vRLMB` clause, which is a fragment. *[unchecked]* marks a
claim argued in prose and not in Lean; *[read]* marks a claim read off the source.

Item 3 edits existing definitions and statements (§3.1):
- the one draft relation and its judgement, in `R1.lean`: (E1) `InScope` in the `∀` clause's first
  conjunct, (E2) `OwnPushM` in its own-lend conjunct, (E3) `StackJM` in `SemSM`;
- (E4) the hypothesis `¬ VFree y T` added to `CallbackExtMutM` and `CallbackExtImmM` (`R1.lean`);
- two statements that (E1) and (E2) make false, or unprovable by their proofs, as they stand:
  `RelMAgreesJ` and its three helper equalities are restated at types with no lifetime `∀`
  (`R1.lean`, `R1Thaw.lean`), and `muAdjNotVRLM` is withdrawn (`R1Thaw.lean`).

Those are the unit's only edits to existing definitions and statements, and the outcome must list
them.

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
the guard. The missing step is one configuration that arises at which `withload`'s row, at its own
index, hands its callback a resource that the guard rejects at both stacks the callback's `∀`
clause reads there. The typed world already contains [TR] 6.150's entry as a constructor: `TW.reb`
(`Core/World.lean:122`) composes the reborrowed resource `cb ∈ reb_β(r.R)` into the world at a
record's `imm` cell. So the arising check is a `TW` history:
- allocate the owner of `Ref 1 ⊗ Ref 1` and its two cells;
- open the 6.64 lend (`LendImmI`, so the configuration is in `ArisesI` and the view is in
  `ArisesVI`);
- apply `TW.reb` at the lend's record, at the lifetime of an own push of the callback's type.

`WithloadPairGapReal` is one existential over that configuration, and it carries every link:
- the configuration arises, and so does the view;
- the typed judgement `p : Imm '0 (Ref 1 ⊗ Ref 1) ⊢ withload p cb` has `SemSM`'s index there, with
  the view as its context;
- the view's cell is the record's, and `TW.reb` reborrows that cell's witness;
- the reborrow's lifetime is the own push's;
- beside every closure resource, the composite fails the table at the stack itself and at the push.

`PairCallbackGuardFails` is the lemma that closes the last link. It is not a conjunct of "real".
"Real" means real for [TR] 6.175's `reb_β` route. `PairCallbackGuardFailsLe` extends the guard's
rejection to any two borrow cells no longer-lived than the outermost lend. Slices get the same
single-configuration statement.

Item 1a's claims are about `vRLM` as it stands at `5210cf1`, before (E1)–(E4), and they are
re-checked after the edits land. The empty stack is not part of 1a:
- Before (E1), the table at `[]` holds of every resource, so the first conjunct reads the callback
  there and there is no gap (`PairNilOldGuardHolds`).
- After (E1), no instance in scope at the empty stack is below `⊓Δ`, so only the own push remains,
  and the push fails the guard. This case is decided against the edited relation in step 3.0 (item
  1a′, `WithloadPairGapNilE1`). It is a cost of (E1), disclosed before (E1) lands (§3.1).

If the gap is real, the fix is to the entry, not the table. A table that admits the cells would
leave cells at an internal lifetime that are neither a view nor above the cut. The thaw could then
only retain them, which breaks the cut, or transport them, which re-reads a stored invariant at a
moved reading. That is `mut_not_natural`'s mechanism, which the freeze binder exists to avoid. The
entry fix is a **block**: one lend of several places at one lifetime, under one binder. It is
represented with GhostEnd's `LEnt` unchanged, as consecutive entries sharing variable and lifetime.
Its cost is `StackOK`'s strict chain becoming a block chain (`StackOKB`), so every row at `binder0`
is re-proved at the revised relation. That work is scheduled last (§5).

**Item 2: `VRLMUnroll`.** This is a port of `Core/RelMu.lean` (`vCE_some`, `vCE_rename`,
`vCE_subst`, `vC_inst`, `vC_unfold`) to `vRLM`'s clauses, using the already-proved `vRLM_mono_at`
and `vRLM_roll`. The rows `RollRowM` and `UnrollRowM` follow at every placement.
- **Why it is owed.** `vRLM`'s `μ` is its own least fixed point over W's clauses, and Core's
  unroll equation is about Core's. This does not depend on `muAdjNotVRLM`, which (E1) is expected
  to make false (§3.1).
- **Which relation.** Item 2 is proved against `SemSM` before (E3) and re-proved after it.
- **Premises.** `RollRowM` takes exactly the `roll` rule's premises and adds none.

The work is mechanical, and no counterexample is expected.

**Item 3: the `∀I` row's open cases.** Four edits come first:
- (E1) instances in scope;
- (E2) own lends whose payload types read only the type's free variables, and not the binder;
- (E3) `StackJ`'s third kind pushed fresh below the reading and read by no entry's payload
  (`StackJM`). This is justified at `binder0`, where no clause produces it. `cbpv`'s `U` own push at
  `vRLM` meets neither conjunct, and that is recorded;
- (E4) `¬ VFree y T` on the callback statements, from the constants' side condition `hfree₁`.

Each edit's costs are disclosed, and §3.1's table gives every result the edits touch a disposition:
re-proved, restated, withdrawn, or rebuilt unchanged. Then:
- *The binder-named index.* `SubOutsideExtendNamed` follows from `StackJM`'s `SubFresh`. At a live
  `U` slot, the reading transport `CtxExtendNamedMSAt` follows from `StackJM`'s payload avoidance.
- *A live `U` slot, the readings.* One symmetric lemma (`VRLMReadEquiv`) gives all three reading
  transports, each with `X = {x}`: the extension at a new variable, the extension at the named
  entry's variable, and the shadow after the push. Its base-reading conjunct agrees off `X`, because
  GhostEnd's views and the operation table read the base reading.
- *A live `U` slot, the push.* It is proved where the slot is push-stable (`PushStable`). The slots
  outside `PushStable` are the target, because `reconB′`'s callback captures `retryR` (DESIGN §9.2),
  whose instances have a `!U` argument and an effect layer.
  - The push's case at each former outside `PushStable` is stated as an elaborating
    `def … : Prop`: `PushArrStep` (refuted as stated at `gd`), `PopUStep`, `PushEffStep` and
    `PushAllStep`.
  - Each case is attempted unrestricted, then under the Core-value restriction (`MonoOwnGMCAt`).
  - `reconB′`'s term is not changed.

**Item 4: `MonoHide` and the consumers.**
- `MonoHide` at `vRLM` is invisible when the hidden names cross no entry, or when no live type
  carries them. That covers both programs. The general case gets one bounded attempt, and its
  failing step is stated as an elaborating `def … : Prop` (`HideStopStep`).
- The consumers check starts from an inventory: every use of `MonoV`, `MonoG`, `MonoOwnG`, `MonoC`,
  `MonoHide` and their `M` forms in the statement files and DESIGN, each mapped to a replacement at
  `vRLM` or marked "remains".
  - Statement 4 gets its own entry: `AllRMono` at `vRLM` over the open types (`AllRMonoM0`), with
    a record-order half and an own-push half.
  - Every row with no proof at `vRLM` is marked [unchecked: no row proof at vRLM].
  - The expected answer is that `AllIRowM` and `MonoExtM` are **not** all the consumers.
    `MonoHideGM` and `AllRMonoM0`'s own-push half remain.
- Three owed rows are flagged that are not monotonicity: `VRLMUnroll` (item 2), the lifetime
  substitution `∀E` reads, and `effSub`.
- Only after the inventory and the table are complete may a document say what statement 0 at
  `binder0` reduces to, and then only with the table's caveat.

**Order.** (1a) → (2) → (3: (E1)–(E4), then 1a′, then §3.2–§3.5) → (4) → (1b) → docs. (2) and (3)
are done whatever item 1 does (§5).

---

## 1. Item 1: the two-cell guard gap

### 1.1 What is proved, and the missing step

- `rebGuardFails` and `loadGuardFails`: the table rejects a reborrowed cell exactly at the own
  lend's lifetime `α`, at a place the pushed stack does not lend.
- `loadGuardFails2`: it rejects two such cells, at distinct places the old stack does not lend, at
  every pushed stack.
- `sliceGuardFails`: it rejects two slice elements.
- `RetainedPaySliceRow`: proved, but vacuous.

Each of these is a fact about the table (`TabAtS`), which (E1)–(E4) do not change.

What the R1 review asked for (CHECKPOINT WARNING) is the step from a configuration that arises,
through the reborrow, to two top-level cells at the callback's guard, composed with the closure's
resource. It was asked for at `ArisesI` "ideally". The design review added that every link must be
proved of the same configuration, and not as a conjunction of facts each provable on its own.

### 1.2 What "real" means here

"Real" is one Lean fact about one configuration `c` (`WithloadPairGapReal`), held to the arising
set's own standard (DESIGN §11). Each item below is a conjunct about that `c`.
- **(a) It arises.** `c ∈ ArisesI`, by a `TW` history and a 6.64 lend (`LendImmI`). Its stack is
  one entry `e`, named `'0`, at `α`, over `Ref 1 ⊗ Ref 1`. Its local part holds `e`'s view `ψ` at
  `e.l`, and the view arises (`ArisesVI.view`).
- **(b) It is the row's index.** The typed judgement
  `'0 ⊏ ⊤; p : Imm '0 (Ref 1 ⊗ Ref 1) ⊢ withload p cb : F B` (`ProbeRules`) has `SemSM`'s index at
  `c`: `SemIdxM` at `c`'s stack, lifetimes and list and at the view's resource
  (`ResU.single e.l ψ`), and `gRLM` at `γ = [loc e.l]`.
- **(c) The view is the record's, and the reborrow is the push's.** The open frame's record `r`
  (`r ∈ c.ps`, `r ∈ rsOf c.ls`, `r.le = e.l`) has `ψ.wit = r.R`, and `r.R` owns two distinct places
  that no entry lends. The callback's type has an own push `en` at `β` at that index (`OwnPushI`).
  `en`'s payload type is closed, so `OwnPushM` follows once (E2) lands. `TW.reb` reborrows `ψ.wit`
  at that same `β` into a tagged `TW` world.
- **(d) The guard reads the argument and rejects it.** Beside every closure resource, the composite
  with the reborrowed resource fails the table at the stack itself and at `en :: σ`. These are the
  two stacks the callback's `∀` clause reads at that index:
  - its first conjunct reads the stack itself, at every instance below the bound, `β` among them
    (`OwnPushI`'s `LtLife`);
  - its own-lend conjunct reads the push.

  The `⊸` inside the callback's answer reads the guard at that composite, whatever the closure
  holds.

**Which relation.** 1a's statements are about `vRLM` before (E1)–(E4): the index is `SemIdxM` (with
`StackJ`), and the push is `OwnPushI`. After the edits land, the same configuration is re-checked in
step 3.0:
- `StackJM` holds at `c`, because its entry is `pairΔ`'s;
- `OwnPushM` holds at `en`, because its payload type is closed;
- the first conjunct reads no instance at `c`, because at the reading `δ = ∅` the only value in
  scope is `α`, and the bound is `α`.

So (d)'s first part holds both before and after the edits.

| statement | what it is about |
|---|---|
| `PairRebCells` | `ResU.Reb` and `vShape`; no relation |
| `PairCallbackGuardFails`, `PairCallbackGuardFailsLe`, `SliceCallbackGuardFails`, `PairNilOldGuardHolds` | the table and the guard's views, which no edit changes |
| `PairBoundBelow` | `LtLife` at `extS`; no relation |
| `PairWithloadTyped`, `SliceTyped` | typing |
| `PairArgCellsLe` | Core's `vC` and `TW` |
| `WithloadPairGapReal`, `SliceGapReal` | `vRLM`, `SemIdxM` and `OwnPushI` before (E1)–(E4); re-checked after |
| `WithloadPairGapNilE1`, `SliceGapNilE1` (1a′) | the edited relation (`InScope`, `OwnPushM`) |

**What "real" covers.** It is real for [TR] 6.175's `reb_β` route, where the argument is `TW.reb`'s:
two `imm` cells exactly at `β`. Core's `ptoImmS` relates an argument read at an instance with cells
at any lifetime at or above that instance, so the callback's argument relation admits other
resources too. `PairCallbackGuardFailsLe` shows that the guard rejects any two borrow cells no
longer-lived than the outermost lend. Whether every argument the row could hand over, composed
into a valid `TW` world beside the frame, has its cells there (`PairArgCellsLe`) is optional and
[unchecked]. Until `PairArgCellsLe` is proved, "real" is claimed for the `reb_β` route only.

**The empty stack is not in 1a.**
- Before (E1), GhostEnd's table at `[]` holds of every resource (`head?` and `getLast?` are
  `none`), and so do the guard's views (`PVLNil`). So at the empty stack the callback's first
  conjunct reads its run on the reborrowed argument, at every instance below the bound. There is
  no gap at the empty stack before (E1) (`PairNilOldGuardHolds`).
- No statement in the probe forces the spanning `withload` (`SpanLoadRow`) onto the own push before
  (E1). Whether `withload` pushes an entry at all is DESIGN §6.2's open "entry-kind finding"
  (`BINDER.md` §5.4 R2).
- After (E1), at the empty stack with a reading that maps only `Δ`'s variables, each once, no
  instance in scope is below `⊓Δ`. So the first conjunct reads nothing, and the own push fails the
  guard (`PairCallbackGuardFails` at `σ = []`). That is (E1)'s cost. Step 3.0 decides it in Lean,
  against the edited relation (`WithloadPairGapNilE1`, §1.3).

### 1.3 The statements (item 1a)

```lean
/-- `Ref 1 ⊗ Ref 1`: a payload with two `Ref` leaves side by side. -/
abbrev pairTy : VTy := .tensor (.ref .unit) (.ref .unit)

/-- `'0 ⊏ ⊤`: the lend's binder, the lifetime context the program is typed in. -/
abbrev pairΔ : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `p : Imm '0 (Ref 1 ⊗ Ref 1)`: the view, the one live slot. -/
abbrev pairΓ : Ctx VTy := [⟨.imm (.var 0) pairTy, true⟩]

/-- `withload`'s callback type at the pair (`axWithloadTy`), as the computation type its `U`
clause forces: `∀'x ⊏ ⊓Δ. F (Imm̲ 'x (Ref 1 ⊗ Ref 1) ⊸ ['x] B)`. -/
abbrev pairCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (pairTy.immReborrow (.var x)) (.box (.var x) B)))

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

/-- **The guard rejects the reborrowed argument at both stacks** (`loadGuardFails2`,
`tabAtS_comp`). Beside any closure resource, two `imm` cells exactly at `β`, at distinct places the
stack does not lend, fail the table at the stack itself when `β` is below its innermost lend, and
at every own-lend push at `β`. At `αs = []` the first part is vacuous: the table at `[]` holds of
every resource. A lemma for `WithloadPairGapReal`'s last conjunct. -/
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

/-- **The guard rejects any two borrow cells no longer-lived than the outermost lend.** At a stack
with a lend, one such cell at a place the stack does not lend fails the table's second conjunct. At
every own-lend push, two of them at distinct places do, since the push lends at most one. Cells of
any kind but `own`, at any lifetime at or below the outermost lend `o`. -/
def PairCallbackGuardFailsLe : Prop :=
  ∀ (σ : LStack) (αs : List Life) (o : Life) (cb ρk ρ : WRes) (l₁ l₂ : BoCa.Loc)
    (ψ₁ ψ₂ : CellU BoCa.Loc Val),
    l₁ ≠ l₂ → l₁ ∉ σ.map LEnt.l → l₂ ∉ σ.map LEnt.l →
    cb.get l₁ = some ψ₁ → cb.get l₂ = some ψ₂ → ψ₁.kind ≠ Kind.own → ψ₂.kind ≠ Kind.own →
    ψ₁.at ≤ o → ψ₂.at ≤ o → ResU.CompS ρk cb ρ →
      (αs.getLast? = some o → ¬ TabAtS σ αs ρ) ∧
      ∀ (en : LEnt) (β : Life), StackOK (en :: σ) (β :: αs) → (β :: αs).getLast? = some o →
        ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **Optional, [unchecked]: every argument the row can hand over has its cells there.** A
resource related, at Core's relation, at `Imm̲ 'x (Ref 1 ⊗ Ref 1)` at the pair, with `'x` read
below the `imm` cell whose witness owns the two places, that composes into a valid typed world
holding that cell, has both of its cells at lifetimes at or below that cell's. With
`PairCallbackGuardFailsLe` it would extend "real" beyond the `reb_β` route. -/
def PairArgCellsLe : Prop :=
  ∀ (s : LSub) (x : LifeVar) (β' : Life) (ls : List SRec) (l₁ l₂ le : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (cb W W' : WRes) (ps rs : List FrameRec),
    TW W ps rs → W.get le = some ψ → ψ.kind = Kind.imm → β' < ψ.at →
    ψ.wit.get l₁ = some (CellU.ownOf .unit) → ψ.wit.get l₂ = some (CellU.ownOf .unit) →
    vC true (pairTy.immReborrow (.var x)) ls (s.extend x β') (.pair (.loc l₁) (.loc l₂)) cb →
    ResU.CompS W cb W' → ResU.Valid W' →
    ∀ (l : BoCa.Loc) (φ : CellU BoCa.Loc Val), (l = l₁ ∨ l = l₂) → cb.get l = some φ →
      φ.at ≤ ψ.at

/-- **`withload`'s bound reads below the lend**: inside a callback whose binder `'0` the stack reads
at `α`, every instance of `withload`'s `∀'x ⊏ ⊓Δ` (`Δ = '0 ⊏ ⊤`) is below `α`. So the first
conjunct is read only below the innermost lend. -/
def PairBoundBelow : Prop :=
  ∀ (δ : LSub) (e : LEnt) (α β : Life), e.x = 0 →
    LtLife (extS δ [e] [α]) pairΔ.meetOfDom β → β < α

/-- **Typing reaches `withload` at the pair inside a lend**: under the lend's binder `'0`, the view
`p : Imm '0 (Ref 1 ⊗ Ref 1)` applied to `withload` with a callback, in the probe's rule set
(`probeRules_of_nu` from a `Targets.CDerivesNU` derivation, as `gdMtDerivable`). A lemma:
`WithloadPairGapReal` carries the judgement with its own `cb` and `B`. -/
def PairWithloadTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules pairΔ pairΓ (.app (.app withload (.var 0)) cb) (.comp (.ret B))

/-- **The two-cell gap is real at `withload`, at one configuration.** The configuration is in the
revised arising set, with one 6.64 entry named `'0` over `Ref 1 ⊗ Ref 1` at `α`. Its local part
holds the entry's view `ψ`, and the view arises there. `ψ`'s witness is the open frame's record's,
and it owns the payload's two places, which are distinct and lent by no entry. At that
configuration:
- the typed judgement `p : Imm '0 (Ref 1 ⊗ Ref 1) ⊢ withload p cb : F B` has `SemSM`'s index, at
  `γ = [loc e.l]`, with the view as its context;
- the callback's type has an own push `en` at `β`, whose payload type is closed;
- [TR] 6.150's step (`TW.reb`) reborrows `ψ`'s witness at that `β` into a tagged typed world;
- beside every closure resource, the composite fails the table at the stack itself, where the `∀`
  clause's first conjunct reads it, and at the push.

Real for 6.175's `reb_β` route. The claim is about `vRLM` before (E1)–(E4); §1.2 says what is
re-checked after them. -/
def WithloadPairGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
      (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) (cbE : Expr) (x : LifeVar) (en : LEnt)
      (β : Life) (ρc cb fρ' : WRes),
    -- (a) the configuration and its view
    ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧ e.T = pairTy ∧
    c.ρ.get e.l = some ψ ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' (ResU.single e.l ψ)) (.loc e.l) (viewTy e) ∧
    -- (c) the view's cell is the record's
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.le = e.l ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧
    ψ.wit = r.R ∧ r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧
    l₁ ≠ l₂ ∧ l₁ ∉ c.σ.map LEnt.l ∧ l₂ ∉ c.σ.map LEnt.l ∧
    -- (b) the typed judgement and its index at `c`
    ProbeRules pairΔ pairΓ (.app (.app withload (.var 0)) cbE) (.comp (.ret B)) ∧
    SemIdxM pairΔ pairΓ (.ret B) δ c.σ c.αs c.ls (ResU.single e.l ψ) ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls pairΓ [.loc e.l] (ResU.single e.l ψ) ∧
    -- (c) the callback's own push at that index, at `β`
    OwnPushI δ (pairCbC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    -- (c) 6.150's step at that `β`, reborrowing the view's witness
    ¬ VFree x r.T ∧ ResU.Reb β ψ.wit cb ∧
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb ∧ StratumLe c.fρ β ∧
    ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls ∧
    -- (d) the composite fails the table at both stacks the `∀` clause reads
    ∀ ρk ρ : WRes, ResU.CompS ρk cb ρ →
      ¬ TabAtS c.σ c.αs ρ ∧ ¬ TabAtS (en :: c.σ) (β :: c.αs) ρ

/-- **At the empty stack the guard holds of every resource** (GhostEnd's `TabAtS` at `[]`;
`PVLNil`). So before (E1) the callback's first conjunct at the empty stack reads its run on the
reborrowed argument, at every instance below the bound, and there is no gap there. A fact about
`vRLM` before (E1). -/
def PairNilOldGuardHolds : Prop :=
  ∀ (s : LSub) (ls : List SRec) (ρ : WRes), TabAtS [] [] ρ ∧ PlaceViewsL s [] [] ls ρ
```

**Item 1a′: the empty stack after (E1).** This statement goes in `Nx.lean` when (E1)–(E4) land
(step 3.0), since it reads `InScope` and `OwnPushM`.

```lean
/-- **After (E1), the gap at the empty stack.** The configuration is in the revised arising set at
the empty stack. Its world holds an open 6.64 frame over `Ref 1 ⊗ Ref 1`, and its local part holds
the frame's `imm` cell `ψ`. At it:
- the typed judgement has its index, at a reading `δ` whose only value is `ψ`'s lifetime, with the
  cell's place as the context;
- the callback's own push is at `β`, at `OwnPushM`;
- `TW.reb` reborrows `ψ`'s witness at that `β`.

No instance in scope meets the bound, so the first conjunct reads nothing. Beside every closure
resource, the composite fails the table at the push. So after (E1) the own push is the only route,
and it fails. Before (E1) the first conjunct read the callback here (`PairNilOldGuardHolds`). `p`
is not shown to arise by `ArisesVI`: no transition of the set makes an `Imm` value arise at the
empty stack, other than a run's answer. What is shown is the configuration's world and the index. -/
def WithloadPairGapNilE1 : Prop :=
  ∃ (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy)
      (cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc cb fρ' : WRes),
    ArisesI (ℍ := ℍ) c ∧ c.σ = [] ∧ c.αs = [] ∧ c.ρ.get r.le = some ψ ∧
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧ ψ.wit = r.R ∧
    r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧ l₁ ≠ l₂ ∧
    ProbeRules pairΔ pairΓ (.app (.app withload (.var 0)) cbE) (.comp (.ret B)) ∧
    SemIdxM pairΔ pairΓ (.ret B) δ [] [] c.ls (ResU.single r.le ψ) ∧
    gRLM (ℍ := ℍ) .binder0 [] δ [] c.ls pairΓ [.loc r.le] (ResU.single r.le ψ) ∧
    OwnPushM δ (pairCbC x B) ρc ([], []) en β ∧
    ¬ VFree x r.T ∧ ResU.Reb β ψ.wit cb ∧
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb ∧ StratumLe c.fρ β ∧
    ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls ∧
    (∀ β', LtLife δ pairΔ.meetOfDom β' → ¬ InScope δ β') ∧
    ∀ ρk ρ : WRes, ResU.CompS ρk cb ρ → ¬ TabAtS [en] [β] ρ
```

`SliceGapNilE1` is the same statement at a slice (`sliceΓ`, `sliceCbC`, the family of two 6.64
frames below), and is stated with it.

**Slices.** The family comes from an owned array that a run at the stack makes (`array_new`, so
the array arises by `ArisesVI.ret`). The slice borrow's run makes two 6.64 frames at `β`
(`TW.immFrame` at each element), which give the `[Imm 'x 1]` family. The imm form is used so that
no `mutFold` with an arbitrary predicate enters; the guard reads only places and lifetimes in any
case.

```lean
/-- `a : Array 1`: the owned array, the one live slot. -/
abbrev sliceΓ : Ctx VTy := [⟨.array .unit, true⟩]

/-- `slice_borrow_imm`'s callback type at `Array 1` (`sliceBorrowITy`), as a computation type. -/
abbrev sliceCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (.arrayImm (.var x) .unit) (.box (.var x) B)))

/-- **The two-cell gap is real at a two-element slice, at one configuration.** The configuration
is in the revised arising set, with one 6.64 entry named `'0` at `α`, and an owned array of two
elements at `ℓ` and `ℓ + 1` (places no entry lends) arises there at `Array 1`. At it:
- the typed slice judgement has `SemSM`'s index at `γ = [arr ℓ 2]`, with the array as its context;
- the callback's type has an own push `en` at `β`, whose payload type is closed;
- two 6.64 frames at `β` turn the elements into a family `ρs` of `imm` cells exactly at `β`, part
  of a tagged typed world;
- beside every closure resource, the composite fails the table at the stack itself and at the
  push. -/
def SliceGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ℓ : BoCa.Loc) (u₀ u₁ : Val) (ρa ρf' : WRes) (δ : LSub)
      (B : VTy) (cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc X Z ρs W' : WRes)
      (ps' : List FrameRec) (ls' : List SRec),
    ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' ρa) (Val.arr ℓ 2) (.array .unit) ∧
    (∀ i < 2, ℓ + i ∉ c.σ.map LEnt.l) ∧
    ProbeRules pairΔ sliceΓ (.app (.app withbor (.var 0)) cbE)
      (.comp (.ret (.tensor (.array .unit) B))) ∧
    SemIdxM pairΔ sliceΓ (.ret (.tensor (.array .unit) B)) δ c.σ c.αs c.ls ρa ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls sliceΓ [Val.arr ℓ 2] ρa ∧
    OwnPushI δ (sliceCbC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    ResU.CompS (ResU.single ℓ (CellU.ownOf u₀)) (ResU.single (ℓ + 1) (CellU.ownOf u₁)) X ∧
    ResU.CompS X Z c.fρ ∧ ResU.CompS ρs Z W' ∧
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) ∧
    TW W' ps' (rsOf ls') ∧ Tagged W' ps' ls' ∧
    ∀ ρk ρ : WRes, ResU.CompS ρk ρs ρ →
      ¬ TabAtS c.σ c.αs ρ ∧ ¬ TabAtS (en :: c.σ) (β :: c.αs) ρ

/-- **The guard rejects the family at both stacks** (`sliceGuardFails` with `tabAtS_comp`, and the
old stack's first conjunct). A lemma for `SliceGapReal`'s last conjunct. -/
def SliceCallbackGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (β : Life) (ρs ρc ρ : WRes) (ℓ : BoCa.Loc),
    (∀ i < 2, ℓ + i ∉ σ.map LEnt.l) →
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) →
    ResU.CompS ρc ρs ρ →
      (∀ h, αs.head? = some h → β < h → ¬ TabAtS σ αs ρ) ∧
      ∀ en : LEnt, StackOK (en :: σ) (β :: αs) → ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **Typing reaches a slice borrow inside a lend** (`withbor` at `sliceBorrowITy`). A lemma. -/
def SliceTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules pairΔ sliceΓ (.app (.app withbor (.var 0)) cb)
      (.comp (.ret (.tensor (.array .unit) B)))
```

The world-link conjuncts (the `TW` and `Tagged` facts and the parts that compose to them) may be
tightened while proving. Nothing else may be weakened:
- the links (a)–(d) of §1.2 stay conjuncts about the one configuration;
- the conjuncts the guard argument reads stay as they are: the cells exactly at `β`, the two places
  distinct, the stack's places, and `β` below the lend.

### 1.4 The route and the lemmas reused

- **The world.** `TW.alloc` three times (owner, `l₁`, `l₂`), as `nv_tw₁` does. Then `TW.immFrame`
  at the owner, as `nv_tw₂` does. Its descendants are the sub-records of `R`'s owned cells, if
  `Desc` gives any: compute them, as `nv_not_desc` does. `Tagged` follows `nv_tagged`. The nil
  configuration is `ArisesI.nil`. `ArisesI.lendImm` needs `LendImmI`: `LendImm`'s fields,
  `LendFresh`, and `α < ⊤` (from H4, as `outerBelowTopArises` reads it). The view comes from
  `ArisesVI.view`.
- **The view and the record.** `LendImm` puts `immOf {α} v R h` at `e.l` in the local part, and the
  record `⟨e.l, v, R, e.T, δ⟩` at the head of both `c.ps` and `rsOf c.ls`. So `ψ.wit = r.R`,
  `r ∈ c.ps` and `r ∈ rsOf c.ls` all come from `LendImm`'s own fields.
- **The index.** `SemIdxM` and `gRLM` at the view, at `δ = ∅`:
  - `StackJ`'s first kind (`'0` is `pairΔ`'s);
  - `pairΔ`'s models from `LendImmI`'s `α < ⊤`;
  - `RecsOutside` from `recsOutsideArises`;
  - the table and the guard's views at the view.

  These are the facts `RetainedPayLoadImmRowMet`'s witness would read. The view's `vRLM` clause is
  Core's `Imm` leaf with `CohS` (its entry is `e`) and `RetainedPay` (vacuous at a lent place).
- **The push.** `en` is at a place and variable new to the stack and to the closure's resource,
  with payload type `1`. It sits at a `β` below every lifetime of the world and of `ρc`. That gives
  `OwnOKI`, and `β < α` gives the bound's `LtLife`. `ViewAt` is vacuous, since the body of
  `pairCbC` is a `.ret`.
- **The reborrow.** `TW.reb` needs:
  - `r ∈ rsOf c.ls`;
  - the world's `imm` cell at `r.le`;
  - `¬ VFree x r.T`;
  - `ResU.Reb β r.R cb`, with `π` given by the two singleton pieces;
  - `vShape` at `Imm 'x 1 ⊗ Imm 'x 1`;
  - `StratumLe c.fρ β`, from the choice of `β`;
  - `Valid` of the composite.
- **The cells.** `PairRebCells` comes from `ResU.RebAt`'s `own` clause at each place, with
  `l ∈ dom cb` from the shape's `ptoImm` at each leaf.
- **The guard.**
  - `PairCallbackGuardFails` uses `tabAtS_comp` (`GhostEnd/Arising.lean:83`). The old stack fails
    the first conjunct (`InStratum (↓h)` at a cell at `β < h`), and the push uses
    `loadGuardFails2`.
  - `PairCallbackGuardFailsLe` uses the second conjunct with `lt_at_of_inStratum`, as
    `sliceGuardFails` does.
  - `SliceCallbackGuardFails` uses `sliceGuardFails` the same way.
- **The bound.** `PairBoundBelow` uses `meetOfDomL` at one entry (`meet (var 0) top`) and
  `Life.interp`.
- **Typing.** `CDerivesNU.withload` (and `sliceBorrowI`, `array_new` for the array's run),
  `lolliE`/`app`, and `probeRules_of_nu`.
- **1a′ (step 3.0).**
  - The configuration is `ArisesI.nil` over a `TW` world built by `alloc` three times and
    `immFrame`, with the frame's cell in the local part.
  - The reading is `δ = ⟨[(0, m)]⟩`, where `α = toDual m`.
  - The first conjunct is empty: `δ`'s only value is `α`, and the bound is `α`.
  - The push is at `OwnPushM`, since its payload type is closed.

### 1.5 Success and failure

- **Real** means `WithloadPairGapReal`, or `SliceGapReal`, is proved. Item 1b then runs, last
  (§5).
- **Not real.** A link is false, or its proof needs a change to a definition. Then record which
  link and why:
  - the configuration is not in `ArisesI`, or the view (the array) is not in `ArisesVI`;
  - the index (`SemIdxM`, `gRLM` at the view) is not met at the configuration;
  - no own push is available at the index;
  - `TW.reb`'s premises cannot be met at the configuration;
  - the shape forces fewer than two cells;
  - the composite meets the guard at one of the two stacks;
  - the program is not typable.

  Do not run item 1b, and say why in the outcome.
- **Wording.** "Real" is claimed only for what is proved, and only for the `reb_β` route (and the
  slice's frames) unless `PairArgCellsLe` is proved. A configuration in `ArisesI` with a `TW.reb`
  world is the arising set's standard. It is not a closed program's execution, so it is evidence
  that the guard misses a real argument, and it refutes no row. No printed object is in question:
  the guard and the stack are ours.
- **1a′** is decided in step 3.0, whatever 1a's result. Its outcome is (E1)'s cost made exact (§3.1).

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
reading, never by `x`. -/
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

/-- **The own lend at the type `C`, a block**: its payload types read only variables free in `C`,
as `OwnPushM`'s (§3.1). -/
def OwnPushB (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (τ : LStack) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ x ∉ CTy.binders C' ∧
    OwnOKB δ s.1 s.2 x τ a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    (∀ e ∈ τ, ∀ y, VFree y e.T → CFree y C) ∧
    ∀ A D, C' = .arr A D → ViewAtB x τ A
```

**The revised relation `vRLMB`/`cRLMB`.** It is `vRLM` after item 3's edits (E1)–(E4) (§3.1), with
one change: the `∀` clause's own-lend conjunct pushes a block. It is a revision that replaces
`vRLM` as the one draft relation once its gate rows are proved (convention of
`vRLI → vRLJ → vRLM`). It is written in `NxBlock.lean`, so that `vRLM`'s results stay the
statements they were.

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
and the views at the pushed stack. At `WithloadPairGapReal`'s configuration it is the gap's
fix. -/
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
its instance at the places `ℓ + i`, so no separate statement is needed. With the block, 1a′'s empty
stack is covered too: the push is then a block lending both places.

One gate check concerns non-data payloads. W's `imm` view reads its payload at `vC true`
(GhostEnd's `vwE`), while a reborrowed leaf meets Core's `Imm` clause at `vC false` (the observable
view). At a data payload the two agree. At a payload with a thunk they do not. Record this as the
gate's open obligation: the views would read `imm` payloads at `vC false`, which is a further draft
change and the user's to decide.

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
  stop item 1b, record the failing statement, and keep `vRLM` as the one draft relation. The
  outcome then states (E1)'s cost at the empty stack as a decision for the user (§3.1).
- Re-prove the rows in the order above. Stop at the first row whose proof needs a definition change
  beyond those listed here (`StackOKB`, `LeafTyAt`, `ViewAtB`, `OwnOKB`, `OwnPushB`, the `∀`
  clause, `StackJB`, `SemSMB`, the two transitions). Record the frontier. `vRLMB` stays a candidate
  in its own files until rows 1–4 are proved.
- Never edit GhostEnd, `Targets`, `Core`, `Paper` or `Support`, and add no relation family beside
  the one draft relation.

---

## 2. Item 2: `VRLMUnroll`

### 2.1 The statements

`vRLM` reads `μ` itself, by a least fixed point over W's clauses. So the unroll row needs `vRLM`'s
analog of Core's substitution lemma: Core's `vC_mu_iff` is an equation about Core's clause, and no
lemma identifies the two clauses at a type with a `U` inside. That is the whole reason, and it does
not depend on `muAdjNotVRLM`. The task cites that result (vRLM strictly smaller than Core at `μ`)
as the reason, but it is a fact about `vRLM` before (E1), and (E1) is expected to make it false
(§3.1). Item 2 stands either way.

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

/-- **`roll` at W.** Its premises are the `roll` rule's own (`Targets/Base/Typing.lean:326`,
`roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)`; `RC_roll`, `:744`); it adds none. -/
def RollRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy), A.NoMut 0 → (VTy.mu A).Cl 0 →
    SemSM (ℍ := ℍ) p Δ Γ e (.val (VTy.inst (.mu A) A)) → SemSM (ℍ := ℍ) p Δ Γ e (.val (.mu A))

/-- **`unroll` at W.** The `unroll` rule has no premise beside its derivation (`:329`). -/
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
  - `U`: `VTy.subst` leaves `U C` alone, and `vRLM_thunk_env`. This case never opens `cRLM`, so
    (E1) and (E2) do not touch it.
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
  - `StackJ`: the third kind does not apply at `.ret`, and the second kind's `¬ CFree` transfers
    because the free lifetime variables of the two types agree.

**Which `SemSM`.** Item 2 runs before (E3), so `RollRowM` and `UnrollRowM` are first proved against
`SemSM` with `StackJ`. After (E3) they are re-proved in step 3.0 (§3.1's table). `StackJM`'s added
conjunct needs an outermost `∀`, so it is inert at `.ret`, and the same proof carries it. The
equations `VRLMSome` … `VRLMUnroll` do not read `SemSM` and rebuild unchanged.

### 2.3 Success, failure, arising

- **Success**: `vRLMUnroll`, `rollRowM` and `unrollRowM` at every placement, before (E3) and
  re-proved after it.
- **Failure**: a clause whose port does not go through. Record the clause; it blocks neither item 3
  nor item 4.
- **Arising**: no counterexample is expected. The statements are equations between two readings of
  one definition, and no refutation is planned.

---

## 3. Item 3: the `∀I` row's two open cases

### 3.1 The edits, what each costs, and what each touches

(E1)–(E3) edit `vRLM`, `cRLM` and `SemSM` in `R1.lean`. (E4) edits two statements in `R1.lean`.
Each answers a step of the route below. They land first (step 3.0), and every result in the table
below gets the disposition it lists before any other item-3 work starts.

```lean
/-- **A lifetime in scope at a reading**: the value of one of its bindings. `∀E` instantiates at a
lifetime term, whose value below `⊤` is one of its variables' (`InScopeOfInterp`). -/
def InScope (s : LSub) (α : Life) : Prop := ∃ p ∈ s.entries, OrderDual.toDual p.2 = α

/-- **The own lend at `vRLM`**: `OwnPushI`, with its payload type reading only variables free in
the type (`payLocal`) and not the binder (`selfFree`). Every borrow constant's own lend meets it.
Its payload type is the callback argument's (`ViewAt`, `e.T = T`), a part of the type under the
binder, and the constant's side condition keeps the binder out of it (`hfree₁`, (E4)). -/
def OwnPushM (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  OwnPushI δ C ρ s e a ∧ (∀ y, VFree y e.T → CFree y C) ∧ ¬ VFree e.x e.T

/-- **`StackJ` at `vRLM`.** An entry of the third kind (the innermost, new to `Δ`, named by the
type's outermost `∀`) was pushed fresh below the reading (`SubFresh`), and no entry's payload type
reads its variable. No `binder0` clause produces such an entry. `cbpv`'s `U` own push at `vRLM`
(`RelendU`'s `OwnPush`) asks neither. -/
def StackJM (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  StackJ σ αs δ Δ Γ C ∧
    ∀ e ∈ σ, Δ.find? e.x = none → σ.head? = some e → (∃ c C', C = .all e.x c C') →
      (∀ a ∈ αs.head?, SubFresh δ a) ∧ ∀ e' ∈ σ, ¬ VFree e.x e'.T
```

The edits:
- **(E1)** In `cRLM`'s `∀` clause, the first conjunct's pure hypothesis
  `⌜LtLife (extS δ σ' αs') c α⌝` becomes `⌜LtLife (extS δ σ' αs') c α ∧ InScope (extS δ σ' αs') α⌝`.
- **(E2)** The own-lend conjunct's `OwnPushI` becomes `OwnPushM`.
- **(E3)** `SemSM`'s `StackJ` becomes `StackJM`.
- **(E4)** `CallbackExtMutM` and `CallbackExtImmM` take `¬ VFree y T` as an added hypothesis.
  - Its source: every borrow constant's typing rule carries it as `hfree₁ : ¬ VFree x A`
    (`Targets/Base/Typing.lean:225–313`: `sliceBorrowM`, `sliceBorrowI`, `withbor1`, `withbor2`,
    `withbor3`, `withload` and their unwinding forms). The callback's argument type there is
    `Mut 'x A`, `Imm 'x A` or `Imm̲ 'x A`, with `A` the rule's.
  - It is non-vacuous: it holds at every closed `T`, `1` among them (`k_reached`'s `kC`, `gd`'s
    `gdCy`).
  - It changes what `Statement0MBesideMono0` says. Its two callback conjuncts are now about
    callbacks whose argument's payload type does not read the binder.

**What each edit costs, stated before it lands.**
- **(E1)**:
  - *The empty-stack route of the borrow constants.* Take an index whose stack's variables are all
    `Δ`'s and whose reading maps only `Δ`'s variables, each once. Every value in scope there is the
    value of one of `Δ`'s variables, and none of these is below `⊓Δ`. So at such an index (the
    empty stack among them, and a stack of `Δ`'s own entries), the first conjunct of a callback
    typed `∀'x ⊏ ⊓Δ` reads nothing. At an index with an entry of the second or third kind, or with
    a shadowed binding, an instance in scope below `⊓Δ` may exist, and nothing here depends on
    one. The constants read the callback at their own push (`CallbackExt*M`).
    - At a payload with one leaf, that route exists.
    - At a `withload` payload with two leaves side by side, or at a slice of two or more elements,
      the push fails the guard (item 1a). So after (E1), and with no block (item 1b), these have no
      route at any stack. Before (E1), the empty stack's first conjunct read them
      (`PairNilOldGuardHolds`).

    1a′ decides this in Lean (`WithloadPairGapNilE1`, `SliceGapNilE1`). If 1b's gate fails,
    `vRLM` keeps (E1) and this cost, and the outcome states it as a decision for the user: keep
    (E1), which §3.3's transports read, or revert it, which restores the empty-stack route and
    leaves the live-`U`-slot transports open.
  - *`MuAdjNotVRLM` is expected to become false* [unchecked].
    - At `[muEnt]`, the `U` clause asks for the body at every instantiation of the stack's
      lifetime. With (E1), the first conjunct then reads one instance: the handed view's own
      lifetime, where `Mut '0 1` holds.
    - The own-lend conjunct is vacuous, because `muEnt` is named by the binder `'0` (`OwnOKI.var`).
    - `adj_not_cRLJ` refuted the clause at the instance `1`, in the gap below `⊤`, which (E1) no
      longer reads. So (E1) removes the reading of the gap that `GAP.md` showed W's `U` clause
      making. That is `wU_allPosJ`, a fact about `vRLJ`, and it is unchanged.
    - `MuAdjVRLME1` (below) decides it in Lean right after (E1) lands, before anything relies on
      it. Item 2 does not rest on it (§2.1).
  - *`RelMAgreesJ` at a type with a lifetime `∀`.* `cRLJ` keeps the old clause, so the two
    relations differ at such a type. `RelMAgreesJ` is restated at types with no lifetime `∀`
    (table).
  - *What (E1) keeps.* `∀E` instantiates at `⟦b⟧`, which is a variable's value
    (`InScopeOfInterp`), and `LtLife` rules out `⊤`. A lifetime is then made only by a lend. That is
    the freeze binder's reading: a resume instantiates exactly the lifetimes the frozen computation
    made.
- **(E2)** keeps the own lend's payload type off variables the type does not read. Without it, the
  set of admissible own lends depends on bindings the type ignores. It is also what keeps
  `ReadEquiv`'s base-reading conjunct at a push (§3.3). Its cost is (E4).
- **(E3)** is the restriction item 3 asks for at the named index (§3.2). It is justified at
  `binder0` only: no `binder0` clause produces a third-kind index, so the strengthening removes no
  index a `binder0` row reads.
  - At `cbpv` the producer at `vRLM` is the `U` clause's own push: `RelendU`'s own conjunct at
    `OwnPush` (`Relation.lean:96`, read by `vRLM` at `R1.lean:103`). It asks neither `SubFresh` nor
    `selfFree`. `RelendUI` (`Binder.lean:366`) asks for `SubFresh`, but it is not `vRLM`'s clause.
  - So `cbpv`'s `U` own push at `vRLM` does not meet `StackJM`.
  - No result proved at `vRLM` calls a `cbpv` premise at a third-kind index [to confirm in the
    build]. `cbpv`'s `U` rows are not redone at `vRLM`, and their redo would take `RelendUI`'s own
    conjunct at `OwnPushM`. This is recorded, not fixed here.
- **(E4)** is (E2)'s cost at the callbacks.

```lean
/-- `⟦b⟧` is the value of one of `b`'s variables, or `⊤`'s: a meet or a join of two values is one of
them. At an instance below a bound, `⊤` is excluded, so the instance is in scope. -/
def InScopeOfInterp : Prop :=
  ∀ (s : LSub) (b : Lifetime.Life) (m : ℕ),
    b.interp s = some m → InScope s (OrderDual.toDual m) ∨ m = Lifetime.SLife.top

/-- **After (E1), `GAP.md` §4's adjacency closure is a `vRLM` value at W's own `μ`.** The negation
of `MuAdjNotVRLM`; expected, and decided right after (E1) lands. -/
def MuAdjVRLME1 : Prop := ¬ MuAdjNotVRLM (ℍ := ℍ)

mutual
/-- No lifetime `∀` at any depth, outside a `Mut` or `Imm` payload and outside `ν`. Both relations
read those with Core's relation. -/
def VAllFree : VTy → Prop
  | .thunk C => CAllFree C
  | .tensor A B => VAllFree A ∧ VAllFree B
  | .sum A B => VAllFree A ∧ VAllFree B
  | .bang A => VAllFree A
  | .box _ A => VAllFree A
  | .ref A => VAllFree A
  | .mu A => VAllFree A
  | .fam A => VAllFree A
  | _ => True
/-- The same at a computation type. An effect layer's operation types are read by Core's relation
(`rowTab`), so only its answer type counts. -/
def CAllFree : CTy → Prop
  | .ret A => VAllFree A
  | .arr A C => VAllFree A ∧ CAllFree C
  | .amp C D => CAllFree C ∧ CAllFree D
  | .top => True
  | .all _ _ _ => False
  | .nu _ => True
  | .eff _ _ _ _ _ C => CAllFree C
end

-- `RelMAgreesJ`, restated: `VMuFree A → VAllFree A → vRLM p none … = vRLJ p …` and
-- `CMuFree C → CAllFree C → cRLM p … = cRLJ p …`.
```

**The results the edits touch.** "Rebuild" means the proof is expected to build unchanged.
"Re-proved" means the statement is unchanged and the proof is redone. "Restated" and "withdrawn" are
statement changes, and they are part of the edits.

| result | edits | disposition |
|---|---|---|
| `cRLM_step` (`R1AllI.lean:132`), its `∀` case | E1, E2 | re-proved: the new hypotheses are passed through |
| `all_ownM` (`R1Stmt0.lean:378`) | E2 | its hypothesis `OwnPushI` becomes `OwnPushM`; re-proved |
| `callbackExtMutM_own`, `callbackExtImmM_own` (`R1Stmt0.lean:399`, `:414`), their four instances | E2, E4 | statements restated (E4); re-proved: `payLocal` from `CFree` at `y' ≠ y`, `selfFree` from the added hypothesis |
| `statement0MBesideMono0` (`:439`) | E4 | what it says changes (E4); re-proved |
| `statement0MAtConsumers0_iff`, `not_statement0M_binder0` | follow | rebuild |
| `allIRowMNKAt0_of` (`R1AllI.lean:322`) | E1, E2, E3 | re-proved: the own-lend case takes `OwnPushI` from `OwnPushM`; `StackJM` at both premise indices (the pushed entry is of the first kind; at the extended reading the old entries keep their kinds). `SemSMNK` may keep `StackJ`: at an index whose stack does not name the binder, the two agree |
| `allIRowMNKUFree0`, `allIRowMNKNil0` | follow | rebuild |
| `gdAllIHoldsAtMt` (`R1AllI.lean:670`) | E1, E2 | re-proved: its proof does not read the conjuncts' hypotheses |
| `gdRowRefutation` (`R1Mono.lean:1253`) | E3 | re-proved: `gd`'s index meets `StackJM`, since `gdX.x = 0` is `gdΔ`'s; `GdIndex` keeps `StackJ` |
| `gdIndex`, `gdRelated`, `gdNotPushed`, `notMonoOwnGM0`, `notMonoGM0`, `notMonoVM0`, `monoUnrestrictedRefuted0`, `gdNotCore`, `gdCtxNotCore`, `gdRestrictedMet` | none | rebuild: `gdTy` has no `∀`, and `MonoOwnGM` takes `OwnPushI` as a hypothesis |
| `vRLM_none_eq`, `cRLM_eq`, `effRetM_eq`, `relMAgreesJ` (`R1Thaw.lean:86–193`) | E1, E2 | restated with `VAllFree`/`CAllFree` added; re-proved (`cRLM_eq`'s `.all` case becomes impossible) |
| `muAdjNotVRLM` (`R1Thaw.lean:686`) | E1 | withdrawn. Its proof rewrites with `vRLM_none_eq` at `U(adjC)`, where `adjC = ∀'0 ⊏ ⊤. F (Mut '0 1)` (`Gap.lean:262`), and (E1) is expected to make its statement false. The definition `MuAdjNotVRLM` stays, and the build proves `MuAdjVRLME1` or records it not derived |
| `relendM_thunk`, `relendMValueE`, `relendMValue`, `thawInstM`, `ctxRelendsAllM` (`R1Thaw.lean`) | none | rebuild: they compose instantiations (`instComp`) and never open `cRLM` [read: `R1Thaw.lean:317–331`]. No proof in the development carries the `∀` clause along an instantiation, so `InScope` never has to survive one there. `VRLMReadEquiv`'s `U` case (§3.3) is the first place that needs it |
| `thunkF_U_M`, `thunkV_U_M` (`R1Thaw.lean:582`, `:608`), the four `U` rows, `statement0UFullM` | E3 | re-proved: the premise at the instantiated index needs `StackJM` there. `SubFresh` moves along the instantiation, which is strictly monotone on the reading's values and on the head. The payload avoidance is about types |
| `forceRowM`, `statement0SharedM`, `nilSoundRetM`, `vRLMDataE`, `vRLMMonoAt`, `vRLMRoll` | none | rebuild |
| `monoExtM0`, `monoExtME0`, `monoOwnGUFreeMA`, `monoOwnUFreeMEA`, `vRLM_reading_uFree`, `ctx*MAt_uFree`, `monoOwnGMCUFreeA` | none | rebuild: each passes `cRLM` through at `U` (`vRLM_thunk_ext`) or reads `U`-free types |
| `RetainedPayLoadImmRow`, `RetainedPaySliceRow`, `RetainedPayLoadImmRowMet` | E2 | statements unchanged: they take `OwnPushI`, which `OwnPushM` gives. A `Met` witness should also meet `OwnPushM`'s new conjuncts, so that it witnesses the row as the edited relation reads it |
| item 2's `rollRowM`, `unrollRowM` (proved before E3) | E3 | re-proved: `StackJM` at `.ret` is `StackJ` |
| item 1a's results (proved before E1–E4) | E1–E4 | re-checked (§1.2): the push at `OwnPushM`, `StackJM` at the configuration, and the first conjunct empty there |
| `wU_allPosJ`, `adj_not_wU`, `adj_core_U`, and every `vRLJ` or `vRL` result | none | unchanged: neither relation is edited |
| `R1MONO.md` §0, §1.2, §1.3 and §6's carry-over table ("what carries over" through `RelMAgreesJ`: `k`, `q2`, `adjIndex`, `MuSlotIndex`'s closure), and the mentions of `muAdjNotVRLM` in CHECKPOINT, README and DESIGN §15.9 | E1, E2 | corrected in the docs step. `k`, `q2` and `adjIndex` sit at types with a lifetime `∀`, so they no longer carry over to `vRLM` through `RelMAgreesJ`. `gd` sits at `gdTy`, which has none |

**The stop rule for the edits.**
- A statement change listed in the table (the restatements, the withdrawal, (E4)) is part of the
  edit. It is not a stop.
- A result listed as "rebuild" or "re-proved" whose statement turns out to need changing, or any
  proved result not in the table that breaks: stop. Revert (E1)–(E4), proceed as §3.6's failure
  branch, and record which result broke and why.

### 3.2 The binder-named index

**The step.** At an index whose innermost entry `e` is named by the binder (`StackJ`'s third kind),
the first conjunct reads the premise at `δ.extend x α`. The premise's index needs
`SubOutside σ αs (δ.extend x α)`. At `e`, `boundBefore x (δ.extend x α)` is all of `δ`'s bindings,
so it needs all of them read above `e`'s lifetime. Nothing gave that, and
`not_subOutsideExtendAny`'s witness reads a binding below it. `StackJM` gives exactly that
(`SubFresh δ (head)`). The witness breaks the restriction: its binding is below the head.

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
shadows: at a context reaching no `U`. -/
def CtxExtendNamedMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    σ.head? = some e → InScope (extS δ σ αs) α → CtxFresh e.x Γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend e.x α) αs ls Γ γ ρ

/-- **The same at every context, at an instance in scope**: the entry's variable is read in no
entry's payload type (`StackJM`'s third kind gives it). `VRLMReadEquiv` with `X = {e.x}` (§3.3). -/
def CtxExtendNamedMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK σ αs → σ.head? = some e → δ.find? e.x = none → (∀ e' ∈ σ, ¬ VFree e.x e'.T) →
    InScope (extS δ σ αs) α → CtxFresh e.x Γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend e.x α) αs ls Γ γ ρ
```

**The route.**
- `allIRowMNKAt0_of`'s first-conjunct case runs as before, with these replacements:
  - `subOutsideExtend` by `SubOutsideExtendNamed`;
  - `stackJ_allExtend` by its named form (the entry is `Δ.extend x b`'s, so of the first kind);
  - `models_allExtend` by its named form (`x` is read at the head, below `b` by the third kind's
    `LtLife`).
- The own-lend conjunct is vacuous: `OwnOKI.var` asks `x ∉ σ.map LEnt.x`.
- At a context reaching no `U`, `CtxExtendNamedMAt` is `gRLM_reading_uFree`: the stack reads `e.x`
  either way. At a live `U` slot it is `CtxExtendNamedMSAt` (§3.3).

**Target (3a).** `allIRowMUFree0 : ∀ Γ, (∀ s ∈ Γ, s.live = true → UFreeM s.ty) → AllIRowMAt
.binder0 Γ`. It removes the "stack does not name the binder" restriction of `allIRowMNKUFree0`.

**Why this restriction.** The restriction is right at `binder0`, because no `binder0` clause
produces the third kind, so strengthening it removes no index a `binder0` row reads. The
alternative is to drop the third kind from `binder0`'s judgement only, which splits `SemSM` by
placement. `StackJM` is preferred because it needs no split, and its cost at `cbpv` is recorded:
`cbpv`'s producer at `vRLM` is `RelendU`'s own push, which carries neither of `StackJM`'s conjuncts
(§3.1, (E3)). `RelendUI` carries `SubFresh`, but it is not `vRLM`'s clause, so no producer of the
third kind at `vRLM` has it.

### 3.3 A live `U` slot: the reading transports

**Why `CtxExtendMAt` and `CtxShadowMAt` fail at a `U` slot.** The design found the reason, and it
is not stated in `R1MONO.md`:
- W's `∀` clause asks its own lend `SubFresh δ α`, which reads every binding of the base reading.
- Extending `δ` by `x ↦ α₀`, with `α₀` a new value below the head, restricts the own lends that a
  `U` value's argument must serve to those below `α₀`.
- In a contravariant position, the closure must then accept more arguments than it was related for.
- With (E1), `α₀` is already a value in scope. The two readings then have the same value set, up to
  the stack's lifetimes, and a lend fresh below one is fresh below the other.
- With (E2), the admissible own lends do not depend on bindings the type ignores.

There is a second reason. GhostEnd's views (`vwE`, through `vwS`, `bodyS` and `OpenS`) and the
operation table (`rowTab`) read the **base** reading `δ`, not `extS δ σ αs`. `cRLM`'s `F_Σ` clause uses both. So two readings must agree at the base wherever a
payload type or an operation type is read. That includes the payload types of entries that later
own pushes add, which the old `payLocal` (`… ∨ y ∈ s.1.map LEnt.x`) let read any stack variable,
the shadowed one among them. The fix has two parts:
- `payLocal` is tightened to `CFree y C` (§3.1);
- every transport takes `X = {x}`, so that the induction's avoidance hypotheses keep the base
  readings' one disagreement out of every read.

The transport is then symmetric:

```lean
/-- **Two readings the relation cannot tell apart at a stack.** The base readings agree off `X`, and
so do the stack's (`extS` reads the stack's variables alike). The values in scope agree. A lend
below the innermost is fresh below one exactly when it is fresh below the other (at the empty
stack, every lend). -/
def ReadEquiv (X : LifeVar → Prop) (σ : LStack) (αs : List Life) (δ₁ δ₂ : LSub) : Prop :=
  (∀ y, ¬ X y → δ₁.find? y = δ₂.find? y) ∧
  (∀ α, InScope (extS δ₁ σ αs) α ↔ InScope (extS δ₂ σ αs) α) ∧
  ∀ a, (∀ h ∈ αs.head?, a < h) → (SubFresh δ₁ a ↔ SubFresh δ₂ a)

/-- **`vRLM` reads only what `ReadEquiv` fixes**, at every type and in both directions. `X` avoids
the type's free variables and binders, the environment's types, and the entries' payload types. -/
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
pushed entry's payload type not reading its own variable (`OwnPushM`'s `selfFree`). With the old
entries' avoidance (`StackPayAvoids`), no payload type reads the shadowed variable, which the base
readings disagree at. `R1AllI.lean`'s `CtxShadowMAt` lacks the first two. -/
def CtxShadowMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK (e :: σ) (α :: αs) → δ.find? e.x = none → ¬ VFree e.x e.T →
    StackPayAvoids e.x σ →
    (∀ s ∈ Γ, s.live = true → ¬ VFree e.x s.ty ∧ e.x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p (e :: σ) δ (α :: αs) ls Γ γ ρ →
      gRLM (ℍ := ℍ) p (e :: σ) (δ.extend e.x α) (α :: αs) ls Γ γ ρ
```

**The route.** `VRLMReadEquiv` is proved by induction on the type, mutually with `cRLM` and
`effRetM` (using `relendMValueE`'s environment generalisation where `μ` needs it). Each of the
following keeps `ReadEquiv` and the avoidance hypotheses:
- **The first conjunct.** The same instances are read on both sides: the values in scope agree, and
  the bound's variables avoid `X`. Both readings are extended by `x' ↦ α'` alike. `α'` is in scope,
  so the value sets still agree and `SubFresh` below the head is unchanged.
- **The own push.** The same pushes are admitted on both sides. `OwnPushM` reads the readings only
  at the type's free variables, which are off `X`, and through `SubFresh` below the head. Both
  readings are extended at the new head. The new entry's payload type avoids `X` by `payLocal`: it
  reads only variables free in a part of a type that avoids `X`.
- **An instantiation.** `θ` maps both readings' values alike. The value sets agree up to the stack's
  lifetimes, and `θ` keeps those at or above the new head.
- **`⊸`.** By the symmetry of the statement.
- **The `F_Σ` clause's base-reading reads.** Payload types (`vwE`) and operation types (`rowTab`)
  avoid `X`.

Each transport is then an instance with `X = {x}`:
- `CtxExtendMSAt`: `x` is new to the stack. The base readings differ only at `x`; `α` is in scope,
  so the value sets agree; and `α` is a stack lifetime at or above the head, or one of `δ`'s values,
  so `SubFresh` below the head agrees.
- `CtxExtendNamedMSAt`: `x = e.x`, the head's variable. The same three facts hold, and the entries'
  payload types avoid `e.x` (`StackJM`).
- `CtxShadowMSAt`: `x = e.x` after the push, and `α` is the head's lifetime. The pushed entry's
  payload type avoids `e.x` by `selfFree`, the old entries' do by `StackPayAvoids`, and the slots'
  types do by `CtxFresh`. The new binding's value is the head's lifetime, so `SubFresh` agrees
  below it.

`allIRowMNKAt0_of` is re-proved with `CtxExtendMSAt` and `CtxShadowMSAt` in place of `CtxExtendMAt`
and `CtxShadowMAt`. The row has both new hypotheses at the pushed index: `StackOK` from `OwnOKI`,
and `selfFree` from `OwnPushM`.

**Targets:** `ctxExtendMSAt_all : ∀ Γ, CtxExtendMSAt .binder0 Γ`,
`ctxExtendNamedMSAt_all : ∀ Γ, CtxExtendNamedMSAt .binder0 Γ`, and
`ctxShadowMSAt_all : ∀ Γ, CtxShadowMSAt .binder0 Γ`.

### 3.4 A live `U` slot: the push

**Why `MonoOwnGMAt` does not follow in general.** At the pushed stack, a `U` value's clause must
serve two kinds of argument that the old clause never covered:
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

**(3b-i) Where the clause's shape carries the push.** No such argument or instance can reach the
slot's computation here:

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

**The route (3b-i).** This extends `monoOwnUFree_go` (`R1Mono.lean`) with the `U` case:
- **The split.** The pushed views are the old ones plus `e`'s, with its flag off (`placeFree`). The
  part above the outermost lend is unchanged. At `σ = []` it is above `a` by `OwnOK.below`.
- **The instantiations.** An instantiation of `a :: αs` restricts to one of `αs` (the same cut at
  `σ ≠ []`). At `σ = []` it fixes `δ`'s values, which are all above `a` (`SubFresh`).
- **The body.** It is carried by a computation-level push for `PushStableC`:
  - `.ret` is the value-level push. The answer's guard facts come from the run (`wpTS_tabAt`, and
    `pvlRuns_arises`'s lemma at distinct places). The pushed place is held by the frame, so the
    answer holds no cell there.
  - `⊸` un-pushes the argument. A `UFreeM ∧ RefFree` argument at the pushed stack holds no borrow
    cell at `e.l`: no variable it reads is read at or below `a`, because the stack's are above the
    head and `δ`'s are by `SubFresh`. It holds no owned cell at all. So it meets the old guard (drop
    `e`), the old clause applies, and the result is pushed back.
  - `&` is componentwise.

**(3b-ii) The slots outside `PushStable`, which the programs need.** `reconB′`'s callback captures
`retryR`. DESIGN §9.2 fixes that shape, and this plan does not change the term. At `vRLM` over value
types, `retryR`'s instances are `!U(!U(1 → F_{exn ⊙ s} bool) → F_s bool)`, one per admissible row
`s ∌ exn`. Statement 4's intersection over them is §4.2's `AllRMonoM0`. Each instance has a `!U`
argument and an effect layer, so each is outside `PushStable`. These slots are the target.

The computation-level push has one case at each former outside `PushStable`. Each case is stated as
an elaborating `def … : Prop`, the exact step the push takes there:

```lean
/-- **The `⊸` case of the push, at an argument holding the pushed view.** A computation related at
`A ⊸ D` at the stack, applied at the pushed stack to an argument related there that holds a borrow
cell at the pushed place at the pushed lifetime, is related at `D` at the pushed stack.
`PushedViewOutsideOldGuard` is why the old clause says nothing about that argument. As stated, this
is refuted at `gd`: `gdF` hands back the thunk over `gdY`'s view, boxed at `'1 ↦ 3` (`gdG_pushed`,
`gd_run_fails_of`), at a configuration not shown to arise. The case does not arise at a `!`
argument, whose resource is empty. -/
def PushArrStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (e : Expr)
    (ρf : WRes) (en : LEnt) (a : Life) (w : Val) (ρv ρ : WRes) (ψ : CellU BoCa.Loc Val),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none →
    ¬ CFree en.x (.arr A D) → en.x ∉ CTy.binders (.arr A D) → StackPayAvoids en.x σ →
    (∀ ψ', ¬ DeepAt ρf en.l ψ') → ρf.InStratum a → TabAtS σ αs ρf →
    PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    cRLM (ℍ := ℍ) .binder0 σ δ (.arr A D) αs ls e ρf →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ A (a :: αs) ls w ρv →
    ρv.get en.l = some ψ → ψ.kind ≠ Kind.own → ψ.at = a →
    ResU.CompS ρf ρv ρ → TabAtS (en :: σ) (a :: αs) ρ →
    PlaceViewsL (extS δ (en :: σ) (a :: αs)) (en :: σ) (a :: αs) ls ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ D (a :: αs) ls (.app e (.val w)) ρ

/-- **`PushArrStep` under the Core-value restriction**: the computation is also Core's at the
stack's reading (`gRLMC`'s slot form). Core's `⊸` has no guard, so it reads an argument holding the
pushed view. The route: `WInsideCoreM` at `A` at the pushed stack, then Core's clause, then
`CoreInsideWM` at `D`'s answer. `gd` is outside the restriction (`GdCtxNotCore`). -/
def PushArrStepC : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (e : Expr)
    (ρf : WRes) (en : LEnt) (a : Life) (w : Val) (ρv ρ : WRes),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none →
    ¬ CFree en.x (.arr A D) → en.x ∉ CTy.binders (.arr A D) → StackPayAvoids en.x σ →
    (∀ ψ', ¬ DeepAt ρf en.l ψ') → ρf.InStratum a → TabAtS σ αs ρf →
    PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    cRLM (ℍ := ℍ) .binder0 σ δ (.arr A D) αs ls e ρf → cC (.arr A D) ls (extS δ σ αs) e ρf →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ A (a :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (en :: σ) (a :: αs) ρ →
    PlaceViewsL (extS δ (en :: σ) (a :: αs)) (en :: σ) (a :: αs) ls ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ D (a :: αs) ls (.app e (.val w)) ρ

/-- **The `⊸` case at an argument reaching a `U` that holds nothing** (the pop): a `U` value over
the empty resource, related at the pushed stack, is related at the stack, so the old clause applies
to it. This is the step `retryR`'s `!U` argument needs. -/
def PopUStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (w : Val) (en : LEnt)
    (a : Life),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none → ¬ CFree en.x C →
    en.x ∉ CTy.binders C → StackPayAvoids en.x σ →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ (.thunk C) (a :: αs) ls w PMap.empty →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls w PMap.empty

/-- **The `F_Σ` case of the push, at a stop.** A stop at the stack is a stop at the pushed stack,
the computation holding nothing at the pushed place and lying above the pushed lend, the answer
carried by the value-level push (`Q` to `Q'`). An operation the pushed entry does not cross stops
at depth `0` at the pushed stack (`depth`'s `takeWhile`), wherever it stopped at the stack. At depth
`d ≥ 1` its continuation is owed only at strict re-lends of the ghost-ended entries (`openFS`); at
depth `0` it is owed at every `ReLend` of the whole stack (`RelendableN`). -/
def PushEffStep : Prop :=
  ∀ (δ : LSub) (σ : LStack) (Tab : OpTab) (Q Q' : List Life → List SRec → Val → WProp)
    (αs : List Life) (ls : List SRec) (t : Expr) (ρ : WRes) (en : LEnt) (a : Life),
    StackOK (en :: σ) (a :: αs) → (∀ ψ, ¬ DeepAt ρ en.l ψ) → ρ.InStratum a → TabAtS σ αs ρ →
    (∀ (a' : Life) (αs' : List Life) (ls' : List SRec) (v : Val) (ρ' : WRes),
      Q αs' ls' v ρ' → Q' (a' :: αs') ls' v ρ') →
    stopS δ σ Tab (OpenS δ σ Tab Q) αs ls t ρ →
    stopS δ (en :: σ) Tab (OpenS δ (en :: σ) Tab Q') (a :: αs) ls t ρ

/-- **The `∀` case of the push**: a computation related at `∀'z ⊏ c. C` at the stack is related
there at the pushed stack. At the pushed stack, its first conjunct reads the instances in scope
there, the pushed lifetime among them, which is not in scope at the stack ((E1), `SubFresh`). Its
own-lend conjunct reads pushes onto `en :: σ`, below the pushed lend. The stack's clause reads
neither. -/
def PushAllStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (z : LifeVar) (c : Lifetime.Life) (C : CTy) (αs : List Life)
    (ls : List SRec) (e : Expr) (ρ : WRes) (en : LEnt) (a : Life),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none → ¬ CFree en.x (.all z c C) →
    en.x ∉ CTy.binders (.all z c C) → StackPayAvoids en.x σ → (∀ ψ, ¬ DeepAt ρ en.l ψ) →
    ρ.InStratum a →
    cRLM (ℍ := ℍ) .binder0 σ δ (.all z c C) αs ls e ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ (.all z c C) (a :: αs) ls e ρ

/-- **`MonoOwnGMC` at one context**, with the pushed variable read in no entry's payload type: the
Core-value restriction (`gRLMC`) at the slots 3b-ii targets. -/
def MonoOwnGMCAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    SubOutside σ αs δ → OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLMC (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLMC (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ
```

**The routes, attempted in this order, with one bounded attempt each:**
1. **Unrestricted.** `PopUStep`, `PushEffStep` and `PushAllStep` from the relation alone. Then
   `MonoOwnGMAt .binder0 Γ`, at a context whose live `U` slots have `retryR`'s instance shape
   (`!U(!U(1 → F_{Σ₁} R₁) → F_{Σ₂} R₂)`, with data answers), from `PopUStep` at the argument and
   `PushEffStep` at the answers.
2. **The Core-value restriction** (`MonoOwnGMCAt`, R1's `gRLMC` at one context).
   - `gd` is outside it (`GdCtxNotCore`), and it is met with a `U` slot at `gd`'s index
     (`GdRestrictedMet`).
   - At `⊸`, Core's clause reads every argument (`PushArrStepC`).
   - At an instantiation other than the identity, it needs Core's relation carried along the
     instantiation. That statement at every type, `InstEquivLeafAll`, is refuted as stated, at a
     configuration not shown to arise, and its `U` instance is not derived (R1MONO §8.1).
   - Expected stops [unchecked]: `WInsideCoreM` at a `!U` argument, and Core inside W at an effect
     layer.
3. **The arising route**, recorded and not attempted. `MonoOwnGMA` would need the own push as a
   transition of the arising set, and there is none today. It would also need an argument that an
   arising closure meets the push, and that argument is the fundamental lemma at the closure's own
   derivation, which is not available inside the row's proof.

**Targets (3b).**
- `monoOwnGMAtPS : MonoOwnGMAtPS .binder0`.
- `allIRowMPS0 : ∀ Γ, (∀ s ∈ Γ, s.live = true → PushStableV s.ty) → AllIRowMAt .binder0 Γ`. This is
  the row at every push-stable context, at every index:
  - at an index whose stack does not name the binder, from `allIRowMNKAt0_of`'s re-proof with
    `CtxExtendMSAt`, `MonoOwnGMAtPS` and `CtxShadowMSAt`;
  - at a named index, from §3.2's route with `CtxExtendNamedMSAt`.
- `not_pushArrStep : ¬ PushArrStep`, from `gd`'s lemmas: a refutation of our statement at a
  configuration not shown to arise.
- For each of `PopUStep`, `PushEffStep`, `PushAllStep` and `PushArrStepC`, one of:
  - it is proved;
  - it is refuted at a configuration that passes DESIGN §11;
  - it is stated in `Nx.lean` with its attempt's frontier, and reported as "I have not derived X
    and have not verified that any obstruction is real".
- `MonoOwnGMAt .binder0`, or `MonoOwnGMCAt .binder0`, at `retryR`'s instance shape, if the steps it
  reads close.

### 3.5 What stays open, and the program check

- **Open.** Unless 3b-ii's steps close, `MonoOwnGMAt` stays open at a `U` slot whose computation has
  any of the following, and with it `AllIRowM .binder0 = ∀ Γ, AllIRowMAt .binder0 Γ` at those
  contexts:
  - a lifetime `∀` (`PushAllStep`): a captured callback can be handed the pushed view at the
    instance `x ↦ a`;
  - an effect layer (`PushEffStep`): a stop of a name the pushed entry does not cross moves to depth
    `0`, which the old clause never owed;
  - `ν`;
  - an argument reaching `U` (`PopUStep`), or holding the pushed view (`PushArrStep`, refuted as
    stated at `gd`; `PushArrStepC`).

  Each open step is reported by its `def … : Prop`, not as a prose obstruction.
- **The arising check.** A refutation would need a closure produced by a typed program (in
  `ArisesVI`) that is related at `σ` and not at the push. DESIGN §4.3 expects none: a derivable
  closure meets the push by its own derivation. `gd` refutes `PushArrStep` at a configuration not
  shown to arise, and that refutes no row.
- **What it says about OQ-8.** It says nothing that decides, and it is evidence. The one future
  `binder0`'s `∀I` row needs is the own push, and `binder0`'s `U` clause does not quantify over it.
  A placement whose `U` clause takes the own push (`uOwn` without `uFut`) would give the push by
  construction. That is a candidate for OQ-8, not adopted here: it is a placement decision. The own
  lend's entry carrying a row that the clause fixes (for example the callback type's row) would
  remove `PushEffStep`'s depth change. That is recorded as a question, not adopted: it would be a
  fifth edit.
- **The program check** (by reading the terms, recorded in the outcome):
  - `genSelf`'s callback `cb genBody` (`Targets/I/Programs.lean:77`, `:199`) captures nothing. Its
    `∀I` context is empty, and §3.2 covers it.
  - `reconB′` is not built. DESIGN §9.2's shape is kept: its callback captures `retryR`, which is
    3b-ii's slot. So `reconB′`'s `∀I` row at `binder0` is `AllIRowMAt` at a context holding
    `retryR`'s instances, and its status is 3b-ii's outcome. Statement 4's `AllRMonoM0` at `retryR`
    is §4.2's own entry. The plan does not reshape the term to move `retryR` out of the context.
  - DESIGN §9.2's own typing question (retry's body capturing the `Imm` view) is a separate choice
    that the builder of `reconB′` makes and records. It is not used to avoid the `∀I` row.

### 3.6 Success and failure

- **Success.** All of the following, with the statements of §3.1–§3.4:
  - (E1)–(E4) land, and every result in §3.1's table is at its disposition;
  - `MuAdjVRLME1` is decided;
  - item 2's rows are re-proved at `StackJM`, item 1a is re-checked, and 1a′ is decided;
  - `allIRowMUFree0`, `ctxExtendMSAt_all`, `ctxExtendNamedMSAt_all`, `ctxShadowMSAt_all`,
    `monoOwnGMAtPS` and `allIRowMPS0` are proved;
  - 3b-ii: `not_pushArrStep`, and each other step proved, refuted at an arising configuration, or
    stated with its frontier;
  - the open class and the program check are recorded.
- **Failure.**
  - The edits: §3.1's stop rule. A listed statement change is not a failure. An unlisted break, or a
    "rebuild" or "re-proved" result whose statement must change, reverts (E1)–(E4). Then prove §3.2
    at `vRLM` with `StackJM` alone, state §3.3's transports with `InScope` as a hypothesis, and
    state the row as open at a `U` slot.
  - If `VRLMReadEquiv` fails at a clause (the base-reading conjunct at the own push, at an
    instantiation, or at `F_Σ`'s reads), record the clause. The three transports are then claimed
    only at the contexts where it holds.
- **What may be claimed.** "The `∀I` row holds at every push-stable context, at every index", and
  at the further contexts 3b-ii proves. It may not be claimed that statement 0 at `binder0` reduces
  to the `∀I` row; §4 decides what it reduces to.

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

/-- **`MonoHideM`'s `F_Σ` case at a stop**, the step the general case reads: a stop at `σ` is a stop
at `hideS N σ`, with the piece's continuation carried along. Hiding a name that the stack's
innermost entries cross moves its stops from depth `d ≥ 1` to `0`. At `σ` the continuation is owed
at strict re-lends of the ghost-ended entries (`openFS`); at `hideS N σ` it is owed re-lendable at
every `ReLend` of the whole stack (`RelendableN`). The mechanism is `PushEffStep`'s. -/
def HideStopStep : Prop :=
  ∀ (δ : LSub) (σ : LStack) (N : UInt32 → Bool) (Tab : OpTab)
    (Q : List Life → List SRec → Val → WProp) (αs : List Life) (ls : List SRec) (t : Expr)
    (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ →
    stopS δ σ Tab (OpenS δ σ Tab Q) αs ls t ρ →
    stopS δ (hideS N σ) Tab (OpenS δ (hideS N σ) Tab Q) αs ls t ρ
```

**The route.**
- `HideInvisible` is list extensionality: `cross n && !N n = cross n` when `N n` implies
  `¬ cross n`.
- `VRLMHideAvoid` is induction on the type, mutual with `cRLM`, at two stacks equal up to `cross`
  at `N`'s names. Pushes keep that relation (the same entry is pushed on both). `cross` is read only
  by GhostEnd's `depth`, inside `tabK`. At a name `m` with `N m = false` the depth agrees. At a name
  `n ∈ N` the type's tables have no entry, because the type does not carry `n`.
- `MonoHideGMHandle0` is the two cases, slot by slot.

**The general case.** `MonoHideGM .binder0` where the hidden name crosses an entry and a live type
carries it. It gets one bounded attempt: `VRLMHideAvoid`'s induction, with its `F_Σ` case at a
crossing name, whose step is `HideStopStep`. `HideStopStep` and `PushEffStep` are attempted
together, since they are the same depth change. If the attempt does not close, record the frontier
and use the wording "I have not derived `MonoHideGM .binder0` in general and have not verified that
any obstruction is real". A derivable value meets the general case by its own derivation, so no
arising witness is expected. Both programs' handlers hide names their lenders do not cross:
`reconB′`'s callback row is `{wait}`, and `retry` hides `exn`. So `HideInvisible` covers them.

### 4.2 The consumers check

**Step 1: the inventory.** List every hypothesis use of `MonoV`, `MonoG`, `MonoOwnG`, `MonoC` and
`MonoHide`, and of their `M` forms, in `Statement0.lean`–`Statement34.lean`, `R1*.lean` and DESIGN.
The builder re-runs the search (`grep -n "MonoV\|MonoG\|MonoOwnG\|MonoC\|MonoHide"` over those
files) and confirms the table below is complete. The designer's reading [read] gives:

| use site | what it consumes | its replacement at `vRLM .binder0` | status |
|---|---|---|---|
| `Statement1.lean`'s `AllIRow` (docstring); DESIGN §2.2 (l. 235–237), §2.5 (l. 494), §5.3 (l. 1064) | `MonoOwnG` at the `∀` clause's own push | `AllIRowM`, through its three transports (item 3) | remains at the contexts §3.5 lists |
| DESIGN §2.2 (l. 236): `ThunkVRow`, `BangThunkVRow` | `MonoOwnG` at the `U` clause's own push | none: `binder0`'s `U` clause makes no own push, and the rows are proved (`statement0UFullM`) | no consumer at `binder0` |
| `Statement0.lean`'s `MonoHideFromMonoV`; `Statement34.lean`'s `HandleRow` (docstring); DESIGN §7 (l. 1333) | `MonoHide`, from `MonoV` | `MonoHideGM .binder0` (§4.1); `MonoVM .binder0` is refuted | the invisible cases are to prove; the general case remains |
| `Statement34.lean`'s `AllRMono`; DESIGN §8 (l. 1376) | `MonoV` at each instance; at `binder0`, `MonoC` | `AllRMonoM0` (below): a record-order half and an own-push half | the record-order half is to prove; the own-push half remains (3b-ii at the instance types) |
| `R1MONO.md` §4.1; `Statement0MAtConsumers0` | `MonoExtM`, for `[let]` and the end of a lend | `MonoExtM .binder0` | proved (`monoExtM0`); the rows that read it are [unchecked: no row proof at vRLM] |
| DESIGN §2.4 (l. 419–421), §2.5 (l. 483), §4.3 (l. 840–860) | `MonoV`, `MonoG`, `MonoC` at futures | none: `binder0` reads no future (`FutQI false`) | `cbpv` and `binder` only; outside this check |
| DESIGN §4.3 (l. 819–822) | `MonoC`, for `MonoV` at a `U` value | internal to `MonoV` | not a consumer |
| `Statement0.lean`'s `Statement0`; `R1.lean`'s `Statement0M`, `MonoGMOfMonoVM`, `MonoOwnGMOfMonoGM`, `AllIRowMOfMonoOwnGM`, `AllIRowMCOfMonoOwnGMC`, `MonoOwnGMA`, `MonoOwnGMC` | bundles and implications between monotonicity statements | — | not consumers |

**Step 2: statement 4's own entry.** `AllRMono` (`Statement34.lean:77`) is stated over `ovalW`, at
the old relation `vRL`, along `Fut`, with `Ext`. `AllIRowM` and `MonoOwnGMAt` range over value-type
contexts at `vRLM`, which has no `∀ρ` former. So item 3 cannot express this consumer, and
`monoExtM0` covers its record-order half only instance by instance. It is restated at `vRLM`, at the
two index changes `binder0`'s rows make. `ovalUM` and `ovalWM` are statement 4's construction read
at the one draft relation; they add no relation beside it.

```lean
/-- Statement 4's `ovalU` at `vRLM`. -/
def ovalUM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OCTy → RowEnv → Val → WProp
  | .allR ρ k C, η, v => fun r => ∀ s : Row, k.cls.Admits s → (∀ o ∈ s, k.adm o) →
      ovalUM p σ δ αs ls C (Function.update η ρ s) v r
  | C, η, v => vRLM (ℍ := ℍ) p none σ δ (.thunk (Targets.Inst.OCTy.den η C)) αs ls v

/-- Statement 4's `ovalW` at `vRLM`. -/
def ovalWM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OVTy → RowEnv → Val → WProp
  | .thunk C, η, v => ovalUM p σ δ αs ls C η v
  | .bang A, η, v => fun r => r = PMap.empty ∧ ovalWM p σ δ αs ls A η v r
  | A, η, v => vRLM (ℍ := ℍ) p none σ δ (Targets.Inst.OVTy.den η A) αs ls v

/-- **Statement 4's `AllRMono` at `vRLM .binder0`**: a row-polymorphic value carried along the two
index changes `binder0`'s rows make. One is the record order (`Ext`, keeping the tags). The other is
the callback's own push (`OwnPushM`, with the `∀` clause's freshness). These are what `reconB′`'s
`retryR` crosses: it is made at `σ = []` and used inside the borrow's callback. -/
def AllRMonoM0 : Prop :=
  (∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls ls' : List SRec) (ρv : RVar) (k : RowCon)
      (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes),
      StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → RecsOutside αs ls' →
      Ext ls ls' r → KeepsT ls ls' r → TabAtS σ αs r → PlaceViewsL (extS δ σ αs) σ αs ls r →
      ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
      ovalWM (ℍ := ℍ) .binder0 σ δ αs ls' (.thunk (.allR ρv k C)) η v r) ∧
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : RVar) (k : RowCon)
    (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes) (C' : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    SubOutside σ αs δ → OwnPushM δ C' r (σ, αs) e a → δ.find? e.x = none →
    (∀ η', ¬ VFree e.x (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C))) ∧
      e.x ∉ VTy.binders (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C)))) →
    RecsOutside (a :: αs) ls → SubFresh δ a → TabAtS σ αs r →
    PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 (e :: σ) δ (a :: αs) ls (.thunk (.allR ρv k C)) η v r
```

- **The record-order half.** `monoExtM0` at each instance's type, through the intersection. To
  prove.
- **The own-push half.** `MonoOwnGMAt` at the one-slot context of each instance's type, through
  the intersection. At `retryR` the instances are outside `PushStable`, so this half stays open
  unless 3b-ii closes at them.

**Step 3: the rule-by-rule table.** Go over the probe's rule set:
- `RulesClosed`'s rules (`Targets/Base/Typing.lean:831`);
- `Tier1SubNU`'s premise-free constants;
- the spanning rules `SpanRule1`, `SpanRule2` and `SpanRuleLoad`;
- statement 4's `RC_allRI` and `RC_allRE`.

For each rule, record the index change its compatibility row would make at `binder0` between its
conclusion and its premises, and the transport that change needs. Most rows have no proof at
`vRLM`. For those, the entry is a prediction from the rule's shape: it is marked
[unchecked: no row proof at vRLM], not "none". A value-judged premise may be a computation
(`SemV` is `SemC` at `F A`). So a rule that evaluates one premise and then uses a later premise's
context carries that context along the first run, which is `MonoExtM`'s shape. The expected table,
to be checked, not assumed:

| index change | rules | transport | status |
|---|---|---|---|
| none: same index, split resource, no run between premises | `app`, `force`, `ret`, `ofRet`, `withI`, `proj`, `sumI`, `zeroE`, `boxI`, `boxE`, `immSub`, `mutSub`, `lam` (`binder0`'s `⊸` reads the stack itself), `nuIn`, `nuOut`, `effPerform`, `effRaise`, the premise-free constants other than the borrow constants | none | [unchecked: no row proof at vRLM] |
| list extended along a run (`Ext`) | `bind`, `tensorI`, `unitE`, `tensorE`, `sumE`, `bangE`, `lolliE`, `effLet` and `effThen` (between stops), a lend's end (6.64's `ext_add`) | `MonoExtM` | transport proved (`monoExtM0`); rows [unchecked: no row proof at vRLM] |
| re-lend at a resume or an instantiation | the `U` rows, `effLet` and `effThen` across a stop, the spanning rules | the thaw (`CtxRelendsAllM`) | `U` rows proved (`statement0UFullM`); the others [unchecked: no row proof at vRLM] |
| own push, reading extension, shadow | `allI` | `MonoOwnGMAt`, `CtxExtendMSAt`, `CtxExtendNamedMSAt`, `CtxShadowMSAt` | item 3 |
| own push and record order of a row-polymorphic value | statement 4's `RC_allRE` at a value made outside the borrow (`AllRMono`) | `AllRMonoM0` | Step 2: the record-order half is to prove, the own-push half remains |
| hiding | `effHandle` | `MonoHideGM` | §4.1 |
| callback at its own push | the borrow constants (`withbor` (1)–(3), `withload`, `foldImm`, the slices), their unwinding forms (`withbor1U/2U/3U`, `withloadU`, `sliceBorrowMU/IU`), the spanning rules | `CallbackExt*M`, with item 1 at a block | proved at one entry, with (E4)'s hypothesis; the rows [unchecked: no row proof at vRLM] |

These are owed rows that are not monotonicity consumers. They are flagged, not decided:
- `roll` and `unroll`: item 2.
- `allE` and `allEV`: the lifetime substitution, `cRLM` at `C.instLife x b` read at
  `δ.extend x ⟦b⟧`. It is not stated at `vRLM`. `RetainedPayInstRow` is its `RetainedPay` part, at
  a `b` with no join.
- `effSub`: row subsumption at the `F_Σ` clause.

**Step 4: the corrected conjunction**, which replaces `Statement0MAtConsumers0` in every claim:

```lean
/-- **Statement 0 at `binder0`, read at the consumers the inventory finds.** Its conjuncts:
- the facts beside monotonicity;
- the record order;
- the `∀I` row (its context across the own push, to the binder's reading, and to the shadow);
- `[handle]`'s context into the hidden stack;
- statement 4's `AllRMono` at `vRLM .binder0`, which DESIGN derives from `MonoV` and `MonoC`. -/
def Statement0MAtConsumers0Full : Prop :=
  Statement0MBesideMono0 (ℍ := ℍ) ∧ MonoExtM (ℍ := ℍ) .binder0 ∧ AllIRowM (ℍ := ℍ) .binder0 ∧
    MonoHideGM (ℍ := ℍ) .binder0 ∧ AllRMonoM0 (ℍ := ℍ)
```

**Success and failure.**
- **Success.**
  - `hideInvisible`, `vRLMHideAvoid` and `monoHideGMHandle0` are proved. `HideStopStep` is proved,
    refuted at an arising configuration, or stated with its frontier.
  - `AllRMonoM0`'s record-order half is proved.
  - The inventory is confirmed complete, and every use site is mapped.
  - The table is complete. Each row with a proof at `vRLM` cites it; every other row carries
    [unchecked: no row proof at vRLM].
  - `Statement0MAtConsumers0Full` is stated, and `statement0MAtConsumers0_iff`'s docstring says that
    it holds by the definition of our own conjunction.
- **What may be claimed.** "Statement 0 at `binder0`, read at the consumers the inventory finds, is
  `Statement0MAtConsumers0Full`. Its open parts are:
  - `AllIRowM` at the contexts §3.5 lists;
  - `MonoHideGM` where the hidden name crosses an entry and a live type carries it;
  - `AllRMonoM0`'s own-push half.

  The table's rows marked [unchecked: no row proof at vRLM] are predictions of the transport each
  row reads, not checked consumers. Until each of those rows is proved at `vRLM`, the table may miss
  a consumer." The claim "reduces to the `∀I` row" is withdrawn.

---

## 5. Order of work and the stop rule

1. **Item 1a** (`Nx.lean`, `NxGuard.lean`), against `vRLM` as at `5210cf1`. It decides whether item
   1b exists.
2. **Item 2** (`NxUnroll.lean`), against `SemSM` before (E3). Independent and mechanical.
3. **Item 3** (`NxAllI.lean`), in this order:
   - **3.0** (E1)–(E4) in `R1.lean`, with every result in §3.1's table brought to its disposition;
     `MuAdjVRLME1`; item 2's rows re-proved at `StackJM`; item 1a re-checked; then item 1a′
     (`WithloadPairGapNilE1`, `SliceGapNilE1`, in `Nx.lean` and `NxGuard.lean`);
   - §3.2;
   - §3.3;
   - §3.4: 3b-i, then 3b-ii;
   - §3.5's record.
4. **Item 4** (`NxHide.lean`, the inventory, `AllRMonoM0`, the table).
5. **Item 1b** (`NxBlock.lean`, `NxBlockRows.lean`), only if 1a is real. It runs last because it
   changes the stack's representation, which every later proof reads. Run last, it is one revision
   that carries item 3's edits too, and (2)–(4) are already done whatever it does.
6. **Docs**:
   - this file's §9 (the outcome) and report lists;
   - README's file table;
   - DESIGN §15.10;
   - CHECKPOINT;
   - correcting the R1 unit's two major findings in README, DESIGN §15.9 and `R1MONO.md` §8: the
     "exactly its `∀I` row" claim, with §4's inventory and table, and the `withload` gap's
     condition, with item 1a's and 1a′'s results;
   - correcting `R1MONO.md`'s carry-over sentences (§0, §1.2, §1.3, §6's table), and every mention
     of `muAdjNotVRLM` as a fact about `vRLM` (CHECKPOINT, README, DESIGN §15.9, `R1MONO.md` §8.1),
     as §3.1's table says.

The orchestrator puts item 1 first. Only its arising check (1a) runs first. 1a′ runs once (E1) has
landed, because it is about the edited relation. The fix (1b) moves last for the reason in step 5.

**The stop rule.**
- **If item 1's route fails** (1a not real, or 1b's gate failing), items (2) and (3) are still done.
  The order guarantees it. 1a's failure skips 1b, and 1b's failure leaves `vRLM` as the one draft
  relation, with (E1)'s cost stated as the user's decision (§3.1).
- **Item 2** failing at a clause does not stop items 3 or 4.
- **Item 3.** §3.1's stop rule tells a planned statement change (not a stop) apart from a needed
  re-proof that turns into a statement change, or an unlisted break (a stop: revert (E1)–(E4) and
  proceed as §3.6's failure branch).
- **Item 1b.** §1.7.
- **Everywhere.**
  - A refutation is a fact about our statement unless it passes DESIGN §11: a configuration in
    `ArisesI`, values in `ArisesVI`, and a closed derivable program.
  - A step that does not close is reported by its `def … : Prop` and frontier, with the wording "I
    have not derived X and have not verified that any obstruction is real". It is never reported as
    a prose obstruction, and never as "not derived" without an attempt.
  - A step that would need a new relation family, a step index, a second guard beside `TW`, or an
    edit outside ProbeD1 stops that item, and is reported as a finding about the structure.
- Commit after each step, with the trailer lines. Never push and never touch `main`. Do not touch
  `~/repos/borrow-core-tier1`.

---

## 6. Files

| file | contents |
|---|---|
| `Nx.lean` | all of this unit's definitions and `def … : Prop` statements (items 1a, 2, 3, 4). Those of 1a and 2 come first; those that read `InScope`, `OwnPushM` or `StackJM` (1a′, item 3, `AllRMonoM0`, 1b's gate) are added at step 3.0 |
| `R1.lean` (edited) | (E1) `InScope` in the `∀` clause, (E2) `OwnPushM` in the own-lend conjunct, (E3) `StackJM` in `SemSM`; `InScope`, `OwnPushM`, `StackJM` defined above `vRLM`; (E4) `¬ VFree y T` on `CallbackExtMutM` and `CallbackExtImmM`; `VAllFree`, `CAllFree`; `RelMAgreesJ` restated |
| `R1Thaw.lean`, `R1Stmt0.lean`, `R1AllI.lean`, `R1Mono.lean` (re-proofs) | §3.1's table: the restated helper equalities and `relMAgreesJ`; `muAdjNotVRLM` withdrawn; `MuAdjVRLME1` decided; the re-proved results |
| `NxGuard.lean` | item 1a's proofs; 1a′'s proofs after step 3.0 |
| `NxUnroll.lean` | item 2's proofs |
| `NxAllI.lean` | item 3's proofs |
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
  - spec §9's slice borrows (`sliceBorrowITy`, `array_new`).
- **Printed hypotheses unspent**: list them per lemma.
- **Uniqueness and functionality results**: `ResU.CompS.functional`, `CellU.CompS.functional` and
  `RebAt`'s piece disjointness are expected. List which are used and which are not.
- **Printed lemmas in the run-up that are untranscribed**:
  - none expected for items 2–4;
  - for item 1b, the share's block re-lend (GhostEnd's `openFS` reads strict re-lends) is a
    forward obligation, not a printed lemma.
- **Hypotheses added and edits made**:
  - (E1)–(E4), each with its producers and consumers and §3.1's table;
  - (E4)'s `¬ VFree y T`, its source `hfree₁`, and its scope (every borrow constant's typing rule);
  - the statement changes `RelMAgreesJ` (restated) and `muAdjNotVRLM` (withdrawn), with
    `MuAdjVRLME1`'s result;
  - `StackJM`'s payload avoidance, beside its `SubFresh`;
  - `PushStableV` as 3b-i's domain, and the Core-value restriction (`MonoOwnGMCAt`) if 3b-ii uses
    it;
  - item 1b's definitions, if it runs.
- **The technique built**: no printed proof governs W's draft relation. `VRLMSubst` is `vCE_subst`'s
  route at W's clauses. `VRLMReadEquiv` is a symmetric invariance, not a one-way transport, because
  `⊸` reads its argument contravariantly.

---

## 8. The design review's findings, answered

| finding | the change |
|---|---|
| Item 1 does not tie the arising configuration to the row (major) | `WithloadPairGapReal` and `SliceGapReal` are each one existential over one configuration. Each carries `ArisesI`, the typed judgement's `SemIdxM` and `gRLM` at `γ = [loc e.l]`, `ψ = c.ρ.get e.l` with `ψ.wit = r.R`, `TW.reb` at the own push's `β`, and the composite failing at both stacks the `∀` clause reads. `PairCallbackGuardFails` is a lemma (§1.2, §1.3). |
| The nil case has no guard statement, and is claimed before (E1) (major) | The nil case is removed from 1a. `PairNilOldGuardHolds` states that before (E1) there is no gap at `[]`. 1a′ (`WithloadPairGapNilE1`) decides the case against the edited relation at step 3.0. A table says which relation each claim is about (§1.2, §1.3, §5). |
| (E1)/(E2) touch unlisted results; the stop rule would revert itself (major) | §3.1's table gives every touched result a disposition: `relMAgreesJ` and its helpers restated, `muAdjNotVRLM` withdrawn (with `MuAdjVRLME1`), the `gd` chain, the thaw (`InScope` never has to survive an instantiation there), the `U` rows. The stop rule separates listed statement changes from unplanned ones (§3.1, §3.6, §5). |
| The live-`U`-slot push is limited to `PushStable`, and `reconB′` is reshaped (major) | `PushStable` stays as 3b-i. 3b-ii targets `retryR`'s instances. The push's case at each former outside `PushStable` is an elaborating Prop (`PushArrStep`, refuted at `gd`; `PopUStep`; `PushEffStep`; `PushAllStep`), attempted unrestricted and under `MonoOwnGMCAt`. The arising route is recorded with what it lacks. The reshaping is dropped (§3.4, §3.5). |
| The consumers check is not a real check (major) | Step 1 is an inventory of every use site, with each mapped. Statement 4 gets its own entry (`AllRMonoM0` over `ovalWM`, with both halves). Every row without a `vRLM` proof is marked [unchecked: no row proof at vRLM], and the final claim carries that caveat. The sequencing rules are moved to the `MonoExtM` row (§4.2). |
| The failure is stated only for cells exactly at `β` (minor) | `PairCallbackGuardFailsLe` covers any two cells no longer-lived than the outermost lend. `PairArgCellsLe` is optional and [unchecked]. "Real" is claimed for the `reb_β` route unless it is proved (§1.2). |
| `MonoHide`'s general case is ruled out in advance (minor) | One bounded attempt, with its step stated as `HideStopStep` and the standard wording if it stays open (§4.1). |
| Item 2's `SemSM` version, and the roll rule's premises (minor) | Item 2 is proved before (E3) and re-proved after it. `RollRowM`'s premises are quoted from the rule; no premise is added (§2.1, §2.2). |
| `CallbackExt*M` cannot build `OwnPushM` (major) | (E4) adds `¬ VFree y T`, with its source `hfree₁` quoted. Its effect on `Statement0MBesideMono0` is stated, and `callbackExt*M_own` is re-proved (§3.1). |
| `relMAgreesJ`, `muAdjNotVRLM` and the carry-overs break (major) | In §3.1's table. `VAllFree` and `CAllFree` are defined; `RelMAgreesJ` is restated. `muAdjNotVRLM` is withdrawn, its expected falsity is argued, and `MuAdjVRLME1` decides it. The corrections to `R1MONO.md`'s carry-over sentences (§0, §1.2, §1.3, §6) are in the docs step (§5). |
| (E3)'s justification rests on `RelendUI`, which `vRLM` does not use (major) | (E3) is justified at `binder0` only. It is recorded that `cbpv`'s `U` own push at `vRLM` (`RelendU`'s `OwnPush`) meets neither of `StackJM`'s conjuncts (§3.1, §3.2). |
| `ReadEquiv`'s second conjunct is not kept in the shadow case (major) | `payLocal` is tightened to `CFree y C`. `ReadEquiv`'s base conjunct agrees off `X`. All three transports take `X = {x}`, so the avoidance hypotheses keep the shadowed variable out of GhostEnd's base-reading reads and `rowTab`'s. The failure branch is kept (§3.1, §3.3, §3.6). |
| (E1) removes the nil route for multi-leaf `withload` and slices (major) | Stated as (E1)'s disclosed cost before it lands. 1a′ decides it in Lean, and it becomes the user's decision if 1b's gate fails (§3.1, §1.7, §5). |
| `r ∈ c.ps` where `TW.reb` asks `r ∈ rsOf c.ls` (minor) | `r ∈ rsOf c.ls` is a conjunct, from `LendImm`'s own field (§1.3, §1.4). |
| `allIRowMPS0` "at every index" has no transport at a named index (minor) | `CtxExtendNamedMSAt` is a target, from `VRLMReadEquiv` with `X = {e.x}`. `StackJM`'s third kind carries the payload avoidance it reads (§3.1, §3.2, §3.3). |
| `RollRowM`/`UnrollRowM` are not in (E3)'s re-proof list (minor) | They are in §3.1's table and in step 3.0. |

---

## 9. Outcome

To be written by the build.
