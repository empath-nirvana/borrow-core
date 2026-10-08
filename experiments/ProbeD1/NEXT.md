# ProbeD1: the two-cell guard gap, the unroll row, the `∀I` row's open cases, `MonoHide` — the design

This is the design for the unit after the R1 unit (`R1MONO.md`, commit `5210cf1`). It plans four
items, in the order of §5, and states every target as a Lean `def … : Prop` with its route, the
lemmas it reuses, what counts as success or failure, and the arising check any counterexample must
pass. It contains no proofs. §8 answers the two design reviews' findings.

The build's outcome is §9. §10 records the user's corrections of 2026-10-08, which supersede this
design wherever it calls a gap on a borrow-only program a cost or a restriction, and §3.5's program
check. The four review findings still open are under *Unresolved*.

The statements go in a new statements file `Nx.lean` (definitions and `def … : Prop` only). It
imports `R1AllI.lean`, and `Statement34.lean` for statement 4's open types. Items 1a's and 2's
statements are written first. Every statement that reads `InScope`, `OwnPushM` or `StackJM` (1a′'s,
item 3's, the thunked callback rows `CallbackExt*MF`, item 4's `AllRMonoM0`, item 1b's gate) is
added at step 3.0, once (E1)–(E4) have landed in `R1.lean`. The proofs go in `NxGuard.lean` (item
1a, then 1a′), `NxUnroll.lean` (item 2), `NxCallback.lean` (the thunked callback rows),
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
  (`R1.lean`, `R1Thaw.lean`), and `muAdjNotVRLM` is withdrawn (`R1Thaw.lean`). Both stay citable
  as proved at `5210cf1`: the outcome and CHECKPOINT record them with the commit (§3.1, §5).

Those are the unit's only edits to existing definitions and statements, and the outcome must list
them. `WInsideCoreM` and `CoreInsideWM` stay as stated; the route that reads them reads them only at
types with no lifetime `∀` (§3.1, §3.4).

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
the guard. The missing step is one configuration that arises at which `withload`'s row hands its
callback a resource that the guard rejects wherever the callback's clause reads it.
- **Where the guard is read.** At `binder0` the callback is a `U` value. Its clause reads the
  forced computation at every instantiation of the stack (`RelendJ`), and the `∀` clause there
  reads every instance below the bound and every own push (`CbReading`).
  - At `withload`'s own type, `∀'x ⊏ ⊓Δ. F (Imm̲ 'x A ⊸ ['x] B)`, the `⊸` sits inside a second
    `U` value. That value instantiates again before the guard reads the argument.
  - At `withloadU`'s type (the same term, at the empty row), `∀'x ⊏ ⊓Δ. Imm̲ 'x A ⊸ F (['x] B)`,
    the `⊸` is directly under the `∀`.

  So the gate is posed at `withloadU`, where the guard at every `CbReading` is the whole obligation.
- **The arising check is a `TW` history.** The typed world already contains [TR] 6.150's entry as a
  constructor: `TW.reb` (`Core/World.lean:122`) composes the reborrowed resource `cb ∈ reb_β(r.R)`
  into the world at a record's `imm` cell. The history:
  - allocate the owner of `Ref 1 ⊗ Ref 1` and its two cells;
  - open the 6.64 lend (`LendImmI`, so the configuration is in `ArisesI` and the view is in
    `ArisesVI`);
  - apply `TW.reb` at the lend's record, at the lifetime of an own push of the callback's type.
- **`WithloadUPairGapReal`** is one existential over that configuration, and it carries every link:
  - the configuration arises, and so does the view (`PairCfg`);
  - the program typed at `withloadU` has `SemSM`'s index there, with the view as its context;
  - the view's cell is the record's, and `TW.reb` reborrows that cell's witness at an own push's
    lifetime into a tagged `TW` world, which keeps the last link from being vacuous;
  - at every reading the callback's clause offers, beside every resource the callback holds, the
    payload reborrowed at the reading's own lifetime fails the table there (`PairGuardRejectsU`).
- **The thunked form.** `withload`'s own type gets its own statement, which carries the answer's
  instantiations (`WithloadPairGapInst`). It is decided, and it does not trigger item 1b. At an
  instantiation that moves the lend below the instance, the reborrowed cells can meet the table
  [unchecked].
- **What "real" covers.** "Real" means real for [TR] 6.175's route: the reborrow at the reading's
  own lifetime. It is real at every reading, and that alone triggers item 1b (§1.5 says why).
  `PairCallbackGuardFailsLe` extends the rejection to any two borrow cells no longer-lived than the
  outermost lend. With `PairArgCellsLe` (optional) that covers every argument, but at the identity
  instantiation only. Slices get the same statements at `sliceBorrowIU`, with every link tied to
  the configuration (`SliceFrames`).

Item 1a's claims are about `vRLM` as it stands at `5210cf1`, before (E1)–(E4). The edited relation
reads fewer readings, so they cover it, and step 3.0 re-checks the rest. The empty stack is not part
of 1a:
- Before (E1), the table at `[]` holds of every resource, so the first conjunct reads the callback
  there and there is no gap (`PairNilOldGuardHolds`).
- After (E1), no instance in scope at the empty stack is below `⊓Δ`, so only the own push remains.
  At `withloadU`'s type the push fails the guard. This is decided against the edited relation in
  step 3.0 (item 1a′, `WithloadUPairGapNilE1`, with `WithloadPairGapNilInstE1` for the thunked
  form). It is a cost of (E1), disclosed before (E1) lands (§3.1).

If the gap is real, the fix is to the entry, not the table. A table that admits the cells would
leave cells at an internal lifetime that are neither a view nor above the cut. The thaw could then
only retain them, which breaks the cut, or transport them, which re-reads a stored invariant at a
moved reading. That is `mut_not_natural`'s mechanism, which the freeze binder exists to avoid. The
entry fix is a **block**: one lend of several places at one lifetime, under one binder. It is
represented with GhostEnd's `LEnt` unchanged, as consecutive entries sharing variable and lifetime.
Its cost is `StackOK`'s strict chain becoming a block chain (`StackOKB`), so every row at `binder0`
is re-proved at the revised relation. Two of its draft definitions are disclosed with their costs:
`ViewAtB` ties the block to the argument only at the `.arr` shape, and `OwnOKB.placeFree` is weaker
than `OwnOKI`'s (§1.6). That work is scheduled last (§5).

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
re-proved, restated, withdrawn, or rebuilt unchanged. One cost concerns the callback rows.
`CallbackExt*M` are stated at the `.arr` shape, the unwinding forms' callback type. The
non-unwinding constants' callbacks are thunked, so their own-push route is a new owed statement
(`CallbackExt*MF`). Then:
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
  - Each case is attempted unrestricted, then under the Core-value restriction (`MonoOwnGMCAt`,
    with `PushArrStepC` at types with no lifetime `∀`).
  - `reconB′`'s term is not changed.

**Item 4: `MonoHide` and the consumers.**
- `MonoHide` at `vRLM` is invisible when the hidden names cross no entry, or when no live type
  carries them. That covers both programs. The general case gets one bounded attempt, and its
  failing step is stated as an elaborating `def … : Prop` (`HideStopStep`).
- The consumers check starts from an inventory: every use of `MonoV`, `MonoG`, `MonoOwnG`, `MonoC`,
  `MonoHide` and their `M` forms in every file of the probe, each mapped to a replacement at `vRLM`
  or marked as a definition, a proof or prose.
  - Statement 4 gets its own entry: `AllRMono` at `vRLM` over the open types (`AllRMonoM0`). At
    `binder0` a row-polymorphic value made outside a borrow and used inside its callback crosses
    four index changes, and `AllRMonoM0` has one half for each: the record order, the own push, the
    instantiation the callback's `U` introduction thaws its captured slots at, and hiding.
  - Every row with no proof at `vRLM` is marked [unchecked: no row proof at vRLM].
  - The expected answer is that `AllIRowM` and `MonoExtM` are **not** all the consumers.
    `MonoHideGM` remains, and so do `AllRMonoM0`'s own-push half, its thaw half and its hide half's
    general case.
- Three owed rows are flagged that are not monotonicity: `VRLMUnroll` (item 2), the lifetime
  substitution `∀E` reads, and `effSub`.
- Only after the inventory and the table are complete may a document say what statement 0 at
  `binder0` reduces to, and then only with the table's caveat.

**Order.** (1a) → (2) → (3: (E1)–(E4), then 1a′ and `CallbackExt*MF`, then §3.2–§3.5) → (4) → (1b) →
docs. (2) and (3) are done whatever item 1 does (§5).

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
resource. It was asked for at `ArisesI` "ideally". Two conditions apply to that step:
- every link is proved of the same configuration, not as a conjunction of facts each provable on
  its own;
- the guard is read wherever the callback's clause reads it: at every instantiation that a `U`
  clause between the callback and its `⊸` offers, at every instance and at every own push.

### 1.2 What "real" means here

**Where a callback's clause reads its argument's guard.** At `binder0` a callback is a `U` value,
and `vRLM` reads a `U` value through `RelendJ` (`R1.lean`, `vRLM`'s `.thunk` clause;
`BinderJ.lean:53`). At every instantiation `ι` of the stack (`InstAt αs ι`: the identity, or a
re-stratification at the stack's cut, `Restrat.Emb`), it reads the forced computation at
`(σ, ι.sub δ, ι.life αs)`. The `∀` clause there offers two kinds of reading:
- the first conjunct: an instance `β` below the bound at the instantiated reading, at the stack
  `(σ, ι.life αs)`. Before (E1) every such instance is read; after it, those in scope;
- the own-lend conjunct: an own push `en` at `β` at the instantiated index, at the stack
  `(en :: σ, β :: ι.life αs)`.

`CbReading` (§1.3) names these readings. Where the argument's guard is read at a reading depends
on the callback's type:
- **`withloadU`'s callback** (`cbUTy`, `Core/EffBorrow.lean:177`, at the empty row:
  `∀'x ⊏ ⊓Δ. Imm̲ 'x A ⊸ F (['x] B)`; `pairCbUC`). The `⊸` is directly under the `∀`. Its guard
  reads the composite at the reading's stack and nowhere else, so the guard at every `CbReading`
  is the whole obligation.
- **`withload`'s callback** (`axWithloadTy`: `∀'x ⊏ ⊓Δ. F (Imm̲ 'x A ⊸ ['x] B)`; `pairCbC`). Here
  `VTy.lolli A B = U (A ⊸ F B)` (`Core/Types.lean:160`), so the instance's run answers a `U`
  value. That value's clause instantiates again, by an `ι₂` with `InstAt αs' ι₂`, before its `⊸`
  reads the argument at `(σ', ι₂.life αs')` and the reading `ι₂.sub δ'`. So the guard is read at
  every `ι₂` as well.

At the empty stack the only instantiation is the identity (`cutOf [] = none`). The answer's `U`
clause after a push still instantiates: `InstAt [β] ι₂` admits a cut above `β`.

**Why the gate is posed at `withloadU`.** `withloadU` types the same term `withload`
(`Targets/Base/Typing.lean:298`). At the empty row its side condition `Row.Unwind [] x` holds
vacuously, and it is in the probe's rule set. At its type, 6.175's route is rejected at every
reading. The route reborrows the payload at the reading's own lifetime (6.150's step at the
instance). The instance is chosen after `ι`, below the instantiated lend (`PairBoundBelow` at the
instantiated reading), so the reborrowed cells are below that lend too, and
`PairCallbackGuardFails` applies at `(σ, ι.life αs)`. At `withload`'s type the instance is fixed
before `ι₂`. An `ι₂` with `θ₂ α < β` exists (`Emb.shift`, `shift_fresh`), and at it the cells at
`β` sit strictly above the instantiated lend, where the table can hold [unchecked]. So `withload`'s
thunked form has its own statement, carrying the second quantifier (`WithloadPairGapInst`). It is
decided, and it does not trigger item 1b.

"Real" is one Lean fact about one configuration `c` (`WithloadUPairGapReal`), held to the arising
set's own standard (DESIGN §11). Links (a)–(c) are `PairCfg` and the conjuncts beside it. Link (d)
is `PairGuardRejectsU`.
- **(a) It arises.** `c ∈ ArisesI`, by a `TW` history and a 6.64 lend (`LendImmI`). Its stack is
  one entry `e`, named `'0`, at `α`, over `Ref 1 ⊗ Ref 1`. Its local part holds `e`'s view `ψ` at
  `e.l`, and the view arises (`ArisesVI.view`).
- **(b) It is the row's index.** The program `pairProgU cbE` is `withload p cb` with `withload`
  typed by `withloadU` at the empty row. It is typed at
  `'0 ⊏ ⊤; p : Imm '0 (Ref 1 ⊗ Ref 1) ⊢ _ : F B` (`ProbeRules`). The judgement's index holds at
  `c`: `SemIdxM` at `c`'s stack, lifetimes and list and at the view's resource
  (`ResU.single e.l ψ`), and `gRLM` at `γ = [loc e.l]`.
- **(c) The view is the record's, and the reborrow arises.** The open frame's record `r`
  (`r ∈ c.ps`, `r ∈ rsOf c.ls`, `r.le = e.l`) has `ψ.wit = r.R`, and `r.R` owns two distinct
  places that no entry lends. One own push `en` at `β` at `c`'s index has a closed payload type,
  and `TW.reb` reborrows `r.R` at that `β` into a tagged `TW` world. This witness keeps (d) from
  being vacuous: the reborrow that (d) quantifies over is one the typed world makes.
- **(d) The guard rejects the reborrow at every reading.** At every `CbReading` of
  `U (pairCbUC x B)` at `c`'s index, beside every resource the callback holds there, the record's
  payload reborrowed at the reading's own lifetime makes a composite that fails the table at the
  reading's stack.

**Which relation.** 1a's statements are about `vRLM` before (E1)–(E4): the index is `SemIdxM`
(with `StackJ`), and the readings are `OwnPushI`'s pushes and every instance below the bound. The
edited relation reads fewer readings: `OwnPushM` implies `OwnPushI`, and `InScope ∧ LtLife`
implies `LtLife`. So (d), proved before the edits, covers the edited relation's readings. Step 3.0
re-checks the rest:
- `StackJM` holds at `c`, because its entry is `pairΔ`'s;
- the witness push meets `OwnPushM`, because its payload type is closed;
- after (E1) the first conjunct reads no instance at `c`, at any instantiation. At the witness's
  reading `δ = ∅` (§1.4), the instantiated reading `extS (ι.sub ∅) [e] [ι.life1 α]` has one value,
  the instantiated lend's lifetime, and every instance below the bound is below it
  (`PairBoundBelow`).

| statement | what it is about |
|---|---|
| `PairRebCells` | `ResU.Reb` and `vShape`; no relation |
| `PairCallbackGuardFails`, `PairCallbackGuardFailsLe`, `SliceCallbackGuardFails`, `PairNilOldGuardHolds` | the table and the guard's views, which no edit changes |
| `PairBoundBelow` | `LtLife` at `extS`; no relation |
| `PairWithloadTyped`, `PairWithloadUTyped`, `SliceTyped`, `SliceUTyped` | typing |
| `PairArgCellsLe` | Core's `vC` and `TW` |
| `PairCfg`, `PairNilCfg`, `SliceCfg`, `SliceFrames`, `PairReb`, `CbReading` | the configuration, the reborrow and the frames, the readings (`OwnPushI`) |
| `WithloadUPairGapReal`, `SliceUGapReal` (the gate) | `vRLM`, `SemIdxM` and `OwnPushI` before (E1)–(E4); re-checked after |
| `WithloadPairGapInst`, `SliceGapInst` (decided, not a gate) | the same, with the answer's `U` clause read at `vRLM` |
| `WithloadUPairGapNilE1`, `SliceUGapNilE1`, `WithloadPairGapNilInstE1`, `SliceGapNilInstE1` (1a′) | the edited relation (`InScope`, `OwnPushM`) |

**What "real" covers.** It covers 6.175's route, where the argument is `TW.reb`'s: two `imm` cells
exactly at the reading's lifetime. Core's `ptoImmS` relates an argument read at an instance with
cells at any lifetime at or above that instance, so the callback's argument relation admits other
resources too.
- At the identity instantiation, `PairCallbackGuardFailsLe` rejects any two borrow cells no
  longer-lived than the outermost lend. `PairArgCellsLe` (optional, [unchecked]) would show that
  every argument the row can hand over has its cells there.
- At an instantiation that moves the lend below the argument's cells (`θ α < β' ≤ α`), the two
  no longer reject. Such an argument is not 6.175's: its cells are above the reading's instance,
  which is below `θ α`. The outermost lend is then `θ α`, and two cells at `β'`, which
  `PairArgCellsLe` allows, can meet the table [unchecked].
  Such a reading's run is about worlds tagged at its instantiated list (`RelendJ`'s `ls'`). That
  list keeps, with its moved tag, every record the callback's views are coherent with (`KeepsS`,
  `RecUpTo`). So when the callback holds a view of the lend, the configuration's world is not
  tagged at that list: its frame cell is at `α`, and the kept record's tag is `θ α` [unchecked:
  `Tagged`, `FrameLife`]. Whether a row could use such a reading at a callback holding no view is
  not attempted.

So "real" is claimed for 6.175's route, at every reading, and that claim alone triggers item 1b.
§1.5 says why it is enough.

**The empty stack is not in 1a.**
- Before (E1), GhostEnd's table at `[]` holds of every resource (`head?` and `getLast?` are
  `none`), and so do the guard's views (`PVLNil`). So at the empty stack the callback's first
  conjunct reads its run on the reborrowed argument, at every instance below the bound. There is
  no gap at the empty stack before (E1) (`PairNilOldGuardHolds`).
- No statement in the probe forces the spanning `withload` (`SpanLoadRow`) onto the own push before
  (E1). Whether `withload` pushes an entry at all is DESIGN §6.2's open "entry-kind finding"
  (`BINDER.md` §5.4 R2).
- After (E1), at the empty stack with a reading that maps only `Δ`'s variables, each once, no
  instance in scope is below `⊓Δ`. So the first conjunct reads nothing. At `withloadU`'s type
  every own push fails the guard (`PairCallbackGuardFails` at `σ = []`), and the empty stack has no
  other instantiation. That is (E1)'s cost. Step 3.0 decides it in Lean, against the edited
  relation (`WithloadUPairGapNilE1`, §1.3). At `withload`'s type the push's answer still
  instantiates, and `WithloadPairGapNilInstE1` decides whether its guard rejects there.

### 1.3 The statements (item 1a)

```lean
/-- `Ref 1 ⊗ Ref 1`: a payload with two `Ref` leaves side by side. -/
abbrev pairTy : VTy := .tensor (.ref .unit) (.ref .unit)

/-- `'0 ⊏ ⊤`: the lend's binder, the lifetime context the program is typed in. -/
abbrev pairΔ : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `p : Imm '0 (Ref 1 ⊗ Ref 1)`: the view, the one live slot. -/
abbrev pairΓ : Ctx VTy := [⟨.imm (.var 0) pairTy, true⟩]

/-- `withloadU`'s callback at the pair, at the empty row (`cbUTy`, with `CTy.effOf [] R = F R`), as
the computation type its `U` clause forces: `∀'x ⊏ ⊓Δ. Imm̲ 'x (Ref 1 ⊗ Ref 1) ⊸ F (['x] B)`. The
`⊸` is directly under the `∀`. -/
abbrev pairCbUC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.arr (pairTy.immReborrow (.var x)) (.ret (.box (.var x) B)))

/-- `withload`'s callback at the pair (`axWithloadTy`), as the computation type its `U` clause
forces: `∀'x ⊏ ⊓Δ. F (Imm̲ 'x (Ref 1 ⊗ Ref 1) ⊸ ['x] B)`. The `⊸` is inside the `U` value the
instance's run answers. -/
abbrev pairCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (pairTy.immReborrow (.var x)) (.box (.var x) B)))

/-- `withload p cb` at `withloadU`'s typing: `cb` is bound, then `withload` is bound, forced
(`forceE` at an arrow type is the variable itself) and applied to `p` and `cb` (`app` takes
variables). Under the second binder, slot `0` is `withload`, `1` the callback and `2` the view. -/
abbrev pairProgU (cbE : Expr) : Expr :=
  .app (.val (.lam (.app (.val (.lam (.app (.app (.var 0) (.var 2)) (.var 1)))) withload))) cbE

/-- **The pair configuration**: links (a)–(c) of §1.2 that concern `c` alone. `c` is in the revised
arising set, with one 6.64 entry `e` named `'0` at `α` over `Ref 1 ⊗ Ref 1`. Its local part holds
`e`'s view `ψ`, which arises there. `ψ`'s witness is the open frame's record's, and it owns the
payload's two places, which are distinct and lent by no entry. The judgement's index holds at `c`
at the reading `δ`, with the view as the context. -/
def PairCfg (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
    (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧ e.T = pairTy ∧
    c.ρ.get e.l = some ψ ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' (ResU.single e.l ψ)) (.loc e.l) (viewTy e) ∧
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.le = e.l ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧
    ψ.wit = r.R ∧ r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧
    l₁ ≠ l₂ ∧ l₁ ∉ c.σ.map LEnt.l ∧ l₂ ∉ c.σ.map LEnt.l ∧
    SemIdxM pairΔ pairΓ (.ret B) δ c.σ c.αs c.ls (ResU.single e.l ψ) ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls pairΓ [.loc e.l] (ResU.single e.l ψ)

/-- **[TR] 6.150's reborrow of a record's payload at `β`** (`TW.reb`'s resource premises): `reb_β`
of the witness, with the reborrowed type's shape holding of the record's value at the reading
extended at `'x ↦ β`. -/
def PairReb (r : FrameRec) (x : LifeVar) (β : Life) (cb : WRes) : Prop :=
  ResU.Reb β r.R cb ∧ vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb

/-- **A reading that a callback's clause offers at an index** (`vRLM .binder0`'s `U` clause, then
the `∀` clause of `C = ∀'x ⊏ b. _`). First an instantiation `ι` of the stack (`RelendJ`'s
`InstAt`). Then the reading extended at `'x ↦ β`, where `β` is either an instance below the bound
at the instantiated reading, with the instantiated stack (the first conjunct; after (E1), the
instances in scope among these), or the lifetime of an own push at the instantiated index, with the
pushed stack (the own-lend conjunct). `σ'` and `αs'` are where a `⊸` directly under the `∀` reads
its guard, and `ρk` is the resource the forced computation holds there. -/
def CbReading (δ : LSub) (C : CTy) (x : LifeVar) (b : Lifetime.Life) (σ : LStack)
    (αs : List Life) (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) : Prop :=
  ∃ ι : Inst, InstAt αs ι ∧ δ' = (ι.sub δ).extend x β ∧
    ((σ' = σ ∧ αs' = ι.life αs ∧ LtLife (extS (ι.sub δ) σ (ι.life αs)) b β) ∨
      ∃ en : LEnt, OwnPushI (ι.sub δ) C ρk (σ, ι.life αs) en β ∧ σ' = en :: σ ∧
        αs' = β :: ι.life αs)

/-- **Link (d) at `withloadU`'s callback.** At every reading that the clause of `U (pairCbUC x B)`
offers at the index, beside every resource the callback holds there, the record's payload
reborrowed at the reading's own lifetime (6.175's route) fails the table where the `⊸` reads it. -/
def PairGuardRejectsU (c : Cfg) (δ : LSub) (r : FrameRec) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (cb ρ : WRes),
    CbReading δ (pairCbUC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β →
    PairReb r x β cb → ResU.CompS ρk cb ρ → ¬ TabAtS σ' αs' ρ

/-- **Link (d) at `withload`'s callback**: `PairGuardRejectsU` at `U (pairCbC x B)`, with the
answer's `U` clause read as well. At every reading, every instantiation `ι₂` of the reading's
stack, every list and every resource beside it, the reborrow at the reading's lifetime is either
not related at the reborrowed type at the instantiated reading, or fails the instantiated table. -/
def PairGuardRejectsF (c : Cfg) (δ : LSub) (r : FrameRec) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (cb : WRes),
    CbReading δ (pairCbC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β → PairReb r x β cb →
    ∀ (ι₂ : Inst) (ls : List SRec) (ρz ρ : WRes), InstAt αs' ι₂ →
      vRLM (ℍ := ℍ) .binder0 none σ' (ι₂.sub δ') (r.T.immReborrow (.var x)) (ι₂.life αs') ls
        r.v cb →
      ResU.CompS ρz cb ρ → ¬ TabAtS σ' (ι₂.life αs') ρ

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

/-- **The guard rejects the reborrowed argument at both kinds of stack** (`loadGuardFails2`,
`tabAtS_comp`). Beside any closure resource, two `imm` cells exactly at `β`, at distinct places the
stack does not lend, fail the table at the stack itself when `β` is below its innermost lend, and
at every own-lend push at `β`. At `αs = []` the first part is vacuous: the table at `[]` holds of
every resource. A lemma for `PairGuardRejectsU` at each reading: an instantiation keeps the stack
and moves its lifetimes, so the lemma applies at `(σ, ι.life αs)`. -/
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
any kind but `own`, at any lifetime at or below the outermost lend `o`. At an instantiated stack,
`o` is the instantiated outermost lend. -/
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
`PairCallbackGuardFailsLe` it would extend "real" beyond the `reb_β` route, at the identity
instantiation of the callback's `U` clause. -/
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
at `α`, every instance of `withload`'s `∀'x ⊏ ⊓Δ` (`Δ = '0 ⊏ ⊤`) is below `α`. It holds at every
reading and every `α`, so at every instantiation of `c`'s index, where `α` is the instantiated
lend. -/
def PairBoundBelow : Prop :=
  ∀ (δ : LSub) (e : LEnt) (α β : Life), e.x = 0 →
    LtLife (extS δ [e] [α]) pairΔ.meetOfDom β → β < α

/-- **Typing reaches `withload` at its thunked typing inside a lend**: under the lend's binder
`'0`, the view `p : Imm '0 (Ref 1 ⊗ Ref 1)` applied to `withload` with a callback, in the probe's
rule set (`CDerivesNU.withload`, `lolliE` twice and `ret`, through `probeRules_of_nu`). A lemma. -/
def PairWithloadTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules pairΔ pairΓ (.app (.app withload (.var 0)) cb) (.comp (.ret B))

/-- **Typing reaches `withload` at its unwinding typing inside a lend**: `pairProgU` with the
callback at `withloadU`'s type at the empty row (`CDerivesNU.withloadU`, `bind` twice, `force`,
`app` twice). A lemma. -/
def PairWithloadUTyped : Prop :=
  ∃ (cbE : Expr) (B : VTy), ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B))

/-- **The two-cell gap is real at `withload`'s unwinding typing, at one configuration** (the gate
for item 1b). At a pair configuration:
- the program is typed, with `withload` at `withloadU`'s type at the empty row;
- one own push at the index has a closed payload type, and [TR] 6.150's step (`TW.reb`) reborrows
  the record's payload at that push's lifetime into a tagged typed world;
- at every reading the callback's clause offers (`CbReading`: each instantiation of the stack,
  then each instance below the bound or each own push), the reborrow at that reading's lifetime
  fails the guard (`PairGuardRejectsU`). The `⊸` is directly under the `∀`, so these are all the
  stacks its guard reads.

Real for 6.175's route. The claim is about `vRLM` before (E1)–(E4); §1.2 says what is re-checked
after them. -/
def WithloadUPairGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
      (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) (cbE : Expr) (x : LifeVar) (en : LEnt)
      (β : Life) (ρc cb fρ' : WRes),
    PairCfg (ℍ := ℍ) c e α ψ ρf' r l₁ l₂ δ B ∧
    ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B)) ∧
    OwnPushI δ (pairCbUC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    ¬ VFree x r.T ∧ PairReb r x β cb ∧ StratumLe c.fρ β ∧
    ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls ∧
    PairGuardRejectsU c δ r x B

/-- **`withload`'s thunked form, with the answer's instantiations** (decided in 1a; not a gate):
at every pair configuration, `PairGuardRejectsF`. -/
def WithloadPairGapInst : Prop :=
  ∀ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
    (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) (x : LifeVar),
    PairCfg (ℍ := ℍ) c e α ψ ρf' r l₁ l₂ δ B → ¬ VFree x r.T →
    PairGuardRejectsF (ℍ := ℍ) c δ r x B

/-- **At the empty stack the guard holds of every resource** (GhostEnd's `TabAtS` at `[]`;
`PVLNil`). So before (E1) the callback's first conjunct at the empty stack reads its run on the
reborrowed argument, at every instance below the bound, and there is no gap there. A fact about
`vRLM` before (E1). -/
def PairNilOldGuardHolds : Prop :=
  ∀ (s : LSub) (ls : List SRec) (ρ : WRes), TabAtS [] [] ρ ∧ PlaceViewsL s [] [] ls ρ
```

**Item 1a′: the empty stack after (E1).** These statements go in `Nx.lean` when (E1)–(E4) land
(step 3.0), since they read `InScope` and `OwnPushM`.

```lean
/-- **The pair configuration at the empty stack.** `c` is in the revised arising set at the empty
stack. Its world holds an open 6.64 frame over `Ref 1 ⊗ Ref 1`, whose record `r` owns two distinct
places, and its local part holds the frame's `imm` cell `ψ`. The judgement's index holds at `c` at
the reading `δ`, with the cell's place as the context. -/
def PairNilCfg (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub)
    (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [] ∧ c.αs = [] ∧ c.ρ.get r.le = some ψ ∧
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧ ψ.wit = r.R ∧
    r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧ l₁ ≠ l₂ ∧
    SemIdxM pairΔ pairΓ (.ret B) δ [] [] c.ls (ResU.single r.le ψ) ∧
    gRLM (ℍ := ℍ) .binder0 [] δ [] c.ls pairΓ [.loc r.le] (ResU.single r.le ψ)

/-- **After (E1), the gap at the empty stack, at `withloadU`'s callback.** At a pair configuration
at the empty stack, at a reading `δ` whose only value is `ψ`'s lifetime:
- the program is typed; one own push is at `OwnPushM`, and `TW.reb` reborrows the record's payload
  at its lifetime;
- no instance in scope meets the bound, so the first conjunct reads nothing, and the empty stack
  has no other instantiation (`cutOf [] = none`);
- at every own push, beside every resource the callback holds, the reborrow at the push's lifetime
  fails the table at the push.

So after (E1) the own push is the only route, and it fails. Before (E1) the first conjunct read the
callback here (`PairNilOldGuardHolds`). `p` is not shown to arise by `ArisesVI`: no transition of
the set makes an `Imm` value arise at the empty stack, other than a run's answer. What is shown is
the configuration's world and the index. -/
def WithloadUPairGapNilE1 : Prop :=
  ∃ (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy)
      (cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc cb fρ' : WRes),
    PairNilCfg (ℍ := ℍ) c ψ r l₁ l₂ δ B ∧
    ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B)) ∧
    OwnPushM δ (pairCbUC x B) ρc ([], []) en β ∧ ¬ VFree x r.T ∧ PairReb r x β cb ∧
    StratumLe c.fρ β ∧ ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧
    Tagged fρ' c.ps c.ls ∧
    (∀ β', LtLife δ pairΔ.meetOfDom β' → ¬ InScope δ β') ∧
    ∀ (ρk : WRes) (en' : LEnt) (β' : Life) (cb' ρ : WRes),
      OwnPushM δ (pairCbUC x B) ρk ([], []) en' β' → PairReb r x β' cb' →
      ResU.CompS ρk cb' ρ → ¬ TabAtS [en'] [β'] ρ

/-- **After (E1), the empty stack at `withload`'s callback, with the answer's instantiations**
(decided; not a gate). At every pair configuration at the empty stack, at every own push at
`OwnPushM` and every instantiation of the push's stack by the answer's `U` clause, the reborrow at
the push's lifetime is either not related at the instantiated reading, or fails the instantiated
table. -/
def WithloadPairGapNilInstE1 : Prop :=
  ∀ (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy)
    (x : LifeVar), PairNilCfg (ℍ := ℍ) c ψ r l₁ l₂ δ B → ¬ VFree x r.T →
    ∀ (ρk : WRes) (en : LEnt) (β : Life) (cb : WRes),
      OwnPushM δ (pairCbC x B) ρk ([], []) en β → PairReb r x β cb →
      ∀ (ι₂ : Inst) (ls : List SRec) (ρz ρ : WRes), InstAt [β] ι₂ →
        vRLM (ℍ := ℍ) .binder0 none [en] (ι₂.sub (δ.extend x β)) (r.T.immReborrow (.var x))
          (ι₂.life [β]) ls r.v cb →
        ResU.CompS ρz cb ρ → ¬ TabAtS [en] (ι₂.life [β]) ρ
```

`SliceUGapNilE1` and `SliceGapNilInstE1` are the same two statements at a slice (`sliceΓ`,
`sliceCbUC` and `sliceCbC`, the family of `SliceFrames` at the push's lifetime in place of
`PairReb`, related at `[Imm 'x 1]`), with the array arising at the empty stack. They are stated
with them.

**Slices.** The family comes from an owned array that a run at the stack makes (`array_new`, so
the array arises by `ArisesVI.ret`). The slice borrow's run makes two 6.64 frames at the reading's
lifetime (`TW.immFrame` at each element), which give the `[Imm 'x 1]` family. The imm form is used
so that no `mutFold` with an arbitrary predicate enters; the guard reads only places and lifetimes
in any case. The gate is posed at `sliceBorrowIU`'s typing, for the reason given for `withloadU`.
Its term is `withborUE d`, so the program carries a closed finaliser `d : Array 1 ⊸ 1`, built from
`array_free` (`arrFree`).

```lean
/-- `a : Array 1`: the owned array, the one live slot. -/
abbrev sliceΓ : Ctx VTy := [⟨.array .unit, true⟩]

/-- `slice_borrow_imm`'s unwinding callback at `Array 1`, at the empty row (`sliceBorrowIUTy`'s
`cbUTy`), as the computation type its `U` clause forces: `∀'x ⊏ ⊓Δ. [Imm 'x 1] ⊸ F (['x] B)`. -/
abbrev sliceCbUC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.arr (.arrayImm (.var x) .unit) (.ret (.box (.var x) B)))

/-- `slice_borrow_imm`'s callback at `Array 1` (`sliceBorrowITy`), as the computation type its
`U` clause forces. -/
abbrev sliceCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (.arrayImm (.var x) .unit) (.box (.var x) B)))

/-- The slice borrow at `sliceBorrowIU`'s typing, with the finaliser `d`: `cb` is bound, then
`withborUE d` is bound, forced and applied to `a` and `cb`. -/
abbrev sliceProgU (d cbE : Expr) : Expr :=
  .app (.val (.lam (.app (.val (.lam (.app (.app (.var 0) (.var 2)) (.var 1)))) (withborUE d))))
    cbE

/-- **The slice configuration.** `c` is in the revised arising set, with one 6.64 entry named `'0`
at `α`. An owned array of two elements at `ℓ` and `ℓ + 1`, places no entry lends, arises there at
`Array 1` with the resource `ρa`. The judgement's index holds at `c` at the reading `δ`, with the
array as the context. -/
def SliceCfg (c : Cfg) (e : LEnt) (α : Life) (ℓ : BoCa.Loc) (ρa ρf' : WRes) (δ : LSub)
    (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' ρa) (Val.arr ℓ 2) (.array .unit) ∧
    (∀ i < 2, ℓ + i ∉ c.σ.map LEnt.l) ∧
    SemIdxM pairΔ sliceΓ (.ret (.tensor (.array .unit) B)) δ c.σ c.αs c.ls ρa ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls sliceΓ [Val.arr ℓ 2] ρa

/-- **Two 6.64 frames at `β` over the array's elements** (`TW.immFrame` twice, from `c`'s world).
The elements' owned cells are the array's (`ρa`). They become the family `ρs`: two `imm` cells
exactly at `β`, with empty witnesses. The frames' records head `ps'`, and `ls'` is `c.ls` with
them in front, tagged at `β`. -/
def SliceFrames (c : Cfg) (ρa : WRes) (ℓ : BoCa.Loc) (u₀ u₁ : Val) (δ₀ : LSub) (β : Life)
    (ρs W' : WRes) (ps' : List FrameRec) (ls' : List SRec) : Prop :=
  ρa.get ℓ = some (CellU.ownOf u₀) ∧ ρa.get (ℓ + 1) = some (CellU.ownOf u₁) ∧
    ∃ (X Z : WRes) (h₀ h₁ : ResU.InStratum (LSet.singleton β).join PMap.empty),
      ResU.CompS (ResU.single ℓ (CellU.ownOf u₀)) (ResU.single (ℓ + 1) (CellU.ownOf u₁)) X ∧
      ResU.CompS X Z c.fρ ∧
      ResU.CompS (ResU.single ℓ (CellU.immOf (LSet.singleton β) u₀ PMap.empty h₀))
        (ResU.single (ℓ + 1) (CellU.immOf (LSet.singleton β) u₁ PMap.empty h₁)) ρs ∧
      ResU.CompS ρs Z W' ∧
      ps' = ⟨ℓ + 1, u₁, PMap.empty, .unit, δ₀⟩ :: ⟨ℓ, u₀, PMap.empty, .unit, δ₀⟩ :: c.ps ∧
      ls' = (⟨ℓ + 1, u₁, PMap.empty, .unit, δ₀⟩, β) :: (⟨ℓ, u₀, PMap.empty, .unit, δ₀⟩, β) ::
        c.ls ∧
      TW W' ps' (rsOf ls') ∧ Tagged W' ps' ls'

/-- **Link (d) at `slice_borrow_imm`'s unwinding callback.** At every reading that the clause of
`U (sliceCbUC x B)` offers at the index, a family of two `imm` cells exactly at the reading's
lifetime at the array's elements, beside every resource the callback holds there, fails the table
where the `⊸` reads it. -/
def SliceGuardRejectsU (c : Cfg) (δ : LSub) (ℓ : BoCa.Loc) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (ρs ρ : WRes),
    CbReading δ (sliceCbUC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β →
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) →
    ResU.CompS ρk ρs ρ → ¬ TabAtS σ' αs' ρ

/-- **The two-cell gap is real at a two-element slice at its unwinding typing, at one
configuration** (the gate for item 1b, with `WithloadUPairGapReal`). At a slice configuration:
- the program is typed, with `withborUE d` at `sliceBorrowIU`'s type at the empty row;
- one own push at the index has a closed payload type, and two 6.64 frames at that push's lifetime
  turn the array's two owned elements into a family of `imm` cells in a tagged typed world, whose
  frames and records are `c`'s with the two new ones in front (`SliceFrames`);
- at every reading the callback's clause offers, such a family at the reading's lifetime fails the
  guard (`SliceGuardRejectsU`). -/
def SliceUGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ℓ : BoCa.Loc) (ρa ρf' : WRes) (δ : LSub) (B : VTy)
      (d cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc : WRes) (u₀ u₁ : Val)
      (δ₀ : LSub) (ρs W' : WRes) (ps' : List FrameRec) (ls' : List SRec),
    SliceCfg (ℍ := ℍ) c e α ℓ ρa ρf' δ B ∧
    ProbeRules pairΔ sliceΓ (sliceProgU d cbE) (.comp (.ret (.tensor (.array .unit) B))) ∧
    OwnPushI δ (sliceCbUC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    SliceFrames c ρa ℓ u₀ u₁ δ₀ β ρs W' ps' ls' ∧
    SliceGuardRejectsU c δ ℓ x B

/-- **The guard rejects the family at both kinds of stack** (`sliceGuardFails` with `tabAtS_comp`,
and the old stack's first conjunct). A lemma for `SliceGuardRejectsU` at each reading. -/
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

/-- **Typing reaches a slice borrow at its unwinding typing inside a lend** (`sliceBorrowIU` at the
empty row, `d` a closed finaliser at `Array 1 ⊸ 1`). A lemma. -/
def SliceUTyped : Prop :=
  ∃ (d cbE : Expr) (B : VTy),
    ProbeRules pairΔ sliceΓ (sliceProgU d cbE) (.comp (.ret (.tensor (.array .unit) B)))
```

`SliceGuardRejectsF` and `SliceGapInst` are `PairGuardRejectsF` and `WithloadPairGapInst` at the
slice: `sliceCbC`, `SliceCfg`, and a family of two `imm` cells exactly at the reading's lifetime in
place of `PairReb`, related at `[Imm 'x 1]` at the instantiated reading. They are stated with the
pair's.

The world-link conjuncts (the `TW` and `Tagged` facts, the parts that compose to them, and
`SliceFrames`' lists where `Desc` gives a frame descendants) may be tightened while proving. Nothing
else may be weakened:
- the links (a)–(d) of §1.2 stay conjuncts about the one configuration;
- (d) stays universal: over every `CbReading`, every resource the callback holds, and every
  reborrow (or family) at the reading's lifetime;
- the conjuncts the guard argument reads stay as they are: the cells exactly at the reading's
  lifetime, the two places distinct, the stack's places, and the bound read below the lend.

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
- **The witness push.** `en` is at a place and variable new to the stack and to the closure's
  resource, with payload type `1`. It sits at a `β` below every lifetime of the world and of `ρc`.
  That gives `OwnOKI`, and `β < α` gives the bound's `LtLife`. `ViewAt` is vacuous at both callback
  types: the argument type `Imm 'x 1 ⊗ Imm 'x 1` is no `Mut` or `Imm` of a variable.
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
- **Link (d), reading by reading.** Unfold `CbReading` to its instantiation `ι` and its case. The
  stack is `c.σ`, so `l₁` and `l₂` are still unlent, and `ι.life [α] = [ι.life1 α]`. Then:
  - at the first conjunct, `PairBoundBelow` at the reading `ι.sub δ` and the lifetime
    `ι.life1 α` gives `β < ι.life1 α`, and `PairCallbackGuardFails`' first part applies;
  - at a push, `OwnOKI`'s `chain` and `var` give `StackOK (en :: c.σ) (β :: ι.life c.αs)` (the
    stack `[e]` has one entry, and an instantiation keeps the lengths), and
    `PairCallbackGuardFails`' second part applies.

  In both cases `PairRebCells` gives the two cells.
- **The guard lemmas.**
  - `PairCallbackGuardFails` uses `tabAtS_comp` (`GhostEnd/Arising.lean:83`). The old stack fails
    the first conjunct (`InStratum (↓h)` at a cell at `β < h`), and the push uses
    `loadGuardFails2`.
  - `PairCallbackGuardFailsLe` uses the second conjunct with `lt_at_of_inStratum`, as
    `sliceGuardFails` does.
  - `SliceCallbackGuardFails` uses `sliceGuardFails` the same way, and `SliceGuardRejectsU`
    follows reading by reading as above.
- **The bound.** `PairBoundBelow` uses `meetOfDomL` at one entry (`meet (var 0) top`) and
  `Life.interp`.
- **Typing.** `CDerivesNU.withloadU` at the empty row (`Row.Unwind []` is vacuous), `bind` twice,
  `force` at the bound constant and `app` twice, through `probeRules_of_nu`. The slice:
  `sliceBorrowIU`, its finaliser from `arrFree`, and `array_new` for the array's run. The thunked
  forms: `CDerivesNU.withload` (`sliceBorrowI`), `lolliE` twice and `ret`.
- **The thunked forms (`WithloadPairGapInst`, `SliceGapInst`).** One bounded attempt each, in both
  directions. The expected outcome [unchecked] is the negation, at the gate's configuration: the
  identity reading of the callback's clause, the first conjunct at an instance `β < α`, and the
  answer's instantiation `ι₂ = Inst.ofEmb (Emb.shift cut k)` with `k` large enough that
  `ι₂.life1 α < β` (`shift_fresh`). There:
  - `ι₂.life1 β ≤ β` (`Emb.le_self`), so Core's `ptoImmS` admits the cells at `β`;
  - the record is kept in the list (take `ls = c.ls`), so `CohE` holds;
  - `CohS` and `RetainedPay` are vacuous or trivial at an unlent place of payload type `1`;
  - with `ρz = PMap.empty`, the composite is `cb`, whose cells at `β` are above the instantiated
    lend, so the table holds.

  If the negation is proved, the outcome says so. It is a fact about the thunked form's guard, and
  it is not shown that a row can use that reading (§1.2, "What real covers").
- **1a′ (step 3.0).**
  - The configuration is `ArisesI.nil` over a `TW` world built by `alloc` three times and
    `immFrame`, with the frame's cell in the local part.
  - The reading is `δ = ⟨[(0, m)]⟩`, where `α = toDual m`.
  - The first conjunct is empty: `δ`'s only value is `α`, and the bound is `α`.
  - Every push is at `OwnPushM`; the witness's payload type is closed.
  - `WithloadPairGapNilInstE1` gets the thunked forms' bounded attempt, at the answer's
    instantiation of `[β]` with `ι₂.life1 β < β`.

### 1.5 Success and failure

- **Real** means `WithloadUPairGapReal`, or `SliceUGapReal`, is proved. Item 1b then runs, last
  (§5).
- **Not real.** A link is false, or its proof needs a change to a definition. Then record which
  link and why:
  - the configuration is not in `ArisesI`, or the view (the array) is not in `ArisesVI`;
  - the index (`SemIdxM`, `gRLM` at the view) is not met at the configuration;
  - no own push is available at the index;
  - `TW.reb`'s premises (the frames') cannot be met at the configuration;
  - the shape forces fewer than two cells;
  - the composite meets the guard at some reading;
  - the program is not typable at the unwinding type.

  Do not run item 1b, and say why in the outcome.
- **The thunked forms** (`WithloadPairGapInst`, `SliceGapInst`) are decided either way, and the
  outcome reports the result. They do not trigger item 1b and do not stop it.
- **Why 6.175's route is enough to trigger 1b.** The design follows the printed proof. [TR] 6.175
  reborrows the payload at the instance it picks for the callback, by 6.150's step at that
  lifetime, and applies the callback there. If our draft guard rejects that argument at every
  reading the clause offers, the printed step does not go through at our relation, and the guard
  is ours. A row proof that hands over another argument, with cells at another lifetime and at a
  reading that moves the lend, would be a route the printed proof does not take. The plan does not
  look for one, and §1.2 records what is known about such readings.
- **The standard met.** `c` is in `ArisesI`, and its view in `ArisesVI`. The world after the
  reborrow (`fρ'`) or after the frames (`W'`) meets `TW` and `Tagged`. It is not shown to be part of
  a configuration in `ArisesI`: that set has no transition for a reborrow, or for frames without a
  pushed entry, until item 1b adds `LendRebI` and `LendSliceI`.
  This is the arising set's standard at the configuration and `TW`'s at the callback's world. It is
  not a closed program's execution, so it is evidence that the guard misses the printed route's
  argument, and it refutes no row. No printed object is in question: the guard and the stack are
  ours.
- **1a′** is decided in step 3.0, whatever 1a's result. Its outcome is (E1)'s cost made exact
  (§3.1).

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
as `OwnPushM`'s (§3.1). `ViewAtB` is read at the `.arr` shape only (see below). -/
def OwnPushB (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (τ : LStack) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ x ∉ CTy.binders C' ∧
    OwnOKB δ s.1 s.2 x τ a ρ ∧ LtLife (extS δ s.1 s.2) c a ∧
    (∀ e ∈ τ, ∀ y, VFree y e.T → CFree y C) ∧
    ∀ A D, C' = .arr A D → ViewAtB x τ A
```

**Where `ViewAtB` ties the block to the argument.** It is read behind the guard
`C' = .arr A D`, as `OwnPushI`'s `ViewAt` is. So it constrains the block at the `.arr` shape
`∀'x ⊏ c. A ⊸ D`. That is the unwinding forms' callback type (`cbUTy`: `withloadU`,
`sliceBorrowIU`, `sliceBorrowMU`, `withbor1U/2U/3U`) and `foldImm`'s algebra
(`∀'y ⊏ ⊤. A_R ⊸ F R`) [read: the rule's docstring]. Item 1a's gate is posed at that shape, so
there the block is the argument's leaves. At the non-unwinding constants' shape
`∀'x ⊏ c. F (A ⊸ ['x] B)` (`axWithloadTy`, `sliceBorrowITy`, `sliceBorrowMTy`,
`axWithbor1Ty/2Ty/3Ty`, all built with `VTy.all`), `C'` is a `.ret`, and `ViewAtB` is vacuous.
There `OwnPushB` admits every block that meets `OwnOKB`, and nothing ties the block to the leaves.
The cost is on the producer's side: the `∀` clause's own-lend conjunct at those types quantifies
over every such block, and the `∀I` row must serve each one. The constants' rows pick the leaves'
block. The plan adds no guard at the `.ret` shape. That would be a further draft change, and
`OwnPushBOfM` would then need `OwnPushM` to carry the same guard.

**A disclosed draft change: `OwnOKB.placeFree` is weaker than `OwnOKI.placeFree`.** `OwnOKI` asks
`∀ ψ, ¬ DeepAt ρ e.l ψ`: the callback holds no cell at the lent place, at any depth. `OwnOKB`
admits `own` cells at a block place, provided each is under an `imm` ancestor
(`ψ.kind = own ∧ ¬ ExAt ρ e.l ψ`).
- **Why.** A callback can hold a copy of the lend's view (`copy`, then capture). That view's
  witness holds the payload's `own` cells, at the very places the block lends, frozen under the
  view's `imm` cell. Under `OwnOKI`'s condition no block push is admissible at such a callback, and
  the gap stays open there.
- **What it costs.**
  - The own-lend conjunct quantifies over more pushes: blocks at places the callback deep-holds
    frozen. The `∀I` row must serve them.
  - Row 4's justification below no longer follows from "the holder holds nothing at a block place".
    It is restated, and `PVLStartB` carries the relaxed condition as its hypothesis.
- **The fallback.** If row 4's restated route or `PVLStartB` fails at a frozen cell, use
  `OwnOKI`'s strict condition for blocks. Then record that a callback holding a copy of the view has
  no block push, and the gap stays open for such callbacks.

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
and the views at the pushed stack. At `WithloadUPairGapReal`'s configuration, at the push of every
reading (each instantiation of the stack), it is the gap's fix. -/
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
2. `CallbackExtMutMB` and `CallbackExtImmMB`, and their thunked forms `CallbackExtMutMFB` and
   `CallbackExtImmMFB` (§3.1): the own-lend conjunct at `τ = [en]` (`OwnPushBOfM`).
3. `ForceRowMB` and `MonoExtMB`.
4. `MonoOwnGUFreeMBA`: the block push at contexts reaching no `U`. A context value's top-level
   cells are not at a block place: `placeFree`'s `¬ ExAt` rules out an exposed cell there. So every
   leaf of a context type (a top-level cell) is at a place no block entry lends, and its `CohS` and
   `RetainedPay` read the same entries as before the push. An `own` cell frozen at a block place
   sits inside an `imm` ancestor's witness, which W reads only through Core's `Imm` clause, at no
   stack [read: `vRLM`'s `Imm` leaf]. The guard's views at the block's places, with such cells
   present, are `PVLStartB`'s.
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
  beyond those listed here. The listed changes are:
  - `StackOKB`, `LeafTyAt`, and `ViewAtB`, read at the `.arr` shape only;
  - `OwnOKB` with its relaxed `placeFree` (or, on the fallback, `OwnOKI`'s), and `OwnPushB`;
  - the `∀` clause, `StackJB`, `SemSMB` and the two transitions.

  Record the frontier. `vRLMB` stays a candidate in its own files until rows 1–4 are proved.
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
the type (`payLocal`) and not the binder (`selfFree`). The own pushes the callback rows use meet
it. Each row takes `e.T = T`, the argument's payload type, as a hypothesis, and the constant's side
condition keeps the binder out of `T` (`hfree₁`, (E4)). `OwnPushI`'s `ViewAt` forces `e.T = T` only
at the `.arr` shape with a `Mut` or `Imm` argument of the binder; at the thunked shape it is
vacuous. -/
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
  - Why it is the fact needed: `CallbackExt*M` take `e.T = T` as a hypothesis, so (E4) gives
    `OwnPushM`'s `selfFree` at the pushed entry directly. It does not rest on `ViewAt`.

**The callback rows' two shapes.** Every non-unwinding borrow constant's callback is built with
`VTy.all` (`axWithbor1Ty/2Ty/3Ty`, `axWithloadTy`, `sliceBorrowMTy/ITy`). Its computation type is
the thunked shape `∀'x ⊏ c. F (U (A ⊸ F (['x] B)))` [checked by `rfl` in the scratch file for
`axWithloadTy` and `sliceBorrowITy`; read for the others]. The own-lend conjunct runs `e ()` to a
`U` value, which `vRLM`'s `U` clause
reads at the pushed stack before its `⊸` reads the view. `CallbackExt*M` (`R1.lean:1285`,
`:1301`), `RetainedPayLoadImmRow` (`R1.lean:864`), `RetainedPaySliceRow` and `OwnPushI`'s `ViewAt`
guard are stated at the `.arr` shape `∀'x ⊏ c. A ⊸ D`. That is the unwinding forms' callback type
(`cbUTy`, `Core/EffBorrow.lean:177`: `withbor1U/2U/3U`, `withloadU`, `sliceBorrowMU/IU`) and
`foldImm`'s algebra (`∀'y ⊏ ⊤. A_R ⊸ F R`) [read: the rule's docstring]. Stating these at the
`.arr` shape predates this unit (`BINDER.md:1920`, R1's statements). So the non-unwinding
constants' own-push route is a new statement at their own shape. It is owed and listed in the
table:

```lean
/-- **The 6.65 callback at `σ·y`, at the non-unwinding constants' shape**: `CallbackExtMutM` with
the callback at `∀'y ⊏ c. F (Mut 'y T ⊸ B')` (`axWithbor2Ty`, `axWithbor3Ty`, with
`B' = ['y] B`). The own push's run of `f ()` answers a `U` value; `vRLM`'s `U` clause reads it at
the pushed stack, and at the identity instantiation its `⊸` takes the view. With (E4)'s
`¬ VFree y T`. -/
def CallbackExtMutMF (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T B' : VTy)
    (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (α : Life) (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .mut → e.T = T → y ∉ CTy.binders (.ret (.lolli (.mut (.var y) T) B')) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls → SubFresh δ α →
    TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    vRLM (ℍ := ℍ) p none σ δ (VTy.all y c (.lolli (.mut (.var y) T) B')) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) (.ret B') (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-- **The 6.64 callback at `σ·y`, at the non-unwinding constants' shape**: `CallbackExtImmM` with
the callback at `∀'y ⊏ c. F (Imm 'y T ⊸ B')` (`axWithbor1Ty`; `axWithloadTy` at a `Ref` payload,
where `Imm̲ 'y (Ref T) = Imm 'y T`). With (E4)'s `¬ VFree y T`. -/
def CallbackExtImmMF (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T B' : VTy)
    (αs : List Life) (ls ls' : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (u : Val) (α : Life)
    (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .imm u → e.T = T → y ∉ CTy.binders (.ret (.lolli (.imm (.var y) T) B')) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls' →
    SubFresh δ α → TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    Ext ls ls' ρf → KeepsT ls ls' ρf →
    vRLM (ℍ := ℍ) p none σ δ (VTy.all y c (.lolli (.imm (.var y) T) B')) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.imm (.var y) T) (α :: αs) ls' w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls' ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) (.ret B') (α :: αs) ls'
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ
```

The route [unchecked]:
- `callbackExt*M_own`'s own-lend step gives the run of `f ()` at the pushed index (`all_ownM` at
  `OwnPushM`). Its answer is a `U` value at the run's final list, which has the same members as
  the list it started at (`wpTS`).
- At the identity instantiation, `RelendJ` hands back the same views at that list (`Ext`, `KeepsT`
  and `KeepsS` reflexive; `RecsOutside` by the equal members).
- `monoExtM0` carries the view `w` to that list. The answer's guard comes from the run
  (`wpTS_tabAt`).
- The `⊸` clause applies at `w`, and `wpTS`'s bind at the evaluation context `.app [·] (.val w)`
  gives the conclusion.

**What each edit costs, stated before it lands.**
- **(E1)**:
  - *The empty-stack route of the borrow constants.* Take an index whose stack's variables are all
    `Δ`'s and whose reading maps only `Δ`'s variables, each once. Every value in scope there is the
    value of one of `Δ`'s variables, and none of these is below `⊓Δ`. So at such an index (the
    empty stack among them, and a stack of `Δ`'s own entries), the first conjunct of a callback
    typed `∀'x ⊏ ⊓Δ` reads nothing. At an index with an entry of the second or third kind, or with
    a shadowed binding, an instance in scope below `⊓Δ` may exist, and nothing here depends on
    one. The constants read the callback at their own push. Which statement gives that route
    depends on the callback's shape and payload:
    - At the `.arr` shape with an argument that is one `Mut` or `Imm` of the binder (`withbor1U`,
      `withbor2U`, `withbor3U`; `withloadU` at a `Ref` payload), `CallbackExt*M` gives it, proved
      at one entry and re-proved with (E4).
    - At the non-unwinding constants' thunked shape with such an argument (`withbor` (1)–(3);
      `withload` at a `Ref` payload), `CallbackExt*MF` would give it, and it is owed. Until it is
      proved, (E1) leaves these constants with no proved route at any stack.
    - At a `withload` payload with two leaves side by side, or at a slice of two or more elements,
      the push fails the guard at the `.arr` shape at every reading (item 1a), and at the thunked
      shape at the identity reading of the answer. So after (E1), and with no block (item 1b),
      these have no route at any stack by 6.175's argument. At the thunked shape an instantiated
      reading of the answer may admit the argument (`WithloadPairGapInst`, `SliceGapInst`), and
      §1.2 records what is known about using it. Before (E1), the empty stack's first conjunct read
      them (`PairNilOldGuardHolds`).

    1a′ decides the empty stack in Lean: `WithloadUPairGapNilE1` and `SliceUGapNilE1` at the
    unwinding forms, and `WithloadPairGapNilInstE1` and `SliceGapNilInstE1` at the thunked forms.
    If 1b's gate fails, `vRLM` keeps (E1) and this cost, and the outcome states it as a decision
    for the user: keep (E1), which §3.3's transports read, or revert it, which restores the
    empty-stack route and leaves the live-`U`-slot transports open.
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
| `callbackExtMutM_own`, `callbackExtImmM_own` (`R1Stmt0.lean:399`, `:414`), their four instances | E2, E4 | statements restated (E4); re-proved: `payLocal` from `CFree` at `y' ≠ y`, `selfFree` from the added hypothesis. They are about the `.arr` shape, the unwinding forms' callbacks |
| `CallbackExtMutMF`, `CallbackExtImmMF` (new, `Nx.lean`, step 3.0) | E2, E4 | owed: the non-unwinding constants' own-push route at their thunked shape, with (E4)'s hypothesis; proved in `NxCallback.lean` by the route above, or stated with the frontier |
| `WInsideCoreM`, `CoreInsideWM` (`R1.lean:726`, `:733`) | E1 | unchanged, and not attempted at `5210cf1`. At a type with a lifetime `∀`, (E1) makes W's `∀` clause read only the instances in scope, while Core's reads every instance below the bound; so `WInsideCoreM` is not expected there [unchecked]. At a `VAllFree` type no `∀` clause is read, and (E1) does not touch either statement. The restricted route reads them only at `VAllFree` types: `PushArrStepC` carries `VAllFree A` and `CAllFree D` (§3.4), and `retryR`'s instances' argument `!U(1 → F_{exn ⊙ s} bool)` and answer `bool` are `VAllFree`. The builder proves the `VAllFree` instances it reads, as lemmas with that hypothesis |
| `statement0MBesideMono0` (`:439`) | E4 | what it says changes (E4); re-proved |
| `statement0MAtConsumers0_iff`, `not_statement0M_binder0` | follow | rebuild |
| `allIRowMNKAt0_of` (`R1AllI.lean:322`) | E1, E2, E3 | re-proved: the own-lend case takes `OwnPushI` from `OwnPushM`; `StackJM` at both premise indices (the pushed entry is of the first kind; at the extended reading the old entries keep their kinds). `SemSMNK` may keep `StackJ`: at an index whose stack does not name the binder, the two agree |
| `allIRowMNKUFree0`, `allIRowMNKNil0` | follow | rebuild |
| `gdAllIHoldsAtMt` (`R1AllI.lean:670`) | E1, E2 | re-proved: its proof does not read the conjuncts' hypotheses |
| `gdRowRefutation` (`R1Mono.lean:1253`) | E3 | re-proved: `gd`'s index meets `StackJM`, since `gdX.x = 0` is `gdΔ`'s; `GdIndex` keeps `StackJ` |
| `gdIndex`, `gdRelated`, `gdNotPushed`, `notMonoOwnGM0`, `notMonoGM0`, `notMonoVM0`, `monoUnrestrictedRefuted0`, `gdNotCore`, `gdCtxNotCore`, `gdRestrictedMet` | none | rebuild: `gdTy` has no `∀`, and `MonoOwnGM` takes `OwnPushI` as a hypothesis |
| `vRLM_none_eq`, `cRLM_eq`, `effRetM_eq`, `relMAgreesJ` (`R1Thaw.lean:86–193`) | E1, E2 | restated with `VAllFree`/`CAllFree` added; re-proved (`cRLM_eq`'s `.all` case becomes impossible) |
| `muAdjNotVRLM` (`R1Thaw.lean:686`) | E1 | withdrawn. Its proof rewrites with `vRLM_none_eq` at `U(adjC)`, where `adjC = ∀'0 ⊏ ⊤. F (Mut '0 1)` (`Gap.lean:262`), and (E1) is expected to make its statement false. The definition `MuAdjNotVRLM` stays, and the build proves `MuAdjVRLME1` or records it not derived. The outcome, CHECKPOINT and `R1MONO.md` §8.1 record `muAdjNotVRLM`, and the unrestricted `relMAgreesJ`, as proved facts about `vRLM` at commit `5210cf1`, citing the commit, so the evidence stays citable |
| `relendM_thunk`, `relendMValueE`, `relendMValue`, `thawInstM`, `ctxRelendsAllM` (`R1Thaw.lean`) | none | rebuild: they compose instantiations (`instComp`) and never open `cRLM` [read: `R1Thaw.lean:317–331`]. No proof in the development carries the `∀` clause along an instantiation, so `InScope` never has to survive one there. `VRLMReadEquiv`'s `U` case (§3.3) is the first place that needs it |
| `thunkF_U_M`, `thunkV_U_M` (`R1Thaw.lean:582`, `:608`), the four `U` rows, `statement0UFullM` | E3 | re-proved: the premise at the instantiated index needs `StackJM` there. `SubFresh` moves along the instantiation, which is strictly monotone on the reading's values and on the head. The payload avoidance is about types |
| `forceRowM`, `statement0SharedM`, `nilSoundRetM`, `vRLMDataE`, `vRLMMonoAt`, `vRLMRoll` | none | rebuild |
| `monoExtM0`, `monoExtME0`, `monoOwnGUFreeMA`, `monoOwnUFreeMEA`, `vRLM_reading_uFree`, `ctx*MAt_uFree`, `monoOwnGMCUFreeA` | none | rebuild: each passes `cRLM` through at `U` (`vRLM_thunk_ext`) or reads `U`-free types |
| `RetainedPayLoadImmRow`, `RetainedPaySliceRow`, `RetainedPayLoadImmRowMet` | E2 | statements unchanged: they take `OwnPushI`, which `OwnPushM` gives. A `Met` witness should also meet `OwnPushM`'s new conjuncts, so that it witnesses the row as the edited relation reads it. They are stated at the `.arr` shape, the unwinding forms' callbacks; the docs step says so |
| item 2's `rollRowM`, `unrollRowM` (proved before E3) | E3 | re-proved: `StackJM` at `.ret` is `StackJ` |
| item 1a's results (proved before E1–E4) | E1–E4 | re-checked (§1.2): link (d) already covers the edited relation's readings (`OwnPushM` implies `OwnPushI`; `InScope ∧ LtLife` implies `LtLife`). Checked: the witness push at `OwnPushM`, `StackJM` at the configuration, and the first conjunct empty there at every instantiation |
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
`CoreInsideWM` at `D`'s answer. Both are read at types with no lifetime `∀` (`VAllFree A`,
`CAllFree D`), where (E1) changes neither relation. `gd` is outside the restriction
(`GdCtxNotCore`). -/
def PushArrStepC : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (e : Expr)
    (ρf : WRes) (en : LEnt) (a : Life) (w : Val) (ρv ρ : WRes),
    VAllFree A → CAllFree D →
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
   - At `⊸`, Core's clause reads every argument (`PushArrStepC`). The route reads `WInsideCoreM`
     and `CoreInsideWM` only at types with no lifetime `∀`, which `retryR`'s instance types are
     (§3.1's table).
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
    is §4.2's own entry: it also carries the callback's `U` introduction, which thaws `retryR`'s
    slot, and `retry`'s handler, which hides `exn` around the body that uses it. The plan does not
    reshape the term to move `retryR` out of the context.
  - DESIGN §9.2's own typing question (retry's body capturing the `Imm` view) is a separate choice
    that the builder of `reconB′` makes and records. It is not used to avoid the `∀I` row.

### 3.6 Success and failure

- **Success.** All of the following, with the statements of §3.1–§3.4:
  - (E1)–(E4) land, and every result in §3.1's table is at its disposition;
  - `MuAdjVRLME1` is decided;
  - item 2's rows are re-proved at `StackJM`, item 1a is re-checked, and 1a′ is decided;
  - `CallbackExtMutMF` and `CallbackExtImmMF` are proved, or stated with their frontier;
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

**Step 1: the inventory.** List every use of `MonoV`, `MonoG`, `MonoOwnG`, `MonoC` and `MonoHide`,
and of their `M` forms, in every file of the probe: each `*.lean` file in `ProbeD1/` and each `*.md`
file in `experiments/ProbeD1`, this file excepted. The builder re-runs the search
(`grep -n "MonoV\|MonoG\|MonoOwnG\|MonoC\|MonoHide"` over those files). Each hit is either mapped
to a row of the first table below, or marked in the second as a definition, a proof, an
implication between monotonicity statements, or prose that names one of the first table's rows.
Only then is the inventory called complete. The designer's reading of that search [read] gives
the following.

The consumers:

| use site | what it consumes | its replacement at `vRLM .binder0` | status |
|---|---|---|---|
| `Statement1.lean`'s `AllIRow` (docstring, l. 142); DESIGN §2.2 (l. 235–237), §2.5 (l. 494), §5.3 (l. 1064) | `MonoOwnG` at the `∀` clause's own push | `AllIRowM`, through its three transports (item 3) | remains at the contexts §3.5 lists |
| DESIGN §2.2 (l. 236), §2.4 (l. 424–426): `ThunkVRow`, `BangThunkVRow`; `Sem.lean`'s `OwnHyg` (docstring, l. 56) | `MonoOwnG` at the `U` clause's own push (`cbpv`) | none: `binder0`'s `U` clause makes no own push, and the rows are proved (`statement0UFullM`) | no consumer at `binder0` |
| `Statement0.lean`'s `MonoHideFromMonoV`; `Statement34.lean`'s `HandleRow` (docstring, l. 12); DESIGN §7 (l. 1333) | `MonoHide`, from `MonoV` | `MonoHideGM .binder0` (§4.1) at value-type contexts; `AllRHideM0` at a row-polymorphic slot; `MonoVM .binder0` is refuted | the invisible cases are to prove; the general case remains |
| `Statement34.lean`'s `AllRMono` (and its docstring, l. 17); DESIGN §8 (l. 1376) | `MonoV` at each instance; at `binder0`, `MonoC` | `AllRMonoM0` (below): four halves | the record-order half is to prove; the own-push half remains (3b-ii at the instance types); the thaw half is to prove at `retryR`'s empty resource and needs `RelendJInter` elsewhere; the hide half's invisible case is to prove |
| `R1MONO.md` §4.1; `Statement0MAtConsumers0` | `MonoExtM`, for `[let]` and the end of a lend | `MonoExtM .binder0` | proved (`monoExtM0`); the rows that read it are [unchecked: no row proof at vRLM] |
| DESIGN §2.4 (l. 419–422), §2.5 (l. 483), §4.3 (l. 840–860); `Thunk.lean` (docstring, l. 34); `R1MONO.md` §4.3's `MonoGPart` | `MonoV`, `MonoG`, `MonoC` at futures | none: `binder0` reads no future (`FutQI false`) | `cbpv` and `binder` only; outside this check |
| DESIGN §4.3 (l. 819–822) | `MonoC`, for `MonoV` at a `U` value | internal to `MonoV` | not a consumer |

The hits that are not consumers:

| files | what the hits are |
|---|---|
| `Statement0.lean` (l. 21–149, 263), `R1.lean` (l. 21–31, 350–477, 509–606, 655–749, 1266, 1320–1338) | definitions, docstrings, and the bundles `Statement0`, `Statement0M`, `MonoUnrestrictedRefuted0`, `Statement0MAtConsumers0` |
| `R1.lean`'s `MonoGMOfMonoVM`, `MonoOwnGMOfMonoGM`, `MonoOwnGUFreeMOfE`, `AllIRowMOfMonoOwnGM`, `AllIRowMCOfMonoOwnGMC`, `MonoOwnGMA`, `MonoOwnGMC` | implications between monotonicity statements, and the restricted forms |
| `Mono.lean` (`monoV_*`, `monoG_*`, `gSepRL_mono`, `monoHideFromMonoV`, `monoHide_*`), `Own.lean` (`monoOwnG_*`), `R1Mono.lean` (`gSepRLM_mono`, `monoGMOfMonoVM`, `monoOwnGMOfMonoGM`, `notMono*0`, `monoOwnGUFreeMA`, `monoOwnGMCUFreeA`), `R1AllI.lean` (`allIRowMNKAt0_of`'s hypothesis `MonoOwnGMAt`, `monoOwnGMAt_uFree`), `R1Stmt0.lean` (l. 447) | proofs. `allIRowMNKAt0_of` is the `∀I` row's, already the first table's first row |
| `Relation.lean` (l. 25), `World.lean` (l. 25–26), `Own.lean` (l. 4–23), `Mono.lean` (l. 16–20) | docstrings naming `MonoOwnG` as `MonoG`'s instance at the push, or `MonoHide` as `MonoV`'s |
| DESIGN l. 52, 626–688, 729–814, 1686–1753, 1843–1950, 1987–2018, 2159–2282; `R1MONO.md`; `BINDER.md` (l. 199–202, 1623–1723, 2325–2422); `GAP.md` (l. 430, 567, 812); README (l. 34–49, 291–294, 361, 387); CHECKPOINT | statement tables, definitions quoted in prose, outcome narratives and re-proof lists. Every consumer they name is a row of the first table |

**Step 2: statement 4's own entry.** `AllRMono` (`Statement34.lean:77`) is stated over `ovalW`, at
the old relation `vRL`, along `Fut`, with `Ext`. `AllIRowM`, `MonoOwnGMAt`, `MonoHideGM` and
`statement0UFullM`'s context thaw range over value-type contexts (`Ctx VTy`) at `vRLM`, which has no
`∀ρ` former. So none of them can express this consumer, and `monoExtM0` covers its record-order half
only instance by instance. It is restated at `vRLM`. `ovalUM` and `ovalWM` are statement 4's
construction read at the one draft relation; they add no relation beside it.

`retryR` is made at `σ = []` and used inside the first borrow's callback (DESIGN §9.2). Between
the two, at `binder0`, it crosses four index changes:
- the record order (`Ext`), along the runs between;
- the callback's own push (the `∀` clause's own-lend conjunct);
- the instantiation that the callback's `U` introduction thaws every captured slot at
  (`CtxRelendsAllM` inside the `U` rows; `RelendJ`'s `ι`);
- `retry`'s handler, which hides `exn` around the body that uses `retryR`.

`reconB′` is not built, so this list is read off DESIGN §9.2's shape [read], and Step 3's table
checks it rule by rule. `AllRMonoM0` has one half per index change.

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

/-- **`AllRMono`'s record-order half at `vRLM .binder0`**: a row-polymorphic value carried along
an extension of the list that keeps the tags. -/
def AllRExtM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls ls' : List SRec) (ρv : RVar) (k : RowCon)
    (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → RecsOutside αs ls' →
    Ext ls ls' r → KeepsT ls ls' r → TabAtS σ αs r → PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls' (.thunk (.allR ρv k C)) η v r

/-- **`AllRMono`'s own-push half**: carried across the callback's own push (`OwnPushM`, with the
`∀` clause's freshness). -/
def AllROwnM0 : Prop :=
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

/-- **`AllRMono`'s instantiation half**: the thaw (`RelendMValue`'s form) through the
intersection. A `U` introduction at `binder0` thaws every captured slot (`CtxRelendsAllM`, inside
`statement0UFullM`). This is that step at a slot holding a row-polymorphic value, which
`statement0UFullM`'s contexts do not range over. -/
def AllRThawM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : RVar) (k : RowCon)
    (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs r →
    PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    RelendJ δ σ
      (fun δ' αs' ls' => ovalWM (ℍ := ℍ) .binder0 σ δ' αs' ls' (.thunk (.allR ρv k C)) η v)
      αs ls r

/-- **`AllRMono`'s hiding half**: carried into a handler of the names `N` (`[handle]`'s context
transport, `MonoHideGM`'s step, at a slot holding a row-polymorphic value). -/
def AllRHideM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : RVar) (k : RowCon)
    (C : Targets.Inst.OCTy) (η : RowEnv) (v : Val) (r : WRes) (N : UInt32 → Bool),
    StackOK σ αs → TabAtS σ αs r → PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 (hideS N σ) δ αs ls (.thunk (.allR ρv k C)) η v r

/-- **Statement 4's `AllRMono` at `vRLM .binder0`**: a row-polymorphic value carried along the
four index changes between its making and its use inside a borrow's callback. -/
def AllRMonoM0 : Prop :=
  AllRExtM0 (ℍ := ℍ) ∧ AllROwnM0 (ℍ := ℍ) ∧ AllRThawM0 (ℍ := ℍ) ∧ AllRHideM0 (ℍ := ℍ)

/-- **An intersection commutes with `RelendJ`**: a resource meeting `RelendJ` at each member of a
nonempty family of clauses meets it at their intersection. The step `AllRThawM0` takes at a slot
that holds resource. -/
def RelendJInter : Prop :=
  ∀ (I : Type) (P : I → LSub → List Life → List SRec → WProp) (δ : LSub) (σ : LStack)
    (αs : List Life) (ls : List SRec) (ρ : WRes), Nonempty I →
    StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    (∀ i, RelendJ δ σ (P i) αs ls ρ) →
    RelendJ δ σ (fun δ' αs' ls' ρ' => ∀ i, P i δ' αs' ls' ρ') αs ls ρ
```

`retryR` sits at `!U(∀ρ ∌ exn. …)` (DESIGN §9.2), so its slot is `ovalWM`'s `!` case: the resource
is empty, and each half there is the `.thunk` half at the empty resource.
- **The record-order half.** `monoExtM0` at each instance's type, through the intersection. To
  prove.
- **The own-push half.** `MonoOwnGMAt` at the one-slot context of each instance's type, through
  the intersection. At `retryR` the instances are outside `PushStable`, so this half stays open
  unless 3b-ii closes at them.
- **The thaw half.** `ThawInstM` (inside `statement0UFullM`) at each instance's type, then the
  intersection through `RelendJ`'s existential split.
  - At the empty resource the split is forced: both parts are empty and every flag is off
    [unchecked: that `vwSW` at an empty resource forces each visible flag off]. So the intersection
    commutes. To prove at `retryR`'s slot.
  - At a slot that holds resource it is `RelendJInter`. Its route is that the split is determined
    by the resource, up to flags at shadowed entries, which `vwSW` does not read. The views are the
    cells at the stack's places at the entries' lifetimes, and the retained part is the rest,
    strictly above the outermost lend [unchecked]. One bounded attempt; otherwise state it with its
    frontier.
- **The hide half.** At `reconB′`'s stacks the hidden `exn` crosses no entry (the callback's row is
  `{wait}`), so `HideInvisible` gives `hideS (· == exn) σ = σ`, and the half is the identity there.
  The general case is `HideStopStep`'s, with `MonoHideGM`'s.

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
context carries that context along the first run, which is `MonoExtM`'s shape. A slot of the
context may hold a row-polymorphic value (an `ovalWM` slot); at such a slot each transport is
`AllRMonoM0`'s matching half. The expected table, to be checked, not assumed:

| index change | rules | transport | status |
|---|---|---|---|
| none: same index, split resource, no run between premises | `app`, `force`, `ret`, `ofRet`, `withI`, `proj`, `sumI`, `zeroE`, `boxI`, `boxE`, `immSub`, `mutSub`, `lam` (`binder0`'s `⊸` reads the stack itself), `nuIn`, `nuOut`, `effPerform`, `effRaise`, the premise-free constants other than the borrow constants | none | [unchecked: no row proof at vRLM] |
| list extended along a run (`Ext`) | `bind`, `tensorI`, `unitE`, `tensorE`, `sumE`, `bangE`, `lolliE`, `effLet` and `effThen` (between stops), a lend's end (6.64's `ext_add`) | `MonoExtM`; at an `ovalWM` slot, `AllRExtM0` | transport proved (`monoExtM0`); `AllRExtM0` to prove; rows [unchecked: no row proof at vRLM] |
| re-lend at a resume or an instantiation | the `U` rows, `effLet` and `effThen` across a stop, the spanning rules | the thaw (`CtxRelendsAllM`); at an `ovalWM` slot, `AllRThawM0` | `U` rows proved at value-type contexts (`statement0UFullM`); `AllRThawM0` to prove (Step 2); the others [unchecked: no row proof at vRLM] |
| own push, reading extension, shadow | `allI` | `MonoOwnGMAt`, `CtxExtendMSAt`, `CtxExtendNamedMSAt`, `CtxShadowMSAt`; at an `ovalWM` slot, `AllROwnM0` | item 3; `AllROwnM0` remains at `retryR` (3b-ii) |
| a row-polymorphic value instantiated | statement 4's `RC_allRE` at a value made outside the borrow (`AllRMono`), `RC_allRI` | `AllRMonoM0`, and `AllREW` at the instance | Step 2 |
| hiding | `effHandle` | `MonoHideGM`; at an `ovalWM` slot, `AllRHideM0` | §4.1; Step 2 |
| callback at its own push, `.arr` shape, one `Mut` or `Imm` leaf | `withbor1U/2U/3U`; `withloadU` and `foldImm`'s algebra at a payload whose reborrow is one `Imm` leaf | `CallbackExt*M` | proved at one entry, with (E4)'s hypothesis; the rows [unchecked: no row proof at vRLM] |
| callback at its own push, thunked shape, one leaf | `withbor` (1)–(3); `withload` at a `Ref` payload | `CallbackExt*MF` (§3.1) | owed; the rows [unchecked: no row proof at vRLM] |
| callback at a payload with two leaves, or a family | `withload` and `withloadU` at two leaves side by side; `sliceBorrowM/I`, `sliceBorrowMU/IU` | none at one entry (item 1) | item 1b at a block, if it runs; [unchecked] |
| the spanning rules' callbacks | `SpanRule1`, `SpanRule2`, `SpanRuleLoad` | as their constants' rows above, at a resuming row | [unchecked: no row proof at vRLM] |

These are owed rows that are not monotonicity consumers. They are flagged, not decided:
- `roll` and `unroll`: item 2.
- `allE` and `allEV`: the lifetime substitution, `cRLM` at `C.instLife x b` read at
  `δ.extend x ⟦b⟧`. It is not stated at `vRLM`. `RetainedPayInstRow` is its `RetainedPay` part, at
  a `b` with no join.
- `effSub`: row subsumption at the `F_Σ` clause.

The `U` introduction's context thaw is not a monotonicity transport either. At a value-type context
it is proved (`statement0UFullM`). At a row-polymorphic slot it is `AllRThawM0`, carried in
statement 4's entry, because statement 4's `AllRMono` is where DESIGN derives a row-polymorphic
value's transports, and at `binder0` that transport across a `U` introduction is the thaw.

**Step 4: the corrected conjunction**, which replaces `Statement0MAtConsumers0` in every claim:

```lean
/-- **Statement 0 at `binder0`, read at the consumers the inventory finds.** Its conjuncts:
- the facts beside monotonicity;
- the record order;
- the `∀I` row (its context across the own push, to the binder's reading, and to the shadow);
- `[handle]`'s context into the hidden stack;
- statement 4's `AllRMono` at `vRLM .binder0`, which DESIGN derives from `MonoV` and `MonoC`: its
  four halves (record order, own push, the thaw, hiding). -/
def Statement0MAtConsumers0Full : Prop :=
  Statement0MBesideMono0 (ℍ := ℍ) ∧ MonoExtM (ℍ := ℍ) .binder0 ∧ AllIRowM (ℍ := ℍ) .binder0 ∧
    MonoHideGM (ℍ := ℍ) .binder0 ∧ AllRMonoM0 (ℍ := ℍ)
```

**Success and failure.**
- **Success.**
  - `hideInvisible`, `vRLMHideAvoid` and `monoHideGMHandle0` are proved. `HideStopStep` is proved,
    refuted at an arising configuration, or stated with its frontier.
  - `AllRExtM0` is proved, `AllRThawM0` at the empty resource and `AllRHideM0`'s invisible case are
    proved, and `RelendJInter` is proved or stated with its frontier.
  - The inventory is confirmed complete over every file of the probe, and every hit is mapped or
    marked.
  - The table is complete. Each row with a proof at `vRLM` cites it; every other row carries
    [unchecked: no row proof at vRLM].
  - `Statement0MAtConsumers0Full` is stated, and `statement0MAtConsumers0_iff`'s docstring says that
    it holds by the definition of our own conjunction.
- **What may be claimed.** "Statement 0 at `binder0`, read at the consumers the inventory finds, is
  `Statement0MAtConsumers0Full`. Its open parts are:
  - `AllIRowM` at the contexts §3.5 lists;
  - `MonoHideGM` where the hidden name crosses an entry and a live type carries it, and
    `AllRHideM0` there too;
  - `AllRMonoM0`'s own-push half;
  - `AllRMonoM0`'s thaw half at a row-polymorphic slot that holds resource, unless `RelendJInter`
    is proved.

  Beside the conjunction, the non-unwinding constants' callback rows at their own shape
  (`CallbackExt*MF`) are owed, and the callbacks at a payload with two leaves or a family have no
  route at one entry (item 1). The table's rows marked [unchecked: no row proof at vRLM] are
  predictions of the transport each row reads, not checked consumers. Until each of those rows is
  proved at `vRLM`, the table may miss a consumer." The claim "reduces to the `∀I` row" is
  withdrawn.

---

## 5. Order of work and the stop rule

1. **Item 1a** (`Nx.lean`, `NxGuard.lean`), against `vRLM` as at `5210cf1`: the gate
   (`WithloadUPairGapReal`, `SliceUGapReal`) and its lemmas, then the thunked forms' decision
   (`WithloadPairGapInst`, `SliceGapInst`). The gate decides whether item 1b exists.
2. **Item 2** (`NxUnroll.lean`), against `SemSM` before (E3). Independent and mechanical.
3. **Item 3** (`NxAllI.lean`), in this order:
   - **3.0** (E1)–(E4) in `R1.lean`, with every result in §3.1's table brought to its disposition;
     `MuAdjVRLME1`; item 2's rows re-proved at `StackJM`; item 1a re-checked; then item 1a′
     (`WithloadUPairGapNilE1`, `SliceUGapNilE1`, `WithloadPairGapNilInstE1`, `SliceGapNilInstE1`,
     in `Nx.lean` and `NxGuard.lean`); then `CallbackExtMutMF` and `CallbackExtImmMF` (`Nx.lean`,
     `NxCallback.lean`);
   - §3.2;
   - §3.3;
   - §3.4: 3b-i, then 3b-ii;
   - §3.5's record.
4. **Item 4** (`NxHide.lean`): the inventory over every file of the probe, `AllRMonoM0`'s four
   halves and `RelendJInter`, the table.
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
     condition, with item 1a's and 1a′'s results, the thunked forms' result, and the scope of
     "real" (6.175's route, at every reading; §1.2);
   - correcting `R1MONO.md`'s carry-over sentences (§0, §1.2, §1.3, §6's table), and every mention
     of `muAdjNotVRLM` as a fact about `vRLM` (CHECKPOINT, README, DESIGN §15.9, `R1MONO.md` §8.1),
     as §3.1's table says. `muAdjNotVRLM` and the unrestricted `relMAgreesJ` are recorded as
     proved facts about `vRLM` at commit `5210cf1`, with the commit cited;
   - recording that `CallbackExt*M`, `RetainedPayLoadImmRow`, `RetainedPaySliceRow` and
     `OwnPushI`'s `ViewAt` are stated at the unwinding forms' `.arr` shape, not at the non-unwinding
     constants' thunked shape. The mismatch predates this unit (`BINDER.md:1920`; `R1.lean:864`,
     `:1285`, `:1301`). README, DESIGN §15.9 and `R1MONO.md` §8 say so wherever they describe
     those rows as the borrow constants' rows.

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
| `Nx.lean` | all of this unit's definitions and `def … : Prop` statements (items 1a, 2, 3, 4). Those of 1a and 2 come first; those that read `InScope`, `OwnPushM` or `StackJM` (1a′, `CallbackExt*MF`, item 3, `AllRMonoM0`, 1b's gate) are added at step 3.0 |
| `R1.lean` (edited) | (E1) `InScope` in the `∀` clause, (E2) `OwnPushM` in the own-lend conjunct, (E3) `StackJM` in `SemSM`; `InScope`, `OwnPushM`, `StackJM` defined above `vRLM`; (E4) `¬ VFree y T` on `CallbackExtMutM` and `CallbackExtImmM`; `VAllFree`, `CAllFree`; `RelMAgreesJ` restated |
| `R1Thaw.lean`, `R1Stmt0.lean`, `R1AllI.lean`, `R1Mono.lean` (re-proofs) | §3.1's table: the restated helper equalities and `relMAgreesJ`; `muAdjNotVRLM` withdrawn; `MuAdjVRLME1` decided; the re-proved results |
| `NxGuard.lean` | item 1a's proofs; 1a′'s proofs after step 3.0 |
| `NxCallback.lean` | `CallbackExtMutMF` and `CallbackExtImmMF` (step 3.0) |
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
  - [TR] 6.175 (`withload_compatX`, its bound `⊓Δ`, and its route: the reborrow at the instance the
    proof picks for the callback, and the application there);
  - [TR] 6.64's and 6.65's H4 (the lends at the new transitions);
  - spec §9's slice borrows (`sliceBorrowITy`, `array_new`, `array_free`);
  - spec §19's unwinding forms (`withloadU`, `sliceBorrowIU`, `cbUTy`), at the empty row.
- **Printed hypotheses unspent**: list them per lemma.
- **Uniqueness and functionality results**: `ResU.CompS.functional`, `CellU.CompS.functional` and
  `RebAt`'s piece disjointness are expected, and `RelendJInter`'s route reads the determinacy of
  `RelendJ`'s split. List which are used and which are not.
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
    it, with `PushArrStepC`'s `VAllFree A` and `CAllFree D`;
  - the new statements at the non-unwinding constants' shape, `CallbackExtMutMF` and
    `CallbackExtImmMF`;
  - item 1b's definitions, if it runs: `ViewAtB` read at the `.arr` shape only, and `OwnOKB`'s
    relaxed `placeFree` (or the strict one, on the fallback), each disclosed in §1.6.
- **The technique built**: no printed proof governs W's draft relation. `VRLMSubst` is `vCE_subst`'s
  route at W's clauses. `VRLMReadEquiv` is a symmetric invariance, not a one-way transport, because
  `⊸` reads its argument contravariantly.

---

## 8. The design reviews' findings, answered

### 8.1 The first review

The names below are the current ones. §8.2 changed the gate's form and the reading of link (d).

| finding | the change |
|---|---|
| Item 1 does not tie the arising configuration to the row (major) | `WithloadUPairGapReal` and `SliceUGapReal` are each one existential over one configuration. Each carries `ArisesI`, the typed judgement's `SemIdxM` and `gRLM` at `γ = [loc e.l]`, `ψ = c.ρ.get e.l` with `ψ.wit = r.R`, `TW.reb` at an own push's `β`, and the composite failing at every reading the callback's clause offers (§8.2). `PairCallbackGuardFails` is a lemma (§1.2, §1.3). |
| The nil case has no guard statement, and is claimed before (E1) (major) | The nil case is removed from 1a. `PairNilOldGuardHolds` states that before (E1) there is no gap at `[]`. 1a′ (`WithloadUPairGapNilE1`, with `WithloadPairGapNilInstE1` for the thunked form) decides the case against the edited relation at step 3.0. A table says which relation each claim is about (§1.2, §1.3, §5). |
| (E1)/(E2) touch unlisted results; the stop rule would revert itself (major) | §3.1's table gives every touched result a disposition: `relMAgreesJ` and its helpers restated, `muAdjNotVRLM` withdrawn (with `MuAdjVRLME1`), the `gd` chain, the thaw (`InScope` never has to survive an instantiation there), the `U` rows. The stop rule separates listed statement changes from unplanned ones (§3.1, §3.6, §5). |
| The live-`U`-slot push is limited to `PushStable`, and `reconB′` is reshaped (major) | `PushStable` stays as 3b-i. 3b-ii targets `retryR`'s instances. The push's case at each former outside `PushStable` is an elaborating Prop (`PushArrStep`, refuted at `gd`; `PopUStep`; `PushEffStep`; `PushAllStep`), attempted unrestricted and under `MonoOwnGMCAt`. The arising route is recorded with what it lacks. The reshaping is dropped (§3.4, §3.5). |
| The consumers check is not a real check (major) | Step 1 is an inventory of every use site, with each mapped. Statement 4 gets its own entry (`AllRMonoM0` over `ovalWM`, now with four halves, §8.2). Every row without a `vRLM` proof is marked [unchecked: no row proof at vRLM], and the final claim carries that caveat. The sequencing rules are moved to the `MonoExtM` row (§4.2). |
| The failure is stated only for cells exactly at `β` (minor) | `PairCallbackGuardFailsLe` covers any two cells no longer-lived than the outermost lend. `PairArgCellsLe` is optional and [unchecked]. "Real" is claimed for 6.175's route; the two cover every argument at the identity instantiation only (§1.2, §8.2). |
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

### 8.2 The second review

| finding | the change |
|---|---|
| Link (d) reads the guard at the wrong stacks at `pairCbC` (major) | §1.2 now says where a callback's clause reads its argument's guard: at every instantiation the callback's own `U` clause offers (`RelendJ`), then at every instance below the bound and every own push (`CbReading`); at `withload`'s thunked type, also at every instantiation the answer's `U` clause offers. The review named the answer's clause. The callback's own clause instantiates too, at both types, and it is quantified as well. The gate is posed at `withloadU`'s type (`pairCbUC`, which is `cbUTy` at the empty row, for the same term `withload`), where the `⊸` is directly under the `∀`, and its (d), `PairGuardRejectsU`, ranges over every `CbReading`. At that type 6.175's route is rejected at every reading, because the instance is chosen after the instantiation (`PairBoundBelow` at the instantiated reading). The thunked form has its own statement with both quantifiers (`PairGuardRejectsF`, `WithloadPairGapInst`). It is decided and is not a gate, and its expected refutation is recorded [unchecked]. The docstring sentence and the "two stacks" claim are removed. 1a′ follows the same split (`WithloadUPairGapNilE1`, `WithloadPairGapNilInstE1`). `rfl` checks in the scratch file confirm the two shapes (§1.2, §1.3, §1.4, §1.5). |
| `AllRMonoM0` lacks the instantiation that the callback's `U` introduction applies, and hiding (major) | `AllRMonoM0` has four halves: `AllRExtM0`, `AllROwnM0`, `AllRThawM0` (the thaw through the intersection) and `AllRHideM0`. `RelendJInter` states the step the thaw half needs at a slot that holds resource; at `retryR`'s `!U` slot the resource is empty and the split is forced. "These are what `retryR` crosses" is replaced by the four index changes, read off DESIGN §9.2 and checked by Step 3's table. Each transport row of the table names its `ovalWM`-slot half. "What may be claimed" lists the open halves. The context thaw at a value-type context stays out of the non-monotonicity list: it is proved, and at a row-polymorphic slot it is `AllRThawM0` (§4.2, §3.5). |
| The inventory's search covers only some files (minor) | The search runs over every `*.lean` and `*.md` file of the probe, this file excepted. A second table marks each non-consumer hit by file and line as a definition, a proof, an implication or prose (§4.2 Step 1). |
| `SliceGapReal` (now `SliceUGapReal`) does not tie the array's cells and the frames' world to `c` (minor) | `SliceFrames` ties the array's owned cells at `ℓ` and `ℓ + 1` (`ρa.get`) to the cells the frames take, the frames' world to `c.fρ`, `ps'` to the two frames' records in front of `c.ps`, and `ls'` to them in front of `c.ls` (§1.3). |
| "Real" rests on the `reb_β` route, and the callback-time world's standard is unnamed (minor) | §1.5 says 6.175's route alone triggers 1b, and why that is enough: the design follows the printed proof, which reborrows at the instance it picks and applies the callback there. §1.2 records how far other arguments are covered. `PairArgCellsLe` with `PairCallbackGuardFailsLe` covers every argument at the identity instantiation only. At a reading that moves the lend below the cells, the table can hold, and the instantiated list is not one the world is tagged at when the callback holds a view [unchecked]. §1.5 says the callback-time world meets `TW` and `Tagged` and is not shown in `ArisesI`. |
| Two callback shapes are treated as one (major) | The `.arr` shape is the unwinding forms' callback type (`cbUTy`), which the probe's rule set contains. So `CallbackExt*M`, `RetainedPayLoadImmRow`, `RetainedPaySliceRow` and `ViewAt` are about real constants, the unwinding ones, and the non-unwinding constants, whose callbacks are thunked, had no statement at their shape. `CallbackExtMutMF` and `CallbackExtImmMF` now state the own-push route at that shape, owed, in §3.1's table and §4.2's table. (E1)'s cost is qualified by shape and payload. `OwnPushM`'s docstring and (E4)'s rationale no longer rest on `ViewAt`: the rows take `e.T = T` themselves. In 1b, `ViewAtB` is read at the `.arr` shape only; at the thunked shape it is vacuous, and the cost is recorded. The docs step records that the mismatch predates this unit (§3.1, §4.2, §1.6, §5). |
| Link (d) is existential over the push (major) | `PairGuardRejectsU` is universal over every reading: every instantiation, every instance below the bound, every own push with every resource the callback holds, and the reborrow at that reading's lifetime. One existential `TW.reb` witness stays, so that (d) is not vacuous. `SliceGuardRejectsU` mirrors it (§1.3). |
| `WInsideCoreM` and `CoreInsideWM` are missing from §3.1's table (minor) | They are in the table, unchanged, and read only at `VAllFree` types. `PushArrStepC` carries `VAllFree A` and `CAllFree D` (§3.1, §3.4). |
| `OwnOKB.placeFree` is weaker than `OwnOKI`'s (minor) | It is disclosed as its own draft change, with its reason (a callback holding a copy of the view), its cost (more pushes to serve; row 4's route), row 4's route restated, and a fallback to the strict form (§1.6, §1.7). |
| Withdrawing `muAdjNotVRLM` loses a cited fact (minor) | The outcome, CHECKPOINT and `R1MONO.md` §8.1 record `muAdjNotVRLM` and the unrestricted `relMAgreesJ` as proved at `5210cf1`, citing the commit (intro, §3.1, §5). |

---

## 9. Outcome

The build is on `targets`, commits `4b7936b` to `6dcdf72` and the documentation commit after them.
The proofs are in:
- `NxGuard.lean` and `NxGuardPair.lean` (item 1a);
- `NxUnroll.lean` (item 2);
- `NxE1.lean` (step 3.0's checks and item 1a′);
- `NxAllI.lean` (§3.2, §3.3);
- `NxHide.lean` (item 4);
- for the corrections of 2026-10-08 (§10), `R1Box.lean`, `NxFloor.lean` and `NxRecon.lean`.

The statements are in `Nx.lean`. `NxCallback.lean`, `NxBlock.lean` and `NxBlockRows.lean` were not
created. `lake build ProbeD1` is clean. There is no `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`. Every theorem in the unit's files and in the edited
`R1*.lean` files was checked with `#print axioms`, and each set is within
`[propext, Classical.choice, Quot.sound]`. Nothing outside ProbeD1 changed, and no printed
definition changed.

**Edits to existing definitions and statements** (all in ProbeD1's draft):
- (E1)–(E4), as §3.1 (`40c35b5`), with every result in §3.1's table at its disposition.
- The persistence box (`55434c6`, §10.2): `BoxStep`, `PBox`, and `vRLM`'s `!` clause reading
  `PBox`. It is not one of §3.1's edits. It answers correction (i).
- Statement changes, each disclosed in its docstring:
  - `RelMAgreesJ` and its three helper equalities are restated at types with no lifetime `∀`
    ((E1)) and no persistent thunk (the box: `VBoxFree`, `CBoxFree`).
  - `muAdjNotVRLM` is withdrawn ((E1)), and `MuAdjVRLME1` is proved in its place.
  - `VRLMSubst` is restated at substitutions that substitute no thunk (the box). The unrolling
    substitutes a `μ`, so item 2's rows are unaffected.
  - `BangThunkFRowM` and `BangThunkVRowM` take `PersistentBoxed` (the box). So
    `Statement0UFullM .binder0` and `Statement0MBesideMono0` hold with the two `!U` rows at
    contexts the box carries.
  - `CtxExtendNamedMAt` carries `StackOK` beside §3.2's statement.
- Two results are recorded as proved at commit `5210cf1`, before the edits: `muAdjNotVRLM` (the
  adjacency closure is no `vRLM` value), and `relMAgreesJ` without `VAllFree` or `VBoxFree`.

### 9.1 Item 1a: the two-cell gap

- **Proved** (`NxGuard.lean`): `PairRebCells`, `PairCallbackGuardFails`,
  `PairCallbackGuardFailsLe`, `SliceCallbackGuardFails`, `PairBoundBelow` and
  `PairNilOldGuardHolds`.
- **Proved** (`NxGuardPair.lean`):
  - the configuration `pc`: `ArisesI.nil`, three allocations and the 6.64 lend (`pc_arises`);
  - the view (`ArisesVI.view`) and the index at it (`pairCfg`);
  - `PairWithloadUTyped` and `PairWithloadTyped`;
  - link (d) at every configuration of the pair's shape (`pairGuardRejectsU_of`), and at every
    configuration of a two-element slice's (`sliceGuardRejectsU_of`).
- **The gate: `WithloadUPairGapReal` is proved** (`withloadUPairGapReal`). The configuration
  arises, and the program is typed at `withloadU`'s type. One own push has a closed payload type,
  and [TR] 6.150's `TW.reb` reborrows at its lifetime into a tagged typed world. At every reading
  the callback's clause offers, the reborrowed pair fails the guard.
- **The thunked form: `WithloadPairGapInst` is refuted** (`not_withloadPairGapInst`). At the gate's
  configuration, the answer's `U` clause instantiates the lend below the reborrowed cells. There
  they are related at `Imm '1 1 ⊗ Imm '1 1` and meet the table. It is not shown that a row can
  use that reading.
- **Not built:** `SliceUGapReal` (the array's frames, `SliceFrames`), `SliceTyped`, `SliceUTyped`,
  and the optional `PairArgCellsLe`. `SliceGapInst` was not stated.
- **What it means.** `withload` of a pair of references is a borrow-only program. Under correction
  (i) (§10), a borrow-only program that the draft does not cover is a defect of the draft. It is
  never a restriction or a cost.
  - Here the defect is in the draft's stack entry. The pushed entry lends one place, and the table
    puts a borrow cell at a place no entry lends strictly above the outermost lend. So one of the
    two reborrowed cells always fails (`loadGuardFails2`).
  - Item 1b's block is the designed fix (§1.6). It is not built (§9.6).

### 9.2 Item 2: `VRLMUnroll`, proved

- `VRLMSome`, `VRLMRename`, `VRLMSubst` and `VRLMInst` are proved (`vRLMSome`, `vRLMRename`,
  `vRLMSubst`, `vRLMInst`). This is `Core/RelMu.lean`'s route at W's clauses.
- `VRLMUnroll` is proved (`vRLMUnroll`): `vRLM_roll` one way, and the least fixed point at the body
  the other.
- `RollRowM` and `UnrollRowM` are proved at every placement (`rollRowM`, `unrollRowM`), and
  re-proved at `StackJM` after (E3).

### 9.3 Step 3.0

- **(E1)–(E4) landed** (`40c35b5`). Re-proved: `all_ownM`, `callbackExt*M_own` and their
  instances, the `U` rows at `StackJM`, `allIRowMNKAt0_of`, `gdRowRefutation`, `rollRowM` and
  `unrollRowM`. Everything else rebuilt unchanged.
- **`MuAdjVRLME1`: proved** (`muAdjVRLME1`). After (E1), the adjacency closure is a `vRLM` value at
  W's own `μ`.
- **Item 1a re-checked** (`pairGate_afterEdits`). The gate's push meets `OwnPushM`, its index meets
  `StackJM`, and after (E1) the callback's first conjunct reads no instance at `pc`'s index at any
  instantiation.
- **Item 1a′.**
  - `WithloadUPairGapNilE1` is proved (`withloadUPairGapNilE1`). At the gate's world at the empty
    stack, after (E1), no instance in scope is below `⊓Δ`, and every own push fails the guard at
    the reborrowed pair.
  - `WithloadPairGapNilInstE1` is refuted (`not_withloadPairGapNilInstE1`). At the thunked type,
    the answer's `U` clause moves the push below the reborrowed cells.
  - Before (E1) there was no gap at `[]` (`pairNilOldGuardHolds`).
  - `SliceUGapNilE1` and `SliceGapNilInstE1` were not stated.
  - Under correction (i), this is §9.1's defect, showing at the empty stack once (E1) removed the
    readings that hid it there (§10.2).
- **`CallbackExtMutMF` and `CallbackExtImmMF`: stated, not built.** `InScopeOfInterp` is stated and
  not proved; no built proof reads it.

### 9.4 Item 3: the `∀I` row's open cases

- **§3.2, the binder-named index: proved.**
  - `SubOutsideExtendNamed` (`subOutsideExtendNamed`), from `StackJM`'s `SubFresh`.
  - The row at one context from its transports (`allIRowMAt0_of`).
  - `CtxExtendNamedMAt` at contexts reaching no `U` (`ctxExtendNamedMAt_uFree`).
  - **Target (3a): the `∀I` row at every context whose live slots reach no `U`, at every index,
    the binder-named index included** (`allIRowMUFree0`). This closes the R1 unit's second open case
    (`not_subOutsideExtendAny`'s index) at those contexts.
- **§3.3, the reading transports at a live `U` slot: not derived.**
  - `VRLMReadEquiv`'s planned route does not pass the `F_Σ` clause. There the continuation of a stop
    is owed at a re-lend of the stack, and `ReadEquiv`'s in-scope conjunct is not kept along a
    re-lend (`not_readEquivRelend`). This is a fact about our `ReadEquiv`, at a configuration not
    shown to arise.
  - The route's other clauses were not built in Lean.
  - I have not derived `VRLMReadEquiv`, `CtxExtendMSAt`, `CtxShadowMSAt` or `CtxExtendNamedMSAt`,
    and have not verified that any obstruction to them is real.
- **§3.4, the push at a live `U` slot: not built.**
  - 3b-i (`MonoOwnGMAtPS`) is not built.
  - 3b-ii's steps (`PushArrStep`, `PushArrStepC`, `PopUStep`, `PushEffStep`, `PushAllStep`) and
    `MonoOwnGMCAt` are stated and not attempted. `not_pushArrStep` was not built, and
    `PushArrStep`'s docstring now says so. `PushedViewOutsideOldGuard` is stated and not proved.
  - 3b-ii's target was `retryR`, captured in `reconB′`'s callback. Written as the language writes
    it (correction (ii), §10.3), `reconB′`'s callback captures nothing.
- **§3.5's program check.**
  - `genSelf`'s callback captures nothing [read, §3.5].
  - `reconB′` is now built (`NxRecon.lean`, §10.3), and its callback is closed [read].
- **What may be claimed.** The `∀I` row holds at every context reaching no `U`, at every index. It
  may not be claimed that statement 0 at `binder0` reduces to the `∀I` row: §4.2's inventory is not
  written.

### 9.5 Item 4: `MonoHide` and the consumers

- **Proved:**
  - `HideInvisible` (`hideInvisible`);
  - `[handle]`'s transport where the handled name crosses no entry (`monoHideGMHandle0_noCross`,
    the first disjunct of `MonoHideGMHandle0`);
  - `AllRHideM0` where the hidden names cross no entry (`allRHideM0_noCross`);
  - `AllRExtM0` (`allRExtM0`);
  - `RelendJInter` at the empty resource (`relendJInter_empty`);
  - `AllRThawM0` at the empty resource (`allRThawM0Empty`, at `AllRThawM0Empty`, a statement added
    beside `AllRThawM0`).
- **Not attempted:**
  - `MonoHideGMHandle0`'s second disjunct (no live type carries the name);
  - `VRLMHideAvoid`;
  - `HideStopStep` (§4.1's bounded attempt was not made);
  - `MonoHideM` and `MonoHideGM` in general.
- **Not derived:** `AllROwnM0`; `AllRThawM0` at a slot holding resource (`RelendJInter` in
  general); `AllRMonoM0`; and `Statement0MAtConsumers0Full`.
- **The inventory and the table** (§4.2 Steps 1 and 3) were not written. So, by §4.2's rule, no
  document says what statement 0 at `binder0` reduces to.

### 9.6 Item 1b: not built

1a is real, so 1b's trigger is met. 1b was scheduled last (§5) and was not reached.
`NxBlock.lean`, `NxBlockRows.lean`, `StackOKB`, `OwnOKB`, `OwnPushB`, `ViewAtB`, `vRLMB`,
`PairGuardHoldsB`, `PVLStartB` and 1b's gate do not exist. 1b is the designed fix for the defect of
§9.1 and §9.3 (§10.2).

### 9.7 Report lists (§7)

- **Printed objects read.**
  - [TR] 6.150's `TW.reb`, the gate's reborrow (`pW₂_tw`).
  - [TR] p. 5's `reb_α` (`ResU.RebAt`, `pRebAt`).
  - [TR] 6.64's lend (`LendImmI`, `pLend`), with its H4 consequence.
  - Spec §19's `withloadU` and `cbUTy` (`pairCbUC`, `pairProgU_typed`), and `sliceBorrowIU`'s
    callback type (`sliceCbUC`).
  - [TR] 6.175's route is read as link (d): the reborrow at the reading's lifetime (§1.2).
  - Not read: `TW.rebEnd`, `wpG_reborrow`, `array_new` and `array_free`. The slice configuration
    was not built.
- **Printed hypotheses unspent.** None. The unit proves no printed lemma: every statement it proves
  is ProbeD1's own, about the draft relation, which no printed proof governs. The printed objects
  it reads are constructors (`TW.reb`, `LendImmI`), applied with every premise discharged.
- **Uniqueness and functionality results.** Used: `ResU.CompS.functional` (`NxGuardPair.lean`,
  `NxE1.lean`, `NxAllI.lean`, `NxHide.lean`). Not used: `CellU.CompS.functional` and `RebAt`'s piece
  disjointness. `RelendJInter` is proved only at the empty resource, where the split is forced. Its
  general case, where §7 expected the determinacy of `RelendJ`'s split to be read, is not derived.
- **Printed lemmas in the run-up that are untranscribed.** None found for items 1a–4. For item 1b
  (not built), the share's block re-lend is a forward obligation, not a printed lemma: GhostEnd's
  `openFS` reads strict re-lends.
- **Hypotheses added.**
  - (E1)–(E4), with §3.1's table.
  - (E4)'s `¬ VFree y T`, from `hfree₁`, at every borrow constant's typing rule.
  - `StackJM`'s payload avoidance, beside its `SubFresh`.
  - `StackOK` on `CtxExtendNamedMAt`.
  - The box's three: `VBoxFree`/`CBoxFree` on `RelMAgreesJ`; the no-thunk substitution on
    `VRLMSubst`; `PersistentBoxed` on the two `!U` rows. Each is non-vacuous:
    - `VBoxFree` holds at every type with no persistent thunk (`gdTy_free`, at `gd`'s type);
    - the no-thunk hypothesis holds at the unrolling's substitution (`vRLMInst`);
    - `PersistentBoxed` holds at every context of persistent thunks and persistent data reaching
      no `U`, the empty context among them.
- **The technique built.**
  - `VRLMSubst` is `vCE_subst`'s route at W's clauses.
  - `VRLMReadEquiv`, the symmetric invariance, was not built.
  - The box's world facts are new to ProbeD1 and follow no printed proof: `BoxIdx`, its transport
    along instantiations and pushes, and `pBox_world` through `instComp`.

---

## 10. The corrections of 2026-10-08

The user corrected the unit on 2026-10-08. The corrections, as given:
- **(i) Borrow-only programs are a sanity floor.**
  - Ordinary closures, higher-order functions and borrows without suspension are proved in Core
    (`fundamentalC` at `σ = []`). The draft relation must reproduce that.
  - A restriction found on a borrow-only program is a defect of the draft, most likely of (E1). It
    is never a sacrifice, and never a cost of a placement for OQ-8. The example given is
    push-monotonicity failing for a closed, persistent `!U` lifetime-polymorphic top-level
    function.
  - Persistent resource-free values must be monotone by construction. If (E1) breaks that, (E1) is
    fixed or reverted, and the outcome says which.
- **(ii) Test programs are written as the language writes them.**
  - `retry` is an effect handler installed around the borrow, and the callback performs
    operations. It captures no retry combinator.
  - `reconB′` is defined that way, and push-stability is judged against it.
  - Real restrictions arise only where a callback suspends while an inner lend is open (tier 2).

For borrow-only programs, they supersede every place where this file, DESIGN or `R1MONO.md` calls a
gap a "cost" or a "restriction". That includes:
- (E1)'s disclosed cost (§0, §3.1, and §5's stop rule);
- "real" in §1.2 and §1.5;
- `withload` and the slices "not covered at W" (`R1MONO.md` §8);
- DESIGN §6.3's outcome (c), where it would fall on a borrow-only program.

Each such gap is a defect of the draft, to be fixed. The corrections also supersede §3.5's program
check, and DESIGN §9.2's requirement that `retry`'s handler sit inside the first borrow.

### 10.1 What the draft lacked

- **The `!` clause.**
  - `vRLM`'s `!` clause added nothing to `A`'s: `!A` at `σ` was `A` at `σ` over the empty
    resource. At `A = U C`, `A`'s clause reads the thunk at every instantiation of the stack
    (`RelendJ`), but no clause read a persistent value after a push.
  - At `vRLJ`, the relation before (E1) and before the box, the persistent closure `!gdTy` over
    `gdF` is related at `gd`'s stack and not after the own lend's push (`gdBangJ`).
  - `gdTy` has no lifetime `∀` (`gdTy_free`), so (E1) plays no part there. Reverting (E1) would not
    make persistent values monotone by construction.
  - `gd` is not shown to arise, and `gdF` is no Core value. The fact is about the clause: it gave no
    persistent value a way across a push.
- **What (E1) does at the top level.**
  - At the empty stack and the empty reading no lifetime is in scope (`inScope_top_none`). So after
    (E1), the `∀` clause's first conjunct reads no instance there. A lifetime-polymorphic value made
    at the top level is checked by its own pushes alone.
  - Before (E1), the first conjunct read every instance below the bound.

### 10.2 The fix: the persistence box, with (E1) kept

**The box** (`R1.lean`, `55434c6`).
- `BoxStep δ ls` is an own push at the empty resource (`OwnOKI`). Its entry is under a reserved
  name (`NsVar`, a name no program binds), new to the reading, and its payload type does not read
  its own variable. It is pushed below `⊤` and fresh below the reading, with the records kept
  outside.
- `PBox A δ σ αs P` holds at a thunk type when `P` holds at every world `binder0`'s order reaches
  from the stack: every instantiation (`InstAt`), every list kept outside the instantiated
  lifetimes, and every finite sequence of `BoxStep`s from there. At every other type it is `True`.
- `vRLM`'s `!` clause is now `ρ = ∅`, the value at `A`, and `PBox` over the value at `A` at the
  empty resource.

**What it gives** (`R1Box.lean`, `NxFloor.lean`):
- the index facts along the box (`BoxIdx`, `boxIdx_inst`, `boxIdx_steps`, `stackJ_of_boxIdx`), and
  the box's transitivity (`boxSteps_inst`, and `pBox_world` through `instComp`);
- a persistent thunk at every box world, by construction (`persistentBoxWorld`), and across an own
  push under a reserved name (`persistentPushN`);
- a persistent context carried to every box world (`gRLM_boxWorld`) and across such a push
  (`monoOwnGMAtBoxN`): persistent thunks by the box, and persistent data reaching no `U` by the
  `U`-free push;
- the two `!U` rows, re-proved at the box (`bangThunkFRowM`, `bangThunkVRowM`, and so
  `statement0UFullM`). At every box world the thunk is the `U` row's conclusion, from the premise
  there, with the context carried there. The rows now take `PersistentBoxed`.

Re-proved with the box: `vRLM_mono_at`, `relendM_valueE`, `monoExtME_go`, `monoOwnUFree_go`,
`vRLM_reading_uFree`, `vRLM_some`, `vRLM_rename` and `vRLM_subst`.

**(E1) is kept, and the `!` clause is fixed.** The reasons:
- The defect was in the `!` clause, and it was there before (E1) (`gdBangJ`). The box fixes the
  clause.
- §3.3's route to the reading transports reads (E1) (§3.1). Without (E1), they were not derived
  (`R1MONO.md` §8).
- The borrow-only program found so far on which (E1) has an effect is `withload` of a pair at the
  empty stack (`withloadUPairGapNilE1`).
  - That is §9.1's two-cell defect. At a non-empty stack it shows with or without (E1)
    (`withloadUPairGapReal`, `pairGate_afterEdits`).
  - Before (E1), the first conjunct's readings at `[]` hid it there (`pairNilOldGuardHolds`).
  - One fix is designed to serve both: item 1b's block, which lends the payload's places together
    at the own push [unchecked: 1b is not built].
  - If 1b's gate fails, (E1) is revisited at the empty stack, as a defect of the draft.

**The box against DESIGN §12.2 (d).** The box makes the `!` clause reach stacks other than its own
by something other than `FutQ`: instantiations, and own pushes at the empty resource under reserved
names. `binder0`'s `U` and `∀` clauses already make those moves.
- The box was made to answer correction (i). Statement 0 does not yet hold, with the box or without
  it, so (d) has not occurred.
- If statement 0 comes to hold only with the box, DESIGN §12.2's reading of (d) applies to it, and
  the report must say so.

### 10.3 `reconB′` as the language writes it (`NxRecon.lean`)

- **The program** (`reconB'`):

      resumer wait (retry (lend tt (Λ. λb. x ← *b; wait (); y ← *b; y)));
      timeout (lend tt (Λ. λb. x ← *b; wait (); y ← *b; y))

  - `retry` handles `Fail` around the lend, and re-runs the attempt once on a raise. The callback,
    like DESIGN §9's, raises nothing, so the run does not exercise the re-run.
  - `resumer` resumes `wait`. `timeout` cancels it, and the cancel ends the lend's frame by its
    finaliser.
  - Each attempt lends a fresh cell holding `tt`.
  - The lend is `lendCell`'s, `withborU`'s term. It is read at `withbor` (1)'s type, an `Imm` lend
    (6.64), as DESIGN §9's term borrows `imm`. The term is the same at `withbor` (2)'s type [read].
- **Its run** (`reconB'_eval`): `(tt, ff)`, and no cell left. This is the interpreter's run, by
  `decide`.
- **Push-stability, judged against it.**
  - The callback `Λ. λb. …` is closed [read]. So its `∀I` row can be read at the empty context,
    where it holds at every index (`reconCb_allI`, from `allIRowMUFree0`).
  - The typing at the probe's rule set is not built. So it is [unchecked] that the derivation
    applies the row at a context with no live `U` slot.
  - `reconB′`'s handlers are installed around the lends, at the empty stack, where every hiding is
    invisible [read].
- **What it owes** is the suspension inside the lend, which is statements 1–3 (tier 2).
  - The callback performs `wait` while its lend is open. The scheduler resumes it, and `timeout`'s
    cancel ends the lend's frame by the finaliser.
  - The unwinding forms admit only abortive operations in the callback (`Row.Unwind`,
    `Core/EffBorrow.lean`), and `wait` is resumed.
- 3b-ii's target, `retryR` captured in the callback, does not occur in this program.

### 10.4 What the floor still owes

Each item below is either a statement not derived, with no obstruction verified, or not built.
Under correction (i), if one fails at a borrow-only program, that is a defect of the draft to fix,
not a restriction.
- **The `∀I` row's own push at a persistent context.**
  - The push is named by the type's binder, not by a reserved name, so the box does not reach it.
  - `VRLMStackRename` (`NxFloor.lean`) states that `vRLM` does not read the entry's name. With
    `persistentPushN`, it is meant to give the push [unchecked: not built].
  - `VRLMStackRename` is not derived.
- **The row's reading transports at a `!U` slot** (`CtxExtendMSAt`, `CtxShadowMSAt`): not derived.
  A box world's pushes may read a variable that the extended reading binds, so they must move with
  the reading too.
- **`PersistentBoxed`'s left-out case**: a persistent slot `!B` whose `B` reaches a `U` other than
  at its top, such as `!(U C ⊗ 1)`.
  - `PBox` reads only `!U C`.
  - The rules make `!` values only by `bangThunkF`, `bangThunkV` and host operations
    (`Core/Fundamental.lean`). So such a slot holds a host operation's value or a bound variable
    [read].
  - The fix to try is `PBox` at every `!B` that reaches a `U`. It was not attempted.
- **Linear closures across a push** (a `U` slot not under `!`).
  - `MonoOwnGMAtPS` (3b-i) is not built, and 3b-ii's steps were not attempted.
  - `gd` refutes the unrestricted `MonoOwnGM` at a configuration not shown to arise, whose closure
    is no Core value.
- **The floor's own statement** is that the draft relates, at `σ = []`, every program
  `fundamentalC` covers. It is not stated in this unit. The nearest statements are OQ-58's
  (`NilAgrees`, `NilAgreesU`, `NilSoundV`, `NilSoundC`; DESIGN §6.3), which were not attempted.
- **The two-cell defect** (`withload` of a pair, and the slices at two or more elements): item 1b,
  not built.

---

## Unresolved: the reviews' findings

The design reviews raised the four major findings below. §8.2 answered each in the text before the
build, and the answers were not reviewed again. Each entry gives the finding, the text's answer,
what the build did, and what stays open.

1. **§1.2(d): at `pairCbC` the guard is read through the answer's `U` clause and `RelendJ`'s
   instantiations.**
   - The text's answer (§8.2): the gate is posed at `withloadU`, where the `⊸` is directly under
     the `∀`. The thunked form has its own statement with both quantifiers.
   - The build:
     - The gate at `withloadU` is proved (`withloadUPairGapReal`).
     - At `pairCbC`, the thunked form is refuted at the gate's configuration
       (`not_withloadPairGapInst`): through the answer's instantiation, the reborrowed cells meet
       the table.
   - Open: at `withload`'s own type, the gap is not established at that configuration. It is not
     shown that a row can use the instantiated reading.
2. **`AllRMonoM0` lacks the thaw (instantiation) half and the hide half; `Statement34`'s
   transport.**
   - The text's answer (§8.2, `Nx.lean`): four halves (`AllRExtM0`, `AllROwnM0`, `AllRThawM0`,
     `AllRHideM0`), with `RelendJInter`.
   - The build:
     - `allRExtM0`;
     - the thaw half at the empty resource (`allRThawM0Empty`);
     - the hide half where the hidden names cross no entry (`allRHideM0_noCross`).
   - Open:
     - `AllROwnM0`;
     - the thaw half at a slot holding resource (`RelendJInter`);
     - the hide half's general case;
     - `AllRMonoM0`, and its use as `Statement34`'s transport.
   - Since §10.3, `reconB′`'s callback does not capture `retryR`, so `reconB′` does not read
     `AllRMonoM0` at its callback [read; the typing is not built]. Statement 4 still states it.
3. **Two callback shapes treated as one.** The two shapes are the unwinding forms' `cbUTy`,
   `.all y c (.arr …)`, and the non-unwinding constants' thunked `∀'x ⊏ c. F (U (A ⊸ …))`.
   `CallbackExt*M`, `OwnPushI`'s `ViewAt` and 1b's `ViewAtB` are at the `.arr` shape.
   - The text's answer (§3.1, §8.2): `CallbackExtMutMF` and `CallbackExtImmMF`, at the thunked
     shape.
   - The build: both are stated, and neither is proved. `ViewAtB` is not built.
   - The mismatch predates this unit. It sits in `BINDER.md:1920`, in `R1.lean`'s
     `CallbackExtMutM`, `CallbackExtImmM`, `RetainedPayLoadImmRow` and `RetainedPaySliceRow`, and in
     `Binder.lean`'s `ViewAt`.
   - Open: the non-unwinding constants' own-push route has no proved statement at their shape.
4. **The guard link is existential where it must be universal** (`PairGuardRejects` over pushes).
   - The text's answer (§8.2): `PairGuardRejectsU` is universal over every reading. That covers
     every instantiation, every instance below the bound, and every own push with every resource
     the callback holds. One existential `TW.reb` witness is kept, so that (d) is not vacuous.
   - The build:
     - `pairGuardRejectsU_of` proves it at every configuration of the pair's shape, and
       `withloadUPairGapReal` carries it.
     - `sliceGuardRejectsU_of` mirrors it at a two-element slice, whose gate (`SliceUGapReal`) is
       not built.
   - Open: the slice gate.
