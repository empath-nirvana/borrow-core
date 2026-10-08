# ProbeD1: the grounding ledger

This file sets every ProbeD1 definition that has a Core counterpart against that counterpart, says
how the two relate, and names the Lean theorem behind each claim. `GROUND.md` is the design (§2 the
ledger, §3 the suite). The theorems are in `ProbeD1/GroundLedger.lean`; the regression suite is
in `ProbeD1/GroundRegress.lean` and its results are in the second half of this file.

**Conventions.**
- **The two sides.** The draft is the one draft relation `vRLM`/`cRLM`/`effRetM`/`gRLM`/`SemSM` at
  `.binder0` (`R1.lean:150–252`). Core is `vCE`/`cC`/`effRet`/`gDenC`/`SemC`
  (`Core/Relation.lean:119–231`).
- **Where they are compared.** At the empty stack (`σ = []`, `αs = []`, where `extS δ [] [] = δ`
  by definition) and, separately, at a non-empty stack. "Same clause" means the two clauses have one
  shape once their sub-relations are identified.
- **Direction.** "Draft ⊆ Core" means the draft's predicate implies Core's: the draft relates
  fewer. "Core ⊆ draft" is the converse. "Equal" means both. "Incomparable" means each adds an
  obligation the other lacks. "Not stated" means no statement relates them.
- **No overclaim.** A row says "equal", "agrees" or gives a direction only where a named theorem
  proves it. A relationship argued without a theorem is marked [read] or [unchecked]; a statement
  with no proof is marked *stated*.
- **Paths.** Draft lines are under `experiments/ProbeD1/ProbeD1/`, Core's under `Core/`, GhostEnd's
  under `experiments/GhostEnd/GhostEnd/`, and Targets' under `experiments/Targets/Targets/`, unless
  a row names the file in full. "GL" is `GroundLedger.lean`.

---

## 1. What the grounding theorems prove

All are in `GroundLedger.lean`, proved, with `#print axioms` within
`[propext, Classical.choice, Quot.sound]`.

| # | statement | theorem (GL line) | what it says |
|---|---|---|---|
| G1 | `VRLMFlat` | `vRLMFlat` (:203), from `vRLM_flatE` (:113) | at a flat type (`FlatB`: Core's `DataB` with `Unk`, opaque, `[@a]`, `Ref`, a persistent non-thunk and `[L]`) the draft value relation **is** Core's, at every stack and every reading, under an environment that is Core's (`EnvCore`) |
| G2 | `VRLMFOArg` | `vRLMFOArg` (:239), `vRLM_foArg` (:216) | at a first-order argument (`FOArg`: flat, `Mut`, `Imm`, and `⊗`, `⊕`, `[@a]`, `Ref`, `[L]` of these) the draft value relation is **inside** Core's, at every stack |
| C14 | `GRLMOfSlots` | `gRLMOfSlots` (:285) | the context relation is Core's given its slots' clauses, and inside Core's given containment |
| G4 | `CoreSubWComp` | `coreSubWComp` (:342) | at a first-order computation type (`FOComp`: `F` of a flat type, `⊸` from a first-order argument, `&`, `⊤`, `ν`) Core's computation relation is **inside** the draft's, at every stack. The step is `cRLM_arr_binder0` (:311): `binder0` reads no future and no record extension at `⊸`, and the guard only adds hypotheses |
| G5 | `CoreToSemSM` | `coreToSemSM` (:364) | **at a first-order judgement (`CtxFO Γ`, `FOComp (jdgCty j)`), Core's derivation gives the draft's semantic judgement at every index** (`fundamentalC`, then G2 at the context and G4 at the conclusion). No instantiation is read |
| — | `GRestrict` | `gRestrict` (:394) | G2 is `WInsideCoreM` restricted to first-order arguments, and G1 both agreement statements restricted to flat types, the index hypotheses unused |
| G5v | `CoreValToW` | `coreValToW` (:510) | a closed value Core relates at every reading at the empty resource, at a thunk or persistent thunk of a first-order computation type (`FOConstTy`), is the draft's at every index |
| G5c | `CoreToSemSMConst` | `coreToSemSMConst` (:544) | a syntactic value Core derives at a dead context (`Ctx.Dead`, no live slot) at a first-order constant type is the draft's at every index. The value's relation at each reading comes from `wpTS` at the empty frame (`post_of_wpTS_val_empty`, :427); the `U` clause reads it at each instantiated reading (`thunk_W_of_core`, :480), the box at each box world (`boxIdx_steps`) |
| G3 | `VRLMNilTy` | `vRLMNilTy` (:856) | at the empty stack, at `NilTy` (flat, `Mut`, `Imm` and their products, sums, boxes, `Ref`s and families) the draft relation is Core's: `CohS` and `RetainedPay` hold at `[]` (`cohS_nil`, `retainedPay_nil`) |
| G4′ | `CoreSubWNil` | `coreSubWNil` (:889) | at the empty stack Core inside the draft at `NilVal`/`NilComp` types, **thunks included, for every semantic value**: `[]` has only the identity instantiation (`vRLM_thunk_nil_iff`) |
| G5′ | `CoreToSemSMNil` | `coreToSemSMNil` (:946) | the floor at the empty stack at `NilComp` judgements over `CtxNil` contexts, constants included |
| G6 | `SemSMNil`, `SemSMNilOfSemSM`, `DraftFL`, `DraftFLNil` | `semSMNilOfSemSM` (:923); the floor statements (:930, :935) *stated* | `SemSM` gives `SemSMNil`; the floor at every index and at `[]` is stated, not claimed |
| G7 | `GuardPVNil`, `RelendJNil`, `VRLMThunkNil`, `CRLMArrNil`, `CRLMAllNil`, `CRLMAllTop`, `CRLMRetNil`, `SemIdxMNil`, `VRLMBangNil`, `KeepsTKeeps` | `guardPVNil` (:582), `relendJNil` (:614), `vRLMThunkNil` (:630), `cRLMArrNil` (:644), `cRLMAllNil` (:687), `cRLMAllTop` (:703), `cRLMRetNil` (:736), `semIdxMNil` (:958), `vRLMBangNil` (:977), `keepsTKeeps` (:992) | the empty-stack unfoldings; `CRLMRetNil` is both directions at a flat answer at every row |
| G7′ | `VRLMLeafDefault`, `CRLMTopNuEq`, `CRLMAmpOfComp`, `EffRetMOfAns`, `CRLMRetFlat` | `vRLMLeafDefault` (:1007), `cRLMTopNuEq` (:1017), `cRLMAmpOfComp` (:1026), `effRetMOfAns` (:727), `cRLMRetFlat` (:760) | the clause unfoldings at every stack |
| G8 | `ArisesITW`, `ArisesINilOfTW` | `arisesITW` (:1039), `arisesINilOfTW` (:1081) | the revised arising set's worlds are tagged `TW` worlds; every tagged `TW` world arises at the empty stack |
| G9 | `ProbeRulesOfNU` | `probeRulesOfNU` (:1089) | every `CDerivesNU` program is a `ProbeRules` program |
| G10 | `AdequacyNilM` | `adequacyNilM` (:1101) | the draft's judgement at the empty stack at `F 1` gives Core's adequacy (`theorem32D`) |
| G11 | `NotTabOfTWPointwise`, `ArisesIArises` | `notTabOfTWPointwise` (:1119), `arisesIArises` (:1147) | the pointwise table fails at `innerView`; the revised arising set is inside the first |
| G12 | `DraftFLEmbed` | *stated* (:1192), not attempted | the floor at BoLo's image |

**The classes are non-vacuous at the suite's types**: `FlatTy` holds at `1`, `I32`, `Ref 1`,
`Ref I32`, `L` and the other data lists; `FOArg` at every `Mut 'x T` and `Imm 'x T`, at
`Imm 'x 1 ⊗ Imm 'x 1`, at `array_imm 'z I32`; `FOComp` at every callback body `A ⊸ F B` with those
arguments and a flat answer. The entries that read them are in §10.

---

## 2. Rows: the relation's clauses

All draft lines are `R1.lean`; all Core lines are `Core/Relation.lean` unless named.

| # | draft | Core | at `σ = []` | at `σ ≠ []` | theorem | what a disagreement means for programs |
|---|---|---|---|---|---|---|
| C0 | `WInsideCoreM`, `CoreInsideWM` (:849, :856) | `vC` at `extS δ σ αs` | at first-order arguments W ⊆ Core (G2); at flat types equal (G1); at `NilTy` equal (G3) | at first-order arguments W ⊆ Core (G2), at flat types equal (G1); in general *stated*, not attempted | `gRestrict` (GL:394), `vRLMFOArg`, `vRLMFlat`, `vRLMNilTy` | a consumer that hands a draft value to Core's clause, or reads Core's answer back, is covered only at first-order and flat types. At `U C` `CoreInsideWM` would read the `U` clause at instantiated readings, where Core's relation of a value known at one reading is not given [read] |
| C1 | `vRLM` `U` (:152) | `vCE` `U` (:127) | Core ⊆ draft given bodies, for every semantic value: the draft reads the body at every extension that keeps the tags (`KeepsT`), Core's at every extension (`vRLM_thunk_nil_iff`, GL:623); so Core ⊆ draft at `NilComp` bodies (`coreSubWNil`) | incomparable [read]: instantiations at the stack's cut, views handed back, `guardPV`. For a closed first-order value Core relates at every reading, Core ⊆ draft (`coreValToW`) | `vRLMThunkNil`, `coreSubWNil`, `coreValToW`, `coreToSemSMConst` | at `[]` every Core thunk with a `NilComp` body is a draft thunk; at a stack, first-order constants and first-order callbacks are covered (G5c, the producer lemmas, §10) |
| C2 | `vRLM` `⊗`, `⊕`, `[@a]`, `Ref`, `[L]` (:159, :161, :166, :168, :183) | :121, :124, :131, :132, :149 | same clause | same clause, leaves at `extS δ σ αs` | equal at flat components (`vRLM_flatE`); inside Core's at first-order components (`vRLM_foArg`) | none |
| C3 | `vRLM` `!` (:164) | :130 | draft ⊆ Core given the payload (`PBox` added at a thunk payload); equal at a flat non-thunk payload (`vRLM_flatE`'s `bang` case); at a thunk payload the box is every box sequence from `([], [])` (`vRLMBangNil`) | the same | `vRLM_flatE`, `vRLMBangNil` (GL:977) | a persistent thunk must hold at every box world (D4). For a first-order persistent value Core derives at a dead context, it does (G5c) |
| C4 | `vRLM` `Mut`, `Imm` (:170, :174) | :137, :134 | equal (`vRLM_nilTy`'s leaf cases: `CohS` and `RetainedPay` hold at `[]`) | draft ⊆ Core: Core's leaf, plus `CohS` and `RetainedPay` (`vRLM_foArg`'s leaf cases) | `vRLMNilTy` (GL:856), `vRLMFOArg` (GL:239) | a consumer at a pushed stack must establish `CohS` and `RetainedPay` for the leaves it hands over (D7) |
| C5 | `vRLM` type variable (:178), environment `WEnt` (:72) | :143, `TEnt` (:72) | candidates; W's drop the mode and the list | the same | `EnvCore` (:1363), read by `vRLM_flatE` | none at flat types |
| C6 | `vRLM` `μ` (:179) | :144 | equal at flat bodies (`vRLM_flatE`, the induction with two least fixed points); with a thunk inside, *not stated* | the same | `vRLMFlat` | W reads a thunk inside `μ` with its own `U`; after (E1) the adjacency closure is a draft value (`muAdjVRLME1`, `NxE1.lean:74`) |
| C7 | `vRLM` default: `1`, `0`, `Unk`, `int`, `opq` (:186) | :120, :123, :140–142 | equal | equal at `extS` | `vRLMLeafDefault` (GL:1007, `rfl` at each type) | none |
| C8 | `cRLM` `F` (:192) | `cC` `F` (:155) | same clause (`wpTS`); equal at a flat answer | equal at a flat answer | `cRLMRetFlat` (GL:760), `cRLMRetNil` (GL:736) | none at flat answers |
| C9 | `cRLM` `F_Σ` (:193) | `cC` `F_Σ` (:165) | equal at a flat answer at every row (`bodyS_nil_iff`, `GhostEnd/Stacked.lean:476`) | GhostEnd's piece (a stop ghost-ends entries): no Core counterpart | `cRLMRetNil` (GL:736) | effectful callbacks at a pushed stack read the piece (out of this suite, §10.7); see D12 for blocks |
| C10 | `cRLM` `⊸` (:201) | `cC` `⊸` (:156) | same clause, guard trivial | same clause plus `guardPV` at the stack | `cRLMArrNil` (GL:644), `cRLM_arr_binder0` (GL:311), `guardPVNil` (GL:582) | a call at a stack needs the table and views of the composite (D9) |
| C11 | `cRLM` `&`, `⊤`, `ν` (:206, :209, :220) | :158, :160, :163 | `⊤` and `ν` equal (`ν` is Core's clause at `extS`); `&` the same clause given its components | the same | `cRLMTopNuEq` (GL:1017, `rfl`), `cRLMAmpOfComp` (GL:1026) | none |
| C12 | `cRLM` `∀` (:210) | `cC` `∀` (:161) | incomparable [read]: the first conjunct reads only instances in scope ((E1), `InScope`, :95), and the own-lend conjunct (`OwnPushM`, :101) has no Core counterpart; at the top level the first conjunct reads nothing | the same | `cRLMAllNil` (GL:687) and `cRLMAllTop` (GL:703) unfold the clause; `cRLM_all_binder0` (GL:652) at every stack. Core's `∀` alone: holds at a `mut` cell adjacent to `⊤` and fails at one at `2` (`coreAllAdjacent`, `GapWitness.lean:127`), not invariant under an embedding that opens the room (`coreAllNotNatural`, :150), does not imply reading (A) at `σ = []` (`not_coreAllImpCutAll`, :156) | every borrow callback is checked at its own push: the producer side is covered for first-order callbacks (G5 with the rows, §10); the consumer side is each borrow constant's row (D1, D2) |
| C13 | `effRetM` (:223) | `effRet` (:176) | equal given the answer's clause | the same, at `extS` | `effRetMOfAns` (GL:727) | none |
| C14 | `gSepRLM`, `gRLM` (:231, :240) | `gSepC`, `gDenC` (:218, :224) | equal given the live slots' clauses; contained given containment | the same, at `extS` | `gRLMOfSlots` (GL:285) | none |
| C15 | `SemSM` (:246) | `SemC` (:228), `SemJ` (`Fundamental.lean:429`) | incomparable as definitions: `SemSM` adds `BindersLow`, `Scoped`, `SubDom` and the index [read]; at `[]` the index holds of every reading (`semSMNilOfSemSM`) | the same | `coreToSemSM` (GL:364), `coreToSemSMNil` (GL:946), `semSMNilOfSemSM` (GL:923) | Core's judgements at first-order types are the draft's at every index |

---

## 3. Rows: world, index, guard

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| W1 | `Stk`, `LEnt`, `LStack` (`World.lean:53`; `GhostEnd/Stacked.lean:99`, :107) | none: Core is `σ = []` | draft-only (§7) | — | — |
| W2 | `guardPV` (`Binder.lean:164`), `TabAtS` (`GhostEnd/Stacked.lean:290`), `PlaceViewsL` (`Binder.lean:144`) | `TW` read pointwise (`TabOfTWPointwise`, `HeldUnderTW`, `Statement1.lean:125`, :119); `TW`'s run invariant (statement 1's facts, `Statement1.lean:43–100`) | trivial at `[]`. Pointwise, the table is not read off one `TW` world: `TabOfTWPointwise` fails at `innerView`, a `TW` world, at a configuration not in `Arises` (`wpG_below_not_arises`): a fact about the pointwise statement. As a run invariant, `TabRelend` is proved (`tabRelend`, `Thunk.lean:185`) and the other eight facts are stated | `guardPVNil` (GL:582); `notTabOfTWPointwise` (GL:1119) | at a stack the guard restricts every call (D9); a guard proved only pointwise from `TW` is not available |
| W3 | `CohS` (`Binder.lean:178`) | `CohE` (:57) | different objects: a view tied to its lending entry, an `imm` cell tied to a record; `CohS` holds of everything at `[]` | `cohS_nil` (GL:803) | D7 |
| W4 | `OwnPushM`, `OwnOKI` (`R1.lean:101`, `Binder.lean:194`, :200) | Core's `∀` instance (:161); 6.64/6.65's lend start (`TW.immFrame`, `TW.mutFold`, `World.lean:115`, :135) | *not stated*: the own push reads an instance as a lend | — | the single-place entry (D2) and `placeFree` (D3) |
| W5 | `Inst`, `InstAt`, `RelendJ` (`Binder.lean:314`, :346; `BinderJ.lean:53`) | Core's `U` quantifier over `Ext` (:127) | at `[]` `RelendJ` is Core's `U` with `KeepsT` added | `relendJNil` (GL:614) | D8 |
| W6 | `KeepsT` (`BinderJ.lean:49`) | `Keeps` (`FrameRecords.lean:156`) | draft ⊆ Core: a record kept with its tag is kept | `keepsTKeeps` (GL:992) | D8 |
| W7 | `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `OuterBelowTop`, `cutOf` (`Binder.lean:250`, :280, :285, :265, :242, :227) | [TR] 6.64/6.65 H4's fresh lifetime; nearest Core object `TW.reb`'s `StratumLe` (`World.lean:92`, :122) | draft-only bookkeeping (§7); each holds of every reading at `[]` (`subOutside_nil`, and `RecsOutside []`, `OuterBelowTop []` vacuous) | `semIdxMNil` (GL:958) | — |
| W8 | `PBox`, `BoxStep` (`R1.lean:132`, :120) | none: Core's `!` is `ρ = ∅ ∧ vC true A` | draft-only (§7) | `vRLMBangNil` (GL:977) unfolds it at `[]` | D4, D5 |
| W9 | `StackJM`, `BindersLow`, `Scoped`, `SubDom` (`R1.lean:108`; `Sem.lean:66`, :74, :78) | `Scoped` ↔ `VScoped`; `Δ.Models` | `Scoped` is `VScoped` at the judgement [read]; the others draft-only; `StackJM` holds at `[]` | `stackJM_nil` (GL:914) | a judgement binding a reserved name (`NsVar`) is outside `SemSM` (vacuous there) |
| W10 | `vwEW`, `vwSW`, `vwSL` (`Binder.lean:121`, :125, :159) over GhostEnd's `vwE` (`Stacked.lean:122`) | `ptoImmS`, `ptoMutS` (:51, :43) | the views read an `imm` payload at `vC true`, Core's `Imm` leaf at `vC false` [read] | — | at a payload holding a thunk the views ask more (D11) |
| W11 | `WP p` (`Sem.lean:119`) | `Targets.coreW` (`Targets/I/World.lean:165`) | stale: it reads statement 0's relation `vRL`, not `vRLM` [read] | — | nothing in this unit reads `WP` |
| W12 | `SemIdxM` (`R1.lean:946`) | `SemC`'s hypotheses: `Δ.Models δ` and `gDenC` | at `[]` it is `BindersLow`, `Scoped`, `SubDom` and `Δ.Models δ` | `semIdxMNil` (GL:958) | `PairCfg`, `SliceCfg` and the `RetainedPay*Row` rows read it |
| W13 | `SemSMC`, `gRLMC`, `gSepRLMC` (`R1.lean:803`, :795, :784) | `SemC`, `gDenC`, `gSepC` | incomparable with `SemSM` as definitions [read] | none | a route device (`MonoOwnGMC`, `AllIRowMC`); no entry reads it |

---

## 4. Rows: arising against the typed world

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| A1 | `ArisesI` (`Binder.lean:582`) | `TW` (`World.lean:110`), `Tagged` (:171) | every arising world is a tagged `TW` world (draft ⊆ Core, worlds); at `[]` every tagged `TW` world arises (Core ⊆ draft); so at `[]` the world sets coincide | `arisesITW` (GL:1039), `arisesINilOfTW` (GL:1081) | a refutation at `[]` needs nothing beyond Core's arising |
| A2 | `ArisesI.lendImm`, `LendImmI` (`Arising.lean:106`; `Binder.lean:576`) | `TW.immFrame` (`World.lean:115`) | `LendImm` carries `TW.immFrame`'s premises, the push, and H4's freshness | inside `arisesITW` (the `lendImm` case is `TW.immFrame`) | — |
| A3 | `ArisesI.lendMut`, `LendMutI` (`Arising.lean:88`; `Binder.lean:571`) | `TW.mutFold` (`World.lean:135`) | the same | inside `arisesITW` (the `lendMut` case is `TW.mutFold`) | — |
| A4 | `RunEnd` (`Arising.lean:73`) | `wpTS`'s run conjuncts (`World.lean:186`) | `RunEnd` transcribes them at a fixed configuration [read] | — (`RunEndOfWpTS` not built) | — |
| A5 | (none) | `TW.immEnd`, `TW.mutUnfold` (`World.lean:151`, :140) | *not stated*: `ArisesI` has no lend-end transition | — | configurations after a lend ends are reached only through `run` |
| A6 | (no transition) | `TW.reb`, `rebDeep`, `rebEnd`, `rebEndDeep` (`World.lean:122`, :128, :157, :162); `wpG_reborrow` (`Reborrow.lean:232`) | *not stated*: `ArisesI` has no reborrow transition. The gate's witness uses `TW.reb` inside a world (`withloadUPairGapReal`). Statement 2 transcribes 6.150 (`rebView`, `rebF`, `RebRelend`, `RCarried`, `TabKeepsRec`, `RebFrameR`, `RebChooserNonVacuous`, `Statement2.lean:67–130`): stated, none proved | — | a configuration inside `withload`'s callback with its push on the stack is not in `ArisesI`; a refutation there cannot pass DESIGN §11 |
| A7 | `ArisesVI` (`Binder.lean:598`) | none: Core quantifies over all values in `TW` worlds | draft-only (refutation check) | — | at `[]` no `Imm` value arises except a run's answer, so a refutation at `[]` of an open judgement with a borrow-typed context cannot pass DESIGN §11 |
| A8 | `Arises`, `ArisesV`, `ArisesCtx` (`Arising.lean:134`, :158, :175); `ArisesAt` (:53); `ArisesNonVacuous` (:186) | `TW`, `Tagged` | the first arising set; `ArisesI ⊆ Arises` and `ArisesVI ⊆ ArisesV` | `arisesIArises` (GL:1147) | none: refutations read `ArisesI` |
| A9 | `ArisesSound` (`Statement1.lean:112`) | `TW` (through `ArisesAt`) | *stated*, not proved; used only to exclude a witness | — | none |

---

## 5. Rows: judgement, typing, statement 0, adequacy

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| J1 | `ProbeRules` (`Rules.lean:31`) | `CDerives` (`Fundamental.lean:60`); `CDerivesNU` (`Targets/Base/Typing.lean:82`) | `CDerivesNU` ⊆ `ProbeRules`; `CDerivesNU` ⊆ `CDerives` (`CDerivesNU.toCDerives`); `ProbeRules` ⊄ `CDerives` (the spanning rules) [read] | `probeRulesOfNU` (GL:1089) | a Core program whose derivation uses no effect rule is built by the same constructors as a `CDerivesNU` one [read], but no theorem converts it, since nothing inverts `CDerives` |
| J2 | statement 0 (`Statement0M`, `R1.lean:1444`; `statement0MBesideMono0`, `R1Stmt0.lean:447`) and the draft rows | `fundamentalC` (`Fundamental.lean:434`) | the draft has rows at `force`, `thunkF`, `thunkV`, the two `!U` rows (with `PersistentBoxed`), `∀I` (contexts reaching no `U`), `roll`, `unroll`; Core proves all 89 constructors. At first-order judgements Core's derivation gives the draft's (G5) | `coreToSemSM` (GL:364); `DraftFL`, `DraftFLNil` *stated* | §6 lists the rows |
| J3 | `semTyping`, `GenSelfAccepted`, `ReconAccepted` (`Programs.lean:38`, :42, :46) | Targets' `AcceptedAt` (`Targets/I/Programs.lean:259`); `adequacyD` | stale: `semTyping` reads `SemS` (`Sem.lean:102`), statement 0's relation `vRL` [read] | — | statement 5's acceptance is not stated at `vRLM` |
| J4 | (no adequacy theorem before this unit) | `adequacyD` (`Demonic.lean:312`), `theorem32D` (:292) | the draft's acceptance at `[]` at `F 1` gives Core's adequacy | `adequacyNilM` (GL:1101) | the draft's floor inherits safety and termination at `[]` |
| J5 | `NilSoundRet`, `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` (`Statement0.lean:95`, :154, :161, :167, :173, at `vRL`); `NilSoundRetM` (`R1.lean:1383`) | OQ-58 (a) | at `vRLM`: `NilSoundRetM` proved one way at data (`nilSoundRetM`); both ways at a flat answer (`cRLMRetNil`); Core inside the draft at `NilVal`/`NilComp` types, thunks included (`coreSubWNil`). The `vRL` statements are at a superseded relation (§9) | `cRLMRetNil` (GL:736), `coreSubWNil` (GL:889) | OQ-58 at `vRLM` is answered at `NilComp` types (Core inside the draft) and at flat types (equal) |
| J6 | `DraftFLEmbed` (GL:1192) | `embed` (`Embedding.lean:235`), `adequacy_of_derivesWf` (:326) | the floor at BoLo's image: *stated*, not attempted | — | the paper's own programs are its instances (§10, P42) |
| J7 | the callback steps `CallbackExtMutM`, `CallbackExtImmM` (`R1.lean:1410`, :1426), `.arr` shape, proved (`callbackExtMutM_own`, `callbackExtImmM_own`, `R1Stmt0.lean:399`, :418); `CallbackExtMutMF`, `CallbackExtImmMF` (`Nx.lean:466`, :483), thunked shape, *stated* | the callback step inside `withbor1_compatX` … (`Compatibility.lean:937`); unwinding forms (`EffBorrow.lean`) | *not stated*: the draft reads the callback at its own push, Core at an instance [read] | none | the draft step of every `withbor` K entry; at the thunked shape Core's non-unwinding programs use, stated and not proved |
| J8 | `PairWithloadTyped`, `PairWithloadUTyped` (`Nx.lean:194`, :201; proved, `pairWithloadTyped`, `pairWithloadUTyped`, `NxGuardPair.lean:581`, :577); `SliceTyped`, `SliceUTyped` (`Nx.lean:331`, :338; stated); `pairProgU`, `sliceProgU` (`Nx.lean:62`, :258) | `CDerives` through `CDerivesNU` | the statements are at `ProbeRules`; the proofs build `CDerivesNU` derivations, so the derivations are Core's by `CDerivesNU.toCDerives` [read] | none | `pairProgU pCbE` is the open node at the view of S1's enclosing lend (§10) |

---

## 6. The rows against `fundamentalC`

One line per `CDerives` constructor (`Fundamental.lean:60–372`), with the lemma `fundamentalC`
applies (`:437–543`) and the draft row. A draft row is the constructor's statement at
`SemSM .binder0`; the rows not proved are stated in GL (:1204–:1445) under the names below. At a
first-order judgement G5 gives the node from Core whatever the rule; at a first-order constant at a
dead context G5c does.

| constructor | Core lemma | draft row | status |
|---|---|---|---|
| `var` | `var_compatC` | `VarRowM` (GL:1204) | stated |
| `unitI` | `unitI_compatC` | `UnitIRowM` | stated; G5 at every dead context |
| `tensorI` | `tensorI_compatC` | `TensorIRowM` | stated |
| `sumI₁`, `sumI₂` | `sumI₁_compatC`, `sumI₂_compatC` | `SumI₁RowM`, `SumI₂RowM` | stated |
| `thunkF`, `thunkV` | `thunkF_compatC`, `thunkV_compatC` | `ThunkFRowM`, `ThunkVRowM` (`R1.lean:434`, :439) | proved (`statement0UFullM`, `R1Box.lean:580`) |
| `ret`, `ofRet` | `ret_compatC`, — | the identity (`jdgCty`) | trivial |
| `bind` | `bind_compatC` | `BindRowM` | stated |
| `force` | `force_compatC` | `ForceRowM` (`R1.lean:1402`) | proved (`forceRowM`, `R1Stmt0.lean:367`) |
| `lam` | `lam_compatC` | `LamRowM` | stated |
| `app` | `app_compatC` | `AppRowM` | stated |
| `withI`, `proj₁`, `proj₂`, `topI` | `withI_compatC`, `proj₁_compatC`, `proj₂_compatC`, `topI_compatC` | `WithIRowM`, `Proj₁RowM`, `Proj₂RowM`; `topI` is `True` | stated; `topI` trivial |
| `unitE`, `tensorE`, `sumE`, `zeroE` | `unitE_compatC`, `tensorE_compatC`, `sumE_compatC`, `zeroE_compatC` | `UnitERowM`, `LetPairRowM`, `SumERowM` | stated (`zeroE` not stated) |
| `allI` | `allI_compatC` | `AllIRowMAt` (`Nx.lean:509`) | proved at contexts reaching no `U` (`allIRowMUFree0`, `NxAllI.lean:209`); open at a live `U` slot (D6) and at a persistent slot, whose push is binder-named (`VRLMStackRename`, D5) |
| `allE`, `allEV` | `allE_compatC`, `allE_compatX` | `AllERowM`, `AllEVRowM` | stated; their step `InScopeOfInterp` (`Nx.lean:396`) stated (D1) |
| `bangThunkF`, `bangThunkV` | `bangThunkF_compatC`, `bangThunkV_compatC` | `BangThunkFRowM`, `BangThunkVRowM` (`R1.lean:446`, :452) | proved with `PersistentBoxed` (`statement0UFullM`) |
| `bangE` | `bangE_compatC` | `BangERowM` | stated |
| `copyBang`, `forgetBang` | `copyBang_compatC`, `forgetBang_compatC` | — | G5c at a flat non-thunk `A`; at a thunk `A` not stated |
| `boxI`, `boxE` | `boxI_compatC`, `boxE_compatC` | `BoxIRowM`, `BoxERowM` | stated |
| `immSub`, `mutSub` | `immSub_compatC`, `mutSub_compatC` | `ImmSubRowM`, `MutSubRowM` | stated (answers hold borrow leaves, D7) |
| `alloc`, `free` | `alloc_compatX`, `free_compatX` | `AllocRowM`, `FreeRowM` | G5c at a flat payload; otherwise stated |
| `swap` | `swap_compatX` | `SwapRowM` | stated: `swap` is curried, its first answer a thunk, so it is no first-order constant type |
| `copy` | `copy_compatX` | `CopyRowM` | stated (answer holds `Imm` leaves, D7) |
| `forgetImm`, `forgetMut`, `forgetUnk` | `forget*_compatX` | — | G5c at every payload (argument `FOArg`, answer `1`) |
| `lit` | `lit_compatX` | — | G5 (a value at a flat type) |
| `hostOp` | `hostOp_compatX` | — | G5c (a persistent first-order function) [read: the host signatures are data] |
| `arrNew`, `arrFree` | `arrNew_compatX`, `arrFree_compatX` | `ArrNewRowM`, `ArrFreeRowM` | stated (higher-order: a `!U` argument) |
| `arrSize`, `arrReplace` | `arrSize_compatX`, `arrReplace_compatX` | — | G5c at a flat element type |
| `arrLen`, `arrForget` | `arrLen_compatX`, `arrForget_compatX` | — | G5c at every element type (argument a family of `Imm` leaves) |
| `arrGet`, `arrCopy` | `arrGet_compatX`, `arrCopy_compatX` | `ArrGetRowM`; `arrCopy` not stated | stated (answers hold `Imm` leaves, D7) |
| `countFold`, `countTry`, `boundedFix` | `countFold_compatX`, `countTry_compatX`, `boundedFix_compatX` | `CountFoldRowM`, `BoundedFixRowM` | stated (higher-order) |
| `sliceBorrowM`, `sliceBorrowI` | `sliceBorrowM_compatX`, `sliceBorrowI_compatX` | `SliceBorrowIRowM` | stated; the slice gate (§10, S2) |
| `sliceGetM`, `sliceLenM`, `sliceSplitI`, `sliceSplitM`, `sliceEmptyI`, `sliceEmptyM`, `sliceReplaceM`, `sliceSwapM` | `slice*_compatX` | — | not stated (answers hold slices or `Mut` leaves, D7) |
| `withbor1`, `withbor2`, `withbor3` | `withbor1_compatX` (`Compatibility.lean:937`), `withbor2_compatX`, `withbor3_compatX` | `Withbor1RowM`, `Withbor2RowM`, `Withbor3RowM` | stated; consumer facts `CallbackExt*M` (`.arr` shape) proved, `CallbackExt*MF` (thunked) stated |
| `withload` | `withload_compatX` (`Compatibility.lean:252`) | `WithloadRowM` | stated; its draft step is the gate (§10) |
| `withswap` | `withswap_compatX` | `WithswapRowM` | stated |
| `withbor1U` … `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU` | `*U_compatX` (`EffBorrow.lean`) | `WithloadURowM` (empty row); the spanning rows `SpanW1Row`, `SpanW2Row`, `SpanLoadRow` at `SemS` (§9) | stated |
| `lolliE` | `lolliE_compatX` | `LolliERowM` | stated (D9) |
| `roll`, `unroll` | `roll_compatX`, `unroll_compatX` | `RollRowM`, `UnrollRowM` (`Nx.lean:380`, :385) | proved (`rollRowM`, `unrollRowM`, `NxUnroll.lean:399`, :408) |
| `foldImm`, `foldOwn`, `foldReuse` | `foldImm_compatX`, `foldOwn_compatX`, `foldReuse_compatX` | `FoldImmRowM`, `FoldOwnRowM`, `FoldReuseRowM` | stated |
| `nuIn`, `nuOut` | `nuIn_compatX`, `nuOut_compatX` | `NuInRowM`; `nuOut` not stated | stated; at `ν` the draft's clause is Core's (`cRLMTopNuEq`) |
| `unfoldN` | `unfold_compatX` | `UnfoldNRowM` | stated |
| `effSub`, `effPerform`, `effRaise`, `effLet`, `effThen`, `effHandle` | `sub_compatC`, `perform_compatC`, `raise_compatC`, `let_compatC`, `then_compatC`, `handle_compatC` | `ThenRow`, `HandleRow` at `SemS` (§9); not stated at `SemSM` | the next suite (§10.7) |

---

## 7. Draft-only definitions

Each exists for suspension. Some are read at every borrow callback, because `binder0` reads each
`∀` instance as a lend (the own push); those reach borrow-only programs, and the divergence
register (§8) tracks them.

| definition | why it exists |
|---|---|
| `Stk`, `LEnt`, `LStack`, `StackOK`, `hideS` | the lends open across a stop, innermost first, with the rows whose stops cross each; read at every own push |
| `TabAtS`, `guardPV` | the only borrow cell at an internal lifetime is at a lent place, so a resume can re-lend exactly those; read at every own push |
| `PlaceViewsL`, `DeepAt`, `ExAt`, `innerAt`, `vwEW`, `vwSW`, `vwSL` | a borrow cell at a lent place is the lend's view, handed back at the thaw (the freeze binder's location half) |
| `CohS` | the 6.65 analog of `CohE`: a view at a lent place is the binder's; read at every own push |
| `OwnOKI`, `OwnPushI`, `OwnPushM`, `ViewAt` | the callback's own lend: an instance read as the lend it names, so a stop can see it; read at every borrow callback |
| `InScope` ((E1)) | so the `∀` clause's reading transports pass the effect clause's re-lend (`NEXT.md` §3.1); read at every `∀E` |
| `Inst`, `InstAt`, `RelendJ`, `KeepsS`, `RecUpTo`, `KeepsT` | a resume re-lends every internal lifetime as one order-preserving instantiation (the freeze binder's lifetime half) |
| `cutOf`, `Internal`, `InternalVar`, `OuterBelowTop`, `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `BoundInside` | the instantiation's bookkeeping: what it moves and what it must fix |
| `PayExt`, `RetainedPay` | a retained cell's payload reads only lifetimes the instantiation fixes (`mut_not_natural`'s mechanism kept out); read at every stack |
| `PBox`, `BoxStep` | a persistent value carried to every world a resume or a push can carry it to |
| `StackJ`, `StackJM`, `BindersLow`, `SubDom`, `CtxFresh`, `OwnHyg` | the hygiene between the stack's names and the judgement's binders |
| `bodyS`, `OpenS`, `openFS`, `stopS`, `ghostS`, `dropS` (GhostEnd) | the piece: a stop ghost-ends the lends it crosses and owes their re-lend |
| `Fut`, `FutStep`, `FutQ`, `FutI`, `FutAvoids`, `OrdW`, `RelendU`, `RelendUI` | the other placements' futures (`cbpv`, `binder`); `binder0` reads none |
| `ArisesVI`, `ArisesCtxI`, `Cfg` | the arising check of a refutation (DESIGN §11) |
| `Placement` | the candidates for where the future-world quantifier sits (OQ-8) |

---

## 8. The divergence register

Each draft condition stricter or weaker than Core where it can reach a borrow-only program, with
the suite entries that probe it (§10). A probe whose entry is NOT BUILT reads the condition only once
its rows are built.

| # | draft condition | what it can reject or leave unproved | probes |
|---|---|---|---|
| D1 | (E1): `∀`'s first conjunct reads instances in scope only | `∀E` at an instance not in scope; a top-level polymorphic value is checked by its own pushes alone (`cRLMAllTop`) | P4 (`∀E` at `'a`, in scope); P7, P21, P22; P20; the borrowers' `g [] b` at the callback's own variable (P10, P11, P25–P27, P29, P33, P34); the persistent defs called at a callback's own variable: P46's `body ['z]`, P48's `body ['z] ['w]` and `inner ['z]`, P43's `get ['x]`, P58's `k ['z]`, P60's externs; P56's `read ['y]` |
| D2 | the own push lends one place (`OwnPushM`) | a consumer handing its callback several cells at one lifetime | S1 (two cells); S2: P46's `withload` at `array i32` (ten cells), P48's two, P43's, P47's, P56's (five), P58's, P57's slice lend; one cell, the positive controls: P5's `withload` of a record, P16's of a variant, P33's of a list cell; no cell: P1, P2, P27's leaf load |
| D3 | `OwnOKI.placeFree`: the callback holds no cell at the lent place, at any depth | a callback holding a copy of the view whose witness owns the reborrowed places | S5 |
| D4 | `PBox`: a persistent thunk holds at every box world | a persistent value Core accepts that misbehaves at a phantom push | P3; the steps of P12, P35–P41; P13's `tab10V`, `dropI32V`; the algebras of P10, P11, P25–P27, P29; P33's stages; the persistent defs of P43–P48; P52's `incCb`; P42's `callBorrowed`; P60's externs. At a first-order persistent value Core derives at a dead context the box holds (G5c) |
| D5 | the box carries only reserved-name pushes | a persistent context value across the `∀I` row's binder-named push | P33 (`stepV` at `g : countTy`; `cbE` and the borrower capturing `g`), P34, the borrowers at `g : fTy` (P10, P11, P25–P27, P29); P58 (`k`); P42's `fnMut`; the `lend_*` combinators of P43–P45; P60 (`write_byte`) |
| D6 | the `∀I` row at a live `U` slot is not derived | a callback capturing a closure | `withborF2` (P7, P8, P18, P19), `withborS` (P9, P20–P24), `borrowerM` (P30–P32); the optics (P50–P52) [read] |
| D7 | `CohS`, `RetainedPay` at a pushed stack, and at answers holding a borrow leaf | arguments a consumer must hand over with these; answers that return a view | P6 and every `withswap`; `copy` at `Imm` (P5, P7, P21); every `array_get` and `array_copy`; P39's `passF`, P41's `logStep`, P49's answer, P55's answer, P42's `captures`, P59's answers |
| D8 | `KeepsT` in the `U` clause | a thunk forced at a list that keeps a relevant record without its tag [unchecked: runs keep tags] | P2 (forces a thunk after the lend) |
| D9 | `guardPV` at `⊸` and `∀` | a call inside a callback whose composite fails the table | the glue at `readOne ()`, `readBoth ()`, `swapFn ()` (P7, P20–P22), the borrowers' `g [] b`, P33's `cbE`, the calls of persistent defs inside a lend's callback (P43–P48, P58, P60). All NOT BUILT. G5 closes a first-order callback without reading the guard, so no PROVED entry reads D9 |
| D10 | W's own `μ`, `[L]`, type variables | a thunk inside `μ` read by W's `U` | the list and tree programs, P17's bag, P13's arrays, the loops' unary counts and families of P43–P48, P59's `Bytes`. At flat `μ` and `[L]` the draft is Core's (G1) |
| D11 | the views read an `imm` payload at `vC true` | a lend whose payload holds a thunk | P2 (`withbor` at `methodsTy`); P42's `callBorrowed` and `captures` |
| D12 | after the block (part (3), `GROUND.md` §4.2): a stop at a stack holding a block | effectful code that stops at a stack holding a block: (i) its resumable stops, read over GhostEnd's strict re-lends, which split a block; (ii) its stops crossing the block, where `ghostS` treats the innermost entry only [unchecked] | none in this suite: borrow-only programs read no `F_Σ` row. Its reach is recorded with part (3)'s outcome (§11) |

---

## 9. Superseded relations

Each earlier draft relation stays as the statement it was. The ledger lists them so that no result
is read at the wrong relation.

| family | definitions | to `vRLM` | results and doc claims that rest on it |
|---|---|---|---|
| W₀ | `vRL`, `cRL`, `effRet`, `gRL` (`Relation.lean:108`, :131, :160); `SemS` (`Sem.lean:102`); `SemSR` (`Thunk.lean:227`); `WP` (`Sem.lean:119`) | no `CohS`, no `RetainedPay`, no instantiations: the `U` clause is GhostEnd's `RelendableS` under `guardW` | statement 0's bundle and shared lemmas (`Statement0.lean`; `statement0Shared`, `Shared.lean:19`; `nilSoundRet`, `Bridge.lean:133`); the rows of `Statement0.lean`, `Rows0.lean`, `Thunk.lean`; statements 1–4 and 6 (`LamRow`, `AllIRow`, `BelowRow`, `SpanW1Row`, `SpanW2Row`, `SpanLoadRow`, `HandleRow`, `ThenRow`, `semTyping`, `GenSelfAccepted`, `ReconAccepted`); OQ-58's `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` |
| W revised | `vRLI`, `cRLI`, `gRLI`, `SemSI` (`BinderW.lean:42`, :66, :115, :122) | an earlier revision: `CohS` without `RetainedPay`, `RelendI` for `RelendJ`, no `μ`, `[L]` or type variable of its own, no (E1)–(E4), no box [read] | the binder unit's results (`BINDER.md`) |
| R1-before | `vRLJ`, `cRLJ`, `gRLJ`, `SemSJ` (`BinderJ.lean:72`, :98, :147, :152); `Statement0UFullJ` (:202) | `vRLM = vRLJ` at types with no `μ`, `[L]`, type variable, lifetime `∀` or persistent thunk (`RelMAgreesJ`, `R1.lean:334`; `relMAgreesJ`, `R1Thaw.lean:195`) | `gdBangJ` (`NxFloor.lean:55`); `GAP.md`'s adjacency at `vRLJ`; the rows `*RowJ`, `*RowTFJ`, `*RowKJ` |
| GhostEnd | `vRLs`, `cRLs` (`GhostEnd/Stacked.lean:237`, :252), `vRLa` (`GhostEnd/Arising.lean:173`) | the ancestors: the stack and the piece without W's guard and leaves | GhostEnd's own results; the piece (`bodyS`, `OpenS`, `openFS`) is read by `vRLM`'s `F_Σ` clause unchanged |

No claim of this unit rests on a superseded family, except `gdBangJ` (at `vRLJ`) and the
`SpanLoadRow`/`ThenRow` mentions (at `SemS`).
