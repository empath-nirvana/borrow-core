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

---

## 10. The regression suite

`ProbeD1/GroundRegress.lean` ("GR"). The design is `GROUND.md` §3. Every theorem in GR is proved,
with `#print axioms` within `[propext, Classical.choice, Quot.sound]` (186 theorems checked).

**The obligation.** A program's obligation is `DraftFL` restricted to its derivation: at every node
`Δ; Γ ⊢ e : j` of its `CDerives` derivation, `SemSM .binder0 Δ Γ e j` at every index (`AccNode`,
GR:52). Each entry is one node. **PROVED**: a theorem proves the entry at every index. **NOT
BUILT**: the docstring names the missing lemma, a row of §6 or another named `def … : Prop`; a
route refuted is recorded as "route blocked" there, with whether its configuration arises. **FAILS**
would need a configuration that arises (`ArisesI`, with `ArisesVI` for every value read), every
hypothesis discharged and the entry's own judgement refuted: no entry is FAILS. Every PROVED entry
has its `EntryRead` lemma (GR:62; `readImmBorrow`, `readPairLoad`, `readBangUse`,
`readArrayGet`, `readRoots`…`readOthers`, GR:416, :1224, :1590, :1711, :1751–:1826), so its
judgement's binders are low and its free variables `Δ`'s: the entry's premises hold and its proof
is not vacuous. No entry is recorded "PROVED at `[]`" alone.

**The floor rule.** Every borrow-only program Core accepts must be accepted by the draft. A FAILS is
a draft defect, never a restriction. NOT BUILT entries are the floor's remaining work.

### 10.1 What the suite builds

| piece | GR | status | what it is |
|---|---|---|---|
| `semSMCallbackOfCore` | :142 | proved | a callback `Λ. return (λx. body)` at `∀'x ⊏ b. A ⊸ F B` (thunked shape), `A` first-order, `B` flat, at a context of first-order slots the binder avoids: G5 at the λ, `ThunkVRowM` (`statement0UFullM.2.2.2.1`), `AllIRowMAt` at a context reaching no `U` (`allIRowMUFree0`), `ThunkVRowM` at the `∀` |
| `semSMCallbackArrOfCore` | :166 | proved | the same at the `.arr` shape `U(∀'x ⊏ b. A ⊸ F B)` |
| `semSMBangCallbackOfCore` | :187 | proved | the same, persistent, at a dead context: `BangThunkVRowM` (`statement0UFullM.2.2.2.2.2`) over the `∀` |
| `semSMBangThunkOfCore`, `semSMThunkOfCore` | :213, :226 | proved | a (persistent) thunk of a first-order computation type: G5 at the λ, then the `!U` or `U` row |
| `semSM_callbackW`, `semSM_algI`, `semSM_const`, `semSM_root`, `semSM_rootV`, `semSM_embedRoot` | :323–:355, :1253 | proved | the producer lemmas at Core's own shapes (`callbackW`, `d_algI`), G5c at a value, G5 at a closed program, G5 at `embed` |
| `LoadGateNil` | :256 | stated | `withload`'s draft step at the empty stack, both cases of `CohE` (`LoadPay`, :246). One hypothesis is added: `x ∉ CTy.binders (C' x)`. The own push names the binder, which the body must not bind again (`OwnPushI`); Core's typing does not exclude it |
| `FreePlaceExists` | :273 | stated | every resource leaves a place free at every depth. Not built here: `[TR]`'s `Res` is finite at every depth (`docs/adjudications.md` D10) |
| `loadGateNil_unit` | :277 | proved, from `FreePlaceExists` | the gate at a payload with no reborrowed cell (`1`), at callback types other than `.arr` or whose `ViewAt` holds |
| S1: `pairLoad`, `pairLoadU` | :1076, :1114 | `d_pairLoad`, `d_pairLoadU` proved; `pairLoad_eval`, `pairLoadU_eval` by `decide` | `withload` of a pair of references, at `withload`'s type and at its unwinding type at the empty row (§10.5) |
| S3: `bangUse` | :1491 | `d_bangUse` proved; `bangUse_eval` = `(7, 8)` by `decide` | the user's case (§10.5) |
| P56: `corpus/array-get.bc` | :1626 | `arrayGetP_checks`, `arrayGet_shape`, `arrayGet_erasures` by `decide +kernel`; `arrayGet_derives` | the checker's derivation of the corpus file, and its `def`s' erasures checked equal to `tabE`, `readE` |

### 10.2 The enumeration

The source is `GROUND.md` §3.4's table. Taken in: every B program there with a Lean derivation
that builds on this branch. Not taken in, each with its reason:

| programs | reason |
|---|---|
| P43–P48 (`loopImm`, `genMut`, `configImm`, `eachImm`, `zipPushPull`, `zipPushPush`; `experiments/LoopBorrow/LoopBorrow/Instances.lean`) | `LoopBorrow.Instances` does not build on this branch: `lend-gen-mut.bc:14:22` and `zip-push-pull.bc:41:14` no longer parse ("expected a type, found name `gen`"), and for the other four `decide +kernel` fails at `(mainOf …).isSome` with the kernel's reduction stuck. Re-running the checker route here (`bcc_program%` on `lend-each-imm.bc`) fails the same way, although `#eval (mainOf …).isSome` is `true` |
| P50–P52 (`fieldProg`, `variantProg`, `iterProg`; Optics) | `Optics.Runs` fails to build on this branch (`Runs.lean:38`, application type mismatch; unsolved goals at `:105`, `:123`, `:137`, `:157`), and `Optics.Lens` imports it, so `Optics.Programs`, `Optics.Prism` and `Optics.Traversal` cannot be imported |
| P60 (Coeffects' `main`) | `Coeffects.Programs` imports `Optics.Lens` (through `Coeffects.Demand`) |
| P57 (`corpus/slice-imm.bc`), P58 (`corpus/lend-lib-each.bc`) | `decide +kernel` fails at `(mainOf …).isSome` with the kernel's reduction stuck; `#eval` gives `true` |

So S2's primary instance (P46) and S3's (P46, P48) are not available here. S2 is served by P56
(`array-get.bc`, five cells at one lifetime); S3 by `bangUse` (built for this) and, slot-carried,
by P33.

### 10.3 Results, per entry

"Kind" is R (root), V (a value at a type with `U`, `∀` or `!`), K (a constant), G (glue). Every
status is at every index. The abbreviations are `GROUND.md` §3.5's: [G5], [G5c] (`coreToSemSM`,
`coreToSemSMConst`); [cb], [cb→], [bcb], [bt] (`semSMCallbackOfCore`, `semSMCallbackArrOfCore`,
`semSMBangCallbackOfCore`, `semSMBangThunkOfCore`) at the named body derivation.

| program | entry (GR) | kind | status | theorem, or the missing lemma |
|---|---|---|---|---|
| P1 `cImmBorrow` | `AccImmBorrowRoot` (:362) | R | PROVED | `accImmBorrowRoot` [G5] |
| | `AccImmBorrowCb` (:366) | V | PROVED | `accImmBorrowCb` [cb] at `d_borrowBody` |
| | `AccImmBorrowLoader` (:370) | V | PROVED | `accImmBorrowLoader` [cb] at `d_loaderBody` (rebuilt from `d_loader`'s constructors) |
| | `AccImmBorrowWithbor` (:375) | K | NOT BUILT | `Withbor1RowM` |
| | `AccImmBorrowWithload` (:381) | K | NOT BUILT | `WithloadRowM`; its gate at `1` is `loadGateNil_unit`, from `FreePlaceExists` |
| | `AccImmBorrowAlloc`, `AccImmBorrowFree` (:386, :390) | K | PROVED | `accImmBorrowAlloc`, `accImmBorrowFree` [G5c] |
| P2 `cRecBorrow` | `AccRecBorrowRoot` (:448) | R | PROVED | [G5] |
| | `AccRecBorrowMethods` (:452) | V | PROVED | `accRecBorrowMethods` [G5c] at `d_methods` |
| | `AccRecBorrowCb` (:456) | V | PROVED | [cb] at `d_borrowBody` |
| | `AccRecBorrowLoader` (:460) | V | PROVED | [cb] at `d_recLoaderBody` (rebuilt from `d_recLoader`'s) |
| | `AccRecBorrowWithbor` (:464) | K | NOT BUILT | `Withbor1RowM` (D11) |
| | `AccRecBorrowAlloc` (:469) | K | NOT BUILT | `AllocRowM` at a thunk payload |
| | `AccRecBorrowForget` (:473) | K | PROVED | [G5c] |
| P3 `cBang` | `AccBangRoot`, `AccBangClosure` (:510, :513) | R, V | PROVED | [G5]; [bt] |
| P4 `cInst` | `AccInstRoot`, `AccInstPoly` (:524, :527) | R, V | PROVED | [G5]; [cb→] |
| P5 `readFields` | `AccReadFieldsRoot`, `AccReadFieldsCb` (:539, :542) | R, V | PROVED | [G5]; [cb] at `d_readBody` |
| | `AccReadFieldsLoad` (:549) | K | NOT BUILT | `WithloadRowM` (one reborrowed cell: the positive control) |
| | `AccReadFieldsCopy` (:554) | K | NOT BUILT | `CopyRowM` (D7) |
| | `AccReadFieldsAlloc` (:558) | K | PROVED | [G5c] |
| P6 `mutFields` | `AccMutFieldsRoot`, `…Flip`, `…Poke` (:573–:580) | R, V, V | PROVED | [G5]; [G5c] at `d_flipG`, `d_pokeG` (`pokeG` lends inside its body) |
| | `AccMutFieldsSwap` (:584) | K | NOT BUILT | `WithswapRowM` (D7) |
| P14 `exProg`, P15 `build3`, P16 `matchSome`, P17 `bagProg` | the roots; `AccExProgPair`, `AccBagPush` (:600–:623) | R, V | PROVED | [G5]; [G5c] |
| P7, P8, P18, P19, P9, P20–P24 (family and block borrows) | the ten roots (:639–:648) | R | PROVED | [G5] |
| | `AccReadCb` (P7, P21), `AccSwapCb A` (P8, P9, P18), `AccNestCb` (P20), `AccNestReadCb` (P22), `AccBagCb` (P23) (:663–:731) | V | PROVED | [cb], their bodies rebuilt from Core's constructors |
| | `AccReadFamilyWithborF2` (P7), `AccBlockSwapWithborS` (P9) (:747, :753) | K | NOT BUILT | `DraftFL` at `withborI2_wf`'s and `withborS_wf`'s derivations: the inner callback captures the user's callback as a live `U` slot (`AllIRowMAt` there, D6). P8, P18, P19, P20–P24's borrow constants are the same two |
| P10, P11, P25, P26, P27, P28, P29, P30, P31 | the nine roots (:764–:772) | R | PROVED | [G5] |
| | `AccCountAlg`, `AccAnyListAlg`, `AccAnyTreeAlg`, `AccSumIAlg`, `AccSumAlg` (:790–:861) | V | PROVED | [bcb] (P27's algebra loads each leaf with `withload`; P29's calls `natCopy` at its own variable, D1) |
| | `AccFreeLAlg`, `AccFreeIAlg` (:821, :851) | V | PROVED | [G5c] |
| | the borrowers at `g : fTy`, `foldImm`, `foldOwn`, `withbor` (1) | V, K | NOT BUILT, not stated as entries | `GROUND.md` §3.5: P10's V2 list (`AllIRowMAt` at a persistent slot, D5), `FoldImmRowM`, `FoldOwnRowM`, `Withbor1RowM` |
| P30 `mapProgC` (open), P32 `mapProg`, P34 `countFreeProg` | `AccMapProgOpenCRoot`, `AccMapProgRoot`, `AccCountFreeRoot` (:904, :901, :909) | R | NOT BUILT | the glue at `U` slots (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`); `borrowerM` at a live `U` slot (D6) |
| P33 `countProg` (the user's case, slot-carried) | `AccCountZero` (:869) | V | PROVED | [bcb] |
| | `AccCountRoot` (:882) | R | NOT BUILT | the glue at `ΓF`'s `U` slots |
| | `AccCountStep` (:888) | V | NOT BUILT | `AllIRowMAt .binder0 (⟨countTy, true⟩ :: Γ)`: the binder-named push at a persistent context (`VRLMStackRename`, D5) |
| | `AccCountCb` (:894) | V | NOT BUILT | as `AccCountStep`, and in the body `AllEVRowM` at `g []` (D1), `LolliERowM` (D9) |
| | `AccCountLoad` (:912) | K | NOT BUILT | `WithloadRowM` (one cell) |
| P12, P35–P41, P13 (affine closures, arrays) | the nine roots (:922–:930) | R | PROVED | [G5] (P39 at every `n`) |
| | `AccCounterStep`, `AccInc`, `AccTab10`, `AccDropI32` (:945, :979, :1000, :1007) | V | PROVED | [G5c] |
| | `AccCntCb` (:956), `AccPassCb n` (:964) | V | PROVED | [cb] at `d_cntBody`; at `passCb`'s body (it hands the borrow through `n` persistent functions) |
| | `AccPassF` (:989) | V | NOT BUILT | `LamRowM` (its answer holds a `Mut` leaf, D7) |
| | `AccPassWithbor3` (:994) | K | NOT BUILT | `Withbor3RowM` |
| S1 `pairLoad` | `AccPairLoadRoot` (:1135) | R | PROVED | `accPairLoadRoot` [G5] |
| | `AccPairLoadCb` (:1139) | V | PROVED | `accPairLoadCb` [cb] at `d_borrowBody` (its body holds the load of the pair) |
| | `AccPairLoadLoader` (:1147) | V | PROVED | `accPairLoadLoader` [cb] at `d_pairLoaderBody` |
| | `AccPairLoadAlloc`, `…Free`, `…Forget` (:1180–:1188); P1's `alloc`, `free` at `1` | K | PROVED | [G5c] |
| | `AccPairLoadWithbor` (:1156) | K | NOT BUILT | `Withbor1RowM` |
| | `AccPairLoadWithload` (:1165) | K | NOT BUILT | `WithloadRowM`. Route blocked at the single own push: it lends one place, and the second reborrowed cell fails the table at the identity instantiation of the answer's `U` clause, at every stack (`loadGuardFails2`). At the thunked type the answer's `U` clause at a non-identity instantiation moves the push below the cells (`not_withloadPairGapInst`), a route neither refuted nor built |
| S1′ `pairLoadU` | `AccPairLoadURoot`, `AccPairLoadCbU`, `AccPairLoadLoaderU` (:1136, :1143, :1151) | R, V, V | PROVED | [G5]; [cb] at `d_borrowBodyU`; [cb→] at `d_pairLoaderBody` |
| | `AccPairLoadWithloadU` (:1175) | K | NOT BUILT | `WithloadURowM`. Route blocked at an arising configuration: `withloadUPairGapReal` (`NxGuardPair.lean:844`), at the stack of the enclosing lend of the pair, `ArisesI` with the view `ArisesVI`. The entry's own judgement is not refuted (`PairArgCellsLe`, not built), so it is not FAILS |
| S3 `bangUse` | `AccBangUseRoot` (:1514) | R | PROVED | `accBangUseRoot` [G5] |
| | `AccBangUseBody` (:1519), the producer | V | PROVED | `accBangUseBody` [bcb], at every `Δ` its binder is fresh for (the use's `Δuse` at `z = 2` among them) and every dead context |
| | `AccBangUseCall` (:1537), `body ['z] (v, 1)` | G | PROVED | `accBangUseCall` [G5]: the node is first-order (its live slot is the view, its answer `['z] I32`) |
| | `AccBangUseCb`, `AccBangUseBorrower` (:1542, :1547) | V | PROVED | [cb] at `d_useCall`, `d_useBorrowerBody` |
| | `AccBangUseDeref` (:1524), `unbang body` | G | NOT BUILT | `BangERowM` |
| | `AccBangUseInst` (:1530), `body ['z]` at the callback's own variable | G | NOT BUILT | `AllEVRowM` (its step `InScopeOfInterp`, D1) |
| | `AccBangUseWithbor`, `AccBangUseLoad`, `AccBangUseInnerLoad` (:1552–:1562) | K | NOT BUILT | `Withbor1RowM`; `WithloadRowM` at `Ref I32` (one cell) and at `I32` (no cell) |
| P42 (×13) | `Acc…Root` for `allocFree`, `fig2c`, `immBorrow`, `mutBorrow`, `loadClosure`, `aliasLoad`, `swapTwo`, `greetProg`, `ownedFn`, `mutClosure`, `callBorrowed`, `captures`, `fnMut` (:1257–:1269) | R | PROVED | `semSM_embedRoot` [G5 at `embed d_X`] |
| | every other node | — | NOT BUILT | `DraftFLEmbed` (G12) at `d_X` |
| P49 `recLog` | `AccRecLogRoot` (:1296) | R | NOT BUILT | its answer `F (Mut @a I32 ⊗ 1)` holds a `Mut` leaf (D7): `BoundedFixRowM`, `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM` |
| | `AccRecLogStep` (:1301) | V | NOT BUILT | `LamRowM` (`BangThunkVRowM` proved) |
| | `AccRecLogClause` (:1305) | K | PROVED | [G5c] |
| P53 `sumAffE`, P54 `blockAffE b` | `AccSumAffRoot`, `AccBlockAffRoot` (:1318, :1321) | R | PROVED | [G5] at `ADerives.elab` (P54 at every `b`) |
| | `AccSumAffAlg` (:1331) | V | PROVED | [bcb] |
| P55 `allBelow` | `AccBelow` (:1359) | V | NOT BUILT | `LamRowM`, with `ThunkFRowM` (proved) over `VarRowM` at the `Mut` slot (D7); the `∀I` step is `allIRowMUFree0 []` |
| P56 `array-get.bc` | `AccArrayGetRoot` (:1653) | R | PROVED | `accArrayGetRoot` [G5] at `arrayGet_derives`, the checker's derivation |
| | `AccArrayGetTab` (:1666) | V | PROVED | [G5c] at `d_tabE` |
| | `AccArrayGetRead` (:1689), `read` inlined at its use | V | PROVED | [cb] at `d_readBody`, at every `Δ` its binder is fresh for |
| | the `withbor` (1) and `withload` callbacks | V | NOT BUILT, not stated | their λ-bodies' derivations are inside the checker's and are not re-derived (§3.1's route for an inline sub-term); both bodies are first-order, so G5 gives each once derived |
| | `AccArrayGetLoad` (:1701), at `array i32` | K | NOT BUILT | `WithloadRowM`; route blocked at the single own push (five cells at one lifetime; `loadGuardFails2` at any two) |
| | `AccArrayGetReadLoad` (:1707), at `I32` in `read` | K | NOT BUILT | `WithloadRowM` (no reborrowed cell) |
| | `array_copy`, `array_get`, `array_new`, `array_len`, `withbor` (1) | K | NOT BUILT, not stated | D7 (`ArrGetRowM`); `ArrNewRowM`; `array_len` is G5c-shaped; `Withbor1RowM` |
| P59 the I/O models | `AccMkInput`, `AccMkOutput`, `AccTakeInput`, `AccTakeOutput` (:1370–:1376) | V | PROVED | [G5] (λs at first-order computation types) |
| | `AccReadByte`, `AccWriteAll` (:1394, :1399) | V | NOT BUILT | `LamRowM` (answers holding the stream's `Mut` leaf, D7) under `allIRowMUFree0 []` |
| S4 `reconB′` | `AccReconRoot`, `AccReconCb` (:1733, :1739) | R, V | NOT BUILT | no Core derivation (tier 2): `wait` resumes inside the lend |

### 10.4 Results, per program

The conjunctions of each program's stated entries are GR:1849–:1911. The third column lists the
nodes `GROUND.md` §3.5 names that GR does not state as entries; the fourth the glue rows (§6) the
program's derivation reads at nodes that are not first-order, as §3.5 reads them off the
derivations [read]. A program's line is never "accepted".

| program | stated entries | not stated (GROUND.md §3.5) | glue rows (§6), not stated [read] |
|---|---|---|---|
| P1 `cImmBorrow` | 5 PROVED, 2 NOT BUILT | — | `BindRowM`, `AppRowM` (`ForceRowM` proved) |
| P2 `cRecBorrow` | 5 PROVED, 2 NOT BUILT | `withload` at `methodsTy` (no cell), `free` at `methodsTy` | `BindRowM`, `AppRowM` at `U` slots; `Proj₁RowM` |
| P3 `cBang` | 2 PROVED | — | `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM` |
| P4 `cInst` | 2 PROVED | — | `AllERowM` at `'a` in scope, `AppRowM`, `BindRowM` |
| P5 `readFields` | 3 PROVED, 2 NOT BUILT | `withbor` (1) at `Pt.valTy`; the field loader and `readCell`'s loader [cb]; `withload` at `B` in `readCell` | `LetPairRowM` at `Imm ⊗ Imm`; `BindRowM`, `AppRowM` |
| P6 `mutFields` | 3 PROVED, 1 NOT BUILT | `mutBorrower` [cb]; `withbor` (2); `forgetMut`, `alloc`, `free` [G5c] | `LetPairRowM` at `Mut ⊗ B` |
| P14 `exProg` | 2 PROVED | — | `BindRowM` at a `U` slot, `Proj₁RowM` |
| P15 `build3`, P16 `matchSome`, P17 `bagProg` | roots PROVED; P17's `pushG` PROVED | P16's borrower and loaders [cb] and its constants; P17's `pushBorrower` [cb], `withbor` (2), `withswap`, the folds | P16: `BindRowM`, `AppRowM`; P17: `LetPairRowM`, `BangERowM`, `LolliERowM` |
| P7, P8, P18, P19, P9, P20–P24 | 10 roots and 5 callbacks PROVED; 2 borrow constants NOT BUILT | `readOne`, `readBoth`, `swapFn` and their loaders [cb]; `withswap`, `copy`, `withload` inside them | `AllEVRowM`, `LolliERowM` at `readOne ()`, `readBoth ()`, `swapFn ()` (D1, D9); `LetPairRowM` at families |
| P10, P11, P25–P29 | 7 roots, 5 algebras, 2 free algebras PROVED | the borrowers at `g : fTy` (NB, P10's V2 list); `foldImm`, `foldOwn`, `withbor` (1); P27's loader [cb] and its `withload` at `I32` | `progOpen`'s nodes at `g : fTy` (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`); `BangERowM` |
| P30, P31 | 2 roots PROVED; P30's open root NOT BUILT | `borrowerM` (D6); `withbor` (2), `withswap`, the folds | the glue at `U` slots |
| P32, P34 | 2 open roots NOT BUILT | the values (`mapInc`, `toPure` [G5v]; `countFree`); the borrowers | the glue at `U` and `!U` slots |
| P33 `countProg` | 1 PROVED, 4 NOT BUILT | `CountNW`; `freeAll` [G5v]; the borrower; `withbor` (1) | as its root: `BindRowM`, `LolliERowM`, `AppRowM`, `LetPairRowM`, `UnitERowM` |
| P12, P35–P41 | 8 roots, `counterStep`, `cntCb`, `passCb`, `incV` PROVED; `passF`, `withbor` (3) NOT BUILT | the scope callbacks [cb]; `ofFnStep`, `onceE`, `mkCounterV`, `doubleStep`, `logStep`, `twiceV`, `reV` (NB, `LamRowM`); `reCb`, `logInner`, `logCb` [cb]; `withbor` (1), (2), `withswap`, `unfoldN` | `d_mkBox`'s and `d_closeBox`'s nodes: `BindRowM` at a `!U` slot, `BoxIRowM`, `WithIRowM`, `NuInRowM`, `BoxERowM`, `Proj₂RowM`, `LetPairRowM` |
| P13 `arrProg` | 3 PROVED | `arrNew`, `arrFree` (NB); `arrReplace`, `arrSize`, `hostOp` [G5c] | `BangERowM` at `arrNew`'s and `arrFree`'s `!` |
| S1 `pairLoad` | 8 PROVED, 2 NOT BUILT | — | none |
| S1′ `pairLoadU` | 8 PROVED, 2 NOT BUILT | — | none |
| S3 `bangUse` | 5 PROVED, 5 NOT BUILT | the inner load's callback [cb], `hostOp` add [G5c] | `BangERowM`, `AllEVRowM` (stated as entries) |
| P42 (×13) | 13 roots PROVED | every other node: NOT BUILT, `DraftFLEmbed` at `d_X` | through G12 |
| P49 `recLog` | 1 PROVED, 2 NOT BUILT | `boundedFix` (`BoundedFixRowM`), `withswap` | `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM`, `LetPairRowM`, `SumERowM` |
| P53, P54 | 3 PROVED | P53: as P27, and the destructor's `foldOwn`; P54: `allocS`, `free`, `freeS` [G5c] | P53: as P27 |
| P55 `allBelow` | 1 NOT BUILT | — | `LamRowM`, `VarRowM` |
| P56 `array-get.bc` | 3 PROVED, 2 NOT BUILT | the two callbacks [cb] (their derivations not extracted); `withbor` (1), `array_copy`, `array_get`, `array_new`, `array_len` | `AllEVRowM`, `LolliERowM` at `read ['y] v` (D1, D9); `BangERowM`; `LetPairRowM` at families |
| P59 the I/O models | 4 PROVED, 2 NOT BUILT | `writeByteV`, `readIntoV` (as `AccReadByte`) | `LetPairRowM`, `SumERowM` at `Mut` and slice slots |
| S4 `reconB′` | 2 NOT BUILT | — | — |

No program is claimed to meet the floor. The suite claims the entries it states, no more.

### 10.5 The seeds

- **S1, `withload` of a pair** (`pairLoad`, `pairLoadU`): the closed programs are new, built from
  `cImmBorrow`'s skeleton with `borrower`, `borrowBody` and `d_borrower`; `pairLoadU`'s borrower
  binds the loader first (`borrowBodyU`), since at `withloadU`'s type the load is applied to the
  view and the callback at once. Both run, leaving no cell (`pairLoad_eval`, `pairLoadU_eval`).
  Every entry but the borrow constants' is PROVED (`accPairLoad_but_constants`, GR:1915). The two
  loads' nodes are `NxGuardPair.lean`'s `PairWithloadTyped` and `PairWithloadUTyped` nodes, under a
  closed program. So the pair's open question is in the `withload` constant's row (`DraftFL` at that
  node), not in any judgement of the program's own terms.
- **S2, `withload` of a slice**: P46 is not available here (§10.2); P56 serves, at five cells.
  `sliceLoad` is not built: P56 serves.
- **S3, the user's case** (`bangUse`): `body : !(∀'z ⊏ ⊤. Imm 'z I32 ⊗ I32 ⊸ ['z] I32)` holds no
  resource, is written at the top of the program, and is called inside the load's callback at the
  callback's own lifetime. It is written in place, as the checker writes a `def` at its use. It
  answers `(7, 8)` (`bangUse_eval`). The producer, the call, both callbacks and the root are PROVED
  (`accBangUse_proved`, GR:1923); the carry side's glue (`unbang body`, `body ['z]`) and the three
  borrow constants are NOT BUILT. The slot-carried form is P33: its producer `stepV` and carry side
  `cbE` wait on the binder-named push at a persistent context (D5).
- **S4, `reconB′`**: recorded, NOT BUILT; tier 2.
- **S5, `loadKeepsView`**: not built (optional, D3). Its gate fails `OwnOKI.placeFree` at the
  needed entry, and stays so after part (3), whose relaxed `placeFree` is for blocks only
  (`GROUND.md` §3.6).

### 10.6 The corpus programs

The checker's acceptance of a corpus file is a `CDerives` derivation (`checkProgram_sound`,
`Frontend/Check/Program.lean:148`). The suite takes in P56 (`array-get.bc`) by the checker route;
`sum-prog-exact.bc` and `count-down-exact.bc` erase exactly to Core's `sumProg` (P29) and
`countDownProg` (C) (`Frontend/Check/CrossCheck.lean:116`–`:140`). P57 (`slice-imm.bc`) and P58
(`lend-lib-each.bc`) are not taken in (§10.2).

The other files `scripts/check-corpus.sh` checks (`corpus/*.bc`, `corpus/surface/*.bc`,
`corpus/axes/*.bc`: 155, of which `forms.bc` is `-- check: parse-only` and `13-1-library.bc` has no
`main`) are classed here by the primitives of their erased `main` (`bcc erase`). **E**: an effect
primitive (`perform`, `raise`, `hnd`, `ubind`, `ccatch`, `cfin`), the forms the effect rules type.
Otherwise borrow-only or codata, split by whether the erasure lends cells (`load`, `store`) or
arrays and slices (`tab`, `idx`, `split`). [read: the class is read off the erasure, not off the
derivation. The checker erases the handlers it can (a resume-once operation as a call, an abortive
one as a branch), so an erasure with no effect primitive uses no effect rule. `withbor`'s erasure
holds no primitive, so the last group may still lend.] None of them has a Lean derivation in this
suite. Each B file is a floor obligation, and the last column names the suite entries nearest its
shape [read]. None is "covered".

| class | files | nearest suite shape [read] |
|---|---|---|
| B, arrays or slices (`tab`, `idx`, `split`), 40 | `array-empty`, `array-get` (P56, taken in), `array-refs`, `array-replace`, `array-sum`, `axes/borrow-across-loop`, `axes/codata-coeffects`, `axes/scope-boxed-iter`, `axes/scope-loop-lend`, `bytes-upper`, `effects-fold-sum`, `effects-map`, `effects-map-hand`, `fields`, `find-bytes`, `for-adapters`, `for-data`, `for-return`, `format`, `hello`, `http-request`, `io-aoc`, `iter-mut`, `iter-mut-count`, `iter-mut-slice`, `json-tokens`, `labels-json`, `lend-lib-each` (P58), `lend-lib-loop`, `print-borrowed-array`, `quicksort`, `rec-deep`, `reverse-bytes`, `slice-imm` (P57), `slice-lib`, `slice-mut`, `slice-split`, `sort-numbers`, `split-at-mut`, `surface/array-sum` | P13, P56, P59; S2 (and the untaken P43–P48, P57, P58) |
| B, cells lent or loaded (`load`, `store`), no array, 27 | `13-2-sum-prog`, `aff-capture`, `aff-coerce`, `aff-counter`, `aff-depth`, `aff-drop`, `aff-higher`, `axes/data-coeffects`, `axes/effects-coeffects`, `axes/result-fold-imm`, `axes/scope-data-effects`, `block-swap`, `borrow-in-scope`, `effects-generic`, `family-swap`, `fn-lifetime`, `implicit-drops`, `iter-close`, `lend-config`, `lend-lib-gen`, `lend-mut`, `lend-server`, `map-reuse`, `sum-i32`, `sum-prog-exact` (Core's `sumProg`, P29), `surface/family-swap`, `surface/map-reuse` | P1, P5, P6, P8, P9, P12, P27, P29–P31, P35–P41; S1, S3 |
| B or C, neither, 37 | `axes/codata-effects`, `axes/codata-generic`, `axes/data-effects`, `axes/free-monad`, `axes/result-fold-own`, `axes/scope-codata-effects`, `capture-log-hand`, `capture-store-cancel-hand`, `capture-tick-hand`, `clone-reuse`, `count-down`, `count-down-exact` (Core's `countDownProg`, C), `count-fold`, `count-try`, `deep-list`, `div-hof`, `for-finite`, `int-arith`, `int-ops`, `io-break`, `io-cat`, `io-for-after`, `io-for-assign`, `io-for-then`, `io-fuel`, `io-guess`, `io-head`, `io-hex`, `io-lines`, `io-sections`, `io-upper`, `io-wc`, `iter-range`, `main-lifetime`, `nats-sum`, `surface/io-upper`, `surface/io-wc` | P14–P16, P28, P59; the `io-*` files are open at the externs `stdin`, `stdout`, as P60 |
| E, 49 | `ascii-upper`, `capture-take-hand`, `clause-captures`, `core-effects-borrow-abort`, `core-effects-borrows`, `core-effects-drop-glue`, `core-effects-loop`, `core-effects-reborrows`, `core-effects-result`, `core-effects-tail`, `core-yield-loop`, `core-yield-pull`, `effects-borrow-raise`, `effects-fold`, `effects-log-fail`, `effects-map-fail`, `for-data-div`, `for-never`, `gen-adapters`, `gen-adapters-fail`, `gen-borrowed`, `gen-cell`, `gen-close`, `gen-div`, `gen-fib`, `gen-from`, `gen-nested`, `gen-pipeline`, `gen-pipeline-adapters`, `gen-produce`, `gen-return`, `gen-value`, `key-value`, `lend-div`, `lend-pipeline`, `parse-int`, `rec-emit`, `rec-even-odd`, `rec-fib`, `rec-layer`, `rec-log`, `rec-mixed`, `rec-overflow`, `rec-parser`, `rec-tree`, `rec-yield`, `sort-lines`, `trim-replace`, `utf8-count` | the next suite (§10.7) |
| not a program | `13-1-library` (its `def`s erase to Core's library terms, `library_erasures`), `forms` (parse-only) | — |

`corpus/sugar/`'s pairs are classed by their core forms (`*.core.bc`, 34): `for-value`, `gen-div`,
`gen-from`, `gen-range`, `gen-return`, `gen-yields` are E; the other 28 hold no effect primitive.
`corpus/reject/`, `corpus/pending/` and `corpus/fail/` are not accepted by Core and are not floor;
`corpus/reject/gen-self-borrow.bc` is the draft's target beyond the floor (tier 2).

### 10.7 Not in this suite

- **The effect programs** (E above, and Core's `EffPrograms.lean`, GhostEnd's `Tuple`, `Capture`,
  `Instance`, `Branch`, `Callee`, Targets' `d_storeCancelNU`, NonVacuity's `d_forgetBody`) are
  tier-1 floor. They read the draft's `F_Σ` clause (GhostEnd's piece) at the pushed stack where a
  lend is open, and the unwinding callback rows. They belong to the next suite.
- **The codata programs** (C) read `ν` through Core's `cC`, equal (`cRLMTopNuEq`); their other
  draft nodes, a persistent step and `unfoldN`, are read by the affine programs.
- **X** (`GROUND.md` §3.4): GhostEnd's `Kernel`, Recursion's `stepV_derives` (CBPVWorld's own
  `CDerives`), SecondClass's derived rules, Grades', Outlives' and CBPV*'s own judgements.
