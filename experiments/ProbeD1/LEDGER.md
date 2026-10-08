# ProbeD1: the grounding ledger

This file sets every ProbeD1 definition that has a Core counterpart against that counterpart, says
how the two relate, and names the Lean theorem behind each claim. `GROUND.md` is the design (§2 the
ledger, §3 the suite, §4 the block). The theorems are in `ProbeD1/GroundLedger.lean`; the
regression suite is in `ProbeD1/GroundRegress.lean` and its results are in the second half of this
file. The block entry, part (3), is §11; its gate and the rows it attempted are in
`ProbeD1/GroundBlock.lean`.

**Conventions.**
- **The two sides.** The draft is the one draft relation `vRLM`/`cRLM`/`effRetM`/`gRLM`/`SemSM` at
  `.binder0` (`R1.lean:155–263`). Core is `vCE`/`cC`/`effRet`/`gDenC`/`SemC`
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
  a row names the file in full. "GL" is `GroundLedger.lean`, "GR" `GroundRegress.lean` and "GB"
  `GroundBlock.lean`.

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
| G3 | `VRLMNilTy` | `vRLMNilTy` (:872) | at the empty stack, at `NilTy` (flat, `Mut`, `Imm` and their products, sums, boxes, `Ref`s and families) the draft relation is Core's: `CohS` and `RetainedPay` hold at `[]` (`cohS_nil`, `retainedPay_nil`) |
| G4′ | `CoreSubWNil` | `coreSubWNil` (:905) | at the empty stack Core inside the draft at `NilVal`/`NilComp` types, **thunks included, for every semantic value**: `[]` has only the identity instantiation (`vRLM_thunk_nil_iff`) |
| G5′ | `CoreToSemSMNil` | `coreToSemSMNil` (:971) | the floor at the empty stack at `NilComp` judgements over `CtxNil` contexts, constants included |
| G6 | `SemSMNil`, `SemSMNilOfSemSM`, `DraftFL`, `DraftFLNil` | `semSMNilOfSemSM` (:948); the floor statements (:955, :960) *stated* | `SemSM` gives `SemSMNil`; the floor at every index and at `[]` is stated, not claimed |
| G7 | `GuardPVNil`, `RelendJNil`, `VRLMThunkNil`, `CRLMArrNil`, `CRLMAllNil`, `CRLMAllTop`, `CRLMRetNil`, `SemIdxMNil`, `VRLMBangNil`, `KeepsTKeeps` | `guardPVNil` (:582), `relendJNil` (:614), `vRLMThunkNil` (:630), `cRLMArrNil` (:644), `cRLMAllNil` (:697), `cRLMAllTop` (:719), `cRLMRetNil` (:752), `semIdxMNil` (:983), `vRLMBangNil` (:1002), `keepsTKeeps` (:1017) | the empty-stack unfoldings; `CRLMRetNil` is both directions at a flat answer at every row. `CRLMAllNil`, `CRLMAllTop` and `cRLM_all_binder0` unfold the `∀` clause with its block conjunct (part (3), §11) |
| G7′ | `VRLMLeafDefault`, `CRLMTopNuEq`, `CRLMAmpOfComp`, `EffRetMOfAns`, `CRLMRetFlat` | `vRLMLeafDefault` (:1032), `cRLMTopNuEq` (:1042), `cRLMAmpOfComp` (:1051), `effRetMOfAns` (:743), `cRLMRetFlat` (:776) | the clause unfoldings at every stack |
| G8 | `ArisesITW`, `ArisesINilOfTW` | `arisesITW` (:1064), `arisesINilOfTW` (:1106) | the revised arising set's worlds are tagged `TW` worlds; every tagged `TW` world arises at the empty stack |
| G9 | `ProbeRulesOfNU` | `probeRulesOfNU` (:1114) | every `CDerivesNU` program is a `ProbeRules` program |
| G10 | `AdequacyNilM` | `adequacyNilM` (:1126) | the draft's judgement at the empty stack at `F 1` gives Core's adequacy (`theorem32D`) |
| G11 | `NotTabOfTWPointwise`, `ArisesIArises` | `notTabOfTWPointwise` (:1144), `arisesIArises` (:1172) | the pointwise table fails at `innerView`; the revised arising set is inside the first |
| G12 | `DraftFLEmbed` | *stated* (:1217), not attempted | the floor at BoLo's image |

**The classes are non-vacuous at the suite's types**: `FlatTy` holds at `1`, `I32`, `Ref 1`,
`Ref I32`, `L` and the other data lists; `FOArg` at every `Mut 'x T` and `Imm 'x T`, at
`Imm 'x 1 ⊗ Imm 'x 1`, at `array_imm 'z I32`; `FOComp` at every callback body `A ⊸ F B` with those
arguments and a flat answer. The entries that read them are in §10.

---

## 2. Rows: the relation's clauses

All draft lines are `R1.lean`; all Core lines are `Core/Relation.lean` unless named.

| # | draft | Core | at `σ = []` | at `σ ≠ []` | theorem | what a disagreement means for programs |
|---|---|---|---|---|---|---|
| C0 | `WInsideCoreM`, `CoreInsideWM` (:860, :867) | `vC` at `extS δ σ αs` | at first-order arguments W ⊆ Core (G2); at flat types equal (G1); at `NilTy` equal (G3) | at first-order arguments W ⊆ Core (G2), at flat types equal (G1); in general *stated*, not attempted | `gRestrict` (GL:394), `vRLMFOArg`, `vRLMFlat`, `vRLMNilTy` | a consumer that hands a draft value to Core's clause, or reads Core's answer back, is covered only at first-order and flat types. At `U C` `CoreInsideWM` would read the `U` clause at instantiated readings, where Core's relation of a value known at one reading is not given [read] |
| C1 | `vRLM` `U` (:157) | `vCE` `U` (:127) | Core ⊆ draft given bodies, for every semantic value: the draft reads the body at every extension that keeps the tags (`KeepsT`), Core's at every extension (`vRLM_thunk_nil_iff`, GL:623); so Core ⊆ draft at `NilComp` bodies (`coreSubWNil`) | incomparable [read]: instantiations at the stack's cut, views handed back, `guardPV`. For a closed first-order value Core relates at every reading, Core ⊆ draft (`coreValToW`) | `vRLMThunkNil`, `coreSubWNil`, `coreValToW`, `coreToSemSMConst` | at `[]` every Core thunk with a `NilComp` body is a draft thunk; at a stack, first-order constants and first-order callbacks are covered (G5c, the producer lemmas, §10) |
| C2 | `vRLM` `⊗`, `⊕`, `[@a]`, `Ref`, `[L]` (:164, :166, :171, :173, :188) | :121, :124, :131, :132, :149 | same clause | same clause, leaves at `extS δ σ αs` | equal at flat components (`vRLM_flatE`); inside Core's at first-order components (`vRLM_foArg`) | none |
| C3 | `vRLM` `!` (:169) | :130 | draft ⊆ Core given the payload (`PBox` added at a thunk payload); equal at a flat non-thunk payload (`vRLM_flatE`'s `bang` case); at a thunk payload the box is every box sequence from `([], [])` (`vRLMBangNil`) | the same | `vRLM_flatE`, `vRLMBangNil` (GL:1002) | a persistent thunk must hold at every box world (D4). For a first-order persistent value Core derives at a dead context, it does (G5c) |
| C4 | `vRLM` `Mut`, `Imm` (:175, :179) | :137, :134 | equal (`vRLM_nilTy`'s leaf cases: `CohS` and `RetainedPay` hold at `[]`) | draft ⊆ Core: Core's leaf, plus `CohS` and `RetainedPay` (`vRLM_foArg`'s leaf cases) | `vRLMNilTy` (GL:872), `vRLMFOArg` (GL:239) | a consumer at a pushed stack must establish `CohS` and `RetainedPay` for the leaves it hands over (D7) |
| C5 | `vRLM` type variable (:183), environment `WEnt` (:77) | :143, `TEnt` (:72) | candidates; W's drop the mode and the list | the same | `EnvCore` (:1363), read by `vRLM_flatE` | none at flat types |
| C6 | `vRLM` `μ` (:184) | :144 | equal at flat bodies (`vRLM_flatE`, the induction with two least fixed points); with a thunk inside, *not stated* | the same | `vRLMFlat` | W reads a thunk inside `μ` with its own `U`; after (E1) the adjacency closure is a draft value (`muAdjVRLME1`, `NxE1.lean:77`) |
| C7 | `vRLM` default: `1`, `0`, `Unk`, `int`, `opq` (:191) | :120, :123, :140–142 | equal | equal at `extS` | `vRLMLeafDefault` (GL:1032, `rfl` at each type) | none |
| C8 | `cRLM` `F` (:198) | `cC` `F` (:155) | same clause (`wpTS`); equal at a flat answer | equal at a flat answer | `cRLMRetFlat` (GL:776), `cRLMRetNil` (GL:752) | none at flat answers |
| C9 | `cRLM` `F_Σ` (:199) | `cC` `F_Σ` (:165) | equal at a flat answer at every row (`bodyS_nil_iff`, `GhostEnd/Stacked.lean:476`) | GhostEnd's piece (a stop ghost-ends entries): no Core counterpart | `cRLMRetNil` (GL:752) | effectful callbacks at a pushed stack read the piece (out of this suite, §10.7); see D12 for blocks |
| C10 | `cRLM` `⊸` (:207) | `cC` `⊸` (:156) | same clause, guard trivial | same clause plus `guardPV` at the stack | `cRLMArrNil` (GL:644), `cRLM_arr_binder0` (GL:311), `guardPVNil` (GL:582) | a call at a stack needs the table and views of the composite (D9) |
| C11 | `cRLM` `&`, `⊤`, `ν` (:212, :215, :231) | :158, :160, :163 | `⊤` and `ν` equal (`ν` is Core's clause at `extS`); `&` the same clause given its components | the same | `cRLMTopNuEq` (GL:1042, `rfl`), `cRLMAmpOfComp` (GL:1051) | none |
| C12 | `cRLM` `∀` (:216) | `cC` `∀` (:161) | incomparable [read]: the first conjunct reads only instances in scope ((E1), `InScope`, :100), and the own-lend conjuncts (the single push `OwnPushM`, :106; the block push `OwnPushB`, `Block.lean:89`, part (3)) have no Core counterpart; at the top level the first conjunct reads nothing | the same | `cRLMAllNil` (GL:697) and `cRLMAllTop` (GL:719) unfold the clause; `cRLM_all_binder0` (GL:652) at every stack. Core's `∀` alone: holds at a `mut` cell adjacent to `⊤` and fails at one at `2` (`coreAllAdjacent`, `GapWitness.lean:127`), not invariant under an embedding that opens the room (`coreAllNotNatural`, :150), does not imply reading (A) at `σ = []` (`not_coreAllImpCutAll`, :156) | every borrow callback is checked at its own push: the producer side is covered for first-order callbacks (G5 with the rows, §10); the consumer side is each borrow constant's row (D1, D2) |
| C13 | `effRetM` (:234) | `effRet` (:176) | equal given the answer's clause | the same, at `extS` | `effRetMOfAns` (GL:743) | none |
| C14 | `gSepRLM`, `gRLM` (:242, :251) | `gSepC`, `gDenC` (:218, :224) | equal given the live slots' clauses; contained given containment | the same, at `extS` | `gRLMOfSlots` (GL:285) | none |
| C15 | `SemSM` (:257) | `SemC` (:228), `SemJ` (`Fundamental.lean:429`) | incomparable as definitions: `SemSM` adds `BindersLow`, `Scoped`, `SubDom` and the index [read]; at `[]` the index holds of every reading (`semSMNilOfSemSM`) | the same | `coreToSemSM` (GL:364), `coreToSemSMNil` (GL:971), `semSMNilOfSemSM` (GL:948) | Core's judgements at first-order types are the draft's at every index |

---

## 3. Rows: world, index, guard

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| W1 | `Stk`, `LEnt`, `LStack` (`World.lean:53`; `GhostEnd/Stacked.lean:99`, :107) | none: Core is `σ = []` | draft-only (§7) | — | — |
| W2 | `guardPV` (`Binder.lean:164`), `TabAtS` (`GhostEnd/Stacked.lean:290`), `PlaceViewsL` (`Binder.lean:144`) | `TW` read pointwise (`TabOfTWPointwise`, `HeldUnderTW`, `Statement1.lean:125`, :119); `TW`'s run invariant (statement 1's facts, `Statement1.lean:43–100`) | trivial at `[]`. Pointwise, the table is not read off one `TW` world: `TabOfTWPointwise` fails at `innerView`, a `TW` world, at a configuration not in `Arises` (`wpG_below_not_arises`): a fact about the pointwise statement. As a run invariant, `TabRelend` is proved (`tabRelend`, `Thunk.lean:185`) and the other eight facts are stated | `guardPVNil` (GL:582); `notTabOfTWPointwise` (GL:1144) | at a stack the guard restricts every call (D9); a guard proved only pointwise from `TW` is not available |
| W3 | `CohS` (`Binder.lean:178`) | `CohE` (:57) | different objects: a view tied to its lending entry, an `imm` cell tied to a record; `CohS` holds of everything at `[]` | `cohS_nil` (GL:819) | D7 |
| W4 | `OwnPushM`, `OwnOKI` (`R1.lean:106`, `Binder.lean:194`, :200); after part (3) also `OwnPushB`, `OwnOKB` (`Block.lean:89`, :72) | Core's `∀` instance (:161); 6.64/6.65's lend start (`TW.immFrame`, `TW.mutFold`, `World.lean:115`, :135) | *not stated*: the own push reads an instance as a lend | — | the single-place entry (D2), the block (§11) and `placeFree` (D3) |
| W5 | `Inst`, `InstAt`, `RelendJ` (`Binder.lean:314`, :346; `BinderJ.lean:53`) | Core's `U` quantifier over `Ext` (:127) | at `[]` `RelendJ` is Core's `U` with `KeepsT` added | `relendJNil` (GL:614) | D8 |
| W6 | `KeepsT` (`BinderJ.lean:49`) | `Keeps` (`FrameRecords.lean:156`) | draft ⊆ Core: a record kept with its tag is kept | `keepsTKeeps` (GL:1017) | D8 |
| W7 | `RecsOutside`, `SubOutside`, `SubFresh`, `LendFresh`, `OuterBelowTop`, `cutOf` (`Binder.lean:250`, :280, :285, :265, :242, :227) | [TR] 6.64/6.65 H4's fresh lifetime; nearest Core object `TW.reb`'s `StratumLe` (`World.lean:92`, :122) | draft-only bookkeeping (§7); each holds of every reading at `[]` (`subOutside_nil`, and `RecsOutside []`, `OuterBelowTop []` vacuous) | `semIdxMNil` (GL:983) | — |
| W8 | `PBox`, `BoxStep` (`R1.lean:137`, :125) | none: Core's `!` is `ρ = ∅ ∧ vC true A` | draft-only (§7) | `vRLMBangNil` (GL:1002) unfolds it at `[]` | D4, D5 |
| W9 | `StackJM`, `BindersLow`, `Scoped`, `SubDom` (`R1.lean:113`; `Sem.lean:66`, :74, :78) | `Scoped` ↔ `VScoped`; `Δ.Models` | `Scoped` is `VScoped` at the judgement [read]; the others draft-only; `StackJM` holds at `[]`; after part (3) `SemSM` reads `StackJB` and `StackOKB` (`Block.lean:107`, :41), which hold at `[]` | `stackJM_nil` (GL:930), `stackJB_nil` (GL:939), `stackOKB_nil` (GL:933) | a judgement binding a reserved name (`NsVar`) is outside `SemSM` (vacuous there) |
| W10 | `vwEW`, `vwSW`, `vwSL` (`Binder.lean:121`, :125, :159) over GhostEnd's `vwE` (`Stacked.lean:122`) | `ptoImmS`, `ptoMutS` (:51, :43) | the views read an `imm` payload at `vC true`, Core's `Imm` leaf at `vC false` [read] | — | at a payload holding a thunk the views ask more (D11) |
| W11 | `WP p` (`Sem.lean:119`) | `Targets.coreW` (`Targets/I/World.lean:165`) | stale: it reads statement 0's relation `vRL`, not `vRLM` [read] | — | nothing in this unit reads `WP` |
| W12 | `SemIdxM` (`R1.lean:957`), blocks admitted after part (3) (`StackOKB`, `StackJBase`) | `SemC`'s hypotheses: `Δ.Models δ` and `gDenC` | at `[]` it is `BindersLow`, `Scoped`, `SubDom` and `Δ.Models δ` | `semIdxMNil` (GL:983) | `PairCfg`, `SliceCfg` and the `RetainedPay*Row` rows read it |
| W13 | `SemSMC`, `gRLMC`, `gSepRLMC` (`R1.lean:814`, :806, :795), blocks admitted after part (3) | `SemC`, `gDenC`, `gSepC` | incomparable with `SemSM` as definitions [read] | none | a route device (`MonoOwnGMC`, `AllIRowMC`); no entry reads it |

---

## 4. Rows: arising against the typed world

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| A1 | `ArisesI` (`Binder.lean:582`) | `TW` (`World.lean:110`), `Tagged` (:171) | every arising world is a tagged `TW` world (draft ⊆ Core, worlds); at `[]` every tagged `TW` world arises (Core ⊆ draft); so at `[]` the world sets coincide | `arisesITW` (GL:1064), `arisesINilOfTW` (GL:1106) | a refutation at `[]` needs nothing beyond Core's arising |
| A2 | `ArisesI.lendImm`, `LendImmI` (`Arising.lean:106`; `Binder.lean:576`) | `TW.immFrame` (`World.lean:115`) | `LendImm` carries `TW.immFrame`'s premises, the push, and H4's freshness | inside `arisesITW` (the `lendImm` case is `TW.immFrame`) | — |
| A3 | `ArisesI.lendMut`, `LendMutI` (`Arising.lean:88`; `Binder.lean:571`) | `TW.mutFold` (`World.lean:135`) | the same | inside `arisesITW` (the `lendMut` case is `TW.mutFold`) | — |
| A4 | `RunEnd` (`Arising.lean:73`) | `wpTS`'s run conjuncts (`World.lean:186`) | `RunEnd` transcribes them at a fixed configuration [read] | — (`RunEndOfWpTS` not built) | — |
| A5 | (none) | `TW.immEnd`, `TW.mutUnfold` (`World.lean:151`, :140) | *not stated*: `ArisesI` has no lend-end transition | — | configurations after a lend ends are reached only through `run` |
| A6 | (no transition) | `TW.reb`, `rebDeep`, `rebEnd`, `rebEndDeep` (`World.lean:122`, :128, :157, :162); `wpG_reborrow` (`Reborrow.lean:232`) | *not stated*: `ArisesI` has no reborrow transition. The gate's witness uses `TW.reb` inside a world (`withloadUPairGapReal`). Statement 2 transcribes 6.150 (`rebView`, `rebF`, `RebRelend`, `RCarried`, `TabKeepsRec`, `RebFrameR`, `RebChooserNonVacuous`, `Statement2.lean:67–130`): stated, none proved | — | a configuration inside `withload`'s callback with its push on the stack is not in `ArisesI`; a refutation there cannot pass DESIGN §11 |
| A7 | `ArisesVI` (`Binder.lean:598`) | none: Core quantifies over all values in `TW` worlds | draft-only (refutation check) | — | at `[]` no `Imm` value arises except a run's answer, so a refutation at `[]` of an open judgement with a borrow-typed context cannot pass DESIGN §11 |
| A8 | `Arises`, `ArisesV`, `ArisesCtx` (`Arising.lean:134`, :158, :175); `ArisesAt` (:53); `ArisesNonVacuous` (:186) | `TW`, `Tagged` | the first arising set; `ArisesI ⊆ Arises` and `ArisesVI ⊆ ArisesV` | `arisesIArises` (GL:1172) | none: refutations read `ArisesI` |
| A9 | `ArisesSound` (`Statement1.lean:112`) | `TW` (through `ArisesAt`) | *stated*, not proved; used only to exclude a witness | — | none |

---

## 5. Rows: judgement, typing, statement 0, adequacy

| # | draft | Core | relationship | theorem | for programs |
|---|---|---|---|---|---|
| J1 | `ProbeRules` (`Rules.lean:31`) | `CDerives` (`Fundamental.lean:60`); `CDerivesNU` (`Targets/Base/Typing.lean:82`) | `CDerivesNU` ⊆ `ProbeRules`; `CDerivesNU` ⊆ `CDerives` (`CDerivesNU.toCDerives`); `ProbeRules` ⊄ `CDerives` (the spanning rules) [read] | `probeRulesOfNU` (GL:1114) | a Core program whose derivation uses no effect rule is built by the same constructors as a `CDerivesNU` one [read], but no theorem converts it, since nothing inverts `CDerives` |
| J2 | statement 0 (`Statement0M`, `R1.lean:1455`; `statement0MBesideMono0`, `R1Stmt0.lean:460`) and the draft rows | `fundamentalC` (`Fundamental.lean:434`) | the draft has rows at `force`, `thunkF`, `thunkV`, the two `!U` rows (with `PersistentBoxed`), `∀I` (contexts reaching no `U`), `roll`, `unroll`; Core proves all 89 constructors. At first-order judgements Core's derivation gives the draft's (G5) | `coreToSemSM` (GL:364); `DraftFL`, `DraftFLNil` *stated* | §6 lists the rows |
| J3 | `semTyping`, `GenSelfAccepted`, `ReconAccepted` (`Programs.lean:38`, :42, :46) | Targets' `AcceptedAt` (`Targets/I/Programs.lean:259`); `adequacyD` | stale: `semTyping` reads `SemS` (`Sem.lean:102`), statement 0's relation `vRL` [read] | — | statement 5's acceptance is not stated at `vRLM` |
| J4 | (no adequacy theorem before this unit) | `adequacyD` (`Demonic.lean:312`), `theorem32D` (:292) | the draft's acceptance at `[]` at `F 1` gives Core's adequacy | `adequacyNilM` (GL:1126) | the draft's floor inherits safety and termination at `[]` |
| J5 | `NilSoundRet`, `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` (`Statement0.lean:95`, :154, :161, :167, :173, at `vRL`); `NilSoundRetM` (`R1.lean:1394`) | OQ-58 (a) | at `vRLM`: `NilSoundRetM` proved one way at data (`nilSoundRetM`); both ways at a flat answer (`cRLMRetNil`); Core inside the draft at `NilVal`/`NilComp` types, thunks included (`coreSubWNil`). The `vRL` statements are at a superseded relation (§9) | `cRLMRetNil` (GL:752), `coreSubWNil` (GL:905) | OQ-58 at `vRLM` is answered at `NilComp` types (Core inside the draft) and at flat types (equal) |
| J6 | `DraftFLEmbed` (GL:1217) | `embed` (`Embedding.lean:235`), `adequacy_of_derivesWf` (:326) | the floor at BoLo's image: *stated*, not attempted | — | the paper's own programs are its instances (§10, P42) |
| J7 | the callback steps `CallbackExtMutM`, `CallbackExtImmM` (`R1.lean:1421`, :1437), `.arr` shape, proved (`callbackExtMutM_own`, `callbackExtImmM_own`, `R1Stmt0.lean:412`, :431); `CallbackExtMutMF`, `CallbackExtImmMF` (`Nx.lean:472`, :489), thunked shape, *stated* | the callback step inside `withbor1_compatX` … (`Compatibility.lean:937`); unwinding forms (`EffBorrow.lean`) | *not stated*: the draft reads the callback at its own push, Core at an instance [read] | none | the draft step of every `withbor` K entry; at the thunked shape Core's non-unwinding programs use, stated and not proved |
| J8 | `PairWithloadTyped`, `PairWithloadUTyped` (`Nx.lean:197`, :204; proved, `pairWithloadTyped`, `pairWithloadUTyped`, `NxGuardPair.lean:582`, :578); `SliceTyped`, `SliceUTyped` (`Nx.lean:334`, :341; stated); `pairProgU`, `sliceProgU` (`Nx.lean:62`, :261) | `CDerives` through `CDerivesNU` | the statements are at `ProbeRules`; the proofs build `CDerivesNU` derivations, so the derivations are Core's by `CDerivesNU.toCDerives` [read] | none | `pairProgU pCbE` is the open node at the view of S1's enclosing lend (§10) |

---

## 6. The rows against `fundamentalC`

One line per `CDerives` constructor (`Fundamental.lean:60–372`), with the lemma `fundamentalC`
applies (`:437–543`) and the draft row. A draft row is the constructor's statement at
`SemSM .binder0`; the rows not proved are stated in GL (:1204–:1445) under the names below. At a
first-order judgement G5 gives the node from Core whatever the rule; at a first-order constant at a
dead context G5c does.

| constructor | Core lemma | draft row | status |
|---|---|---|---|
| `var` | `var_compatC` | `VarRowM` (GL:1229) | stated |
| `unitI` | `unitI_compatC` | `UnitIRowM` | stated; G5 at every dead context |
| `tensorI` | `tensorI_compatC` | `TensorIRowM` | stated |
| `sumI₁`, `sumI₂` | `sumI₁_compatC`, `sumI₂_compatC` | `SumI₁RowM`, `SumI₂RowM` | stated |
| `thunkF`, `thunkV` | `thunkF_compatC`, `thunkV_compatC` | `ThunkFRowM`, `ThunkVRowM` (`R1.lean:445`, :450) | proved (`statement0UFullM`, `R1Box.lean:601`) |
| `ret`, `ofRet` | `ret_compatC`, — | the identity (`jdgCty`) | trivial |
| `bind` | `bind_compatC` | `BindRowM` | stated |
| `force` | `force_compatC` | `ForceRowM` (`R1.lean:1413`) | proved at `binder0` (`forceRowM`, `R1Stmt0.lean:379`) |
| `lam` | `lam_compatC` | `LamRowM` | stated |
| `app` | `app_compatC` | `AppRowM` | stated |
| `withI`, `proj₁`, `proj₂`, `topI` | `withI_compatC`, `proj₁_compatC`, `proj₂_compatC`, `topI_compatC` | `WithIRowM`, `Proj₁RowM`, `Proj₂RowM`; `topI` is `True` | stated; `topI` trivial |
| `unitE`, `tensorE`, `sumE`, `zeroE` | `unitE_compatC`, `tensorE_compatC`, `sumE_compatC`, `zeroE_compatC` | `UnitERowM`, `LetPairRowM`, `SumERowM` | stated (`zeroE` not stated) |
| `allI` | `allI_compatC` | `AllIRowMAt` (`Nx.lean:515`) | proved at contexts reaching no `U` (`allIRowMUFree0`, `NxAllI.lean:303`), the block conjunct included after part (3); open at a live `U` slot (D6) and at a persistent slot, whose push is binder-named (`VRLMStackRename`, D5) |
| `allE`, `allEV` | `allE_compatC`, `allE_compatX` | `AllERowM`, `AllEVRowM` | stated; their step `InScopeOfInterp` (`Nx.lean:399`) stated (D1) |
| `bangThunkF`, `bangThunkV` | `bangThunkF_compatC`, `bangThunkV_compatC` | `BangThunkFRowM`, `BangThunkVRowM` (`R1.lean:457`, :463) | proved with `PersistentBoxed` (`statement0UFullM`) |
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
| `withbor1`, `withbor2`, `withbor3` | `withbor1_compatX` (`Compatibility.lean:937`), `withbor2_compatX`, `withbor3_compatX` | `Withbor1RowM`, `Withbor2RowM`, `Withbor3RowM` | stated; consumer facts `CallbackExt*M` (`.arr` shape) proved, `CallbackExt*MF` (thunked) stated; at `[]` `Withbor1NilRowM` (GB:978) stops at the payload in 6.64's frame (§11.5) |
| `withload` | `withload_compatX` (`Compatibility.lean:252`) | `WithloadRowM`; at `[]` `WithloadNilRowM` (GB:984) | stated; its draft step is the gate (§10), proved at the pair and at an array of `I32` after part (3); the row at `[]` stops at (l3) (§11.5) |
| `withswap` | `withswap_compatX` | `WithswapRowM` | stated |
| `withbor1U` … `withbor3U`, `withloadU`, `sliceBorrowMU`, `sliceBorrowIU` | `*U_compatX` (`EffBorrow.lean`) | `WithloadURowM` (empty row), at `[]` `WithloadUNilRowM` (GB:990); the spanning rows `SpanW1Row`, `SpanW2Row`, `SpanLoadRow` at `SemS` (§9) | stated |
| `lolliE` | `lolliE_compatX` | `LolliERowM` | stated (D9) |
| `roll`, `unroll` | `roll_compatX`, `unroll_compatX` | `RollRowM`, `UnrollRowM` (`Nx.lean:383`, :388) | proved (`rollRowM`, `unrollRowM`, `NxUnroll.lean:420`, :430) |
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
| D2 | the own push lends one place (`OwnPushM`). After part (3) the `∀` clause also reads a block of two or more entries at one lifetime, at a callback whose argument fits them (`OwnPushB`, `BlockFits`, `CbArg`); the gate passes at the pair and at an array of `I32` at the empty stack (§11) | a consumer handing its callback several cells at one lifetime. After part (3) the block gate passes at the empty stack; its guard lemma holds at every stack under hypotheses discharged only at `[]`; at the arising configuration (`withloadUPairGapReal`, the enclosing lend's stack) the block gate is not attempted; the rows at `[]` stop at (l3) (§11.5) | S1 (two cells); S2: P46's `withload` at `array i32` (ten cells), P48's two, P43's, P47's, P56's (five), P58's, P57's slice lend; one cell, the positive controls: P5's `withload` of a record, P16's of a variant, P33's of a list cell; no cell: P1, P2, P27's leaf load |
| D3 | `OwnOKI.placeFree`: the callback holds no cell at the lent place, at any depth (a block's `OwnOKB.placeFree` admits `own` cells frozen under an `imm` ancestor) | a callback holding a copy of the view whose witness owns the reborrowed places; at the rows, a callee's resource the frame rule and [TR] 6.150 hand over at the predicate level (§11.5) | S5 |
| D4 | `PBox`: a persistent thunk holds at every box world | a persistent value Core accepts that misbehaves at a phantom push | P3; the steps of P12, P35–P41; P13's `tab10V`, `dropI32V`; the algebras of P10, P11, P25–P27, P29; P33's stages; the persistent defs of P43–P48; P52's `incCb`; P42's `callBorrowed`; P60's externs. At a first-order persistent value Core derives at a dead context the box holds (G5c) |
| D5 | the box carries only reserved-name pushes | a persistent context value across the `∀I` row's binder-named push | P33 (`stepV` at `g : countTy`; `cbE` and the borrower capturing `g`), P34, the borrowers at `g : fTy` (P10, P11, P25–P27, P29); P58 (`k`); P42's `fnMut`; the `lend_*` combinators of P43–P45; P60 (`write_byte`) |
| D6 | the `∀I` row at a live `U` slot is not derived | a callback capturing a closure | `withborF2` (P7, P8, P18, P19), `withborS` (P9, P20–P24), `borrowerM` (P30–P32); the optics (P50–P52) [read] |
| D7 | `CohS`, `RetainedPay` at a pushed stack, and at answers holding a borrow leaf | arguments a consumer must hand over with these; answers that return a view | P6 and every `withswap`; `copy` at `Imm` (P5, P7, P21); every `array_get` and `array_copy`; P39's `passF`, P41's `logStep`, P49's answer, P55's answer, P42's `captures`, P59's answers |
| D8 | `KeepsT` in the `U` clause | a thunk forced at a list that keeps a relevant record without its tag [unchecked: runs keep tags] | P2 (forces a thunk after the lend) |
| D9 | `guardPV` at `⊸` and `∀` | a call inside a callback whose composite fails the table | the glue at `readOne ()`, `readBoth ()`, `swapFn ()` (P7, P20–P22), the borrowers' `g [] b`, P33's `cbE`, the calls of persistent defs inside a lend's callback (P43–P48, P58, P60). All NOT BUILT. G5 closes a first-order callback without reading the guard, so no PROVED entry reads D9 |
| D10 | W's own `μ`, `[L]`, type variables | a thunk inside `μ` read by W's `U` | the list and tree programs, P17's bag, P13's arrays, the loops' unary counts and families of P43–P48, P59's `Bytes`. At flat `μ` and `[L]` the draft is Core's (G1) |
| D11 | the views read an `imm` payload at `vC true` | a lend whose payload holds a thunk | P2 (`withbor` at `methodsTy`); P42's `callBorrowed` and `captures` |
| D12 | after the block (part (3), `GROUND.md` §4.2): a stop at a stack holding a block | effectful code that stops at a stack holding a block: (i) its resumable stops, read over GhostEnd's strict re-lends, which split a block; (ii) its stops crossing the block, where `ghostS` treats the innermost entry only [unchecked] | none in this suite: borrow-only programs read no `F_Σ` row. Its two obligations and their reach are §11.7 |

---

## 9. Superseded relations

Each earlier draft relation stays as the statement it was. The ledger lists them so that no result
is read at the wrong relation.

| family | definitions | to `vRLM` | results and doc claims that rest on it |
|---|---|---|---|
| W₀ | `vRL`, `cRL`, `effRet`, `gRL` (`Relation.lean:108`, :131, :160); `SemS` (`Sem.lean:102`); `SemSR` (`Thunk.lean:227`); `WP` (`Sem.lean:119`) | no `CohS`, no `RetainedPay`, no instantiations: the `U` clause is GhostEnd's `RelendableS` under `guardW` | statement 0's bundle and shared lemmas (`Statement0.lean`; `statement0Shared`, `Shared.lean:19`; `nilSoundRet`, `Bridge.lean:133`); the rows of `Statement0.lean`, `Rows0.lean`, `Thunk.lean`; statements 1–4 and 6 (`LamRow`, `AllIRow`, `BelowRow`, `SpanW1Row`, `SpanW2Row`, `SpanLoadRow`, `HandleRow`, `ThenRow`, `semTyping`, `GenSelfAccepted`, `ReconAccepted`); OQ-58's `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` |
| W revised | `vRLI`, `cRLI`, `gRLI`, `SemSI` (`BinderW.lean:42`, :66, :115, :122) | an earlier revision: `CohS` without `RetainedPay`, `RelendI` for `RelendJ`, no `μ`, `[L]` or type variable of its own, no (E1)–(E4), no box [read] | the binder unit's results (`BINDER.md`) |
| R1-before | `vRLJ`, `cRLJ`, `gRLJ`, `SemSJ` (`BinderJ.lean:72`, :98, :147, :152); `Statement0UFullJ` (:202) | `vRLM = vRLJ` at types with no `μ`, `[L]`, type variable, lifetime `∀` or persistent thunk (`RelMAgreesJ`, `R1.lean:345`; `relMAgreesJ`, `R1Thaw.lean:195`) | `gdBangJ` (`NxFloor.lean:55`); `GAP.md`'s adjacency at `vRLJ`; the rows `*RowJ`, `*RowTFJ`, `*RowKJ` |
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
`readArrayGet`, `readRoots`…`readOthers`, GR:431, :1246, :1612, :1734, :1774–:1849), so its
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
| `semSM_callbackW`, `semSM_algI`, `semSM_const`, `semSM_root`, `semSM_rootV`, `semSM_embedRoot` | :338–:370, :1275 | proved | the producer lemmas at Core's own shapes (`callbackW`, `d_algI`), G5c at a value, G5 at a closed program, G5 at `embed` |
| `LoadGateNil` | :256 | stated | `withload`'s draft step at the empty stack, both cases of `CohE` (`LoadPay`, :246). One hypothesis is added: `x ∉ CTy.binders (C' x)`. The own push names the binder, which the body must not bind again (`OwnPushI`); Core's typing does not exclude it |
| `FreePlaceExists` | :273 | proved in part (3) (`freePlaceExists`, `GroundBlock.lean:931`) | every resource leaves a place free at every depth: `Res` is finite at every depth (`deepFin`, `docs/adjudications.md` D10) |
| `loadGateNil_unit` | :315, from `loadGateNil_unit_of` (:277) | proved, from `FreePlaceExists` | the gate at a payload with no reborrowed cell (`1`), at callback types other than `.arr` or whose `ViewAt` holds; it reads neither the reborrow's structure nor the callback's freedom at the reborrowed places |
| S1: `pairLoad`, `pairLoadU` | :1091, :1129 | `d_pairLoad`, `d_pairLoadU` proved; `pairLoad_eval`, `pairLoadU_eval` by `decide` | `withload` of a pair of references, at `withload`'s type and at its unwinding type at the empty row (§10.5) |
| S3: `bangUse` | :1513 | `d_bangUse` proved; `bangUse_eval` = `(7, 8)` by `decide` | the user's case (§10.5) |
| P56: `corpus/array-get.bc` | :1648 | `arrayGetP_checks`, `arrayGet_shape`, `arrayGet_erasures` by `decide +kernel`; `arrayGet_derives` | the checker's derivation of the corpus file, and its `def`s' erasures checked equal to `tabE`, `readE` |

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
| P1 `cImmBorrow` | `AccImmBorrowRoot` (:377) | R | PROVED | `accImmBorrowRoot` [G5] |
| | `AccImmBorrowCb` (:381) | V | PROVED | `accImmBorrowCb` [cb] at `d_borrowBody` |
| | `AccImmBorrowLoader` (:385) | V | PROVED | `accImmBorrowLoader` [cb] at `d_loaderBody` (rebuilt from `d_loader`'s constructors) |
| | `AccImmBorrowWithbor` (:390) | K | NOT BUILT | `Withbor1RowM` |
| | `AccImmBorrowWithload` (:396) | K | NOT BUILT | `WithloadRowM`; its gate at `1` is `loadGateNil_unit` (`FreePlaceExists` proved in part (3)). At `[]`, `WithloadNilRowM` passes (l3) at `1` (`loadGateNilBI_unit`) and its next step reads the answer's `U` clause at the pushed stack (§11.5) |
| | `AccImmBorrowAlloc`, `AccImmBorrowFree` (:401, :405) | K | PROVED | `accImmBorrowAlloc`, `accImmBorrowFree` [G5c] |
| P2 `cRecBorrow` | `AccRecBorrowRoot` (:463) | R | PROVED | [G5] |
| | `AccRecBorrowMethods` (:467) | V | PROVED | `accRecBorrowMethods` [G5c] at `d_methods` |
| | `AccRecBorrowCb` (:471) | V | PROVED | [cb] at `d_borrowBody` |
| | `AccRecBorrowLoader` (:475) | V | PROVED | [cb] at `d_recLoaderBody` (rebuilt from `d_recLoader`'s) |
| | `AccRecBorrowWithbor` (:479) | K | NOT BUILT | `Withbor1RowM` (D11) |
| | `AccRecBorrowAlloc` (:484) | K | NOT BUILT | `AllocRowM` at a thunk payload |
| | `AccRecBorrowForget` (:488) | K | PROVED | [G5c] |
| P3 `cBang` | `AccBangRoot`, `AccBangClosure` (:525, :528) | R, V | PROVED | [G5]; [bt] |
| P4 `cInst` | `AccInstRoot`, `AccInstPoly` (:539, :542) | R, V | PROVED | [G5]; [cb→] |
| P5 `readFields` | `AccReadFieldsRoot`, `AccReadFieldsCb` (:554, :557) | R, V | PROVED | [G5]; [cb] at `d_readBody` |
| | `AccReadFieldsLoad` (:564) | K | NOT BUILT | `WithloadRowM` (one reborrowed cell: the positive control) |
| | `AccReadFieldsCopy` (:569) | K | NOT BUILT | `CopyRowM` (D7) |
| | `AccReadFieldsAlloc` (:573) | K | PROVED | [G5c] |
| P6 `mutFields` | `AccMutFieldsRoot`, `…Flip`, `…Poke` (:588–:595) | R, V, V | PROVED | [G5]; [G5c] at `d_flipG`, `d_pokeG` (`pokeG` lends inside its body) |
| | `AccMutFieldsSwap` (:599) | K | NOT BUILT | `WithswapRowM` (D7) |
| P14 `exProg`, P15 `build3`, P16 `matchSome`, P17 `bagProg` | the roots; `AccExProgPair`, `AccBagPush` (:615–:638) | R, V | PROVED | [G5]; [G5c] |
| P7, P8, P18, P19, P9, P20–P24 (family and block borrows) | the ten roots (:654–:663) | R | PROVED | [G5] |
| | `AccReadCb` (P7, P21), `AccSwapCb A` (P8, P9, P18), `AccNestCb` (P20), `AccNestReadCb` (P22), `AccBagCb` (P23) (:678–:746) | V | PROVED | [cb], their bodies rebuilt from Core's constructors |
| | `AccReadFamilyWithborF2` (P7), `AccBlockSwapWithborS` (P9) (:762, :768) | K | NOT BUILT | `DraftFL` at `withborI2_wf`'s and `withborS_wf`'s derivations: the inner callback captures the user's callback as a live `U` slot (`AllIRowMAt` there, D6). P8, P18, P19, P20–P24's borrow constants are the same two |
| P10, P11, P25, P26, P27, P28, P29, P30, P31 | the nine roots (:779–:787) | R | PROVED | [G5] |
| | `AccCountAlg`, `AccAnyListAlg`, `AccAnyTreeAlg`, `AccSumIAlg`, `AccSumAlg` (:805–:876) | V | PROVED | [bcb] (P27's algebra loads each leaf with `withload`; P29's calls `natCopy` at its own variable, D1) |
| | `AccFreeLAlg`, `AccFreeIAlg` (:836, :866) | V | PROVED | [G5c] |
| | the borrowers at `g : fTy`, `foldImm`, `foldOwn`, `withbor` (1) | V, K | NOT BUILT, not stated as entries | `GROUND.md` §3.5: P10's V2 list (`AllIRowMAt` at a persistent slot, D5), `FoldImmRowM`, `FoldOwnRowM`, `Withbor1RowM` |
| P30 `mapProgC` (open), P32 `mapProg`, P34 `countFreeProg` | `AccMapProgOpenCRoot`, `AccMapProgRoot`, `AccCountFreeRoot` (:919, :916, :924) | R | NOT BUILT | the glue at `U` slots (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`); `borrowerM` at a live `U` slot (D6) |
| P33 `countProg` (the user's case, slot-carried) | `AccCountZero` (:884) | V | PROVED | [bcb] |
| | `AccCountRoot` (:897) | R | NOT BUILT | the glue at `ΓF`'s `U` slots |
| | `AccCountStep` (:903) | V | NOT BUILT | `AllIRowMAt .binder0 (⟨countTy, true⟩ :: Γ)`: the binder-named push at a persistent context (`VRLMStackRename`, D5) |
| | `AccCountCb` (:909) | V | NOT BUILT | as `AccCountStep`, and in the body `AllEVRowM` at `g []` (D1), `LolliERowM` (D9) |
| | `AccCountLoad` (:927) | K | NOT BUILT | `WithloadRowM` (one cell) |
| P12, P35–P41, P13 (affine closures, arrays) | the nine roots (:937–:945) | R | PROVED | [G5] (P39 at every `n`) |
| | `AccCounterStep`, `AccInc`, `AccTab10`, `AccDropI32` (:960, :994, :1015, :1022) | V | PROVED | [G5c] |
| | `AccCntCb` (:971), `AccPassCb n` (:979) | V | PROVED | [cb] at `d_cntBody`; at `passCb`'s body (it hands the borrow through `n` persistent functions) |
| | `AccPassF` (:1004) | V | NOT BUILT | `LamRowM` (its answer holds a `Mut` leaf, D7) |
| | `AccPassWithbor3` (:1009) | K | NOT BUILT | `Withbor3RowM` |
| S1 `pairLoad` | `AccPairLoadRoot` (:1150) | R | PROVED | `accPairLoadRoot` [G5] |
| | `AccPairLoadCb` (:1154) | V | PROVED | `accPairLoadCb` [cb] at `d_borrowBody` (its body holds the load of the pair) |
| | `AccPairLoadLoader` (:1162) | V | PROVED | `accPairLoadLoader` [cb] at `d_pairLoaderBody` |
| | `AccPairLoadAlloc`, `…Free`, `…Forget` (:1202–:1210); P1's `alloc`, `free` at `1` | K | PROVED | [G5c] |
| | `AccPairLoadWithbor` (:1174) | K | NOT BUILT | `Withbor1RowM`. At `[]`, `Withbor1NilRowM`: the payload step ports at the flat `pairTy` (`nilPayloadCore_flat`); the own push at the frame's place reads `ImmFramePlaceFree`, not derived (§11.5) |
| | `AccPairLoadWithload` (:1186) | K | NOT BUILT | `WithloadRowM`. The single own push lends one place, and the second reborrowed cell fails the table at the identity instantiation of the answer's `U` clause, at every stack (`loadGuardFails2`). After part (3) the relation also reads the block push of both places, and at `[]` the block gate passes (`loadGateNilB_pairTy`). `WithloadNilRowM` stops at (l3): the gate reads the reborrow's structure, which [TR] 6.150's rule does not hand its continuation (`LoadGateNilBI`, not derived; §11.5). At the thunked type the answer's `U` clause at a non-identity instantiation moves a single push below the cells (`not_withloadPairGapInst`), a route neither refuted nor built |
| S1′ `pairLoadU` | `AccPairLoadURoot`, `AccPairLoadCbU`, `AccPairLoadLoaderU` (:1151, :1158, :1166) | R, V, V | PROVED | [G5]; [cb] at `d_borrowBodyU`; [cb→] at `d_pairLoaderBody` |
| | `AccPairLoadWithloadU` (:1197) | K | NOT BUILT | `WithloadURowM`. At an arising configuration (`withloadUPairGapReal`, `NxGuardPair.lean:846`, at the stack of the enclosing lend of the pair, `ArisesI` with the view `ArisesVI`) every single-push reading fails the guard. After part (3) the relation also reads the block push of both places, which those readings do not list; at `[]` the block gate passes (`loadGateNilB_pairTy`), and `WithloadUNilRowM` stops at (l3) (`LoadGateNilBI`, §11.5). The entry's own judgement is not refuted, so it is not FAILS |
| S3 `bangUse` | `AccBangUseRoot` (:1536) | R | PROVED | `accBangUseRoot` [G5] |
| | `AccBangUseBody` (:1541), the producer | V | PROVED | `accBangUseBody` [bcb], at every `Δ` its binder is fresh for (the use's `Δuse` at `z = 2` among them) and every dead context |
| | `AccBangUseCall` (:1559), `body ['z] (v, 1)` | G | PROVED | `accBangUseCall` [G5]: the node is first-order (its live slot is the view, its answer `['z] I32`) |
| | `AccBangUseCb`, `AccBangUseBorrower` (:1564, :1569) | V | PROVED | [cb] at `d_useCall`, `d_useBorrowerBody` |
| | `AccBangUseDeref` (:1546), `unbang body` | G | NOT BUILT | `BangERowM` |
| | `AccBangUseInst` (:1552), `body ['z]` at the callback's own variable | G | NOT BUILT | `AllEVRowM` (its step `InScopeOfInterp`, D1) |
| | `AccBangUseWithbor`, `AccBangUseLoad`, `AccBangUseInnerLoad` (:1574–:1584) | K | NOT BUILT | `Withbor1RowM`; `WithloadRowM` at `Ref I32` (one cell) and at `I32` (no cell) |
| P42 (×13) | `Acc…Root` for `allocFree`, `fig2c`, `immBorrow`, `mutBorrow`, `loadClosure`, `aliasLoad`, `swapTwo`, `greetProg`, `ownedFn`, `mutClosure`, `callBorrowed`, `captures`, `fnMut` (:1279–:1291) | R | PROVED | `semSM_embedRoot` [G5 at `embed d_X`] |
| | every other node | — | NOT BUILT | `DraftFLEmbed` (G12) at `d_X` |
| P49 `recLog` | `AccRecLogRoot` (:1318) | R | NOT BUILT | its answer `F (Mut @a I32 ⊗ 1)` holds a `Mut` leaf (D7): `BoundedFixRowM`, `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM` |
| | `AccRecLogStep` (:1323) | V | NOT BUILT | `LamRowM` (`BangThunkVRowM` proved) |
| | `AccRecLogClause` (:1327) | K | PROVED | [G5c] |
| P53 `sumAffE`, P54 `blockAffE b` | `AccSumAffRoot`, `AccBlockAffRoot` (:1340, :1343) | R | PROVED | [G5] at `ADerives.elab` (P54 at every `b`) |
| | `AccSumAffAlg` (:1353) | V | PROVED | [bcb] |
| P55 `allBelow` | `AccBelow` (:1381) | V | NOT BUILT | `LamRowM`, with `ThunkFRowM` (proved) over `VarRowM` at the `Mut` slot (D7); the `∀I` step is `allIRowMUFree0 []` |
| P56 `array-get.bc` | `AccArrayGetRoot` (:1675) | R | PROVED | `accArrayGetRoot` [G5] at `arrayGet_derives`, the checker's derivation |
| | `AccArrayGetTab` (:1688) | V | PROVED | [G5c] at `d_tabE` |
| | `AccArrayGetRead` (:1711), `read` inlined at its use | V | PROVED | [cb] at `d_readBody`, at every `Δ` its binder is fresh for |
| | the `withbor` (1) and `withload` callbacks | V | NOT BUILT, not stated | their λ-bodies' derivations are inside the checker's and are not re-derived (§3.1's route for an inline sub-term); both bodies are first-order, so G5 gives each once derived |
| | `AccArrayGetLoad` (:1724), at `array i32` | K | NOT BUILT | `WithloadRowM`. The single own push lends one place (`loadGuardFails2` at any two of the five cells); after part (3) the block push of the reborrowed cells passes the gate at `[]` (`loadGateNilB_arrayI32`, every length), and `WithloadNilRowM` stops at (l3) (`LoadGateNilBI`, §11.5) |
| | `AccArrayGetReadLoad` (:1730), at `I32` in `read` | K | NOT BUILT | `WithloadRowM` (no reborrowed cell) |
| | `array_copy`, `array_get`, `array_new`, `array_len`, `withbor` (1) | K | NOT BUILT, not stated | D7 (`ArrGetRowM`); `ArrNewRowM`; `array_len` is G5c-shaped; `Withbor1RowM` |
| P59 the I/O models | `AccMkInput`, `AccMkOutput`, `AccTakeInput`, `AccTakeOutput` (:1392–:1398) | V | PROVED | [G5] (λs at first-order computation types) |
| | `AccReadByte`, `AccWriteAll` (:1416, :1421) | V | NOT BUILT | `LamRowM` (answers holding the stream's `Mut` leaf, D7) under `allIRowMUFree0 []` |
| S4 `reconB′` | `AccReconRoot`, `AccReconCb` (:1756, :1762) | R, V | NOT BUILT | no Core derivation (tier 2): `wait` resumes inside the lend |

### 10.4 Results, per program

The conjunctions of each program's stated entries are GR:1872–:1934. The third column lists the
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
  Every entry but the borrow constants' is PROVED (`accPairLoad_but_constants`, GR:1938). The two
  loads' nodes are `NxGuardPair.lean`'s `PairWithloadTyped` and `PairWithloadUTyped` nodes, under a
  closed program. So the pair's open question is in the `withload` constant's row (`DraftFL` at that
  node), not in any judgement of the program's own terms. After part (3) the gate at the pair
  passes at the empty stack, both shapes, both cases of `CohE` (`loadGateNilB_pairTy`), and the
  callback and the loader are PROVED at block pushes too (§11.6). The constants' rows at `[]` stop
  at (l3) (§11.5).
- **S2, `withload` of a slice**: P46 is not available here (§10.2); P56 serves, at five cells.
  `sliceLoad` is not built: P56 serves. After part (3) the gate at an array of `I32` passes at the
  empty stack at every length (`loadGateNilB_arrayI32`); the row at `[]` stops at (l3) (§11.5).
- **S3, the user's case** (`bangUse`): `body : !(∀'z ⊏ ⊤. Imm 'z I32 ⊗ I32 ⊸ ['z] I32)` holds no
  resource and is called inside the load's callback at the callback's own lifetime. S3 is the
  inlined form: `bangBodyE` is written inside `useCb`, at its use, as Core's checker compiles a
  top-level `def`. The top-level, slot-carried form is P33, NOT BUILT on D5. It
  answers `(7, 8)` (`bangUse_eval`). The producer, the call, both callbacks and the root are PROVED
  (`accBangUse_proved`, GR:1946); the carry side's glue (`unbang body`, `body ['z]`) and the three
  borrow constants are NOT BUILT. The slot-carried form is P33: its producer `stepV` and carry side
  `cbE` wait on the binder-named push at a persistent context (D5).
- **S4, `reconB′`**: recorded, NOT BUILT. Its typing is not built; which rule types
  `withborUE dFlag` under `wait` is open [read], so it is not classified as outside the floor on
  that basis.
- **S5, `loadKeepsView`**: not built. It is a borrow-only `cImmBorrow` variant Core accepts, so it
  is a floor obligation, open on D3. That its gate fails `OwnOKI.placeFree` at the needed entry is
  [read], unchecked in Lean; if it holds, it is a draft defect. It and stays so after part (3), whose relaxed `placeFree` is for blocks only
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

---

## 11. Part (3): the block entry

`GROUND.md` §4 is the design. The block is built in place in the one draft relation. Its
definitions are in `Block.lean`, its gate and the rows attempted in `GroundBlock.lean` ("GB"), and
the lemmas the re-proofs read in `R1Block.lean` and `R1MonoB.lean`. Every theorem is proved with
`#print axioms` within `[propext, Classical.choice, Quot.sound]`: the whole-module check reports
all 4152 of ProbeD1's declarations within the three.

### 11.1 The edit

| definition | change |
|---|---|
| `cRLM`'s `∀` clause (`R1.lean:216`) | a third conjunct: at every block push (`OwnPushB`, `Block.lean:89`), the body under the guard at the pushed stack `τ ++ σ`, `blockL τ α ++ αs`, at the reading extended at the binder. The first conjunct and the single push are unchanged |
| `SemSM` (`R1.lean:257`) | `StackOK` becomes `StackOKB`, `StackJM` becomes `StackJB` |
| `SemSMC` (:814), `SemIdxM` (:957) | `StackOK` becomes `StackOKB`, `StackJ` becomes `StackJBase` |

Nothing else in the relation changes: `BoxStep`, `PBox`, the single push (`OwnPushM`, `OwnPushI`,
`OwnOKI`, `ViewAt`) and GhostEnd's piece are as they were. A block is pushed only at a callback
whose argument fits two or more entries, one per leaf (`BlockFits`), at both callback shapes
(`CbArg`).

### 11.2 The gate (`GROUND.md` §4.4)

| statement | theorem | status |
|---|---|---|
| `StackOKBOfOK`, `InstStackOKB`, `StackJBaseIff` | `stackOKB_of_ok`, `instStackOKB`, `stackJBaseIff` (`R1Block.lean:53`, :66, :100) | proved |
| `BlockFitsLeafLe`, `BlockFitsReb` | `blockFitsLeafLe`, `blockFitsReb` (GB:40, :63) | proved |
| `PVLStartB` | `pvlStartB` (GB:109) | proved |
| `PairGuardHoldsB` | `pairGuardHoldsB` (GB:233) | proved, with two hypotheses added to the design's statement, both `PVLStart`'s: the pushed reading agrees with the old one at the old entries' payload types, and the views' nested cells at the stack's places are views. The gate's proofs discharge both at its payloads |
| `LoadGateNilB` at `pairTy`, both shapes, both cases of `CohE` | `loadGateNilB_pair` (GB:616), `loadGateNilB_pairTy` (GB:938) | proved |
| `LoadGateNilB` at `Array I32`, both shapes, every length | `loadGateNilB_array` (GB:851), `loadGateNilB_arrayI32` (GB:944) | proved |
| `FreePlaceExists` (`GroundRegress.lean:273`, stated in part (2)) | `freePlaceExists` (GB:931), from `deepFin` (GB:923): a resource's places at every depth lie in one list, by induction on the stratum | proved |

The gate entries lend the cells exactly at `β`, one entry each, and leave the cells above `β`
unlent. Two or more exact cells give a block, one a single push, none a single push at a free place.

### 11.3 The re-proof, and the stop rule

The rows are re-proved in `GROUND.md` §4.5's order, and `lake build ProbeD1` is clean.
- **The length forms.** Lemmas that read only the stack's length are stated at the length:
  `relendJ_mutK_len`, `relendJ_immK_len` (`GapRows.lean`), `relendM_valueE_len`,
  `relendMValue_len`, `relendM_gSep_len`, `ctxRelends_len` (`R1Thaw.lean`), `retainedPayPush_len`,
  `vRLJ_leaf_push_len`, `monoOwnUFree_go_len` (`R1Mono.lean`), `monoOwnGUFreeMA_len`,
  `pBox_worldB`. Each old statement is now a wrapper and keeps its text, two of them with an
  unused binder renamed (§11.4 (b)).
- **The guard at an instantiated block stack** is read directly (`GuardInstB`, `guardInstB`,
  `R1Block.lean:264`, :272): an instantiation keeps a block's lifetimes equal, so it is no strict
  `ReLend`, which `guardInst`'s route (`instReLend`, `tabRelend`) reads.
- **The `∀I` row's block conjunct**: `MonoOwnGMBAt` (the context across a block,
  `monoOwnGUFreeMB`, `R1MonoB.lean:357`), `CtxShadowMBAt`, and the index carried
  (`stackJBase_allBlock`, `stackOKB_block`, `models_allBlock`, `subOutsideBlock`,
  `outerBelowTop_block`, `R1AllI.lean:403–:590`). **The binder-named block**: the entries named
  by the binder are the innermost block (`subOutsideExtendNamedB`, `stackJBase_allNamed`,
  `CtxExtendNamedMBAt`, `NxAllI.lean:135–:290`).
- **The watched rows** (§4.5). `cRLM_step`'s `F_Σ` case is unchanged: it is generic in the
  postcondition. `statement0MBesideMono0`'s shared lemmas are unchanged (`statement0SharedM`,
  `R1Stmt0.lean:155`). `guardInst` keeps its statement and proof at `StackOK`, and the thaw's `U`
  rows read `guardInstB`. `ReadEquivRelend` and `tabRelend` are at `StackOK` and are unchanged.
- **The stop rule's general clause was met outside the draft, at `forceRowM`.** `SemSM` admits
  block stacks at every placement. At `cbpv` and `binder` the `U` clause reads `RelendU`, and
  `force` reads it at the reflexive re-lend `ReLend αs αs`, whose chain is strict, while a block
  stack's chain is not. `forceRowM` is now stated at the placements whose `U` clause reads
  `RelendJ` (`(p.uFut || p.uOwn) = false`: `binder0`, the draft's). At `cbpv` and `binder`, at
  block stacks, it is not derived. The draft uses `binder0` only, every watched row passed, and
  the condition was met at placements that are not the draft's, so the fallback (§4.8: revert the
  edits to `cRLM`, `SemSM`, `SemIdxM`, `SemSMC`) was not applied: the clause was read as scoped to
  §4.5's watched rows, as its parenthetical says. At stacks with no block nothing proved before is
  lost; the row at every placement under `StackOK` is not yet a named theorem in the library. The edit and its re-proofs are
  one commit (`06fc3dc`), so the fallback is that commit reverted.

### 11.4 The statement-change register (`GROUND.md` §4.7)

**(a) Text changed**, with the reason.

| statement | file | change | reason |
|---|---|---|---|
| `cRLM`, `SemSM`, `SemSMC`, `SemIdxM` | `R1.lean` | §11.1 | the edit |
| `SemSMNK` | `R1AllI.lean:127` | `StackOKB`, `StackJBase` | `SemSM` at the indices not naming the binder follows `SemSM`'s index |
| `BoxIdx` | `R1Box.lean:176` | `ok : StackOKB` | the box index is `SemSM`'s index |
| `stackJ_of_boxIdx` | `R1Box.lean:257` | gains `(σ.map LEnt.x).Nodup` | `BoxIdx` no longer carries distinct variables; the block form is `stackJBase_of_boxIdx` |
| `cRLM_all_binder0`, `CRLMAllNil`, `CRLMAllTop` | GL:652, :682, :705 | gain the block conjunct | they unfold the `∀` clause (planned in §4.7 (a)) |
| `allIRowMNKAt0_of` | `R1AllI.lean:632` | takes `MonoOwnGMAtB` (the single push at a stack with blocks), `MonoOwnGMBAt` and `CtxShadowMBAt` | the block conjunct and block indices |
| `allIRowMAt0_of` | `NxAllI.lean:197` | the same, and `CtxExtendNamedMBAt` for `CtxExtendNamedMAt` | the same, and the binder-named block |
| `forceRowM` | `R1Stmt0.lean:379` | gains `(p.uFut || p.uOwn) = false` | §11.3 |

**(b) Proof changed, text unchanged.** The wrappers: `relendJ_mutK`, `relendJ_immK`,
`relendM_valueE`, `relendM_gSep`, `retainedPayPush`, `vRLJ_leaf_push` (an unused binder renamed
`_hch`), `monoOwnUFree_go`, `pBox_world` (an unused binder renamed `_hok`), `force_UM`,
`thunkF_U_M`, `thunkV_U_M`, `boxIdx_of_index`, `loadGateNil_unit`. Re-proved: `cRLM_step`,
`thunkFRowM`, `thunkVRowM`, `bangThunkFRowM`, `bangThunkVRowM`, `boxIdx_step`, `uFree_boxSteps`,
`slot_boxWorld`, `all_ownM`, `statement0MBesideMono0`, `gdRowRefutation`, `gdAllIHoldsAtMt`,
`allIRowMNKUFree0`, `allIRowMUFree0`, `rollRowM`, `unrollRowM`, `muAdjVRLME1`, `pSemIdx`,
`pSemIdxN`, `semSMNilOfSemSM`, `semIdxMNil`, `coreToSemSMConst`.

**(c) Text unchanged, meaning changed**, since they read `vRLM`, `cRLM`, `SemSM`, `SemIdxM` or
`SemSMC`:
- `statement0UFullM`, `allIRowMUFree0`, `rollRowM`, `unrollRowM`, `muAdjVRLME1`, the box's facts,
  and the `Ground*` theorems.
- **The producers at a type whose argument fits a block** now prove the block conjunct as well:
  `semSMCallbackOfCore` and `semSMCallbackArrOfCore` through `allIRowMUFree0`, and the PROVED
  entries at such types, S1's loaders (`AccPairLoadLoader`, `AccPairLoadLoaderU`, argument
  `Imm '1 1 ⊗ Imm '1 1`). At a type whose argument fits no block of two their meaning is unchanged
  (`blockFitsLeafLe`): every `withbor` callback, and the borrowers at `Imm 'x S`.
- **The single-push facts**: `CbReading`, `PairGuardRejectsU`, `PairGuardRejectsF`,
  `withloadUPairGapReal`, `not_withloadPairGapInst`, `WithloadUPairGapNilE1`. Their docstrings now
  say "every single-push reading": the pair's callback is also read at block pushes.
- **`SemIdxM`, `SemSMC`**, and the statements reading them (the `RetainedPay*Row` rows, `PairCfg`,
  `SliceCfg`, `MonoOwnGMC`, `AllIRowMC`): they admit block indices. At a stack with no block the
  index is the old one (`stackOKB_of_ok`, `stackJBaseIff`).
- **`cRLM`'s `F_Σ` clause at block stacks**: GhostEnd's text, now read at stacks holding a block
  (D12, §11.7).
- `callbackExtMutM_own`, `callbackExtImmM_own`: their text reads the single push, at a top-level
  `Mut 'y T` or `Imm 'y T`, which fits no block of two, so their meaning is unchanged.

### 11.5 The rows attempted at the empty stack (`GROUND.md` §4.6)

None closes. Each row's first step that does not port is stated as the lemma it is missing
(GB:949–:1052). None of them is derived, and no obstruction to any of them is verified.

| row (GB) | route | first step that does not port | missing lemma | after it |
|---|---|---|---|---|
| `Withbor1NilRowM` (:978) | `withbor1_compatX` | the payload put into 6.64's frame: `wpTS_I_frameX` holds it at Core's `vC true A`, in and out; the row holds it at the draft's relation at `[]` | `NilPayloadCore A` (:999); holds at a flat payload (`nilPayloadCore_flat`, :1004), not derived at a payload with a thunk inside | at a flat payload, (w1): the own push at the frame's place reads `OwnOKI.placeFree` (D3), and the frame rule hands the callee any resource beside the borrow (`ImmFramePlaceFree`, :1012); (w3) is `CallbackExtImmMF` (`Nx.lean:489`), stated |
| `WithloadNilRowM` (:984) | `withload_compatX` | (l3), the callback's push at `β`: the gate reads `ResU.Reb`, `LoadPay` and the callback's freedom at the reborrowed places, and `wpTS_reborrow` hands its continuation a wand over every resource at Core's relation at the reborrowed type | `LoadGateNilBI A (loadCbF A B)` (:1030); holds at `1` (`loadGateNilBI_unit`, :1046) | at `1`, the answer's `U` clause at the pushed stack, whose guard is read at the run's answer, which the `F` postcondition does not carry [read] (`CallbackExtImmMF`'s step) |
| `WithloadUNilRowM` (:990) | `withloadU_compatX` | (l3), as above | `LoadGateNilBI A (loadCbU A B)` | not attempted beyond (l3) |

The chooser and [TR] 6.150 (`wpTS_reborrow`) are Core's, and the `withload` argument is Core's at
`Imm` at `[]` (G3), so (l1)–(l2) port [read]. The entries that read the rows stay NOT BUILT with
these lemmas: K1 of P1 and of nearly every program (`Withbor1NilRowM`), and the `withload` K
entries of P1, P2, P5, P16, P27, P33, P56 and S1 (`WithloadNilRowM`, `WithloadUNilRowM`). The
every-index rows (`GROUND.md` §4.6's stretch) are not attempted.

### 11.6 The suite after the block

- Every entry PROVED before the block is PROVED after it: GR builds at the edited relation, with
  `loadGateNil_unit` now through `loadGateNil_unit_of` and `FreePlaceExists` proved. No entry
  moves to PROVED or to FAILS.
- The gates of S1 and S2 are PROVED at the empty stack (`loadGateNilB_pairTy`,
  `loadGateNilB_arrayI32`). The pair and slice entries read: the gates PROVED; K2 and K2′ at `[]`
  NOT BUILT at (l3) (`LoadGateNilBI`); at every index NOT BUILT (`WithloadRowM`,
  `WithloadURowM`).
- S5 stays route-blocked: its payload `Ref 1` has one leaf, so its push is the single push, whose
  `placeFree` is `OwnOKI`'s.

### 11.7 D12: the two obligations and their reach

- **(i) The share must re-lend a block together.** After a resumable stop the piece re-lends over
  `ReLend` and `openFS`, whose strict chains give a block's entries distinct lifetimes. The
  replacement is the share over instantiations (`ShareReLendInst`'s direction,
  `Binder.lean:549`), which keeps a block's lifetimes equal. It is owed before any program with a
  resumable stop at a stack holding a block is claimed.
- **(ii) What a stop crossing a block owes the block's other entries**, beside `ghostS`'s innermost
  one [unchecked]. It is owed before any program with a stop crossing a block is claimed.
- **Their reach.** A stack holds a block only at or below a callback whose argument fits two or
  more entries, one per leaf, at either callback shape. A single-leaf callback pushes none
  (`blockFitsLeafLe`). So neither obligation reaches a borrow-only program, which reads no `F_Σ`
  row, nor one of Core's effect programs, whose lends are at `Flag`, one leaf [read], nor any
  program of this suite. They reach effectful code inside or below a multi-leaf callback: the
  `withload` of a pair, an array or a list of references, a slice lend, a fold algebra at a node
  with two leaves.
- Also carried: `InstReLend` is proved at `StackOK` only (`instReLend`, `BinderInst.lean:267`), and
  the guard at an instantiated block stack is read without it (`guardInstB`); statement 2's
  `SpanLoadRow` at a payload with two leaves becomes attemptable.

### 11.8 Report lists (CLAUDE.md §5)

- **Printed objects read.** [TR] 6.150 (`wpTS_reborrow`; `TW.reb`, `TW.rebDeep` through the gate's
  hypotheses) at (l3); [TR] 6.64 (`wpTS_I_frameX`) at `withbor` (1)'s payload step and own push;
  [TR] 6.172 and 6.175's compatibility lemmas as the rows' routes (`withbor1_compatX`,
  `withload_compatX`, `withloadU_compatX`); [TR] p. 5's `reb_β` (`ResU.Reb`, `reb_cell`,
  `reb_cell_ls`) in the gate.
- **Printed hypotheses unspent.** None: no printed lemma is proved here. The printed objects are
  Core's lemmas, read as routes; none is applied with a premise left open.
- **Uniqueness and functionality results.** Used: `ResU.CompS.functional` (the `∀I` rows, the
  binder-named index, the gate at `1`) and `CellU.immOf_inj` (the block gates). Unused:
  6.150's chooser determinacy, which the rows do not reach.
- **Printed lemmas in the run-up that are untranscribed.** None for the edit and the gate. At the
  rows, the draft's forms of 6.64 and 6.150 consumed through an own push (`ImmFramePlaceFree`,
  `LoadGateNilBI`) are ProbeD1's own statements, not printed rows.
- **Hypotheses added.** `PairGuardHoldsB`'s two (§11.2), discharged at the gate's payloads.
  `stackJ_of_boxIdx`'s distinct variables. `forceRowM`'s placement (§11.3). The `∀I` rows' block
  transports (`MonoOwnGMBAt`, `CtxShadowMBAt`, `CtxExtendNamedMBAt`), each discharged at every
  context reaching no `U` (`allIRowMUFree0`).
- **Technique built.** The guard at an instantiated block stack read without `ReLend`
  (`guardInstB`, `no_bound_of_stratS_le`); the `U`-free push of a block (`monoOwnGUFreeMB`); the
  binder-named block (`subOutsideExtendNamedB`); `Res` finite at every depth (`deepFin`).
