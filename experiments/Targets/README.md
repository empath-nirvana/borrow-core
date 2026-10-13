# Targets — an effect system, a borrow calculus, and their interaction, in Lean

`RESTRUCTURE.md` says what "done" means, as two systems and the rules of their interaction:

- **A**, an effect system, stated abstractly over any calculus;
- **B**, the borrow calculus (BoLo), whose guarantees are given;
- **I**, the interaction, the only place where A and B meet, with the combined theorem;
- **the Instance**, our calculus as one instance of A.

This library states every target as a `def … : Prop`, proves what the design asks for now, and
records each target's status in `Targets/Status.lean`, grouped by system. `RESTRUCTURE.md`
§Unresolved records where the Lean departs from the design and what is not built. `AGREE.md` is
the page to agree.

```
lake build Targets
```

The build has no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or
`implemented_by`. `Targets/AxiomCheck.lean` prints `#print axioms` of every theorem the sources
state. It fails the build if any theorem or definition of the library uses an axiom outside
`[propext, Classical.choice, Quot.sound]`, or if any constant is `opaque`, an `axiom`, carries
`implemented_by`, or is unsafe (other than the compiler's `._unsafe_rec` copies).
`Targets/Audit.lean`, the step-index audit, fails the build if `coreW`'s report changes or a
negative test is not rejected.

## Layout

The imports run one way: A imports nothing of ours; base imports no A; B imports no A, I or
Instance; the Instance imports no B or I; I imports everything.

| part | path | contents |
|---|---|---|
| **A** | `Targets/A/EffAlg.lean` | the effect algebra (Yoshioka–Sekiyama–Igarashi Def. 3.5) and its safety (Def. 5.1) |
| | `Targets/A/System.lean` | `EffectSystem` (CBPV formers over an effect algebra; contexts with five named frames, the driver `driveF` among them; a labelled machine; typing); runners and runs; `SafeRuns`, `Terminates`, `RunsTo`, `RunsForever`; the schemas `PolyUse`, `PolyUseLacks`, `PolyUseOpen`, `CallsThrough` |
| | `Targets/A/Machine.lean` | S0: `ConfLaws`, `KontLaws`, `AppLaw`, `Congr`, `NoIO`, `OpStuck`, `DataInj`, `LoopLaws`, `DriveLaws`, `MachShape`; the let law `LetLaw` |
| | `Targets/A/Soundness.lean` | S1 `RowAlgebra`, S2 `DataDiv` and `Safety`, S3 `EffSafe`, S4 `HandlerSem`, S5 `Cancellation` (the cancel and unwind traces), S6 `ContUse`; `SProps` |
| | `Targets/A/Programs.lean` | the signatures, runners and programs of E1–E10, and S6's witnesses R1–R4 |
| | `Targets/A/Expressiveness.lean` | E1 `NoColouring` … E10 `Reconciler`; `EProps`; `Props := SProps ∧ EProps` |
| | `Targets/A/NonVacuity.lean` | the abstract non-vacuity lemmas |
| | `Targets/A/Binary.lean`, `Targets/A/Lowering.lean` | A₂ (the binary laws) and A₃ (the erased lowering over a fixed target), stated, out of the first pass |
| **base** | `Targets/Base/*` | Core's machine, rows and typing as B, I and the Instance read them: platforms, runs, `PRun`, `ReleasedOnce`, B5's `Named`, `Expr.mapLoc`, `Heap.push`, `RelAt`, `Bump`, `BumpSim` (`Machine.lean`); the statements about runs that mention no world, `Sound`, Core's `EffSafe`, `EffSafeDrive` (`RunProps.lean`); `TypingJ`, `tier1`, `tier1NU`, the `RC_*` rules (`Typing.lean`); Core's cancel and unwind shapes (`CoreCancel.lean`); the answering implementations; contextual approximation |
| **B** | `Targets/B/World.lean` | `BWorld`, a borrow world with borrow fields only; `coreB`, Core's relation as one |
| | `Targets/B/Guarantees.lean` | B0–B7 and the bounds as Props: `ExtendsB`, `FL`, `Adequate`, `Sound`, `SoundContracts` (externs at `ContractsW`), `ReleasedOnceReuse`, `ExclusiveB`, `LifetimeSound`, `WBound`; `B.Guarantees` |
| | `Targets/B/BoLo.lean` | each guarantee at BoLo, by citing `Core` and `Paper` |
| | `Targets/B/Routes.lean` | the routes: `soundnessOfFL`, `soundContractsOfFL`, `releasedOnceReuse_of_bumpSim`, … |
| | `Targets/B/Release.lean` | release as lemmas about runs: `ReleasedOnceAll`, a tautology; `releasedOnce_of_ends`; `bump_follows` |
| | `Targets/B/NonVacuity.lean` | `not_releasedOnceReuse_staleFree`: B5 is not a tautology |
| | `Targets/B/Conservativity.lean`, `RunEnd.lean`, `Binder.lean` | P14; the run-end laws where `Upd` is Core's; the freeze binder's machine half |
| **Instance** | `Targets/Instance/Rows.lean` | our row forms as instances of A's effect algebra (`orowAlg`, `orowRF`, `RowLink`) |
| | `Targets/Instance/Types.lean`, `Typing.lean` | the open types (`OVTy`, `OCTy`, with `effF` and the row `∀`), `OurTyping`, its reading `read` (the design's `⟦J⟧`), `tier1Open`, `RowVarKernel` |
| | `Targets/Instance/Core.lean` | `AdmEff`, `ourInst RF Ξ J : A.EffectSystem`, the encodings, the labelled machine `OStep` |
| | `Targets/Instance/Bridges.lean` | A's syntactic laws at our instance: `ConfLaws`, `KontLaws`, `NoIO`, `DataInj`, `LiftExt` |
| | `Targets/Instance/Restricted/*`, `Binary.lean`, `ZeroCost.lean` | Core's no-interception and two-frame unwind; `storeCancel` unr-free; A₂ over Core, stated; A₃'s lowering classes |
| **I** | `Targets/I/World.lean` | `SemWorld extends B.BWorld` (`held`, `Stop`, `share`), `coreW`, the effectful wp |
| | `Targets/I/Interface.lean`, `Device.lean`, `Pins.lean`, `Routes.lean` | I1–I5 at the world; `Bounds`, `Interface`, the proof device `Device`, `EmbedsNil`; R-CLOSEDOP; `effSafeOfFL`, `contractsW_of_meets` |
| | `Targets/I/Programs.lean` | the composite programs: `at02`, `at04`, `at12`, `at17`, `genSelf`, and the rejected AT05–AT08, AT13; `AcceptedAt`, `Tier2Programs`, `Rejects`, `RejectsAT07` |
| | `Targets/I/Combined.lean` | **`I.Combined`**, done's statement; `Tier1`, `Tier1Core`; the corollaries |
| | `Targets/I/RunEnd.lean`, `Binder.lean`, `NonVacuity.lean`, `Restricted/*` | FIX-RUN-END's checks and witness worlds; the freeze binder at W; witnesses for the pins; the restricted results at `coreW` and `tier1` |
| meta | `Targets/Audit.lean`, `Status.lean`, `AxiomCheck.lean` | the step-index audit with nine negative tests and the pin of Core's relation; the record; the axiom check |

## Done

```lean
def I.Combined (RF : RowForm) (J : OurTyping RF) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  (∀ Ξ, AdmEff Ξ → (ourInst RF Ξ J).Props)   -- nothing breaks the effect algebra
  ∧ B.Guarantees J.read M.toBWorld            -- nothing breaks the borrow calculus
  ∧ Bounds M ∧ Interface M                    -- the interaction's option-neutral rules
  ∧ Pins J Adm c                              -- what the composite's typing must contain
  ∧ Accepts J.read c ∧ Rejects J.read         -- the composite's programs and its rejections
```

**Done** is `Combined orowRF J₂ W admClosedOp .any` at a **named** tier-2 typing system `J₂` and a
**named** world `W`, with `audit_W`. **It is OPEN**: neither `J₂` nor `W` exists. **Tier 1** is
`Combined orowRF J₁ coreW admClosedOp .abortive`, also OPEN: `J₁` (today's rules over open rows
with the row `∀`) waits on RESTRUCTURE §7 Q1–Q2.

**The restricted tier-1 reduction** `Tier1Core` (today's kernel `tier1Open`, Core's world) is
OPEN. Proved of it: the world conjuncts and the device at `coreW` (`tier1Core_world`), and B's
guarantees from `Adequate coreB` and the step-for-step simulation `BumpSim`
(`tier1Core_guarantees_of`). Missing: A's (S) properties at our instance (the Instance's bridges
are not built), and `I4a` at today's unr-free kernel.

## Status, by system

From `Targets/Status.lean`. *PROVED AT σ=[]* is Core's relation (`coreB`, `coreW`) or Core's typing
(`tier1`); *generic* is for every world or typing system; *every instance* is for every
`EffectSystem`.

### A — an effect system

| target | status | Lean |
|---|---|---|
| `EffectSystem`, S0–S6, E1–E10, `Props`; A₂, A₃ | stated | `Targets/A/*` |
| a typing that types nothing fails `EProps`; so does an instance with no effects | PROVED (every instance) | `not_eProps_of_emptyTyping`, `not_eProps_of_noLabels` |
| E1, E2, E6, E10 need effect polymorphism (decision 62's row variables) | PROVED (every instance) | `not_noColouring_of_monoCallback` and its three siblings |
| E3 needs divergence; a pure-row loop that diverges is not at a data answer | PROVED (every instance) | `not_loops_of_total`, `divInTypes_of_loops` |
| effect safety has teeth; Def. 5.1 (1) from one signature object | PROVED (every instance) | `not_der_unhandled`, `c1_of_rowSig` |
| the runners `Rtick`, `Rtl`, `Rrec` keep their protocol | PROVED (every instance) | `rtick_respects`, `rtl_respects`, `rrec_respects` |
| A's properties at our instance | OPEN (the Instance's bridges) | — |
| A₃'s reference programs | not written | — |

### B — the borrow calculus

| id | guarantee | status at BoLo | Lean |
|---|---|---|---|
| B0 | BoLo's programs stay typed | PROVED AT σ=[] | `extendsB_tier1` |
| B1 | the fundamental property | PROVED AT σ=[] | `fl_core_tier1`, `fl_core_tier1NU` |
| B2 | adequacy | PROVED AT A RESTRICTION (no platform operation, data answers); in full OPEN | `adequateRetAt_core_none` |
| B3, B4 | no use after free, no double free; leak freedom | PROVED AT A RESTRICTION (the same) | `soundRetAt_tier1_none` |
| B4′ | the same with externs meeting W's contract | PROVED (generic, from B1 and B2) | `soundContractsOfFL` |
| B5 | release exactly once, location reuse included | from B4′ given `BumpSim`: PROVED (generic); `BumpSim` OPEN (OQ-43); not a tautology: PROVED | `releasedOnceReuse_of_bumpSim`, `not_releasedOnceReuse_staleFree` |
| B6 | exclusive mutable borrows | PROVED AT σ=[] | `exclusiveB_core` |
| B7 | lifetimes respected | PROVED AT σ=[] | `lifetimeSound_core` |
| — | the bounds | PROVED AT σ=[] | `wBound_core` |
| — | `ReleasedOnceAll` | a **tautology about runs**, a lemma, not a guarantee | `releasedOnceAll` |
| — | the run-end laws where `Upd` is Core's; P14 | PROVED (generic; at `coreB`) | `updRefl_of_core` …, `wbCore`, `conservative_core` |

### I — the interaction

| target | status | Lean |
|---|---|---|
| `Bounds`, `Interface`, the device and `WBCore` at `coreW` | PROVED AT σ=[] (abortive rows) | `tier1Core_world` |
| the corollaries of `Combined`: the conjuncts that read no world, I1 and I2 at the program level, Core's P2, the SPEC's externs (with `EmbedsNil`) | PROVED (generic) | `combined_prog`, `i1Prog_of_combined`, `i2Prog_of_combined`, `effSafe_core_of_combined`, `soundnessContractsAR_of_combined` |
| a reachable leak breaks the combined theorem | PROVED (generic) | `not_combined_of_leak` |
| Core's extern contract gives W's at row-abortive types, with `EmbedsNil` | PROVED (generic) | `contractsW_of_meets` |
| the composite programs run (interpreter, evidence only) | checked | `at02_eval` … `at17_eval`, `genSelf_eval`, `at07_eval` (a use after free) |
| `CompositeT1 tier1`'s typing and safety | PROVED AT A RESTRICTION (no platform operation) | `acceptedT1_*` |
| `Tier2Programs`, `Accepts`, `Rejects`, `RejectsAT07` at a typing system | OPEN | — |
| I1, I3, I5, P11 at `coreW`; I2 at abortive rows; `EmbedsNil coreW` | PROVED AT σ=[]; AT A RESTRICTION | `status_device_core`, `embedsNil_core` |
| FIX-RUN-END's checks and witness worlds | PROVED | `Targets/I/RunEnd.lean` |

### The Instance

| target | status | Lean |
|---|---|---|
| `tier1Open.read = tier1NU` | PROVED | `tier1Open_read` |
| `ConfLaws`, `KontLaws`, `NoIO`, `DataInj`, `LiftExt` at our instance | PROVED | `confLaws_ourInst`, `kontLaws_orow`, `noIO_ourInst`, `dataInj_ourInst`, `liftExt_orow` |
| our rows meet Def. 3.5 and Def. 5.1 | PROVED AT A RESTRICTION (`orowRF`) | `rowAlgSafe_orowRF`, `rowLink_orowRF` |
| no typed term intercepts a cancel; the two-frame unwind | PROVED AT σ=[]; an instance | `noInterception_tier1`; `two_frame` |
| the semantic bridges (`AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`, `LetLaw`, `RowAlgebra`, `Safety`, `EffSafe`, `HandlerSem`, `Cancellation`, `ContUse`) | OPEN | — |
| `monoCallback_tier1Open`, R1–R4 at our machine, the positive (E) runs | OPEN | — |

### The step-index audit

`coreW`'s report is pinned: recursion on an array's length, a clause index or a de Bruijn index;
the lifetime stratification `Cell`; the allocator's allocation count (`AHead`, `ARun`); and
`Table`, `ewpTS`, `vCE._f`, whose `∀`-bound predicates range over lend records. The nine
negative tests (step-indexed toy worlds) are each rejected at their own entry. When `W` is built,
`audit_W` is the same check at `W`.

## The survey's package

| survey | here |
|---|---|
| A1 type soundness with suspended frames | B1, B3, B4 in the composite; I's `Arises`; the device's I1 |
| A2 effect safety and algebra conditions | A's S1 `RowAlgebra` and S3 `EffSafe` |
| A3 multiplicity soundness | A's S6 `ContUse` (linear and affine continuations); multi-shot dropped (decision 63) |
| A4 lifetime and escape soundness | B7 `LifetimeSound`; S3 |
| A5 exclusivity across the handler | B6 `ExclusiveB`, I's `Exclusive`, I4 |
| A6 discard semantics | resource half: B4 with B5; continuation half: S6 `ContUse`; S5 `Cancellation` |
| A7 conservativity | the device (`ConservativeWB`, `EmbedsNil`); `Conservative` beside done; `WBCore` a companion lemma |
| T0 effect algebra | S1 |
| T1 capture lemma | the device's I1; E9 and E1′ in done |
| T2 preservation | I's `Arises` in done; the device's I2 and I3 |
| T3 progress and effect safety | B3 (`SafeRuns`), S3 |
| T4 resource conservation | B4 with B5 |
| T5 borrow invariants with suspended frames | B6, I's `Exclusive`, B7, S3 |
| T6 discard | B4 with B5; S5; E7, E9c |
| T7 conservativity | the device |
| T8 abstraction safety | A₂ `Abstraction` (binary, out of the first pass) |
| T9 elaboration | not a target |

## Review findings

`RESTRUCTURE.md` §9 maps every review finding of the design to where it is resolved. The third
review's blocker and two major findings were answered in the design text and not reviewed again;
§Unresolved says how the build implements each, and what of each is unchecked. `FIX-RUN-END.md`
§Unresolved lists the two major findings its own review ended with, also revised and not reviewed
again. `AGREE.md` boxes every finding still open.
