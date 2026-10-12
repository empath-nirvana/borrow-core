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
| | `Targets/A/System.lean` | `EffectSystem` (CBPV formers over an effect algebra; contexts with five named frames, the driver `driveF` among them; a continuation's cell, `captureAt`, `cellFree`, `withCell`; a labelled machine; typing); runners and runs; `SafeRuns`, `Terminates`, `RunsTo`, `RunsForever`; the schemas `PolyUse`, `PolyUseLacks`, `PolyUseOpen`, `CallsThrough` |
| | `Targets/A/Machine.lean` | S0: `ConfLaws`, `KontLaws`, `AppLaw`, `Congr`, `NoIO`, `OpStuck`, `DataInj`, `LoopLaws`, `DriveLaws`, `MachShape`; the let law `LetLaw` |
| | `Targets/A/Soundness.lean` | S1 `RowAlgebra`, S2 `DataDiv` and `Safety`, S3 `EffSafe`, S4 `HandlerSem` (a catch may allocate one fresh cell for `κ`, which its resume and affine cancel release: `CatchLaw`, `ResumeCellLaw`, `CancelCellLaw`, `JoinAcross`; `HandlerSemNoCell`, S4 with no cell, kept; at an instance with no cells the two agree, `handlerSem_iff_noCell`), S5 `Cancellation` (every run from a cancel's or an unwind's start a prefix of a cancel or unwind trace), S6 `ContUseEv` (per capture event; `ContUse`, read at `capture`, kept); `SProps` |
| | `Targets/A/CancelWhole.lean` | S5 read whole (`NoInterceptWhole`, `UnwindOrderWhole`, `CancellationWhole`: every run a trace), kept as a record; it implies S5 (`cancellation_of_whole`) |
| | `Targets/A/Programs.lean` | the signatures, runners and programs of E1–E10, and S6's witnesses R1–R4 |
| | `Targets/A/Expressiveness.lean` | E1 `NoColouring` … E10 `Reconciler`; `EProps`; `Props := SProps ∧ EProps` |
| | `Targets/A/NonVacuity.lean` | the abstract non-vacuity lemmas |
| | `Targets/A/Binary.lean`, `Targets/A/Lowering.lean` | A₂ (the binary laws) and A₃ (the erased lowering over a fixed target), stated, out of the first pass |
| | `Targets/A/UnaryLaws.lean`, `Targets/A/Theories.lean` | the unary laws beside done, run-level (`TailLaw`, `AlgLaw`, `EtaHold`, `EtaLin`), algebraicity with a finaliser's start observed but not its code (`RunsAlikeStart`, `Ev.start`; `AlgLawCode` kept), each and S4 failing where the handler or bind ignores its clauses (`not_handlerSem_toy`); theories: equations in signatures (`Eqn`, `Theory`), the state-passing handler of co-operations (`ansHnd`, `runAt`), handler correctness (`AnsCorrect`), comodels (`IsComodel`), global state (`stateTheory`, `stateCo`) |
| **base** | `Targets/Base/*` | Core's machine, rows and typing as B, I and the Instance read them: platforms, runs, `PRun`, `ReleasedOnce`, B5's `Named`, `Expr.mapLoc`, `Heap.push`, `RelAt`, `Bump`, `BumpSim` (`Machine.lean`); the statements about runs that mention no world, `Sound`, Core's `EffSafe`, `EffSafeDrive` (`RunProps.lean`); `TypingJ`, `tier1`, `tier1NU`, the `RC_*` rules (`Typing.lean`); Core's cancel and unwind shapes (`CoreCancel.lean`); a typed term is closed at its context (`Closed.lean`); the polymorphic let's premise term (`Fill.lean`); runs computed by the kernel, `look` (steps that keep the memory) and `runM` (the memory steps added, a run of Core's machine, `runM_sound`) (`Look.lean`, `LookMem.lean`); the answering implementations; contextual approximation |
| **B** | `Targets/B/World.lean` | `BWorld`, a borrow world with borrow fields only; `coreB`, Core's relation as one |
| | `Targets/B/Adequacy.lean`, `PlatSafe.lean` | B2 at BoLo (`adequate_core`); runs under a platform that answers part of the row |
| | `Targets/B/HeapFrame.lean` | a closed program in Core's relation runs from every finite memory, its cells `wpG`'s frame (`ownWorld`, `runs_of_rel`, `runs_of_rel_unit`) |
| | `Targets/B/Guarantees.lean` | B0–B7 and the bounds as Props: `ExtendsB`, `FL`, `Adequate`, `Sound`, `SoundContracts` (externs at `ContractsW`), `ReleasedOnceReuse`, `ExclusiveB`, `LifetimeSound`, `WBound`; `B.Guarantees` |
| | `Targets/B/BoLo.lean` | each guarantee at BoLo, by citing `Core` and `Paper` |
| | `Targets/B/Routes.lean` | the routes: `soundnessOfFL`, `soundContractsOfFL`, `releasedOnceReuse_of_bumpSim`, … |
| | `Targets/B/Release.lean` | release as lemmas about runs: `ReleasedOnceAll`, a tautology; `releasedOnce_of_ends`; `bump_follows` |
| | `Targets/B/NonVacuity.lean` | `not_releasedOnceReuse_staleFree`: B5 is not a tautology |
| | `Targets/B/BumpSim.lean` | the step-for-step simulation B5 rests on (OQ-43 (b)): renaming along a function commutes with every head step, the array steps where it moves their blocks (`head_image`); `BumpSimAt`, `BumpSim` with the hypotheses a bump run supplies, proved (`bumpSimAt`); every run keeps the platform's protocol (`platData_of_safe`); B5 from B4′ (`releasedOnceReuse_of_soundContracts`) |
| | `Targets/B/Conservativity.lean`, `RunEnd.lean`, `Binder.lean` | P14; the run-end laws where `Upd` is Core's; the freeze binder's machine half |
| **Instance** | `Targets/Instance/Rows.lean` | our row forms as instances of A's effect algebra (`orowAlg`, `orowRF`, `RowLink`) |
| | `Targets/Instance/Types.lean`, `Typing.lean` | the open types (`OVTy`, `OCTy`, with `effF` and the row `∀`), `OurTyping`, its reading `read` (the design's `⟦J⟧`), `tier1Open`, `RowVarKernel` |
| | `Targets/Instance/Core.lean` | `AdmEff`, `ourInst RF Ξ J : A.EffectSystem`, the encodings, the labelled machine `OStep` |
| | `Targets/Instance/Bridges.lean` | A's syntactic laws at our instance: `ConfLaws`, `KontLaws`, `NoIO`, `DataInj`, `LiftExt` |
| | `Targets/Instance/Platform.lean` | the platform a runner gives (`platformOf`), its protocol, and its steps as the runner's |
| | `Targets/Instance/Restricted/*`, `Binary.lean`, `ZeroCost.lean` | Core's no-interception and two-frame unwind; `storeCancel` unr-free; A₂ over Core, stated; A₃'s lowering classes |
| | `Targets/Instance/J1.lean` | `J₁`, tier 1's typing: Core's kernel over the open types, a polymorphic slot closed by substitution (`Closing`, `fillS`); its reading is `tier1`; its judgement at an effect context, its inner rows tied (`J1DerAt`, decision R); the let law and S1 at our instance |
| | `Targets/Instance/TiedKernel.lean` | Core's kernel with the rows of its handlers and operations tied to the effect context (`CDerivesAt`, decision R); a tied derivation is Core's; a tied handler's signature is a prefix of the context's |
| | `Targets/Instance/Inversion.lean`, `J1Checks.lean` | what today's kernel does not type (A-level handlers, a let read at two instances, a persistent function called at an effectful row, `()` at a resuming `unr` row); the checks on TIER1-PLAN §2's route; the let law and S1's parts at our instance |
| | `Targets/Instance/Runs.lean`, `CellRuns.lean`, `Theories.lean`, `UnaryLaws.lean` | quiet runs (`Quiet`) and complete runs along a chain; runs around a capture cell (`CellQuiet`, `Calm`, `runsAlike_of_calm`); the fold of a straight-line computation under the answering handler and the comodel reduction (`calm_fold`, `ansCorrect_of_comodel`), global state correct and its bad `put` no model; algebraicity observing a finaliser's code fails at `J₁`, its inner rows tied, by a finaliser that holds an affine `κ` (`not_algLawCode_J₁`), and as restated holds at that configuration (`algLaw_algAffProg`); the round-2 witness outside the tied kernel (`not_rowAt_R5`); the tail law and algebraicity at the answering class |
| | `Targets/Instance/AlgSim.lean` | algebraicity's two sides step for step: terms related but at algebraicity's frames (`AlgRel`), every head step of Core's machine kept (`AlgRel.head`), a machine step and a runner's step matched forward and back (`ostep_sim`, `rstep_fwd`, `rstep_bwd`), so the same complete runs (`obsStartFrom_iff_rel`); algebraicity at every typing system whose typed programs' runs are `AlgGood` (`algLaw_of_good`) |
| | `Targets/Instance/ContUse.lean` | S6's tooth at the capture cell: R1's run, and a typing system that types R1 fails `ContUseEv` (`not_contUseEv_of_der_R1`, `teeth_JR_ΞA`) |
| | `Targets/Instance/HandlerCell.lean` | S4 at the capture cell, at every effect context (`handlerSem_ourInst`, `handlerSem_orow`): a catch at an unrestricted operation keeps the store (`catch_unr_ourInst`), one at a linear or affine operation allocates `κ`'s cell (`catch_cell_ourInst`), resume and cancel at a cell release it (`resumeCellLaw_ourInst`, `cancelCellLaw_ourInst`); S4 with no cell fails at `J₁` and `ΞA` (`not_handlerSemNoCell_J₁_ΞA`) |
| | `Targets/Instance/CancelRuns.lean` | S5's traces at our machine: a step of a context around a stepping term is the term's (`rstep_unplug`); the unwind's and the cancel's traces, every path a trace once the β-step after a fire step that ends it is appended, or as it is (`unwind_pfx`, `cancel_pfx`, `FireExt`); the bridges (`unwindOrder_of_core`, `noIntercept_of_core`, `cancellation_of_core`), the no-interception's added hypothesis in two halves (`CancelsStd`, `CancelsNoCtl`, `CancelsNZ`); a path that stops right after a fire step follows no unwind trace (`not_unwindTrace_one`) |
| | `Targets/Instance/FinRaise.lean`, `ELabels.lean`, `ETyping.lean`, `EHof.lean`, `ERuns.lean`, `E1.lean`, `E1Runs.lean`, `EProps.lean`, `E2.lean`, `E4.lean`, `E5.lean`, `E6.lean`, `E7.lean`, `E8.lean`, `E9.lean`, `E10.lean` | A's (E) properties at `J₁` (decision E): E1, E4, E6, E7 (E7c rejected at the rows without its inner label, decision D3) and E8 at every admissible context, E5, E9 and E2's `sumGen` program with no `unr` operation in the way, E10's `timeout` |
| **I** | `Targets/I/World.lean` | `SemWorld extends B.BWorld` (`held`, `Stop`, `share`), `coreW`, the effectful wp |
| | `Targets/I/Interface.lean`, `Device.lean`, `Pins.lean`, `Routes.lean` | I1–I5 at the world; `Bounds`, `Interface`, the proof device `Device`, `EmbedsNil`; R-CLOSEDOP; `effSafeOfFL`, `contractsW_of_meets` |
| | `Targets/I/Programs.lean` | the composite programs: `at02`, `at04`, `at12`, `at17`, `genSelf`, and the rejected AT05–AT08, AT13; AT08's control `at08Once` (the copy of `κ` used once); `AcceptedAt`, `Tier2Programs`, `Rejects`, `RejectsAT07` |
| | `Targets/I/Combined.lean` | **`I.Combined`**, done's statement; `Tier1`, `Tier1Core`; the corollaries |
| | `Targets/I/RunEnd.lean`, `Binder.lean`, `NonVacuity.lean`, `Restricted/*` | FIX-RUN-END's checks and witness worlds; the freeze binder at W; witnesses for the pins; the restricted results at `coreW` and `tier1` |
| | `Targets/I/OpenRel.lean`, `Tier1Route.lean` | Law 1 at the relation (`ovalW`, `FLOpen`, `fl_of_flOpen`); the elaboration route does not reach tier 1; `Tier1Core` from S5 (`tier1Core_of_S5`) |
| | `Targets/I/Restricted/InstanceSafety.lean` | S2, S3 and `LiveOK` at every typing system whose closed programs are Core's (today's kernel, `J₁`): a run under a runner is the run under its platform, and B2's runs give A's |
| | `Targets/I/J1.lean`, `GhostCoupling.lean` | B1, B's guarantees, the pins, FL at the open judgements and A's (S) properties at `J₁`, S4 at every effect context (`handlerSem_J₁`) and not vacuously (`catchLaw_progT_cell`); `Tier1 J₁` from what is open (`tier1_J₁_of`); route 8.4's obligation at the capture cell: R1 at a linear or affine operation is not in Core's relation (`not_semC_R1`) |
| | `Targets/I/ContUseJ1.lean` | S6 at the capture cell: a capture event allocates `κ`'s cell (`catchEv_cell`), a use releases it (`use_frees_cell`), leak freedom (`leakFreeAt_J₁`); S6 from the cell's ownership (`contUseEv_of_cells`, `contUseEv_J₁_of`) |
| | `Targets/I/Theories.lean` | the answering class at `J₁`: global state's handler correct, the tail law and algebraicity there |
| | `Targets/I/Rejects.lean` | inversions of Core's kernel (fourteen inductions on `CDerives`, a class of judgements carried through the same-term rules; every free variable of a typed term has a live slot, `fv_live`; `swap` typed at its axiom alone, `der_swap`); AT05, AT06, AT08 and AT13 have no derivation (`rejects_tier1`), AT08's by the continuation rule: its copy of `κ` is used on both sides of a split, and the same clause with the copy used once is typed (`d_at08Once`, `at08Once_runs`) |
| | `Targets/I/AcceptsRejects.lean` | decision AR: the composite's eight programs with their answers on computed runs (`compositeT1_tier1`), `Accepts` and `Rejects` at `J₁` (`I.accepts_J₁`, `I.rejects_J₁`); `Tier1 J₁` from A's (E) properties and S6, S4 and S5 being proved (`I.tier1_J₁_of_EU`; with S5, `I.tier1_J₁_of_ECU`; with S4, `I.tier1_J₁_of_ESU`) |
| | `Targets/I/AlgJ1.lean` | algebraicity at `J₁`, a finaliser's start observed but not its code, given `CfinQuiet` (`I.algLaw_J₁_of`): a typed program's runs answer data (`lamFree_answer_of_coreClosed`) and ask the runner at data (`lamFree_io_of_coreClosed`, `platData_of_start`) |
| | `Targets/I/CancelsNZ.lean` | no run of a typed program creates a handler named `0`, under every runner that keeps its protocol (`hndNZ_reach`: the runner is asked at data and answers data, a driven program's runs too, `driveData_of_reach`); so a cancelled continuation's context has no handler of `0` (`cancelsNZ_of_coreClosed`, `I.cancelsNZ_J₁`) |
| | `Targets/I/S5J1.lean` | S5 at `J₁` and today's kernel: a fired finaliser that meets the no-interception condition runs to `()` from every finite memory (`finOK_of_finRow`); the unwind (`unwindOrder_J₁`), the no-interception given `CancelsNamed` (`noIntercept_J₁_of`, `cancellation_J₁_of`, `cancellation_tier1Open`), which at `J₁` is a run invariant (`noIntercept_J₁`, `cancellation_J₁`); S5 read whole fails (`not_cancellationWhole_J₁`, `not_cancellationWhole_tier1Open`, `not_cancellationWhole_admissible`) |
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
`Combined orowRF J₁ coreW admClosedOp .abortive`; it is **OPEN** through A's (E) properties and
S6. S5, read prefix-closed (every run a prefix of a trace) and under frame deadness, is proved at
`J₁` at every effect context, its unwind outright and its no-interception from a run invariant
(`cancellation_J₁`, `cancelsNamed_J₁`); read whole it fails (`not_cancellationWhole_J₁`). S4,
restated so that a catch may allocate the capture cell, is proved at `J₁` at every effect context
(`handlerSem_J₁`). `J₁` is Core's kernel
with SPEC §24's rules over the open types, with the row `∀` (decision D5); our instance reads it at
an effect context with its handlers' and operations' rows tied to the context (decision R).
`Accepts` and `Rejects` are proved at `J₁` (decision AR; AT08 refused by the continuation rule), so
`Tier1 J₁` follows from A's (E) properties and S6 (`tier1_J₁_of_EU`).  Of the (E) properties at
`J₁`, E1, E4, E6, E7 (E7c rejected at the rows without its inner label, decision D3) and E8 are
proved at every admissible context, E5 and E9 where no `exn` is `unr`, E2d where no operation is;
E2a–c, E3 and E10's `retry` and loop are not derived (`status_eProps_J₁`).  So tier 1 needs, at
every admissible context, E2, E3 and E10, E5 and E9 where an `exn` is `unr`, and S6's two ownership
properties of the capture cell, `OnlyOwnerFrees` and `NoDanglingUse` (`status_tier1_J₁_of_open`).

**The restricted tier-1 reduction** `Tier1Core` (today's kernel `tier1Open`, Core's world)
follows from S5 at today's kernel (`tier1Core_of_S5`). Proved of it: A's properties but S5 at every
admissible effect context (`sPropsNoCancel_tier1Open`), B's guarantees, B5 included
(`tier1Core_guarantees`), the world conjuncts and the device at `coreW` (`tier1Core_world`), and
`Pins` (`pins_tier1Open`). Missing: S5 at our instance, whose unwind is proved there and whose
no-interception is proved given `CancelsNoCtl` (`cancellation_tier1Open`).

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
| B5 | release exactly once, location reuse included | PROVED (generic, from B4′), through the step-for-step simulation at the configurations a bump run reaches (`bumpSimAt`); so PROVED AT σ=[] at today's unr-free kernel and at `J₁`; not a tautology: PROVED | `releasedOnceReuse_of_soundContracts`, `releasedOnceReuse_tier1NU`, `I.releasedOnceReuse_J₁`, `not_releasedOnceReuse_staleFree` |
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
| the composite programs run (interpreter, evidence only) | checked | `at02_eval` … `at17_eval`, `genSelf_eval`, `at07_eval` (a use after free), `at08_eval` (the second resume frees `κ`'s cell again), `at08Once_eval` |
| `CompositeT1 tier1`: typed, safe and terminating under the empty platform, one complete run answering the stated value | PROVED AT σ=[] (the runs computed by `runM`) | `compositeT1_tier1`, `acceptedT1_*`, `run_*` |
| `Accepts J₁.read .abortive`, `Rejects J₁.read` (decision AR) | PROVED AT σ=[]; AT08 RESTATED (M5), refused by the continuation rule | `I.accepts_J₁`, `I.rejects_J₁`, `Rej.not_der_at08`, `Rej.d_at08Once` |
| `Tier2Programs`, `RejectsAT07` at a typing system | OPEN | — |
| I1, I3, I5, P11 at `coreW`; I2 at abortive rows; `EmbedsNil coreW` | PROVED AT σ=[]; AT A RESTRICTION | `status_device_core`, `embedsNil_core` |
| FIX-RUN-END's checks and witness worlds | PROVED | `Targets/I/RunEnd.lean` |

### The Instance

| target | status | Lean |
|---|---|---|
| `tier1Open.read = tier1NU` | PROVED | `tier1Open_read` |
| `ConfLaws`, `KontLaws`, `NoIO`, `DataInj`, `LiftExt` at our instance | PROVED | `confLaws_ourInst`, `kontLaws_orow`, `noIO_ourInst`, `dataInj_ourInst`, `liftExt_orow` |
| our rows meet Def. 3.5 and Def. 5.1 | PROVED AT A RESTRICTION (`orowRF`) | `rowAlgSafe_orowRF`, `rowLink_orowRF` |
| no typed term intercepts a cancel; the two-frame unwind | PROVED AT σ=[]; an instance | `noInterception_tier1`; `two_frame` |
| the semantic bridges (`AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`, `LetLaw`, `RowAlgebra`, `Safety`, `EffSafe`, `HandlerSem`, `Cancellation`, `ContUseEv`) | S0, the let law, S1, S2, S3 and S4 (at the capture cell) PROVED AT σ=[] at `J₁` and today's kernel (`Targets/Status.lean`); `Cancellation` FAILS AS WRITTEN; `ContUseEv` OPEN | `status_sPropsNoCancel_J₁`, `status_machShape_handlerSem` |
| `monoCallback_tier1Open`, R1–R4 at our machine | OPEN | — |
| A's (E) properties at `J₁` (decision E) | `EProps` FAILS AS WRITTEN (E7, E8, E9; option A). PROVED: E1, E4, E6 at every admissible context; E5 where no `exn` signature is `unr`; E2d where no operation is `unr`; E10's `timeout`. NOT DERIVED, no obstruction verified: E2a–E2c and E10's `retry` (a function at `!U C` forced), E3 and E10's loop (`unfold`'s stepped value `etaN`) | `status_eProps_J₁`, `e2d_J₁`, `derV_timeoutR_J₁`, `polyUseOpen_timeoutR_J₁` |

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
| A3 multiplicity soundness | A's S6 `ContUseEv` (linear and affine continuations); multi-shot dropped (decision 63) |
| A4 lifetime and escape soundness | B7 `LifetimeSound`; S3 |
| A5 exclusivity across the handler | B6 `ExclusiveB`, I's `Exclusive`, I4 |
| A6 discard semantics | resource half: B4 with B5; continuation half: S6 `ContUseEv`; S5 `Cancellation` |
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
