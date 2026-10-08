import Targets.I.Combined
import Targets.B.NonVacuity
import Targets.B.Release
import Targets.Instance.Bridges
import Targets.Instance.Binary
import Targets.Instance.ZeroCost
import Targets.Instance.Checks
import Targets.Instance.Safety
import Targets.Instance.LiveWitness
import Targets.Instance.Restricted.NoInterception
import Targets.Instance.Restricted.Unwind
import Targets.Instance.Restricted.Programs
import Targets.A.NonVacuity
import Targets.A.Binary
import Targets.A.UnaryLaws
import Targets.A.Lowering
import Targets.Audit
import Targets.I.Tier1Route
import Targets.I.Restricted.FinAlone
import Targets.Instance.ClauseRefusals
import Targets.Instance.ContUse
import Targets.Instance.RunTyping
import Targets.I.Restricted.InstanceSafety
import Targets.I.GhostCoupling
import Targets.I.J1
import Targets.I.Theories
import Targets.Instance.UnaryLaws

/-!
# Targets — status, by system (RESTRUCTURE §0)

Status words: **PROVED**, **PROVED AT σ=[]**, **PROVED AT A RESTRICTION** (the restriction named),
**OPEN**, **FAILS AS WRITTEN** (a machine-checked configuration; the restatement is the user's),
**RESTATED** (by the user's decisions of 2026-10-07, below; a refutation of the earlier statement is
not kept).  Four parts: **A**, an effect system, abstractly; **B**, the borrow calculus, given;
**I**, the interaction and the combined theorem; **the Instance**, our calculus as one instance of
A.

## Done

Done is `I.Combined orowRF J₂ W admClosedOp .any` (`Targets/I/Combined.lean`) at a **named**
tier-2 typing system `J₂` and a **named** world `W`, with `audit_W` (`Targets/Audit.lean`): A's
properties at our instance at every admissible effect context, B's guarantees in the composite, the
interaction's option-neutral rules, the pins, the composite's programs and its rejections.  Fixed at
`admClosedOp` until OQ-56 is chosen and at `orowRF` until OQ-13's remaining question is answered.

**Done: OPEN.**  Neither `J₂` nor `W` is defined.

**Tier 1** (`I.Tier1 J₁`): OPEN, **reduced** (`status_tier1_J₁_of`).  `J₁` is built (decision D5):
Core's kernel with SPEC §24's rules (the polymorphic let, the general `[handle]`, `[then]` at option
A) over the open types, with the row `∀` (`Targets/Instance/J1.lean`).  Proved of it: A's (S)
properties but S5 and S6 at every effect context, B's guarantees (B5 given `BumpSim`), the world's
conjuncts and the pins.  `I.Tier1 J₁` follows from what is open: A's (E) properties, S5 and S6 at
every admissible effect context, the composite's programs (`Accepts`) and rejections (`Rejects`),
and `BumpSim`.  TIER1-PLAN §2's first route (elaborating each derivation into the kernel before
D5) does not reach tier 1 (`status_elab_route`); `J₁` is built by D5's route instead.

**The restricted tier-1 reduction** (`I.Tier1Core`, at today's kernel `tier1Open` and Core's world):
**PROVED AT σ=[] given S5 at today's kernel and `BumpSim`** (`status_tier1Core_of`).  Proved of it:
A's properties but S5 at every admissible effect context — S0 and S4 (from `LiveOK`, proved), the
let law, S1, `DataDiv`, S2 and S3 (`status_sPropsNoCancel_tier1Open`); B's guarantees but B5
(`status_tier1Core_B`), and B5 given `BumpSim` (`status_releasedOnceReuse_tier1Open_of_bumpSim`);
the world conjuncts and the device at `coreW` (`status_tier1Core_world`); its `Pins` conjunct
(`status_pins_tier1Open`).  Missing: S5 at our instance (its bridges `noIntercept_of_core`,
`unwindOrder_of_core` are not built) and `BumpSim` (OQ-43).

## The decisions of 2026-10-07

* **D1, rows tied to the effect context** (`RowAt`).  Our instance reads a program only at a
  returner whose row, at every row environment tied to `Ξ`, is tied to `Ξ` (`OCTy.TiedAt`): every
  operation it finds is a label's, at the signature `Ξ` declares; `orowAlg`'s well-formed rows are
  tied rows.  The tie is needed: today's `[perform]` types a program at a row no label's operation
  is in, stuck at once (`safety_needs_tie`), and a runner's answer at a type the row does not
  declare leaves a run stuck (`liveOK_needs_tie`).  It gives S2, S3 and `LiveOK`.
* **D2, distinct keys and positive loop bodies.**  B2's drive conjunct, `SoundDriveAt`,
  `EffSafeDrive` and our instance's loop sums take `CTy.NuOk` of the loop body (decision D2: `νX. C`
  is well formed at a positive `C`); at rows with distinct keys that a platform answers, every loop
  body is positive (`loopEffBody_nuOk_of_uniq`).  The hypothesis is needed
  (`adequateDrive_needs_nuOk`, `effSafeDrive_needs_nuOk`).
* **D3, finalisers: option A.**  S5's endings are parameterised by the labels whose raises a
  finaliser may let escape (`Cancellation FR`); the target reads the empty instance `noFinRaise`.
  `FinaliserOrder` reads the same parameter (`FinAloneAt FR`, platform-free, subsuming `FinAlone`);
  option A's is `finaliserOrder_A`.  The kernel half is applied with D5: Core's `[then]` types its
  finaliser at the pure row (SPEC §24, `CDerives.effThen`), and so do `CDerivesNU` and the pin's
  `RC_effThen`.  Check 2's derivations, whose finalisers let a raise escape, are not kept.
  OQ-7 is separate and open.
* **D4, the restatements.**  S6 counts a step that applies `κ` to a data value as a use (`UseAt`);
  `RunsAlike` (read by `AlgLaw`, `TailLaw`, `EtaHold`) compares a program's data answers;
  `EffSafeDrive` observes a finished drive (`DoneDrive`); S5's runs carry the no-interception
  condition on the finalisers they fire (`FinRow`: a finaliser is typed at a row of abortive
  operations of labels in `FR`).  The condition is needed (`noIntercept_needs_finRow`).
* **D6, S1.**  `SubClosed` carries `[sub]`'s well-formedness premise.  At an admissible context a
  well-formed row is unr-free (`rowNU_of_wf`), and S1 holds at today's kernel
  (`rowAlgebra_ourInst_tier1Open`); the premise is needed (`subClosed_needs_wf`).  The earlier
  refutation used a row that is well formed at no admissible context, and is withdrawn.
* **D5, `J₁` by new Core rules** (SPEC §24).  Core's `CDerives` gains the polymorphic let
  `letPoly` (a closed λ-value bound by substitution, so one function is used at several rows) and
  the general `[handle]` `effHandleV` (the handler a value form over a persistent context; the
  two-variable form `CDerives.effHandle` is its instance), and its `[then]` takes the finaliser at
  the pure row; each with its `fundamentalC` case (`letPoly_compatC`, `handleV_compatC`,
  `thenA_compatC`); `fundamentalC`, `adequacyC` and `adequacyD` keep their statements.  No change to
  the machine, the relation or the borrow rules.  `tier1Open` (`CDerivesNU`) is the kernel's
  unr-free fragment without the two additions; the rows below that read "today's kernel" are about
  that fragment.  `J₁` closes a polymorphic slot by substitution (`fillS`), so its reading is Core's
  kernel (`j1_read`) and its FL is `fundamentalC`; at a context with no polymorphic slot its open
  judgements meet `FLOpen`'s relation, a polymorphic type read as the intersection of its instances
  (Law 1, `flOpen_J₁_mono`).
* **S6 by a ghost obligation in `contShare` (route 8.4): probed, and stopped.**  At BoLo's relation
  a closed program at its pure type is related by `wpTS`, where no protocol table occurs; R1 (κ
  never used), R2 (κ resumed twice) and R3 (a linear κ cancelled) are in it and break S6
  (`status_ghostCoupling`: a typing system with FL at BoLo fails S6); along their runs the heap is
  empty and BoLo's world at the empty heap is the empty resource, so `NoOwn` sees no obligation.
  The route needs a resource kind or a run-end condition BoLo's model does not have.
* **An encoding defect, repaired.**  Reading every operation index through `UInt32.ofNat` made `i`
  and `i + 2³²` one operation, and a runner keeping its protocol could answer the second at any
  type; checked in Lean before the repair.  An index beyond `UInt32` now encodes to an open stuck
  term (`opJunk`), which no closed configuration holds.

## Piece 5: the answering class (D1.h1, D1.h3, D1.h4)

* **Theories** (D1.h3, D1.h4; `Targets/A/Theories.lean`).  Equations are writable in signatures:
  an equation is two straight-line computations over one label's operations and the same
  parameters, ending in the continuation (`Eqn`, `SLComp`, `Theory`, OQ-22 (a)).  The answering
  handler is the state-passing handler of co-operations (`ansHnd`, decision 59); it is a model of
  a theory when the two sides of each equation, handled and run from each state, run alike
  (`AnsCorrect`, Plotkin–Pretnar Def. 4.5 at `RunsAlike`); co-operations are a comodel when their
  own runs of the two sides reach one final state and continuation argument (`IsComodel`,
  Ahman–Bauer Def. 1 with equations).  Global state is the first theory (`stateTheory`, four laws).
* **The comodel reduction, D1.h4 (c)** (`ansCorrect_of_comodel`): at our instance, co-operations
  that run quietly (`PureCo`, this piece's added hypothesis) and form a comodel give a correct
  handler, at every typing system whose reached configurations are closed: the handled sides fold
  as the co-runs do (`quiet_fold`, the native counterpart of `handle_fold`) and meet.  `stateCo`
  is a comodel and its handler correct (`state_isComodel`, `state_correct`; at `J₁`,
  `I.state_correct_J₁`).  Not vacuous: at `J₁` and an admissible context with a state signature
  (`Ξst`), the handler whose `put` keeps the old state fails the update–lookup law at a typed
  program, and its co-operations are no comodel (`status_theories`).
* **The unary laws at our instance** (D1.h1, D4's restatement).  **Algebraicity FAILS AS WRITTEN
  at `J₁`** (`status_unaryLaws`): an inner handler at an `unr` operation holds its persistent
  continuation in a finaliser frame, and the trace's `fire D` compares `D`'s code, which mentions
  the continuation the two sides capture differently (`Targets/Instance/UnaryLaws.lean`).  At a
  linear or affine continuation no finaliser at `F 1` can hold it.  Two repairs, the user's: a
  finaliser's start observed without its code (D4 read at the trace's events), or `unr`
  restricted (decision 63).  The tail-resumptive law and η: OPEN (below).  At the answering class
  (a tail-resumptive clause whose code runs quietly) both the tail-resumptive law and
  algebraicity hold (`tailLaw_quiet`, `algLaw_quiet`; at `J₁`, `I.tailLaw_quiet_J₁`,
  `I.algLaw_quiet_J₁`).

## System A

| target | status | Lean |
|---|---|---|
| `EffectSystem`, S0–S6, E1–E10, `Props`; A₂ (`HandlerLaws`, `EffDepLaws`, `Abstraction`); A₃ (`Tgt`, `LoweringCorrect`, `ZeroCost`) | stated (elaborate) | `Targets/A/*` |
| a typing that types nothing fails `EProps`; no effects fail it | PROVED (every instance) | `not_eProps_of_emptyTyping`, `not_eProps_of_noLabels` |
| E1, E2, E6, E10 need effect polymorphism (row variables, decision 62) | PROVED (every instance; E10 with `LiftExt`) | `not_noColouring_of_monoCallback`, `not_higherOrderPoly_of_monoCallback`, `not_tunnel_of_monoCallback`, `not_reconciler_of_monoCallback` |
| E3 needs divergence; a pure-row loop that diverges is not at a data answer | PROVED (every instance; the latter with `RowAlgebra`) | `not_loops_of_total`, `divInTypes_of_loops` |
| effect safety has teeth; Def. 5.1 (1) from one signature object | PROVED (every instance) | `not_der_unhandled`, `c1_of_rowSig` |
| the runners `Rtick`, `Rtl`, `Rrec` keep their protocol | PROVED (every instance; `Rrec` at distinct labels) | `rtick_respects`, `rtl_respects`, `rrec_respects` |
| A's properties at our instance | at today's kernel, every admissible effect context: S0, the let law, S1, `DataDiv`, S2, S3, S4 PROVED AT σ=[]; at `J₁`, every effect context: the same, PROVED AT σ=[]; S5 OPEN (bridges not built); S6 OPEN (below) | `status_sPropsNoCancel_tier1Open`, `status_sPropsNoCancel_J₁` |
| the unary laws beside done, `UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`) and the alternative `EtaLin`: run-level (menu form F.3), the tail law's hygiene as hypotheses, compared at a program's data answers (D4) | RESTATED; STATED (at our instance: the Instance's rows); **not in done**: whether they join done is a menu choice (P11/I5 menu axes H, F, K), for the user | `Targets/A/UnaryLaws.lean` |
| theories (D1.h3, D1.h4 (a)–(b)): equations in signatures (`Eqn`, `SLComp`, `Theory`), the state-passing handler of co-operations (`ansHnd`, `runAt`), handler correctness (`AnsCorrect`, Plotkin–Pretnar Def. 4.5 at `RunsAlike`), comodels (`IsComodel`, Ahman–Bauer Def. 1 with equations), global state (`stateTheory`, `stateCo`, `badStateCo`) | stated (elaborate); at our instance: the Instance's rows | `Targets/A/Theories.lean` |
| `EtaHold` gives `EtaLin`; each of the four fails at an instance whose handler or bind ignores its clauses | PROVED | `etaLin_of_etaHold`, `not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy`, `not_etaLin_toy` |
| A₃'s reference programs (the `Tgt` code checking each `refCost` entry) | not written | RESTRUCTURE §Unresolved |

## System B

| id | guarantee | status at BoLo | Lean |
|---|---|---|---|
| B0 | BoLo's programs stay typed | PROVED AT σ=[] | `extendsB_tier1` |
| B1 | the fundamental property | PROVED AT σ=[] | `fl_core_tier1`, `fl_core_tier1NU` (at `coreB`) |
| B2 | adequacy | PROVED AT σ=[] at every platform that keeps its protocol: the return conjunct through its answers; the drive conjunct at positive loop bodies (D2), so at rows with distinct keys. The hypothesis is needed: at a loop type whose body is not positive (a shadowed entry with an open type) `cC` holds of `()`, whose drive is stuck at `nextE ()` | `adequateRetAt_core`, `adequateDriveAt_core`, `adequate_core`, `adequateDriveAt_core_uniq`, `adequateAt_core_none`; `adequateDrive_needs_nuOk` |
| B3, B4 | safety, leak freedom | PROVED AT σ=[] at today's unr-free kernel (from FL and B2), the drive conjunct at positive loop bodies | `sound_tier1NU`, `soundRetAt_tier1NU`, `soundDriveAt_tier1NU` |
| B4′ | with externs meeting W's contract | PROVED (generic, from B1 and B2, finding #7); from B1 and B2's return conjunct alone (generic), so PROVED AT σ=[] at today's unr-free kernel | `soundContractsOfFL`, `soundContractsOfFL_ret`, `soundContracts_tier1NU` |
| B5 | release exactly once, reuse included | from B4′ given the step-for-step simulation `BumpSim`: PROVED (generic), and so at today's unr-free kernel; `BumpSim` itself OPEN (OQ-43), its conclusion met at a reuse step: PROVED; not a tautology: PROVED | `releasedOnceReuse_of_bumpSim`, `releasedOnceReuse_tier1NU_of_bumpSim`, `bumpSim_at_reuse`, `not_releasedOnceReuse_staleFree` |
| B6 | exclusive mutable borrows | PROVED AT σ=[] | `exclusiveB_core` |
| B7 | lifetimes respected | PROVED AT σ=[] | `lifetimeSound_core` |
| — | the bounds | PROVED AT σ=[] | `wBound_core` |
| — | `ReleasedOnceAll` | a **tautology about runs** (finding #2), a lemma, not a guarantee | `releasedOnceAll` |
| — | the run-end laws where `Upd` is Core's | PROVED (generic); at `coreB` | `updRefl_of_core` …, `updRefl_core` … |
| — | P14: `WBCore`; `ConservativeWB`, `Conservative` at `coreB` | PROVED; PROVED AT σ=[] | `wbCore`, `conservativeWB_core`, `conservative_core` |

## The interaction

| target | status | Lean |
|---|---|---|
| `Bounds coreW`, `Interface coreW`, `Device coreW tier1Open.read admClosedOp .abortive`, `WBCore` | PROVED AT σ=[] (abortive rows) | `I.tier1Core_world` |
| the corollaries of `Combined` | PROVED (generic) | `combined_prog`, `i1Prog_of_combined`, `i2Prog_of_combined`, `effSafe_core_of_combined`, `soundnessContractsAR_of_combined` |
| Core's extern contract gives W's at row-abortive types, with `EmbedsNil` | PROVED (generic) | `contractsW_of_meets` |
| a reachable leak breaks the combined theorem | PROVED (generic) | `not_combined_of_leak`; the witness `leakW` |
| the composite programs run (interpreter, evidence) | checked | `at02_eval` … `at17_eval`, `genSelf_eval` (the generator borrowing its own state), `at07_eval` (AT07 runs into `useAfterFree`) |
| `CompositeT1 tier1`'s typing and safety | PROVED AT A RESTRICTION (`Platform.none`) | `acceptedT1_*` |
| `Tier2Programs`, `Accepts`, `Rejects`, `RejectsAT07` | OPEN (no tier-2 typing system; inversions to build) | — |
| `EffSafe tier1` (Core's P2) | PROVED AT σ=[] | `effSafe_tier1` |
| `EffSafeDrive` (P2 for driven programs), RESTATED (D2: a positive loop body; D4: a finished drive observed, `DoneDrive`) | PROVED AT σ=[] at every typing system with FL at BoLo, so at today's unr-free kernel; the hypothesis is needed; the route at a generic world, `EffSafeDriveOfFL`, OPEN | `effSafeDrive_of_FL`, `effSafeDrive_tier1NU`; `effSafeDrive_needs_nuOk` |
| `Pins tier1Open admClosedOp .abortive`, with `I4a` at the unr-free rules | PROVED AT σ=[] (abortive rows) | `I.pins_tier1Open`, `i4a_tier1NU` |
| Law 1 at the relation: `ovalW` at `U(∀ρ:k. C)` and `!U(∀ρ:k. C)` is the intersection of the instances; `FLOpen M J` gives `FL M J.read`; `FLOpen` at today's kernel | PROVED (generic); PROVED AT σ=[] | `I.ovalW_allR`, `I.ovalW_bang_allR`, `I.fl_of_flOpen`, `I.flOpen_core_tier1Open` |
| `J₁`: its reading is Core's kernel; FL at BoLo (B1); B's guarantees, B5 given `BumpSim`; the pins; FL at its open judgements over contexts with no polymorphic slot, a polymorphic type read as the intersection of its instances (Law 1) | PROVED AT σ=[] (abortive rows for the pins); `FLOpen coreB J₁` at contexts with a polymorphic slot NOT PROVED (a value `ovalW` relates there need not be a closed λ-value Core types) | `status_j1`, `status_guarantees_J₁`, `status_pins_J₁`, `I.flOpen_J₁_mono` |
| tier 1 at `J₁` | OPEN; follows from A's (E) properties, S5, S6, `Accepts`, `Rejects` and `BumpSim` | `status_tier1_J₁_of` |
| TIER1-PLAN §2's route (elaborate `J₁` into today's unr-free kernel, then `fundamentalC`) | **DOES NOT REACH TIER 1**: closed derivations that elaborate type no A-level handler, so E8 fails; today's kernel types no let-bound function read at two rows | `I.not_tier1_of_elabClosed`, `not_der_letTwo` |
| FIX-RUN-END's checks and witness worlds | PROVED | `Targets/I/RunEnd.lean` (73 results) |
| I1, I3, I5, P11 at `coreW` (the device); I2 at `coreW` | PROVED AT σ=[]; PROVED AT A RESTRICTION (abortive rows) | `i1_core`, `i3_core`, `i5_core`, `p11_core`; `i2_core_abortive` |
| `EmbedsNil coreW` | PROVED AT σ=[] | `embedsNil_core` |
| `AdequateOfLaws`, `FreezeBinder`, `BinderMachine`, `NotVDenNaturalArises`, `I4Typing`, `I4c` | OPEN (stated) | — |

## The Instance

| target | status | Lean |
|---|---|---|
| `ourInst RF Ξ J`, `AdmEff`, the open types, `OurTyping`, `tier1Open`, `read` | defined | `Targets/Instance/*` |
| `tier1Open.read = tier1NU` | PROVED | `tier1Open_read` |
| `ConfLaws`, `KontLaws` (names told apart), `NoIO`, `DataInj` at our instance | PROVED | `confLaws_ourInst`, `kontLaws_ourInst`, `kontLaws_orow`, `noIO_ourInst`, `dataInj_ourInst` |
| `LiftExt` at the tail-variable rows | PROVED | `liftExt_orow` |
| our rows meet Def. 3.5 and Def. 5.1; `RowLink orowRF` | PROVED AT A RESTRICTION (`RF = orowRF`) | `rowAlgSafe_orowRF`, `rowLink_orowRF`, `closedRowAlg_lawsSafe` |
| no typed term intercepts a cancel; the two-frame unwind | PROVED AT σ=[]; an instance | `noInterception_tier1`; `two_frame` |
| the machine read through contexts: run splitting, determinism where nothing is allocated, runs that join run alike, closed runs stay closed, no step creates a handler named `0` | PROVED AT σ=[] | `steps_plug_split`, `det_ourInst`, `rstep_det`, `runsAlike_of_join`, `closed_steps`, `hndNamesNZ_steps` |
| S0 (`MachShape`: `AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`) and S4 (`HandlerSem`) at our instance | PROVED AT σ=[] given `LiveOK` (every configuration a typed program reaches has a closed term and goes on), at every typing system; `Congr` and `OpStuck` without it. At today's kernel `LiveOK` holds at every effect context (D1), so S0 and S4 are PROVED AT σ=[] there. `LiveOK` needs the tie | `machShape_orow`, `handlerSem_orow`, `handlerSem_ourInst`; `liveOK_tier1Open`, `status_machShape_handlerSem_tier1Open`; `liveOK_needs_tie` |
| `LiveOK` is met at a typing system that types one program with a handler, an operation it catches and a continuation | PROVED | `liveOK_JnLog` |
| S5 (`Cancellation noFinRaise`) at our instance, RESTATED (D3, D4) | OPEN: the bridges `noIntercept_of_core`, `unwindOrder_of_core` are not built. The no-interception condition is needed: `NoInterception` is syntactic, and a typed program's cancelled finaliser may perform the operation its region's dying handler catches; its run follows no cancel trace at any set of endings | `noIntercept_needs_finRow` |
| Core's `FinaliserOrder` (I3.b) | PROVED, given `NoInterception` and `FinAloneAt FR` (a fired finaliser's run alone, platform-free, ends at a value or an uncaught raise of a name in `FR`), at today's endings (nonzero names) and at option A's (none). At a typing system with FL at Core's world, `FinAloneAt FR` follows from `FinRowsAt FR` (an operation the finaliser's run alone leaves uncaught is a raise of a name in `FR`): stuck redexes are excluded by FL and B2's runs. So at today's unr-free kernel `FinaliserOrder` follows from `FinRowsAt` alone (PROVED AT σ=[]). `FinRowsAt` OPEN: route 8.2's obligations (`RowRoute`) give it (PROVED), and no `RowRoute` is built (TIER1-PLAN §4: the review did not accept route 8.2) | `finaliserOrder_at`, `finaliserOrder_A`, `finAloneAt_of_finRows`, `finaliserOrder_tier1NU_of_finRows`, `finaliserOrder_tier1NU_of_finRowsA`, `finRowsAt_of_route`, `finaliserOrder_of_route` |
| `FinAlone` (piece 1's added hypothesis) | RESTATED by D3: its consumer reads `FinAloneAt FR`, platform-free | — |
| S6 (`ContUse`) at our instance, RESTATED (D4: a use is a step that applies `κ` to a data value) | OPEN at today's kernel and at `J₁` | — |
| route 8.4 to S6: a ghost obligation in `contShare`, consumed where `κ` is resumed or cancelled, read by `NoOwn` at a run's end | **STOPPED at its probe**: FL at BoLo does not give S6, at one capture, one resume and one cancel (R1, R2, R3 are in Core's relation at `F bool`, whose clause is `wpTS`, and break S6); along their runs BoLo's world is the empty resource | `status_ghostCoupling`, `I.not_ghostCoupling`, `I.ghost_probe`, `I.lower_empty_eq` |
| S6's teeth: R1–R4 (RESTRUCTURE §6.1) at our machine | PROVED: every typing system over our machine that types one of them at `F 0 bool` fails S6 (R1 at a label whose first operation resumes, R3 at a linear one, R2 and R4 at any; at a general row form, given what `orowRF` gives); `JR` types all four, and at `ΞA` each lemma applies | `not_contUse_of_der_R1` … `_R4`, `not_contUse_of_der_R1_orow` … `_R4_orow`, `teeth_JR_ΞA` |
| today's kernel types none of R1–R4 | PROVED, by the handler's form (our handler is the run-time frame, its clauses values; `[handle]` types clause variables). At the clauses, by the linearity of `κ` (RESTRUCTURE §6.1's reason): today's clause typing refuses R1's, R2's and R4's clauses at every resuming `lin` or `aff` operation (a live slot of `kTy` is neither dropped nor duplicated) and R3's at every `lin` one (a linear `κ`'s cancel is at `⊤`); at the clause type of a linear `1 ↠ 1`, where all four are refused, a clause that resumes `κ` once is typed, and `cancelCl` is typed at `aff` and refused at `lin`. At `unr` the argument does not apply (multi-shot is not considered) | `refuses_R_tier1Open`, `refuses_R_clauses`, `clauseRefusals_pinned` |
| `AlgLaw`, `TailLaw`, `EtaHold` at our instance, RESTATED (D4: data answers) | `AlgLaw` **FAILS AS WRITTEN at `J₁`**, at the admissible `ΞA`: `algFireProg`, typed by Core's kernel, reaches the law's left side under a handler at an `unr` operation whose clause holds its persistent continuation in a finaliser and raises; the two runs answer `()` and show `fire` of finalisers that differ as terms. `TailLaw` OPEN: by this mechanism no witness types (an `unr` outer handler forces the tail clause's continuation context persistent, and our instance's `resume` forces only a `U` slot); not proved. `EtaHold` OPEN: `[handle]`'s `hnS` keeps a forwarding handler's own name out of its clauses' row, so by that reading no typed program installs one (not checked by an inversion); not proved | `not_algLaw_J₁`, `not_algLaw_ΞA`, `d_algFireProg`, `finE_DL_ne` |
| the tail-resumptive law and algebraicity at the answering class (a clause `λ(a, k). c a to b. k.resume b` whose code runs quietly) | PROVED at every typing system with `LiveOK`, so at `J₁` | `quiet_tailClause`, `tailLaw_quiet`, `algLaw_quiet`, `I.tailLaw_quiet_J₁`, `I.algLaw_quiet_J₁` |
| D1.h4 (c), the comodel reduction: co-operations that run quietly (`PureCo`) and form a comodel give a correct handler | PROVED at every typing system with `LiveOK` whose typed closed values are closed | `ansCorrect_of_comodel`, `quiet_fold`, `quiet_opStep`, `quiet_coFrom` |
| global state: `stateCo` a comodel of the four laws, its handler correct; not vacuous | PROVED (at `J₁`: `I.state_correct_J₁`); at `J₁` and the admissible `Ξst`, the handler whose `put` keeps the old state fails the update–lookup law at a typed program, and its co-operations are no comodel | `state_isComodel`, `state_correct`, `I.state_correct_J₁`, `not_ansCorrect_badState`, `not_isComodel_badState`, `admEff_Ξst` |
| `LetLaw` at today's kernel | PROVED (typing) | `letLaw_ourInst_tier1Open` |
| S1 (`RowAlgebra`) at our instance, RESTATED (D6: `SubClosed` at a well-formed target row) | PROVED at today's kernel, at every effect context with no resuming `unr` operation, the admissible ones among them; `EA.Laws`, `EA.Safe` and `RowSig` at every typing system. The premise is needed | `rowAlgebra_ourInst_tier1Open`, `rowAlgebra_noSub_ourInst`, `subClosed_nu_tier1Open`, `rowNU_of_wf`; `subClosed_needs_wf` |
| A-level handlers at today's kernel | **NOT TYPED** by `tier1Open` (the kernel's fragment without SPEC §24's rules): our instance's `handle` is the run-time frame, clauses as values; the fragment's `[handle]` types only `hndTerm n ir ic e`. So E4, E5, E6, E7 and E8 **FAIL** at `tier1Open` at every effect context.  Core's `[handle]` (§24) types the frame form, and so does `J₁`; no (E) property is checked at `J₁` | `not_der_handleK`, `not_der_handle_tier1Open`, `status_handlers_tier1Open` |
| a let-bound function used at two rows; a persistent function called at an effectful row | **NOT TYPED** by today's kernel: one slot has one type, of which every judgement a variable is read at is a view; a variable used as a function is a `U` slot | `not_der_letTwo`, `der_var_inv`, `der_var_arr_thunk`, `not_der_callBang` |
| `Safety` (S2), `EffSafe` (S3), `LiveOK` at our instance | PROVED AT σ=[] at today's kernel, every effect context (D1): a run under a runner is the run under the platform it gives (`platformOf`), step for step from a typed program, and B2's runs give A's. The tie is needed | `safety_ourInst_tier1Open`, `effSafe_ourInst_tier1Open`, `liveOK_tier1Open`; `safety_needs_tie`, `liveOK_needs_tie` |
| `DataDiv` at our instance | PROVED (every row form, effect context and typing system) | `dataDiv_ourInst` |
| `J₁`, `Pins J₁`, the let law and S1 at `J₁` | BUILT; PROVED AT σ=[] (S1 at every effect context: Core's `[sub]` asks nothing of its rows) | `Inst.J₁`, `status_pins_J₁`, `status_sPropsNoCancel_J₁` |
| `RowVarKernel J₁`, the schema halves of E1, E2, E6, E10, the (E) programs at `J₁` | NOT PROVED, not attempted.  A schema's callback `λ_. M` puts `M`, typed at the empty context, under a live binder it does not use (Core's `lam`); Core's λ with a dead binder (`thunkF`) is at the pure returner only, and Core has no weakening by an unused live slot (a direct induction meets `bangThunkV`'s `Persistent` premise).  `[allR-I]` at `J₁` reads a value judgement at `U C` as Core typing the λ at `C`, an inversion of Core's thunk rules.  Neither is derived, and no obstruction is verified | — |
| `monoCallback_tier1Open` (today's kernel fails E1, E2, E6, E10); the positive (E) runs at `tier1Open` | OPEN (inversions and runs to build, RESTRUCTURE §6.1) | — |
| `RowVarKernel J₂`, `spanRules_J₂` | OPEN (`J₂` not built) | — |
| A₂ over Core (`Laws`, `Abstraction`), A₃'s lowering classes | stated, out of the first pass | `Targets/Instance/Binary.lean`, `Targets/Instance/ZeroCost.lean` |

## The step-index audit (finding #6)

`coreW`'s report (`Targets/Audit.lean`, pinned): report 1, `Cell` (`WellFounded.fix`: the
stratification by lifetime decision 7 keeps), `sepRange`, `tabFill`, `dropFill` and their
auxiliaries (recursion on an array's length), and the matchers `clauseAt.match_1`,
`VTy.upR.match_1` (a clause's index, a de Bruijn index: data); report 2, `AHead`, `ARun` (index `ℕ`:
the allocator's allocation count, never decremented, which selects the allocator's location), and,
via `Loc` only, `Head`, `Chain`, `GPos`, `LinPath`, `MutPos`, `RefPos`, `TW` (heaps, resources,
locations: names); report 3, `Table`, `ewpTS`, `vCE._f` (their `∀`-bound predicates range over
lend records, `List SRec`, whose `Life` is a lifetime); report 5 (a), `AHead.alloc`, `AHead.tab`
(the allocation count).  Reports 4 and 5 (b): none.  The nine negative tests pass, each at its own
entry.

## Retired and restated (nothing silently dropped)

* `EndStateAt`, `EndState`, `Guarantees` (the library's), `Tier1End`, `EndStateBinder`: restated
  as `I.Combined`, done, `B.Guarantees`, `I.Tier1` (with `I.Tier1Core`) and `I.CombinedBinder`.
* `status_tier1End_of` (`Adequate coreW → FinaliserOrder tier1 → Tier1End`): **retired**.  Its
  conjuncts `EffSafe`, `NoInterception` and `FinaliserOrder` became A's properties at our instance,
  which need the bridges, and B5 now has content, which needs `BumpSim`.  Its proved content is
  kept: `status_tier1Core_world`, `status_tier1Core_B`, `status_tier1Core_guarantees_of_bumpSim`.
* The refutations of the statements the decisions of 2026-10-07 restated are not kept: of B2's
  drive conjunct, `Adequate coreB`, `I.Tier1` and `I.Tier1Core` without a positive loop body; of
  `EffSafeDrive` and `EffSafeDriveOfFL` before D2 and D4; of S2, S3 and `LiveOK` before the tie; of
  `FinAlone` over every platform; of S5, S6, `AlgLaw` and `TailLaw` before D3 and D4 (checks 1–3);
  of S1 without `[sub]`'s premise.  What each restatement needs is pinned (the decisions, above).
* `endState_prog`, `i1Prog_of_endState`, `i2Prog_of_endState`, `not_endState_of_leak` (and their
  status rows): restated as `combined_prog`, `i1Prog_of_combined`, `i2Prog_of_combined` (at
  `c = .any`), `not_combined_of_leak`.
* `P8a`, `p8a_of_endState`, `status_p8a_of_endState`: **retired**.  `P8a` was `ReleasedOnceAll`
  read at the runs that capture a continuation, a tautology about runs (#2); P8.a is B4 with B5, and
  P8.b (the use count) is A's S6 `ContUse`.
* `ReleasedOnceAll`: kept as a lemma about runs (`releasedOnceAll`), out of done; done holds B5
  `ReleasedOnceReuse`, restated (per-step maps from a bump run, `ContractsW`).
* `effSafeOfFL`, `soundnessContractsOfFLWB`: restated over `FamEmpty ∧ AdequateEvery` and
  `EmbedsNil`.  `Tier2Pinned`, `AcceptsTier2`: kept as definitions, superseded in done by
  `SpanRulesAt` (recorded) and `Tier2Programs` (with answers).
* Check 2's derivations (`d_thenProgNU`, `d_prog₃TNU`, `d_thenRaiseProgNU`, `d_unwindProgNU`):
  **removed** with D3's kernel half.  Their finalisers let a raise escape, which option A excludes
  (SPEC §24); the programs stay (`Instance/CheckPrograms.lean`).
* `Targets/Checks/RunEnd.lean` (untracked, not imported): **deleted**, superseded: each of its 17
  theorems has a same-named successor in `Targets/I/RunEnd.lean`, restated against the field `Upd`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets.Inst (OurTyping ourInst AdmEff tier1Open J₁)
open Targets (ORow orowAlg)

/-! ## Done and tier 1 (OPEN) -/

/-- **Done**, at a named `J₂` and `W`: the statement elaborates.  OPEN. -/
example (J₂ : OurTyping orowRF) (W : SemWorld) : Prop :=
  I.Combined (ℍ := ℍ) orowRF J₂ W admClosedOp .any

/-- **Tier 1**, at `J₁` (decision D5): OPEN, reduced by `status_tier1_J₁_of`. -/
example : Prop := I.Tier1 (ℍ := ℍ) J₁

/-- The restricted tier-1 reduction: OPEN. -/
example : Prop := I.Tier1Core (ℍ := ℍ)

/-- PROVED AT σ=[]: the tier-1 world conjuncts and the device at `coreW`. -/
theorem status_tier1Core_world :
    I.Bounds (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ I.Interface (coreW (ℍ := ℍ)) ∧
      Device (ℍ := ℍ) (coreW (ℍ := ℍ)) tier1Open.read admClosedOp .abortive ∧ WBCore (ℍ := ℍ) :=
  I.tier1Core_world

/-- PROVED AT σ=[], given S5 at today's kernel and the step-for-step simulation: the restricted
tier-1 reduction. -/
theorem status_tier1Core_of
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise)
    (hS : BumpSim (ℍ := ℍ)) : I.Tier1Core (ℍ := ℍ) :=
  I.tier1Core_of hC hS

/-- PROVED AT σ=[]: A's properties at today's kernel but S5 (and S6, which the restricted reduction
does not hold), at every admissible effect context. -/
theorem status_sPropsNoCancel_tier1Open {Ξ : EffCtx} (hΞ : AdmEff Ξ) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).LetLaw ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RowAlgebra ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).DataDiv ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).EffSafe ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).HandlerSem :=
  I.sPropsNoCancel_tier1Open hΞ

/-- PROVED AT σ=[]: B's guarantees at today's kernel but B5 — B0, B1, B2, B3 and B4, B4′, B6, B7
and the bounds. -/
theorem status_tier1Core_B :
    B.ExtendsB tier1Open.read ∧ FL (B.coreB (ℍ := ℍ)) tier1Open.read ∧
      Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧ Sound (ℍ := ℍ) tier1Open.read ∧
      B.SoundContracts (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧
      LifetimeSound (B.coreB (ℍ := ℍ)) tier1Open.read.out ∧ B.WBound (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_B

/-- PROVED (given `BumpSim`): B5 at today's kernel and BoLo. -/
theorem status_releasedOnceReuse_tier1Open_of_bumpSim (hS : BumpSim (ℍ := ℍ)) :
    B.ReleasedOnceReuse (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_releasedOnceReuse_of_bumpSim hS

/-- PROVED AT σ=[] (given the step-for-step simulation): B's guarantees at today's kernel, B5
included. -/
theorem status_tier1Core_guarantees_of_bumpSim (hS : BumpSim (ℍ := ℍ)) :
    B.Guarantees (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_guarantees_of_bumpSim hS

/-! ## System A -/

section A
open Targets.A Targets.A.EffectSystem
variable {S : A.EffectSystem}

/-- The first pass of A elaborates at every instance. -/
example (S : A.EffectSystem) : Prop := S.Props

/-- A₂ and A₃, stated, out of the first pass. -/
example (S : A.EffectSystem) (L : S.Lowering) : Prop :=
  S.HandlerLaws ∧ S.EffDepLaws ∧ S.Abstraction ∧ S.LoweringCorrect L ∧ S.ZeroCost L

/-- The unary laws beside done (tail-resumptive, algebraicity, η with a holding frame), and η's
typing-restricted alternative: STATED, not proved.  Not a conjunct of S4 or of done; whether they
join done is a menu choice (P11/I5 menu axes H, F, K). -/
example (S : A.EffectSystem) : Prop := S.UnaryLaws ∧ S.EtaLin

/-- PROVED: `EtaHold` gives `EtaLin`. -/
theorem status_etaLin_of_etaHold (h : S.EtaHold) : S.EtaLin := etaLin_of_etaHold S h

/-- PROVED: each unary law fails at an instance whose handler or bind ignores its clauses. -/
theorem status_unaryLaws_not_vacuous (hd : Bool → Bool) (bd : Bool → Bool → Bool) :
    ¬ (toy id bd).TailLaw ∧ ¬ (toy hd (fun M _ => !M)).AlgLaw ∧ ¬ (toy (fun _ => true) bd).EtaHold ∧
      ¬ (toy (fun _ => true) bd).EtaLin :=
  ⟨not_tailLaw_toy, not_algLaw_toy, not_etaHold_toy, not_etaLin_toy⟩

/-- PROVED: an instance that types nothing fails the (E) properties. -/
theorem status_not_eProps_of_emptyTyping (h : ∀ Γ e C, ¬ S.der Γ e C) : ¬ S.EProps :=
  not_eProps_of_emptyTyping h

/-- PROVED: an instance with no error label (no effects) fails the (E) properties. -/
theorem status_not_eProps_of_noLabels (h : ∀ l, S.sig l ≠ S.sigExn) : ¬ S.EProps :=
  not_eProps_of_noLabels h

/-- PROVED: no instance meets S0, S1, S3, the let law and E1 without effect polymorphism. -/
theorem status_not_noColouring_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra)
    (he : S.EffSafe) (hl : S.LetLaw) (hmono : MonoCallback S) : ¬ S.NoColouring :=
  not_noColouring_of_monoCallback hm hr he hl hmono

/-- PROVED: the same at E2a, E6 and E10 (E10 at labels well formed at the empty context). -/
theorem status_not_poly_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (hl : S.LetLaw) (hmono : MonoCallback S) (hext : LiftExt S) (hwf : ∀ l, S.EA.WFLab [] l) :
    ¬ S.HigherOrderPoly ∧ ¬ S.Tunnel ∧ ¬ S.Reconciler :=
  ⟨not_higherOrderPoly_of_monoCallback hm hr he hl hmono, not_tunnel_of_monoCallback hm hr he hl hmono,
    not_reconciler_of_monoCallback hm hr he hl hmono hext hwf⟩

/-- PROVED: totality fails E3; divergence at the pure row is not at a data answer. -/
theorem status_loops (hr : S.RowAlgebra) (hs : S.Safety) (hd : S.DataDiv) :
    (Total S → ¬ S.Loops) ∧
      (S.Loops → ∀ L, S.der [] (S.runL S.spinL) (S.F S.EA.unit (S.Sum S.UnitT L)) → ¬ S.DataTy L) :=
  ⟨not_loops_of_total, fun hl => divInTypes_of_loops hr hs hd hl⟩

/-- PROVED: the runners keep their protocol. -/
theorem status_runners_respect {lt llog lk : S.EA.Lab} (ht : S.sig lt = S.sigTick)
    (hl : S.sig llog = S.sigLog) (hk : S.sig lk = S.sigKube) (hne : llog ≠ lk) :
    (S.Rtick lt).Respects ∧ (S.Rtl lt llog).Respects ∧ (S.Rrec lk llog).Respects :=
  ⟨rtick_respects ht, rtl_respects ht hl, rrec_respects hk hl hne⟩

/-- PROVED: an operation is untypable at the pure row on its own; Def. 5.1 (1) from `RowSig`. -/
theorem status_effSafe_teeth (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe) :
    (∀ l i v A', ¬ S.der [] (S.perform l i v) (S.F S.EA.unit A')) ∧
      ∀ L, ¬ S.EA.Sub (S.EA.lift L) S.EA.unit :=
  ⟨fun l i v A' => not_der_unhandled hm hr he l i v A', c1_of_rowSig hr.2.2.1⟩

end A

/-! ## System B -/

/-- PROVED AT σ=[]: B0. -/
theorem status_extendsB_tier1 : B.ExtendsB tier1 := extendsB_tier1

/-- PROVED AT σ=[]: B1 (`fundamentalC`). -/
theorem status_fl_core_tier1 : FL (B.coreB (ℍ := ℍ)) tier1 := fl_core_tier1

/-- PROVED AT A RESTRICTION (`P = Platform.none`): B2's return conjunct. -/
theorem status_adequateRet_core_none : AdequateRetAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) Platform.none :=
  adequateRetAt_core_none

/-- PROVED AT σ=[]: B2 at BoLo, at every platform that keeps its protocol, the drive conjunct at
positive loop bodies (D2).  The hypothesis is needed: at every platform with an operation, a loop
type whose body is not positive has `()` in Core's relation, and its drive is stuck. -/
theorem status_adequate_core :
    Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧ AdequateAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) Platform.none ∧
    ∀ P : Platform, P.Respects → ∀ o ∈ P.ops,
      RowLe [o, shadowOp o] P.ops ∧ ¬ (CTy.loopEffBody [o, shadowOp o] .unit .unit).NuOk ∧
      cC (ℍ := ℍ) (CTy.effOf [o, shadowOp o] (.thunk (CTy.loopEff [o, shadowOp o] .unit .unit))) []
        BoCa.Lifetime.LSub.empty (.val Val.unit) PMap.empty ∧
      ¬ SafeDrive (ℍ := ℍ) P .unit (.val Val.unit) :=
  ⟨adequate_core, adequateAt_core_none, fun _ hP _ ho => adequateDrive_needs_nuOk hP ho⟩

/-- PROVED AT σ=[]: B3 and B4 at today's unr-free kernel, and B4′. -/
theorem status_sound_tier1NU :
    Sound (ℍ := ℍ) tier1NU ∧ (∀ P : Platform, P.Respects →
      SoundRetAt (ℍ := ℍ) tier1NU P ∧ SoundDriveAt (ℍ := ℍ) tier1NU P) ∧
    B.SoundContracts (ℍ := ℍ) tier1NU (B.coreB (ℍ := ℍ)) :=
  ⟨sound_tier1NU, fun P hP => ⟨soundRetAt_tier1NU P hP, soundDriveAt_tier1NU P hP⟩,
    soundContracts_tier1NU⟩

/-- PROVED AT A RESTRICTION (`P = Platform.none`): B3 and B4's return conjunct. -/
theorem status_soundRet_tier1_none : SoundRetAt (ℍ := ℍ) tier1 Platform.none := soundRetAt_tier1_none

/-- PROVED (generic): B3, B4 from B1, B2. -/
theorem status_soundnessOfFL : SoundnessOfFL (ℍ := ℍ) := soundnessOfFL

/-- PROVED (generic): B4′ from B1, B2, externs at W's contract (finding #7). -/
theorem status_soundContractsOfFL {M : B.BWorld} {J : TypingJ} (hFL : FL M J)
    (hA : Adequate (ℍ := ℍ) M) : B.SoundContracts (ℍ := ℍ) J M := soundContractsOfFL hFL hA

/-- PROVED (generic): the alternative route, with Core's contracts through `Conservative`. -/
theorem status_soundnessContractsOfFL : SoundnessContractsOfFL (ℍ := ℍ) := soundnessContractsOfFL

/-- PROVED: B5 is not a tautology (finding #2). -/
theorem status_not_releasedOnceReuse_staleFree (J : TypingJ) (M : B.BWorld)
    (h : J.closed B.staleFree (.ret .unit)) : ¬ B.ReleasedOnceReuse (ℍ := ℍ) J M :=
  B.not_releasedOnceReuse_staleFree J M h

/-- PROVED, and a **tautology about runs**: `ReleasedOnceAll` holds at every typing system; it is
a lemma, not a guarantee (finding #2). -/
theorem status_releasedOnceAll : ∀ J : TypingJ, ReleasedOnceAll (ℍ := ℍ) J := releasedOnceAll

/-- PROVED: D9's machine lemma (its premises unused). -/
theorem status_releasedOnceOfSound : ReleasedOnceOfSound (ℍ := ℍ) := releasedOnceOfSound

/-- PROVED AT σ=[]: B6. -/
theorem status_exclusiveB_core : B.ExclusiveB (B.coreB (ℍ := ℍ)) := exclusiveB_core

/-- PROVED AT σ=[]: B7. -/
theorem status_lifetimeSound_core : LifetimeSound (B.coreB (ℍ := ℍ)) OutJ.core := lifetimeSound_core

/-- PROVED AT σ=[]: the bounds. -/
theorem status_wBound_core : B.WBound (B.coreB (ℍ := ℍ)) := wBound_core

/-- PROVED: P14.a. -/
theorem status_wbCore : WBCore (ℍ := ℍ) := wbCore

/-- PROVED AT σ=[]: P14.b, P14.b′ at `coreB`. -/
theorem status_conservative_core :
    ConservativeWB (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧ Conservative (ℍ := ℍ) (B.coreB (ℍ := ℍ)) :=
  ⟨conservativeWB_core, conservative_core⟩

/-- PROVED (generic): where `Upd` is Core's at every index, the run-end laws hold. -/
theorem status_updLaws_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) :
    UpdRefl M ∧ UpdOwn M ∧ UpdSeq M ∧ UpdReclaim M ∧ UpdFrame M ∧ UpdOutlives M ∧ UpdLendBack M :=
  ⟨updRefl_of_core hC, updOwn_of_core hC, updSeq_of_core hC, updReclaim_of_core hC,
    updFrame_of_core hC, updOutlives_of_core hC, updLendBack_of_core hC⟩

/-- PROVED AT σ=[]: the run-end laws at `coreB`. -/
theorem status_updLaws_core :
    UpdRefl (B.coreB (ℍ := ℍ)) ∧ UpdOwn (B.coreB (ℍ := ℍ)) ∧ UpdSeq (B.coreB (ℍ := ℍ)) ∧
      UpdReclaim (B.coreB (ℍ := ℍ)) ∧ UpdFrame (B.coreB (ℍ := ℍ)) ∧
      UpdOutlives (B.coreB (ℍ := ℍ)) ∧ UpdLendBack (B.coreB (ℍ := ℍ)) :=
  ⟨updRefl_core, updOwn_core, updSeq_core, updReclaim_core, updFrame_core, updOutlives_core,
    updLendBack_core⟩

/-- PROVED (generic): B5 from B4′, given the step-for-step simulation. -/
theorem status_releasedOnceReuse_of_bumpSim (hS : BumpSim (ℍ := ℍ)) {J : TypingJ} {M : B.BWorld}
    (hC : B.SoundContracts (ℍ := ℍ) J M) : B.ReleasedOnceReuse (ℍ := ℍ) J M :=
  releasedOnceReuse_of_bumpSim hS hC

/-- OPEN (stated): the step-for-step simulation (OQ-43 (b), or (c) through a binary FP). -/
example : Prop := BumpSim (ℍ := ℍ)

/-- PROVED: `BumpSim`'s conclusion at an `alloc` step whose given run reuses a location, for every
finite `X`: the configuration on which `BlocksAffine`'s earlier, unbound-length reading refuted
`BumpSim`. -/
theorem status_bumpSim_at_reuse (X : Finset Loc) :
    RelAt id B.reuseConf B.reuseConf ∧ BlocksAffine id B.reuseConf.μ B.reuseConf.e ∧
    PStep (ℍ := ℍ) Platform.none B.reuseConf B.reuseConf' ∧
    ∃ cB' g', PStep (ℍ := ℍ) Platform.none B.reuseConf cB' ∧
      (∀ ℓ, B.reuseConf.μ ℓ = none → (cB'.μ ℓ).isSome →
        ¬ Named B.reuseConf.μ B.reuseConf.e ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named B.reuseConf.μ B.reuseConf.e ℓ → g' ℓ = id ℓ) ∧ RelAt g' B.reuseConf' cB' ∧
      BlocksAffine g' cB'.μ cB'.e :=
  B.bumpSim_at_reuse X

/-! ## The interaction -/

section I
variable {RF : RowForm} {J : OurTyping RF} {M : SemWorld} {Adm : OpAdm} {c : RowClass}

/-- PROVED (generic): the combined theorem's conjuncts that read no world. -/
theorem status_combined_prog (h : I.Combined (ℍ := ℍ) RF J M Adm c) :
    (∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) RF Ξ J).Props) ∧ Sound (ℍ := ℍ) J.read ∧
      B.ReleasedOnceReuse₀ (ℍ := ℍ) J.read ∧ B.ExtendsB J.read ∧ I.Pins J Adm c ∧
      I.Accepts (ℍ := ℍ) J.read c ∧ Rejects J.read :=
  I.combined_prog h

/-- PROVED (generic): I1 and I2 at the program level, at `c = .any`. -/
theorem status_progs_of_combined (h : I.Combined (ℍ := ℍ) RF J M Adm .any) :
    I1Prog (ℍ := ℍ) J.read ∧ I2Prog (ℍ := ℍ) J.read :=
  ⟨I.i1Prog_of_combined h, I.i2Prog_of_combined h⟩

/-- PROVED (generic): Core's form of P2, from the combined theorem. -/
theorem status_effSafe_core_of_combined (h : I.Combined (ℍ := ℍ) RF J M Adm c) :
    EffSafe (ℍ := ℍ) J.read := I.effSafe_core_of_combined h

/-- PROVED (generic): the SPEC's externs, from the combined theorem with the device's `EmbedsNil`. -/
theorem status_soundnessContractsAR_of_combined (h : I.Combined (ℍ := ℍ) RF J M Adm c)
    (hE : EmbedsNil (ℍ := ℍ) M) : SoundnessContractsAR (ℍ := ℍ) J.read :=
  I.soundnessContractsAR_of_combined h hE

/-- PROVED (generic): Core's extern contract gives W's at row-abortive types, with `EmbedsNil`. -/
theorem status_contractsW_of_meets (hE : EmbedsNil (ℍ := ℍ) M) {Γ : Ctx VTy} {γ : List Val}
    (hAR : ∀ s ∈ Γ, s.ty.AbortRows) (hγ : ExternsMeet (ℍ := ℍ) Γ γ) : B.ContractsW M.toBWorld Γ γ :=
  contractsW_of_meets hE hAR hγ

/-- PROVED (generic): a reachable leak breaks the combined theorem. -/
theorem status_not_combined_of_leak {α : Life} (hL : RunEnd.LeakAt M α) :
    ¬ I.Combined (ℍ := ℍ) RF J M Adm c := I.not_combined_of_leak hL

end I

/-- PROVED AT σ=[]: Core's P2 at tier 1, from FL, `FamEmpty` and `AdequateEvery`. -/
theorem status_effSafe_tier1 : EffSafe (ℍ := ℍ) tier1 := effSafe_tier1

/-- PROVED (generic): effect safety from FL, `FamEmpty` and `AdequateEvery`. -/
theorem status_effSafeOfFL : EffSafeOfFL (ℍ := ℍ) := effSafeOfFL

/-- PROVED AT σ=[]: Core's P2 for driven programs, at every typing system with FL at BoLo, so at
today's unr-free kernel (D2, D4).  The positivity hypothesis is needed. -/
theorem status_effSafeDrive :
    EffSafeDrive (ℍ := ℍ) tier1NU ∧ (∀ J : TypingJ, FL (B.coreB (ℍ := ℍ)) J → EffSafeDrive (ℍ := ℍ) J) ∧
      ¬ (CTy.loopEffBody rowShadow .unit .unit).NuOk :=
  ⟨effSafeDrive_tier1NU, fun _ h => effSafeDrive_of_FL h, effSafeDrive_needs_nuOk.2.1⟩

/-- PROVED (generic): row-abortive externs at Core's contract, from FL, `EmbedsNil` and adequacy. -/
theorem status_soundnessContractsOfFLWB : SoundnessContractsOfFLWB (ℍ := ℍ) :=
  soundnessContractsOfFLWB

/-- PROVED AT σ=[]: the device's laws at `coreW`. -/
theorem status_wlaws_core : WLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) := wlaws_core

/-- PROVED AT σ=[] (I1, I3, I5, P11), AT A RESTRICTION (I2, at abortive rows). -/
theorem status_device_core :
    I1 (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ I2 (ℍ := ℍ) (coreW (ℍ := ℍ)) OutJ.core admClosedOp .abortive ∧
      I3 (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ I5 (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ P11 (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  ⟨i1_core, i2_core_abortive, i3_core, i5_core, p11_core⟩

/-- PROVED (generic): I5.β at every world. -/
theorem status_I5beta : ∀ M : SemWorld, I5beta (ℍ := ℍ) M := i5beta

/-- PROVED AT A RESTRICTION (tier 1, abortive rows): I4.a. -/
theorem status_I4a_tier1_abortive : I4a tier1 admClosedOp .abortive := i4a_tier1

/-- PROVED: R-CLOSEDOP bounds every admissibility. -/
theorem status_admExtends_closedOp : AdmExtends admClosedOp := admExtends_closedOp

/-- PROVED AT σ=[]: today's unr-free rules and outlives judgements. -/
theorem status_extendsNU_tier1 : ExtendsNU tier1 ∧ OutExtends OutJ.core :=
  ⟨extendsNU_tier1, outExtends_core⟩

/-- PROVED (generic, at every world meeting `SliceShape`): a `wpG` run is a `wpGW` run at the nil
index that ends on the nil slice. -/
theorem status_wpGW_of_wpG_nil {M : SemWorld} (hS : SliceShape M) (ls : List SRec) (e : Expr)
    (Q : Idx M.Stk → Expr → WProp) (ρ : WRes) :
    wpG (ℍ := ℍ) ls e (fun ls' t => Q (ls', M.nil) t) ρ → wpGW (ℍ := ℍ) M (ls, M.nil) e Q ρ :=
  wpGW_of_wpG_nil hS ls e Q ρ

/-- PROVED (generic): a run-end relation that relates everything fails the pin. -/
theorem status_not_sliceShape_of_updTop {M : SemWorld} (h : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π) :
    ¬ SliceShape M := RunEnd.not_sliceShape_of_updTop h

/-- PROVED at the witness `leakW`: it meets the pin, `EffInterp`, `DataVals`, admits a leak, and
fails `Adequate` and `UpdReclaim`. -/
theorem status_leakW (α : Life) :
    SliceShape (RunEnd.leakW (ℍ := ℍ)) ∧ EffInterp (ℍ := ℍ) (RunEnd.leakW (ℍ := ℍ)) ∧
      DataVals (RunEnd.leakW (ℍ := ℍ)).toBWorld ∧ RunEnd.LeakAt (RunEnd.leakW (ℍ := ℍ)) α ∧
      ¬ Adequate (ℍ := ℍ) (RunEnd.leakW (ℍ := ℍ)).toBWorld ∧
      ¬ UpdReclaim (RunEnd.leakW (ℍ := ℍ)).toBWorld :=
  ⟨RunEnd.sliceShape_leakW, RunEnd.effInterp_leakW, RunEnd.dataVals_leakW,
    RunEnd.leakAt_leakW α, RunEnd.not_adequate_leakW α, RunEnd.not_updReclaim_leakW⟩

/-- PROVED at the witness `carryW`: the run-end laws admit an end that holds a `Mut` lend as a
cell; the printed forms of 6.50 and 6.27 at every index exclude it. -/
theorem status_carryW :
    SliceShape (RunEnd.carryW (ℍ := ℍ)) ∧ UpdRefl (RunEnd.carryW (ℍ := ℍ)).toBWorld ∧
      UpdOwn (RunEnd.carryW (ℍ := ℍ)).toBWorld ∧ UpdSeq (RunEnd.carryW (ℍ := ℍ)).toBWorld ∧
      UpdReclaim (RunEnd.carryW (ℍ := ℍ)).toBWorld ∧
      ¬ UpdOutlives (RunEnd.carryW (ℍ := ℍ)).toBWorld ∧ ¬ UpdLendBack (RunEnd.carryW (ℍ := ℍ)).toBWorld :=
  ⟨RunEnd.sliceShape_carryW, RunEnd.updRefl_carryW, RunEnd.updOwn_carryW, RunEnd.updSeq_carryW,
    RunEnd.updReclaim_carryW, RunEnd.not_updOutlives_carryW, RunEnd.not_updLendBack_carryW⟩

/-! ## The Instance -/

/-- PROVED: the reading of today's kernel over the open types is `tier1NU`. -/
theorem status_tier1Open_read : tier1Open.read = tier1NU := Inst.tier1Open_read

/-- PROVED: the syntactic laws of A's machine at our instance. -/
theorem status_ourInst_syntactic (Ξ : EffCtx) (J : OurTyping orowRF) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).ConfLaws ∧ (ourInst (ℍ := ℍ) orowRF Ξ J).KontLaws ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).NoIO ∧ (ourInst (ℍ := ℍ) orowRF Ξ J).DataInj ∧
      A.EffectSystem.LiftExt (ourInst (ℍ := ℍ) orowRF Ξ J) :=
  ⟨Inst.confLaws_ourInst, Inst.kontLaws_orow J, Inst.noIO_ourInst, Inst.dataInj_ourInst,
    Inst.liftExt_orow J⟩

/-- PROVED AT A RESTRICTION (`RF = orowRF`): our rows meet Def. 3.5 and Def. 5.1, and the link. -/
theorem status_rows : RowAlgSafe orowRF ∧ RowLink orowRF := ⟨rowAlgSafe_orowRF, rowLink_orowRF⟩

/-- PROVED AT σ=[]: no typed term intercepts a cancel. -/
theorem status_noInterception_tier1 : NoInterception tier1 := noInterception_tier1

/-- PROVED AT σ=[], given `LiveOK`: S0 and S4 at our instance, at every typing system. -/
theorem status_machShape_handlerSem (Ξ : EffCtx) (J : OurTyping orowRF)
    (hL : Inst.LiveOK (ℍ := ℍ) orowRF Ξ J) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ J).HandlerSem :=
  ⟨Inst.machShape_orow hL, Inst.handlerSem_orow hL⟩

/-- PROVED AT σ=[]: `LiveOK`, so S0 and S4, at today's kernel at every effect context (D1). -/
theorem status_machShape_handlerSem_tier1Open (Ξ : EffCtx) :
    Inst.LiveOK (ℍ := ℍ) orowRF Ξ tier1Open ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).MachShape ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).HandlerSem :=
  ⟨Inst.liveOK_tier1Open, Inst.machShape_orow Inst.liveOK_tier1Open,
    Inst.handlerSem_orow Inst.liveOK_tier1Open⟩

/-- PROVED: S5's no-interception condition is needed (D4).  A typing system that types one program
with no `ccatch`, no `cfin` and no handler named `0` reaches a cancel whose region's finaliser
performs the operation the region's dying handler catches; that finaliser meets `FinRow` at no set
of endings, and the run from the cancel follows no cancel trace at any. -/
theorem status_noIntercept_needs_finRow {Ξ : EffCtx} (h2 : Ξ 2 = [(.aff, .unit, .unit)]) :
    NoInterception Inst.J₄.read ∧
      (∀ FR, ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).FinRow FR Inst.finP) ∧
      ∀ FR, ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).CancelTrace (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).R₀ FR
        ((ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).Region (Inst.lab2 Ξ h2) Inst.p5K) .hole
        ((Adequacy.emptyMem, lookEnd 8 Inst.finAloneProg), ()) [Inst.finP] none (Inst.p5q (ℍ := ℍ) Ξ) :=
  let h := Inst.noIntercept_needs_finRow (ℍ := ℍ) Ξ h2
  ⟨h.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- PROVED, given `NoInterception` and `FinAloneAt` at today's endings or at option A's: Core's
`FinaliserOrder`. -/
theorem status_finaliserOrder_of {J : TypingJ} (hN : NoInterception J) :
    (FinAloneAt (ℍ := ℍ) (· ≠ 0) J → FinaliserOrder (ℍ := ℍ) J) ∧
      (FinAloneAt (ℍ := ℍ) (fun _ => False) J → FinaliserOrder (ℍ := ℍ) J) :=
  ⟨finaliserOrder_at hN, finaliserOrder_A hN⟩

/-- PROVED: what a typed program does at run time, at today's kernel.  `LiveOK` holds at every
effect context, and needs the tie; `FinaliserOrder` at today's unr-free kernel follows from
`FinRowsAt` alone, at today's endings and at option A's; route 8.2's obligations give `FinRowsAt`. -/
theorem status_runTyping :
    (∀ Ξ, Inst.LiveOK (ℍ := ℍ) orowRF Ξ tier1Open) ∧
      (AdmEff Inst.ΞA ∧ ¬ RowAt Inst.ΞA Inst.Slv ∧ ¬ Inst.GoesOn (ℍ := ℍ) orowRF Inst.ΞA Inst.lvStuck) ∧
      (FinRowsAt (ℍ := ℍ) (· ≠ 0) tier1NU → FinaliserOrder (ℍ := ℍ) tier1NU) ∧
      (FinRowsAt (ℍ := ℍ) (fun _ => False) tier1NU → FinaliserOrder (ℍ := ℍ) tier1NU) ∧
      ∀ J : TypingJ, NoInterception J → RowRoute (ℍ := ℍ) J → FL (B.coreB (ℍ := ℍ)) J →
        FinaliserOrder (ℍ := ℍ) J :=
  ⟨fun _ => Inst.liveOK_tier1Open,
    ⟨Inst.liveOK_needs_tie.1, Inst.liveOK_needs_tie.2.2.1, Inst.liveOK_needs_tie.2.2.2.2.2.1⟩,
    finaliserOrder_tier1NU_of_finRows, finaliserOrder_tier1NU_of_finRowsA,
    fun _ hN hr hFL => finaliserOrder_of_route hN hr hFL⟩

/-- PROVED: S6's teeth.  At the open-row form, a typing system that types R2 or R4 at `F 0 bool`
fails S6, at every label; `JR` types all four witnesses and fails S6 at `ΞA`; today's kernel types
none of them, by the handler's form. -/
theorem status_contUse_teeth {Ξ : EffCtx} {J : OurTyping orowRF} (l : (orowAlg Ξ).Lab) :
    ((ourInst (ℍ := ℍ) orowRF Ξ J).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ J).withCl l (ourInst (ℍ := ℍ) orowRF Ξ J).twiceCl)
        ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (ourInst (ℍ := ℍ) orowRF Ξ J).bool) →
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).ContUse) ∧
    ((ourInst (ℍ := ℍ) orowRF Ξ J).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ J).withCl l (ourInst (ℍ := ℍ) orowRF Ξ J).cancelResumeCl)
        ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (ourInst (ℍ := ℍ) orowRF Ξ J).bool) →
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).ContUse) ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA Inst.JR).ContUse ∧
    ∀ C, ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).dropCl) C :=
  ⟨Inst.not_contUse_of_der_R2_orow l, Inst.not_contUse_of_der_R4_orow l,
    Inst.teeth_JR_ΞA.2.2.2.2.2, fun C => (Inst.refuses_R_tier1Open l C).1⟩

/-- PROVED: today's clause typing refuses R1–R4's clauses (RESTRUCTURE §6.1's reason): R1's, R2's
and R4's at every resuming `lin` or `aff` operation, R3's at every `lin` one.  At the clause type of
a linear `1 ↠ 1` a clause that resumes `κ` once is typed; `cancelCl` is typed at `aff` and refused
at `lin`. -/
theorem status_clauseRefusals {Δ : BoCa.Lifetime.LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy}
    {q : Qual} {A B : VTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    (¬ CDerivesNU Δ Γ Inst.dropV.1 (.val (clauseTy S R (q, A, B))) ∧
      ¬ CDerivesNU Δ Γ Inst.twiceV.1 (.val (clauseTy S R (q, A, B))) ∧
      ¬ CDerivesNU Δ Γ Inst.cancelV.1 (.val (clauseTy S R (.lin, A, B))) ∧
      ¬ CDerivesNU Δ Γ Inst.cancelResumeV.1 (.val (clauseTy S R (q, A, B)))) ∧
    CDerivesNU Δ [] Inst.tailClE (.val (clauseTy Inst.S₁₁ .unit (.lin, .unit, .unit))) ∧
    CDerivesNU Δ [] Inst.cancelCl (.val (clauseTy [] .unit (.aff, .unit, .unit))) ∧
    ¬ CDerivesNU Δ [] Inst.cancelCl (.val (clauseTy [] .unit (.lin, .unit, .unit))) :=
  ⟨Inst.refuses_R_clauses hq hres, Inst.clauseRefusals_pinned.1.1, Inst.clauseRefusals_pinned.2⟩

/-- PROVED: the let law at today's kernel. -/
theorem status_letLaw_tier1Open (Ξ : EffCtx) : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).LetLaw :=
  Inst.letLaw_ourInst_tier1Open

/-- PROVED: S1 at today's kernel, at every effect context with no resuming `unr` operation (D6);
`SubClosed`'s well-formedness premise is needed. -/
theorem status_rowAlgebra_tier1Open (Ξ : EffCtx) :
    (Ξ.NU → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RowAlgebra) ∧
      (AdmEff Ξ → (orowAlg Ξ).Sub (orowAlg Ξ).unit ⟨[Inst.unrOp], none⟩ ∧
        (¬ ∃ Δ, (orowAlg Ξ).WF Δ ⟨[Inst.unrOp], none⟩) ∧
        ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] .unit
          ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F ⟨[Inst.unrOp], none⟩ .unit)) :=
  ⟨fun h => Inst.rowAlgebra_ourInst_tier1Open h, fun h =>
    let p := Inst.subClosed_needs_wf (ℍ := ℍ) h
    ⟨p.1, p.2.1, p.2.2.2⟩⟩

/-- PROVED: today's kernel types no A-level handler, so E4, E5, E6, E7 and E8 fail at `tier1Open`
at every effect context. -/
theorem status_handlers_tier1Open (Ξ : EffCtx) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).DeepHandler ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).NestedHandlers ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Tunnel ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).CancelPolicy ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).UnwindPolicy :=
  ⟨Inst.not_deepHandler_tier1Open, Inst.not_nestedHandlers_tier1Open, Inst.not_tunnel_tier1Open,
    Inst.not_cancelPolicy_tier1Open, Inst.not_unwindPolicy_tier1Open⟩

/-- PROVED: TIER1-PLAN §2's route does not reach tier 1.  A typing system whose closed derivations
elaborate into today's unr-free kernel fails tier 1 (E8's handler); and today's kernel types no
let-bound λ read at two different `!U` types. -/
theorem status_elab_route {Δ : BoCa.Lifetime.LifeCtx} {Γ : Ctx VTy} {b : Expr} {c₁ c₂ : CTy}
    (hr₁ : c₁.isRet = false) (hn₁ : ∀ C, c₁ ≠ .nu C) (hr₂ : c₂.isRet = false)
    (hn₂ : ∀ C, c₂ ≠ .nu C) (hne : c₁ ≠ c₂) :
    (∀ J : OurTyping orowRF, Inst.ElabClosed J → ¬ I.Tier1 (ℍ := ℍ) J) ∧
      ¬ CDerivesNU Δ Γ (.app (.lam (withPair (.var 2) (.var 2))) (.lam b))
        (.comp (.amp (.ret (.bang (.thunk c₁))) (.ret (.bang (.thunk c₂))))) :=
  ⟨fun _ hE => I.not_tier1_of_elabClosed hE, Inst.not_der_letTwo hr₁ hn₁ hr₂ hn₂ hne⟩

/-- PROVED (generic; AT σ=[]): Law 1 at the relation, and FL at the open judgements gives FL at the
reading; at today's kernel it is `fundamentalC`. -/
theorem status_law1_relation :
    (∀ (M : B.BWorld) (J : OurTyping orowRF), I.FLOpen M J → FL M J.read) ∧
      I.FLOpen (B.coreB (ℍ := ℍ)) tier1Open :=
  ⟨fun _ _ h => I.fl_of_flOpen h, I.flOpen_core_tier1Open⟩

/-- PROVED AT σ=[] (abortive rows): `Pins` at today's kernel over the open types, with `I4a` at the
unr-free rules. -/
theorem status_pins_tier1Open :
    I.Pins tier1Open admClosedOp .abortive ∧ I4a tier1NU admClosedOp .abortive :=
  ⟨I.pins_tier1Open, i4a_tier1NU⟩

/-- PROVED AT σ=[]: S2 and S3 at today's kernel, at every effect context (D1); the tie is needed.
PROVED at every row form, effect context and typing system: `DataDiv`. -/
theorem status_safety_tier1Open (Ξ : EffCtx) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).EffSafe ∧
      (¬ RowAt Ξ [Inst.op₀] ∧
        ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] Inst.perform₀
          ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F Inst.ε₀ .unit)) ∧
      ∀ (RF : RowForm) (J : OurTyping RF), (ourInst (ℍ := ℍ) RF Ξ J).DataDiv :=
  ⟨Inst.safety_ourInst_tier1Open, Inst.effSafe_ourInst_tier1Open,
    ⟨(Inst.safety_needs_tie Ξ).2.1, (Inst.safety_needs_tie Ξ).2.2.2.2.2⟩,
    fun _ _ => Inst.dataDiv_ourInst⟩

/-! ## Decision D5: `J₁` and the S6 probe -/

/-- PROVED AT σ=[]: `J₁`'s reading is Core's kernel, its FL is `fundamentalC`, its closed programs
are Core's, and its open judgements over contexts with no polymorphic slot meet `FLOpen`'s relation. -/
theorem status_j1 :
    J₁.read = tier1 ∧ FL (B.coreB (ℍ := ℍ)) J₁.read ∧ Inst.CoreClosed J₁ ∧
      ∀ {Θ Δ Γ e j}, J₁.der Θ Δ Γ e j → Inst.octxRFree Γ → ∀ η, Θ.Models η → ∀ δ γ i ρ,
        Δ.Models δ → I.ogDenW (B.coreB (ℍ := ℍ)) i η δ Γ γ ρ →
          I.ojdgW (B.coreB (ℍ := ℍ)) j i η δ (substAll γ e) ρ :=
  ⟨Inst.j1_read, I.fl_core_J₁, Inst.coreClosed_J₁,
    fun hd hΓ η hη δ γ i ρ hδ hg => I.flOpen_J₁_mono hd hΓ η hη δ γ i ρ hδ hg⟩

/-- PROVED AT σ=[]: B's guarantees at `J₁` but B5, and with B5 given the step-for-step simulation. -/
theorem status_guarantees_J₁ :
    (B.ExtendsB J₁.read ∧ FL (B.coreB (ℍ := ℍ)) J₁.read ∧ Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧
      Sound (ℍ := ℍ) J₁.read ∧ B.SoundContracts (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ)) ∧
      B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧ LifetimeSound (B.coreB (ℍ := ℍ)) J₁.read.out ∧
      B.WBound (B.coreB (ℍ := ℍ))) ∧
    (BumpSim (ℍ := ℍ) → B.Guarantees (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ))) :=
  ⟨I.guarantees_noB5_J₁, I.guarantees_J₁_of_bumpSim⟩

/-- PROVED AT σ=[] (abortive rows): `Pins` at `J₁`. -/
theorem status_pins_J₁ : I.Pins J₁ admClosedOp .abortive := I.pins_J₁

/-- PROVED AT σ=[]: A's (S) properties at `J₁` but S5 and S6, at every effect context. -/
theorem status_sPropsNoCancel_J₁ (Ξ : EffCtx) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).LetLaw ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).RowAlgebra ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).DataDiv ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).EffSafe ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem :=
  I.sPropsNoCancel_J₁

/-- PROVED: tier 1 at `J₁` follows from A's (E) properties, S5 and S6 at every admissible effect
context, the composite's programs and rejections, and the step-for-step simulation. -/
theorem status_tier1_J₁_of
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUse)
    (hAc : I.Accepts (ℍ := ℍ) J₁.read .abortive) (hRj : Rejects J₁.read) (hS : BumpSim (ℍ := ℍ)) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of hE hC hU hAc hRj hS

/-- PROVED: route 8.4's coupling fails at BoLo's world and relation.  A typing system with FL at
BoLo fails S6 at an admissible context, at a capture never used (R1), at a capture resumed twice
(R2) and at a linear capture cancelled (R3); BoLo's world at the empty heap is the empty resource. -/
theorem status_ghostCoupling :
    ¬ I.GhostCoupling (ℍ := ℍ) ∧ FL (B.coreB (ℍ := ℍ)) I.JRp.read ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA I.JRp).ContUse ∧
      (∀ ρ : WRes, ResU.Lower ρ Adequacy.emptyMem → ρ = PMap.empty) :=
  ⟨I.not_ghostCoupling, I.fl_core_JRp, I.ghost_probe_resume, fun _ h => I.lower_empty_eq h⟩

/-! ## Piece 5: the answering class -/

/-- **FAILS AS WRITTEN at `J₁`**: algebraicity, at the admissible effect context `ΞA`.  The
witness is typed by Core's kernel. -/
theorem status_unaryLaws :
    (AdmEff Inst.ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).AlgLaw) ∧
      CDerives BoCa.Lifetime.LifeCtx.empty [] Inst.algFireProg (.comp (.ret .unit)) ∧
      Inst.finE Inst.DL5.1 ≠ Inst.finE Inst.DR5.1 :=
  ⟨Inst.not_algLaw_ΞA, Inst.d_algFireProg, Inst.finE_DL_ne⟩

/-- **PROVED AT σ=[]**: the theory of global state at `J₁` — `stateCo` is a comodel and its
handler is correct, at every effect context, carrier and label; and not vacuously: at the
admissible `Ξst`, the handler whose `put` keeps the old state is no model and its co-operations no
comodel. -/
theorem status_theories :
    (∀ (Ξ : EffCtx) (T : Inst.OVTy) (l : (orowAlg Ξ).Lab),
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).IsComodel ((ourInst (ℍ := ℍ) orowRF Ξ J₁).stateTheory T) l
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).stateCo T ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).AnsCorrect ((ourInst (ℍ := ℍ) orowRF Ξ J₁).stateTheory T) l
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).stateCo T) ∧
    AdmEff Inst.Ξst ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).AnsCorrect
      ((ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).stateTheory Inst.stT) Inst.labSt
      (ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).badStateCo Inst.stT ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).IsComodel
      ((ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).stateTheory Inst.stT) Inst.labSt
      (ourInst (ℍ := ℍ) orowRF Inst.Ξst J₁).badStateCo Inst.stT :=
  ⟨fun _ T l => ⟨Inst.state_isComodel_J₁ T l, I.state_correct_J₁ T l⟩, Inst.admEff_Ξst,
    Inst.not_ansCorrect_badState, Inst.not_isComodel_badState⟩

/-- Binary and cross-language over Core, out of the first pass (stated, OPEN). -/
example (J : TypingJ) (fuse : Val → Val → Val) : Prop :=
  Laws (ℍ := ℍ) J fuse ∧ Abstraction (ℍ := ℍ) J ∧ I4c (ℍ := ℍ) J

end Targets

end
