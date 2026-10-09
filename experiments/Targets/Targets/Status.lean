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
import Targets.I.RejectsFin
import Targets.Instance.ContUse
import Targets.Instance.RunTyping
import Targets.I.Restricted.InstanceSafety
import Targets.I.GhostCoupling
import Targets.I.J1
import Targets.I.ContUseJ1
import Targets.I.Theories
import Targets.Instance.UnaryLaws
import Targets.B.BumpSim
import Targets.Instance.E10
import Targets.I.S5J1
import Targets.I.AcceptsRejects
import Targets.I.AlgJ1

/-!
# Targets — status, by system (RESTRUCTURE §0)

Status words: **PROVED**, **PROVED AT σ=[]**, **PROVED AT A RESTRICTION** (the restriction named),
**OPEN**, **FAILS AS WRITTEN** (a machine-checked configuration; the restatement is the user's),
**RESTATED** (by the user's decisions of 2026-10-07, below; a refutation of the earlier statement is
not kept, except where a row says it is kept as a record).  Four parts: **A**, an effect system, abstractly; **B**, the borrow calculus, given;
**I**, the interaction and the combined theorem; **the Instance**, our calculus as one instance of
A.

## Done

Done is `I.Combined orowRF J₂ W admClosedOp .any` (`Targets/I/Combined.lean`) at a **named**
tier-2 typing system `J₂` and a **named** world `W`, with `audit_W` (`Targets/Audit.lean`): A's
properties at our instance at every admissible effect context, B's guarantees in the composite, the
interaction's option-neutral rules, the pins, the composite's programs and its rejections.  Fixed at
`admClosedOp` until OQ-56 is chosen and at `orowRF` until OQ-13's remaining question is answered.

**Done: OPEN.**  Neither `J₂` nor `W` is defined.

**Tier 1** (`I.Tier1 J₁`): **FAILS AS WRITTEN** (`status_tier1_J₁`): its A conjunct asks A's (E)
properties at every admissible effect context, and E7, E8 and E9 fail at `J₁` at every effect
context under option A (decision E, below).  **S5 is RESTATED prefix-closed** (fix-up F3, below):
every run from a cancel's or an unwind's start is a prefix of a trace; and **RESTATED under frame
deadness** (M3, below): a cancel's trace passes the running finaliser of an earlier cancel
(`pend`), and a cancel's start is a cancel of `capture l H K` or of an affine continuation at its
cell.  At `J₁` at every effect context its unwind is PROVED and its no-interception PROVED given
`CancelsNamed` (every cancelled continuation's running finalisers hold kept errors of labels'
names; OPEN, a syntactic run invariant) (`status_cancellation_J₁`; SPEC §19, decisions D1 and D2
of 2026-10-08).  Read whole, S5 fails at `ΞA` and is kept as a record.  **S4 is RESTATED at the capture cell and PROVED at `J₁` at every
effect context** (`status_handlerSem_cell`; fix-up F1, below): a catch either hands `capture l H K`
and keeps the store, or allocates one fresh unit cell and hands `κ` at it; S4 with no cell fails at
`ΞA` and is kept as a record.  `J₁` is built (decision D5): Core's kernel with
SPEC §24's rules (the polymorphic let, the general `[handle]`, `[then]` at option A) over the open
types, with the row `∀` (`Targets/Instance/J1.lean`); our instance at an effect context reads it with
the rows of its handlers and operations tied to the context (decision R, below).  Proved of it: A's
(S) properties but S6 at every effect context, S5 given `CancelsNamed`, B's guarantees (B5 included,
piece 6), the world's conjuncts and the pins, and the composite's programs (`Accepts`) and
rejections (`Rejects`; decision AR, below).  So `I.Tier1 J₁` follows from A's (E) properties,
`CancelsNamed` and S6 at every admissible effect context (`status_tier1_J₁_of_ENU`; with S5 as a
hypothesis, `status_tier1_J₁_of_ECU`; with S4 too, `status_tier1_J₁_of_ESU`).
TIER1-PLAN §2's first route (elaborating each derivation into the kernel before D5) does not reach
tier 1 (`status_elab_route`); `J₁` is built by D5's route instead.

**The restricted tier-1 reduction** (`I.Tier1Core`, at today's kernel `tier1Open` and Core's world):
**PROVED AT σ=[] given S5 at today's kernel** (`status_tier1Core_of_S5`; with S4 as a hypothesis,
`status_tier1Core_of`).  Proved of it: A's properties but S5 at every admissible effect context — S0
(from `LiveOK`, proved), the let law, S1, `DataDiv`, S2 and S3 (`status_sPropsNoCancel_tier1Open`),
S4 at every effect context (`status_machShape_handlerSem_tier1Open`); B's guarantees, B5 included
(`status_tier1Core_guarantees`; B5 alone, `status_releasedOnceReuse_tier1Open`); the world
conjuncts and the device at `coreW` (`status_tier1Core_world`); its `Pins` conjunct
(`status_pins_tier1Open`).  Missing: S5 at our instance, whose unwind is PROVED there and whose
no-interception is PROVED given `CancelsNamed` (`cancellation_tier1Open`).

## Piece 6: the step-for-step simulation (OQ-43 (b))

**B5 is PROVED** at every typing system and borrow world from B4′
(`status_releasedOnceReuse_of_soundContracts`), so at today's unr-free kernel, at `J₁` and at
`tier1Open`, at BoLo (`status_releasedOnceReuse_tier1Open`, `status_guarantees_J₁`).  Every complete
run of a typed program is, step for step, the image of a run of the bump allocator from the same
start (`Targets/B/BumpSim.lean`):

* **The simulation** (`status_bumpSimAt`): `BumpSim` with the hypotheses a bump run supplies — the
  platform keeps its protocol; the memory is finite (every memory a run from `init` reaches is);
  `g` moves as a block the window `[ℓ, ℓ + (k + 1) · 2³²]` above every named location `ℓ`, at `k`
  the steps to go (`AffineAbove`, read at `k + 1` before a step and at `k` after it; the identity
  meets it at `init`); and the platform's stops are at data arguments (`PlatData`).  The bump step allocates above every name, every window and `X`, where the
  new map translates onto the given step's cell or block; a step that allocates nothing is the
  given step renamed, along the same map (`head_image`, Core's unique decomposition), and its array
  arithmetic stays within the windows.
* **The protocol on every run** (`platData_of_safe`): a program safe under the platform restricted
  to data arguments asks the platform at data arguments only, on every run; B4′ quantifies over
  every platform that keeps its protocol, the restricted one among them.
* **`BumpSim`** over every related configuration: not proved, and not used.  Its hypotheses carry
  none of the invariants a bump run keeps; `BumpSimAt` adds them.

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
  option A's is `finaliserOrder_A`.  The kernel half is applied with D5: Core's `[then]` at option A
  types its finaliser at the pure row (SPEC §24, now the derived rule `CDerives.effThenA` of SPEC
  §27's `[then]`), and so do `CDerivesNU`, `CDerivesAt` and the pin's `RC_effThen`, each with
  `[then]`'s unrestricted premise read at every depth of the cancel rows (`Row.UnrD`), as Core's.
  Check 2's derivations, whose finalisers let a raise escape, are not kept.  OQ-7 is separate and
  open.
* **D4, the restatements.**  S6 counts a step that applies `κ` to a data value as a use (`UseAt`);
  `RunsAlike` (read by `TailLaw`, `EtaHold` and `AlgLawCode`; `AlgLaw` reads it with a finaliser's
  start observed but not its code, fix-up F2) compares a program's data answers;
  `EffSafeDrive` observes a finished drive (`DoneDrive`); S5's runs carry the no-interception
  condition on the finalisers they fire (`FinRow`: a finaliser is typed at a row of abortive
  operations of labels in `FR`).  Its teeth are OPEN under frame deadness (below): a finaliser
  that performs the operation of the cancelled continuation's handler now meets no handler, and its
  run is a cancel trace at every set of endings (`status_finAlone_dead`).
* **D6, S1.**  `SubClosed` carries `[sub]`'s well-formedness premise.  At an admissible context a
  well-formed row is unr-free (`rowNU_of_wf`), and S1 holds at today's kernel
  (`rowAlgebra_ourInst_tier1Open`); the premise is needed (`subClosed_needs_wf`).  The earlier
  refutation used a row that is well formed at no admissible context, and is withdrawn.
* **D5, `J₁` by new Core rules** (SPEC §24).  Core's `CDerives` gains the polymorphic let
  `letPoly` (a closed λ-value bound by substitution, so one function is used at several rows) and
  the general `[handle]` `effHandleV` (the handler a value form over a persistent context; the
  two-variable form `CDerives.effHandle` is its instance), and its `[then]` takes the finaliser at
  the pure row; each with its `fundamentalC` case (`letPoly_compatC`, `handleV_compatC`,
  `then_compatC`); `fundamentalC`, `adequacyC` and `adequacyD` keep their statements.  No change to
  the machine, the relation or the borrow rules.  `tier1Open` (`CDerivesNU`) is the kernel's
  unr-free fragment without the two additions; the rows below that read "today's kernel" are about
  that fragment.  `J₁` closes a polymorphic slot by substitution (`fillS`), so its reading is Core's
  kernel (`j1_read`) and its FL is `fundamentalC`; at a context with no polymorphic slot its open
  judgements meet `FLOpen`'s relation, a polymorphic type read as the intersection of its instances
  (Law 1, `flOpen_J₁_mono`).
* **S6 by a ghost obligation (route 8.4): its probe found none in BoLo's model; the capture cell
  (decision S6, below) is that obligation.**  The probe ran R1, R2 and R3 on the machine before the
  cell, where they allocate nothing and are in Core's relation.
* **An encoding defect, repaired.**  Reading every operation index through `UInt32.ofNat` made `i`
  and `i + 2³²` one operation, and a runner keeping its protocol could answer the second at any
  type; checked in Lean before the repair.  An index beyond `UInt32` now encodes to an open stuck
  term (`opJunk`), which no closed configuration holds.

## The capture cell (decision S6, 2026-10-08)

The machine carries a linear or affine capture's obligation at run time (SPEC §25): a handler's
value carries its operations' tags, and the catch of a linear or affine operation hands its clause
`κ` with a fresh unit cell, allocated by the ordinary allocator; `κ`'s resume frees the cell, and
so does an affine `κ`'s cancel; a linear `κ`'s cancel branch has no step.  No BoLo definition
changed; Core's effect lemmas and `fundamentalC` are re-proved with `adequacyC` and `adequacyD`
unchanged; the lowering's counts are unchanged.

* **S6, restated per capture event** (decision S6; `ContUseEv`, `CatchEvAt`, `caughtEv`): on every
  complete run of a typed program at a data answer, each `κ` that a capture event hands is used
  once per event, and cancelled at most once per affine event.  The capture event reads `κ` off the
  run (the first hand-off of the clause after the catch), so the cell's `κ`, which no function of
  the handler and the context names, is counted.  `ContUse`, read at `capture`, is kept as the
  earlier reading.
* **S6's tooth** (`status_contUse_teeth`): a typing system that types R1 at a resuming linear or
  affine operation fails S6 (its run completes at `ff`, `κ` handed once and never used, its cell
  left allocated); `JR` types it at `ΞA`.  R2–R4 have no complete run at such an operation, and no
  lemma here concludes more of them.
* **The obligation is in Core's relation** (`status_ghostCoupling`): R1 at a linear or affine
  operation is not in Core's relation at `F bool` (`I.not_semC_R1`): its run leaks `κ`'s cell, and
  Core's relation at a returner ends every run from the empty memory at the empty memory.
* **The answering class keeps its laws** (`Targets/Instance/CellRuns.lean`): a run around one cell
  — quiet to the allocation, quiet at every location from the allocation to the release, quiet on —
  is calm (`Calm`), and two terms with a common calm reduct run alike (`runsAlike_of_calm`), the
  memories of reached configurations being finite (`finDom_reach`).  The tail-resumptive law,
  algebraicity at the answering class and D1.h4's comodel reduction hold at every operation
  (`calm_tailClause`, `calm_opStep`, `calm_fold`); the bad-state witness runs calmly around two
  cells.
* **S4, restated at the cell, is PROVED at `J₁` at every effect context** (`status_handlerSem_cell`;
  fix-up F1, below).  S4 with no cell (`HandlerSemNoCell`), whose catch law hands `capture l H K`
  and keeps the store, fails at `ΞA`: Core's handled program at the linear `tick` reaches the catch,
  from which the store-keeping steps reach only the catch and the clause at `κ` before its cell,
  while the clause at `capture l H K` runs through terms that name neither `perform` nor `alloc`
  (`not_handlerSemNoCell_J₁_ΞA`, kept as a record).  It holds at an effect context whose resuming
  operations are unrestricted (`handlerSemNoCell_orow`); an admissible context has none.
* **S6 at `J₁`, reduced to the cell's ownership** (`status_contUseEv_J₁_of`): a capture event hands
  `kappaC aff ℓ …` at a freshly allocated `ℓ` (`catchEv_cell`); a use releases `ℓ` three steps later,
  a linear `κ`'s cancel reaching a branch with no step (`use_frees_cell`); every complete run ends at
  the empty memory (`I.leakFreeAt_J₁`).  From these, S6 follows given two run properties of the cell,
  OPEN: only a capture's `κ` releases its cell (`OnlyOwnerFrees`), and a `κ` is used only while a
  cell of its own lives (`NoDanglingUse`) (`contUseEv_of_cells`).

## Fix-up F1: S4 at the capture cell

S4's catch law asked every catch to hand `capture l H K`, a value computed from the handler and the
context, and to keep the store; the capture cell (decision S6, SPEC §25) makes the catch of a linear
or affine operation allocate.  S4 is restated so that a catch may allocate the cell, and no further.

* **The statement** (`Targets/A/Soundness.lean`).  A continuation may own a cell of the store: A
  carries the cells (`Cell`), `κ` at a cell (`captureAt k l H K ℓ`, the continuation of a caught
  operation of class `k`), a location the store does not hold (`cellFree`), and the store with a
  unit cell added (`withCell`) — the one-shot continuation object of Affect §3.1, allocated at the
  catch and released by the continuation's use.  `JoinAcross c c' t`: a common reduct with `t` at
  `c'`'s store, reached from `c` by store-keeping steps but one, which leaves the store of `c'`.  The
  catch law (`CatchLaw`): the clause gets the argument and `κ`, either `capture l H K` with the store
  kept (`PureJoin`, as before), or `κ` at a fresh cell `ℓ` with the store gaining `ℓ` and nothing else
  (`JoinAcross c (withCell c ℓ)`).  Deep resume and cancel at a cell (`ResumeCellLaw`,
  `CancelCellLaw`, an affine `κ`'s): `κ` at `ℓ`, in a store holding `ℓ`, releases `ℓ` and then runs as
  `capture l H K` does.  The return, abortive, deep-resume, cancel and finaliser laws are unchanged.
  `HandlerSem` is the nine laws; `HandlerSemNoCell` is S4 with no cell (seven laws, the catch
  store-keeping), kept.
* **Not weakened beyond the cell.**  At an instance with no cells the two are the same statement
  (`handlerSem_iff_noCell`, every instance), so every refutation of S4 with no cell at such an
  instance refutes S4 (`not_handlerSem_of_noCell`).  S4 has teeth where no cell is involved: at an
  instance whose `handle` ignores its clauses the catch law fails (`not_handlerSem_toy`).  The cell
  alternative changes the store by exactly one allocation, of a location the store does not hold,
  and hands `κ` at that location, whose resume and cancel the cell laws pin.
* **At our instance, PROVED at every effect context** (`handlerSem_ourInst`, `handlerSem_orow`;
  at `J₁`, `I.handlerSem_J₁`; at today's kernel from `liveOK_tier1Open`), given `LiveOK`: at an
  unrestricted operation the catch hands `kappa` and keeps the store (`catch_unr_ourInst`); at a
  linear or affine one it allocates `()` at a location the reached memory leaves free (memories of
  reached configurations are finite) and hands `kappaC` there (`catch_cell_ourInst`); resuming
  `kappaC` and cancelling an affine one release the cell three steps later and run on as `kappa`'s do
  (`resumeCellLaw_ourInst`, `cancelCellLaw_ourInst`; `kappaC_resume_parts`, `kappaC_cancel_parts`).
* **Not vacuous at `J₁`** (`I.catchLaw_progT_cell`, `status_cellLaws_J₁`): at the admissible `ΞA`,
  `progT` reaches the catch of the linear `tick`, where every premise of the catch law holds; the
  store-keeping alternative fails there (`not_pureJoin_progT`), and the catch allocates `κ`'s cell.
  E4's `deepGen` reaches its clause's resume of `κ` at its cell (`resumeCell_deepGen`), and
  algebraicity's witness `algAffProg` its finaliser's cancel of an affine `κ` at its cell
  (`cancelCell_algAffProg`), each a configuration at which every premise of the law at a cell
  holds.

## Fix-up F2: algebraicity, a finaliser's start observed but not its code

Algebraicity compared the two sides' traces event by event, each finaliser's start `fire D` by its
code `D`; at the tied `J₁` a finaliser holding the clause's `κ` makes `D` differ between the sides,
which capture different continuations, though it starts at the same point of each run.  The repair
that adds no surface restriction is applied: a finaliser's start is observed, not its code (D4 read
at the trace's events).  The reading is pending the user's confirmation; the alternative, keeping
continuations out of finalisers, is a surface rule and is not applied.

* **The statement** (`Targets/A/UnaryLaws.lean`).  `Ev.start` reads `fire D` as `fire ()` and every
  other event as it is; two events read alike exactly when equal or both a finaliser's start
  (`Ev.start_eq_start_iff`).  `RunsAlikeStart` is `RunsAlike` with each trace read through
  `Ev.start` (`ObsStartFrom`, `obsStartFrom_iff`); `AlgLaw` reads it.  `AlgLawCode`, the statement
  before, reads `RunsAlike` and is kept; it implies `AlgLaw` (`algLaw_of_algLawCode`).
* **Teeth.**  `AlgLaw` fails where `bind` does not associate with `perform` (`not_algLaw_toy`,
  `toy` showing no event), as `AlgLawCode` does (`not_algLawCode_toy`).
* **At `J₁`: PROVED at every effect context given `CfinQuiet`** (`status_algLaw_J₁`,
  `I.algLaw_J₁_of`).  The two sides' runs are matched step for step (`Targets/Instance/AlgSim.lean`):
  `AlgRel M N` relates terms equal but where the left holds `(x to x. M) to y. N` and the right
  `y to x. (M to y. N)`, so the continuations a catch hands each side are related, and so is
  everything a clause builds from them.  Every rule of Core's machine steps alike at related redexes
  (`AlgRel.head`); a step's label agrees read without a finaliser's code (`labelOf_start`); at the
  left's inner `x to x. M` at a value the two β-steps reach `M[x] to y. N` (`ostep_sim`).  A run of
  the right is matched back by a run of the left reached by a typed program (`rstep_bwd`: the left
  goes on, its step is the right's by Core's unique decomposition and determinism, an allocation
  taken at the right's location).  So the complete runs show the same answers and traces read
  without a finaliser's code (`obsStartFrom_iff_rel`, `algLaw_of_good`), at every typing system
  whose typed programs' runs are `AlgGood`: closed and going on (`LiveOK`), answering data
  (`lamFree_answer_of_coreClosed`), asking the runner at data (`lamFree_io_of_coreClosed`, the
  platform restricted to data arguments, `platData_of_start`), and keeping, at a cancel-mode
  finaliser's raise, an error with no λ.
* **`CfinQuiet`, the added hypothesis**: no configuration a typed program reaches is at a
  `[cfin-raise]` step.  Source: option A (SPEC §19, decision D3), `[then]` types a finaliser at
  `F 1`, so it handles its raises itself.  Scope: the configurations the law reads (`Live`).  It is
  not proved here: Core's relation gives it inside `[then]`'s compatibility (`ewp_cfin` at an
  abort-only table with no entry), and no lemma carries that to a run's configurations; fix-up F4's
  `guard` frame makes every `cfin` frame hold `guard e` or a value, so that no `[cfin-raise]` redex
  arises.  Non-vacuity of the hypothesis at `J₁` is that discharge, not shown here.
* **The witness, on the right side** (`algLaw_algAffProg`, `algAffProg_start`): at the
  configuration `algAffProg` reaches with the law's left side under its two handlers, under every
  runner, each side's complete runs answer `()` and show one finaliser's start — at every cell
  `κ`'s allocation picks (`obsFrom_algAffL`, `obsFrom_algAffR`).  `AlgLawCode` fails there
  (`not_algLawCode_J₁`).

## Fix-up F3: S5 read prefix-closed

S5 read every run from a cancel's or an unwind's start whole, as a trace.  A trace stops only where
its constructors stop it, and a fire step's constructor reads the administrative steps that start
the finaliser whole; at our machine `[finalise]` leaves `D ()`, one β-step from `D`, so a run that
stops right after a fire step followed no trace, and S5 failed at `J₁` (`fireProg`).  S5 is restated
so that every run is a prefix of a trace, as a safety property is read, and a trace's fire step goes
with its β-step.

* **The statement** (`Targets/A/Soundness.lean`).  `NoIntercept` and `UnwindOrder`: every run from
  the start is a prefix of a trace — some continuation of it, itself a run, follows the trace.  The
  traces' docstrings say where a trace stops.  S5 read whole (`CancellationWhole`,
  `Targets/A/CancelWhole.lean`) is kept as a record and implies S5 (`cancellation_of_whole`).
* **Not weakened beyond the β-step.**  Every step a run takes is a trace's step; only where it may
  stop changes.  At our machine the extension a run needs is nothing, or the one step after a fire
  step that ends it, the β-step that starts the finaliser (`FireExt`; `unwind_pfx`, `cancel_pfx`).
* **Teeth: OPEN.**  At `J₄`, whose program meets `NoInterception`, the cancelled region's
  finaliser performs the operation of the handler whose continuation is cancelled; the cancel runs
  the region dead, so that operation meets no handler, the run stops there, and the run is a cancel
  trace at every set of endings (`status_finAlone_dead`).  Teeth for `FinRow` need a finaliser whose
  raise escapes to a live handler, which today's kernel does not type (option A).
* **At `J₁` and today's kernel, at every effect context** (`status_cancellation_J₁`): the unwind
  PROVED (`unwindOrder_J₁`, `cancellation_tier1Open`); the no-interception, as restated under frame
  deadness (M3, below), PROVED given `CancelsNamed` (`noIntercept_J₁_of`).  No handler named `0` in
  a cancelled context (`CancelsNZ`) is PROVED as a
  run invariant (`cancelsNZ_J₁`, `cancelsNZ_tier1Open`; `Targets/I/CancelsNZ.lean`): a typed program
  names no handler `0` (I3.c), no machine step creates one, and the runner answers with data — every
  run of a program in Core's relation asks the platform at data arguments only, a driven program's
  too (`driveData_of_reach`) — so every configuration a typed program reaches names none
  (`hndNZ_reach`), and `κ`'s resume branch, which holds `κ`'s context, names none.  The
  no-interception does not read it: the cancel runs the dead region `K†`, which holds no handler.
* **On the right side**: at `fireProg`'s configuration S5 holds with the β-step appended
  (`unwindOrder_fireProg`), where the whole reading fails (`not_cancellationWhole_ΞA`).
* **`CancelsNoCtl`** (no cancelled context holds a `ccatch` or a `cfin` frame) was this section's
  hypothesis; under D2 a cancel nested in a cancel puts a running finaliser's `cfin` frame in the
  region, and the restated trace passes it (M3, below), so it is read by nothing.
* **What S5's no-interception reads.**  Restated (M3, below): a cancel of `capture l H K` (the
  unrestricted `κ`) and a cancel of an affine `κ` at its cell (SPEC §25), the cancels that arise at
  an admissible context, where every resuming operation is linear or affine.

## S5's bridges (decision S5, 2026-10-08)

S5 reads every run from the start of a cancel or of an unwind as a prefix of a trace: each
finaliser fires, runs alone, and hands the cancel or the raise on (SPEC §19).  Decision D4 put the no-interception
condition into the statement: the finalisers it fires are closed programs typed at a row of
abortive operations of `FR`'s labels (`FinRow`), at option A the pure row.

* **What typing gives about such a finaliser** (`status_finOK`): a closed program in Core's
  relation at `F A` runs to a value from every memory with finitely many cells, the memory's cells
  `wpG`'s frame (`ownWorld`: a finite memory is the lowering of a `TW` world, built by `TW.alloc`);
  at a typing system whose closed programs are Core's, a finaliser meeting the condition at option A
  is typed at `F 1` (its row, tied to the effect context, admits nothing and so is empty) and runs
  to `()` from every finite memory (`finOK_of_finRow`).  `FinRowsAt` is not on this route.
* **The traces at our machine** (`Targets/Instance/CancelRuns.lean`): a step of `Kf[t]`, `t`
  stepping, is `t`'s step under `Kf` with its label (`rstep_unplug`), so a fired finaliser runs
  alone while it steps; `[finalise]` (labelled `fire D`), the β-step that starts `D`, `D`'s run alone
  to `()` and `(); raise p` make an unwind trace through a context of A's shape (`unwind_pfx`);
  `[finalise-cancel]`, the β-step when `D` is a λ, `D`'s run alone under `cfin`, `[cfin-ret]`
  (labelled `finEnd none`) and at the end `[cancel]` make a cancel trace with nothing kept, from
  `cancelOf` at a region with no `ccatch`, `cfin` or handler named `0` (`cancel_pfx`; `cancelOf`'s
  region is the dead `K†`, `fins_dead`; a cancelled finaliser frame holds a pair of values, from
  `LiveOK`, `ubind_pair_live`).
* **S5 read whole fails** at every typing system that types `fireProg` and `(); ()` (`J₁` and today's
  kernel among them), at every effect context declaring `exn : 1 ↠ 0` at `1`, the admissible `ΞA`
  among them (`status_cancellation_J₁`): a path that stops right after a fire step, before `D ()`
  has reduced to `D`, follows no trace (`not_unwindTrace_one`).  Kept as a record (fix-up F3,
  above).

## Frame deadness (decision D1 of 2026-10-08, SPEC §19)

A cancel of `κ`, captured at `K`, runs `ccatch (K†[raise (0, (0, none))])`: `K†` (`Kont.dead`) is
`K` without its handler frames and its `ccatch` frames, which catch nothing during the cancel.  The
cancel's state is the error it keeps alone, the first kept winning; `[cfin-cancel]` passes a
running finaliser's `cfin` frame.  No statement here changes.

* **S5's bridges** read the dead region (`cancel_pfx` at `K†`, which keeps `K`'s finalisers,
  `fins_dead`, and holds no handler, `hasHnd_dead`, and no `ccatch` frame, `noCC_dead`).
  `CancelsNZ` is kept as a record, read off `κ`'s resume branch, which holds `K`
  (`cancelsNZ_of_coreClosed`, `hasHnd_shift`).
* **Core's `FinaliserOrder`** no longer reads `NoInterception` (`cancelOrder_at`, at `K†`).
* **The label of `[cfin-cancel]`** is `finEnd` of the kept error of the cancel that passed the
  frame (`labelOf_cfcancel`); the restated trace's `pend` step (M3, below).
* **Algebraicity's simulation** relates the dead regions of related contexts (`AlgRelK.dead`) and
  steps `[cfin-cancel]` alike (`AlgRel.head`, `labelOf_start`).
* **Check 4** (`status_finAlone_dead`): the finaliser that performs the operation of the cancelled
  continuation's handler meets no handler; its run stops there and is a cancel trace at every set
  of endings, so the no-interception condition's teeth are OPEN.

## Finalisers with effects (decisions D2, D3 of 2026-10-08, SPEC §27)

Core's rows carry cancel rows: each capturable operation records what a cancel of its continuation
may do, `[sub]` lets them only grow, `κ`'s cancel branch is at `F_{F ⊕ Σ} 1`, and `[then]` combines
the finaliser's row into the cancel rows of its computation (`⋈`).  Here:

* **Rows.**  `RowLe` is the cancel-row order (`RowLe.sig`, `RowLe.of_find`).  `PlatAgree` asks a
  platform's operation to be the row's by signature (`OpSig.Sig`), since a platform answers at the
  row's types: a strengthening of every theorem that assumes it.
* **The tied kernel stays at option A.**  `CDerivesNU`, `CDerivesAt` and `RC_effThen` keep their
  `[then]` with the finaliser at the pure row, Core's derived `CDerives.effThenA`, and read its
  premise on unrestricted operations at every depth of the cancel rows (`Row.UnrD`), as Core's.  So
  `J₁` types no finaliser with effects, and the refutations of E7, E8 and E9 at `J₁`
  (`Instance/FinRaise.lean`) stand; they are of option A, and are replaced when the tied kernel
  takes §27's `[then]` (FINALISERS §4).
* **I3 and `FrameW`** are stated at entries whose cancel row is empty, the cancel they describe
  (`ShareCancel`'s cancel at the empty error table); `i3_core`, `frameW_core` and `i1_core` read
  Core's cancel obligations.
* **D3 at Core's kernel** (`I/RejectsFin.lean`).  `progT`, typed at a row holding `2`
  (`d_progT`), has no derivation at a row without `2` (`not_der_progT`): the `[then]` puts `2` in
  the cancel row of `perform 1`'s continuation, and `H₁`'s clause reads `κ`'s cancel at its own row.
  `progNCrecT`, two finalisers that perform `4` under the handler of `4` that cancels, has no
  derivation at all (`not_der_progNCrecT`, the leftover clause), and its run ends at a `perform 4`
  no handler catches (`progNCrecT_stuck`).  The inversions read each rule and then the same-term
  rules, which only grow rows (`JS.effSub`'s order, `JR.rowLe`).
* **The audit** pins Core's relation anew and reports `cancelOK` among the fixed points: its
  `∀`-bound predicate is the cancel obligation an entry carries.

## S5 under frame deadness (M3, decisions D1 and D2 of 2026-10-08)

Under D2 a finaliser may perform an operation of a live handler, and that handler may cancel the
finaliser's continuation: a cancel nested in a cancel, whose region holds the running finaliser's
`cfin` frame, which `[cfin-cancel]` passes (SPEC §19).

* **RESTATED** (`Targets/A/Soundness.lean`), into line with D1 and D2; the traces admit the
  algebra's runs and no other:
  - a region's **actions** (`acts`), innermost first: its finalisers (`fire D`), and the running
    finalisers of earlier cancels, each with the error its cancel has kept (`pend e`).  The context
    laws pin them (`KontLaws`): A's frames act as their finalisers say, a frame that stops no raise
    acts on nothing, and the fired finalisers are the context's;
  - the cancel trace takes a `pend e` in one step, labelled `finEnd` of the error kept so far, the
    earlier error `e` first.  `keep` is first-wins with no name list: no error is dropped for its
    label;
  - a cancel's start (`CancelStart`) is a cancel of `capture l H K`, or of an affine continuation
    at its cell, the cell's release among the steps to it (as F1 restated S4).  At an admissible
    context every resuming operation is linear or affine, and these are the cancels that arise
    there.
* **At our instance** (`cancel_pfx`): the dead region holds no handler and no `ccatch` frame, so the
  innermost frame that stops the cancel is a finaliser frame or a running finaliser's `cfin` frame
  (`frame_of_cancel`); at the latter `[cfin-cancel]` passes it, its state a cancel's
  (`cfin_state_live`, `rstep_cfcancel_inv`).  The trace reads a kept error at the labels
  (`keptErrOf`), the first error read first (`keptErrOf_or`), and the canceller is answered with the
  kept error so read (`answered_some`).
* **`CancelsNamed`, the hypothesis left (OPEN)**: at a configuration a typed program reaches that
  cancels a continuation captured at `K`, every running finaliser's `cfin` frame of `K` holds none
  or the raise of a label's name.  A kept error of a name no label has would be read as none, and
  the canceller answered `()` where the machine raises it.  Its source is syntactic: a `cfin` frame
  keeps what a finaliser raised (`[cfin-raise]`) or what a passing cancel kept (`[cfin-cancel]`);
  at `J₁` every raise a typed program writes is of a label's name (the tie, decision R), and the
  machine raises only those, the cancel's `0`, and kept errors.  A run invariant of `hndNZ_reach`'s
  kind.
* **`CancelsNoCtl`** is read by nothing: the restated trace passes a `cfin` frame.

## Decision R: `J₁`'s inner rows tied (2026-10-08)

Decision D1 ties a program's row to the effect context; decision R ties the rows inside its
derivation the same way (`status_innerTie`).

* **The tied kernel** (`Targets/Instance/TiedKernel.lean`): `CDerivesAt Ξ` is Core's `CDerives`
  with `RowAt Ξ` at the three rules that read an operation's signature off a row — `[perform]` and
  `[raise]` (the row the operation is found in) and `[handle]` (the handled row `(n)↑E ⊙ Σ`).  Every
  tied derivation is Core's (`CDerivesAt.toCDerives`), so `fundamentalC` holds of it.  At a tied
  handler the signature `E` is a prefix of `Ξ n`, so the handler value's tags (SPEC §25) are a
  prefix of `Ξ`'s qualifiers of `n` (`sig_prefix_of_rowAt`, `hndTags_of_rowAt`).
* **`J₁` at an effect context** (`J1DerAt`): `J1Der` with Core's kernel read as `CDerivesAt Ξ`, at
  the row environments tied to `Ξ` (`EnvAt`, as D1 reads a program's row), polymorphic slots closed
  by λ-values typed at their instances at tied rows.  A typing system carries its judgement at an
  effect context (`OurTyping.derAt`), which our instance at `Ξ` reads; every other typing system
  here ties nothing (`derAt` is `der`).  `J₁.read`, which B and the pins read, is Core's whole
  kernel (`j1_read`, unchanged), so B's guarantees, FL and the pins at `J₁` are unchanged.
* **Re-established at the tied `J₁`**, every statement unchanged: the let law and S1
  (`letLaw_ourInst_J₁`, `rowAlgebra_ourInst_J₁`), S0, S2, S3 and `LiveOK` (through
  `coreClosed_J₁At`), S4 with no cell where resuming operations are unrestricted, leak freedom
  and S6's reduction, the comodel results, the answering-class laws, and the failures of S4 with no
  cell (`progT` types with its rows tied, `progT_derivesAt`) and of the bad state's handler
  (`d_stProg` at `Ξst`).
* **The open finding on algebraicity, settled** (`status_unaryLaws`): the round-2 witness handles
  the name `5` at an `unr` operation where `ΞA` declares `tick` linear; its handled row is not tied
  to `ΞA` (`not_rowAt_R5`), no tied handler of `5` carries the tag `unr` (`not_tied_hnd5_unr`), and
  the tied `J₁` at `ΞA` types it at no type (`not_der_algFireProg_J₁`, by inversions of the tied
  kernel at its two handlers: `derAt_withH`, `derAt_let`, `derAt_lam`, `derAt_hnd`).  Algebraicity
  still **FAILS AS WRITTEN at the tied `J₁`** at `ΞA`, by a witness at the affine `wait` (below).
* **A tied handler may declare a prefix of `Ξ n`.**  A's `handle` is the handler frame at `Ξ`'s whole
  tags (`qsOf`), so the frame of a typed program's handler of a proper prefix is no A-level handler
  frame, and S4's catch law and S6's capture events do not read its catches.  Whether a handler
  declares all of `Ξ n` is a reading for the user (TIER1-PLAN, round 3, step T2).

## A's (E) properties at `J₁` (decision E, 2026-10-08)

**`EProps` FAILS AS WRITTEN at `J₁`**, at every effect context (`status_eProps_J₁`): E7, E8 and E9
each ask for a typing of a program whose finaliser raises to its context, and `[then]` types a
finaliser at `F 1`
(option A, D3; `not_cancelPolicy_J₁`, `not_unwindPolicy_J₁`, `not_storedK_J₁`).  The others, at
every admissible effect context:

* **The callbacks** (SPEC §26, Entry 25): Core's `[λ-dead]` types `λx. M : 1 ⊸ F_Σ B` with `x`'s
  slot dead (`lamDead_compatC`), so a schema's callback `λ_. M`, `M` typed at the empty context, is
  typed (`d_cbDead`).  Weakening by an unused live slot is not derived.
* **E1, no colouring: PROVED** (`noColouring_J₁`): `hof` typed once at `U(∀ρ. U(1 ⊸ F_ρ bool) ⊸
  F_ρ bool)`, its schema, its call, and E1's and E1′'s programs typed and run, E1′'s around the
  affine `wait`'s capture cell.
* **E2, higher-order polymorphism: NOT DERIVED.**  Its fourth program (E2d, `sumGen`) is PROVED at
  every admissible effect context with no `unr` operation (`e2d_J₁`, at every label list
  `higherOrderPoly_e2d_J₁`; `NoUnr`, met by `ΞA`): typed once, its schema at every `yield ⊙ ε`,
  its body typed and run.  Its clause's `[let]` holds
  `x : bool` across the resume, and at a row with an `unr` operation `[let]` asks the continuation's
  context to be persistent (`!`).  E2a (`twice`), E2b (`compose`) and E2c (`retryP`) are not derived
  and no obstruction is verified: each holds a function at `!U C` (used twice; held across a `[let]`
  at a row with a non-linear operation, whose continuation's context must drop; called from a
  handler's clause, whose context is persistent) and forces it, and Core's `force` reads a slot at
  `U C` only.
* **E3, loops: NOT DERIVED**, no obstruction verified.  Our instance writes `unfold f g s` as the
  stepped codata value `etaN C ⟨f, g⟩ s` (`unfoldE`), whose code applies Core's recursive handle
  `selfNu` (the self-application `selfV`).  The tied kernel types coiteration only as the constant
  `unfold_C` (`[unfold]`) and a `&`-computation only in `⟨M, N⟩`'s form (`withI`); no rule concludes
  a type for `etaN`.  TIER1-PLAN §4 records that `unfold`'s unrolled states need a rule of their own.
  E3's runs are not attempted.
* **E4, deep handlers: PROVED** (`deepHandler_J₁`): `deepGen` typed at `tick`'s row; it answers `()`
  showing two ticks, each yield caught around `κ`'s cell and the handler reinstalled by the resume.
* **E5, nested handlers in both orders: PROVED** at every admissible effect context with no `unr`
  `exn` signature (`nestedHandlers_J₁`, `NoUnrExn`, met by `ΞA`).  With `toResult` outside,
  `withLog`'s clause is typed at `exn`'s row, and its state function's `[let]` holds the logged
  `bool` across the resume.
* **E6, no accidental handling: PROVED** (`tunnel_J₁`): `fwrap` typed once, its handler at the row
  without `exnᵢ`; the callback's raise of `exnₒ` passes it.
* **E10, the reconciler: NOT DERIVED.**  `timeout` is typed once, with its schema and its call
  (`derV_timeoutR_J₁`, `polyUseOpen_timeoutR_J₁`, `callsThrough_timeoutR`).  `retry` forces a body
  at `!U C` (as E2c); the loop is built by `unfold` (as E3).

## The composite's programs and rejections at `J₁` (decision AR, 2026-10-08)

`J₁`'s reading is Core's kernel (`j1_read`), so both conjuncts are about `CDerives`.

* **`Accepts J₁.read .abortive`: PROVED AT σ=[]** (`I.accepts_J₁`; `CompositeT1 tier1`,
  `compositeT1_tier1`).  Each of the eight programs is typed at its data answer and safe and
  terminating under the empty platform (`acceptedT1_*`), and one complete run answers the stated value.
  The run is computed: `runM` (`Targets/Base/LookMem.lean`) adds the memory steps (`alloc`, `free`,
  `load`, `store`, at a memory kept as a list of cells) to `look`'s steps, the kernel evaluates it to
  the answer at the empty memory (`run_*`, by `rfl`), and `runM_sound` makes it a run of Core's
  machine.  The interpreter's runs (`*_eval`) stay evidence; these are proofs.
* **`Rejects J₁.read`: PROVED AT σ=[]** (`I.rejects_J₁`; `Rej.rejects_tier1`): AT05, AT06, AT08 and
  AT13 have no derivation in Core's kernel, at any context and any judgement
  (`Targets/I/Rejects.lean`).  The inversions are thirteen inductions on `CDerives`, each carrying a
  class of judgements through the fourteen same-term rules (the value rules `!E`, `[]I`, `[]E`, the
  two `⊑`, `roll`, `unroll`; `return`, `ofRet`, `[sub]`, `ν`'s two; at a λ-value, the two thunk
  rules): a variable, a pair, `()`, an application, a λ-value (with its constants' axioms), `let (x,
  y)`, `;`, `then`, `handle`, `alloc`, the primitives; and every free variable of a typed term has a
  live slot (`fv_live`).  About 2200 lines, 17 s to build.
  * **AT06** (`not_der_at06`): the clause is in `[handle]`'s clause tuple, so at a `!U` type over a
    persistent context, and it uses the cell, whose slot is a view of a `Ref`.
  * **AT13** (`not_der_at13`): the clause's `κ` is at `kTy` at `lin`, a thunk of an `&`; `forget`'s
    axioms take `!`, `Imm`, `Mut`, `Unk` and `ArrayImm`, and as a λ it drops a persistent argument
    only (`not_forget_kappa`).
  * **AT05** (`not_der_at05`): typed as a λ, `withborU dFlag` uses its source on both sides of its
    `then` (`wb_generic`), and the cell is a `Ref`; typed by an unwinding constant, the callback is
    at `∀'x ⊏ @b. L ⊸ F_Σ(['x] B)`, `L` a borrow, where `λm. (m, m)` uses `m` on both sides of a
    split (`not_at05F_cb`).  The `copy` axiom types the λ-value `copy`, not a body under a borrow,
    so the rejection holds at the `Imm` lend too.
  * **AT08** (`not_der_at08`): **the rejection rests on `load`**, which has no rule of its own in
    Core's kernel (`der_prim`, `not_der_load_app`); reads go through `withload` and `swap`.  The
    reason RESTRUCTURE §3.4 gives (`kTy` at `lin` and `aff` neither droppable nor persistent) is not
    what refuses the program as written.  A restatement of AT08's program, reading the cell by
    `withload` or `swap`, is the user's.

## Piece 5: the answering class (D1.h1–h4)

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
  calmly as the co-runs do (`calm_fold`, the native counterpart of `handle_fold`) and meet.  `stateCo`
  is a comodel and its handler correct (`state_isComodel`, `state_correct`; at `J₁`,
  `I.state_correct_J₁`).  Not vacuous: at `J₁` and an admissible context with a state signature
  (`Ξst`), the handler whose `put` keeps the old state fails the update–lookup law at a typed
  program, and its co-operations are no comodel (`status_theories`).
* **The unary laws at our instance** (D1.h1, D4's restatement).  **Algebraicity, restated with a
  finaliser's start observed but not its code (fix-up F2), is PROVED at `J₁` at every effect context
  given `CfinQuiet`** (`status_algLaw_J₁`; below).  Observing the finaliser's code, it **FAILS AS
  WRITTEN at `J₁`, its inner rows tied** (`status_unaryLaws`, kept as a record): at `ΞA`, an inner
  handler of the affine `wait` raises `exn` from its clause inside a finaliser frame whose finaliser
  cancels the clause's `κ` and handles the cancel's `exn` itself, so it is at the pure row (option
  A); the trace's `fire D` compared `D`'s code, which mentions the `κ` the two sides capture
  differently (`Targets/Instance/UnaryLaws.lean`); at the same configuration the restated law holds
  (`algLaw_algAffProg`).  The round-2 witness, at an `unr` continuation, is outside the tied kernel.
  The tail-resumptive law and η: OPEN (below).  At the answering class (a tail-resumptive clause
  whose code runs quietly) both the tail-resumptive law and algebraicity hold, observing the
  finaliser's code (`tailLaw_quiet`, `algLaw_quiet`; at `J₁`, `I.tailLaw_quiet_J₁`,
  `I.algLaw_quiet_J₁`).
* **The answering class as `[handle]`, D1.h2: OPEN.**  `I4Typing` (the typing half) and `I4Runs`
  (the run correspondence, stated here: the control form and the borrow form in one evaluation
  context of a reached configuration reach the same values) are not derived at `J₁`, and no
  obstruction is verified (the interaction's rows).  Under D1+B4 the facts the hard test asks of an
  answering handler (its fold, its correctness as a model, the answering-class laws) are proved at
  native `hnd` directly, above.

## System A

| target | status | Lean |
|---|---|---|
| `EffectSystem`, S0–S6, E1–E10, `Props`; A₂ (`HandlerLaws`, `EffDepLaws`, `Abstraction`); A₃ (`Tgt`, `LoweringCorrect`, `ZeroCost`) | stated (elaborate) | `Targets/A/*` |
| a typing that types nothing fails `EProps`; no effects fail it | PROVED (every instance) | `not_eProps_of_emptyTyping`, `not_eProps_of_noLabels` |
| E1, E2, E6, E10 need effect polymorphism (row variables, decision 62) | PROVED (every instance; E10 with `LiftExt`) | `not_noColouring_of_monoCallback`, `not_higherOrderPoly_of_monoCallback`, `not_tunnel_of_monoCallback`, `not_reconciler_of_monoCallback` |
| E3 needs divergence; a pure-row loop that diverges is not at a data answer | PROVED (every instance; the latter with `RowAlgebra`) | `not_loops_of_total`, `divInTypes_of_loops` |
| effect safety has teeth; Def. 5.1 (1) from one signature object | PROVED (every instance) | `not_der_unhandled`, `c1_of_rowSig` |
| the runners `Rtick`, `Rtl`, `Rrec` keep their protocol | PROVED (every instance; `Rrec` at distinct labels) | `rtick_respects`, `rtl_respects`, `rrec_respects` |
| A's properties at our instance | at today's kernel, every admissible effect context: S0, the let law, S1, `DataDiv`, S2, S3 PROVED AT σ=[]; at `J₁`, every effect context: the same, PROVED AT σ=[]; S4, RESTATED at the capture cell, PROVED AT σ=[] at both at every effect context (S4 with no cell at an effect context whose resuming operations are unrestricted; it fails at `J₁` at `ΞA`, kept as a record); S5, RESTATED prefix-closed and under frame deadness (M3), PROVED AT σ=[] at both at every effect context given `CancelsNamed` (OPEN), its unwind outright (below); S6 OPEN (below) | `status_sPropsNoCancel_tier1Open`, `status_sPropsNoCancel_J₁`, `status_machShape_handlerSem_tier1Open`, `status_handlerSem_cell`, `status_cancellation_J₁` |
| S4 (`HandlerSem`), RESTATED at the capture cell (F1): a catch hands `capture l H K` keeping the store, or one fresh unit cell and `κ` at it (`CatchLaw`, `JoinAcross`); `κ` at a cell released by its resume and an affine cancel (`ResumeCellLaw`, `CancelCellLaw`); the other five laws unchanged. S4 with no cell (`HandlerSemNoCell`) kept | at an instance with no cells the two agree (PROVED, every instance), so a refutation of S4 with no cell there refutes S4; S4 fails where `handle` ignores its clauses (PROVED) | `handlerSem_iff_noCell`, `not_handlerSem_of_noCell`, `catchLaw_of_keep`, `not_handlerSem_toy`, `not_handlerSemNoCell_toy` |
| the unary laws beside done, `UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`) and the alternative `EtaLin`: run-level (menu form F.3), the tail law's hygiene as hypotheses, compared at a program's data answers (D4); `AlgLaw` with a finaliser's start observed but not its code (`RunsAlikeStart`, `Ev.start`; fix-up F2), `AlgLawCode` (the finaliser's code observed, `RunsAlike`) kept as a record | RESTATED; STATED (at our instance: the Instance's rows); **not in done**: whether they join done is a menu choice (P11/I5 menu axes H, F, K), for the user | `Targets/A/UnaryLaws.lean` |
| `AlgLawCode` gives `AlgLaw`; the two observations differ only at a finaliser's start | PROVED (every instance) | `algLaw_of_algLawCode`, `runsAlikeStart_of_runsAlike`, `obsStartFrom_iff`, `Ev.start_eq_start_iff` |
| theories (D1.h3, D1.h4 (a)–(b)): equations in signatures (`Eqn`, `SLComp`, `Theory`), the state-passing handler of co-operations (`ansHnd`, `runAt`), handler correctness (`AnsCorrect`, Plotkin–Pretnar Def. 4.5 at `RunsAlike`), comodels (`IsComodel`, Ahman–Bauer Def. 1 with equations), global state (`stateTheory`, `stateCo`, `badStateCo`) | stated (elaborate); at our instance: the Instance's rows | `Targets/A/Theories.lean` |
| `EtaHold` gives `EtaLin`; each of the four fails at an instance whose handler or bind ignores its clauses (and so does `AlgLawCode`) | PROVED | `etaLin_of_etaHold`, `not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy`, `not_etaLin_toy`, `not_algLawCode_toy` |
| S5 (`Cancellation FR`), RESTATED prefix-closed (F3): every run from the start a prefix of a trace (`NoIntercept`, `UnwindOrder`). S5 read whole (`NoInterceptWhole`, `UnwindOrderWhole`, `CancellationWhole`: every run a trace) kept as a record | the whole reading implies S5 (PROVED, every instance) | `noIntercept_of_whole`, `unwindOrder_of_whole`, `cancellation_of_whole` |
| A₃'s reference programs (the `Tgt` code checking each `refCost` entry) | not written | RESTRUCTURE §Unresolved |

## System B

| id | guarantee | status at BoLo | Lean |
|---|---|---|---|
| B0 | BoLo's programs stay typed | PROVED AT σ=[] | `extendsB_tier1` |
| B1 | the fundamental property | PROVED AT σ=[] | `fl_core_tier1`, `fl_core_tier1NU` (at `coreB`) |
| B2 | adequacy | PROVED AT σ=[] at every platform that keeps its protocol: the return conjunct through its answers; the drive conjunct at positive loop bodies (D2), so at rows with distinct keys. The hypothesis is needed: at a loop type whose body is not positive (a shadowed entry with an open type) `cC` holds of `()`, whose drive is stuck at `nextE ()` | `adequateRetAt_core`, `adequateDriveAt_core`, `adequate_core`, `adequateDriveAt_core_uniq`, `adequateAt_core_none`; `adequateDrive_needs_nuOk` |
| B3, B4 | safety, leak freedom | PROVED AT σ=[] at today's unr-free kernel (from FL and B2), the drive conjunct at positive loop bodies | `sound_tier1NU`, `soundRetAt_tier1NU`, `soundDriveAt_tier1NU` |
| B4′ | with externs meeting W's contract | PROVED (generic, from B1 and B2, finding #7); from B1 and B2's return conjunct alone (generic), so PROVED AT σ=[] at today's unr-free kernel | `soundContractsOfFL`, `soundContractsOfFL_ret`, `soundContracts_tier1NU` |
| B5 | release exactly once, reuse included | PROVED (generic, from B4′), so PROVED AT σ=[] at today's unr-free kernel and at `J₁`: through the step-for-step simulation at the configurations a bump run reaches (`BumpSimAt`, PROVED; piece 6); not a tautology: PROVED | `releasedOnceReuse_of_soundContracts`, `releasedOnceReuse_tier1NU`, `I.releasedOnceReuse_J₁`, `bumpSimAt`, `not_releasedOnceReuse_staleFree` |
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
| `CompositeT1 tier1`: typed, safe and terminating under the empty platform, one complete run answering the stated value | PROVED AT σ=[] (the run computed by `runM`, `runM_sound`) | `compositeT1_tier1`, `acceptedT1_*`, `run_*` |
| `Accepts J₁.read .abortive`, `Rejects J₁.read` (decision AR) | PROVED AT σ=[]; AT08's rejection rests on `load` having no rule | `I.accepts_J₁`, `I.rejects_J₁`, `Rej.rejects_tier1`, `status_acceptsRejects_J₁` |
| `Tier2Programs`, `RejectsAT07` | OPEN (no tier-2 typing system; AT07's stuck run not written out) | — |
| `EffSafe tier1` (Core's P2) | PROVED AT σ=[] | `effSafe_tier1` |
| `EffSafeDrive` (P2 for driven programs), RESTATED (D2: a positive loop body; D4: a finished drive observed, `DoneDrive`) | PROVED AT σ=[] at every typing system with FL at BoLo, so at today's unr-free kernel; the hypothesis is needed; the route at a generic world, `EffSafeDriveOfFL`, OPEN | `effSafeDrive_of_FL`, `effSafeDrive_tier1NU`; `effSafeDrive_needs_nuOk` |
| `Pins tier1Open admClosedOp .abortive`, with `I4a` at the unr-free rules | PROVED AT σ=[] (abortive rows) | `I.pins_tier1Open`, `i4a_tier1NU` |
| Law 1 at the relation: `ovalW` at `U(∀ρ:k. C)` and `!U(∀ρ:k. C)` is the intersection of the instances; `FLOpen M J` gives `FL M J.read`; `FLOpen` at today's kernel | PROVED (generic); PROVED AT σ=[] | `I.ovalW_allR`, `I.ovalW_bang_allR`, `I.fl_of_flOpen`, `I.flOpen_core_tier1Open` |
| `J₁`: its reading is Core's kernel; FL at BoLo (B1); B's guarantees; the pins; FL at its open judgements over contexts with no polymorphic slot, a polymorphic type read as the intersection of its instances (Law 1) | PROVED AT σ=[] (abortive rows for the pins); `FLOpen coreB J₁` at contexts with a polymorphic slot NOT PROVED (a value `ovalW` relates there need not be a closed λ-value Core types) | `status_j1`, `status_guarantees_J₁`, `status_pins_J₁`, `I.flOpen_J₁_mono` |
| tier 1 at `J₁` | **FAILS AS WRITTEN**: A's (E) properties fail at `J₁` (E7, E8, E9, option A; decision E); S5 read whole fails too (kept as a record).  S4, restated at the capture cell, is PROVED at every effect context, and S5, restated prefix-closed and under frame deadness, given `CancelsNamed`, so tier 1 follows from A's (E) properties, `CancelsNamed` and S6 at every admissible effect context, `Accepts` and `Rejects` being proved (decision AR) | `status_tier1_J₁`, `I.not_tier1_J₁`, `status_handlerSem_cell`, `status_tier1_J₁_of`, `status_tier1_J₁_of_ESU`, `status_tier1_J₁_of_ECU`, `status_tier1_J₁_of_ENU`, `status_eProps_J₁`, `status_cancellation_J₁` |
| TIER1-PLAN §2's route (elaborate `J₁` into today's unr-free kernel, then `fundamentalC`) | **DOES NOT REACH TIER 1**: closed derivations that elaborate type no A-level handler, so E8 fails; today's kernel types no let-bound function read at two rows | `I.not_tier1_of_elabClosed`, `not_der_letTwo` |
| FIX-RUN-END's checks and witness worlds | PROVED | `Targets/I/RunEnd.lean` (73 results) |
| I1, I3, I5, P11 at `coreW` (the device); I2 at `coreW` | PROVED AT σ=[]; PROVED AT A RESTRICTION (abortive rows) | `i1_core`, `i3_core`, `i5_core`, `p11_core`; `i2_core_abortive` |
| `EmbedsNil coreW` | PROVED AT σ=[] | `embedsNil_core` |
| `AdequateOfLaws`, `FreezeBinder`, `BinderMachine`, `NotVDenNaturalArises`, `I4c` | OPEN (stated) | — |
| D1.h2: `I4Typing` (the typing half) and `I4Runs` (the run correspondence, unary: from a configuration a typed program at a data answer reaches, the control form and the borrow form in one evaluation context reach the same values; data state, operations and body answer, `s₀` at a value judgement) | OPEN (stated); not derived at `J₁`, and no obstruction verified. `I4Typing` needs inversions of Core's typing at `bindE`, at `effHandleV` and along `capPass`'s spine, the clause typing read back to `co_j`'s, a typing of an `n`-free subterm at the row without `n` (none found in Core), and `ansCall`'s typing through `withswap`. `I4Typing` carries no judgement of `s₀`, which the borrow form reads under `alloc'` at a value judgement and `I4a` carries; it is not derived at an `s₀` typed only at an effectful row. `I4Runs` needs a simulation of `n`-free code run under the handler frame on one side and the lend's frames on the other, through the continuations outer handlers capture | `Targets/I/Interface.lean` |

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
| S0 (`MachShape`: `AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`) and S4 (`HandlerSem`) at our instance | S0 PROVED AT σ=[] given `LiveOK` (every configuration a typed program reaches has a closed term and goes on), at every typing system; `Congr` and `OpStuck` without it. S4, RESTATED at the capture cell, the same at every effect context: the catch of an unrestricted operation hands `kappa` and keeps the store; that of a linear or affine one allocates `()` at a free location and hands `kappaC` there; resuming `kappaC` and cancelling an affine one release the cell (SPEC §25). Not vacuous: at `J₁` and `ΞA` the catch of the linear `tick` holds the law by its cell alone. S4 with no cell (`HandlerSemNoCell`) at an effect context whose resuming operations are unrestricted (`CatchUnr`); it **FAILS at `J₁`** at `ΞA`, kept as a record. At today's kernel `LiveOK` holds at every effect context (D1). `LiveOK` needs the tie | `machShape_orow`, `handlerSem_orow`, `handlerSem_ourInst`, `catchLaw_ourInst`, `catch_unr_ourInst`, `catch_cell_ourInst`, `resumeCellLaw_ourInst`, `cancelCellLaw_ourInst`, `I.catchLaw_progT_cell`, `handlerSemNoCell_orow`, `not_handlerSemNoCell_J₁_ΞA`; `liveOK_tier1Open`, `status_machShape_handlerSem_tier1Open`; `liveOK_needs_tie` |
| `LiveOK` is met at a typing system that types one program with a handler, an operation it catches and a continuation | PROVED | `liveOK_JnLog` |
| S5 (`Cancellation noFinRaise`) at our instance, RESTATED (D3, D4; F3: prefix-closed; M3: under frame deadness, `pend` and the cell's cancel) | The bridges (`unwindOrder_of_core`, `noIntercept_of_core`, `cancellation_of_core`, from `LiveOK`, labels named nonzero, and each fired finaliser meeting the condition running to `()` from every finite memory) give, at `J₁` and today's kernel at every effect context, the unwind PROVED AT σ=[], the no-interception PROVED AT σ=[] given `CancelsNamed` (OPEN); no handler named `0` in a cancelled context PROVED AT σ=[] as a run invariant (no run of a typed program creates a handler named `0`), read by nothing: the cancel runs the dead region `K†` (SPEC §19). The extension a run needs is the β-step after a fire step, or nothing (`FireExt`). Read whole (kept as a record) S5 **FAILS** at every typing system that types `fireProg` and `(); ()`, at every effect context declaring `exn : 1 ↠ 0` at `1` (`ΞA` among them): the path of a fire step alone follows no unwind trace. The no-interception condition's teeth are OPEN: at `J₄` the cancelled finaliser performs the operation of the cancelled continuation's handler, which is dead, so the run stops at it and is a cancel trace at every set of endings | `status_cancellation_J₁`, `status_finOK`, `unwind_pfx`, `cancel_pfx`, `FireExt`, `cancelsNZ_J₁`, `hndNZ_reach`, `driveData_of_reach`, `unwindOrder_fireProg`, `not_unwindOrderWhole_of_types`, `not_cancellationWhole_ΞA`; `finAlone_dead` |
| Core's `FinaliserOrder` (I3.b) | PROVED, given `FinAloneAt FR` (a fired finaliser's run alone, platform-free, ends at a value or an uncaught raise of a name in `FR`), at today's endings (nonzero names) and at option A's (none). At a typing system with FL at Core's world, `FinAloneAt FR` follows from `FinRowsAt FR` (an operation the finaliser's run alone leaves uncaught is a raise of a name in `FR`): stuck redexes are excluded by FL and B2's runs. So at today's unr-free kernel `FinaliserOrder` follows from `FinRowsAt` alone (PROVED AT σ=[]). `FinRowsAt` OPEN: route 8.2's obligations (`RowRoute`) give it (PROVED), and no `RowRoute` is built (TIER1-PLAN §4: the review did not accept route 8.2). It is not on S5's bridges' route: decision D4 put the fired finalisers' typing into S5, and typing gives each such finaliser's run to `()` from every finite memory (`finOK_of_finRow`) | `finaliserOrder_at`, `finaliserOrder_A`, `finAloneAt_of_finRows`, `finaliserOrder_tier1NU_of_finRows`, `finaliserOrder_tier1NU_of_finRowsA`, `finRowsAt_of_route`, `finaliserOrder_of_route` |
| `FinAlone` (piece 1's added hypothesis) | RESTATED by D3: its consumer reads `FinAloneAt FR`, platform-free | — |
| S6 (`ContUseEv`) at our instance, RESTATED (decision S6: per capture event, on complete runs, at data answers) | OPEN at today's kernel; at `J₁` REDUCED to two ownership properties of the capture cell, `OnlyOwnerFrees` and `NoDanglingUse` (OPEN), given `LiveOK` and leak freedom (PROVED at `J₁`): a capture event allocates `κ`'s cell, a use releases it three steps later, a linear `κ`'s cancel is stuck | `status_contUseEv_J₁_of`, `contUseEv_of_cells`, `catchEv_cell`, `use_frees_cell`, `leakFree_of_coreClosed` |
| route 8.4 to S6: an obligation created at `[op]`, consumed where `κ` is resumed or cancelled, read by leak freedom at a run's end | the capture cell is that obligation (SPEC §25): R1 at a linear or affine operation is not in Core's relation at `F bool` (its run leaks `κ`'s cell); BoLo's world at the empty heap is the empty resource | `status_ghostCoupling`, `I.not_semC_R1`, `I.lower_empty_eq` |
| S6's tooth: R1 (RESTRUCTURE §6.1) at our machine | PROVED: every typing system over our machine that types R1 at `F 0 bool`, at a label whose first operation resumes and is linear or affine, fails S6; `JR` types it, and at `ΞA` the lemma applies. R2–R4 have no complete run at such an operation | `not_contUseEv_of_der_R1`, `not_contUseEv_of_der_R1_orow`, `teeth_JR_ΞA` |
| today's kernel types none of R1–R4 | PROVED, by the handler's form (our handler is the run-time frame, its clauses values; `[handle]` types clause variables). At the clauses, by the linearity of `κ` (RESTRUCTURE §6.1's reason): today's clause typing refuses R1's, R2's and R4's clauses at every resuming `lin` or `aff` operation (a live slot of `kTy` is neither dropped nor duplicated) and R3's at every `lin` one (a linear `κ`'s cancel is at `⊤`); at the clause type of a linear `1 ↠ 1`, where all four are refused, a clause that resumes `κ` once is typed, and `cancelCl` is typed at `aff` and refused at `lin`. At `unr` the argument does not apply (multi-shot is not considered) | `refuses_R_tier1Open`, `refuses_R_clauses`, `clauseRefusals_pinned` |
| `AlgLaw`, `TailLaw`, `EtaHold` at our instance, RESTATED (D4: data answers; F2: a finaliser's start observed but not its code) | `AlgLaw` **PROVED at `J₁` at every effect context given `CfinQuiet`** (no configuration a typed program reaches is at a `[cfin-raise]` step; option A; F4's `guard` frame is its route): the two sides run step for step alike, every term along the two runs related by `AlgRel` (the left's frames `□ to x. M`, `□ to y. N` against the right's `□ to x. (M to y. N)`, wherever a catch puts them), every rule of Core's machine stepping alike at related redexes, the left's inner β-step at `x to x. M` and the right's at `y to x. (M to y. N)` reaching `M[x] to y. N`; a typed program's runs are closed and go on, answer data and ask the runner at data. Not vacuous: at `algAffProg`'s configuration (`J₁`, `ΞA`) each side's complete runs answer `()` and show one finaliser's start, where `AlgLawCode` fails. `AlgLawCode` **FAILS AS WRITTEN at `J₁`** (kept as a record): `algAffProg`, typed by Core's kernel with every handler's and operation's row tied to `ΞA`, reaches the law's left side under a handler of the affine `wait` whose clause raises inside a finaliser frame; the finaliser cancels `κ` and handles the cancel's raises itself; the two runs answer `()` and show `fire` of finalisers that differ as terms, at every cell `κ`'s allocation picks. The round-2 witness `algFireProg` (an `unr` continuation held by a finaliser) is outside the tied kernel: its handled row is not tied to `ΞA`, no tied handler of `5` carries the tag `unr`, and the tied `J₁` at `ΞA` types it at no type. `TailLaw` OPEN: not proved, not refuted; it compares `fire D` by `D`'s code, as `AlgLawCode` does. `EtaHold` OPEN: `[handle]`'s `hnS` keeps a forwarding handler's own name out of its clauses' row, so by that reading no typed program installs one (not checked by an inversion); not proved | `I.algLaw_J₁_of`, `algLaw_of_good`, `algGood_of_coreClosed`, `AlgRel.head`, `ostep_sim`, `rstep_fwd`, `rstep_bwd`, `obsStartFrom_iff_rel`, `lamFree_answer_of_coreClosed`, `lamFree_io_of_coreClosed`, `algLaw_algAffProg`, `algAffProg_start`; `not_algLawCode_J₁`, `not_algLawCode_ΞA`, `d_algAffProg`, `finE_D2_ne`; `d_algFireProg`, `not_rowAt_R5`, `not_tied_hnd5_unr`, `not_der_algFireProg_J₁` |
| the tail-resumptive law and algebraicity at the answering class (a clause `λ(a, k). c a to b. k.resume b` whose code runs quietly) | PROVED at every typing system with `LiveOK`, so at `J₁`, at every operation: quietly when `κ` owns no cell, around its cell when it does | `calm_tailClause`, `quiet_tailClause`, `cellQuiet_tailClause`, `tailLaw_quiet`, `algLaw_quiet`, `I.tailLaw_quiet_J₁`, `I.algLaw_quiet_J₁` |
| runs around a capture cell: finite memories on every run from `init`; the allocation at every free location; calm runs compose, go under contexts and keep the complete runs' answers and traces | PROVED | `finDom_reach`, `obsFrom_alloc_iff`, `obsFrom_mstep_iff`, `obsFrom_calm_iff`, `runsAlike_of_calm`, `kappaC_resume_parts` |
| D1.h4 (c), the comodel reduction: co-operations that run quietly (`PureCo`) and form a comodel give a correct handler | PROVED at every typing system with `LiveOK` whose typed closed values are closed | `ansCorrect_of_comodel`, `calm_fold`, `calm_opStep`, `calm_side`, `quiet_coFrom` |
| global state: `stateCo` a comodel of the four laws, its handler correct; not vacuous | PROVED (at `J₁`: `I.state_correct_J₁`); at `J₁` and the admissible `Ξst`, the handler whose `put` keeps the old state fails the update–lookup law at a typed program, and its co-operations are no comodel | `state_isComodel`, `state_correct`, `I.state_correct_J₁`, `not_ansCorrect_badState`, `not_isComodel_badState`, `admEff_Ξst` |
| `LetLaw` at today's kernel | PROVED (typing) | `letLaw_ourInst_tier1Open` |
| S1 (`RowAlgebra`) at our instance, RESTATED (D6: `SubClosed` at a well-formed target row) | PROVED at today's kernel, at every effect context with no resuming `unr` operation, the admissible ones among them; `EA.Laws`, `EA.Safe` and `RowSig` at every typing system. The premise is needed | `rowAlgebra_ourInst_tier1Open`, `rowAlgebra_noSub_ourInst`, `subClosed_nu_tier1Open`, `rowNU_of_wf`; `subClosed_needs_wf` |
| A-level handlers at today's kernel | **NOT TYPED** by `tier1Open` (the kernel's fragment without SPEC §24's rules): our instance's `handle` is the run-time frame, clauses as values; the fragment's `[handle]` types only `hndTerm n ir ic e`. So E4, E5, E6, E7 and E8 **FAIL** at `tier1Open` at every effect context.  Core's `[handle]` (§24) types the frame form, and so does `J₁`; the (E) properties at `J₁` are the row below | `not_der_handleK`, `not_der_handle_tier1Open`, `status_handlers_tier1Open` |
| a let-bound function used at two rows; a persistent function called at an effectful row | **NOT TYPED** by today's kernel: one slot has one type, of which every judgement a variable is read at is a view; a variable used as a function is a `U` slot | `not_der_letTwo`, `der_var_inv`, `der_var_arr_thunk`, `not_der_callBang` |
| `Safety` (S2), `EffSafe` (S3), `LiveOK` at our instance | PROVED AT σ=[] at today's kernel, every effect context (D1): a run under a runner is the run under the platform it gives (`platformOf`), step for step from a typed program, and B2's runs give A's. The tie is needed | `safety_ourInst_tier1Open`, `effSafe_ourInst_tier1Open`, `liveOK_tier1Open`; `safety_needs_tie`, `liveOK_needs_tie` |
| `DataDiv` at our instance | PROVED (every row form, effect context and typing system) | `dataDiv_ourInst` |
| `J₁`, `Pins J₁`, the let law and S1 at `J₁` | BUILT; PROVED AT σ=[] (S1 at every effect context: Core's `[sub]` asks nothing of its rows); our instance reads `J₁` at an effect context with its handlers' and operations' rows tied to it (decision R): Core's tied kernel `CDerivesAt Ξ` at tied row environments, every tied derivation Core's, a tied handler's tags a prefix of the context's | `Inst.J₁`, `status_pins_J₁`, `status_sPropsNoCancel_J₁`, `status_innerTie` |
| A's (E) properties at `J₁` (decision E) | `EProps` **FAILS AS WRITTEN** at every effect context: E7, E8, E9 (option A).  PROVED at every admissible effect context: E1, E4, E6; E5 where no `exn` signature is `unr`; E2's fourth program (E2d) where no operation is `unr`; E10's `timeout` (typed once, its schema, its call).  NOT DERIVED, no obstruction verified: E2a–E2c and E10's `retry` (a function at `!U C` forced; Core's `force` reads a `U C` slot); E3 and E10's loop (`unfold`'s stepped value `etaN`, which no rule types).  The callbacks by SPEC §26's `[λ-dead]`; weakening by an unused live slot not derived | `status_eProps_J₁`, `noColouring_J₁`, `deepHandler_J₁`, `tunnel_J₁`, `nestedHandlers_J₁`, `e2d_J₁`, `higherOrderPoly_e2d_J₁`, `derV_timeoutR_J₁`, `polyUseOpen_timeoutR_J₁`, `callsThrough_timeoutR`, `not_eProps_J₁`, `lamDead_compatC` |
| `RowVarKernel J₁` | NOT PROVED, not attempted.  `[allR-I]` at `J₁` reads a value judgement at `U C` as Core typing the λ at `C`, an inversion of Core's thunk rules; not derived, and no obstruction is verified | — |
| `monoCallback_tier1Open` (today's kernel fails E1, E2, E6, E10); the positive (E) runs at `tier1Open` | OPEN (inversions and runs to build, RESTRUCTURE §6.1) | — |
| `RowVarKernel J₂`, `spanRules_J₂` | OPEN (`J₂` not built) | — |
| A₂ over Core (`Laws`, `Abstraction`), A₃'s lowering classes | stated, out of the first pass | `Targets/Instance/Binary.lean`, `Targets/Instance/ZeroCost.lean` |

## The step-index audit (finding #6)

`coreW`'s report (`Targets/Audit.lean`, pinned): report 1, `Cell` (`WellFounded.fix`: the
stratification by lifetime decision 7 keeps), `sepRange`, `tabFill`, `dropFill` and their
auxiliaries (recursion on an array's length), and the matchers `clauseAt.match_1`,
`VTy.upR.match_1`, `capTag.match_1` and `capTag._sparseCasesOn_5` (a clause's index, a de Bruijn
index, an operation's index into its handler's tag list: data); report 2, `AHead`, `ARun` (index `ℕ`:
the allocator's allocation count, never decremented, which selects the allocator's location), and,
via `Loc` only, `Head`, `Chain`, `GPos`, `LinPath`, `MutPos`, `RefPos`, `TW` (heaps, resources,
locations: names); report 3, `Table`, `ewpTS`, `vCE._f` (their `∀`-bound predicates range over
lend records, `List SRec`, whose `Life` is a lifetime) and `cancelOK` (its `∀`-bound predicate is
the cancel obligation an entry carries, SPEC §27, read at lend records); report 5 (a), `AHead.alloc`, `AHead.tab`
(the allocation count).  Reports 4 and 5 (b): none.  The nine negative tests pass, each at its own
entry.

## Retired and restated (nothing silently dropped)

* `EndStateAt`, `EndState`, `Guarantees` (the library's), `Tier1End`, `EndStateBinder`: restated
  as `I.Combined`, done, `B.Guarantees`, `I.Tier1` (with `I.Tier1Core`) and `I.CombinedBinder`.
* `status_tier1End_of` (`Adequate coreW → FinaliserOrder tier1 → Tier1End`): **retired**.  Its
  conjuncts `EffSafe`, `NoInterception` and `FinaliserOrder` became A's properties at our instance,
  which need the bridges, and B5 now has content, which B4′ gives through the step-for-step
  simulation.  Its proved content is kept: `status_tier1Core_world`, `status_tier1Core_B`,
  `status_tier1Core_guarantees`.
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
* `not_algLaw_J₁` at `J₁` before decision R (its inner judgements untied), with the witness
  `algFireProg` and its runs (`alg_c`, `algL_q`, `algR_q`, `obs_algL`, `obs_algR`, `finE_DL_ne`):
  **not kept**.  The witness's handler of `5` is at `unr` where `ΞA` declares `tick` linear, which
  the tie excludes (`not_rowAt_R5`, `not_tied_hnd5_unr`): the tied `J₁` at `ΞA` types the witness at
  no type (`not_der_algFireProg_J₁`).  `algFireProg` and its typing by Core's kernel
  (`d_algFireProg`) stay.
* Algebraicity observing a finaliser's code (the statement before fix-up F2): **kept** as
  `AlgLawCode`, with its refutation at the tied `J₁` by `algAffProg` (`not_algLawCode_J₁`,
  `not_algLawCode_ΞA`; formerly `not_algLaw_J₁`, `not_algLaw_ΞA`) and at `toy`
  (`not_algLawCode_toy`).  `AlgLaw` is restated with a finaliser's start observed but not its code
  (fix-up F2, above).
* S4's statement before the capture cell (every catch hands `capture l H K` and keeps the store):
  **kept** as S4 with no cell, `HandlerSemNoCell`, with its refutation at `J₁` and `ΞA` (`not_handlerSemNoCell_J₁_ΞA`, from
  `not_pureJoin_progT`) and its proof where resuming operations are unrestricted
  (`handlerSemNoCell_orow`).  S4 is restated at the capture cell (fix-up F1, above).  The earlier
  S4 proofs are split into one theorem per law, the laws that read no cell shared by both
  statements (`retLaw_ourInst` … `finLaw_ourInst`).
* S5 read whole (every run from a cancel's or an unwind's start a trace): **kept** as
  `CancellationWhole` (`NoInterceptWhole`, `UnwindOrderWhole`), with its refutation at `J₁`, today's
  kernel and `ΞA` (`not_unwindOrderWhole_of_types`, `not_cancellationWhole_J₁`,
  `not_cancellationWhole_tier1Open`, `not_cancellationWhole_ΞA`,
  `not_cancellationWhole_admissible`).  S5 is restated prefix-closed (fix-up F3, above).
* Check 2's derivations (`d_thenProgNU`, `d_prog₃TNU`, `d_thenRaiseProgNU`, `d_unwindProgNU`):
  **removed** with D3's kernel half.  Their finalisers let a raise escape, which option A excludes
  (SPEC §24); the programs stay (`Instance/CheckPrograms.lean`).
* `Targets/Checks/RunEnd.lean` (untracked, not imported): **deleted**, superseded: each of its 17
  theorems has a same-named successor in `Targets/I/RunEnd.lean`, restated against the field `Upd`.
* `noIntercept_needs_finRow` and `status_noIntercept_needs_finRow` (S5's no-interception condition
  needed, at `J₄`): **retired** with frame deadness.  Its witness's finaliser performed the
  operation its region's handler caught, and that handler is dead during the cancel; the run now
  stops at the operation and is a cancel trace at every set of endings (`finAlone_dead`,
  `status_finAlone_dead`).
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

/-- PROVED AT σ=[], given S4 and S5 at today's kernel: the restricted tier-1 reduction. -/
theorem status_tier1Core_of
    (hS4 : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).HandlerSem)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise) : I.Tier1Core (ℍ := ℍ) :=
  I.tier1Core_of hS4 hC

/-- PROVED AT σ=[], given S5 at today's kernel: the restricted tier-1 reduction; S4 holds there at
every effect context. -/
theorem status_tier1Core_of_S5
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise) : I.Tier1Core (ℍ := ℍ) :=
  I.tier1Core_of_S5 hC

/-- PROVED AT σ=[]: A's properties at today's kernel but S4, S5 (and S6, which the restricted
reduction does not hold), at every admissible effect context.  S4 at
`status_machShape_handlerSem_tier1Open`. -/
theorem status_sPropsNoCancel_tier1Open {Ξ : EffCtx} (hΞ : AdmEff Ξ) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).LetLaw ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RowAlgebra ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).DataDiv ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).EffSafe :=
  I.sPropsNoCancel_tier1Open hΞ

/-- PROVED AT σ=[]: B's guarantees at today's kernel but B5 — B0, B1, B2, B3 and B4, B4′, B6, B7
and the bounds. -/
theorem status_tier1Core_B :
    B.ExtendsB tier1Open.read ∧ FL (B.coreB (ℍ := ℍ)) tier1Open.read ∧
      Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧ Sound (ℍ := ℍ) tier1Open.read ∧
      B.SoundContracts (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧
      LifetimeSound (B.coreB (ℍ := ℍ)) tier1Open.read.out ∧ B.WBound (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_B

/-- PROVED AT σ=[]: B5 at today's kernel and BoLo. -/
theorem status_releasedOnceReuse_tier1Open :
    B.ReleasedOnceReuse (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_releasedOnceReuse

/-- PROVED AT σ=[]: B's guarantees at today's kernel, B5 included. -/
theorem status_tier1Core_guarantees : B.Guarantees (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_guarantees

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

/-- PROVED (generic): B5 from B4′, through the step-for-step simulation. -/
theorem status_releasedOnceReuse_of_soundContracts {J : TypingJ} {M : B.BWorld}
    (hC : B.SoundContracts (ℍ := ℍ) J M) : B.ReleasedOnceReuse (ℍ := ℍ) J M :=
  releasedOnceReuse_of_soundContracts hC

/-- PROVED: the step-for-step simulation at the configurations a bump run reaches (OQ-43 (b)). -/
theorem status_bumpSimAt : BumpSimAt (ℍ := ℍ) := bumpSimAt

/-- PROVED: every run of a program safe under the platform restricted to data arguments asks the
platform at data arguments only. -/
theorem status_platData_of_safe {P : Platform} {A : VTy} {e : Expr}
    (hS : SafeRuns (ℍ := ℍ) P.restrict A e) :
    ∀ c, PSteps (ℍ := ℍ) P (init P e) c → PlatData P c :=
  fun c hc => (platData_of_safe hS c hc).1

/-- Not proved, and not used: the step-for-step simulation over every related configuration,
whose hypotheses carry none of the invariants a bump run keeps (`BumpSimAt` adds them). -/
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

/-- PROVED AT σ=[], given `LiveOK`: S0 and S4 at our instance, at every typing system and effect
context, S4 at the capture cell (a linear or affine operation's catch allocates `κ`'s cell, SPEC
§25); S4 with no cell at an effect context whose resuming operations are unrestricted
(`CatchUnr`), where every catch hands `capture` and keeps the store. -/
theorem status_machShape_handlerSem (Ξ : EffCtx) (J : OurTyping orowRF)
    (hL : Inst.LiveOK (ℍ := ℍ) orowRF Ξ J) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ J).HandlerSem ∧
      (Ξ.CatchUnr → (ourInst (ℍ := ℍ) orowRF Ξ J).HandlerSemNoCell) :=
  ⟨Inst.machShape_orow hL, Inst.handlerSem_orow hL, Inst.handlerSemNoCell_orow hL⟩

/-- PROVED AT σ=[]: `LiveOK`, so S0 and S4, at today's kernel at every effect context (D1); S4 with no
cell there at an effect context whose resuming operations are unrestricted. -/
theorem status_machShape_handlerSem_tier1Open (Ξ : EffCtx) :
    Inst.LiveOK (ℍ := ℍ) orowRF Ξ tier1Open ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).MachShape ∧
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).HandlerSem ∧
      (Ξ.CatchUnr → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).HandlerSemNoCell) :=
  ⟨Inst.liveOK_tier1Open, Inst.machShape_orow Inst.liveOK_tier1Open,
    Inst.handlerSem_orow Inst.liveOK_tier1Open, Inst.handlerSemNoCell_orow Inst.liveOK_tier1Open⟩

/-- PROVED: a cancel runs its region dead (SPEC §19, decision D1 of 2026-10-08).  A typing system
that types one program with no `ccatch`, no `cfin` and no handler named `0` reaches a cancel whose
region's finaliser performs the operation of the handler whose continuation is cancelled; that
finaliser meets `FinRow` at no set of endings.  The cancel runs the region with that handler
removed: the finaliser fires and starts, its operation meets no frame that catches it, and the run
stops there, a cancel trace of the region's one action at every set of endings. -/
theorem status_finAlone_dead {Ξ : EffCtx} (h2 : Ξ 2 = [(.unr, .unit, .unit)]) :
    NoInterception Inst.J₄.read ∧
      (∀ FR, ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).FinRow FR Inst.finP) ∧
      (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).RPath (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).R₀
        ((Adequacy.emptyMem, lookEnd 8 Inst.finAloneProg), ()) (Inst.p5q (ℍ := ℍ) Ξ) ∧
      (∀ ev c', ¬ (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).RStep (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).R₀
        ((Adequacy.emptyMem, Inst.p5Kf.plug Inst.finP), ()) ev c') ∧
      (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).acts Inst.p5K = [.fire Inst.finP] ∧
      ∀ FR, (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).CancelTrace (ourInst (ℍ := ℍ) orowRF Ξ Inst.J₄).R₀ FR
        .hole ((Adequacy.emptyMem, lookEnd 8 Inst.finAloneProg), ()) [.fire Inst.finP] none
        (Inst.p5q (ℍ := ℍ) Ξ) :=
  let h := Inst.finAlone_dead (ℍ := ℍ) Ξ h2
  ⟨h.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- PROVED, given `FinAloneAt` at today's endings or at option A's: Core's `FinaliserOrder`. -/
theorem status_finaliserOrder_of {J : TypingJ} :
    (FinAloneAt (ℍ := ℍ) (· ≠ 0) J → FinaliserOrder (ℍ := ℍ) J) ∧
      (FinAloneAt (ℍ := ℍ) (fun _ => False) J → FinaliserOrder (ℍ := ℍ) J) :=
  ⟨finaliserOrder_at, finaliserOrder_A⟩

/-- PROVED: what a typed program does at run time, at today's kernel.  `LiveOK` holds at every
effect context, and needs the tie; `FinaliserOrder` at today's unr-free kernel follows from
`FinRowsAt` alone, at today's endings and at option A's; route 8.2's obligations give `FinRowsAt`
at every typing system with FL at Core's world. -/
theorem status_runTyping :
    (∀ Ξ, Inst.LiveOK (ℍ := ℍ) orowRF Ξ tier1Open) ∧
      (AdmEff Inst.ΞA ∧ ¬ RowAt Inst.ΞA Inst.Slv ∧ ¬ Inst.GoesOn (ℍ := ℍ) orowRF Inst.ΞA Inst.lvStuck) ∧
      (FinRowsAt (ℍ := ℍ) (· ≠ 0) tier1NU → FinaliserOrder (ℍ := ℍ) tier1NU) ∧
      (FinRowsAt (ℍ := ℍ) (fun _ => False) tier1NU → FinaliserOrder (ℍ := ℍ) tier1NU) ∧
      ∀ J : TypingJ, RowRoute (ℍ := ℍ) J → FL (B.coreB (ℍ := ℍ)) J →
        FinaliserOrder (ℍ := ℍ) J :=
  ⟨fun _ => Inst.liveOK_tier1Open,
    ⟨Inst.liveOK_needs_tie.1, Inst.liveOK_needs_tie.2.2.1, Inst.liveOK_needs_tie.2.2.2.2.2.1⟩,
    finaliserOrder_tier1NU_of_finRows, finaliserOrder_tier1NU_of_finRowsA,
    fun _ hr hFL => finaliserOrder_of_route hr hFL⟩

/-- PROVED: S6's tooth.  At the open-row form, a typing system that types R1 at `F 0 bool`, at a
label whose first operation resumes and is linear or affine, fails S6; `JR` types R1 at the affine
`wait` of `ΞA` and fails S6; today's kernel types none of R1–R4, by the handler's form. -/
theorem status_contUse_teeth {Ξ : EffCtx} {J : OurTyping orowRF} (l : (orowAlg Ξ).Lab)
    {q : Qual} {qs : List Qual} (hqs : Inst.qsL (RF := orowRF) (Ξ := Ξ) l = q :: qs) (hq : q ≠ .unr)
    {o : A.OpSig Inst.OVTy} (ho : ((ourInst (ℍ := ℍ) orowRF Ξ J).sig l)[0]? = some o)
    (hk : o.cls ≠ .abortive) :
    ((ourInst (ℍ := ℍ) orowRF Ξ J).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ J).withCl l (ourInst (ℍ := ℍ) orowRF Ξ J).dropCl)
        ((ourInst (ℍ := ℍ) orowRF Ξ J).F (orowAlg Ξ).unit (ourInst (ℍ := ℍ) orowRF Ξ J).bool) →
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).ContUseEv) ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA Inst.JR).ContUseEv ∧
    ∀ C, ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).dropCl) C :=
  ⟨Inst.not_contUseEv_of_der_R1_orow l hqs hq ho hk, Inst.teeth_JR_ΞA.2.2.2,
    fun C => (Inst.refuses_R_tier1Open l C).1⟩

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

/-- PROVED: decision R.  Our instance at `Ξ` reads `J₁` at `Ξ`, its handlers' and operations' rows
tied to `Ξ`; a tied derivation is one of Core's; a tied handler's signature is a prefix of the
context's; `J₁`'s reading, which B and the pins read, is Core's whole kernel. -/
theorem status_innerTie :
    (∀ Ξ, ourInst (ℍ := ℍ) orowRF Ξ J₁ =
      ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (Inst.J1DerAt Ξ))) ∧
      (∀ Ξ Δ Γ e j, CDerivesAt Ξ Δ Γ e j → CDerives Δ Γ e j) ∧
      (∀ (Ξ : EffCtx) (n : UInt32) (E : List (Qual × VTy × VTy)) (S : Row),
        RowAt Ξ (Row.ofEff n E 0 ++ S) → E.length ≤ 2 ^ 32 → E <+: Ξ n) ∧
      J₁.read = tier1 :=
  ⟨fun Ξ => Inst.ourInst_J₁ Ξ, fun _ _ _ _ _ h => h.toCDerives,
    fun _ _ _ _ h hl => sig_prefix_of_rowAt h hl, Inst.j1_read⟩

/-- PROVED AT σ=[]: B's guarantees at `J₁`, B5 included. -/
theorem status_guarantees_J₁ : B.Guarantees (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ)) :=
  I.guarantees_J₁

/-- PROVED AT σ=[] (abortive rows): `Pins` at `J₁`. -/
theorem status_pins_J₁ : I.Pins J₁ admClosedOp .abortive := I.pins_J₁

/-- PROVED AT σ=[]: A's (S) properties at `J₁` but S5 and S6, at every effect context, S4 at the
capture cell. -/
theorem status_sPropsNoCancel_J₁ (Ξ : EffCtx) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).LetLaw ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).RowAlgebra ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).DataDiv ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).EffSafe ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem :=
  ⟨I.sPropsNoCancel_J₁.1, I.sPropsNoCancel_J₁.2.1, I.sPropsNoCancel_J₁.2.2.1,
    I.sPropsNoCancel_J₁.2.2.2.1, I.sPropsNoCancel_J₁.2.2.2.2.1, I.sPropsNoCancel_J₁.2.2.2.2.2,
    I.handlerSem_J₁⟩

/-- PROVED: tier 1 at `J₁` follows from A's (E) properties, S4, S5 and S6 at every admissible
effect context, and the composite's programs and rejections. -/
theorem status_tier1_J₁_of
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hS4 : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv)
    (hAc : I.Accepts (ℍ := ℍ) J₁.read .abortive) (hRj : Rejects J₁.read) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of hE hS4 hC hU hAc hRj

/-- PROVED AT σ=[] (decision AR): the composite's programs at `J₁`, each typed, safe, terminating and
with a computed complete run answering the stated value; and its rejections, AT05, AT06, AT08 and
AT13, typed at no type by Core's kernel, nor by the tied kernel at any effect context.  AT08's
rejection rests on `load` having no rule. -/
theorem status_acceptsRejects_J₁ :
    I.Accepts (ℍ := ℍ) J₁.read .abortive ∧ Rejects J₁.read ∧
      (∀ (Ξ : EffCtx) (Δ : BoCa.Lifetime.LifeCtx) (Γ : Ctx VTy) (j : Jdg),
        ¬ CDerivesAt Ξ Δ Γ at05 j ∧ ¬ CDerivesAt Ξ Δ Γ at06 j ∧ ¬ CDerivesAt Ξ Δ Γ at08 j ∧
          ¬ CDerivesAt Ξ Δ Γ at13 j) ∧
      ∀ (Δ : BoCa.Lifetime.LifeCtx) (Γ : Ctx VTy) (X : Expr) (j : Jdg),
        ¬ CDerives Δ Γ (.app (.prim .load) X) j :=
  ⟨I.accepts_J₁, I.rejects_J₁, fun Ξ _ _ _ => I.rejects_tied Ξ, fun _ _ _ _ => Rej.not_der_load_app⟩

/-- PROVED: tier 1 at `J₁` follows from A's (E) properties, S4, S5 and S6 at every admissible
effect context (decision AR discharges `Accepts` and `Rejects`). -/
theorem status_tier1_J₁_of_ESU
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hS4 : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of_ESU hE hS4 hC hU

/-- PROVED: tier 1 at `J₁` follows from A's (E) properties, S5 and S6 at every admissible effect
context: S4 is proved at every effect context (`I.handlerSem_J₁`), and `Accepts` and `Rejects`
(decision AR). -/
theorem status_tier1_J₁_of_ECU
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of_ECU hE hC hU

/-- **FAILS AS WRITTEN**: tier 1 at `J₁`.  Its A conjunct asks A's (E) properties at every
admissible effect context, and E7, E8 and E9 fail at `J₁` at every effect context under option A.
S5 read whole fails too, at the admissible `ΞA` (kept as a record); S5 is read prefix-closed
(fix-up F3), restated under frame deadness (M3), and holds given `CancelsNamed`
(`status_cancellation_J₁`). -/
theorem status_tier1_J₁ :
    ¬ I.Tier1 (ℍ := ℍ) J₁ ∧ ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).EProps ∧
      ¬ (∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).CancellationWhole
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise) :=
  ⟨I.not_tier1_J₁, Inst.not_eProps_J₁, I.not_cancellationWhole_admissible⟩

/-- PROVED: tier 1 at `J₁` follows from A's (E) properties, `CancelsNamed` (every cancelled
continuation's running finalisers hold kept errors of labels' names) and S6 at every admissible
effect context: S4 is proved, S5 is proved but `CancelsNamed` (M3), and `Accepts` and `Rejects`
(decision AR). -/
theorem status_tier1_J₁_of_ENU
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hN : ∀ Ξ, AdmEff Ξ → Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ J₁)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of_ENU hE hN hU

/-- PROVED (decision E): A's (E) properties at `J₁`.  At every admissible effect context E1, E4 and
E6, and E5 where no `exn` signature is `unr`; E7, E8 and E9 fail as written at every effect context
(option A), and so `EProps`, and with it the (E) hypothesis of `status_tier1_J₁_of`. -/
theorem status_eProps_J₁ {Ξ : EffCtx} (hΞ : AdmEff Ξ) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).NoColouring ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).DeepHandler ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).Tunnel ∧
      (Inst.NoUnrExn Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).NestedHandlers) ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).CancelPolicy ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).UnwindPolicy ∧ ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).StoredK ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps :=
  ⟨Inst.noColouring_J₁ hΞ, Inst.deepHandler_J₁ hΞ, Inst.tunnel_J₁ hΞ, Inst.nestedHandlers_J₁ hΞ,
    Inst.not_cancelPolicy_J₁, Inst.not_unwindPolicy_J₁, Inst.not_storedK_J₁, Inst.not_eProps_J₁⟩

/-- PROVED (decision E): the hypotheses of E2d and E5 are met at the admissible `ΞA`. -/
theorem status_noUnr_ΞA : AdmEff Inst.ΞA ∧ Inst.NoUnr Inst.ΞA ∧ Inst.NoUnrExn Inst.ΞA :=
  ⟨Inst.admEff_ΞA, Inst.noUnr_ΞA, Inst.noUnrExn_ΞA⟩

/-- PROVED: route 8.4's obligation, at the capture cell.  R1 at a linear or affine operation is not
in Core's relation at `F bool`: its run leaks `κ`'s cell, and Core's relation at a returner ends every
run at the empty memory; BoLo's world at the empty heap is the empty resource. -/
theorem status_ghostCoupling :
    (∀ (n : UInt32) (q : Qual) (qs : List Qual), q ≠ .unr →
      ¬ SemC BoCa.Lifetime.LifeCtx.empty [] (Inst.rProg n (q :: qs) Inst.dropV) (.ret Inst.boolT)) ∧
      (∀ ρ : WRes, ResU.Lower ρ Adequacy.emptyMem → ρ = PMap.empty) :=
  ⟨fun n _ qs hq => I.not_semC_R1 (ℍ := ℍ) n qs hq, fun _ h => I.lower_empty_eq h⟩

/-- **PROVED AT σ=[]** (fix-up F1): S4, restated at the capture cell, at `J₁` at every effect
context; not vacuously, its catch law holding at the catch of `ΞA`'s linear `tick` by the cell
alone.  S4 with no cell fails at the admissible `ΞA` (the witness is Core's handled program at the
linear `tick`), and is kept as a record.  At every instance with no cells the two agree, and S4 fails
at an instance whose `handle` ignores its clauses. -/
theorem status_handlerSem_cell :
    (∀ Ξ, (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem) ∧
      (AdmEff Inst.ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).HandlerSemNoCell) ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).PureJoin (Adequacy.emptyMem, lookEnd 2 Inst.progT)
        ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).setT (Adequacy.emptyMem, lookEnd 2 Inst.progT)
          ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).plug .hole ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).app
            ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).force ⟨Inst.clT, .lam⟩)
            ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).pair (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).unitV
              ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).capture Inst.lab5A
                ((ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).hnd ⟨Inst.hrT, .lam⟩ [⟨Inst.clT, .lam⟩])
                .hole))))) ∧
      (∀ S : A.EffectSystem, IsEmpty S.Cell → (S.HandlerSem ↔ S.HandlerSemNoCell)) ∧
      (∀ bd : Bool → Bool → Bool, ¬ (A.toy id bd).HandlerSem) :=
  ⟨fun _ => I.handlerSem_J₁, ⟨Inst.admEff_ΞA, Inst.not_handlerSemNoCell_J₁_ΞA⟩,
    I.catchLaw_progT_cell.2.2.2.1, fun S hC => S.handlerSem_iff_noCell hC,
    fun _ => A.EffectSystem.not_handlerSem_toy⟩

/-- **PROVED AT σ=[]**: S4's laws at a cell are not vacuous at `J₁`.  At every effect context with a
`yield` and a `tick` label, `deepGen` (E4) reaches the clause's resume of `κ` at its cell, the memory
holding the cell; at every one declaring `exn` at `1` and `wait` at `2`, `algAffProg` reaches its
finaliser's cancel of the affine `κ` at its cell — each a configuration at which every premise of
the law holds. -/
theorem status_cellLaws_J₁ :
    (∀ (Ξ : EffCtx) (ly lt : (orowAlg Ξ).Lab), Ξ ly.1 = [(.aff, Inst.boolT, .unit)] →
      Ξ lt.1 = [(.lin, .unit, .unit)] → ly.1 ≠ lt.1 →
      ∃ c ℓ K₀ H K w, (ourInst (ℍ := ℍ) orowRF Ξ J₁).cellFree c ℓ ∧
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).Live ((ourInst (ℍ := ℍ) orowRF Ξ J₁).withCell c ℓ) ∧
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).term ((ourInst (ℍ := ℍ) orowRF Ξ J₁).withCell c ℓ) =
          (ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K₀ ((ourInst (ℍ := ℍ) orowRF Ξ J₁).resume
            ((ourInst (ℍ := ℍ) orowRF Ξ J₁).captureAt .affine ly H K ℓ) w)) ∧
    (∀ (Ξ : EffCtx), Ξ 1 = Inst.Eab → ∀ (h2 : Ξ 2 = Inst.Ew),
      ∃ c ℓ K₀ H K, (ourInst (ℍ := ℍ) orowRF Ξ J₁).cellFree c ℓ ∧
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).Live ((ourInst (ℍ := ℍ) orowRF Ξ J₁).withCell c ℓ) ∧
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).term ((ourInst (ℍ := ℍ) orowRF Ξ J₁).withCell c ℓ) =
          (ourInst (ℍ := ℍ) orowRF Ξ J₁).plug K₀ ((ourInst (ℍ := ℍ) orowRF Ξ J₁).cancel
            ((ourInst (ℍ := ℍ) orowRF Ξ J₁).captureAt .affine (Inst.labWait Ξ h2) H K ℓ))) :=
  ⟨fun _ _ _ hly hlt hne => Inst.resumeCell_deepGen hly hlt hne,
    fun Ξ h1 h2 => Inst.cancelCell_algAffProg Ξ h1 h2⟩

/-- PROVED AT σ=[]: what typing gives about a fired finaliser that meets S5's no-interception
condition at option A.  A program in Core's relation at `F 1` runs to `()` from every finite memory;
at `J₁` and at today's kernel, at every effect context, such a finaliser does. -/
theorem status_finOK :
    (∀ (e : Expr), cC (ℍ := ℍ) (CTy.effOf [] .unit) [] BoCa.Lifetime.LSub.empty e PMap.empty →
      ∀ μ, FinDom μ → Inst.FinOK (ℍ := ℍ) μ e) ∧
    (∀ (Ξ : EffCtx) (D : Expr), (ourInst (ℍ := ℍ) orowRF Ξ J₁).FinRow
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise D → ∀ μ, FinDom μ → Inst.FinOK (ℍ := ℍ) μ D) ∧
    (∀ (Ξ : EffCtx) (D : Expr), (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).FinRow
      (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise D → ∀ μ, FinDom μ →
        Inst.FinOK (ℍ := ℍ) μ D) :=
  ⟨fun _ h _ hμ _ _ hs => runs_of_rel_unit h hμ hs, fun _ _ h _ hμ => I.finOK_J₁ h hμ,
    fun _ _ h _ hμ => I.finOK_of_finRow (D := Inst.tier1OpenDer) Inst.coreClosed_tier1Open h hμ⟩

/-- **PROVED AT σ=[]** (fix-up F3, M3): S5, read prefix-closed and restated under frame deadness, at
`J₁` and at today's kernel, at every effect context: the unwind outright, the no-interception given
`CancelsNamed` (every cancelled continuation's running finalisers hold kept errors of labels' names;
OPEN, a syntactic run invariant); no handler named `0` in a cancelled context is a run invariant
(`cancelsNZ_J₁`, `cancelsNZ_tier1Open`), read by nothing since a cancel runs its region dead.  Read
whole (kept as a record), S5 fails at the admissible `ΞA`; at the witness's configuration S5 holds,
the β-step after the fire step appended. -/
theorem status_cancellation_J₁ :
    (∀ Ξ, (ourInst (ℍ := ℍ) orowRF Ξ J₁).UnwindOrder (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise) ∧
      (∀ Ξ, Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ J₁ →
        (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise) ∧
      (∀ Ξ, Inst.CancelsNZ (ℍ := ℍ) orowRF Ξ J₁) ∧
      (∀ Ξ, (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).UnwindOrder
        (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise) ∧
      (∀ Ξ, Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ tier1Open →
        (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).NoIntercept
          (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).noFinRaise) ∧
      (∀ Ξ, Inst.CancelsNZ (ℍ := ℍ) orowRF Ξ tier1Open) ∧
      AdmEff Inst.ΞA ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).CancellationWhole
        (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).noFinRaise ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA tier1Open).CancellationWhole
        (ourInst (ℍ := ℍ) orowRF Inst.ΞA tier1Open).noFinRaise ∧
      ∃ q', (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).UnwindTrace (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).R₀
        (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).noFinRaise I.fireK₀
        ((Adequacy.emptyMem, lookEnd 2 I.fireProg), ()) (Inst.thenK (.var 0) I.finSeq)
        ([(.fire I.finSeq, ((Adequacy.emptyMem, I.fireAfter), ()))] ++ q') :=
  ⟨fun _ => I.unwindOrder_J₁, fun _ => I.cancellation_J₁_of, fun _ => I.cancelsNZ_J₁,
    fun _ => I.cancellation_tier1Open.1, fun _ => I.cancellation_tier1Open.2,
    fun _ => I.cancelsNZ_tier1Open, Inst.admEff_ΞA, I.not_cancellationWhole_ΞA,
    I.not_cancellationWhole_tier1Open (by simp [Inst.ΞA]),
    (I.unwindOrder_fireProg (by simp [Inst.ΞA])).imp fun _ h => h.2⟩

/-- PROVED AT σ=[]: leak freedom at `J₁`, and S6 at `J₁` from the capture cell's two ownership
properties (OPEN). -/
theorem status_contUseEv_J₁_of :
    (∀ Ξ, Inst.LeakFreeAt (ℍ := ℍ) Ξ J₁) ∧
    ((∀ Ξ, AdmEff Ξ → Inst.OnlyOwnerFrees (ℍ := ℍ) Ξ J₁) →
      (∀ Ξ, AdmEff Ξ → Inst.NoDanglingUse (ℍ := ℍ) Ξ J₁) →
      ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :=
  ⟨fun _ => I.leakFreeAt_J₁, I.contUseEv_J₁_of⟩

/-! ## Piece 5: the answering class -/

/-- Algebraicity at `J₁`, its inner rows tied, at the admissible effect context `ΞA`.  **Observing a
finaliser's code, it FAILS AS WRITTEN** (kept as a record): the witness is typed by Core's kernel
with its handlers' and operations' rows tied to `ΞA`, and its two sides fire finalisers that differ
as terms at every pair of cells.  **As restated (fix-up F2), the witness's configuration meets it**:
under every runner each side's complete runs answer `()` and show one finaliser's start, read
without its code.  The round-2 witness, typed by Core's kernel, handles `5` at a row not tied to
`ΞA`; no tied handler of `5` carries the tag `unr`, and the tied `J₁` at `ΞA` types the witness at
no type. -/
theorem status_unaryLaws :
    (AdmEff Inst.ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).AlgLawCode) ∧
      CDerivesAt Inst.ΞA BoCa.Lifetime.LifeCtx.empty [] Inst.algAffProg (.comp (.ret .unit)) ∧
      (∀ ℓ ℓ', Inst.finE (Inst.DV Inst.KL2 ℓ).1 ≠ Inst.finE (Inst.DV Inst.KR2 ℓ').1) ∧
      (∀ (R : (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).Runner) (s : R.St) (v : Inst.OVal)
        (tr : List (A.Ev (orowAlg Inst.ΞA).Lab Inst.OVal Unit)),
        (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).ObsStartFrom R
          ((Adequacy.emptyMem, Inst.algAffK₀.plug Inst.algL2), s) v tr ↔
        (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).ObsStartFrom R
          ((Adequacy.emptyMem, Inst.algAffK₀.plug Inst.algR2), s) v tr) ∧
      (CDerives BoCa.Lifetime.LifeCtx.empty [] Inst.algFireProg (.comp (.ret .unit)) ∧
        ¬ RowAt Inst.ΞA Inst.R5 ∧
        (∀ (E : List (Qual × VTy × VTy)) (S : Row), RowAt Inst.ΞA (Row.ofEff 5 E 0 ++ S) →
          E.length ≤ 2 ^ 32 → E.map Prod.fst ≠ [.unr]) ∧
        ∀ C, ¬ (ourInst (ℍ := ℍ) orowRF Inst.ΞA J₁).der [] Inst.algFireProg C) :=
  ⟨Inst.not_algLawCode_ΞA, Inst.d_algAffProg rfl rfl, Inst.finE_D2_ne,
    Inst.algLaw_algAffProg Inst.ΞA,
    Inst.d_algFireProg, Inst.not_rowAt_R5, fun _ _ h hl => Inst.not_tied_hnd5_unr h hl,
    Inst.not_der_algFireProg_J₁⟩

/-- **PROVED AT σ=[] given `CfinQuiet`**: algebraicity as restated (a finaliser's start observed
but not its code, fix-up F2) at `J₁`, at every effect context, given that no configuration a typed
program reaches is at a `[cfin-raise]` step; at every typing system whose typed programs' runs are
`AlgGood`; and the statement with the finaliser's code observed gives it, at every instance. -/
theorem status_algLaw_J₁ :
    (∀ Ξ, Inst.CfinQuiet (ℍ := ℍ) orowRF Ξ J₁ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).AlgLaw) ∧
    (∀ (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF),
      (∀ (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (P : Expr) (ε : (RF.alg Ξ).Eff) (A : Inst.OVTy)
        (c : (ourInst (ℍ := ℍ) RF Ξ J).RConf R), R.Respects → (ourInst (ℍ := ℍ) RF Ξ J).DataTy A →
        (ourInst (ℍ := ℍ) RF Ξ J).der [] P ((ourInst (ℍ := ℍ) RF Ξ J).F ε A) →
        (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((ourInst (ℍ := ℍ) RF Ξ J).rinit R P) c →
        Inst.AlgGood R c) → (ourInst (ℍ := ℍ) RF Ξ J).AlgLaw) ∧
    (∀ S : A.EffectSystem, S.AlgLawCode → S.AlgLaw) :=
  ⟨fun _ h => I.algLaw_J₁_of h, fun _ _ _ h => Inst.algLaw_of_good h,
    fun S h => S.algLaw_of_algLawCode h⟩

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
