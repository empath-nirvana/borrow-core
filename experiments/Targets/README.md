# Targets — the effect calculus's end state, in Lean

`DESIGN.md` says what "done" means for the effect calculus. This library states every target
there as a `def … : Prop`, proves the restricted instances the design asks for now (its §9), and
records each target's status in `Targets/Status.lean`. W, the world the effect calculus needs, is
not built here: it is the parameter `M : SemWorld` of the end state.

```
lake build Targets
```

The build has no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`, `unsafe` or
`implemented_by`. `Targets/AxiomCheck.lean` prints `#print axioms` of every theorem the sources
state and fails the build if any theorem of the library uses an axiom outside
`[propext, Classical.choice, Quot.sound]`.

## Layout

| path | contents |
|---|---|
| `Targets/Defs/Effects.lean` | rows, row variables and row contexts (`Row.NU`, `RowClass`, `RowCtx.Models`); the effect algebra (`EffAlg`, `EffAlg.Laws`, `EffAlg.Safe`), the row forms `closedRowAlg` and `orowRF`; `Kont.fins`, `cancelOf` |
| `Targets/Defs/Typing.lean` | `OutJ`, `TypingJ`; `tier1` (Core's `CDerives`), `CDerivesNU` and `tier1NU` (Core's rules without resuming `unr` operations); the rule transcriptions `RC_*`; `Extends`, `ExtendsNU` |
| `Targets/Defs/Runs.lean` | platforms (`Platform`, `Platform.Respects`, `PStep`), the outermost driver (`RStep`), data (`VTy.Data`, `DataVal`), `Final`, `SafeRuns`, `Terminates`, `SafeDrive`, `StopsIn`, runs as lists (`PRun`, `Allocated`, `Released`, `NoReuse`, `ReleasedOnce`) |
| `Targets/Defs/World.lean` | `SemWorld`; W's `wpGW`, `ewpW`, `opTabW`, `cancelTabW`, `ptoMutSW`, `ptoImmSW`, `gDenW`, `SemW`; `coreW`, Core's relation as the instance whose lend stack has one point |
| `Targets/Defs/Binder.lean` | D11: the actions of a location permutation and of a re-stratification, `StkAct`, `BlockAffine`, `StepsIn` |
| `Targets/Defs/Ctx.lean` | D12: observations and contextual approximation (binary targets) |
| `Targets/Defs/Programs.lean` | D13: answering implementations (`AnsImpl`, `ansRun`, `ctlForm`, `capPass`); D14: the acceptance terms `at02`, `at04`, `at12`, `at17` |
| `Targets/Statements/*.lean` | every target; `Guarantees`, `EndStateAt`, `EndState`, `Tier1End`, `EndStateBinder`, `I1Prog`, `I2Prog` (`EndState.lean`) |
| `Targets/Restricted/*.lean` | the proofs: the restricted instances, the generic composition lemmas, non-vacuity |
| `Targets/Audit.lean` | the step-index audit, run on `coreW`; the pin of Core's relation |
| `Targets/Status.lean` | the record: done, tier 1, every conjunct, the targets beside done, the corollaries, the named-only targets, the corrections and the unresolved review findings |
| `Targets/AxiomCheck.lean` | the axioms of every proved result |

## Done

Done is `EndStateAt J₂ W Adm RF` at a **named** tier-2 typing system `J₂` and a **named** world `W`,
together with `audit_W`, the step-index audit of `W`'s definition. **It is OPEN**: neither `J₂` nor
`W` exists. `EndState`, the existential, follows from done and is not done.

`Tier1End`, every guarantee for Core's typing at Core's relation with lends spanning abortive rows
only, is **OPEN**. It follows from two statements (`status_tier1End_of`): `Adequate coreW`,
adequacy at Core's world under every platform with operations and for driven loops (T1 and its
contract form then follow from `FL`), and `FinaliserOrder tier1`. Every other conjunct is proved.

## The definitions

- **An effect** is a name with a signature of operations `A ↠^q B` (`EffCtx`), each `q` linear,
  affine or unrestricted, or abortive at `B = 0`. **A row** is Core's list of operation signatures,
  read by first match (`Row.find`); a row variable stands for a closed row (`RowEnv`), constrained
  by a class and an admissibility condition (`RowCon`, `RowCtx.Models`). The rows form an effect
  algebra (Yoshioka–Sekiyama–Igarashi Def. 3.5, `EffAlg.Laws`) that is safe (Def. 5.1,
  `EffAlg.Safe`); `RowLink` ties the algebra to the rows the typing rules read.
- **A handler** is Core's `hnd (n, (h_ret, hs))` and its `[handle]` rule; handling is the machine's
  `[ret]`, `[op]` and `[unwind]` steps.
- **A suspension** is the value `κ = kappa n H K` the `[op]` step hands a clause, at the type
  `kTy` of its qualifier: resumed (`κ (inj₁ ())`), or cancelled (`κ (inj₂ ())`, which runs
  `cancelOf n H K` and fires the frozen finalisers `Kont.fins`).
- **Effect safety** (`EffSafe`): a typed program at the row `S` either runs to a value, keeps
  stepping, or stops at an operation of `S` that no handler catches (`StopsIn S`).
- **Soundness** (T1, `Soundness`): under every platform that respects its protocol, every run of
  a typed program at a data answer is safe (`SafeRuns`) and terminates (`Terminates`) with the
  memory empty (`Final`); a program returning a loop is safe at every finite prefix of its drive
  (`SafeDrive`).
- **Finalisation exactly once** (D9, `ReleasedOnceAll`): on every complete run that reuses no
  location, every allocated cell is released exactly once; finalisers fire once each, innermost
  first, on a cancel and on an unwind (`FinaliserOrder`); no typed program intercepts a cancel
  (`NoInterception`).
- **The invariant** is W's family of configurations (`SemWorld.Fam`, at Core the typed worlds
  `TW`), with what suspensions hold (`SemWorld.held`) and W's relation (`val`, `comp`, `share`).
  **Arising** (`Arises`) says every configuration W reaches is a typed world over the visible and
  the held frames.

## Status

From `Targets/Status.lean`. *PROVED AT σ=[]* is Core's relation (`coreW`) or Core's typing
(`tier1`); *generic* is for every world or typing system.

| target | world | status | Lean |
|---|---|---|---|
| done: `EndStateAt J₂ W Adm RF` + `audit_W` | W | OPEN | — |
| `Tier1End` | Core σ=[] | OPEN; follows from `Adequate coreW` and `FinaliserOrder tier1` | `status_tier1End_of` |
| T0: `RowAlgSafe`, `RowLink` | prog | PROVED AT A RESTRICTION (`orowRF`) | `rowAlgSafe_orowRF`, `rowLink_orowRF` |
| `AdmExtends` | prog | PROVED AT A RESTRICTION (`admClosedOp`) | `admExtends_closedOp` |
| `Tier2Pinned`, `AcceptsTier2` | prog | OPEN (no tier-2 typing); the four terms run | `at02_eval` … `at17_eval` |
| `I4a` (I4.a) | prog | PROVED AT A RESTRICTION (tier 1, abortive rows) | `i4a_tier1` |
| `ExtendsNU`, `OutExtends` | prog | PROVED AT σ=[] | `extendsNU_tier1`, `outExtends_core` |
| `Soundness` (T1) | prog | return conjunct PROVED AT A RESTRICTION (`Platform.none`); at tier 1, follows from `Adequate coreW`: OPEN | `soundRetAt_tier1_none` |
| `SoundnessOfFL`, `SoundnessContractsOfFL`, `EffSafeOfFL` | generic | PROVED | `soundnessOfFL`, `soundnessContractsOfFL`, `effSafeOfFL` |
| `SoundnessContracts` | prog | at tier 1, follows from `Adequate coreW`: OPEN | `soundnessContractsOfFL` |
| `ReleasedOnceAll` (D9, P8.a) | prog | PROVED, generic (every `J`) | `releasedOnceAll`, `releasedOnceOfSound` |
| `EffSafe` (P2) | prog | PROVED AT σ=[] | `effSafe_tier1` |
| `NoInterception` (I3.c) | prog | PROVED AT σ=[] | `noInterception_tier1` |
| `FinaliserOrder` (I3.b) | prog | OPEN; its two-frame instance PROVED | `two_frame` |
| `WLaws` | W | PROVED AT σ=[] | `wlaws_core` |
| `FL` | W | PROVED AT σ=[] | `fl_core_tier1` |
| `Adequate` | W | return conjunct PROVED AT A RESTRICTION (`Platform.none`); full: OPEN | `adequateRetAt_core_none` |
| `I1` | W | PROVED AT σ=[] | `i1_core` |
| `I2` | W | PROVED AT A RESTRICTION (abortive rows) | `i2_core_abortive` |
| `I3` (I3.a) | W | PROVED AT A RESTRICTION (nothing held) | `i3_core` |
| `I5` | W | PROVED AT σ=[]; `I5beta` generic | `i5_core`, `i5beta` |
| `LifetimeSound` (P9) | W | PROVED AT σ=[] | `lifetimeSound_core` |
| `Exclusive` (P10) | W | PROVED AT σ=[] | `exclusive_core` |
| `P11` | W | PROVED AT σ=[]; `RedLaws` generic at monotone tables | `p11_core`, `redLaws_of_mono` |
| `ConservativeWB` (P14.b) | W | PROVED AT σ=[] | `conservativeWB_core` |
| `WBCore` (P14.a) | Core | PROVED | `wbCore` |
| `FreezeBinder`, `BinderMachine`, `EndStateBinder` | beside done | OPEN | — |
| `NotVDenNaturalArises` (the binder's first check) | Core σ=[] | OPEN | — |
| `Conservative` | beside done | OPEN; at `coreW` PROVED AT σ=[] | `conservative_core` |
| `ReleasedOnceReuse`, `I4Typing` | beside done | OPEN | — |
| `I1Prog`, `I2Prog`, P8.a from done | corollaries | PROVED (generic) | `i1Prog_of_endState`, `i2Prog_of_endState`, `p8a_of_endState` |
| T2 `Laws`, T3 `Abstraction`, `I4c` | binary, out of the first pass | OPEN (stated) | — |
| `CancelCloses`, P8.b, T3's proof device, T4 | named-only | OPEN (no statement) | — |
| the step-index audit on `coreW`; Core's relation pinned | meta | passes | `Targets/Audit.lean` |

`ReleasedOnceAll` holds at every typing system: its run premises carry the empty memory at the
start and `Final` at the end, and with `NoReuse` that is all the occupancy argument reads. Its
typing content is T1's `Terminates` and `SafeRuns`.

Non-vacuity (`Targets/Restricted/NonVacuity.lean`): `Platform.none` and a platform with a linear
operation respect their protocol; `RowSpan admClosedOp` is met at each class by a row with an
operation, and `OpTabI.Resuming` by resuming tables; every hypothesis of `I4a tier1` is met by one
configuration at an abortive row, whose borrow form is then typed (`d_ansRun_witness`).

## The survey's package, translated

DESIGN §7 maps each of the survey's A1–A7 and T0–T9:

| survey | here |
|---|---|
| A1 type soundness with suspended frames | T1, `FL`, `I1`, semantic preservation (`Arises`) |
| A2 effect safety and algebra conditions | `EffSafe`; T0 (`RowAlgSafe`, `RowLink`) |
| A3 multiplicity soundness | P8, for `lin`/`aff`; multi-shot dropped (decision 63) |
| A4 lifetime and escape soundness | `LifetimeSound` (6.60 at every type, at the typing system's outlives judgments), `EffSafe` |
| A5 exclusivity across the handler | `Exclusive`, I4 |
| A6 discard semantics | resource half: `ReleasedOnceAll`, I3; continuation-use half: P8.b, named-only (OQ-50) |
| A7 conservativity | `ConservativeWB` (T7's shape) in done, `Conservative` beside it, against Core's relation as pinned |
| T0 effect algebra | `RowAlgSafe`, `RowLink` |
| T1 capture lemma | `I1` |
| T2 preservation | `I2`, `I3` |
| T3 progress and effect safety | `SafeRuns`, `EffSafe` |
| T4 resource conservation | `ReleasedOnceAll`; use count behind OQ-50 |
| T5 borrow invariants with suspended frames | `Exclusive`, `I2`, `LifetimeSound`, `EffSafe` |
| T6 discard | T1 with `ReleasedOnceAll`; `FinaliserOrder`; `ShareCancel` |
| T7 conservativity | `ConservativeWB` |
| T8 abstraction safety | T3 `Abstraction` (binary, out of the first pass) |
| T9 elaboration | not a target |

## The acceptance programs

**Tier 2 (D14).** The terms tier 2 must type, run by `Support`'s interpreter
(`Targets/Restricted/Acceptance.lean`, by `decide`):

| term | survey program | answer | observation |
|---|---|---|---|
| `at02` | 2: a cell lent across a once-resuming `Foo`, then read | `Flag` | `inj₁ ()`, memory empty |
| `at04` | 4: `v.push(do choose())`, one-shot | `Flag ⊗ Flag` | `(inj₁ (), inj₂ ())`, memory empty |
| `at12` | 12: `thread::scope` with the continuation cancelled | `Flag` | `inj₂ ()`, memory empty; the lend's finaliser frees the cell during the cancel |
| `at17` | 17: a lend across a perform in a moved continuation | `Flag` | `inj₁ ()`, memory empty |

DESIGN §8 expects tier 1 to reject each (its unwinding constants ask `Row.Unwind`); the
rejections are not proved here. Tier 2's typing does not exist, so `AcceptsTier2` is OPEN.

**Tier 1.** These effect programs of `Core/EffPrograms.lean` and `Core/EffExamples.lean` are
`AcceptedT1`: typed by tier 1 at a data answer, and every run under the platform with no operation
safe and terminating with the memory empty (`Targets/Restricted/AcceptedT1.lean`): `prog`, `progC`,
`logOutside`, `failOutside`, `reborrowRaise`, `nLogOutside`, `nFailOutside`, `logInBorrow`,
`tickProg n`, `takeProg n`, `storeCancel`, `tickAnsProg n`. `storeCancel` is also typed by the
unr-free fragment (`d_storeCancelNU`), which `I1Prog`'s derivation from done uses.

DESIGN §8 places the survey's seventeen programs: the multi-shot ones are dropped, AT02, AT04,
AT12 and AT17 are above, and the rejects are outside the first pass.

## Corrections and open review findings

`DESIGN.md` §Corrections lists the four places the Lean departs from the design as first printed
(C1 `SemW₀`, C2 `SoundnessContractsOfFL`, C3 the A-normal acceptance terms, C4 `I4a`'s freshness
premises) and the elaboration-only adjustments. §Unresolved review findings lists the ten
findings the statement review ended with, and the revision that answers each; the revised
statements were not reviewed again.
