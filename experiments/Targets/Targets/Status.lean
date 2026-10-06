import Targets.Restricted.Acceptance
import Targets.Restricted.AcceptedT1
import Targets.Restricted.Answering
import Targets.Restricted.Composition
import Targets.Restricted.CoreLaws
import Targets.Restricted.Corollaries
import Targets.Restricted.EffectSafety
import Targets.Restricted.Interface
import Targets.Restricted.NoInterception
import Targets.Restricted.NonVacuity
import Targets.Restricted.RowAlg
import Targets.Restricted.Soundness
import Targets.Restricted.Transport
import Targets.Restricted.Typing
import Targets.Restricted.Unwind
import Targets.Restricted.Release
import Targets.Restricted.Handlers
import Targets.Statements.Abstraction
import Targets.Statements.ZeroCost
import Targets.Audit

/-!
# Targets — status (DESIGN §1.6)

Status words: **PROVED**, **PROVED AT σ=[]**, **PROVED AT A RESTRICTION** (the restriction
named), **OPEN**.

## Done

Done is `EndStateAt J₂ W Adm RF` (`Statements/EndState.lean`) at the `Adm` OQ-56 settles and the
`RF` OQ-13's remaining question settles, with two parts:

1. `theorem endState_W : EndStateAt J₂ W Adm RF` at a **named** tier-2 typing system `J₂` (the
   kernel's, unr-free) and a **named** world `W`;
2. `audit_W`: the step-index audit of `W`'s definition (`Targets/Audit.lean`, DESIGN §4.4)
   passing.

**Done: OPEN.**  Neither `J₂` nor `W` is defined.  `EndState` (the existential) follows from done
and is not done: an existential witness has no definition to audit.

**Tier 1 (`Tier1End`): OPEN.**  Proved at Core σ=[]: `RowAlgSafe orowRF`, `RowLink orowRF`,
`WBCore`, `I4a tier1 admClosedOp .abortive`, and of `Guarantees tier1 coreW admClosedOp .abortive`
the conjuncts `ExtendsNU`, `OutExtends`, `ReleasedOnceAll`, `EffSafe`, `NoInterception`, `WLaws`,
`FL`, `I1`, `I2`, `I3`, `I5`, `LifetimeSound`, `Exclusive`, `P11`, `ConservativeWB`.  Not proved:
`Soundness tier1` (its return conjunct is proved at `Platform.none`), `SoundnessContracts tier1`,
`FinaliserOrder tier1`, and `Adequate coreW` (its return conjunct is proved at `Platform.none`).
`Tier1End` follows from `Adequate coreW` and `FinaliserOrder tier1` alone
(`status_tier1End_of`): T1 and its contract form follow from FL and adequacy.  These two are what
remains of DESIGN §9's second wave for tier 1, beside `AdequateOfLaws`, `BinderMachine` and the
arising check.

**`ReleasedOnceAll` holds at every typing system** (`releasedOnceAll`): its run premises carry the
empty memory at the run's start and `Final` at its end, and with `NoReuse` that is all the
occupancy argument reads.  Its typing content is T1's (`Terminates`, `SafeRuns`).

## DESIGN §9

**First wave.**

| # | target | status | Lean |
|---|---|---|---|
| 1 | `(closedRowAlg Ξ).Laws ∧ .Safe`; `RowAlgSafe orowRF`; `RowLink orowRF` | PROVED AT A RESTRICTION (`RF = orowRF`) | `closedRowAlg_lawsSafe`, `rowAlgSafe_orowRF`, `rowLink_orowRF` |
| 2 | `coreW`, the transports; `WLaws coreW` | PROVED AT σ=[] | `wpGW_core`, `ewpW_core`, `opTabW_core`, `cancelTabW_core`, `ptoMutSW_core`, `ptoImmSW_core`; `wlaws_core` |
| 3 | `CDerivesNU`; `Extends tier1`, `ExtendsNU tier1`, `FL coreW tier1` | PROVED AT σ=[] | `CDerivesNU.toCDerives`, `extends_tier1`, `extendsNU_tier1`, `fl_core_tier1` |
| 4 | `SoundnessOfFL`, `SoundnessContractsOfFL` (C2), `EffSafeOfFL` | PROVED (generic) | `soundnessOfFL`, `soundnessContractsOfFL`, `soundnessContractsOfFLWB`, `effSafeOfFL` |
| 5 | `AdequateRetAt coreW Platform.none` | PROVED AT A RESTRICTION (`P = Platform.none`) | `adequateRetAt_core_none` |
| 6 | `SoundRetAt tier1 Platform.none` | PROVED AT A RESTRICTION (`P = Platform.none`) | `soundRetAt_tier1_none` |
| 7 | `stop_irreducible`; `AdequateEvery coreW`; `EffSafe tier1` | PROVED AT σ=[] | `stop_irreducible`, `adequateEvery_core`, `effSafe_tier1` |
| 8 | `I1 coreW` | PROVED AT σ=[] | `i1_core` |
| 9 | `I2 coreW OutJ.core admClosedOp .abortive` | PROVED AT A RESTRICTION (abortive rows) | `i2_core_abortive` |
| 10 | `I3 coreW` | PROVED AT A RESTRICTION (nothing held) | `i3_core` |
| 11 | `AdmExtends admClosedOp`; `OutExtends OutJ.core` | PROVED AT A RESTRICTION (`Adm = admClosedOp`); PROVED AT σ=[] | `admExtends_closedOp`, `outExtends_core` |
| 12 | `NoInterception tier1` | PROVED AT σ=[] | `noInterception_tier1` |
| 13 | `I5 coreW`; `I5beta` | PROVED AT σ=[]; PROVED (generic) | `i5_core`, `i5beta` |
| 14 | `I4a tier1 admClosedOp .abortive` (C4) | PROVED AT A RESTRICTION (tier 1, abortive rows) | `i4a_tier1` |
| 15 | `LifetimeSound coreW OutJ.core` | PROVED AT σ=[] | `lifetimeSound_core` |
| 16 | `Exclusive coreW` | PROVED AT σ=[] | `exclusive_core` |
| 17 | `HandleCompat coreW` | PROVED AT σ=[] | `handleCompat_core` |
| 18 | `WBCore`; `ConservativeWB coreW`; `Conservative coreW` | PROVED; PROVED AT σ=[] | `wbCore`, `conservativeWB_core`, `conservative_core` |
| 19 | the step-index audit on `coreW`; the pin of Core's relation | PASSES (`run_meta`) | `Targets/Audit.lean` |
| 20 | the existing effect programs against T1 | PROVED AT A RESTRICTION (`P = Platform.none`) | `acceptedT1_*` |
| 21 | the two-frame `UnwindRun` of §5 I3 | PROVED (an instance) | `two_frame`, `two_frame_steps`, `one_frame` |

**Second wave.**

| target | status | Lean |
|---|---|---|
| `ReleasedOnceOfSound`; `ReleasedOnceAll J` | PROVED; PROVED (generic, every `J`) | `releasedOnceOfSound`, `releasedOnceAll` |
| `RedLaws coreW`, hence `P11 coreW` | PROVED AT σ=[]; `RedLaws` PROVED (generic, at monotone tables) | `redLaws_core`, `p11_core`, `redLaws_of_mono` |
| `AdequateOfLaws` | OPEN | |
| `SoundRetAt tier1 P` at platforms with operations, then `Soundness tier1` | OPEN | |
| `SoundDriveAt tier1 Platform.none` | OPEN | |
| `SoundnessContracts tier1` | OPEN | |
| `FinaliserOrder tier1` | OPEN | |
| `BinderMachine` at `rs = []` | OPEN | |
| the arising check of Restrat's `not_vDenNatural` witness at `coreW` | OPEN (stated) | `NotVDenNaturalArises` |
| the AT-rejects | OPEN | |

## Corrections to the design (DESIGN §Corrections)

* **C1.** `SemW₀` reads `.val A` as `.comp (.ret A)` through the helper `SemWC`, not by calling
  itself (the design's clause is not structural recursion).  Same meaning.
* **C2.** `SoundnessContractsOfFL` asks `ExtPre M` and `Conservative M` (an extern may sit at any
  persistent type, a thunk at a resuming row included, and the nil index must be reachable); the
  design's route is kept as `SoundnessContractsOfFLWB`, at externs of row-abortive type.
* **C3.** `ansRun`, `lendCell` and `at04` are in A-normal form: Core's `[app]` applies only to a
  variable, and `lolliE` only at an arrow into `F`, so the unwinding borrow constant is bound and
  called on variables.
* **C4.** `I4a` adds `CDerives.allI`'s premises `hΔx`, `hΓx`: `x` is fresh for `Δ`'s bounds and for
  `Γ`'s live types.  The callback `Λ. λm. body` of the borrow form needs them.

DESIGN §Corrections also lists the elaboration-only adjustments, which change no meaning.

## Unresolved review findings (DESIGN §Unresolved)

The statement review ended with ten major findings.  The design was revised in response to each
(the response is in DESIGN.md's text); the revised statements were not reviewed again.

1. `UnwindRun.fin`: a finaliser's own raise stops under the `seq` frame `ufin` leaves.  Response:
   `fin`'s `hD` ends at `Kd.plug (raise …)` with `Kd.Catches m = false`, and `hr` starts at
   `(K₀.comp Kd).plug …`; checked on two frames here (`two_frame`).  `Kd` may hold handler frames
   of other names (DESIGN §5 I3), where the finding asked for none.
2. I2 and I3 did not state spanning lends or the frames a cancel closes.  Response: `FramesW`
   (6.64/6.65 at W, in the printed rule's shape) and `SpanBorrows` are conjuncts of `I2`;
   `ShareCancel` has the closing clause; at `coreW` they are recorded PROVED AT A RESTRICTION.
   `CancelCloses` (the lends a cancel ends) is named-only under OQ-57.
3. `FreezeBinder` was a conjunct of done.  Response: it is beside done (`EndStateBinder`), with
   its lifetime clauses forward implications.
4. `Adm` had no lower bound and the outlives judgment was not the typing system's.  Response:
   `AdmExtends Adm` is a conjunct; `TypingJ` carries `out : OutJ`, read by every rule
   transcription, by `OutExtends J.out` and by `LifetimeSound M J.out`.
5. Done as an existential could not carry decision 7.  Response: done is `EndStateAt` at a named
   `W` with `audit_W`; `Targets/Audit.lean` runs the audit on `coreW`.
6. A6 and T7 overclaimed.  Response: A6's continuation-use half is P8.b (named-only, OQ-50);
   `ConservativeWB` (T7's shape) is in done, `Conservative` beside it; Core's relation is pinned by
   hash (`Targets/Audit.lean`), so a redefined Core cannot meet either by definition.
7. `Slice` pinned R-T1 at σ=[] for every type.  Response: `SliceShape` pins the nil slice
   structurally only; the embedding is `ConservativeWB`; DESIGN §10 asks the user whether the
   equivalence was meant.
8. `FreezeBinder`'s lifetime half against `not_vDenNatural`.  Response: beside done; the arising
   check of the witness at `coreW` is stated (`NotVDenNaturalArises`) and OPEN.
9. `Extends` needed resuming `unr` operations at W.  Response: done asks `ExtendsNU` (Core's rules
   without resuming `unr` operations, `CDerivesNU`); `Tier1End` keeps `tier1` at Core σ=[] only.
10. `RelShape`'s `Imm`/`Mut` clauses were not Core's.  Response: they transcribe Core's clauses
    with W's relation for the payload (`ptoImmSW`, `ptoMutSW`, `CohE`); OQ-46 is open only in
    `payStk`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

/-! ## Done -/

/-- The statement of done elaborates.  **OPEN.** -/
example (J : TypingJ) (M : SemWorld) : Prop := EndStateAt (ℍ := ℍ) J M admClosedOp orowRF

/-- Implied by done, not done. -/
example : Prop := EndState (ℍ := ℍ) admClosedOp orowRF

/-- **Tier 1: OPEN** (the conjuncts missing are listed in the module docstring). -/
example : Prop := Tier1End (ℍ := ℍ)

/-- **`Tier1End` from its two open parts**: adequacy at Core's world for every platform and every
drive, and the finaliser order for Core's typing.  Every other conjunct is proved. -/
theorem status_tier1End_of (hA : Adequate (ℍ := ℍ) (coreW (ℍ := ℍ)))
    (hF : FinaliserOrder (ℍ := ℍ) tier1) : Tier1End (ℍ := ℍ) :=
  ⟨rowAlgSafe_orowRF, rowLink_orowRF, wbCore, i4a_tier1,
    extendsNU_tier1, outExtends_core, soundnessOfFL _ _ fl_core_tier1 hA,
    soundnessContractsOfFL _ _ fl_core_tier1 extPre_core conservative_core hA,
    releasedOnceAll tier1, effSafe_tier1, noInterception_tier1, hF, wlaws_core, fl_core_tier1, hA,
    i1_core, i2_core_abortive, i3_core, i5_core, lifetimeSound_core, exclusive_core, p11_core,
    conservativeWB_core⟩

/-! ## The conjuncts of `EndStateAt`

At the end state every conjunct is OPEN until done is proved.  Below, each conjunct's status at
tier 1, σ = [] or a restriction. -/

/-! ### `RowAlgSafe RF`, `RowLink RF` (T0) -/

/-- PROVED AT A RESTRICTION (`RF = orowRF`, the minimal tail-variable form). -/
theorem status_rowAlgSafe_orow : RowAlgSafe orowRF := rowAlgSafe_orowRF

/-- PROVED AT A RESTRICTION (`RF = orowRF`). -/
theorem status_rowLink_orow : RowLink orowRF := rowLink_orowRF

/-! ### `AdmExtends Adm` -/

/-- PROVED AT A RESTRICTION (`Adm = admClosedOp`, OQ-56 (a)). -/
theorem status_admExtends_closedOp : AdmExtends admClosedOp := admExtends_closedOp

/-! ### `Tier2Pinned J Adm`, `AcceptsTier2 J` -/

/-- OPEN: they are about tier 2's typing system, which does not exist.  The acceptance terms run
(`at02_eval`, `at04_eval`, `at12_eval`, `at17_eval`). -/
example (J : TypingJ) (Adm : OpAdm) : Prop := Tier2Pinned J Adm ∧ AcceptsTier2 J

/-! ### `I4a J Adm .any` (I4.a) -/

/-- PROVED AT A RESTRICTION (tier 1, abortive rows).  Statement corrected (C4).  Non-vacuity:
`i4a_witness`, `d_ansRun_witness`. -/
theorem status_I4a_tier1_abortive : I4a tier1 admClosedOp .abortive := i4a_tier1

/-! ## The conjuncts of `Guarantees` -/

/-! ### `ExtendsNU J`, `OutExtends J.out` -/

/-- PROVED AT σ=[] (also `extends_tier1 : Extends tier1`, `extendsNU_tier1NU`). -/
theorem status_extendsNU_tier1 : ExtendsNU tier1 := extendsNU_tier1

/-- PROVED AT σ=[]. -/
theorem status_outExtends_core : OutExtends OutJ.core := outExtends_core

/-! ### `Soundness J` (T1) -/

/-- PROVED AT A RESTRICTION (`P = Platform.none`, the return conjunct).  `Soundness tier1`:
OPEN (second wave).  Non-vacuity: `platformNone_respects`, `platformPing_respects`, the
`acceptedT1_*` programs. -/
theorem status_soundRet_tier1_none : SoundRetAt (ℍ := ℍ) tier1 Platform.none :=
  soundRetAt_tier1_none

/-- PROVED (generic): T1 is FL and adequacy. -/
theorem status_soundnessOfFL : SoundnessOfFL (ℍ := ℍ) := soundnessOfFL

/-! ### `SoundnessContracts J` -/

/-- OPEN at tier 1 (second wave).  PROVED (generic) from FL, `ExtPre`, `Conservative` and
adequacy (C2). -/
theorem status_soundnessContractsOfFL : SoundnessContractsOfFL (ℍ := ℍ) := soundnessContractsOfFL

/-- PROVED (generic): the design's route, at externs of row-abortive type. -/
theorem status_soundnessContractsOfFLWB : SoundnessContractsOfFLWB (ℍ := ℍ) :=
  soundnessContractsOfFLWB

/-! ### `ReleasedOnceAll J` (D9, P8.a) -/

/-- PROVED: D9's machine lemma. -/
theorem status_releasedOnceOfSound : ReleasedOnceOfSound (ℍ := ℍ) := releasedOnceOfSound

/-- PROVED (generic): at every typing system, by the occupancy argument on complete no-reuse
runs; its typing content is T1's. -/
theorem status_releasedOnceAll : ∀ J : TypingJ, ReleasedOnceAll (ℍ := ℍ) J := releasedOnceAll

/-! ### `EffSafe J` (P2) -/

/-- PROVED AT σ=[] (unr-free rows, by the statement). -/
theorem status_effSafe_tier1 : EffSafe (ℍ := ℍ) tier1 := effSafe_tier1

/-- PROVED (generic). -/
theorem status_effSafeOfFL : EffSafeOfFL (ℍ := ℍ) := effSafeOfFL

/-! ### `NoInterception J` (I3.c) -/

/-- PROVED AT σ=[]. -/
theorem status_noInterception_tier1 : NoInterception tier1 := noInterception_tier1

/-! ### `FinaliserOrder J` (I3.b) -/

/-- OPEN (second wave).  Its first instance, the two-frame unwind, is proved (`two_frame`,
`two_frame_steps`, `one_frame`). -/
example (J : TypingJ) : Prop := FinaliserOrder (ℍ := ℍ) J

/-! ### `WLaws M` -/

/-- PROVED AT σ=[]. -/
theorem status_wlaws_core : WLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) := wlaws_core

/-! ### `FL M J` -/

/-- PROVED AT σ=[] (`fundamentalC`). -/
theorem status_fl_core_tier1 : FL (coreW (ℍ := ℍ)) tier1 := fl_core_tier1

/-! ### `Adequate M` -/

/-- PROVED AT A RESTRICTION (`P = Platform.none`, the return conjunct).  `Adequate coreW` and
`AdequateOfLaws`: OPEN (second wave). -/
theorem status_adequateRet_core_none : AdequateRetAt (ℍ := ℍ) (coreW (ℍ := ℍ)) Platform.none :=
  adequateRetAt_core_none

/-! ### `I1 M` -/

/-- PROVED AT σ=[]. -/
theorem status_I1_core : I1 (ℍ := ℍ) (coreW (ℍ := ℍ)) := i1_core

/-! ### `I2 M J.out Adm c` -/

/-- PROVED AT A RESTRICTION (abortive rows: no resuming entry, so the frames at resuming tables
and the spanning rules at resuming rows are not exercised). -/
theorem status_I2_core_abortive : I2 (ℍ := ℍ) (coreW (ℍ := ℍ)) OutJ.core admClosedOp .abortive :=
  i2_core_abortive

/-! ### `I3 M` (I3.a) -/

/-- PROVED AT A RESTRICTION (nothing held at σ = []: the closing clause is vacuous). -/
theorem status_I3_core : I3 (ℍ := ℍ) (coreW (ℍ := ℍ)) := i3_core

/-! ### `I5 M` -/

/-- PROVED AT σ=[]. -/
theorem status_I5_core : I5 (ℍ := ℍ) (coreW (ℍ := ℍ)) := i5_core

/-- PROVED (generic). -/
theorem status_I5beta : ∀ M : SemWorld, I5beta (ℍ := ℍ) M := i5beta

/-! ### `LifetimeSound M J.out` (P9) -/

/-- PROVED AT σ=[]. -/
theorem status_lifetimeSound_core : LifetimeSound (coreW (ℍ := ℍ)) OutJ.core := lifetimeSound_core

/-! ### `Exclusive M` (P10) -/

/-- PROVED AT σ=[]. -/
theorem status_exclusive_core : Exclusive (coreW (ℍ := ℍ)) := exclusive_core

/-! ### `P11 M` -/

/-- PROVED AT σ=[]: `HandleCompat coreW` and `RedLaws coreW`. -/
theorem status_P11_core : P11 (ℍ := ℍ) (coreW (ℍ := ℍ)) := p11_core

/-- PROVED (generic): the reduction laws at every world whose operation tables are monotone. -/
theorem status_redLaws_of_mono {M : SemWorld} (hM : ∀ T, TableI.Mono (opTabW M T)) :
    RedLaws (ℍ := ℍ) M := redLaws_of_mono hM

/-! ### `ConservativeWB M` (P14.b) -/

/-- PROVED AT σ=[]. -/
theorem status_conservativeWB_core : ConservativeWB (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  conservativeWB_core

/-! ### `WBCore` (P14.a, a conjunct of `Tier1End`) -/

/-- PROVED. -/
theorem status_wbCore : WBCore (ℍ := ℍ) := wbCore

/-! ## Beside done (OPEN unless stated) -/

example (M : SemWorld) (act : StkAct M) : Prop := FreezeBinder M act
example : Prop := BinderMachine (ℍ := ℍ)
example (J : TypingJ) (M : SemWorld) (act : StkAct M) (Adm : OpAdm) (RF : RowForm) : Prop :=
  EndStateBinder (ℍ := ℍ) J M act Adm RF
example (J : TypingJ) : Prop := ReleasedOnceReuse (ℍ := ℍ) J
example (J : TypingJ) (Adm : OpAdm) : Prop := I4Typing J Adm .any
/-- The binder's first check (second wave): OPEN. -/
example : Prop := NotVDenNaturalArises (ℍ := ℍ)

/-- `Conservative W`: OPEN; at `coreW` PROVED AT σ=[]. -/
theorem status_conservative_core : Conservative (ℍ := ℍ) (coreW (ℍ := ℍ)) := conservative_core

/-! ## Corollaries of done (PROVED, generic) -/

theorem status_i1Prog_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm} :
    EndStateAt (ℍ := ℍ) J M Adm RF → I1Prog (ℍ := ℍ) J := i1Prog_of_endState

theorem status_i2Prog_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm} :
    EndStateAt (ℍ := ℍ) J M Adm RF → I2Prog (ℍ := ℍ) J := i2Prog_of_endState

theorem status_p8a_of_endState {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm} :
    EndStateAt (ℍ := ℍ) J M Adm RF → P8a (ℍ := ℍ) J := p8a_of_endState

/-! ## Binary and cross-language, out of the first pass (stated, OPEN) -/

example (J : TypingJ) (fuse : Val → Val → Val) : Prop := Laws (ℍ := ℍ) J fuse
example (J : TypingJ) : Prop := Abstraction (ℍ := ℍ) J
example (J : TypingJ) : Prop := I4c (ℍ := ℍ) J

/-! ## Named-only (no statement; excluded from the elaboration check)

* **`CancelCloses`** (beside done, OQ-57): a cancel ends every lend the cancelled continuation
  holds, at W.  Missing: the frames a continuation froze, as distinct from frames other suspended
  computations hold at the same index (OQ-57's closing accounting).
* **P8.b, `ContUse`** (beside done, OQ-50): each continuation a step creates is used as its
  qualifier says.  Missing: an observation of a continuation's use (an instrumented `hop`, or the
  TR's one-shot-cell machine).
* **T3's proof device, `AbstractionOfFL₂`** (out of the first pass): T3 from a binary
  fundamental lemma.  Missing: a binary world `SemWorld₂`.
* **T4, `LoweringCorrect` and `ZeroCost`** (out of the first pass, OQ-23): the lowering preserves
  observations, and the lowered code allocates and indirects only where the reference encoding
  does.  Missing: the backend's fuel-parametric stage interpreter, and each class's reference
  encoding and cost model (`LowClass` names the classes).
-/

end Targets

end
