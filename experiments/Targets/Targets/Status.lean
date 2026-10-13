import Targets.I.Combined
import Targets.B.NonVacuity
import Targets.B.Release
import Targets.Instance.Bridges
import Targets.Instance.Binary
import Targets.Instance.ZeroCost
import Targets.Instance.Restricted.NoInterception
import Targets.Instance.Restricted.Unwind
import Targets.Instance.Restricted.Programs
import Targets.A.NonVacuity
import Targets.A.Binary
import Targets.A.UnaryLaws
import Targets.A.Lowering
import Targets.Audit

/-!
# Targets — status, by system (RESTRUCTURE §0)

Status words: **PROVED**, **PROVED AT σ=[]**, **PROVED AT A RESTRICTION** (the restriction named),
**OPEN**.  Four parts: **A**, an effect system, abstractly; **B**, the borrow calculus, given; **I**,
the interaction and the combined theorem; **the Instance**, our calculus as one instance of A.

## Done

Done is `I.Combined orowRF J₂ W admClosedOp .any` (`Targets/I/Combined.lean`) at a **named**
tier-2 typing system `J₂` and a **named** world `W`, with `audit_W` (`Targets/Audit.lean`): A's
properties at our instance at every admissible effect context, B's guarantees in the composite, the
interaction's option-neutral rules, the pins, the composite's programs and its rejections.  Fixed at
`admClosedOp` until OQ-56 is chosen and at `orowRF` until OQ-13's remaining question is answered.

**Done: OPEN.**  Neither `J₂` nor `W` is defined.  **Tier 1** (`I.Tier1 J₁`): OPEN; `J₁` (today's
rules over open rows with the row `∀`) waits on RESTRUCTURE §7 Q1–Q2.

**The restricted tier-1 reduction** (`I.Tier1Core`, at today's kernel `tier1Open` and Core's world):
OPEN.  Proved of it: the world conjuncts and the device at `coreW` (`status_tier1Core_world`), and
B's guarantees from `Adequate coreB` and the step-for-step simulation `BumpSim`
(`status_tier1Core_guarantees_of`; B5 aside, from `Adequate coreB` alone, `status_tier1Core_B_of`).
Missing: A's (S) properties at our instance (the bridges below marked OPEN) and `I4a` at today's
unr-free kernel; and the two open statements themselves, `Adequate coreB` at every platform and for
the drive, and `BumpSim` (OQ-43).

## System A

| target | status | Lean |
|---|---|---|
| `EffectSystem`, S0–S6, E1–E10, `Props`; A₂ (`HandlerLaws`, `EffDepLaws`, `Abstraction`); A₃ (`Tgt`, `LoweringCorrect`, `ZeroCost`) | stated (elaborate) | `Targets/A/*` |
| a typing that types nothing fails `EProps`; no effects fail it | PROVED (every instance) | `not_eProps_of_emptyTyping`, `not_eProps_of_noLabels` |
| E1, E2, E6, E10 need effect polymorphism (row variables, decision 62) | PROVED (every instance; E10 with `LiftExt`) | `not_noColouring_of_monoCallback`, `not_higherOrderPoly_of_monoCallback`, `not_tunnel_of_monoCallback`, `not_reconciler_of_monoCallback` |
| E3 needs divergence; a pure-row loop that diverges is not at a data answer | PROVED (every instance; the latter with `RowAlgebra`) | `not_loops_of_total`, `divInTypes_of_loops` |
| effect safety has teeth; Def. 5.1 (1) from one signature object | PROVED (every instance) | `not_der_unhandled`, `c1_of_rowSig` |
| the runners `Rtick`, `Rtl`, `Rrec` keep their protocol | PROVED (every instance; `Rrec` at distinct labels) | `rtick_respects`, `rtl_respects`, `rrec_respects` |
| A's properties at our instance | OPEN (the Instance's bridges, below) | — |
| the unary laws beside done, `UnaryLaws` (`TailLaw`, `AlgLaw`, `EtaHold`) and the alternative `EtaLin`: run-level (menu form F.3), the tail law's hygiene as hypotheses | STATED, not proved (at no instance); **not in done**: whether they join done is a menu choice (P11/I5 menu axes H, F, K), for the user | `Targets/A/UnaryLaws.lean` |
| `EtaHold` gives `EtaLin`; each of the four fails at an instance whose handler or bind ignores its clauses | PROVED | `etaLin_of_etaHold`, `not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy`, `not_etaLin_toy` |
| A₃'s reference programs (the `Tgt` code checking each `refCost` entry) | not written | RESTRUCTURE §Unresolved |

## System B

| id | guarantee | status at BoLo | Lean |
|---|---|---|---|
| B0 | BoLo's programs stay typed | PROVED AT σ=[] | `extendsB_tier1` |
| B1 | the fundamental property | PROVED AT σ=[] | `fl_core_tier1`, `fl_core_tier1NU` (at `coreB`) |
| B2 | adequacy | PROVED AT A RESTRICTION (the platform with no operation, data answers); every platform and the drive: OPEN | `adequateRetAt_core_none` |
| B3, B4 | safety, leak freedom | PROVED AT A RESTRICTION (the same) | `soundRetAt_tier1_none` |
| B4′ | with externs meeting W's contract | PROVED (generic, from B1 and B2, finding #7) | `soundContractsOfFL` |
| B5 | release exactly once, reuse included | from B4′ given the step-for-step simulation `BumpSim`: PROVED (generic); `BumpSim` itself OPEN (OQ-43), its conclusion met at a reuse step: PROVED; not a tautology: PROVED | `releasedOnceReuse_of_bumpSim`, `bumpSim_at_reuse`, `not_releasedOnceReuse_staleFree` |
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
| `AppLaw`, `Congr`, `OpStuck`, `LoopLaws`, `DriveLaws`, `LetLaw`, `RowAlgebra`, `Safety`, `EffSafe`, `HandlerSem`, `Cancellation`, `ContUse` at our instance | OPEN (the bridges to build, RESTRUCTURE §4.1) | — |
| `monoCallback_tier1Open` (today's kernel fails E1, E2, E6, E10); R1–R4 (S6 bites); the positive (E) runs at `tier1Open` | OPEN (inversions and runs to build, RESTRUCTURE §6.1) | — |
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
  kept: `status_tier1Core_world`, `status_tier1Core_B_of`, `status_tier1Core_guarantees_of`.
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
* `Targets/Checks/RunEnd.lean` (untracked, not imported): **deleted**, superseded: each of its 17
  theorems has a same-named successor in `Targets/I/RunEnd.lean`, restated against the field `Upd`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets.Inst (OurTyping ourInst AdmEff tier1Open)

/-! ## Done and tier 1 (OPEN) -/

/-- **Done**, at a named `J₂` and `W`: the statement elaborates.  OPEN. -/
example (J₂ : OurTyping orowRF) (W : SemWorld) : Prop :=
  I.Combined (ℍ := ℍ) orowRF J₂ W admClosedOp .any

/-- **Tier 1**: OPEN. -/
example (J₁ : OurTyping orowRF) : Prop := I.Tier1 (ℍ := ℍ) J₁

/-- The restricted tier-1 reduction: OPEN. -/
example : Prop := I.Tier1Core (ℍ := ℍ)

/-- PROVED AT σ=[]: the tier-1 world conjuncts and the device at `coreW`. -/
theorem status_tier1Core_world :
    I.Bounds (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ I.Interface (coreW (ℍ := ℍ)) ∧
      Device (ℍ := ℍ) (coreW (ℍ := ℍ)) tier1Open.read admClosedOp .abortive ∧ WBCore (ℍ := ℍ) :=
  I.tier1Core_world

/-- PROVED (from adequacy at BoLo): B's guarantees but B5, at today's kernel. -/
theorem status_tier1Core_B_of (hA : Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ))) :
    B.ExtendsB tier1Open.read ∧ FL (B.coreB (ℍ := ℍ)) tier1Open.read ∧ Sound (ℍ := ℍ) tier1Open.read ∧
      B.SoundContracts (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧
      LifetimeSound (B.coreB (ℍ := ℍ)) tier1Open.read.out ∧ B.WBound (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_B_of hA

/-- PROVED (from adequacy at BoLo and the step-for-step simulation): B's guarantees at today's
kernel, B5 included. -/
theorem status_tier1Core_guarantees_of (hA : Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)))
    (hS : BumpSim (ℍ := ℍ)) : B.Guarantees (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) :=
  I.tier1Core_guarantees_of hA hS

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

/-- PROVED: the same at E2a, E6 and E10. -/
theorem status_not_poly_of_monoCallback (hm : S.MachShape) (hr : S.RowAlgebra) (he : S.EffSafe)
    (hl : S.LetLaw) (hmono : MonoCallback S) (hext : LiftExt S) :
    ¬ S.HigherOrderPoly ∧ ¬ S.Tunnel ∧ ¬ S.Reconciler :=
  ⟨not_higherOrderPoly_of_monoCallback hm hr he hl hmono, not_tunnel_of_monoCallback hm hr he hl hmono,
    not_reconciler_of_monoCallback hm hr he hl hmono hext⟩

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

/-- The A properties at our instance: OPEN (the bridges to build). -/
example (Ξ : EffCtx) : Prop := AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).SPropsNoUse

/-- Binary and cross-language over Core, out of the first pass (stated, OPEN). -/
example (J : TypingJ) (fuse : Val → Val → Val) : Prop :=
  Laws (ℍ := ℍ) J fuse ∧ Abstraction (ℍ := ℍ) J ∧ I4c (ℍ := ℍ) J

end Targets

end
