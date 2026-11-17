import Core.Chain.HandlerLawN
import Core.Chain.Adequacy791N
import Core.Chain.CodeLoop855N
import Core.Chain.Externs791N
import Core.Chain.IO791N
import Core.Chain.Nest844N
import Core.PinFundamental
import Core.DelayApprox
import Core.EffCancel
import Support.Model.Tree.World.EscBeneath
import Support.Model.Tree.Port.Six34to39
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.LiteralReadings.S6_8_FundamentalProperty

/-!
# The hypothesis register  `[spec §62]`

Every named hypothesis of the library: each closed `Prop` that a theorem takes as a premise, and
the named schemas such a `Prop` is made of. Each entry names the definition (a `Name` Lean
resolves), its research question in the register of issue #1122 (`RQ1`–`RQ6`, or `none` for an
assumption that is engineering), where it stands, and the theorems that take it.

* **Assumed** (`Standing.assumed`): no proof and no refutation. `HandlerLawN` and `PinLaw` are the
  two the shipped headlines read; the others are their conjuncts and equivalents, and two
  engineering residuals that no headline reads.
* **Proved** (`Standing.proved`): a residual a theorem discharges; the theorem is named, and an
  `example` below checks it.
* **Refuted** (`Standing.refuted`): a candidate statement a theorem refutes; likewise checked.

What is proved with no hypothesis (`fundamentalC`, `adequacyC`/`adequacyD`, `goal791N_nil`) is
not listed: those theorems take none.

`scripts/check-assumptions.sh` (the sanity gate) fails on a closed `Prop` taken as a premise in
the library, or in the compiler, that this file does not list. A hypothesis whose definition lies
outside this module's imports (the checker's, under `Frontend/`) is listed in `outside` by name
and file, since `Core` cannot import it.

Nothing here states a new proposition: each entry refers to the existing definition, and each
`example` restates only the existing theorem's type.
-/

noncomputable section

namespace BoCa.Assumptions

/-- Where a registered hypothesis stands. -/
inductive Standing where
  /-- Neither proved nor refuted: a premise of the theorems that take it. -/
  | assumed
  /-- Discharged by the named theorem. -/
  | proved (byThm : Lean.Name)
  /-- Refuted by the named theorem. -/
  | refuted (byThm : Lean.Name)

/-- One registered hypothesis. -/
structure Entry where
  /-- The definition, a closed `Prop`. -/
  decl : Lean.Name
  /-- Its research question in issue #1122's register, or `none`; an open engineering debt says
  so, with its issue. -/
  rq : String
  /-- Where it stands. -/
  standing : Standing
  /-- The theorems that take it as a premise, in `Core`'s imports. -/
  takenBy : List Lean.Name
  /-- What else holds of it: an equivalence, a field it is part of, its consumers outside
  `Core`'s imports. -/
  note : String := ""

/-- One registered hypothesis whose definition lies outside `Core`'s imports. -/
structure OutsideEntry where
  /-- The definition's name, as declared. -/
  name : String
  /-- The file that declares it. -/
  file : String
  /-- Its research question, or `none`. -/
  rq : String
  /-- Where it stands, and what takes it. -/
  note : String

/-- **The register.** -/
def register : List Entry := [
  -- RQ1: a continuation that owns an open borrow is a first-class value (the chain, #791).
  { decl := ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.HandlerLawN
    rq := "RQ1"
    standing := .assumed
    takenBy := [
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.goal791N,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.prog791_orDiverges,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.CodeLoop855N.progK_orDiverges,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.meets_of_derivesN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.externN_of_rep,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.readByte_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.writeByte_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.mkInput_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.mkOutput_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.takeInput_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.takeOutput_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.writeAll_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.readInto_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.clockNow_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.clockSleep_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.mkClock_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.takeClock_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.readArg_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.mkArgs_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.takeArgs_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.stdModel_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.externsMeetN_of_model,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.externs_every_runN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.io_every_runN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.externs_loop_every_runN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.io_loop_every_runN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.IO791N.ioX_meetsN,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.IO791N.progIO_res_orDiverges,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.IO791N.progIO_can_orDiverges,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Nest844N.progRes_orDiverges,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Nest844N.progCan_orDiverges]
    note := "Fields handleV, handleVB, reify (HandleVN, HandleVBN, ReifyN). Equivalent to MissingN \
      (handlerLawN_iff). Its consumers are the chain's theorems only: goal791N and the kernel \
      programs built on the suspending-lend constants (Const791), where it is read at \
      effHandleV/effHandleVB/reify. The checker emits no Const791 constant, so no checked \
      program rests on it: a checked main rests on fundamentalC, or on fundamentalC_pin under \
      PinLaw. Frontend.Check.IORun.every_runN and IORun.loop_every_runN \
      (Frontend/Check/Externs.lean) restate the chain's run at no constants, where Core's \
      IORun.every_run already holds with no hypothesis." },
  { decl := ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.MissingN
    rq := "RQ1"
    standing := .assumed
    takenBy := [
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.fundamentalN_all,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.constNAt_all,
      ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.constN_all]
    note := "HandlerLawN as a conjunction (handlerLawN_iff)." },
  { decl := ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.HandleVN
    rq := "RQ1"
    standing := .assumed
    takenBy := []
    note := "HandlerLawN.handleV: [handle] at a value form (effHandleV)." },
  { decl := ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.HandleVBN
    rq := "RQ1"
    standing := .assumed
    takenBy := []
    note := "HandlerLawN.handleVB: BOXED-κ [handle] (effHandleVB)." },
  { decl := ``BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N.ReifyN
    rq := "RQ1"
    standing := .assumed
    takenBy := []
    note := "HandlerLawN.reify: reify_res (reify)." },
  -- RQ1 and RQ2: the relaxed lends R1 and R2 (`CDerivesP`).
  { decl := ``BoCa.Fig16.LogRel.Core.PinLaw
    rq := "RQ1, RQ2"
    standing := .assumed
    takenBy := [
      ``BoCa.Fig16.LogRel.Core.fundamentalC_pin,
      ``BoCa.Fig16.LogRel.Core.PinLaw.stop,
      ``BoCa.Fig16.LogRel.Core.PinLaw.loop,
      ``BoCa.Fig16.LogRel.Core.adequacyC_pin,
      ``BoCa.Fig16.LogRel.Core.adequacyD_pin,
      ``BoCa.Fig16.LogRel.Core.total_open_pin,
      ``BoCa.Fig16.LogRel.Core.adequacyD_pin_safe]
    note := "Fields lendFrame (LendFrame, RQ1) and loopFrame (LoopFrame, RQ2). Equivalent to \
      PinStop ∧ PinLoop (pinLaw_iff). Read only at R1 (lendR) and R2 (lendLoopR) sites, which \
      `bcc check` lists. Also taken by Frontend.Check.checked_sem_pin and checked_runs_pin \
      (Frontend/Check/Program.lean)." },
  { decl := ``BoCa.Fig16.LogRel.Core.LendFrame
    rq := "RQ1"
    standing := .assumed
    takenBy := []
    note := "PinLaw.lendFrame: the relaxed withborUV lend at every LendForm (R1)." },
  { decl := ``BoCa.Fig16.LogRel.Core.LoopFrame
    rq := "RQ2"
    standing := .assumed
    takenBy := []
    note := "PinLaw.loopFrame: the per-observation imm lend (R2)." },
  { decl := ``BoCa.Fig16.LogRel.Core.PinStop
    rq := "RQ1"
    standing := .assumed
    takenBy := [``BoCa.Fig16.LogRel.Core.PinLaw.of_stop_loop]
    note := "R1's compatibility lemma; LendFrame at ref (PinLaw.stop)." },
  { decl := ``BoCa.Fig16.LogRel.Core.PinLoop
    rq := "RQ2"
    standing := .assumed
    takenBy := [``BoCa.Fig16.LogRel.Core.PinLaw.of_stop_loop]
    note := "R2's compatibility lemma; LoopFrame (PinLaw.loop)." },
  -- Engineering residuals no headline reads.
  { decl := ``BoCa.Fig16.LogRel.Core.WpChainCommutes
    rq := "none: engineering, #180"
    standing := .assumed
    takenBy := [
      ``BoCa.Fig16.LogRel.Core.approxLim_le_delayRel,
      ``BoCa.Fig16.LogRel.Core.delayRel_iff_approxLim]
    note := "The delay type as the limit of its approximations (SPEC §7)." },
  -- Residuals a theorem discharges.
  { decl := ``BoCa.Fig16.Tree.Wp.EscBeneathT
    rq := "none"
    standing := .proved ``BoCa.Fig16.Tree.Wp.escBeneathT
    takenBy := [``BoCa.Fig16.Tree.Wp.fd_esc_of_branch] },
  { decl := ``BoCa.Fig16.ResU.SixThirtyEightResidual
    rq := "none"
    standing := .proved ``BoCa.Fig16.ResU.sixThirtyEightResidual
    takenBy := [``BoCa.Fig16.ResU.sixThirtyEight_of_residual] },
  { decl := ``BoCa.Fig16.Tree.ResUT.SixThirtyEightResidual
    rq := "none"
    standing := .proved ``BoCa.Fig16.Tree.ResUT.sixThirtyEightResidual
    takenBy := [``BoCa.Fig16.Tree.ResUT.sixThirtyEight_of_residual] },
  -- Candidate statements a theorem refutes.
  { decl := ``BoCa.Fig16.LogRel.Core.CancelIntercept.ThenAbortCompat
    rq := "none"
    standing := .refuted ``BoCa.Fig16.LogRel.Core.CancelIntercept.not_thenAbort_compatC
    takenBy := [``BoCa.Fig16.LogRel.Core.CancelIntercept.semC_thenProg] },
  { decl := ``BoCa.Fig16.LogRel.EveryDerivationInRegime
    rq := "none"
    standing := .refuted ``BoCa.Fig16.LogRel.not_everyDerivationInRegime
    takenBy := [``BoCa.Fig16.LogRel.fundamentalProperty_of] }]

/-- **The register, outside `Core`'s imports.** -/
def outside : List OutsideEntry := [
  { name := "UnmentionedAbsorbed"
    file := "Frontend/Check/Masks.lean"
    rq := "none: engineering, #746 F5"
    note := "Assumed (UNPROVED:, #746 F5). Taken by Frontend.Check.neitherAbsorbed_of; \
      SplitMasks.NeitherAbsorbed is read by Backend2's Convert and Lint." },
  { name := "KeepKripkeRun"
    file := "research/tree/ResearchTree/TreeSemObs.lean"
    rq := "none"
    note := "Refuted by BoCa.Fig16.Tree.Wp.Obs.cerwpT_not_keepKripke; taken by \
      BoCa.Fig16.Tree.Wp.Obs.keepKripkeRunNil_of. The tree archive (#1133): checked by \
      research/tree/ResearchTree/Assumptions.lean." },
  { name := "KeepKripkeRunNil"
    file := "research/tree/ResearchTree/TreeSemObs.lean"
    rq := "none"
    note := "Refuted by BoCa.Fig16.Tree.Wp.Obs.cerwpT_not_keepKripkeNil; taken by \
      BoCa.Fig16.Tree.Wp.Obs.obsE_cerwpT. The tree archive (#1133): checked by \
      research/tree/ResearchTree/Assumptions.lean." }]

/-! ### The entries' standing and premises, checked

Each `example` restates the type of an existing theorem: an assumed hypothesis's place as a
premise of a headline, and a proved or refuted entry's proof. -/

section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

example : HandlerLawN (ℍ := ℍ) → BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N (ℍ := ℍ) := goal791N
example : HandlerLawN (ℍ := ℍ) ↔ MissingN (ℍ := ℍ) := handlerLawN_iff
example : MissingN (ℍ := ℍ) = (HandleVN (ℍ := ℍ) ∧ HandleVBN (ℍ := ℍ) ∧ ReifyN (ℍ := ℍ)) := rfl
example (h : HandlerLawN (ℍ := ℍ)) : HandleVN (ℍ := ℍ) ∧ HandleVBN (ℍ := ℍ) ∧ ReifyN (ℍ := ℍ) :=
  ⟨h.handleV, h.handleVB, h.reify⟩
example (h : PinLaw (ℍ := ℍ)) : LendFrame (ℍ := ℍ) ∧ LoopFrame (ℍ := ℍ) :=
  ⟨h.lendFrame, h.loopFrame⟩
example : PinLaw (ℍ := ℍ) ↔ PinStop (ℍ := ℍ) ∧ PinLoop (ℍ := ℍ) := pinLaw_iff
example (h : PinLaw (ℍ := ℍ)) {Δ : BoCa.Lifetime.LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (d : CDerivesP Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j := fundamentalC_pin h d
example (hc : WpChainCommutes (ℍ := ℍ)) (VA : List SRec → Val → BoCa.Fig16.BoLo.WProp) :
    (approxLim VA).Le (delayRel VA) := approxLim_le_delayRel hc VA

example : BoCa.Fig16.Tree.Wp.EscBeneathT := BoCa.Fig16.Tree.Wp.escBeneathT
example : BoCa.Fig16.ResU.SixThirtyEightResidual := BoCa.Fig16.ResU.sixThirtyEightResidual
example {K : BoCa.Fig16.Tree.WCactus} : BoCa.Fig16.Tree.ResUT.SixThirtyEightResidual (K := K) :=
  BoCa.Fig16.Tree.ResUT.sixThirtyEightResidual

example : ¬ CancelIntercept.ThenAbortCompat (ℍ := ℍ) := CancelIntercept.not_thenAbort_compatC
example : ¬ BoCa.Fig16.LogRel.EveryDerivationInRegime (ℍ := ℍ) :=
  BoCa.Fig16.LogRel.not_everyDerivationInRegime
end

end BoCa.Assumptions

end
