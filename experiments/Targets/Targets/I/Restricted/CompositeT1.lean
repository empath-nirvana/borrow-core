import Core.Totality
import Core.EffPrograms
import Targets.B.BoLo
import Targets.Base.Data

/-!
# The interaction — the composite programs at tier 1 (RESTRUCTURE §3.4)

`AcceptedT1`: a closed Core program at a data answer,
typed by tier 1, every run under the empty platform safe and terminating with the memory empty.
Each `acceptedT1_*` is `acceptedT1_of_derives`, which
rests on B's `soundRetAt_tier1_none`, so they live here.  `prog`, `progC`, `nLogOutside`,
`nFailOutside` and `tickProg` are Core's encodings of A-level programs: evidence for E7, E5 and
E3.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A closed Core program at a data answer: typed by tier 1, and every run under the empty
platform safe and terminating with the memory empty. -/
def AcceptedT1 (e : Expr) (A : VTy) : Prop :=
  tier1.closed e (.ret A) ∧ SafeRuns (ℍ := ℍ) Platform.none A e ∧
    Terminates (ℍ := ℍ) Platform.none A e

/-- A closed `CDerives` derivation at a data answer is accepted. -/
theorem acceptedT1_of_derives {e : Expr} {A : VTy} (hA : A.Data)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) : AcceptedT1 (ℍ := ℍ) e A :=
  ⟨fun _ _ => h, soundRetAt_tier1_none [] A e hA (RowLe.nil _) (fun _ _ => h)⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Fig16.LogRel.Core.EffExamples

theorem acceptedT1_prog : AcceptedT1 (ℍ := ℍ) prog .unit :=
  acceptedT1_of_derives (.unit 0) prog_derives

theorem acceptedT1_progC : AcceptedT1 (ℍ := ℍ) progC .unit :=
  acceptedT1_of_derives (.unit 0) progC_derives

theorem acceptedT1_logOutside : AcceptedT1 (ℍ := ℍ) logOutside (.tensor Flag (.sum .zero .unit)) :=
  acceptedT1_of_derives (.tensor flag_data err_data) d_logOutside

theorem acceptedT1_failOutside : AcceptedT1 (ℍ := ℍ) failOutside (.sum .zero .unit) :=
  acceptedT1_of_derives err_data d_failOutside

theorem acceptedT1_reborrowRaise : AcceptedT1 (ℍ := ℍ) reborrowRaise (.sum .zero .unit) :=
  acceptedT1_of_derives err_data d_reborrowRaise

theorem acceptedT1_nLogOutside :
    AcceptedT1 (ℍ := ℍ) nLogOutside (.tensor (.sum .zero .unit) Flag) :=
  acceptedT1_of_derives (.tensor err_data flag_data) d_nLogOutside

theorem acceptedT1_nFailOutside :
    AcceptedT1 (ℍ := ℍ) nFailOutside (.sum (.tensor .zero Flag) .unit) :=
  acceptedT1_of_derives (.sum (.tensor (.zero 0) flag_data) (.unit 0)) d_nFailOutside

theorem acceptedT1_logInBorrow : AcceptedT1 (ℍ := ℍ) logInBorrow (.tensor Flag Flag) :=
  acceptedT1_of_derives (.tensor flag_data flag_data) d_logInBorrow

theorem acceptedT1_tickProg (n : ℕ) : AcceptedT1 (ℍ := ℍ) (tickProg n) .unit :=
  acceptedT1_of_derives (.unit 0) (d_tickProg n)

theorem acceptedT1_takeProg (n : ℕ) : AcceptedT1 (ℍ := ℍ) (takeProg n) Flag :=
  acceptedT1_of_derives flag_data (d_takeProg n)

theorem acceptedT1_storeCancel : AcceptedT1 (ℍ := ℍ) storeCancel .unit :=
  acceptedT1_of_derives (.unit 0) d_storeCancel

theorem acceptedT1_tickAnsProg (n : ℕ) : AcceptedT1 (ℍ := ℍ) (tickAnsProg n) Flag :=
  acceptedT1_of_derives flag_data (d_tickAnsProg n)

end Targets

end
