import Targets.Restricted.Soundness

/-!
# Targets — the existing effect programs against T1's restricted instance (DESIGN §9 item 20)

Every closed effect program of `Core/EffPrograms.lean` and `Core/EffExamples.lean` typed at a data
answer is `AcceptedT1`: typed by tier 1, and every run under the platform with no operation safe
and terminating with the memory empty (`acceptedT1_of_derives`, from
`soundRetAt_tier1_none`).  The programs handle every operation they perform, raise through
finaliser frames, cancel continuations that hold cells, and lend cells across operations, so they
are the non-vacuity witnesses of T1's restricted instance.  `[prog]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Fig16.LogRel.Core.EffExamples

theorem flag_data : VTy.Data Flag := .sum (.unit 0) (.unit 0)

theorem err_data : VTy.Data (.sum .zero .unit) := .sum (.zero 0) (.unit 0)

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
