import Core.PinLaw
import Core.DivDefs

/-!
# Spike743 — round 3: W-tick and W-hold, as stated

* `resumeOT_tick_await`, `not_resumeO_tick_await`: the nursery's row `tick, await` is in
  `Row.ResumeOT` and not in `Row.ResumeO`: W-tick admits exactly the row `Row.ResumeO` refuses for
  the nursery (#750 round 2's `not_resumeOC_nursery`).
* `pinStop_of_tick`, `pinStopImm_of_tick`: `PinStopTick` gives `PinStop` and `PinStopImm` (at
  `k = false` and `k = true`, with `Row.ResumeO.toT`): the field widens both, and states nothing
  about rows `Row.ResumeO` already admits beyond what they do.

Nothing here is a proof of either field.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Round3
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

theorem resumeOT_tick_await (x : LifeVar) : Row.ResumeOT [tickSig, pinAwaitSig] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact .inl rfl
  · exact .inr (resumeO_await_yield x pinAwaitSig (by simp))

theorem not_resumeO_tick_await (x : LifeVar) : ¬ Row.ResumeO [tickSig, pinAwaitSig] x := by
  intro h
  have := (h tickSig (by simp)).2.2.2.1
  simp [tickSig, nextTy] at this

theorem pinStop_of_tick (h : PinStopTick (ℍ := ℍ)) : PinStop (ℍ := ℍ) :=
  fun Δ x b T B d M S hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM =>
    h Δ x b T B d M S false hb hx hbx hΔx hT hB hBn (by simpa [LendSide] using hside) hS.toE hM1 hcb
      hdc hd (by simpa [lendView] using hM)

theorem pinStopImm_of_tick (h : PinStopTick (ℍ := ℍ)) : PinStopImm (ℍ := ℍ) :=
  fun Δ x b T B d M S hb hx hbx hΔx hT hB hBn hsc hS hM1 hcb hdc hd hM =>
    h Δ x b T B d M S true hb hx hbx hΔx hT hB hBn (by simpa [LendSide] using hsc) hS.toCE.toE hM1 hcb
      hdc hd (by simpa [lendView] using hM)

end Spike743.Round3
