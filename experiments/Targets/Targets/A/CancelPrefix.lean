import Targets.A.Soundness

/-!
# System A — S5's traces, read prefix-closed (a candidate restatement)

S5 (`Cancellation`, `Targets/A/Soundness.lean`) says that every run from the start of a cancel or
an unwind follows a trace, and its traces' docstring says that "a trace may stop anywhere".  The
definitions stop a trace only at `[]` (`CancelTrace.stop`, `UnwindTrace.stop`, `FinTrace.running`,
`PendTrace.running`), and the fire step's constructor reads the administrative steps after the fire
whole: `fire` asks `PurePath c₁ q₀ c₂` and the finaliser at `c₂`.  So at an instance whose fire step
is followed by administrative steps before the finaliser starts, a path that stops between them
follows no trace.  Our instance is one: `[finalise]` leaves `D ()`, one β-step from `D`
(`Targets/I/S5J1.lean`, `not_unwindOrder_J₁`).

The readings here ask each run to be a prefix of a trace: some continuation of the path, itself a
path, follows the trace.  They are a candidate restatement of S5, not S5; whether S5 is restated is
the user's call.  The target implies them (`unwindOrderPfx_of`, `noInterceptPfx_of`,
`cancellationPfx_of`).
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-- **S5's no-interception, prefix-closed**: as `NoIntercept`, with every path a prefix of a cancel
trace. -/
def NoInterceptPfx (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c₀ c : S.RConf R) K₀ l H K q, S.RReach R (S.rinit R e) c₀ →
      S.term c₀.1 = S.plug K₀ (S.cancel (S.capture l H K)) →
      S.PureSteps c₀.1 c.1 → c.2 = c₀.2 → S.term c.1 = S.plug K₀ (S.cancelOf l H K) →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → ∃ q', S.RPath R c (q ++ q') ∧
        S.CancelTrace R FR (S.Region l K) K₀ c (S.fins K) none (q ++ q')

/-- **S5's unwind, prefix-closed**: as `UnwindOrder`, with every path a prefix of an unwind
trace. -/
def UnwindOrderPfx (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c : S.RConf R) K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → ∃ q', S.RPath R c (q ++ q') ∧ S.UnwindTrace R FR K₀ c K (q ++ q')

/-- **S5, prefix-closed.** -/
def CancellationPfx (FR : S.EA.Lab → Prop) : Prop := S.NoInterceptPfx FR ∧ S.UnwindOrderPfx FR

variable {S}

/-- The target implies its prefix-closed reading. -/
theorem noInterceptPfx_of {FR : S.EA.Lab → Prop} (h : S.NoIntercept FR) : S.NoInterceptPfx FR :=
  fun R hR e ε A hA he c₀ c K₀ l H K q hreach h₀ hps hs hc hfin hq =>
    ⟨[], by simpa using hq, by simpa using h R hR e ε A hA he c₀ c K₀ l H K q hreach h₀ hps hs hc hfin hq⟩

theorem unwindOrderPfx_of {FR : S.EA.Lab → Prop} (h : S.UnwindOrder FR) : S.UnwindOrderPfx FR :=
  fun R hR e ε A hA he c K₀ K m j w q hreach hK hc hm hfin hq =>
    ⟨[], by simpa using hq, by simpa using h R hR e ε A hA he c K₀ K m j w q hreach hK hc hm hfin hq⟩

theorem cancellationPfx_of {FR : S.EA.Lab → Prop} (h : S.Cancellation FR) : S.CancellationPfx FR :=
  ⟨noInterceptPfx_of h.1, unwindOrderPfx_of h.2⟩

end EffectSystem

end Targets.A
