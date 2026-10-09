import Targets.A.Soundness

/-!
# System A — S5 read whole (kept as a record)

S5 (`Cancellation`, `Targets/A/Soundness.lean`) reads every run from the start of a cancel or of an
unwind as a prefix of a trace.  Read whole, every such run is itself a trace.  A trace stops only
where its constructors stop it (`CancelTrace.stop`, `UnwindTrace.stop`, `FinTrace.running`,
`PendTrace.running`), and the fire step's constructor reads the administrative steps after the fire
whole: `fire` asks `PurePath c₁ q₀ c₂` and the finaliser at `c₂`.  So at an instance whose fire step
is followed by administrative steps before the finaliser starts, a run that stops between them
follows no trace.  Our instance is one: `[finalise]` leaves `D ()`, one β-step from `D`
(`Targets/I/S5J1.lean`, `not_unwindOrderWhole_J₁`).

The whole reading implies S5 (`noIntercept_of_whole`, `unwindOrder_of_whole`,
`cancellation_of_whole`).
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-- **S5's no-interception, read whole**: as `NoIntercept`, with every run from the cancel's start a
cancel trace. -/
def NoInterceptWhole (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c₀ c : S.RConf R) K₀ l H K q, S.RReach R (S.rinit R e) c₀ → S.CancelStart c₀ c K₀ l H K →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → S.CancelTrace R FR K₀ c (S.acts K) none q

/-- **S5's unwind, read whole**: as `UnwindOrder`, with every run from the raise an unwind
trace. -/
def UnwindOrderWhole (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c : S.RConf R) K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → S.UnwindTrace R FR K₀ c K q

/-- **S5, read whole.** -/
def CancellationWhole (FR : S.EA.Lab → Prop) : Prop :=
  S.NoInterceptWhole FR ∧ S.UnwindOrderWhole FR

variable {S}

/-- The whole reading implies S5: a run that is a trace is a prefix of one. -/
theorem noIntercept_of_whole {FR : S.EA.Lab → Prop} (h : S.NoInterceptWhole FR) :
    S.NoIntercept FR :=
  fun R hR e ε A hA he c₀ c K₀ l H K q hreach hst hfin hq =>
    ⟨[], by simpa using hq, by simpa using h R hR e ε A hA he c₀ c K₀ l H K q hreach hst hfin hq⟩

theorem unwindOrder_of_whole {FR : S.EA.Lab → Prop} (h : S.UnwindOrderWhole FR) :
    S.UnwindOrder FR :=
  fun R hR e ε A hA he c K₀ K m j w q hreach hK hc hm hfin hq =>
    ⟨[], by simpa using hq, by simpa using h R hR e ε A hA he c K₀ K m j w q hreach hK hc hm hfin hq⟩

theorem cancellation_of_whole {FR : S.EA.Lab → Prop} (h : S.CancellationWhole FR) :
    S.Cancellation FR :=
  ⟨noIntercept_of_whole h.1, unwindOrder_of_whole h.2⟩

end EffectSystem

end Targets.A
