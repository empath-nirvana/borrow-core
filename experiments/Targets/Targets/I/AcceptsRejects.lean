import Targets.I.J1
import Targets.I.Rejects
import Targets.Base.LookMem
import Targets.Instance.FinRaise

/-!
# The interaction — the composite's programs and rejections at `J₁` (decision AR)

`J₁`'s reading is Core's kernel (`Inst.j1_read`), so both conjuncts are about `CDerives`.

**`Accepts J₁.read .abortive`** is `CompositeT1 tier1` (the tier-2 conjunct is empty at
`.abortive`): each of the eight programs is typed by Core's kernel at its data answer, every run under
the empty platform is safe and terminates with the memory empty (`acceptedT1_*`, from B's
`soundRetAt_tier1_none`), and one complete run answers the stated value.  That run is computed:
`runM` (`Targets/Base/LookMem.lean`) steps the program from the empty memory, `look` deciding the steps
that keep the memory and `memOp` the memory steps, and the kernel evaluates it to the answer at the
empty list (`run_*`, by `rfl`).  `runM_sound` makes it a run of Core's machine, hence a run under the
empty platform (`prun_of_steps`).

**`Rejects J₁.read`** is `Rej.rejects_tier1` (`Targets/I/Rejects.lean`): AT05, AT06, AT08 and AT13
have no derivation in Core's kernel, at any context and judgement.

**Tier 1 at `J₁`** follows from A's (E) properties, S4, S5 and S6 at every admissible effect context
(`tier1_J₁_of_ESU`).  S4 is proved at every effect context (`I.handlerSem_J₁`, the capture cell's
catch law), so it follows from (E), S5 and S6 (`tier1_J₁_of_ECU`).  (E) fails as written at `J₁`
under option A (E7–E9), so tier 1 does (`not_tier1_J₁`); S5 fails as written too, and S6 is open
(`Targets/Status.lean`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag logOutside failOutside reborrowRaise logInBorrow
  tickAnsProg takeProg storeCancel)
open Targets.Inst (ourInst AdmEff J₁)

/-- **A machine run is a run under the empty platform**, as the list of its configurations, ending
at the run's end. -/
theorem prun_of_steps (s : Platform.none.St) {μ μ' : Heap} {e e' : Expr}
    (h : Steps (ℍ := ℍ) μ e μ' e') :
    ∃ cs c, PRun (ℍ := ℍ) Platform.none (⟨μ, e, s⟩ :: cs) ∧ (⟨μ, e, s⟩ :: cs).getLast? = some c ∧
      c = ⟨μ', e', s⟩ := by
  induction h with
  | refl μ e => exact ⟨[], _, .one _, rfl, rfl⟩
  | more h _ ih =>
      obtain ⟨cs, c, hr, hl, hc⟩ := ih
      refine ⟨_ :: cs, c, .cons (PStep.mach h) hr, ?_, hc⟩
      rw [List.getLast?_cons_cons]
      exact hl

/-- **Accepted with its answer**, from tier 1's acceptance and a computed run from the empty memory
to the answer at the empty memory. -/
theorem acceptedAt_of_runM {e : Expr} {A : VTy} {v : Val} (hA : AcceptedT1 (ℍ := ℍ) e A)
    (k : ℕ) (hr : runM k [] e = ([], v.1)) (hD : DataVal A v) :
    AcceptedAt (ℍ := ℍ) tier1 e A v := by
  obtain ⟨hJ, hS, hT⟩ := hA
  have hs := runM_sound (ℍ := ℍ) k [] e
  rw [hr] at hs
  obtain ⟨cs, c, hrun, hl, rfl⟩ := prun_of_steps (ℍ := ℍ) Platform.none.s₀ hs
  exact ⟨hJ, hS, hT, cs, _, hrun, hl, ⟨v, rfl, hD, rfl⟩, rfl⟩

/-! ### The eight runs, computed -/

theorem run_logOutside :
    runM 100 [] logOutside = ([], (Val.pair (Val.inj₂ .unit) (Val.inj₂ .unit)).1) := by rfl

theorem run_failOutside : runM 100 [] failOutside = ([], (Val.inj₂ .unit).1) := by rfl

theorem run_logInBorrow :
    runM 100 [] logInBorrow = ([], (Val.pair (Val.inj₂ .unit) (Val.inj₂ .unit)).1) := by rfl

theorem run_reborrowRaise : runM 100 [] reborrowRaise = ([], (Val.inj₂ .unit).1) := by rfl

set_option maxRecDepth 20000 in
theorem run_tickAnsProg : runM 200 [] (tickAnsProg 3) = ([], (Val.inj₂ .unit).1) := by rfl

theorem run_takeProg1 : runM 100 [] (takeProg 1) = ([], (Val.inj₂ .unit).1) := by rfl

theorem run_takeProg5 : runM 100 [] (takeProg 5) = ([], (Val.inj₁ .unit).1) := by rfl

theorem run_storeCancel : runM 100 [] storeCancel = ([], Val.unit.1) := by rfl

/-! ### The composite at tier 1, and `Accepts` at `J₁` -/

theorem flag_inj₁ : DataVal Flag (Val.inj₁ .unit) := .inj₁ .unit

theorem flag_inj₂ : DataVal Flag (Val.inj₂ .unit) := .inj₂ .unit

theorem err_inj₂ : DataVal (.sum .zero .unit) (Val.inj₂ .unit) := .inj₂ .unit

/-- **The tier-1 composite at Core's kernel**: each program typed at its data answer, safe and
terminating under the empty platform, and one complete run answering the stated value. -/
theorem compositeT1_tier1 : I.CompositeT1 (ℍ := ℍ) tier1 :=
  ⟨acceptedAt_of_runM acceptedT1_logOutside 100 run_logOutside (.pair flag_inj₂ err_inj₂),
    acceptedAt_of_runM acceptedT1_failOutside 100 run_failOutside err_inj₂,
    acceptedAt_of_runM acceptedT1_logInBorrow 100 run_logInBorrow (.pair flag_inj₂ flag_inj₂),
    acceptedAt_of_runM acceptedT1_reborrowRaise 100 run_reborrowRaise err_inj₂,
    acceptedAt_of_runM (acceptedT1_tickAnsProg 3) 200 run_tickAnsProg flag_inj₂,
    acceptedAt_of_runM (acceptedT1_takeProg 1) 100 run_takeProg1 flag_inj₂,
    acceptedAt_of_runM (acceptedT1_takeProg 5) 100 run_takeProg5 flag_inj₁,
    acceptedAt_of_runM acceptedT1_storeCancel 100 run_storeCancel .unit⟩

/-- **`Accepts` at `J₁`** (decision AR): `J₁`'s reading is Core's kernel (`Inst.j1_read`), and at
`.abortive` the tier-2 conjunct asks nothing. -/
theorem I.accepts_J₁ : I.Accepts (ℍ := ℍ) J₁.read .abortive := by
  rw [Inst.j1_read]
  exact ⟨compositeT1_tier1, fun h => by cases h⟩

/-- **`Rejects` at `J₁`** (decision AR): AT05, AT06, AT08 and AT13 have no type in Core's kernel. -/
theorem I.rejects_J₁ : Rejects J₁.read := by
  rw [Inst.j1_read]
  exact Rej.rejects_tier1

/-- **The rejections at the tied kernel**: at every effect context, a tied derivation is Core's
(`CDerivesAt.toCDerives`), so AT05, AT06, AT08 and AT13 have none either. -/
theorem I.rejects_tied (Ξ : EffCtx) {Δ : BoCa.Lifetime.LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ at05 j ∧ ¬ CDerivesAt Ξ Δ Γ at06 j ∧ ¬ CDerivesAt Ξ Δ Γ at08 j ∧
      ¬ CDerivesAt Ξ Δ Γ at13 j :=
  ⟨fun h => Rej.not_der_at05 h.toCDerives, fun h => Rej.not_der_at06 h.toCDerives,
    fun h => Rej.not_der_at08 h.toCDerives, fun h => Rej.not_der_at13 h.toCDerives⟩

/-- **Tier 1 at `J₁`, given A's (E) properties, S4, S5 and S6 at every admissible effect context**:
`tier1_J₁_of` with the composite's programs and rejections discharged. -/
theorem I.tier1_J₁_of_ESU
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hS4 : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of hE hS4 hC hU I.accepts_J₁ I.rejects_J₁

/-- **Tier 1 at `J₁`, given A's (E) properties, S5 and S6 at every admissible effect context**: S4
is proved at every effect context (`I.handlerSem_J₁`, the capture cell's catch law), and `Accepts`
and `Rejects` (decision AR). -/
theorem I.tier1_J₁_of_ECU
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv) :
    I.Tier1 (ℍ := ℍ) J₁ :=
  I.tier1_J₁_of_ESU hE (fun _ _ => I.handlerSem_J₁) hC hU

/-- **Tier 1 at `J₁` FAILS AS WRITTEN**: its A conjunct asks A's (E) properties at every admissible
effect context, and E7, E8 and E9 fail at `J₁` at every effect context under option A
(`Inst.not_eProps_J₁`); its S5 hypothesis fails as written too (`I.not_cancellation_admissible`).
S4 holds at every effect context (`I.handlerSem_J₁`). -/
theorem I.not_tier1_J₁ : ¬ I.Tier1 (ℍ := ℍ) J₁ := fun h =>
  Inst.not_eProps_J₁ (h.1 Inst.ΞA Inst.admEff_ΞA).2

end Targets

end
