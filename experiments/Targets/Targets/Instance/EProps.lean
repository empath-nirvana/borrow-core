import Targets.Instance.E1Runs

/-!
# The Instance — A's (E) properties at `J₁`

* **E1, no colouring: PROVED** at every admissible effect context (`noColouring_J₁`): `hof` is
  typed once, its one typing serves a callback at every row (SPEC §26's `[λ-dead]` passes the
  callback), it calls its callback catching nothing, and E1's and E1′'s programs are typed and run
  to their answers with no event, around the capture cell of the affine `wait` (SPEC §25).
* **E7, E8, E9: FAIL AS WRITTEN** at every effect context (`Targets/Instance/FinRaise.lean`): each
  asks for a typing of a program whose finaliser raises to its context, and `[then]` types a
  finaliser at `F 1` (option A, decision D3).  So `EProps` fails as written at `J₁`
  (`not_eProps_J₁`).
* **E2, E4, E5, E6, E10** at `J₁`: `Targets/Instance/E2.lean`, `E4.lean`, `E5.lean`, `E6.lean`,
  `E10.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets (EffCtx orowRF orowAlg)

section E
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- A closed program typed at `J₁` at a returner of a data type is closed. -/
theorem closed_of_der_J₁ {M : Expr} {ε : Targets.ORow} {A : VTy}
    (hA : ∀ A₀ L, A ≠ .sum A₀ (.thunk L)) (h : (𝕁).der [] M ((𝕁).F ε (OVTy.ofV A))) :
    closedAt 0 M = true := by
  obtain ⟨-, Θ, hΘ, hd⟩ := der_core_J₁ hA h
  simpa using closedAt_of_derives (hd _ (models_anyCon_nil hΘ) (envAt_nil Ξ)).toCDerives

/-- **E1's labels** at a rich context with no resuming `unr` operation. -/
theorem labelsAt_E1 (hΞ : AdmEff Ξ) : ∃ ls, (𝕁).LabelsAt [(𝕁).sigExn, (𝕁).sigWait] ls := by
  obtain ⟨le, -, -, hle, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .zero)]) (by simp [eSigs])
  obtain ⟨lw, -, -, hlw, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .unit)]) (by simp [eSigs])
  refine ⟨[le, lw], rfl, ?_, fun k h₁ _ => ?_⟩
  · have hne : le ≠ lw := lab_ne_of_sig (by rw [hle, hlw]; simp)
    exact List.nodup_cons.mpr ⟨fun h => hne (List.mem_singleton.mp h), List.nodup_singleton _⟩
  · match k, h₁ with
    | 0, _ => exact (sig_exn_iff le).mpr ⟨.aff, hle, by decide⟩
    | 1, _ => exact (sig_wait_iff hΞ.1 lw).mpr hlw

/-- **E1, no colouring, at `J₁`**, at every admissible effect context. -/
theorem noColouring_J₁ (hΞ : AdmEff Ξ) : (𝕁).NoColouring := by
  refine ⟨labelsAt_E1 hΞ, fun ls hls le lw hlsEq => ?_⟩
  subst hlsEq
  obtain ⟨q, hle, hq⟩ := (sig_exn_iff le).mp (hls.2.2 0 (by simp) (by simp))
  have hlw := (sig_wait_iff hΞ.1 lw).mp (hls.2.2 1 (by simp) (by simp))
  refine ⟨polyTy (hofC boolT), derV_hof_J₁ boolT, polyUse_hof_J₁ hΞ.1, fun ε M hM => ?_,
    der_retTt_J₁, der_raise_J₁ hle hq boolT, der_waitTt_J₁ hlw, der_threeUses_J₁ hΞ.1 hle hq hlw,
    runsTo_noColour hle hlw, der_usesS_J₁ hΞ.1 hlw, runsTo_noColourS hlw⟩
  exact callsThrough_hof (closed_of_der_J₁ boolT_not_loop hM)

end E

end Targets.Inst

end
