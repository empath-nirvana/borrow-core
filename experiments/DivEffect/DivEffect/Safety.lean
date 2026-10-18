import DivEffect.Then
import Core.Demonic
import Core.Totality

/-!
# DivEffect — a closed program at the row `{Div}`  (§4.1, unknown 1, items 3 and 6)

**Item 3, the fuel form** (`fuel_every_run`), as `externs_loop_every_run` is for `main`'s loop
today: a closed program `M` at `F_{Div} A`, for every `n`, driven by `div_fuel n`: every run of
`div_fuel n M` from the empty memory, under every allocator, continues to a value at the empty
memory.  So no prefix of such a run is stuck.  `fuel_total` and Core's `theorem32D`.

**Item 3, the runtime's clause** (`runtime_every_run`, `Runtime.lean`): the same for `hnd_d H_rt M`,
`H_rt`'s clause `κ next`: every prefix of every run is an answer or steps.

**Item 6** (`total_every_run_unchanged`): Core's `total_every_run` at a closed computation of
`F A`, restated with no change.  Its row is empty, so `cwp` never applies.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem rowTab_nil (δ : LSub) : Row.tab ([] : Row) δ = OpTab.empty := by
  funext n i; simp [Row.tab, Row.find, OpTab.empty]

/-- **Every run of `div_fuel n M`** for a closed `M` at `F_{Div} A`, `A` persistent, under every
allocator, continues to a value of `A` at the empty memory.  (§4.1 unknown 1 item 3, the fuel
form.) -/
theorem fuel_every_run {M : Expr} {d : UInt32} {A : VTy} (hA : A.Persistent)
    (h : SemD LifeCtx.empty [] M d [] A) (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (fuelE d n M) μ₁ e₁) :
    ∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true A ls δ v PMap.empty := by
  have hc := h LSub.empty [] [] PMap.empty (models_empty_any _) (gDenC_nil _ _)
  rw [show substAll [] M = M from Adequacy.psub_nil 0 M] at hc
  have hTd : ∀ i, Row.tab ([] : Row) LSub.empty d i = none := fun i => by
    rw [rowTab_nil]; rfl
  have hPC : (Row.tab ([] : Row) LSub.empty).PlainCancel := Row.tab_plainCancel _ _
  have he := fuel_total hTd hPC n hc
  rw [rowTab_nil] at he
  have hwp := ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ h => (opTable_empty h).elim) (fun _ _ _ h => h) he)
  have hwp' : wpTS [] (fuelE d n M)
      (fun _ v => Fig16.BoLo.pure (∃ ls δ, vC true A ls δ v PMap.empty)) PMap.empty := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty hwp
    obtain rfl := vP_empty_of_persistent hA hv
    exact ⟨rfl, ls, LSub.empty, hv⟩
  exact theorem32D _ _ hwp' hs

/-- **Item 6**: Core's `total_every_run`, its statement unchanged. -/
theorem total_every_run_unchanged {e : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    ∃ (μ' : Heap) (v : Val), Steps (ℍ := ℍ) μ₁ e₁ μ' (.val v) :=
  total_every_run h hs

end BoCa.Fig16.LogRel.Core.DivEffect

end
