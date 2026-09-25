import CBPVCore.Compat

/-!
# CBPVCore — Agreement

The typed world's relation `vX` is `vC` at the call-by-value translation, at every BoLo type
and in both modes (`vX_eq_vC_fun`).  At `⊸`/`∀` the `U` clause forces the thunk by using the
λ-value as it stands (`forceE`), so `𝒱⟦U (A ⊸ F B)⟧(v)` applies `v` itself, as `vX`'s `⊸` clause
does.  At `Imm` the preimage in `vC`'s `CohE` conjunct is unique (`cbv_injective`).

Contexts translate slotwise (`cbvCtx`), and `SemX` is `SemV` at the translation
(`semX_iff_semV`): every `_compatX` lemma of the typed world is a `SemV` fact.
-/

namespace CBPVCore
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

/-- **Agreement.**  At every BoLo type and in both modes, `vX` at the tagged `wpTS` is `vC` at
the call-by-value translation. -/
theorem vX_eq_vC_fun : ∀ (b : Bool) (T : Ty), vX wpTS b T = vC b (cbv T) := by
  intro b T
  induction T generalizing b with
  | unit => cases b <;> rfl
  | unk => cases b <;> rfl
  | sum T₁ T₂ ih₁ ih₂ => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih₁, ih₂]
  | tensor T₁ T₂ ih₁ ih₂ => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih₁, ih₂]
  | lolli T₁ T₂ ih₁ ih₂ =>
      cases b
      · rfl
      · funext ls δ v; simp only [vX, vC, cC, cbv, forceE, ih₁, ih₂]
  | ref T ih => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih]
  | bang T ih => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih]
  | imm a T ih =>
      funext ls δ v
      have hc : ∀ (ℓ : Loc) (rs : List FrameRec) (δ : LSub),
          (∃ S, cbv S = cbv T ∧ CohE rs ℓ S δ) ↔ CohE rs ℓ T δ :=
        fun ℓ rs δ => ⟨fun ⟨S, hS, h⟩ => cbv_injective hS ▸ h, fun h => ⟨T, rfl, h⟩⟩
      cases b <;> simp only [vX, vC, cbv, ih, hc]
  | «mut» a T ih => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih]
  | box a T ih => funext ls δ v; cases b <;> simp only [vX, vC, cbv, ih]
  | all x c T ih =>
      cases b
      · rfl
      · funext ls δ v; simp only [vX, vC, cC, cbv, forceE, ih]

theorem vP_eq_vC (T : Ty) : vP T = vC true (cbv T) := vX_eq_vC_fun true T

/-- `Γ⁺`: the slotwise translation of a BoLo context. -/
def cbvCtx (Γ : Ctx Ty) : Ctx VTy := Γ.map fun s => ⟨cbv s.ty, s.live⟩

@[simp] theorem cbvCtx_nil : cbvCtx [] = [] := rfl
@[simp] theorem cbvCtx_cons (s : Slot Ty) (Γ : Ctx Ty) :
    cbvCtx (s :: Γ) = ⟨cbv s.ty, s.live⟩ :: cbvCtx Γ := rfl

theorem gSepX_eq_gSepC (ls : List SRec) (δ : LSub) :
    ∀ (Γ : Ctx Ty) (γ : List Val), gSepX ls δ Γ γ = gSepC ls δ (cbvCtx Γ) γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      rw [cbvCtx_cons]
      simp only [gSepX, gSepC, gSepX_eq_gSepC ls δ Γ γ, vP_eq_vC]

theorem liveWithin_cbvCtx : ∀ (Γ : Ctx Ty) (γ : List Val),
    Ctx.LiveWithin (cbvCtx Γ) γ ↔ Ctx.LiveWithin Γ γ
  | [], γ => by simp
  | s :: Γ, [] => by
      rw [cbvCtx_cons, Ctx.liveWithin_cons_nil, Ctx.liveWithin_cons_nil, liveWithin_cbvCtx Γ []]
  | s :: Γ, v :: γ => by
      rw [cbvCtx_cons, Ctx.liveWithin_cons, Ctx.liveWithin_cons, liveWithin_cbvCtx Γ γ]

theorem gDenX_eq_gDenC (ls : List SRec) (δ : LSub) (Γ : Ctx Ty) (γ : List Val) :
    gDenX ls δ Γ γ = gDenC ls δ (cbvCtx Γ) γ := by
  unfold gDenX gDenC
  rw [gSepX_eq_gSepC, propext (liveWithin_cbvCtx Γ γ)]

/-- **Transfer.**  `SemX` is `SemV` at the translation. -/
theorem semX_iff_semV (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) :
    SemX Δ Γ e T ↔ SemV Δ (cbvCtx Γ) e (cbv T) := by
  have hv : ∀ δ, (fun ls' => vP T ls' δ) = (fun ls' => vC true (cbv T) ls' δ) :=
    fun δ => funext fun ls' => by rw [vP_eq_vC]
  simp only [SemX, SemV, SemC, cC, gDenX_eq_gDenC, hv]

/-- A closed typed-world fact, at any consumed CBPV context. -/
theorem semV_of_semX_nil {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T : Ty} (hΓ : Ctx.Dead Γ)
    (h : SemX Δ [] e T) : SemV Δ Γ e (cbv T) :=
  semC_dead Ctx.Dead.nil hΓ ((semX_iff_semV Δ [] e T).mp h)

/-! ### The payloads outside the translation's image

`vC`'s `Imm` clause reads `CohE` at a preimage.  At a payload no BoLo type translates to, the
clause holds at no resource: such an `Imm @a A` is empty. -/

theorem vC_imm_outside_image {A : VTy} (hA : ∀ T, cbv T ≠ A) (b : Bool) (a : Lifetime.Life)
    (ls : List SRec) (δ : LSub) (v : Val) (ρ : WRes) : ¬ vC b (.imm a A) ls δ v ρ := by
  cases b <;>
  · rintro ⟨_, _, _, _, _, _, ⟨_, _, T, hT, _⟩, _⟩
    exact hA T hT

theorem cbv_ne_zero (T : Ty) : cbv T ≠ .zero := by cases T <;> simp [cbv]
theorem cbv_ne_thunk_ret (T : Ty) (A : VTy) : cbv T ≠ .thunk (.ret A) := by cases T <;> simp [cbv]
theorem cbv_ne_thunk_amp (T : Ty) (C D : CTy) : cbv T ≠ .thunk (.amp C D) := by
  cases T <;> simp [cbv]
theorem cbv_ne_thunk_top (T : Ty) : cbv T ≠ .thunk .top := by cases T <;> simp [cbv]
/-- A curried computation arrow: BoLo's curried `⊸` translates to `U (A ⊸ F (U (B ⊸ F C)))`. -/
theorem cbv_ne_thunk_arr_arr (T : Ty) (A B : VTy) (C : CTy) :
    cbv T ≠ .thunk (.arr A (.arr B C)) := by cases T <;> simp [cbv]

end
end CBPVCore
