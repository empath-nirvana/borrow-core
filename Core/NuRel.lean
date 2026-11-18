import Core.Compatibility
import Core.DivWp

/-!
# Core — the relation at `νX. C`  `[spec §7]`

`cC`'s `nu` clause is, at a positive body (`CTy.NuOk`), the greatest fixed point `nuRel` of
`nuF C δ`: one unfolding of the observation tree `C` with the candidate `R` for `U X`
(`cB`, `nuEnv`).  `nuF` is monotone in the candidate (`nuF_mono`, from `wpTS_mono` and
`vCE_mono_at`: a polynomial `X` is outside every `Mut` payload), so the greatest fixed point is a fixed point
(`nuRel_out`, `nuRel_roll`).  At the relation itself one unfolding is `cC` at the unrolling
`C[U(νX. C)/X]` (`cB_unroll`), so `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` (`cC_nu_iff`).  Under a `∀` leaf
the tree is read at an extension of `δ` while the candidate stays at `δ`; the two agree on
`νX. C` because no leaf binder is free in `C` (`CTy.NuOk`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- One unfolding of `νX. C` at the candidate `R`. -/
def nuF (C : CTy) (δ : LSub) (R : CPred) : CPred := fun ls e => cB (some (nuEnv C R)) C ls δ e

/-- `⟦νX. C⟧ = ⋃{R | R ⊆ nuF C δ R}`. -/
def nuRel (C : CTy) (δ : LSub) : CPred := fun ls e ρ => ∃ R : CPred, R.Le (nuF C δ R) ∧ R ls e ρ

/-- At a positive shape, `cC (νX. C)` is `nuRel`. -/
theorem cC_nu_eq {C : CTy} (hC : C.NuShape) (δ : LSub) :
    (fun ls e => cC (.nu C) ls δ e) = nuRel C δ := by
  funext ls e ρ
  exact propext ⟨fun h => h hC, fun h _ => h⟩

theorem nuP_mono {R R' : CPred} (h : R.Le R') :
    ∀ b ls v ρ, nuP R b ls v ρ → nuP R' b ls v ρ
  | true, _, _, _, hv => fun ls' hk => h _ _ _ (hv ls' hk)
  | false, _, _, _, _ => trivial

/-- The answer relation of an effectful observation is monotone in the candidate. -/
theorem effRetE_mono (C : CTy) {R R' : CPred} (h : R.Le R') :
    ∀ {D : CTy}, D.EffLeaf → ∀ (δ : LSub) (ls : List SRec) (v : Val),
      Entails (effRetE (some (nuEnv C R)) D δ ls v) (effRetE (some (nuEnv C R')) D δ ls v)
  | .ret A, hA, δ, ls, v =>
      vCE_mono_at A 0 _ _ (VTy.noMut_of_poly hA) (fun n => by cases n <;> rfl)
        (fun n hn => by
          cases n with
          | zero => exact absurd rfl hn
          | succ n => rfl)
        (nuP_mono h) true ls δ v
  | .eff _ _ _ _ _ _ _ D, hD, δ, ls, v => effRetE_mono C h (D := D) hD.2.2 δ ls v

/-- One unfolding of an observation tree is monotone in the candidate. -/
theorem cB_mono (C : CTy) {R R' : CPred} (h : R.Le R') :
    ∀ {D : CTy}, D.NuLeaf → ∀ (ls : List SRec) (δ : LSub) (e : Expr),
      Entails (cB (some (nuEnv C R)) D ls δ e) (cB (some (nuEnv C R')) D ls δ e)
  | .ret A, hA, ls, δ, e => wpTS_mono (fun ls' w =>
      vCE_mono_at A 0 _ _ (VTy.noMut_of_poly hA) (fun n => by cases n <;> rfl)
        (fun n hn => by
          cases n with
          | zero => exact absurd rfl hn
          | succ n => rfl)
        (nuP_mono h) true ls' δ w)
  | .amp D₁ D₂, hD, ls, δ, e => fun ρ ⟨h₁, h₂⟩ =>
      ⟨cB_mono C h hD.1 ls δ _ ρ h₁, cB_mono C h hD.2 ls δ _ ρ h₂⟩
  | .eff n i q A B fin _ D, hD, ls, δ, e => fun ρ h' =>
      effWp_post (fun ls' v σ hv => effRetE_mono C h (D := D) hD.2.2 δ ls' v σ hv) h'
  | .arr _ D, hD, ls, δ, e => fun ρ h' v ρ₁ ρ₂ hv hc =>
      cB_mono C h (D := D) hD.2 ls δ _ ρ₂ (h' v ρ₁ ρ₂ hv hc)
  | .all x _ D, hD, ls, δ, e => fun ρ h' α ρ₁ ρ₂ hα hc =>
      cB_mono C h (D := D) hD ls (δ.extend x α) _ ρ₂ (h' α ρ₁ ρ₂ hα hc)

theorem nuF_mono {C : CTy} (hC : C.NuShape) (δ : LSub) {R R' : CPred} (h : R.Le R') :
    (nuF C δ R).Le (nuF C δ R') := by
  cases C with
  | amp C₁ C₂ => exact fun ls e => cB_mono _ h (D := .amp C₁ C₂) hC ls δ e
  | _ => exact hC.elim

/-- Coinduction. -/
theorem nuRel_coind {C : CTy} {δ : LSub} {R : CPred} (hR : R.Le (nuF C δ R)) :
    R.Le (nuRel C δ) :=
  fun _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem nuRel_out {C : CTy} (hC : C.NuShape) (δ : LSub) : (nuRel C δ).Le (nuF C δ (nuRel C δ)) := by
  rintro ls e ρ ⟨R, hR, h⟩
  exact nuF_mono hC δ (nuRel_coind hR) ls e ρ (hR ls e ρ h)

/-- `roll`. -/
theorem nuRel_roll {C : CTy} (hC : C.NuShape) (δ : LSub) : (nuF C δ (nuRel C δ)).Le (nuRel C δ) :=
  nuRel_coind (nuF_mono hC δ (nuRel_out hC δ))

/-- `cC (νX. C)` is one unfolding of `C` at `cC (νX. C)`. -/
theorem cC_nu_unfold {C : CTy} (hC : C.NuShape) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.nu C) ls δ e ρ ↔ nuF C δ (fun ls e => cC (.nu C) ls δ e) ls e ρ := by
  rw [cC_nu_eq hC δ]
  exact ⟨fun h => nuRel_out hC δ ls e ρ (h hC), fun h _ => nuRel_roll hC δ ls e ρ h⟩

/-- The variable `U X` at `cC (νX. C)` is `𝒱⟦U(νX. C)⟧`: the environment `nuEnv` is the
substitution `[U(νX. C)/X]`. -/
theorem vCE_nuEnv (C : CTy) (δ : LSub) (b : Bool) (A : VTy) (ls : List SRec) :
    vCE (some (nuEnv C (fun ls e => cC (.nu C) ls δ e))) b A ls δ
      = vC b (VTy.inst (.thunk (.nu C)) A) ls δ := by
  rw [vC_eq_some, VTy.inst, vCE_subst]
  congr 2
  funext n
  cases n with
  | zero =>
      refine TEnt.ext' (VTy.subst_id _).symm ?_
      funext b ls v
      cases b <;> rfl
  | succ n => rfl

/-- `vCE_nuEnv` with the candidate at `δ₀` and the type read at `δ`, the two agreeing on the free
variables of `νX. C`. -/
theorem vCE_nuEnv_at (C : CTy) {δ₀ δ : LSub} (hag : ∀ y, CFree y C → δ₀.find? y = δ.find? y)
    (b : Bool) (A : VTy) (ls : List SRec) :
    vCE (some (nuEnv C (fun ls e => cC (.nu C) ls δ₀ e))) b A ls δ
      = vC b (VTy.inst (.thunk (.nu C)) A) ls δ := by
  have : (fun ls e => cC (.nu C) ls δ₀ e) = (fun ls e => cC (.nu C) ls δ e) := by
    funext ls e; rw [cC_congr (.nu C) hag ls]
  rw [this, vCE_nuEnv]

theorem effTab_instT (S : VTy) (δ : LSub) : ∀ D : CTy, effTab (D.instT S) δ = effTab D δ
  | .eff n i q A B fin _ D => by simp only [CTy.instT, effTab, effTab_instT S δ D]
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nuSys _ _ _ => by simp [CTy.instT, effTab]

/-- The answer of an effectful observation at `cC (νX. C)` is `𝒱⟦·⟧` at the unrolling, the
candidate at `δ₀` and the answer read at `δ`, agreeing on the free variables of `νX. C`. -/
theorem effRetE_unroll (C : CTy) {δ₀ δ : LSub} (hag : ∀ y, CFree y C → δ₀.find? y = δ.find? y) :
    ∀ {D : CTy}, D.EffLeaf →
    effRetE (some (nuEnv C (fun ls e => cC (.nu C) ls δ₀ e))) D δ
      = effRet (D.instT (.thunk (.nu C))) δ
  | .ret A, _ => by
      funext ls v
      simp only [effRetE, effRet, CTy.instT, vCE_nuEnv_at C hag]
  | .eff _ _ _ _ _ _ _ D, hD => by
      simp only [effRetE, effRet, CTy.instT]
      exact effRetE_unroll C hag (D := D) hD.2.2

/-- **One unfolding at `cC (νX. C)` is `cC` at the unrolling**, the candidate at `δ₀` and the
tree read at `δ`, agreeing on the free variables of `νX. C`.  Under a `∀'x` leaf the tree is
read at `δ[x ↦ α]`, which still agrees with `δ₀` on `νX. C` because `'x` is not free in `C`. -/
theorem cB_unroll (C : CTy) (δ₀ : LSub) : ∀ {D : CTy}, D.NuLeaf →
    (∀ x, D.LeafBinds x → ¬ CFree x C) → ∀ (δ : LSub),
    (∀ y, CFree y C → δ₀.find? y = δ.find? y) → ∀ (ls : List SRec),
    cB (some (nuEnv C (fun ls e => cC (.nu C) ls δ₀ e))) D ls δ
      = cC (D.instT (.thunk (.nu C))) ls δ
  | .ret A, _, _, δ, hag, ls => by
      funext e
      show wpTS ls e (fun ls'' => vCE _ true A ls'' δ)
        = wpTS ls e (fun ls'' => vC true (VTy.inst _ A) ls'' δ)
      simp only [vCE_nuEnv_at C hag]
  | .amp D₁ D₂, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (cB _ D₁ ls δ _ ρ ∧ cB _ D₂ ls δ _ ρ)
        = (cC (D₁.instT _) ls δ _ ρ ∧ cC (D₂.instT _) ls δ _ ρ)
      rw [cB_unroll C δ₀ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag ls,
        cB_unroll C δ₀ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag ls]
  | .eff n i q A B fin rc D, hD, _, δ, hag, ls => by
      funext e
      show effWp _ _ _ ls e = effWp _ _ _ ls e
      rw [effRetE_unroll C hag (D := D) hD.2.2, ← effTab_instT (.thunk (.nu C)) δ D,
        ← CTy.divAt_instT (.thunk (.nu C)) (.eff n i q A B fin rc D)]
      rfl
  | .arr A D, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (∀ v, (vC true A ls δ v ─⋆ cB _ D ls δ (.app e (.val v))) ρ)
        = (∀ v, (vC true A ls δ v ─⋆ cC (D.instT _) ls δ (.app e (.val v))) ρ)
      rw [cB_unroll C δ₀ hD.2 hfr δ hag ls]
  | .all x c D, hD, hfr, δ, hag, ls => by
      funext e ρ
      have hag' : ∀ α, ∀ y, CFree y C → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (find?_extend_ne δ α hxy).symm
      show (∀ α, (⌜LtLife δ c α⌝ ─⋆ cB _ D ls (δ.extend x α) (.app e (.val .unit))) ρ)
        = (∀ α, (⌜LtLife δ c α⌝ ─⋆ cC (D.instT _) ls (δ.extend x α) (.app e (.val .unit))) ρ)
      refine propext (forall_congr' fun α => ?_)
      rw [cB_unroll C δ₀ (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) (hag' α) ls]
  | .top, hD, _, _, _, _ | .nuSys _ _ _, hD, _, _, _, _ => hD.elim

/-- **`νX. C` is its unrolling**: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧`.  `[spec §7]` -/
theorem cC_nu_iff {C : CTy} (hC : C.NuOk) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.nu C) ls δ e ρ ↔ cC C.unroll ls δ e ρ := by
  rw [cC_nu_unfold hC.1]
  cases C with
  | amp C₁ C₂ =>
      show cB _ (.amp C₁ C₂) ls δ e ρ ↔ _
      rw [cB_unroll (.amp C₁ C₂) δ (D := .amp C₁ C₂) hC.1 hC.2 δ (fun _ _ => rfl)]
  | _ => exact hC.1.elim

end BoCa.Fig16.LogRel.Core

end
