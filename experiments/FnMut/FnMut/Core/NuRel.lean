import FnMut.Core.Compatibility

/-!
# Core — the relation at `νX. C`  `[spec §7]`

`cC`'s `nu` clause is, at a positive body (`CTy.NuOk`), the greatest fixed point `nuRel` of
`nuF C δ`: one unfolding of the observation tree `C` with the candidate `R` for `U X`
(`cB`, `nuEnv`).  `nuF` is monotone in the candidate (`nuF_mono`, from `wpTS_mono` and
`vCE_mono_at`: a polynomial `X` is outside every `Mut` payload), so the greatest fixed point is a fixed point
(`nuRel_out`, `nuRel_roll`).  At the relation itself one unfolding is `cC` at the unrolling
`C[U(νX. C)/X]` (`cB_unroll`), so `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` (`cC_nu_iff`).
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

/-- At a positive body, `cC (νX. C)` is `nuRel`. -/
theorem cC_nu_eq {C : CTy} (hC : C.NuOk) (δ : LSub) :
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
  | .eff _ _ _ _ _ D, hD, δ, ls, v => effRetE_mono C h (D := D) hD.2.2 δ ls v

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
  | .eff n i q A B D, hD, ls, δ, e => fun ρ h' =>
      ewp_mono (opTable_mono _) (fun _ _ _ _ h => h)
        (fun ls' v σ hv => effRetE_mono C h (D := D) hD.2.2 δ ls' v σ hv) h'

theorem nuF_mono {C : CTy} (hC : C.NuOk) (δ : LSub) {R R' : CPred} (h : R.Le R') :
    (nuF C δ R).Le (nuF C δ R') := by
  cases C with
  | amp C₁ C₂ => exact fun ls e => cB_mono _ h (D := .amp C₁ C₂) hC ls δ e
  | _ => exact hC.elim

/-- Coinduction. -/
theorem nuRel_coind {C : CTy} {δ : LSub} {R : CPred} (hR : R.Le (nuF C δ R)) :
    R.Le (nuRel C δ) :=
  fun _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem nuRel_out {C : CTy} (hC : C.NuOk) (δ : LSub) : (nuRel C δ).Le (nuF C δ (nuRel C δ)) := by
  rintro ls e ρ ⟨R, hR, h⟩
  exact nuF_mono hC δ (nuRel_coind hR) ls e ρ (hR ls e ρ h)

/-- `roll`. -/
theorem nuRel_roll {C : CTy} (hC : C.NuOk) (δ : LSub) : (nuF C δ (nuRel C δ)).Le (nuRel C δ) :=
  nuRel_coind (nuF_mono hC δ (nuRel_out hC δ))

/-- `cC (νX. C)` is one unfolding of `C` at `cC (νX. C)`. -/
theorem cC_nu_unfold {C : CTy} (hC : C.NuOk) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
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

theorem effTab_instT (S : VTy) (δ : LSub) : ∀ D : CTy, effTab (D.instT S) δ = effTab D δ
  | .eff n i q A B D => by simp only [CTy.instT, effTab, effTab_instT S δ D]
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nu _ => by simp [CTy.instT, effTab]

/-- The answer of an effectful observation at `cC (νX. C)` is `𝒱⟦·⟧` at the unrolling. -/
theorem effRetE_unroll (C : CTy) (δ : LSub) : ∀ {D : CTy}, D.EffLeaf →
    effRetE (some (nuEnv C (fun ls e => cC (.nu C) ls δ e))) D δ
      = effRet (D.instT (.thunk (.nu C))) δ
  | .ret A, _ => by
      funext ls v
      simp only [effRetE, effRet, CTy.instT, vCE_nuEnv]
  | .eff _ _ _ _ _ D, hD => by
      simp only [effRetE, effRet, CTy.instT]
      exact effRetE_unroll C δ (D := D) hD.2.2

/-- **One unfolding at `cC (νX. C)` is `cC` at the unrolling.** -/
theorem cB_unroll (C : CTy) (δ : LSub) : ∀ {D : CTy}, D.NuLeaf → ∀ (ls : List SRec),
    cB (some (nuEnv C (fun ls e => cC (.nu C) ls δ e))) D ls δ
      = cC (D.instT (.thunk (.nu C))) ls δ
  | .ret A, _, ls => by
      funext e
      show wpTS ls e (fun ls'' => vCE _ true A ls'' δ)
        = wpTS ls e (fun ls'' => vC true (VTy.inst _ A) ls'' δ)
      simp only [vCE_nuEnv]
  | .amp D₁ D₂, hD, ls => by
      funext e ρ
      show (cB _ D₁ ls δ _ ρ ∧ cB _ D₂ ls δ _ ρ)
        = (cC (D₁.instT _) ls δ _ ρ ∧ cC (D₂.instT _) ls δ _ ρ)
      rw [cB_unroll C δ hD.1, cB_unroll C δ hD.2]
  | .eff n i q A B D, hD, ls => by
      funext e
      show ewpTS ls e _ _ = ewpTS ls e _ _
      rw [effRetE_unroll C δ (D := D) hD.2.2, ← effTab_instT (.thunk (.nu C)) δ D]

/-- **`νX. C` is its unrolling**: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧`.  `[spec §7]` -/
theorem cC_nu_iff {C : CTy} (hC : C.NuOk) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.nu C) ls δ e ρ ↔ cC C.unroll ls δ e ρ := by
  rw [cC_nu_unfold hC]
  cases C with
  | amp C₁ C₂ =>
      show cB _ (.amp C₁ C₂) ls δ e ρ ↔ _
      rw [cB_unroll (.amp C₁ C₂) δ (D := .amp C₁ C₂) hC]
  | _ => exact hC.elim

end BoCa.Fig16.LogRel.Core

end
