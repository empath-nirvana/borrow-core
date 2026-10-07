import Core.Demonic
import Targets.Base.Machine

/-!
# Base — Core's machine, read through contexts

A run through a context splits where the inner term stops stepping (`steps_plug_split`): a run of
`K[e]` is `K` around a run of `e`, or it runs `e` to a term that takes no step and goes on from `K`
around that term.  The single-step form is `step1_plug_of_step`.  A variable at an evaluation
position blocks every step (`step1_plug_var`), and a context is determined by the non-value it
holds (`plug_inj_ctx`).  These read Core's unique decomposition (`plug_cmp`, `head_plug`,
`step1_plug_inv_active`) and state nothing about a world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal)

/-! ### Run splitting -/

/-- A step of `K[e]`, where `e` itself steps, is a step of `e` under `K`. -/
theorem step1_plug_of_step (K : Kont) {μ μ₁ μ' : Heap} {e e₁ E : Expr}
    (he : Step1 (ℍ := ℍ) μ e μ₁ e₁) (h : Step1 (ℍ := ℍ) μ (K.plug e) μ' E) :
    ∃ e', E = K.plug e' ∧ Step1 (ℍ := ℍ) μ e μ' e' := by
  obtain ⟨K₀, a₀, a₀', rfl, -, h₀⟩ := he
  exact step1_plug_inv_active K K₀ rfl h₀ h

/-- **Run splitting.**  A run from `K[e]` is `K` around a run of `e`, or it runs `e` to a term
that takes no step and continues from `K` around that term. -/
theorem steps_plug_split (K : Kont) {μ μ' : Heap} {e E : Expr}
    (hs : Steps (ℍ := ℍ) μ (K.plug e) μ' E) :
    (∃ e', E = K.plug e' ∧ Steps (ℍ := ℍ) μ e μ' e') ∨
    ∃ μ₁ t, Steps (ℍ := ℍ) μ e μ₁ t ∧ (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ t₂) ∧
      Steps (ℍ := ℍ) μ₁ (K.plug t) μ' E := by
  generalize hE : K.plug e = E₀ at hs
  induction hs generalizing e with
  | refl μ E₀ => exact .inl ⟨e, hE.symm, .refl _ _⟩
  | @more μ μ₁ μ' E₀ E₁ E' h t ih =>
      subst hE
      by_cases hst : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ e μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hst
        obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K h₂ h
        rcases ih rfl with ⟨e'', rfl, hs''⟩ | ⟨μ₃, t₃, hs₃, hirr, hrest⟩
        · exact .inl ⟨e'', rfl, .more he' hs''⟩
        · exact .inr ⟨μ₃, t₃, .more he' hs₃, hirr, hrest⟩
      · push_neg at hst
        exact .inr ⟨μ, e, .refl _ _, hst, .more h t⟩

/-! ### Stuck terms -/

theorem plug_eq_var {K : Kont} {a : Expr} {j : ℕ} (h : K.plug a = .var j) : K = .hole ∧ a = .var j := by
  cases K <;> simp_all [Kont.plug]

/-- A variable and an operation are never both at evaluation positions of one term. -/
theorem plug_var_ne_plug_op (K K' : Kont) (j : ℕ) (r : Bool) (p : Val) :
    K.plug (.var j) ≠ K'.plug (opE r p) := by
  intro h
  rcases plug_cmp K K' not_isVal_var (opE_not_isVal r p) h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · obtain ⟨-, h₂⟩ := plug_eq_var h₁.symm
    cases r <;> simp [opE, raiseE, performE] at h₂
  · cases K'' with
    | hole => cases r <;> simp [opE, raiseE, performE, Kont.plug] at h₁
    | appR f K₃ =>
        have h₂ : opE r p = .app f (K₃.plug (.var j)) := h₁
        rw [opE_eq_app] at h₂
        simp only [Expr.app.injEq] at h₂
        exact not_isVal_var (K₃.isVal_of_plug (by rw [← h₂.2]; exact p.2))
    | appL K₃ v =>
        have h₂ : opE r p = .app (K₃.plug (.var j)) v.1 := h₁
        rw [opE_eq_app] at h₂
        simp only [Expr.app.injEq] at h₂
        have h₃ := h₂.1
        cases K₃ <;> simp [Kont.plug] at h₃
    | _ => cases r <;> simp [opE, raiseE, performE, Kont.plug] at h₁

/-- **A variable at an evaluation position blocks every step.** -/
theorem step1_plug_var (K : Kont) (j : ℕ) {μ μ' : Heap} {t : Expr} :
    ¬ Step1 (ℍ := ℍ) μ (K.plug (.var j)) μ' t := by
  rintro ⟨K', a, a', hE, -, hh⟩
  rcases plug_cmp K K' not_isVal_var hh.not_isVal hE with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · obtain ⟨-, rfl⟩ := plug_eq_var h₁.symm
    cases hh
  · by_cases h0 : K'' = .hole
    · subst h0; simp only [Kont.plug] at h₁; subst h₁; cases hh
    rcases head_plug hh K'' not_isVal_var h₁ h0 with
      ⟨n, hr, hs, K₃, rfl⟩ | ⟨N, D, K₃, rfl⟩ | ⟨K₃, rfl⟩ | ⟨w, H, q, -, rfl, he⟩ |
        ⟨Ns, err, K₃, rfl⟩
    · generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n hr hs))) K₃).plug
        (.var j) = X at h₁
      subst h₁
      cases hh with
      | hret n' hr' hs' w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact not_isVal_var (K₃.isVal_of_plug (by rw [hX.2]; exact w.2))
      | hop n' i hr' hs' c v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j false (opPayload n' i v) hX.2
      | hunwind n' i hr' hs' c v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (opPayload n' i v) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K₃).plug
        (.var j) = X at h₁
      subst h₁
      cases hh with
      | uthen N' D' w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact not_isVal_var (K₃.isVal_of_plug (by rw [hX.2]; exact w.2))
      | ufin N' D' n i v K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (opPayload n i v) hX.2
      | ufinC N' D' Ns err K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal Ns err) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.val (.prim .ccatch)) K₃).plug (.var j) = X at h₁
      subst h₁
      cases hh with
      | cancel Ns K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal Ns none) hX.2
      | creraise Ns E K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal Ns (some E)) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
    · cases he
    · generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal Ns err))) K₃).plug
        (.var j) = X at h₁
      subst h₁
      cases hh with
      | cferr Ns' err' m j' w K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (opPayload m j' w) hX.2
      | cfret Ns' err' w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact not_isVal_var (K₃.isVal_of_plug (by rw [hX.2]; exact w.2))
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]

/-! ### Contexts are determined by what they hold -/

theorem sizeOf_plug_le : ∀ (K : Kont) (e : Expr), sizeOf e ≤ sizeOf (K.plug e) := by
  intro K e
  induction K with
  | hole => exact le_refl _
  | _ => rename_i ih; simp only [Kont.plug, Expr.pair.sizeOf_spec, Expr.inj₁.sizeOf_spec,
      Expr.inj₂.sizeOf_spec, Expr.letpair.sizeOf_spec, Expr.case.sizeOf_spec,
      Expr.app.sizeOf_spec, Expr.seq.sizeOf_spec]; omega

theorem sizeOf_plug_lt : ∀ (K : Kont) (e : Expr), K ≠ .hole → sizeOf e < sizeOf (K.plug e) := by
  intro K e hK
  cases K with
  | hole => exact absurd rfl hK
  | pairL K _ | pairR _ K | letpair K _ | case K _ _ | appR _ K | appL K _ | seq K _ | inj₁ K
  | inj₂ K =>
      have := sizeOf_plug_le K e
      simp only [Kont.plug, Expr.pair.sizeOf_spec, Expr.inj₁.sizeOf_spec, Expr.inj₂.sizeOf_spec,
        Expr.letpair.sizeOf_spec, Expr.case.sizeOf_spec, Expr.app.sizeOf_spec,
        Expr.seq.sizeOf_spec]
      omega

theorem plug_eq_self {K : Kont} {e : Expr} (h : K.plug e = e) : K = .hole := by
  by_contra hK
  have := sizeOf_plug_lt K e hK
  rw [h] at this
  exact lt_irrefl _ this

/-- **A context is determined by the non-value it holds.** -/
theorem plug_inj_ctx {K K' : Kont} {e : Expr} (hnv : ¬ IsVal e) (h : K.plug e = K'.plug e) :
    K = K' := by
  rcases plug_cmp K K' hnv hnv h with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · rw [h₂, plug_eq_self h₁.symm, Kont.comp_hole]
  · rw [h₂, plug_eq_self h₁.symm, Kont.comp_hole]

end Targets

end
