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

A term that holds a stuck redex at an evaluation position takes no step (`StuckAt`,
`stuck_no_step`).  A run from a closed term, with closed stored values, keeps both closed
(`closed_steps`): a head step substitutes closed values, and an evaluation context binds nothing
(`closedAt_plug_iff`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)

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
      · simp only [not_exists] at hst
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
      ⟨n, qs, hr, hs, K₃, rfl⟩ | ⟨N, D, K₃, rfl⟩ | ⟨K₃, rfl⟩ | ⟨w, H, q, -, rfl, he⟩ |
        ⟨err, K₃, rfl⟩
    · generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n qs hr hs))) K₃).plug
        (.var j) = X at h₁
      subst h₁
      cases hh with
      | hret n' qs' hr' hs' w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact not_isVal_var (K₃.isVal_of_plug (by rw [hX.2]; exact w.2))
      | hop n' i qs' hr' hs' c v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j false (opPayload n' i v) hX.2
      | hunwind n' i qs' hr' hs' c v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (opPayload n' i v) hX.2
      | _ => simp_all [Kont.plug, ubindE, ccatchE, cfinE]
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
      | ufinC N' D' err K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal err) hX.2
      | _ => simp_all [Kont.plug, hndE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.val (.prim .ccatch)) K₃).plug (.var j) = X at h₁
      subst h₁
      cases hh with
      | cancel K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal none) hX.2
      | creraise E K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal (some E)) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, cfinE]
    · cases he
    · generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) K₃).plug
        (.var j) = X at h₁
      subst h₁
      cases hh with
      | cferr err' m j' w K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (opPayload m j' w) hX.2
      | cfcancel err' err'' K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact plug_var_ne_plug_op K₃ K₀ j true (cancelVal err'') hX.2
      | cfret err' w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact not_isVal_var (K₃.isVal_of_plug (by rw [hX.2]; exact w.2))
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE]

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

/-! ### Stuck redexes -/

/-- `s` is a stuck redex: no value, no head rule reduces it, every proper evaluation subterm of it
is a value, and it is neither an operation nor an inert primitive applied to a value. -/
structure StuckAt (s : Expr) : Prop where
  not_val : ¬ IsVal s
  no_head : ∀ μ μ' a', ¬ Head (ℍ := ℍ) μ s μ' a'
  subs : ∀ (K : Kont) (a : Expr), s = K.plug a → K ≠ .hole → IsVal a
  not_op : ∀ (r : Bool) (p : Val), s ≠ opE r p
  not_inert : ∀ (p : Prim) (H : Val), p.Inert → s ≠ .app (.val (.prim p)) (.val H)

/-- A proper evaluation subterm of an operation is a value. -/
theorem isVal_of_plug_opE {K : Kont} {s : Expr} {r : Bool} {p : Val}
    (h : K.plug s = opE r p) (hK : K ≠ .hole) : IsVal s := by
  rw [opE_eq_app] at h
  cases K with
  | hole => exact absurd rfl hK
  | appR f K =>
      simp only [Kont.plug, Expr.app.injEq] at h
      exact K.isVal_of_plug (by rw [h.2]; exact p.2)
  | appL K v =>
      simp only [Kont.plug, Expr.app.injEq] at h
      have h1 := h.1
      cases K <;> simp [Kont.plug] at h1
      rw [h1]; exact .prim
  | _ => simp [Kont.plug] at h

/-- A stuck redex and an operation are never both at evaluation positions of one term. -/
theorem stuck_ne_op {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K K' : Kont) (r : Bool) (p : Val) :
    K.plug s ≠ K'.plug (opE r p) := by
  intro h
  rcases plug_cmp K K' hs.not_val (opE_not_isVal r p) h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · by_cases h0 : K'' = .hole
    · subst h0; exact hs.not_op r p h₁
    · exact opE_not_isVal r p (hs.subs K'' _ h₁ h0)
  · by_cases h0 : K'' = .hole
    · subst h0; exact hs.not_op r p h₁.symm
    · exact hs.not_val (isVal_of_plug_opE h₁.symm h0)

/-- **A term holding a stuck redex at an evaluation position takes no step.** -/
theorem stuck_no_step {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K : Kont) {μ μ' : Heap} {t : Expr} :
    ¬ Step1 (ℍ := ℍ) μ (K.plug s) μ' t := by
  rintro ⟨K', a, a', hE, -, hh⟩
  rcases plug_cmp K K' hs.not_val hh.not_isVal hE with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · by_cases h0 : K'' = .hole
    · subst h0; simp only [Kont.plug] at h₁; subst h₁; exact hs.no_head _ _ _ hh
    · exact hh.not_isVal (hs.subs K'' a h₁ h0)
  · by_cases h0 : K'' = .hole
    · subst h0; simp only [Kont.plug] at h₁; subst h₁; exact hs.no_head _ _ _ hh
    have hbody : ∀ (K₃ : Kont) (w : Val), K₃.plug s ≠ w.1 := fun K₃ w h =>
      hs.not_val (K₃.isVal_of_plug (by rw [h]; exact w.2))
    rcases head_plug hh K'' hs.not_val h₁ h0 with
      ⟨n, qs, hr, hs', K₃, rfl⟩ | ⟨N, D, K₃, rfl⟩ | ⟨K₃, rfl⟩ | ⟨w, H, q, hq, rfl, he⟩ |
        ⟨err, K₃, rfl⟩
    · generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n qs hr hs'))) K₃).plug s = X
        at h₁
      subst h₁
      cases hh with
      | hret _ _ _ _ w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | hop n' i _ _ _ _ v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ false (opPayload n' i v) hX.2
      | hunwind n' i _ _ _ _ v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload n' i v) hX.2
      | _ => simp_all [Kont.plug, ubindE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K₃).plug s = X
        at h₁
      subst h₁
      cases hh with
      | uthen _ _ w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | ufin _ _ n i v K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload n i v) hX.2
      | ufinC _ _ err K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal err) hX.2
      | _ => simp_all [Kont.plug, hndE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.val (.prim .ccatch)) K₃).plug s = X at h₁
      subst h₁
      cases hh with
      | cancel K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal none) hX.2
      | creraise E K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal (some E)) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, cfinE]
    · exact hs.not_inert q H hq he
    · generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) K₃).plug s = X
        at h₁
      subst h₁
      cases hh with
      | cferr _ m j w K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload m j w) hX.2
      | cfcancel _ err' K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal err') hX.2
      | cfret _ w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE]

/-- `()` applied to a value is a stuck redex. -/
theorem stuckAt_unit_app (x : Val) : StuckAt (ℍ := ℍ) (.app .unit x.1) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.app .unit x.1 = E at h
    cases h <;> simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at h
        exact K.isVal_of_plug (by rw [← h.2]; exact x.2)
    | appL K v =>
        simp only [Kont.plug, Expr.app.injEq] at h
        have h1 := h.1
        cases K <;> simp [Kont.plug] at h1
        rw [← h1]; exact .unit
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- `let (x, y) = v in e` at a value that is no pair is a stuck redex. -/
theorem stuckAt_letpair {v : Val} (hv : ∀ a b, v.1 ≠ .pair a b) (e : Expr) :
    StuckAt (ℍ := ℍ) (.letpair v.1 e) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.letpair v.1 e = E at h
    cases h with
    | letpair v₁ v₂ _ =>
        simp only [Expr.letpair.injEq] at hE
        exact hv _ _ hE.1
    | _ => simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | letpair K _ =>
        simp only [Kont.plug, Expr.letpair.injEq] at h
        exact K.isVal_of_plug (by rw [← h.1]; exact v.2)
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- `case v {…}` at a value that is no injection is a stuck redex. -/
theorem stuckAt_case {v : Val} (hv : ∀ a, v.1 ≠ .inj₁ a ∧ v.1 ≠ .inj₂ a) (e₁ e₂ : Expr) :
    StuckAt (ℍ := ℍ) (.case v.1 e₁ e₂) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.case v.1 e₁ e₂ = E at h
    cases h with
    | case₁ w _ _ =>
        simp only [Expr.case.injEq] at hE
        exact (hv _).1 hE.1
    | case₂ w _ _ =>
        simp only [Expr.case.injEq] at hE
        exact (hv _).2 hE.1
    | _ => simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | case K _ _ =>
        simp only [Kont.plug, Expr.case.injEq] at h
        exact K.isVal_of_plug (by rw [← h.1]; exact v.2)
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-! ### Closed runs -/

/-- Substituting a closed value for a variable below the bound lowers it by one. -/
theorem closedAt_subst : ∀ (e : Expr) {k j : ℕ} (s : Val), closedAt 0 s.1 = true →
    closedAt (k + 1) e = true → j ≤ k → closedAt k (e.subst j s) = true
  | .var i, k, j, s, hs, h, hj => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.subst]
      split
      · exact closedAt_mono _ hs (Nat.zero_le _)
      · split
        · simp only [closedAt, decide_eq_true_eq]; omega
        · simp only [closedAt, decide_eq_true_eq]; omega
  | .unit, _, _, _, _, _, _ => rfl
  | .loc _, _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _, _ => rfl
  | .pair a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .seq a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .app a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .inj₁ a, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢; exact closedAt_subst a s hs h hj
  | .inj₂ a, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢; exact closedAt_subst a s hs h hj
  | .lam b, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact closedAt_subst b (k := k + 1) (j := j + 1) s hs h (by omega)
  | .letpair a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b (k := k + 2) (j := j + 2) s hs h.2 (by omega)⟩
  | .case a b c, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact ⟨⟨closedAt_subst a s hs h.1.1 hj, closedAt_subst b (k := k + 1) (j := j + 1) s hs h.1.2
        (by omega)⟩, closedAt_subst c (k := k + 1) (j := j + 1) s hs h.2 (by omega)⟩

/-- An evaluation context binds nothing: `K[x]` is closed at `k` as `K[()]` and `x` are. -/
theorem closedAt_plug_iff (k : ℕ) : ∀ (K : Kont) (x : Expr),
    closedAt k (K.plug x) = (closedAt k (K.plug .unit) && closedAt k x)
  | .hole, x => by simp [Kont.plug, closedAt]
  | .pairL K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .pairR v K, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .letpair K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .case K e₁ e₂, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .appR f K, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .appL K v, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .seq K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .inj₁ K, x => by simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]
  | .inj₂ K, x => by simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]

/-- A closed context is fixed by every shift. -/
theorem kont_shift_closed (d : ℕ) : ∀ (K : Kont) (c : ℕ), closedAt 0 (K.plug .unit) = true →
    K.shift d c = K
  | .hole, _, _ => rfl
  | .pairL K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, shift_closedAt e d h.2 (Nat.zero_le c)]
  | .pairR v K, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.2, val_shift_closed h.1]
  | .letpair K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1,
        shift_closedAt e (k := 0 + 2) (c := c + 2) d h.2 (by omega)]
  | .case K e₁ e₂, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1.1,
        shift_closedAt e₁ (k := 0 + 1) (c := c + 1) d h.1.2 (by omega),
        shift_closedAt e₂ (k := 0 + 1) (c := c + 1) d h.2 (by omega)]
  | .appR f K, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.2, shift_closedAt f d h.1 (Nat.zero_le c)]
  | .appL K v, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, val_shift_closed h.2]
  | .seq K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, shift_closedAt e d h.2 (Nat.zero_le c)]
  | .inj₁ K, c, h => by
      simp only [Kont.plug, closedAt] at h; simp only [Kont.shift, kont_shift_closed d K c h]
  | .inj₂ K, c, h => by
      simp only [Kont.plug, closedAt] at h; simp only [Kont.shift, kont_shift_closed d K c h]

/-- Every stored value is closed. -/
def HeapClosed (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → closedAt 0 v.1 = true

theorem heapClosed_upd {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) {v : Val}
    (hv : closedAt 0 v.1 = true) : HeapClosed (μ.upd ℓ v) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h; subst h; exact hv
  · rw [Heap.upd_other hk] at h; exact hμ k w h

theorem heapClosed_del {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) : HeapClosed (μ.del ℓ) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h
  · rw [Heap.del_other hk] at h; exact hμ k w h

theorem heapClosed_fill {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) (n : ℕ) {v : Val}
    (hv : closedAt 0 v.1 = true) : HeapClosed (μ.fill ℓ n v) := by
  intro k w h
  simp only [Heap.fill] at h
  split at h
  · cases h; exact hv
  · exact hμ k w h

theorem heapClosed_empty : HeapClosed Adequacy.emptyMem := fun _ _ h => by
  simp [Adequacy.emptyMem] at h

theorem closedAt_cancelVal {err : Option Val}
    (h : ∀ E, err = some E → closedAt 0 E.1 = true) : closedAt 0 (cancelVal err).1 = true := by
  cases err with
  | none =>
      simp [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₁, Val.unit, closedAt]
  | some E =>
      have hE := h E rfl
      simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt]
        at hE ⊢
      simp [hE]

/-- A dead region keeps a part of the region's frames, so it is closed when the region is. -/
theorem closedAt_dead (k : ℕ) : ∀ (K : Kont), closedAt k (K.plug .unit) = true →
    closedAt k (K.dead.plug .unit) = true
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead]
      split
      · exact closedAt_dead k K h.2
      · simp only [Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨h.1, closedAt_dead k K h.2⟩
  | .pairL K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨closedAt_dead k K h.1, h.2⟩
  | .pairR v K, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨h.1, closedAt_dead k K h.2⟩
  | .letpair K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨closedAt_dead k K h.1, h.2⟩
  | .case K e₁ e₂, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨⟨closedAt_dead k K h.1.1, h.1.2⟩, h.2⟩
  | .appL K v, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨closedAt_dead k K h.1, h.2⟩
  | .seq K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨closedAt_dead k K h.1, h.2⟩
  | .inj₁ K, h => by
      simp only [Kont.plug, closedAt] at h
      simp only [Kont.dead, Kont.plug, closedAt]; exact closedAt_dead k K h
  | .inj₂ K, h => by
      simp only [Kont.plug, closedAt] at h
      simp only [Kont.dead, Kont.plug, closedAt]; exact closedAt_dead k K h

theorem closedAt_kappa {H : Val} {K : Kont} (hH : closedAt 0 H.1 = true)
    (hK : closedAt 0 (K.plug .unit) = true) : closedAt 0 (kappa H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [kappa, val_shift_closed hH, kont_shift_closed _ K 0 hK, kont_shift_closed _ K.dead 0 hK']
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [closedAt_plug_iff 3, closedAt_plug_iff 2]
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩ <;> (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- `κ` with its cell at `ℓ` is closed. -/
theorem closedAt_kappaC (aff : Bool) (ℓ : Loc) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaC aff ℓ H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [BoCa.BoLo.kappaC, val_shift_closed hH, kont_shift_closed _ K 0 hK,
    kont_shift_closed _ K.dead 0 hK']
  cases aff <;>
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq, BoCa.BoLo.freeE, BoCa.BoLo.stuckE, Val.loc, Val.unit, Bool.false_eq_true,
    if_true, if_false] <;>
  (try rw [closedAt_plug_iff 3]) <;> (try rw [closedAt_plug_iff 2]) <;>
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- `κ` before its cell is closed. -/
theorem closedAt_kappaCell (aff : Bool) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaCell aff H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [BoCa.BoLo.kappaCell, BoCa.BoLo.kappaCBody, val_shift_closed hH,
    kont_shift_closed _ K 0 hK, kont_shift_closed _ K.dead 0 hK']
  cases aff <;>
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq, BoCa.BoLo.freeE, BoCa.BoLo.stuckE, Val.unit, Bool.false_eq_true,
    if_true, if_false] <;>
  (try rw [closedAt_plug_iff 4]) <;> (try rw [closedAt_plug_iff 3]) <;>
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- The continuation `[op]` hands is closed, at every tag. -/
theorem closedAt_kappaAt (t : UInt32) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaAt t H K) = true := by
  unfold BoCa.BoLo.kappaAt
  split
  · exact closedAt_kappaCell false hH hK
  · split
    · exact closedAt_kappaCell true hH hK
    · exact closedAt_kappa hH hK

theorem closedAt_clauseAt : ∀ (e : Expr) (i : ℕ) {c : Val}, BoCa.BoLo.clauseAt e i = some c →
    closedAt 0 e = true → closedAt 0 c.1 = true
  | .pair c' _, 0, c, h, he => by
      simp only [BoCa.BoLo.clauseAt] at h
      split at h
      · cases h; simp only [closedAt, Bool.and_eq_true] at he; exact he.1
      · cases h
  | .pair _ r, i + 1, c, h, he => by
      simp only [closedAt, Bool.and_eq_true] at he
      exact closedAt_clauseAt r i h he.2
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [BoCa.BoLo.clauseAt] at h

theorem closedAt_host (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) :
    closedAt 0 r.1 = true := by
  have hi32 : ∀ n, closedAt 0 (Val.i32 n).1 = true := fun _ => rfl
  have hi64 : ∀ n, closedAt 0 (Val.i64 n).1 = true := fun _ => rfl
  have hu8 : ∀ n, closedAt 0 (Val.u8 n).1 = true := fun _ => rfl
  have hbool : ∀ b, closedAt 0 (Val.bool b).1 = true := fun b => by cases b <;> rfl
  have hopt : ∀ (o : Option Val), (∀ v, o = some v → closedAt 0 v.1 = true) →
      closedAt 0 (Val.opt o).1 = true := fun o ho => by
    cases o with
    | none => rfl
    | some v => simp only [Val.opt, Val.inj₁, closedAt]; exact ho v rfl
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _

theorem closedAt_tabFill {f : Val} (hf : closedAt 0 f.1 = true) (ℓ : Loc) (n : UInt32) :
    ∀ i k, closedAt 0 (tabFill f ℓ n i k) = true
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [tabFill, closedAt, Bool.and_eq_true, Expr.val, Val.i32, Val.loc, Val.prim]
      exact ⟨⟨⟨trivial, trivial⟩, hf, trivial⟩, closedAt_tabFill hf ℓ n (i + 1) k⟩

theorem closedAt_dropFill {f : Val} (hf : closedAt 0 f.1 = true) (ℓ : Loc) :
    ∀ i k, closedAt 0 (dropFill f ℓ i k) = true
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [dropFill, closedAt, Bool.and_eq_true, Expr.val, Val.loc, Val.prim]
      exact ⟨⟨hf, trivial, trivial⟩, closedAt_dropFill hf ℓ (i + 1) k⟩

/-- **A head step keeps a closed redex closed**, and stores only closed values. -/
theorem closed_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (ha : closedAt 0 a = true) (hμ : HeapClosed μ) : closedAt 0 a' = true ∧ HeapClosed μ' := by
  cases h with
  | beta b v =>
      simp only [closedAt, Expr.val, Val.lam, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst b v ha.2 ha.1 (le_refl 0), hμ⟩
  | alloc v ℓ hℓ =>
      simp only [closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      exact ⟨rfl, heapClosed_upd hμ ℓ ha.2⟩
  | free ℓ v hv => exact ⟨hμ ℓ v hv, heapClosed_del hμ ℓ⟩
  | load ℓ v hv => exact ⟨hμ ℓ v hv, hμ⟩
  | store ℓ v w hw =>
      simp only [closedAt, Expr.val, Val.prim, Val.loc, Bool.and_eq_true] at ha
      exact ⟨rfl, heapClosed_upd hμ ℓ ha.2⟩
  | seq e => simp only [closedAt, Expr.val, Val.unit, Bool.and_eq_true] at ha; exact ⟨ha.2, hμ⟩
  | letpair v₁ v₂ e =>
      simp only [closedAt, Expr.val, Val.pair, Bool.and_eq_true] at ha
      refine ⟨closedAt_subst _ v₁ ha.1.1 ?_ (le_refl 0), hμ⟩
      rw [val_shift_closed ha.1.2]
      exact closedAt_subst e (k := 1) (j := 0) v₂ ha.1.2 ha.2 (Nat.zero_le _)
  | case₁ v e₁ e₂ =>
      simp only [closedAt, Expr.val, Val.inj₁, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst e₁ v ha.1.1 ha.1.2 (le_refl 0), hμ⟩
  | case₂ v e₁ e₂ =>
      simp only [closedAt, Expr.val, Val.inj₂, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst e₂ v ha.1.1 ha.2 (le_refl 0), hμ⟩
  | host op v r hr => exact ⟨closedAt_host ℍ op hr, hμ⟩
  | tab c f ℓ hℓ =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      exact ⟨closedAt_tabFill ha.2.2 ℓ _ _ _, heapClosed_fill hμ ℓ _ rfl⟩
  | idx ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [idxAns]; split <;> rfl
  | split ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [splitAns]; split <;> rfl
  | drop f ℓ n =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.arr, Bool.and_eq_true] at ha
      exact ⟨closedAt_dropFill ha.2.1 ℓ _ _, hμ⟩
  | count f n i s' =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [countNext]; split
      · simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true]
        exact ⟨trivial, ha.2.1, trivial, trivial, ha.2.1, trivial, ha.2.2.2.2⟩
      · exact ha.2.2.2.2
  | countTry f n i s' =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [countTryNext]; split
      · simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true,
          val_shift_closed ha.2.1, decide_eq_true_eq]
        exact ⟨⟨⟨ha.2.1, trivial, ha.2.2.2.2⟩, trivial, closedAt_mono _ ha.2.1 (by omega), trivial,
          trivial, by omega⟩, by omega⟩
      · simp only [closedAt, Expr.val, Val.inj₁]; exact ha.2.2.2.2
  | boundedFix s' k a =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [boundedFixNext, closedAt, Expr.val, Val.pair, Bool.and_eq_true]
      refine ⟨ha.2.1, ?_, ha.2.2.2⟩
      simp only [fixSelf]; split
      · rfl
      · simp only [Val.inj₂, Val.lam, closedAt, Val.prim, Val.i32, Bool.and_eq_true,
          val_shift_closed ha.2.1, decide_eq_true_eq]
        exact ⟨trivial, closedAt_mono _ ha.2.1 (by omega), trivial, by omega⟩
  | hret n qs hr hs w =>
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨⟨ha.1.2.2.2.1, ha.2⟩, hμ⟩
  | hop n i qs hr hs c v K hc hK =>
      have ha' := ha
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      rw [closedAt_plug_iff] at ha'
      simp only [performE, opPayload, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      have hH : closedAt 0 (hndVal n qs hr hs).1 = true := by
        simp only [hndVal, closedAt, Val.pair, Val.i32, Bool.and_eq_true]
        exact ⟨trivial, ha'.1.2.2.1, ha'.1.2.2.2.1, ha'.1.2.2.2.2⟩
      refine ⟨?_, hμ⟩
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨closedAt_clauseAt hs.1 i.toNat hc ha'.1.2.2.2.2, ha'.2.2.2.2.2,
        closedAt_kappaAt _ hH ha'.2.1⟩
  | hunwind n i qs hr hs c v K hc hK =>
      have ha' := ha
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      rw [closedAt_plug_iff] at ha'
      simp only [raiseE, opPayload, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      refine ⟨?_, hμ⟩
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨closedAt_clauseAt hs.1 i.toNat hc ha'.1.2.2.2.2, ha'.2.2.2.2.2⟩
  | uthen N D w =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨⟨ha.1.2.1, ha.2⟩, hμ⟩
  | ufin N D n i v K hn hK =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Val.unit, Bool.and_eq_true]
      exact ⟨⟨⟨ha.1.2.2, trivial⟩, ha.2.2⟩, hμ⟩
  | ufinC N D err K hK =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      simp only [cfinE, closedAt, Expr.val, Val.prim, Val.unit, Bool.and_eq_true]
      exact ⟨⟨⟨trivial, ha.2.2.2⟩, ha.1.2.2, trivial⟩, hμ⟩
  | cfret err w =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      exact ⟨⟨trivial, ha.1.2⟩, hμ⟩
  | cferr err m j w K hm hK =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      refine ⟨trivial, closedAt_cancelVal ?_⟩
      intro E hE
      have hs := ha.1.2
      cases err with
      | some E' =>
          simp only [BoCa.BoLo.errNext, Option.some_or, Option.some.injEq] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs
          simp_all
      | none =>
          simp only [BoCa.BoLo.errNext, Option.none_or, Option.some.injEq] at hE
          subst hE; exact ha.2.2.2
  | cfcancel err err' K hK =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      refine ⟨trivial, closedAt_cancelVal ?_⟩
      intro E hE
      have hs := ha.1.2
      have hs' := ha.2.2
      cases err with
      | some E' =>
          simp only [Option.some_or, Option.some.injEq] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs
          simp_all
      | none =>
          simp only [Option.none_or] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs'
          simp_all
  | cancel K hK => exact ⟨rfl, hμ⟩
  | creraise E K hK =>
      simp only [ccatchE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      have hs := ha.2.2.2
      simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
        Bool.and_eq_true] at hs
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      exact ⟨⟨trivial, hs.2.2⟩, hμ⟩

theorem closed_step1 {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (he : closedAt 0 e = true) (hμ : HeapClosed μ) : closedAt 0 e' = true ∧ HeapClosed μ' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  rw [closedAt_plug_iff, Bool.and_eq_true] at he
  obtain ⟨ha', hμ'⟩ := closed_head hh he.2 hμ
  rw [closedAt_plug_iff, he.1, ha']
  exact ⟨rfl, hμ'⟩

/-- **A run from a closed term, with closed stored values, keeps both closed.** -/
theorem closed_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e')
    (he : closedAt 0 e = true) (hμ : HeapClosed μ) : closedAt 0 e' = true ∧ HeapClosed μ' := by
  induction h with
  | refl => exact ⟨he, hμ⟩
  | more h₁ _ ih =>
      obtain ⟨he₁, hμ₁⟩ := closed_step1 h₁ he hμ
      exact ih he₁ hμ₁

end Targets

end
