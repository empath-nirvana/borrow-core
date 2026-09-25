import CBPVMu.Compatibility

/-!
# CBPVMu — Computations

`𝒞⟦C⟧` as the stack semantics (`cC_iff_stacks`), closure under pure steps in front
(`cC_step`, `cC_head`), bind at every computation type (`cC_bind`), and the context facts the
CBPV rules use: dead slots, consumed contexts (`semC_dead`), and contexts equal up to the types
of dead slots (`LiveEq`, `semC_liveEq`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Stacks -/

/-- `S[e]`: `e` applied to the stack's values, innermost first. -/
def plugS : List Val → Expr → Expr
  | [], e => e
  | v :: S, e => plugS S (.app e (.val v))

/-- `𝒮⟦C⟧(ls)δ(S, Q)`: `S` is a stack for `C` whose final `F A` has postcondition `Q`, and the
resource holds its arguments. -/
def sS : CTy → List SRec → LSub → List Val → (List SRec → Val → WProp) → WProp
  | .ret A, _, δ, [], Q => ⌜Q = fun ls'' => vC true A ls'' δ⌝
  | .arr A C, ls, δ, v :: S, Q => vC true A ls δ v ⋆ sS C ls δ S Q
  | .amp C D, ls, δ, v :: S, Q =>
      BoLo.or (⌜v = .inj₁ .unit⌝ ⋆ sS C ls δ S Q) (⌜v = .inj₂ .unit⌝ ⋆ sS D ls δ S Q)
  | .all x c C, ls, δ, v :: S, Q =>
      ex fun α => ⌜v = .unit ∧ LtLife δ c α⌝ ⋆ sS C ls (δ.extend x α) S Q
  | _, _, _, _, _ => fun _ => False

/-- `cC` is the stack semantics. -/
theorem cC_iff_stacks : ∀ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    cC C ls δ e ρ ↔ ∀ S Q, (sS C ls δ S Q ─⋆ wpTS ls (plugS S e) Q) ρ
  | .ret A, ls, δ, e, ρ => by
      constructor
      · intro hw S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil =>
            obtain ⟨rfl, rfl⟩ := hs
            rw [eq_of_compS_empty_left (ResU.CompS.comm hc)]
            exact hw
        | cons v S => exact hs.elim
      · intro h
        exact h [] _ PMap.empty ρ ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ)
  | .arr A C, ls, δ, e, ρ => by
      constructor
      · intro h S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            obtain ⟨a, b, hab, ha, hb⟩ := hs
            obtain ⟨x, hx, hxb⟩ := compS_reassoc' hab hc
            exact (cC_iff_stacks C ls δ _ x).mp (h v a x ha hx) S Q b ρ₂ hb hxb
      · intro h v a x ha hx
        refine (cC_iff_stacks C ls δ _ x).mpr ?_
        intro S Q b y hb hy
        obtain ⟨z, hz, hzy⟩ := compS_reassoc hx hy
        exact h (v :: S) Q z y ⟨a, b, hz, ha, hb⟩ hzy
  | .amp C D, ls, δ, e, ρ => by
      constructor
      · rintro ⟨h₁, h₂⟩ S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            rcases hs with hs | hs
            · obtain ⟨rfl, hs'⟩ := pure_sep_iff.mp hs
              exact (cC_iff_stacks C ls δ _ ρ).mp h₁ S Q ρ₁ ρ₂ hs' hc
            · obtain ⟨rfl, hs'⟩ := pure_sep_iff.mp hs
              exact (cC_iff_stacks D ls δ _ ρ).mp h₂ S Q ρ₁ ρ₂ hs' hc
      · intro h
        refine ⟨(cC_iff_stacks C ls δ _ ρ).mpr ?_, (cC_iff_stacks D ls δ _ ρ).mpr ?_⟩
        · intro S Q ρ₁ ρ₂ hs hc
          exact h (_ :: S) Q ρ₁ ρ₂ (Or.inl (pure_sep_mk rfl hs)) hc
        · intro S Q ρ₁ ρ₂ hs hc
          exact h (_ :: S) Q ρ₁ ρ₂ (Or.inr (pure_sep_mk rfl hs)) hc
  | .top, ls, δ, e, ρ => by
      constructor
      · intro _ S Q ρ₁ ρ₂ hs _
        cases S <;> exact hs.elim
      · intro _; trivial
  | .all x c C, ls, δ, e, ρ => by
      constructor
      · intro h S Q ρ₁ ρ₂ hs hc
        cases S with
        | nil => exact hs.elim
        | cons v S =>
            obtain ⟨α, hs⟩ := hs
            obtain ⟨⟨rfl, hlt⟩, hs'⟩ := pure_sep_iff.mp hs
            exact (cC_iff_stacks C ls (δ.extend x α) _ ρ).mp
              (h α PMap.empty ρ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ)) S Q ρ₁ ρ₂ hs' hc
      · intro h α a y ha hy
        obtain ⟨rfl, hlt⟩ := ha
        rw [eq_of_compS_empty_left (ResU.CompS.comm hy)]
        refine (cC_iff_stacks C ls (δ.extend x α) _ ρ).mpr ?_
        intro S Q ρ₁ ρ₂ hs hc
        exact h (.unit :: S) Q ρ₁ ρ₂ ⟨α, pure_sep_mk ⟨rfl, hlt⟩ hs⟩ hc


/-- `𝒱⟦A⟧` is carried to a list with the same members (`vP_same` for `vC`). -/
theorem vC_same {b : Bool} {A : VTy} {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hv : vC b A ls δ v ρ) : vC b A ls' δ v ρ :=
  vC_local b A (ext_of_same h ρ) hv

/-! ### Reduction in front of `wpTS` and `𝒞⟦C⟧` -/

/-- One pure step, in any evaluation context, in front of a `wpTS` (`wpTS_head`, with the step
taken by `Step1`). -/
theorem wpTS_step {e e' : Expr} (h : ∀ μ : Heap, Step1 μ e μ e') (ls : List SRec)
    (Q : List SRec → Val → WProp) : Entails (wpTS ls e' Q) (wpTS ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇,
    .more (h μ) h₈, h₉, hA, hB, hT', htg', hps, hls, hC⟩

/-- `𝒞⟦C⟧` is closed under a pure step in front. -/
theorem cC_step : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1 μ e μ e') →
    ∀ (ls : List SRec) (δ : LSub), Entails (cC C ls δ e') (cC C ls δ e)
  | .ret _, _, _, h, ls, _ => wpTS_step h ls _
  | .arr _ C, _, _, h, ls, δ => fun _ h' v ρ₁ ρ₂ hv hc =>
      cC_step C (fun μ => (h μ).plug (Kont.appL .hole v)) ls δ _ (h' v ρ₁ ρ₂ hv hc)
  | .amp C D, _, _, h, ls, δ => fun _ ⟨h₁, h₂⟩ =>
      ⟨cC_step C (fun μ => (h μ).plug (Kont.appL .hole _)) ls δ _ h₁,
       cC_step D (fun μ => (h μ).plug (Kont.appL .hole _)) ls δ _ h₂⟩
  | .top, _, _, _, _, _ => fun _ _ => trivial
  | .all x _ C, _, _, h, ls, δ => fun _ h' α ρ₁ ρ₂ hp hc =>
      cC_step C (fun μ => (h μ).plug (Kont.appL .hole _)) ls (δ.extend x α) _
        (h' α ρ₁ ρ₂ hp hc)

/-- One head step in front of `𝒞⟦C⟧`. -/
theorem cC_head (C : CTy) {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e')
    (ls : List SRec) (δ : LSub) : Entails (cC C ls δ e') (cC C ls δ e) :=
  cC_step C (fun μ => Step1.head (h μ)) ls δ

/-- **Bind at `𝒞⟦C⟧`.**  Run `M` in the hole of `K`, framing `R` through the run; the rest of
the computation — `K` and the stack `C` is eliminated by — continues at the list `M` returns.
`wpTS_bind_frame` at every computation type: the stack's arguments join the frame. -/
theorem cC_bind : ∀ (C : CTy) (K : Kont) (M : Expr) (ls : List SRec) (δ : LSub)
    (P : List SRec → Val → WProp) (R : List SRec → WProp),
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls')) →
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails (P ls' v ⋆ R ls') (cC C ls' δ (K.plug (.val v)))) →
    Entails (wpTS ls M P ⋆ R ls) (cC C ls δ (K.plug M))
  | .ret A, K, M, ls, δ, P, R, hR, h =>
      wpTS_bind_frame K M ls P R (fun ls'' => vC true A ls'' δ) hR h
  | .arr A C, K, M, ls, δ, P, R, hR, h => by
      rintro ρ ⟨ρ₁, ρ₂, hc, hw, hr⟩ v a x ha hx
      obtain ⟨y, hy, hyx⟩ := compS_reassoc hc hx
      refine cC_bind C (.appL K v) M ls δ P (fun l => R l ⋆ vC true A l δ v) ?_ ?_ x
        ⟨ρ₁, y, hyx, hw, ρ₂, a, hy, hr, ha⟩
      · rintro ls' hls σ ⟨σ₁, σ₂, hcσ, h₁, h₂⟩
        exact ⟨σ₁, σ₂, hcσ, hR ls' hls σ₁ h₁, vC_same hls h₂⟩
      · rintro ls' hls w σ ⟨σ₁, σ₂, hcσ, hp, τ₁, τ₂, hcτ, hr', hv⟩
        obtain ⟨z, hz, hzσ⟩ := compS_reassoc' hcτ hcσ
        exact h ls' hls w z ⟨σ₁, τ₁, hz, hp, hr'⟩ v τ₂ σ hv hzσ
  | .amp C D, K, M, ls, δ, P, R, hR, h => fun ρ hρ =>
      ⟨cC_bind C (.appL K _) M ls δ P R hR (fun ls' hls w σ hσ => (h ls' hls w σ hσ).1) ρ hρ,
       cC_bind D (.appL K _) M ls δ P R hR (fun ls' hls w σ hσ => (h ls' hls w σ hσ).2) ρ hρ⟩
  | .top, _, _, _, _, _, _, _, _ => fun _ _ => trivial
  | .all x c C, K, M, ls, δ, P, R, hR, h => by
      rintro ρ hρ α a y ⟨rfl, hlt⟩ hy
      rw [eq_of_compS_empty_left (ResU.CompS.comm hy)]
      exact cC_bind C (.appL K .unit) M ls (δ.extend x α) P R hR
        (fun ls' hls w σ hσ => h ls' hls w σ hσ α PMap.empty σ ⟨rfl, hlt⟩
          (ResU.comp_empty_right σ)) ρ hρ


/-- A dead slot contributes nothing. -/
theorem gDenC_dead_cons {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (A : VTy) (v : Val) (hg : gDenC ls δ Γ γ ρ) : gDenC ls δ (⟨A, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  exact gDenC_mk (by simpa using hlen) (by simpa [gSepC] using hs)


/-- A consumed context denotes `emp`, whatever its slots' types. -/
theorem gDenC_dead_eq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (γ : List Val) : gDenC ls δ Γ₁ γ = gDenC ls δ Γ₂ γ := by
  have hs : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ, gSepC ls δ Γ γ = emp := by
    intro Γ hd
    induction hd with
    | nil => intro γ; cases γ <;> rfl
    | cons _ ih => intro γ; cases γ with
      | nil => rfl
      | cons v γ => simp only [gSepC, Bool.false_eq_true, if_false, ih]
  have hl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ : List Val, Ctx.LiveWithin Γ γ := by
    intro Γ hd
    induction hd with
    | nil => intro γ; simp
    | cons _ ih => intro γ; cases γ with
      | nil => exact ⟨by simp, ih []⟩
      | cons v γ => exact ih γ
  unfold gDenC
  rw [hs h₁, hs h₂, propext (iff_of_true (hl h₁ γ) (hl h₂ γ))]

/-- `SemC` at a consumed context does not read the slots' types. -/
theorem semC_dead {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {C : CTy} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (h : SemC Δ Γ₁ e C) : SemC Δ Γ₂ e C := by
  intro δ γ ls ρ hδ hg
  rw [gDenC_dead_eq h₂ h₁] at hg
  exact h δ γ ls ρ hδ hg

/-- `Γ₁` and `Γ₂` have the same live slots, at the same positions and types; their dead slots
may be at different types. -/
inductive LiveEq : Ctx VTy → Ctx VTy → Prop where
  | nil : LiveEq [] []
  | live {A : VTy} {Γ₁ Γ₂ : Ctx VTy} : LiveEq Γ₁ Γ₂ → LiveEq (⟨A, true⟩ :: Γ₁) (⟨A, true⟩ :: Γ₂)
  | dead {A B : VTy} {Γ₁ Γ₂ : Ctx VTy} : LiveEq Γ₁ Γ₂ →
      LiveEq (⟨A, false⟩ :: Γ₁) (⟨B, false⟩ :: Γ₂)

theorem LiveEq.refl : ∀ Γ : Ctx VTy, LiveEq Γ Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .live (LiveEq.refl Γ)
  | ⟨_, false⟩ :: Γ => .dead (LiveEq.refl Γ)

theorem gSepC_liveEq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂) :
    ∀ γ, gSepC ls δ Γ₁ γ = gSepC ls δ Γ₂ γ := by
  induction h with
  | nil => intro γ; cases γ <;> rfl
  | live _ ih => intro γ; cases γ with
    | nil => rfl
    | cons v γ => simp only [gSepC, if_true, ih]
  | dead _ ih => intro γ; cases γ with
    | nil => rfl
    | cons v γ => simp only [gSepC, Bool.false_eq_true, if_false, ih]

theorem liveWithin_liveEq {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂) :
    ∀ γ : List Val, Ctx.LiveWithin Γ₁ γ ↔ Ctx.LiveWithin Γ₂ γ := by
  induction h with
  | nil => intro γ; simp
  | live _ ih => intro γ; cases γ with
    | nil => simp only [Ctx.liveWithin_cons_nil]; simp
    | cons v γ => simp only [Ctx.liveWithin_cons]; exact ih γ
  | dead _ ih => intro γ; cases γ with
    | nil => simp only [Ctx.liveWithin_cons_nil]; exact and_congr Iff.rfl (ih [])
    | cons v γ => simp only [Ctx.liveWithin_cons]; exact ih γ

/-- The context relation does not read the types of dead slots. -/
theorem gDenC_liveEq {ls : List SRec} {δ : LSub} {Γ₁ Γ₂ : Ctx VTy} (h : LiveEq Γ₁ Γ₂)
    (γ : List Val) : gDenC ls δ Γ₁ γ = gDenC ls δ Γ₂ γ := by
  unfold gDenC
  rw [gSepC_liveEq h γ, propext (liveWithin_liveEq h γ)]

theorem semC_liveEq {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {C : CTy} (hE : LiveEq Γ₁ Γ₂) :
    SemC Δ Γ₁ e C ↔ SemC Δ Γ₂ e C := by
  simp only [SemC, gDenC_liveEq hE]


end BoCa.Fig16.LogRel.CBPVMu

end
