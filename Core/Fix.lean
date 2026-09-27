import Core.Compat

/-!
# Core — the Z combinator over BoCa's untyped λ  `[spec §6]`

`experiments/Recursion/Recursion/Fix.lean` at this world's `wpTS`, with `substAll_closed`.

BoCa's `Expr` is untyped call-by-value with `λ`, so a recursive function needs no new syntax
and no new machine rule. For a functional `F = λself. λx. B`:

    X     = λx. F (λv. x x v)
    selfV = λv. X X v
    fixV  = λx. B[selfV/self]

`fixV` is what `Z F` reduces to, and `selfV w` reaches `fixV w` by three β-steps
(`wpTS_selfV`), all pure head steps in front of a `wpTS`. `closedAt k e` says every free
variable of `e` is below `k`; substitution and shifting at or above `k` leave `e` unchanged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Closed terms -/

/-- Every free variable of `e` is below `k`. -/
def closedAt : Nat → Expr → Bool
  | k, .var i => decide (i < k)
  | _, .unit => true
  | k, .pair e₁ e₂ => closedAt k e₁ && closedAt k e₂
  | k, .inj₁ e => closedAt k e
  | k, .inj₂ e => closedAt k e
  | k, .lam b => closedAt (k + 1) b
  | _, .loc _ => true
  | _, .prim _ => true
  | k, .seq e₁ e₂ => closedAt k e₁ && closedAt k e₂
  | k, .letpair e₁ e₂ => closedAt k e₁ && closedAt (k + 2) e₂
  | k, .case e e₁ e₂ => closedAt k e && closedAt (k + 1) e₁ && closedAt (k + 1) e₂
  | k, .app f a => closedAt k f && closedAt k a

theorem closedAt_mono : ∀ (e : Expr) {k k' : Nat}, closedAt k e = true → k ≤ k' →
    closedAt k' e = true
  | .var i, _, _, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h ⊢; omega
  | .unit, _, _, _, _ => rfl
  | .pair e₁ e₂, _, _, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono e₁ h.1 hk, closedAt_mono e₂ h.2 hk⟩
  | .inj₁ e, _, _, h, hk => closedAt_mono e h hk
  | .inj₂ e, _, _, h, hk => closedAt_mono e h hk
  | .lam b, _, _, h, hk => closedAt_mono b h (by omega)
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq e₁ e₂, _, _, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono e₁ h.1 hk, closedAt_mono e₂ h.2 hk⟩
  | .letpair e₁ e₂, _, _, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono e₁ h.1 hk, closedAt_mono e₂ h.2 (by omega)⟩
  | .case e e₁ e₂, _, _, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨closedAt_mono e h.1.1 hk, closedAt_mono e₁ h.1.2 (by omega)⟩,
        closedAt_mono e₂ h.2 (by omega)⟩
  | .app f a, _, _, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono f h.1 hk, closedAt_mono a h.2 hk⟩

/-- Substitution at or above the bound leaves a closed term unchanged. -/
theorem subst_closedAt : ∀ (e : Expr) {k j : Nat} (s : Val), closedAt k e = true → k ≤ j →
    e.subst j s = e
  | .var i, _, _, _, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | .unit, _, _, _, _, _ => rfl
  | .pair e₁ e₂, _, _, s, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.subst, subst_closedAt e₁ s h.1 hk, subst_closedAt e₂ s h.2 hk]
  | .inj₁ e, _, _, s, h, hk => by simp only [Expr.subst, subst_closedAt e s h hk]
  | .inj₂ e, _, _, s, h, hk => by simp only [Expr.subst, subst_closedAt e s h hk]
  | .lam b, k, j, s, h, hk => by
      simp only [Expr.subst, subst_closedAt b (k := k + 1) (j := j + 1) _ h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq e₁ e₂, _, _, s, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.subst, subst_closedAt e₁ s h.1 hk, subst_closedAt e₂ s h.2 hk]
  | .letpair e₁ e₂, k, j, s, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.subst, subst_closedAt e₁ s h.1 hk,
        subst_closedAt e₂ (k := k + 2) (j := j + 2) _ h.2 (by omega)]
  | .case e e₁ e₂, k, j, s, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.subst, subst_closedAt e s h.1.1 hk,
        subst_closedAt e₁ (k := k + 1) (j := j + 1) _ h.1.2 (by omega),
        subst_closedAt e₂ (k := k + 1) (j := j + 1) _ h.2 (by omega)]
  | .app f a, _, _, s, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.subst, subst_closedAt f s h.1 hk, subst_closedAt a s h.2 hk]

/-- Shifting at or above the bound leaves a closed term unchanged. -/
theorem shift_closedAt : ∀ (e : Expr) {k c : Nat} (d : Nat), closedAt k e = true → k ≤ c →
    e.shift d c = e
  | .var i, _, _, _, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.shift]
      rw [if_pos (by omega)]
  | .unit, _, _, _, _, _ => rfl
  | .pair e₁ e₂, _, _, d, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, shift_closedAt e₁ d h.1 hk, shift_closedAt e₂ d h.2 hk]
  | .inj₁ e, _, _, d, h, hk => by simp only [Expr.shift, shift_closedAt e d h hk]
  | .inj₂ e, _, _, d, h, hk => by simp only [Expr.shift, shift_closedAt e d h hk]
  | .lam b, k, c, d, h, hk => by
      simp only [Expr.shift, shift_closedAt b (k := k + 1) (c := c + 1) d h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq e₁ e₂, _, _, d, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, shift_closedAt e₁ d h.1 hk, shift_closedAt e₂ d h.2 hk]
  | .letpair e₁ e₂, k, c, d, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, shift_closedAt e₁ d h.1 hk,
        shift_closedAt e₂ (k := k + 2) (c := c + 2) d h.2 (by omega)]
  | .case e e₁ e₂, k, c, d, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, shift_closedAt e d h.1.1 hk,
        shift_closedAt e₁ (k := k + 1) (c := c + 1) d h.1.2 (by omega),
        shift_closedAt e₂ (k := k + 1) (c := c + 1) d h.2 (by omega)]
  | .app f a, _, _, d, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, shift_closedAt f d h.1 hk, shift_closedAt a d h.2 hk]

theorem val_subst_closed {v : Val} (h : closedAt 0 v.1 = true) (j : Nat) (s : Val) :
    Expr.subst j s (.val v) = .val v :=
  subst_closedAt v.1 s h (Nat.zero_le j)

theorem val_shift_closed {v : Val} (h : closedAt 0 v.1 = true) (d c : Nat) : v.shift d c = v :=
  Val.ext (shift_closedAt v.1 d h (Nat.zero_le c))

/-- A closing substitution under at least `k` binders leaves a term closed at `k` unchanged. -/
theorem psub_closedAt : ∀ (e : Expr) {k j : Nat} (γ : List Val), closedAt k e = true → k ≤ j →
    Expr.psub j γ e = e
  | .var i, _, _, _, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.psub]
      rw [if_pos (by omega)]
  | .unit, _, _, _, _, _ => rfl
  | .pair e₁ e₂, _, _, γ, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_closedAt e₁ γ h.1 hk, psub_closedAt e₂ γ h.2 hk]
  | .inj₁ e, _, _, γ, h, hk => by simp only [Expr.psub, psub_closedAt e γ h hk]
  | .inj₂ e, _, _, γ, h, hk => by simp only [Expr.psub, psub_closedAt e γ h hk]
  | .lam b, k, j, γ, h, hk => by
      simp only [Expr.psub, psub_closedAt b (k := k + 1) (j := j + 1) γ h (by omega)]
  | .loc _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _ => rfl
  | .seq e₁ e₂, _, _, γ, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_closedAt e₁ γ h.1 hk, psub_closedAt e₂ γ h.2 hk]
  | .letpair e₁ e₂, k, j, γ, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_closedAt e₁ γ h.1 hk,
        psub_closedAt e₂ (k := k + 2) (j := j + 2) γ h.2 (by omega)]
  | .case e e₁ e₂, k, j, γ, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_closedAt e γ h.1.1 hk,
        psub_closedAt e₁ (k := k + 1) (j := j + 1) γ h.1.2 (by omega),
        psub_closedAt e₂ (k := k + 1) (j := j + 1) γ h.2 (by omega)]
  | .app f a, _, _, γ, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_closedAt f γ h.1 hk, psub_closedAt a γ h.2 hk]

/-- A closed value is fixed by every closing substitution. -/
theorem substAll_closed {v : Val} (h : closedAt 0 v.1 = true) (γ : List Val) :
    substAll γ (.val v) = .val v :=
  psub_closedAt v.1 γ h (Nat.zero_le 0)

/-! ### The Z combinator -/

/-- `X = λx. F (λv. x x v)` for `F = λself. λx. B`. -/
def zX (B : Expr) : Val :=
  .lam (.app (.val (.lam (.lam B))) (.val (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))

/-- `selfV = λv. X X v`: the recursive handle, a value. -/
def selfV (B : Expr) : Val := .lam (.app (.app (.val (zX B)) (.val (zX B))) (.var 0))

/-- `fixV = λx. B[selfV/self]`: the function `Z F` reduces to. -/
def fixV (B : Expr) : Val := .lam (B.subst 1 ((selfV B).shift 1 0))

theorem zX_closed {B : Expr} (hB : closedAt 2 B = true) : closedAt 0 (zX B).1 = true := by
  simp [zX, closedAt, closedAt_mono B hB (by omega : 2 ≤ 3)]

theorem selfV_closed {B : Expr} (hB : closedAt 2 B = true) : closedAt 0 (selfV B).1 = true := by
  have := zX_closed hB
  simp only [selfV, Val.val_lam, closedAt, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨closedAt_mono _ this (Nat.zero_le _), closedAt_mono _ this (Nat.zero_le _)⟩, by omega⟩

/-- `fixV = λx. B[selfV/self]` with the shift of the closed handle removed. -/
theorem fixV_eq {B : Expr} (hB : closedAt 2 B = true) :
    fixV B = .lam (B.subst 1 (selfV B)) := by
  rw [fixV, val_shift_closed (selfV_closed hB)]

/-- A head step inside an evaluation context, at every heap. -/
theorem step_in (K : Kont) {a a' : Expr} (h : ∀ μ : Heap, Head μ a μ a') :
    ∀ μ : Heap, Step1 μ (K.plug a) μ (K.plug a') :=
  fun μ => ⟨K, a, a', rfl, rfl, h μ⟩

/-! ### Pure reduction -/

/-- `e` reduces to `e'` by steps that take every heap to itself. -/
def PureSteps (e e' : Expr) : Prop :=
  Relation.ReflTransGen (fun a b => ∀ μ : Heap, Step1 μ a μ b) e e'

theorem PureSteps.trans {a b c : Expr} (h₁ : PureSteps a b) (h₂ : PureSteps b c) :
    PureSteps a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem PureSteps.plug (K : Kont) {e e' : Expr} (h : PureSteps e e') :
    PureSteps (K.plug e) (K.plug e') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (fun μ => (hs μ).plug K)

theorem PureSteps.head {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') : PureSteps e e' :=
  .single (fun μ => Step1.head (h μ))

/-- `(λx. b) v ↦ b[v/x]`, in an evaluation context. -/
theorem PureSteps.beta_in (K : Kont) (b : Expr) (v : Val) :
    PureSteps (K.plug (.app (.val (.lam b)) (.val v))) (K.plug (b.subst 0 v)) :=
  .single (step_in K (fun μ => Head.beta μ b v))

theorem PureSteps.beta (b : Expr) (v : Val) :
    PureSteps (.app (.val (.lam b)) (.val v)) (b.subst 0 v) :=
  PureSteps.beta_in .hole b v

theorem wpTS_pureSteps {e e' : Expr} (h : PureSteps e e') (ls : List SRec)
    (Q : List SRec → Val → WProp) : Entails (wpTS ls e' Q) (wpTS ls e Q) := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ hs ih => exact fun ρ h => ih ρ (wpTS_step hs ls Q ρ h)

/-- **Unrolling**, in any evaluation context: `K[selfV w]` reaches `K[fixV w]` by three
β-steps. -/
theorem selfV_steps_in {B : Expr} (hB : closedAt 2 B = true) (K : Kont) (w : Val) :
    PureSteps (K.plug (.app (.val (selfV B)) (.val w))) (K.plug (.app (.val (fixV B)) (.val w))) := by
  have hX := zX_closed hB
  -- `selfV w ↦ X X w`
  have h₁ : (Expr.app (.app (.val (zX B)) (.val (zX B))) (.var 0)).subst 0 w
      = .app (.app (.val (zX B)) (.val (zX B))) (.val w) := by
    simp only [Expr.subst, val_subst_closed hX]; rfl
  -- `X X ↦ F selfV`
  have h₂ : (Expr.app (.val (.lam (.lam B)))
      (.val (.lam (.app (.app (.var 1) (.var 1)) (.var 0))))).subst 0 (zX B)
      = .app (.val (.lam (.lam B))) (.val (selfV B)) := by
    simp [selfV, Expr.subst, val_shift_closed hX, subst_closedAt B (k := 2) (j := 2) _ hB le_rfl]
  have hK : ∀ e, K.plug (.app e (.val w)) = (K.comp (.appL .hole w)).plug e := fun e => by
    rw [Kont.plug_comp]; rfl
  refine (PureSteps.beta_in K _ w).trans ?_
  rw [h₁, hK]
  refine (PureSteps.beta_in _ _ (zX B)).trans ?_
  rw [h₂]
  refine (PureSteps.beta_in _ (.lam B) (selfV B)).trans ?_
  rw [← hK]
  exact .refl

/-- **Unrolling**, in any evaluation context, at `wpTS`. -/
theorem wpTS_selfV_in {B : Expr} (hB : closedAt 2 B = true) (K : Kont) (w : Val)
    (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (K.plug (.app (.val (fixV B)) (.val w))) Q)
      (wpTS ls (K.plug (.app (.val (selfV B)) (.val w))) Q) :=
  wpTS_pureSteps (selfV_steps_in hB K w) ls Q

/-- **Unrolling.** `selfV w` reaches `fixV w` by three β-steps. -/
theorem wpTS_selfV {B : Expr} (hB : closedAt 2 B = true) (w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.val (fixV B)) (.val w)) Q)
      (wpTS ls (.app (.val (selfV B)) (.val w)) Q) :=
  wpTS_selfV_in hB .hole w ls Q

end BoCa.Fig16.LogRel.Core

end
