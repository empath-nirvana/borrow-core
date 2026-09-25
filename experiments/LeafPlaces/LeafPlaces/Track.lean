import LeafPlaces.Steps

/-!
# Borrowing returns the struct's own handle

`withborS σ h g` returns `(h, t)` with `h` the handle it was given, on every run
(`withborS_ret`).  This is what makes *pack after borrow* sound for a one-word handle: the
tuple of leaf addresses that comes back is the block's own, so it is again `addr b σ`.  The
typing rule alone does not say so — `refTy σ ⊗ T` is inhabited by other handles too.

The result `t` is also the result of a run of the callback `g () m` at some closed family `m`
of leaf borrows.

`⇓σ m` (`shortenE`) runs to `m` itself (`shortenE_run`): at run time the change of lifetime
is the identity.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.BoLo BoCa.Programs

/-! ## Substitution facts -/

theorem shortenE_subst : ∀ (σ : Shape) (e : Expr) (j : Nat) (s : Val),
    (shortenE σ e).subst j s = shortenE σ (e.subst j s)
  | .leaf _, _, _, _ => rfl
  | .node s₁ s₂, e, j, s => by
      have h₂ : ¬ (1 > j + 2) := by omega
      simp [shortenE, Expr.subst, shortenE_subst s₁, shortenE_subst s₂, h₂]

theorem withborS_subst (σ : Shape) (j : Nat) (s : Val) : (withborS σ).subst j s = withborS σ :=
  subst_clAt _ s (clAt_withborS σ) (Nat.zero_le j)

theorem cl_subst {v : Val} (h : clAt 0 v.1 = true) (j : Nat) (s : Val) : v.1.subst j s = v.1 :=
  subst_clAt _ s h (Nat.zero_le j)

theorem cl_shiftE {v : Val} (h : clAt 0 v.1 = true) (d c : Nat) : v.1.shift d c = v.1 :=
  shift_clAt _ d h (Nat.zero_le c)

theorem cl_shift {v : Val} (h : clAt 0 v.1 = true) (d c : Nat) : v.shift d c = v :=
  Val.shift_cl h d c

/-- `(u↑)[s/0] = u`. -/
theorem subst_shift_val (u s : Val) : (u.shift 1 0).1.subst 0 s = u.1 := by
  have := Expr.subst_shift 0 0 0 s u.1 (le_refl _) (by omega)
  rw [Expr.shift_zero] at this
  exact this

/-- `(e↑)[s/0] = e`. -/
@[simp] theorem subst_shift_expr (e : Expr) (s : Val) : (e.shift 1 0).subst 0 s = e := by
  have := Expr.subst_shift 0 0 0 s e (le_refl _) (by omega)
  rw [Expr.shift_zero] at this
  exact this

/-! ## `⇓σ` is the identity at run time -/

theorem shortenE_run : ∀ (σ : Shape) {m w : Val} {μ μ' : Heap},
    Steps μ (shortenE σ m.1) μ' w.1 → w = m
  | .leaf _, _, _, _, _, h => (steps_from_val h).2
  | .node s₁ s₂, m, w, μ, μ', h => by
      obtain ⟨μm, v₁, v₂, h₁, h₂⟩ := steps_letpair_inv h
      obtain ⟨rfl, hm⟩ := steps_from_val (v := m) h₁
      subst hm
      simp [Expr.subst, shortenE_subst] at h₂
      obtain ⟨u₁, u₂, rfl, μ₁, μ₂, r₁, r₂⟩ := steps_pair_inv h₂
      rw [shortenE_run s₁ r₁, shortenE_run s₂ r₂]

/-! ## The callbacks of `withborS (node s₁ s₂)`, instantiated -/

/-- The inner callback with `g` and the outer family `mx` in place. -/
def innerM (s₁ : Shape) (g m : Val) : Expr :=
  lam (lam (app2 g.1 unit' (.pair (shortenE s₁ m.1) (.var 0))))

/-- The outer callback with `y` and `g` in place. -/
def outerV (s₁ s₂ : Shape) (v₂ g : Val) : Expr :=
  lam (lam (.letpair (app2 (withborS s₂) v₂.1
      (lam (lam (app2 g.1 unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))))
    (.pair (.var 1) (.var 0))))

theorem clAt_innerM (s₁ : Shape) {g m : Val} (hg : clAt 0 g.1 = true) (hm : clAt 0 m.1 = true) :
    clAt 0 (innerM s₁ g m) = true := by
  simp [innerM, lam, app2, Val.lam, unit', Val.unit, clAt, clAt_mono _ hg (Nat.zero_le _),
    clAt_shortenE s₁ (clAt_mono _ hm (Nat.zero_le 2))]

theorem clAt_outerV (s₁ s₂ : Shape) {v₂ g : Val} (hv : clAt 0 v₂.1 = true) (hg : clAt 0 g.1 = true) :
    clAt 0 (outerV s₁ s₂ v₂ g) = true := by
  simp [outerV, lam, app2, Val.lam, unit', Val.unit, clAt, clAt_mono _ hg (Nat.zero_le _),
    clAt_mono _ hv (Nat.zero_le _), clAt_mono _ (clAt_withborS s₂) (Nat.zero_le _),
    clAt_shortenE s₁ (show clAt 4 (.var 2) = true by simp [clAt])]

/-- The inner callback's runs: each is a run of `g () (m₁, m₂)`. -/
theorem inner_ret (s₁ : Shape) {g m₁ m₂ t : Val} {μ μ' : Heap} (hg : clAt 0 g.1 = true)
    (hm₁ : clAt 0 m₁.1 = true) (hs : Steps μ (app2 (innerM s₁ g m₁) unit' m₂.1) μ' t.1) :
    ∃ μ₁, Steps μ₁ (app2 g.1 unit' (Val.pair m₁ m₂).1) μ' t.1 := by
  have h := steps_app2_lam2 (a := Val.unit) (b := m₂)
    (X := app2 g.1 unit' (.pair (shortenE s₁ m₁.1) (.var 0))) hs
  simp [app2, Expr.subst, cl_subst hg, shortenE_subst, cl_subst hm₁, unit', Val.unit] at h
  obtain ⟨μm, a, h₁, h₂⟩ := steps_appR_inv h
  obtain ⟨u₁, u₂, rfl, μa, μb, r₁, r₂⟩ := steps_pair_inv h₁
  rw [shortenE_run s₁ r₁] at h₂
  obtain ⟨-, rfl⟩ := steps_from_val (v := m₂) r₂
  exact ⟨μm, h₂⟩

/-! ## The tracking theorem -/

/-- **Borrowing returns the handle it was given.**  Every run of `withborS σ v g` to a value
returns `(v, r)`, and `r` is the result of a run of `g () m` at a closed family `m`. -/
theorem withborS_ret : ∀ (σ : Shape) {v g w : Val} {μ μ' : Heap},
    clAt 0 v.1 = true → clAt 0 g.1 = true →
    Steps μ (app2 (withborS σ) v.1 g.1) μ' w.1 →
    ∃ r : Val, w = .pair v r ∧
      ∃ (m : Val) (μ₁ μ₂ : Heap), clAt 0 m.1 = true ∧ Steps μ₁ (app2 g.1 unit' m.1) μ₂ r.1
  | .leaf _, v, g, w, μ, μ', hv, hg, hs => by
      have h := steps_app2_lam2 (X := .pair (.var 1) (.app (.app (.var 0) unit') (.var 1))) hs
      simp [Expr.subst, cl_shift hv, cl_subst hv, unit', Val.unit] at h
      obtain ⟨u, rfl, μm, h₁⟩ := steps_pairR_inv h
      exact ⟨u, rfl, v, μ, μm, hv, h₁⟩
  | .node s₁ s₂, v, g, w, μ, μ', hv, hg, hs => by
      rw [withborS_node] at hs
      have h := steps_app2_lam2 hs
      simp [Expr.subst, cl_shift hv, cl_subst hv, cl_shiftE hg, withborS_subst,
        shortenE_subst, outerS, innerS, app2, lam, Val.lam, unit', Val.unit] at h
      obtain ⟨μm, v₁, v₂, h₁, h₂⟩ := steps_letpair_inv h
      obtain ⟨rfl, rfl⟩ := steps_from_val (v := v) h₁
      simp [Val.pair, clAt] at hv
      obtain ⟨hv₁, hv₂⟩ := hv
      simp [Expr.subst, cl_shift hv₁, cl_shift hv₂, cl_subst hv₂, cl_subst hg,
        withborS_subst, shortenE_subst] at h₂
      -- the outer borrow, of `s₁`
      obtain ⟨μa, x', r, h₃, h₄⟩ := steps_letpair_inv h₂
      obtain ⟨r', hxr, m₁, μ₁, μ₂, hm₁, hrun₁⟩ :=
        withborS_ret s₁ (v := v₁) (g := ⟨outerV s₁ s₂ v₂ g, .lam⟩) hv₁ (clAt_outerV s₁ s₂ hv₂ hg) h₃
      obtain ⟨rfl, rfl⟩ : x' = v₁ ∧ r = r' := by
        simp only [Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at hxr
        exact ⟨Subtype.ext hxr.1, Subtype.ext hxr.2⟩
      -- the outer callback's run: the inner borrow, of `s₂`
      have h₅ := steps_app2_lam2 (a := Val.unit) (b := m₁)
        (X := .letpair (app2 (withborS s₂) v₂.1
            (lam (lam (app2 g.1 unit' (.pair (shortenE s₁ (.var 2)) (.var 0))))))
          (.pair (.var 1) (.var 0))) hrun₁
      simp [Expr.subst, cl_subst hv₂, cl_subst hg, cl_shiftE hm₁,
        withborS_subst, shortenE_subst, app2, lam, Val.lam, unit', Val.unit] at h₅
      obtain ⟨μc, y', t, h₆, h₇⟩ := steps_letpair_inv h₅
      obtain ⟨t', hyt, m₂, μ₃, μ₄, hm₂, hrun₂⟩ :=
        withborS_ret s₂ (v := v₂) (g := ⟨innerM s₁ g m₁, .lam⟩) hv₂ (clAt_innerM s₁ hg hm₁) h₆
      obtain ⟨rfl, rfl⟩ : y' = v₂ ∧ t = t' := by
        simp only [Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at hyt
        exact ⟨Subtype.ext hyt.1, Subtype.ext hyt.2⟩
      obtain ⟨μ₅, hrun⟩ := inner_ret s₁ hg hm₁ hrun₂
      simp [Expr.subst] at h₇
      obtain ⟨-, hr⟩ := steps_from_val (v := Val.pair y' t) h₇
      subst hr
      -- the family's result
      simp [Expr.subst, cl_shiftE hv₁] at h₄
      obtain ⟨μd, a₁, a₂, h₈, h₉⟩ := steps_letpair_inv h₄
      obtain ⟨-, hr'⟩ := steps_from_val (v := Val.pair y' t) h₈
      obtain ⟨rfl, rfl⟩ : a₁ = y' ∧ a₂ = t := by
        simp only [Val.pair, Subtype.mk.injEq, Expr.pair.injEq] at hr'
        exact ⟨Subtype.ext hr'.1, Subtype.ext hr'.2⟩
      simp [Expr.subst, cl_subst hv₁] at h₉
      obtain ⟨-, rfl⟩ := steps_from_val (v := Val.pair (Val.pair x' a₁) a₂) h₉
      refine ⟨a₂, rfl, Val.pair m₁ m₂, μ₅, μ₄, ?_, hrun⟩
      simp [Val.pair, clAt, hm₁, hm₂]

end BoCa.LeafPlaces

end
