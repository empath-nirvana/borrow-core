import Core.Fundamental

/-!
# Base — the polymorphic let's premise term

`CDerives.letPoly` types `let x = λy. b in N` from `(N.subst 0 (λy. b)).shift 1 0`: `N` with the
closed λ-value for `x`, every other variable where it was.  The syntactic facts the inductions over
`CDerives` read of it:

* `fill_shift`: it commutes with a shift above the filled variable (`CDerives.insert_dead`);
* `closedAt_of_fill`: `N` is closed where its filling is (`closedAt_of_derives`);
* `okE_of_fill`-style facts are in `Targets/Instance/Restricted/NoInterception.lean`.
-/

noncomputable section

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core

/-- Filling a variable commutes with a shift above it. -/
theorem fill_shift {V : Val} (hV : closedAt 0 V.1 = true) (d : Nat) :
    ∀ (N : Expr) (j c : Nat), j ≤ c →
      ((N.shift d (c + 1)).subst j V).shift 1 j = ((N.subst j V).shift 1 j).shift d (c + 1)
  | .var i, j, c, hjc => by
      have hs : ∀ (d' c' : Nat), V.1.shift d' c' = V.1 :=
        fun d' c' => shift_closedAt V.1 d' hV (Nat.zero_le c')
      by_cases h1 : i < c + 1
      · by_cases h2 : i = j
        · subst h2
          simp only [Expr.shift, if_pos h1, Expr.subst]
          rw [if_pos trivial, hs, hs]
        · by_cases h3 : i > j
          · have h4 : ¬ (i - 1 < j) := by omega
            have h5 : i - 1 + 1 < c + 1 := by omega
            simp only [Expr.shift, if_pos h1, Expr.subst, if_neg h2, if_pos h3, if_neg h4, if_pos h5]
          · have h4 : i < j := by omega
            simp only [Expr.shift, if_pos h1, Expr.subst, if_neg h2, if_neg h3, if_pos h4]
      · have h2 : ¬ (i + d = j) := by omega
        have h3 : i + d > j := by omega
        have h4 : ¬ (i = j) := by omega
        have h5 : i > j := by omega
        have h6 : ¬ (i + d - 1 < j) := by omega
        have h7 : ¬ (i - 1 < j) := by omega
        have h8 : ¬ (i - 1 + 1 < c + 1) := by omega
        simp only [Expr.shift, if_neg h1, Expr.subst, if_neg h2, if_pos h3, if_neg h4, if_pos h5,
          if_neg h6, if_neg h7, if_neg h8]
        congr 1; omega
  | .unit, _, _, _ => rfl
  | .pair a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h, fill_shift hV d b j c h]
  | .inj₁ a, j, c, h => by simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h]
  | .inj₂ a, j, c, h => by simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h]
  | .lam b, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV,
        fill_shift hV d b (j + 1) (c + 1) (by omega)]
  | .loc _, _, _, _ => rfl
  | .prim _, _, _, _ => rfl
  | .seq a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h, fill_shift hV d b j c h]
  | .letpair a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV, fill_shift hV d a j c h,
        fill_shift hV d b (j + 2) (c + 2) (by omega)]
  | .case a b e, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV, fill_shift hV d a j c h,
        fill_shift hV d b (j + 1) (c + 1) (by omega), fill_shift hV d e (j + 1) (c + 1) (by omega)]
  | .app f a, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d f j c h, fill_shift hV d a j c h]

/-- **`N` is closed where its filling is**, at a bound above the filled variable. -/
theorem closedAt_of_fill {V : Val} (hV : closedAt 0 V.1 = true) :
    ∀ (N : Expr) (j m : Nat), j < m → closedAt m ((N.subst j V).shift 1 j) = true →
      closedAt m N = true
  | .var i, j, m, hjm, h => by
      simp only [closedAt, decide_eq_true_eq]
      by_cases h2 : i = j
      · omega
      · by_cases h3 : i > j
        · have h4 : ¬ (i - 1 < j) := by omega
          simp only [Expr.subst, if_neg h2, if_pos h3, Expr.shift, if_neg h4, closedAt,
            decide_eq_true_eq] at h
          omega
        · have h4 : i < j := by omega
          simp only [Expr.subst, if_neg h2, if_neg h3, Expr.shift, if_pos h4, closedAt,
            decide_eq_true_eq] at h
          omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b j m hjm h.2⟩
  | .inj₁ a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt] at h ⊢; exact closedAt_of_fill hV a j m hjm h
  | .inj₂ a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt] at h ⊢; exact closedAt_of_fill hV a j m hjm h
  | .lam b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, val_shift_closed hV] at h ⊢
      exact closedAt_of_fill hV b (j + 1) (m + 1) (by omega) h
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b j m hjm h.2⟩
  | .letpair a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true, val_shift_closed hV] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b (j + 2) (m + 2) (by omega) h.2⟩
  | .case a b e, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true, val_shift_closed hV] at h ⊢
      exact ⟨⟨closedAt_of_fill hV a j m hjm h.1.1,
        closedAt_of_fill hV b (j + 1) (m + 1) (by omega) h.1.2⟩,
        closedAt_of_fill hV e (j + 1) (m + 1) (by omega) h.2⟩
  | .app f a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV f j m hjm h.1, closedAt_of_fill hV a j m hjm h.2⟩

end Targets

end
