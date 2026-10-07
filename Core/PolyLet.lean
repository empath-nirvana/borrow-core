import Core.Fix

/-!
# Core — the polymorphic let  `[spec §24]`

`let x = V in N` for a closed value `V`, typed by typing `N` with `V` in place of `x`
(`CDerives.letPoly`): the bound slot stays in the context, dead, and every occurrence of `V` in
`N` is typed on its own.  Terms carry no rows, so one closed λ-value is used at as many rows as its
occurrences have: this is the kernel's row polymorphism, as let-polymorphism by substitution.

`letPoly_compatC`: the rule is sound.  Its term steps by one β-step, which allocates nothing, to
`N` with `V` for `x` (`cC_head`); and closing that term, with `V` at the dead slot, is closing `N`
at `V` (`psub_fill`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head)
open BoCa.Lifetime (LSub LifeCtx)

/-- **Filling a bound variable with a closed value, its slot kept, then closing**: the same as
closing with the value at that slot.  `(N.subst k V).shift 1 k` is `N` with `V` for the variable
`k` and every other variable where it was. -/
theorem psub_fill {V : Val} (hV : closedAt 0 V.1 = true) (γ : List Val) :
    ∀ (N : Expr) (k : Nat),
      Expr.psub k (V :: γ) ((N.subst k V).shift 1 k) = Expr.psub k (V :: γ) N
  | .var i, k => by
      rcases Nat.lt_trichotomy i k with h | rfl | h
      · have h₁ : ¬ (i = k) := by omega
        have h₂ : ¬ (i > k) := by omega
        simp only [Expr.subst, if_neg h₁, if_neg h₂, Expr.shift, if_pos h]
      · simp only [Expr.subst]
        rw [if_pos trivial, shift_closedAt V.1 1 hV (Nat.zero_le i),
          psub_closedAt V.1 (V :: γ) hV (Nat.zero_le i)]
        simp only [Expr.psub, Nat.lt_irrefl, if_false, Nat.sub_self, List.getElem?_cons_zero,
          val_shift_closed hV]
      · have h₁ : ¬ (i = k) := by omega
        have h₃ : ¬ (i - 1 < k) := by omega
        simp only [Expr.subst, if_neg h₁, if_pos h, Expr.shift, if_neg h₃]
        rw [show i - 1 + 1 = i by omega]
  | .unit, _ => rfl
  | .pair a b, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, psub_fill hV γ a k, psub_fill hV γ b k]
  | .inj₁ a, k => by simp only [Expr.subst, Expr.shift, Expr.psub, psub_fill hV γ a k]
  | .inj₂ a, k => by simp only [Expr.subst, Expr.shift, Expr.psub, psub_fill hV γ a k]
  | .lam b, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, val_shift_closed hV, psub_fill hV γ b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, psub_fill hV γ a k, psub_fill hV γ b k]
  | .letpair a b, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, val_shift_closed hV, psub_fill hV γ a k,
        psub_fill hV γ b (k + 2)]
  | .case a b c, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, val_shift_closed hV, psub_fill hV γ a k,
        psub_fill hV γ b (k + 1), psub_fill hV γ c (k + 1)]
  | .app f a, k => by
      simp only [Expr.subst, Expr.shift, Expr.psub, psub_fill hV γ f k, psub_fill hV γ a k]

/-- **The polymorphic let** (`[let-poly]`): `let x = V in N`, for a closed value `V`, from `N`
with `V` for `x`, `x`'s slot dead.  `[spec §24]` -/
theorem letPoly_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (V : Val)
    (hV : closedAt 0 V.1 = true)
    (hN : SemC Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 V).shift 1 0) C) :
    SemC Δ Γ (.app (.val (.lam N)) (.val V)) C := by
  intro δ γ ls ρ hδ hg
  have h := hN δ (V :: γ) ls ρ hδ (gDenC_dead_cons .unit V hg)
  have e₁ : substAll (V :: γ) ((N.subst 0 V).shift 1 0) = (Expr.psub 1 γ N).subst 0 V := by
    show Expr.psub 0 (V :: γ) _ = _
    rw [psub_fill hV γ N 0, Expr.psub_cons 0 V γ N, Val.shift_zero]
  rw [e₁] at h
  show cC C ls δ (Expr.psub 0 γ (.app (.val (.lam N)) (.val V))) ρ
  simp only [Expr.psub]
  rw [psub_closedAt V.1 γ hV (Nat.zero_le 0)]
  exact cC_head C (fun μ => Head.beta μ (Expr.psub 1 γ N) V) rfl ls δ ρ h

end BoCa.Fig16.LogRel.Core

end
