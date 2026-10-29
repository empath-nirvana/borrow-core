import NestedFold.Loop

/-!
# NestedFold — the dispatch

`selfD ks G` applied to the tag of the `i`-th binder `b` runs `b`'s branch: the traversal of
`b`'s body with the handle `selfD` itself, then `b`'s algebra (`selfD_run`). Three β-steps into
the Z combinator (`wpTS_selfV`), one to substitute the tag, and `i + 1` case steps.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open Classical

section
variable (ks : List Stack) (G : Algs)

/-- The dispatch with the fixed point substituted. -/
def dspV (sv : Val) : List Stack → Expr
  | [] => .var 0
  | b :: r => .case (.var 0)
      (bindE (.app (.app (.val (travB ks G b)) (.val sv)) (.var 0)) (.app (.val (G.alg b)) (.var 0)))
      (dspV sv r)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem dsp_subst {sv : Val} (hsv : closedAt 0 sv.1 = true) :
    ∀ (r : List Stack) (j : Nat), 1 ≤ j → (dsp ks G j r).subst j sv = dspV ks G sv r
  | [], j, hj => by
      simp only [dsp, dspV, Expr.subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | b :: r, j, hj => by
      have ih := dsp_subst hsv r (j + 1) (by omega)
      simp only [dsp, dspV, Expr.subst, val_shift_closed hsv, ih]
      rw [if_neg (by omega), if_neg (by omega)]
      simp [bindE, closed_subst (travB_closed ks G b), closed_subst (G.alg_closed b)]

theorem dspV_closed {sv : Val} (hsv : closedAt 0 sv.1 = true) :
    ∀ r : List Stack, closedAt 1 (dspV ks G sv r) = true
  | [] => rfl
  | b :: r => by
      have h₁ := dspV_closed hsv r
      have h₂ := closedAt_mono _ (G.alg_closed b) (Nat.zero_le 3)
      have h₃ := closedAt_mono _ (travB_closed ks G b) (Nat.zero_le 2)
      have h₄ := closedAt_mono _ hsv (Nat.zero_le 2)
      have h₂' : closedAt 2 (Val.lam ((G.alg b).1.app (Expr.var 0))).1 = true := by
        simp [closedAt, h₂]
      have h₁' := closedAt_mono _ h₁ (show 1 ≤ 2 by omega)
      simp [dspV, bindE, closedAt, h₁', h₃, h₂, h₄]

theorem dspV_run {sv : Val} (hsv : closedAt 0 sv.1 = true) (w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    ∀ (r : List Stack) (i : Nat) (b : Stack), r[i]? = some b →
      Entails (wpTS ls ((Kont.appR (.val (.lam (.app (.val (G.alg b)) (.var 0)))) .hole).plug
          (.app (.app (.val (travB ks G b)) (.val sv)) (.val w))) Q)
        (wpTS ls ((dspV ks G sv r).subst 0 (tagV i w)) Q)
  | [], _, _, h => by simp at h
  | c :: r, 0, b, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      intro ρ hw
      have e : (dspV ks G sv (c :: r)).subst 0 (tagV 0 w)
          = .case (.val (.inj₁ w))
              (bindE (.app (.app (.val (travB ks G c)) (.val sv)) (.var 0))
                (.app (.val (G.alg c)) (.var 0)))
              (dspV ks G sv r) := by
        simp only [dspV, Expr.subst, if_pos, tagV]
        rw [subst_closedAt _ _ (dspV_closed ks G hsv r) (le_refl 1)]
        simp [bindE, closed_subst (travB_closed ks G c), closed_subst (G.alg_closed c),
          closed_subst hsv]
      rw [e]
      refine wpTS_sum₁ ls w _ _ Q ρ ?_
      simpa [bindE, Kont.plug, closed_subst (travB_closed ks G c), closed_subst (G.alg_closed c),
        closed_subst hsv, closed_shift hsv] using hw
  | c :: r, i + 1, b, h => by
      simp only [List.getElem?_cons_succ] at h
      intro ρ hw
      have e : (dspV ks G sv (c :: r)).subst 0 (tagV (i + 1) w)
          = .case (.val (.inj₂ (tagV i w)))
              (bindE (.app (.app (.val (travB ks G c)) (.val sv)) (.var 0))
                (.app (.val (G.alg c)) (.var 0)))
              (dspV ks G sv r) := by
        simp only [dspV, Expr.subst, if_pos, tagV]
        rw [subst_closedAt _ _ (dspV_closed ks G hsv r) (le_refl 1)]
        simp [bindE, closed_subst (travB_closed ks G c), closed_subst (G.alg_closed c),
          closed_subst hsv]
      rw [e]
      exact wpTS_sum₂ ls (tagV i w) _ _ Q ρ (dspV_run hsv w ls Q r i b h ρ hw)

/-- **The dispatch.**  At the tag of the `i`-th binder `b`, the recursive call runs `b`'s
traversal with itself as the handle, then `b`'s algebra. -/
theorem selfD_run (i : Nat) (b : Stack) (hb : ks[i]? = some b) (w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((Kont.appR (.val (.lam (.app (.val (G.alg b)) (.var 0)))) .hole).plug
        (.app (.app (.val (travB ks G b)) (.val (selfD ks G))) (.val w))) Q)
      (wpTS ls (.app (.val (selfD ks G)) (.val (tagV i w))) Q) := by
  intro ρ hw
  refine wpTS_selfV (dsp_closed ks G ks 1) (tagV i w) ls Q ρ ?_
  rw [fixV_eq (dsp_closed ks G ks 1)]
  refine wpTS_lolli ls _ (tagV i w) Q ρ ?_
  change wpTS ls (Expr.subst 0 _ (Expr.subst 1 (selfD ks G) _)) Q ρ
  rw [dsp_subst ks G (selfD_closed ks G) ks 1 le_rfl]
  exact dspV_run ks G (selfD_closed ks G) w ls Q ks i b hb ρ hw

/-- The handle of binder `b`, applied, is the recursive call at `b`'s tag. -/
theorem hdl_app (b : Stack) (w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.val (selfD ks G)) (.val (tagV (ks.idxOf b) w))) Q)
      (wpTS ls (.app (.val (hdl ks G b)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_lolli ls _ w Q ρ ?_
  simpa [tagE_subst, closed_subst (selfD_closed ks G), tagE_val] using hw

end

end BoCa.Fig16.LogRel.Core.NestedFold

end
