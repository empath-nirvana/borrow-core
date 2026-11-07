import Core.Chain.FoldG836N
import Core.Chain.Withload791N
import Core.FoldImm

/-!
# The borrowed fold on the chain: reductions  `[spec §6]`

Core's `foldImm_compatX` (`Core/FoldImm.lean`) at the chain, line by line: Core's term
(`foldImmV`, `travK`, `selfF`, `hV`) and its reductions, and Core's induction on a bound of the
borrowed cell's witness size and then on the view's size. `withload_sizedN` is Core's
`withload_sized` at the empty row: `withload_reb`, its callback handed the image's relation to the
loaded witness (`ResU.Reb β σ χ`), so the view handed over is `Good` at the witness's size
(`good_of_imageN`).

This file holds Core's reductions at `erwp` (`cbOf_appN`, `travK_appN`, `hV_appN`);
`FoldImmKW835N` holds `withload_sizedN`, `good_of_imageN` and the rule at `SemJN`
(`foldImm_compatN`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### Reductions -/

section Red
variable {Φ : LocFam} {Q : PostN}

theorem cbOf_appN (hΦ : Φ.Down) (hQ : Q.Down) (h w : Val) {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val h) (.val w)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (cbOf h)) (.val .unit)) (.val w)) ρ := by
  refine erwp_headE hΦ hQ (.appL .hole w) (fun μ => Head.beta μ _ Val.unit) rfl ?_
  have e : Expr.subst 0 Val.unit (h.1.shift 1 0) = h.1 := by
    rw [subst_shift_succ _ _ (Nat.le_refl 0), Expr.shift_zero]
  simpa [Kont.plug, e] using hw

theorem travK_appN (hΦ : Φ.Down) (hQ : Q.Down) (G : FShape) (h w : Val) {n : Nat}
    {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (((tB G).subst 1 (h.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (travK G)) (.val h)) (.val w)) ρ := by
  rw [travK_eq]
  refine erwp_headE hΦ hQ (.appL .hole w) (fun μ => Head.beta μ _ h) rfl ?_
  exact erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ w) rfl hw

/-- `h w` for `h = λw. self g w` reaches `travK T h w to r. g [] r` (Core's `hV_app`). -/
theorem hV_appN (hΦ : Φ.Down) (hQ : Q.Down) (F : FShape) (g w : Val) {n : Nat}
    {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((Kont.appR (.val (.lam (.app (.app (.val (g.shift 1 0)) (.val .unit)) (.var 0)))) .hole).plug
        (.app (.app (.val (travK F)) (.val (hV F g))) (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hV F g)) (.val w)) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ w) rfl ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfF F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfF F)) (.val g)) (.val w) := by
    simp [closed_subst (selfF_closed F), subst_shift_succ]
  simp only [Kont.plug]
  rw [e₁]
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fB_closed F) (.appL .hole w) g) ?_
  rw [fixV_eq (fB_closed F)]
  refine erwp_headE hΦ hQ (.appL .hole w) (fun μ => Head.beta μ _ g) rfl ?_
  rw [fB_subst F (selfF_closed F)]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ w) rfl ?_
  rw [fB_body F (selfF_closed F)]
  exact hw

end Red

section Trav
variable (M R : VTy) (y : LifeVar) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (Nb : Nat)

end Trav

section Ind
variable {M R : VTy} {y : LifeVar} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {Nb : Nat}

end Ind

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
