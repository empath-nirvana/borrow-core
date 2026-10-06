import Core.Fundamental
import Targets.Base.CoreCancel
import Targets.Base.Typing

/-!
# The Instance — no typed term intercepts a cancel, at tier 1 (DESIGN §9 item 12)

`noInterception_tier1 : NoInterception tier1` (typed
terms hold no `ccatch`, no `cfin`, and no handler named `0`), by induction on `CDerives`.  It reads
base's `NoInterception` and Core's typing only: the syntactic route to A's `NoIntercept` at our
instance (RESTRUCTURE §4.1).  PROVED AT σ=[].
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE raiseE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The three conditions of I3.c on one term, decided together. -/
def okE : Expr → Bool
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m != 0 && okE r
  | .prim p => p != .hnd && p != .ccatch && p != .cfin
  | .var _ | .unit | .loc _ => true
  | .pair a b | .seq a b | .letpair a b | .app a b => okE a && okE b
  | .inj₁ a | .inj₂ a | .lam a => okE a
  | .case a b c => okE a && okE b && okE c

theorem okE_sound (e : Expr) (h : okE e = true) :
    ¬ e.HasPrim .ccatch ∧ ¬ e.HasPrim .cfin ∧ e.HndNamesNZ := by
  fun_induction okE e with
  | case1 m r ih =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨h₁, h₂, h₃⟩ := ih h.2
      refine ⟨?_, ?_, ?_⟩
      · simp [Expr.HasPrim, h₁]
      · simp [Expr.HasPrim, h₂]
      · simp only [Expr.HndNamesNZ]; exact ⟨h.1, h₃⟩
  | case2 p =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      refine ⟨?_, ?_, ?_⟩
      · simp only [Expr.HasPrim]; exact h.1.2
      · simp only [Expr.HasPrim]; exact h.2
      · simp only [Expr.HndNamesNZ]; exact h.1.1
  | case3 => exact ⟨by simp [Expr.HasPrim], by simp [Expr.HasPrim], by simp [Expr.HndNamesNZ]⟩
  | case4 => exact ⟨by simp [Expr.HasPrim], by simp [Expr.HasPrim], by simp [Expr.HndNamesNZ]⟩
  | case5 => exact ⟨by simp [Expr.HasPrim], by simp [Expr.HasPrim], by simp [Expr.HndNamesNZ]⟩
  | case6 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨a₁, a₂, a₃⟩ := iha h.1
      obtain ⟨b₁, b₂, b₃⟩ := ihb h.2
      exact ⟨by simp [Expr.HasPrim, a₁, b₁], by simp [Expr.HasPrim, a₂, b₂],
        by simp only [Expr.HndNamesNZ]; exact ⟨a₃, b₃⟩⟩
  | case7 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨a₁, a₂, a₃⟩ := iha h.1
      obtain ⟨b₁, b₂, b₃⟩ := ihb h.2
      exact ⟨by simp [Expr.HasPrim, a₁, b₁], by simp [Expr.HasPrim, a₂, b₂],
        by simp only [Expr.HndNamesNZ]; exact ⟨a₃, b₃⟩⟩
  | case8 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨a₁, a₂, a₃⟩ := iha h.1
      obtain ⟨b₁, b₂, b₃⟩ := ihb h.2
      exact ⟨by simp [Expr.HasPrim, a₁, b₁], by simp [Expr.HasPrim, a₂, b₂],
        by simp only [Expr.HndNamesNZ]; exact ⟨a₃, b₃⟩⟩
  | case9 a b hab iha ihb =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨a₁, a₂, a₃⟩ := iha h.1
      obtain ⟨b₁, b₂, b₃⟩ := ihb h.2
      refine ⟨by simp [Expr.HasPrim, a₁, b₁], by simp [Expr.HasPrim, a₂, b₂], ?_⟩
      rw [Expr.HndNamesNZ.eq_9 a b hab]
      exact ⟨a₃, b₃⟩
  | case10 a iha =>
      obtain ⟨a₁, a₂, a₃⟩ := iha h
      exact ⟨by simp [Expr.HasPrim, a₁], by simp [Expr.HasPrim, a₂],
        by simp only [Expr.HndNamesNZ]; exact a₃⟩
  | case11 a iha =>
      obtain ⟨a₁, a₂, a₃⟩ := iha h
      exact ⟨by simp [Expr.HasPrim, a₁], by simp [Expr.HasPrim, a₂],
        by simp only [Expr.HndNamesNZ]; exact a₃⟩
  | case12 a iha =>
      obtain ⟨a₁, a₂, a₃⟩ := iha h
      exact ⟨by simp [Expr.HasPrim, a₁], by simp [Expr.HasPrim, a₂],
        by simp only [Expr.HndNamesNZ]; exact a₃⟩
  | case13 a b c iha ihb ihc =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨a₁, a₂, a₃⟩ := iha h.1.1
      obtain ⟨b₁, b₂, b₃⟩ := ihb h.1.2
      obtain ⟨c₁, c₂, c₃⟩ := ihc h.2
      exact ⟨by simp [Expr.HasPrim, a₁, b₁, c₁], by simp [Expr.HasPrim, a₂, b₂, c₂],
        by simp only [Expr.HndNamesNZ]; exact ⟨a₃, b₃, c₃⟩⟩

theorem okE_app {a b : Expr} (ha : okE a = true) : okE (.app a b) = okE b := by
  rw [okE.eq_9 a b (fun m r h₁ _ => by subst h₁; simp [okE] at ha)]
  simp [ha]

theorem okE_lam (b : Expr) : okE (Val.lam b).1 = okE b := rfl

theorem okE_travK : ∀ F : FShape, okE (travK F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travK, bindE, okE, okE_app, okE_travK F, okE_travK G]
  | .sum F G => by
      simp [travK, bindE, okE, okE_app, okE_travK F, okE_travK G]

theorem okE_travO : ∀ F : FShape, okE (travO F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travO, bindE, okE, okE_app, okE_travO F, okE_travO G]
  | .sum F G => by
      simp [travO, bindE, okE, okE_app, okE_travO F, okE_travO G]

theorem okE_travR : ∀ F : FShape, okE (travR F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travR, bindE, okE, okE_app, okE_travR F, okE_travR G]
  | .sum F G => by
      simp [travR, bindE, okE, okE_app, okE_travR F, okE_travR G]

theorem okE_selfV {B : Expr} (hB : okE B = true) : okE (selfV B).1 = true := by
  simp [selfV, zX, okE, hB]

theorem okE_foldImmV (F : FShape) : okE (foldImmV F).1 = true := by
  have hB : okE (fB F) = true := by simp [fB, bindE, okE, okE_app, okE_travK]
  simp [foldImmV, okE, okE_app, okE_travK, okE_selfV hB]

theorem okE_foldOwnV (F : FShape) : okE (foldOwnV F).1 = true := by
  have hB : okE (fBO F) = true := by simp [fBO, bindE, okE, okE_app, okE_travO]
  simp [foldOwnV, okE, okE_app, okE_selfV hB]

theorem okE_foldReuseV (F : FShape) : okE (foldReuseV F).1 = true := by
  have hB : okE (fBR F) = true := by simp [fBR, bindE, okE, okE_app, okE_travR]
  simp [foldReuseV, okE, okE_app, okE_selfV hB]

theorem okE_mapV : ∀ A : VTy, okE (mapV A).1 = true
  | .tvar 0 => rfl
  | .tensor A B => by simp [mapV, okE, okE_app, okE_mapV A, okE_mapV B]
  | .sum A B => by simp [mapV, okE, okE_app, okE_mapV A, okE_mapV B]
  | .box _ A => okE_mapV A
  | .tvar (_ + 1) | .unit | .zero | .thunk _ | .ref _ | .imm _ _ | .mut _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

theorem okE_nodeV : ∀ C : CTy, okE (nodeV C).1 = true
  | .ret A => by simp [nodeV, bindE, okE, okE_app, okE_mapV]
  | .amp C D => by simp [nodeV, okE, okE_app, okE_nodeV C, okE_nodeV D]
  | .eff _ _ _ _ _ C => by simp [nodeV, bindE, okE, okE_app, okE_mapV]
  | .arr _ D => by simp [nodeV, okE, okE_app, okE_nodeV D]
  | .top | .all _ _ _ | .nu _ => rfl

theorem okE_unfoldV (C : CTy) : okE (unfoldV C).1 = true := by
  have hB : okE (fBN C) = true := by simp [fBN, okE, okE_app, okE_nodeV]
  simp [unfoldV, okE, okE_app, okE_selfV hB]

theorem okE_forceE_var (C : CTy) (i : Nat) : okE (forceE C (.var i)) = true := by
  cases C <;> rfl

theorem okE_withPair {M N : Expr} (hM : okE M = true) (hN : okE N = true) :
    okE (withPair M N) = true := by
  simp [withPair, okE, hM, hN]

theorem okE_withborUE {d : Expr} (hd : okE d = true) : okE (withborUE d) = true := by
  simp [withborUE, thenE, okE, okE_app, hd]

theorem okE_of_derives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : okE e = true := by
  induction h with
  | force => exact okE_forceE_var _ _
  | withI _ _ ihM ihN => exact okE_withPair ihM ihN
  | withbor1U _ _ _ _ _ _ _ _ _ ih => exact okE_withborUE ih
  | withbor2U _ _ _ _ _ _ _ _ _ ih => exact okE_withborUE ih
  | withbor3U _ _ _ _ _ _ _ _ ih => exact okE_withborUE ih
  | sliceBorrowMU _ _ _ _ _ _ _ _ _ ih => exact okE_withborUE ih
  | sliceBorrowIU _ _ _ _ _ _ _ _ _ _ ih => exact okE_withborUE ih
  | foldImm => exact okE_foldImmV _
  | foldOwn => exact okE_foldOwnV _
  | foldReuse => exact okE_foldReuseV _
  | unfoldN => exact okE_unfoldV _
  | lolliE _ _ _ iha ihf => rw [okE_app ihf]; exact iha
  | effHandle _ _ _ _ hn0 _ _ _ ih =>
      simp [hndTerm, Val.i32, okE, okE_app, ih, hn0]
  | _ => first | rfl | simp_all [okE, okE_app, absurdE, thenE, performE, raiseE, opArgE, Val.i32]

/-- Every row context admits the environment of empty rows. -/
theorem models_empty (Θ : RowCtx) : Θ.Models (fun _ => []) := by
  intro ρ c _
  refine ⟨?_, fun o ho => absurd ho (by simp)⟩
  rcases c with ⟨cls, adm⟩
  cases cls <;> simp [RowClass.Admits, Row.NU, Row.find]

/-- **`NoInterception tier1`** (I3.c). -/
theorem noInterception_tier1 : NoInterception tier1 := by
  intro Θ Δ Γ e j h
  exact okE_sound e (okE_of_derives (h _ (models_empty Θ)))

end Targets

end
