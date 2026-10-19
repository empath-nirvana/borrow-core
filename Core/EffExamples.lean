import Core.Demonic

/-!
# Core — a handled program, typed and run  `[spec §19]`

`handle_1 (perform (1, (0, ()))) with (λx. x, (λp. let (x, k) = p; k.resume x, ()))`: one linear
operation `1 ↠ 1`, whose clause resumes `κ` once. The program is typed at `F 1` by §19's rules
(`effHandle`, `effPerform`), so `adequacyD` runs every run of it to `()` at the empty memory.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.EffExamples
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The effect: one linear operation `1 ↠ 1`. -/
abbrev E₁ : List (Qual × VTy × VTy) := [(.lin, .unit, .unit)]

/-- The clause `λp. let (x, k) = p; (k (inj₁ ())) x`: resume `κ` with the argument. -/
def cl₀ : Expr := .val (.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 1))))

/-- The clauses `(cl₀, ())`. -/
def cls : Expr := .pair cl₀ (.val .unit)

/-- `h_ret = λx. x`. -/
def hr : Expr := .val (.lam (.var 0))

/-- The program. -/
def prog : Expr :=
  bindE cls (bindE hr (hndTerm 1 [.lin] 0 1 (performE (opArgE 1 0 (.val .unit)))))

theorem cl₀_derives : CDerives LifeCtx.empty [] cl₀ (.val (clauseTy [] .unit (.lin, .unit, .unit))) := by
  refine .bangThunkV (fun _ hs => by simp at hs) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .app (.left (.right (.dead .nil)))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) .top) (.here (.cons (.cons .nil)))))
    (.there (.here (.cons .nil)))

theorem prog_derives : CDerives LifeCtx.empty [] prog (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil cl₀_derives (.unitI .nil))) ?_
  refine .bind (.right .nil)
    (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun s hs hl => by
      simp at hs; subst hs; simp at hl) rfl (.lam (.ret (.var (.here (.cons .nil))))))) ?_
  exact .effHandle (S := []) (E := E₁) (A := .unit) (R := .unit)
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp) rfl
    (.effPerform (o := ⟨1, 0, .lin, .unit, .unit, .ret .unit⟩) (by rfl) rfl (.unitI (.cons (.cons .nil))))

/-- **Every run of the handled program reaches `()` at the empty memory.** -/
theorem prog_runs {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem prog μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD prog_derives hs

/-! ### Cancelling `κ` -/

/-- The clause `λp. let (x, k) = p; x; k (inj₂ ())`: cancel `κ`. -/
def clC : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1) (.app (.var 0) (.val (.inj₂ .unit))))))

/-- The program with an affine operation whose clause cancels `κ`. -/
def progC : Expr :=
  bindE (.pair clC (.val .unit)) (bindE hr (hndTerm 1 [.aff] 0 1 (performE (opArgE 1 0 (.val .unit)))))

theorem clC_derives : CDerives LifeCtx.empty [] clC (.val (clauseTy [] .unit (.aff, .unit, .unit))) := by
  refine .bangThunkV (fun _ hs => by simp at hs) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .unitE (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil)))) ?_
  exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) (CTy.effOf [] .unit))
    (.here (.cons (.cons .nil))))

theorem progC_derives : CDerives LifeCtx.empty [] progC (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil clC_derives (.unitI .nil))) ?_
  refine .bind (.right .nil)
    (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun s hs hl => by
      simp at hs; subst hs; simp at hl) rfl (.lam (.ret (.var (.here (.cons .nil))))))) ?_
  exact .effHandle (S := []) (E := [(.aff, .unit, .unit)]) (A := .unit) (R := .unit)
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp) rfl
    (.effPerform (o := ⟨1, 0, .aff, .unit, .unit, .ret .unit⟩) (by rfl) rfl (.unitI (.cons (.cons .nil))))

/-- **Every run of the cancelling program reaches `()` at the empty memory.** -/
theorem progC_runs {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem progC μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD progC_derives hs

end BoCa.Fig16.LogRel.Core.EffExamples
