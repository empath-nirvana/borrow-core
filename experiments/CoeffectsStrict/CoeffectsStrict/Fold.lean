import Core

/-!
# Data: `foldOwn` is the unique algebra homomorphism out of `μX. T`, on runs

The initial-algebra laws, stated about machine runs, at every shape `T` of `FShape`
(SPEC §6).  `in : T[μX.T/X] → μX.T` is `roll`, which is the identity on terms, so the
algebra map of the initial algebra is invisible at run time.

* **β (computation law)** `fold g ∘ in = g ∘ T(fold g)`:
  `fold_beta` — `fold g w` reaches `travO T (fold g) w to r. g r` by pure steps, at every
  shape and every value `w`.  `travO T h` is the functor's action on morphisms: the
  `functor_*` lemmas show it is the identity at a leaf, `h` at `X`, and componentwise at `⊗`
  and `⊕`.
* **Uniqueness (η)**: `fold_unique` — any `h` that satisfies the same equation as a
  reduction (an algebra homomorphism, `IsHom`) reaches the same value as `fold g` on every
  finite value built from leaves, `X`, `⊗` and `⊕` (`SV`), when the algebra `g` terminates on
  every input.

At `Ref X` the action frees a cell, a heap step, so `Ref X` positions are outside `SV` and
outside the uniqueness statement here.

A deep handler of an algebraic signature is a fold of its free model; `Handler.lean`
instantiates these laws at the free model of one operation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CoeffectsStrict
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head Kont)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- `e` reaches the value `v` by pure steps. -/
def Evals (e : Expr) (v : Val) : Prop := PureSteps (ℍ := ℍ) e (.val v)

/-- `x ← [·]; g x`, the continuation that hands a result to the algebra. -/
def algK (g : Val) : Kont := .appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole

theorem algK_plug_val (g r : Val) :
    PureSteps (ℍ := ℍ) ((algK g).plug (.val r)) (.app (.val g) (.val r)) := by
  refine (PureSteps.beta _ r).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- `foldOwn g ↦ λw. self g w`. -/
theorem foldOwn_app (F : FShape) (g : Val) :
    PureSteps (ℍ := ℍ) (.app (.val (foldOwnV F)) (.val g)) (.val (hO F g)) := by
  have := PureSteps.beta (ℍ := ℍ) (.val (.lam (.app (.app (.val (selfO F)) (.var 1)) (.var 0)))) g
  rwa [foldOwnV_subst] at this

/-- `(λw. self g w) w` reaches `travO T (λw. self g w) w to r. g r`: the unrolled fold. -/
theorem hO_steps (F : FShape) (g w : Val) :
    PureSteps (ℍ := ℍ) (.app (.val (hO F g)) (.val w))
      ((algK g).plug (.app (.app (.val (travO F)) (.val (hO F g))) (.val w))) := by
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfO F)) (.val (g.shift 1 0))) (.var 0))
      = (Kont.appL .hole w).plug (.app (.val (selfO F)) (.val g)) := by
    simp [Kont.plug, closed_subst (selfO_closed F), subst_shift_succ]
  refine (PureSteps.beta _ w).trans ?_
  rw [e₁]
  refine (selfV_steps_in (fBO_closed F) (.appL .hole w) g).trans ?_
  rw [fixV_eq (fBO_closed F)]
  refine (PureSteps.beta_in (.appL .hole w) _ g).trans ?_
  rw [fBO_subst F (selfO_closed F)]
  refine (PureSteps.beta _ w).trans ?_
  rw [fBO_body F (selfO_closed F)]
  exact .refl

/-- **β, the computation law of the initial algebra**: `fold g (in w)` reaches
`T(fold g) w to r. g r`, with `fold g = hO F g` the value `foldOwn g` reduces to. -/
theorem fold_beta (F : FShape) (g w : Val) :
    PureSteps (ℍ := ℍ) (.app (.app (.val (foldOwnV F)) (.val g)) (.val w))
      ((algK g).plug (.app (.app (.val (travO F)) (.val (hO F g))) (.val w))) :=
  (PureSteps.plug (.appL .hole w) (foldOwn_app F g)).trans (hO_steps F g w)

/-- The β law in its run form: if the functor's action reaches `r`, the fold reaches `g r`. -/
theorem fold_beta_run (F : FShape) (g w r : Val)
    (hr : Evals (ℍ := ℍ) (.app (.app (.val (travO F)) (.val (hO F g))) (.val w)) r) :
    PureSteps (ℍ := ℍ) (.app (.val (hO F g)) (.val w)) (.app (.val g) (.val r)) :=
  (hO_steps F g w).trans ((PureSteps.plug (algK g) hr).trans (algK_plug_val g r))

/-! ### `travO` is the functor's action on morphisms -/

/-- `travO G h w ↦ tO G[h, w]`. -/
theorem travO_steps (G : FShape) (h w : Val) :
    PureSteps (ℍ := ℍ) (.app (.app (.val (travO G)) (.val h)) (.val w))
      (((tO G).subst 1 (h.shift 1 0)).subst 0 w) := by
  rw [travO_eq]
  refine (PureSteps.beta_in (.appL .hole w) _ h).trans ?_
  have : (Expr.val (.lam (tO G))).subst 0 h = .val (.lam ((tO G).subst 1 (h.shift 1 0))) := by
    simp
  rw [this]
  exact PureSteps.beta _ w

/-- At a leaf, the identity. -/
theorem functor_leaf (A : VTy) (h w : Val) :
    Evals (ℍ := ℍ) (.app (.app (.val (travO (.leaf A))) (.val h)) (.val w)) w := by
  have := travO_steps (ℍ := ℍ) (.leaf A) h w
  rwa [tO_leaf] at this

/-- At `X`, the morphism itself. -/
theorem functor_varX (h w : Val) :
    PureSteps (ℍ := ℍ) (.app (.app (.val (travO .varX)) (.val h)) (.val w)) (.app (.val h) (.val w)) := by
  have := travO_steps (ℍ := ℍ) .varX h w
  rwa [tO_varX] at this

/-- At `⊕`, left. -/
theorem functor_sum₁ (F G : FShape) (h v r : Val)
    (hr : Evals (ℍ := ℍ) (.app (.app (.val (travO F)) (.val h)) (.val v)) r) :
    Evals (ℍ := ℍ) (.app (.app (.val (travO (.sum F G))) (.val h)) (.val (.inj₁ v))) (.inj₁ r) := by
  refine (travO_steps _ h _).trans ?_
  rw [tO_sum]
  refine (PureSteps.head (fun μ => Head.case₁ μ v _ _) rfl).trans ?_
  rw [sumO_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
  refine (PureSteps.plug _ hr).trans ?_
  refine (PureSteps.beta _ r).trans ?_
  simp
  exact inj₁_steps .refl

/-- At `⊕`, right. -/
theorem functor_sum₂ (F G : FShape) (h v r : Val)
    (hr : Evals (ℍ := ℍ) (.app (.app (.val (travO G)) (.val h)) (.val v)) r) :
    Evals (ℍ := ℍ) (.app (.app (.val (travO (.sum F G))) (.val h)) (.val (.inj₂ v))) (.inj₂ r) := by
  refine (travO_steps _ h _).trans ?_
  rw [tO_sum]
  refine (PureSteps.head (fun μ => Head.case₂ μ v _ _) rfl).trans ?_
  rw [sumO_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
  refine (PureSteps.plug _ hr).trans ?_
  refine (PureSteps.beta _ r).trans ?_
  simp
  exact inj₂_steps .refl

/-- At `⊗`, componentwise, left to right. -/
theorem functor_tensor (F G : FShape) (h v₁ v₂ r₁ r₂ : Val)
    (h₁ : Evals (ℍ := ℍ) (.app (.app (.val (travO F)) (.val h)) (.val v₁)) r₁)
    (h₂ : Evals (ℍ := ℍ) (.app (.app (.val (travO G)) (.val h)) (.val v₂)) r₂) :
    Evals (ℍ := ℍ) (.app (.app (.val (travO (.tensor F G))) (.val h)) (.val (.pair v₁ v₂)))
      (.pair r₁ r₂) := by
  refine (travO_steps _ h _).trans ?_
  rw [tO_tensor]
  refine (PureSteps.head (fun μ => Head.letpair μ v₁ v₂ _) rfl).trans ?_
  rw [tensorO_body]
  refine (PureSteps.plug _ h₁).trans ?_
  refine (PureSteps.beta _ r₁).trans ?_
  rw [tensorO_body₂]
  refine (PureSteps.plug _ h₂).trans ?_
  refine (PureSteps.beta _ r₂).trans ?_
  simp
  exact pair_steps .refl .refl

/-! ### Uniqueness -/

/-- Finite values of the shape `G` inside `μX. F`, with `X` read as `F` again: built from
leaves, `X`, `⊗` and `⊕` (no `Ref X`, whose action is a heap step). -/
inductive SV (F : FShape) : FShape → Val → Prop
  | leaf (A : VTy) (w : Val) : SV F (.leaf A) w
  | varX {w : Val} : SV F F w → SV F .varX w
  | tensor {G₁ G₂ : FShape} {v₁ v₂ : Val} : SV F G₁ v₁ → SV F G₂ v₂ → SV F (.tensor G₁ G₂) (.pair v₁ v₂)
  | sum₁ {G₁ G₂ : FShape} {v : Val} : SV F G₁ v → SV F (.sum G₁ G₂) (.inj₁ v)
  | sum₂ {G₁ G₂ : FShape} {v : Val} : SV F G₂ v → SV F (.sum G₁ G₂) (.inj₂ v)

/-- `h` is an algebra homomorphism from `in` to `g`, as a reduction: whenever the functor's
action `T(h) w` reaches `r`, `h w` reaches `g r`.  `fold g` is one (`fold_isHom`). -/
def IsHom (F : FShape) (g h : Val) : Prop :=
  ∀ w r, Evals (ℍ := ℍ) (.app (.app (.val (travO F)) (.val h)) (.val w)) r →
    PureSteps (ℍ := ℍ) (.app (.val h) (.val w)) (.app (.val g) (.val r))

theorem fold_isHom (F : FShape) (g : Val) : IsHom (ℍ := ℍ) F g (hO F g) :=
  fun w r hr => fold_beta_run F g w r hr

/-- The algebra terminates on every input. -/
def Total (g : Val) : Prop := ∀ x, ∃ r, Evals (ℍ := ℍ) (.app (.val g) (.val x)) r

/-- Two homomorphisms from `in` to a total `g` reach one common value at every finite value
of every sub-shape. -/
theorem homs_agree {F : FShape} {g h₁ h₂ : Val} (hg : Total (ℍ := ℍ) g)
    (e₁ : IsHom (ℍ := ℍ) F g h₁) (e₂ : IsHom (ℍ := ℍ) F g h₂) :
    ∀ {G : FShape} {w : Val}, SV F G w → ∃ r,
      Evals (ℍ := ℍ) (.app (.app (.val (travO G)) (.val h₁)) (.val w)) r ∧
      Evals (ℍ := ℍ) (.app (.app (.val (travO G)) (.val h₂)) (.val w)) r := by
  intro G w hw
  induction hw with
  | leaf A w => exact ⟨w, functor_leaf A h₁ w, functor_leaf A h₂ w⟩
  | varX _ ih =>
      obtain ⟨r', a₁, a₂⟩ := ih
      obtain ⟨r, hr⟩ := hg r'
      exact ⟨r, (functor_varX _ _).trans ((e₁ _ _ a₁).trans hr),
        (functor_varX _ _).trans ((e₂ _ _ a₂).trans hr)⟩
  | tensor _ _ ih₁ ih₂ =>
      obtain ⟨r₁, a₁, b₁⟩ := ih₁
      obtain ⟨r₂, a₂, b₂⟩ := ih₂
      exact ⟨.pair r₁ r₂, functor_tensor _ _ _ _ _ _ _ a₁ a₂, functor_tensor _ _ _ _ _ _ _ b₁ b₂⟩
  | sum₁ _ ih =>
      obtain ⟨r, a, b⟩ := ih
      exact ⟨.inj₁ r, functor_sum₁ _ _ _ _ _ a, functor_sum₁ _ _ _ _ _ b⟩
  | sum₂ _ ih =>
      obtain ⟨r, a, b⟩ := ih
      exact ⟨.inj₂ r, functor_sum₂ _ _ _ _ _ a, functor_sum₂ _ _ _ _ _ b⟩

/-- **Uniqueness of the fold**: every algebra homomorphism `h` from `in` to a total algebra
`g` reaches the same value as `fold g` on every finite value of `μX. T`. -/
theorem fold_unique {F : FShape} {g h : Val} (hg : Total (ℍ := ℍ) g) (eh : IsHom (ℍ := ℍ) F g h)
    {w : Val} (hw : SV F F w) :
    ∃ r, Evals (ℍ := ℍ) (.app (.val h) (.val w)) r ∧
      Evals (ℍ := ℍ) (.app (.app (.val (foldOwnV F)) (.val g)) (.val w)) r := by
  obtain ⟨r', a₁, a₂⟩ := homs_agree hg eh (fold_isHom F g) hw
  obtain ⟨r, hr⟩ := hg r'
  exact ⟨r, (eh _ _ a₁).trans hr,
    (PureSteps.plug (.appL .hole w) (foldOwn_app F g)).trans ((fold_isHom F g _ _ a₂).trans hr)⟩

end BoCa.Fig16.LogRel.Core.CoeffectsStrict

end
