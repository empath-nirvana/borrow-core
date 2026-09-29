import CoeffectsStrict.Fold

/-!
# Coeffects: which context modalities of the core are comonads

A coeffect in the sense of Petricek–Orchard–Mycroft and Brunel et al. is a (graded) comonad
on value types, applied to the context.  This file checks the core's context modalities
against the comonad laws, syntactically (`CDerives`) and in the model (`vCE`).

* **`Imm 'a U` is a comonoid.**  `copy` is the diagonal (`copy_diag`) and `forget` the
  counit (`forget_steps`), so `Imm 'a U ⊗ −` is the product (reader) comonad, the
  implicit-parameter coeffect.
* **`!A`**: dereliction (`bangE`), contraction (`copyBang`), weakening (`forgetBang`) are
  rules; digging `!A ⊸ !!A` is not, since promotion applies only to `λ`/`Λ`.  In the model
  `!!A` and `!A` are the same predicate (`bang_idem`), so digging holds semantically.
* **`[@a]A`**: the counit is `boxE` (`d_box_counit`).  Comultiplication at a shorter index is
  derivable: `[@b]A ⊸ [@a][@b]A` when `a ⊏ b` (`d_box_dig`).  At the same index it needs
  `[@a]A ⊐ @a`, which `VOutlives` gives only for `a ⊏ a`.  In the model `[@a][@a]A` and
  `[@a]A` are the same predicate (`box_idem`), so the same-index comultiplication holds
  semantically.
* **Thunks**: `U C` outlives no lifetime (`thunk_not_outlives`), while `μ` is checked
  structurally (`mu_outlives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CoeffectsStrict
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### `Imm`: a comonoid -/

/-- `copy v ↦* (v, v)`: `copy` is the diagonal. -/
theorem copy_diag (v : Val) : Evals (ℍ := ℍ) (.app copy (.val v)) (.pair v v) := by
  refine (PureSteps.beta _ v).trans ?_
  simp [v0]
  exact pair_steps .refl .refl

/-- `forget v ↦* ()`: `forget` is the counit. -/
theorem forget_steps (v : Val) : Evals (ℍ := ℍ) (.app forget (.val v)) .unit := by
  refine (PureSteps.beta _ v).trans ?_
  simp [unit']
  exact .refl

/-- The comonoid's counit law, on runs: copying and forgetting either copy gives back `v`
(the pair `(v, ())` or `((), v)`, the unitor's image of `v`). -/
theorem copy_counit (v : Val) :
    Evals (ℍ := ℍ) (.letpair (.app copy (.val v)) (.pair (.var 1) (.app forget (.var 0))))
      (.pair v .unit) := by
  refine (PureSteps.plug (.letpair .hole _) (copy_diag v)).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ v v _) rfl).trans ?_
  simp
  exact (PureSteps.plug (.pairR v .hole) (forget_steps v)).trans (pair_steps .refl .refl)

/-- The typing of `copy` and `forget` at `Imm 'a U`: the comonoid is in the judgment. -/
theorem d_imm_comonoid {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) (a : Lifetime.Life) (U : VTy) :
    CDerives Δ Γ copy (.val (axCopyTy a U)) ∧ CDerives Δ Γ forget (.val (axForgetImmTy a U)) :=
  ⟨.copy hΓ, .forgetImm hΓ⟩

/-! ### `!`: an idempotent comonad in the model -/

/-- `!!A` and `!A` are the same predicate. -/
theorem bang_idem (η : Option (Nat → TEnt)) (b : Bool) (A : VTy) (ls : List SRec) (δ : LSub)
    (v : Val) (ρ : WRes) :
    vCE η b (.bang (.bang A)) ls δ v ρ ↔ vCE η b (.bang A) ls δ v ρ := by
  simp only [vCE]
  constructor
  · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨h, h, h'⟩

/-! ### `[@a]`: a lifetime-indexed comonad -/

/-- The counit `[@a]A ⊸ A`. -/
theorem d_box_counit {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {a : Lifetime.Life} {A : VTy}
    (h : Ctx.SoloP Γ i (.box a A)) : CDerives Δ Γ (.var i) (.val A) :=
  .boxE (.var h)

/-- The comultiplication at a shorter index, `[@b]A ⊸ [@a][@b]A` for `a ⊏ b`. -/
theorem d_box_dig {Δ : LifeCtx} {a b : Lifetime.Life} {A : VTy} (hd : Δ.Defines a)
    (hlt : Δ.EntailsLt a b) :
    CDerives Δ [⟨.box b A, true⟩] (.var 0) (.val (.box a (.box b A))) :=
  .boxI (.var (.here .nil)) ⟨hd, fun s hs _ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact .box hlt⟩

/-- `[@a][@a]A` and `[@a]A` are the same predicate: the same-index comultiplication holds in
the model. -/
theorem box_idem (η : Option (Nat → TEnt)) (b : Bool) (a : Lifetime.Life) (A : VTy)
    (ls : List SRec) (δ : LSub) (v : Val) (ρ : WRes) :
    vCE η b (.box a (.box a A)) ls δ v ρ ↔ vCE η b (.box a A) ls δ v ρ := by
  simp only [vCE, atLife, box]
  constructor
  · rintro ⟨α, h, ⟨α', h', hp, ho'⟩, ho⟩
    exact ⟨α', h', hp, ho'⟩
  · rintro ⟨α, h, hp, ho⟩
    exact ⟨α, h, ⟨α, h, hp, ho⟩, ho⟩

/-! ### Thunks carry no lifetime bound -/

/-- No thunk outlives any lifetime: `U C` has no `VOutlives` rule, so a value of `U C` never
leaves a borrow scope (`withbor`'s callback returns `['x] T`, and `[]I` needs `T ⊐ @x`), even
when it captures no borrow.  Only `!U C` does (`VOutlives.bang`). -/
theorem thunk_not_outlives {Δ : LifeCtx} {a : Lifetime.Life} {C : CTy} :
    ¬ VOutlives Δ a (.thunk C) := by
  intro h; cases h

/-- `μ` is transparent to outlives: `μX. A ⊐ @a` from `A ⊐ @a`. -/
theorem mu_outlives {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutlives Δ a A) :
    VOutlives Δ a (.mu A) := .mu h

/-- Codata crosses a scope as data does: `[]I` boxes a thunk of `νX. C` at `@d` from a context
that outlives `@d` (a `Mut 'a` capture needs `'d ⊏ 'a`), the same rule that boxes `μX. A`. -/
theorem d_box_codata {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {d : Lifetime.Life} {C : CTy}
    (h : CDerives Δ Γ e (.val (.thunk (.nu C)))) (hΓ : CtxOutlives Δ Γ d) :
    CDerives Δ Γ e (.val (.box d (.thunk (.nu C)))) := .boxI h hΓ

/-- The same rule at data. -/
theorem d_box_data {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {d : Lifetime.Life} {A : VTy}
    (h : CDerives Δ Γ e (.val (.mu A))) (hΓ : CtxOutlives Δ Γ d) :
    CDerives Δ Γ e (.val (.box d (.mu A))) := .boxI h hΓ

end BoCa.Fig16.LogRel.Core.CoeffectsStrict

end
