import Core

/-!
# Affine — destructors as derived terms

`dtorE T` is a closed term `T ⊸ F 1` for every type `T` with `HasDtor T`, and `dtor_wf` types it
in `CDerives` at every dead context: it is an ordinary linear program built from existing rules.

| type | destructor |
|---|---|
| `1`, `0`, `I32`, `I64`, `Unk`, `!A` | `forget` (the slot is persistent) |
| `Imm @a A`, `Mut @a A` | `forget` (the borrow axiom constant: ends the loan, frees nothing) |
| `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise |
| `Ref A` | `free`, then the destructor of `A` |
| `μX. T`, `T` in `FShape` | `foldOwn` whose algebra is the destructor of `T[1/X]` |
| `U(C & F 1)`, `U(D A)`, `U(Stream A)` | `close`: force, then the second projection |

`U C` in general has none: a thunk of `F A` or of `A ⊸ C` can only be disposed of by running it.
`μ` outside `FShape` (for example `X` under `U`) has none. A type is **droppable** when it has a
destructor (`HasDtor`); every forgettable type of `Core/Records.lean` (`Affine`) is droppable
(`hasDtor_of_affine`).

The `μ` case recovers the fold's shape from the body (`toFShape`, with `(toFShape A).ty = A`) and
names the algebra by the same recursion in its `alg` mode (`algE = dt true`), so both are one
structural recursion on `VTy`; `algE_eq` identifies the algebra with the destructor of `T[1/X]`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Affine
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The shape of a `μ` body -/

/-- The `FShape` reading of a `μ` body: `Ref X` and `X` at variable `0`, `⊗` and `⊕` through,
every other type a leaf. -/
def toFShape : VTy → FShape
  | .tensor A B => .tensor (toFShape A) (toFShape B)
  | .sum A B => .sum (toFShape A) (toFShape B)
  | .ref (.tvar 0) => .refX
  | .tvar 0 => .varX
  | A => .leaf A

theorem toFShape_ty : ∀ A : VTy, (toFShape A).ty = A
  | .tensor A B => by simp [toFShape, FShape.ty, toFShape_ty A, toFShape_ty B]
  | .sum A B => by simp [toFShape, FShape.ty, toFShape_ty A, toFShape_ty B]
  | .ref (.tvar 0) => rfl
  | .ref (.tvar (_ + 1)) => rfl
  | .tvar 0 => rfl
  | .tvar (_ + 1) => rfl
  | .unit => rfl
  | .zero => rfl
  | .thunk _ => rfl
  | .ref .unit => rfl
  | .ref (.tensor _ _) => rfl
  | .ref .zero => rfl
  | .ref (.sum _ _) => rfl
  | .ref (.thunk _) => rfl
  | .ref (.ref _) => rfl
  | .ref (.imm _ _) => rfl
  | .ref (.mut _ _) => rfl
  | .ref (.box _ _) => rfl
  | .ref (.bang _) => rfl
  | .ref .unk => rfl
  | .ref (.mu _) => rfl
  | .ref (.int _) => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ _ => rfl
  | .bang _ => rfl
  | .unk => rfl
  | .mu _ => rfl
  | .int _ => rfl

/-! ### The destructors -/

/-- `X`, the `μ`'s own variable. -/
def isX0 : VTy → Bool
  | .tvar 0 => true
  | _ => false

/-- The destructor of `T` (`alg = false`), or of `T[1/X]` for a `μ` body `T` (`alg = true`: `forget`
at `Ref X` and at `X`). -/
def dt : Bool → VTy → Expr
  | alg, .tensor A B => .val (.lam (.letpair (.var 0)
      (.seq (.app (dt alg A) (.var 1)) (.app (dt alg B) (.var 0)))))
  | alg, .sum A B => .val (.lam (.case (.var 0) (.app (dt alg A) (.var 0)) (.app (dt alg B) (.var 0))))
  | alg, .ref A => if alg && isX0 A then forget else
      .val (.lam (bindE (.app (.val (.prim .free)) (.var 0)) (.app (dt false A) (.var 0))))
  | _, .box _ A => .val (.lam (.app (dt false A) (.var 0)))
  | _, .mu A => .val (.lam (.app (.app (.val (foldOwnV (toFShape A)))
      (.val (.lam (.app (dt true A) (.var 0))))) (.var 0)))
  | _, .thunk _ => .val (.lam (.app (.var 0) (.val (.inj₂ .unit))))
  | _, _ => forget

/-- The destructor of `T`, a closed `λ`. -/
abbrev dtorE : VTy → Expr := dt false

/-- The `foldOwn` algebra of a `μ` body `T`: the destructor of `T[1/X]`. -/
abbrev algE : VTy → Expr := dt true

/-- The algebra is the destructor of `T[1/X]`. -/
theorem algE_eq : ∀ A : VTy, algE A = dtorE ((toFShape A).resO .unit)
  | .tensor A B => by simp [dt, toFShape, FShape.resO, algE_eq A, algE_eq B]
  | .sum A B => by simp [dt, toFShape, FShape.resO, algE_eq A, algE_eq B]
  | .ref (.tvar 0) => rfl
  | .ref (.tvar (_ + 1)) => rfl
  | .tvar 0 => rfl
  | .tvar (_ + 1) => rfl
  | .unit => rfl
  | .zero => rfl
  | .thunk _ => rfl
  | .ref .unit => rfl
  | .ref (.tensor _ _) => rfl
  | .ref .zero => rfl
  | .ref (.sum _ _) => rfl
  | .ref (.thunk _) => rfl
  | .ref (.ref _) => rfl
  | .ref (.imm _ _) => rfl
  | .ref (.mut _ _) => rfl
  | .ref (.box _ _) => rfl
  | .ref (.bang _) => rfl
  | .ref .unk => rfl
  | .ref (.mu _) => rfl
  | .ref (.int _) => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ _ => rfl
  | .bang _ => rfl
  | .unk => rfl
  | .mu _ => rfl
  | .int _ => rfl

/-! ### Which types have one -/

/-- `T` is droppable: `dtorE T` is a destructor for it. -/
inductive HasDtor : VTy → Prop where
  | unit : HasDtor .unit
  | zero : HasDtor .zero
  | int {w} : HasDtor (.int w)
  | unk : HasDtor .unk
  | bang {A} : HasDtor (.bang A)
  | imm {a A} : HasDtor (.imm a A)
  | «mut» {a A} : HasDtor (.mut a A)
  | tensor {A B} : HasDtor A → HasDtor B → HasDtor (.tensor A B)
  | sum {A B} : HasDtor A → HasDtor B → HasDtor (.sum A B)
  | box {a A} : HasDtor A → HasDtor (.box a A)
  /-- An owned cell: freed, then its content dropped. -/
  | ref {A} : HasDtor A → HasDtor (.ref A)
  /-- An inductive type in the fold class: `foldOwn` with the destructor of `T[1/X]`. -/
  | mu {A} (hF : (toFShape A).WF) (hG : (toFShape A).Guarded)
      (h : HasDtor ((toFShape A).resO .unit)) : HasDtor (.mu A)
  /-- A computation with a `close` component. -/
  | close {C} : HasDtor (.thunk (.amp C (.ret .unit)))
  | delay {A} : HasDtor (.thunk (.delay A))
  | stream {A} : HasDtor (.thunk (.stream A))

theorem hasDtor_of_affine {A : VTy} (h : Affine A) : HasDtor A := by
  induction h with
  | unit => exact .unit
  | zero => exact .zero
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | imm => exact .imm
  | «mut» => exact .mut
  | unk => exact .unk
  | bang => exact .bang
  | int => exact .int

/-! ### The destructors are `CDerives` derivations -/

/-- `forget : T ⊸ 1` at a persistent `T`, from `λ` and `Ctx.DeadP.drop`. -/
theorem forget_persistent {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hT : T.Persistent)
    (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val (.lolli T .unit)) :=
  .thunkV rfl (.lam (.ret (.unitI (.drop hT hΓ.toP))))

/-- `λx. close x : U(C & F 1) ⊸ F 1` body, from `force`/`proj₂`. -/
theorem close_body {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.thunk (.amp C (.ret .unit)), true⟩ :: Γ) (.app (.var 0) (.val (.inj₂ .unit)))
      (.comp (.ret .unit)) :=
  .proj₂ (C := C) (.force (C := .amp C (.ret .unit)) (.here hΓ.toP))

/-- **Every droppable type's destructor is a closed `CDerives` derivation**, at every lifetime
context and every dead context. -/
theorem dtor_wf {Δ : LifeCtx} {T : VTy} (hT : HasDtor T) :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE T) (.val (.lolli T .unit)) := by
  induction hT generalizing Δ with
  | unit => intro Γ hΓ; exact forget_persistent rfl hΓ
  | zero => intro Γ hΓ; exact forget_persistent rfl hΓ
  | int => intro Γ hΓ; exact forget_persistent rfl hΓ
  | unk => intro Γ hΓ; exact forget_persistent rfl hΓ
  | bang => intro Γ hΓ; exact forget_persistent rfl hΓ
  | imm => intro Γ hΓ; exact .forgetImm hΓ.toP
  | «mut» => intro Γ hΓ; exact .forgetMut hΓ.toP
  | tensor _ _ ih₁ ih₂ =>
      intro Γ hΓ
      exact .lamV (.letpairV (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
        (.seqV (.right (.left (.dead (deadSplit hΓ))))
          (.lolliE (.dead (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ.toP))))
            (ih₁ (.cons (.cons (.cons hΓ)))))
          (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP))))
            (ih₂ (.cons (.cons (.cons hΓ)))))))
  | sum _ _ ih₁ ih₂ =>
      intro Γ hΓ
      exact .lamV (.caseV (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
          (ih₁ (.cons (.cons hΓ))))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
          (ih₂ (.cons (.cons hΓ)))))
  | box _ ih =>
      intro Γ hΓ
      exact .lamV (.lolliE (.left (deadSplit hΓ)) (.boxE (.var (.here hΓ.toP)))
        (ih (.cons hΓ)))
  | ref _ ih =>
      intro Γ hΓ
      exact .lamV (.eletV (.left (deadSplit hΓ))
        (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (.free (Ctx.Dead.cons hΓ).toP))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (ih (.cons (.cons hΓ)))))
  | @mu A hF hG _ ih =>
      intro Γ hΓ
      have halg : CDerives Δ (⟨.mu A, false⟩ :: Γ) (.val (.lam (.app (algE A) (.var 0))))
          (.val (algOTy (toFShape A) .unit)) := by
        rw [algE_eq]
        exact d_algO (.cons hΓ) (.ret (.lolliE (.left (.dead (deadSplit hΓ)))
          (.var (.here (Ctx.Dead.cons hΓ).toP)) (ih (.cons (.cons hΓ)))))
      have hfold : CDerives Δ (⟨.mu A, false⟩ :: Γ)
          (.app (.val (foldOwnV (toFShape A))) (.val (.lam (.app (algE A) (.var 0)))))
          (.val (.lolli (.mu A) .unit)) := by
        have h := CDerives.bangE (CDerives.lolliE (deadSplit (.cons hΓ)) halg
          (.foldOwn (toFShape A) .unit (Ctx.Dead.cons hΓ).toP hF hG))
        rwa [toFShape_ty] at h
      exact .lamV (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) hfold)
  | close => intro Γ hΓ; exact .thunkV rfl (.lam (close_body hΓ))
  | @delay A =>
      intro Γ hΓ
      exact .thunkV rfl (.lam (.proj₂ (C := .ret (.sum A (.thunk (.delay A))))
        (.delayOut (.force (C := .delay A) (.here hΓ.toP)))))
  | @stream A =>
      intro Γ hΓ
      exact .thunkV rfl (.lam (.proj₂ (C := .ret (.tensor A (.thunk (.stream A))))
        (.streamOut (.force (C := .stream A) (.here hΓ.toP)))))

/-! ### A borrow's destructor frees nothing -/

/-- At `Imm @a A` and `Mut @a A` the destructor is `forget = λx. ()`: dropping a borrow ends the
loan and deallocates nothing. -/
theorem dtorE_imm (a : Lifetime.Life) (A : VTy) : dtorE (.imm a A) = forget := rfl

theorem dtorE_mut (a : Lifetime.Life) (A : VTy) : dtorE (.mut a A) = forget := rfl

end BoCa.Fig16.LogRel.Core.Affine

end
