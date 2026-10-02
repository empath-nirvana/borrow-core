import FnMut.Core.Records
import FnMut.Core.Folds

/-!
# Core — destructors  `[spec §12]`

`dtorE T : T ⊸ F 1` is a closed term for every type `T` with `HasDtor T`, and `dtor_wf` types it
in `CDerives` at every lifetime context and every dead context: it is an ordinary linear program
built from existing rules. The checker inserts `dropE T i e = (dtorE T xᵢ; e)` where an owned
value goes unused (`drop_derives`), so the elaborated term uses the value exactly once.

| type | destructor |
|---|---|
| `1`, `0`, `I32`, `I64`, `Unk`, `!A` | `forget` (the slot is persistent) |
| `Imm @a A`, `Mut @a A` | `forget` (the borrow axiom constant: ends the loan, frees nothing) |
| `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise |
| `Ref A` | `free`, then the destructor of `A` |
| `μX. T`, `T` in `FShape` | `foldOwn` whose algebra is the destructor of `T[1/X]` |
| `U(C & F 1)` | `close`: force, then the second projection |
| `U(νX. C & F R)`, `R` closed | `close`, then the destructor of the residual `R` |
| `Array A` | `array_free` with the destructor of `A` as the consumer |
| `ArrayImm @a A` | `array_forget` |

The first two rows are the forgettable types, whose destructor does nothing; every type of
`Affine` (`Core/Records.lean`) is one (`hasDtor_of_affine`). The other rows deallocate or run
`close` code. `U C` in general has no destructor: a thunk of `F A` or of `A ⊸ C` can only be
disposed of by running it. Nor does `μ` outside `FShape` (for example `X` under `U`).

The `μ` case recovers the fold's shape from the body (`toFShape`, with `(toFShape A).ty = A`) and
names the algebra by the same recursion in its `alg` mode (`algE = dtorAt true`), so both are one
structural recursion on `VTy`; `algE_eq` identifies the algebra with the destructor of `T[1/X]`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

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
  | .ref (.opq _) => rfl
  | .ref (.fam _) => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ _ => rfl
  | .bang _ => rfl
  | .unk => rfl
  | .mu _ => rfl
  | .int _ => rfl
  | .opq _ => rfl
  | .fam _ => rfl

/-! ### The destructors -/

/-- `X`, the `μ`'s own variable. -/
def isX0 : VTy → Bool
  | .tvar 0 => true
  | _ => false

/-- The destructor of `T` (`alg = false`), or of `T[1/X]` for a `μ` body `T` (`alg = true`: `forget`
at `Ref X` and at `X`). -/
def dtorAt : Bool → VTy → Expr
  | alg, .tensor A B => .val (.lam (.letpair (.var 0)
      (.seq (.app (dtorAt alg A) (.var 1)) (.app (dtorAt alg B) (.var 0)))))
  | alg, .sum A B => .val (.lam (.case (.var 0) (.app (dtorAt alg A) (.var 0)) (.app (dtorAt alg B) (.var 0))))
  | alg, .ref A => if alg && isX0 A then forget else
      .val (.lam (bindE (.app (.val (.prim .free)) (.var 0)) (.app (dtorAt false A) (.var 0))))
  | _, .box _ A => .val (.lam (.app (dtorAt false A) (.var 0)))
  | _, .mu A => .val (.lam (.app (.app (.val (foldOwnV (toFShape A)))
      (.val (.lam (.app (dtorAt true A) (.var 0))))) (.var 0)))
  | _, .thunk (.nu (.amp _ (.ret R))) => .val (.lam
      (bindE (.app (.var 0) (.val (.inj₂ .unit))) (.app (dtorAt false R) (.var 0))))
  | _, .thunk _ => .val (.lam (.app (.var 0) (.val (.inj₂ .unit))))
  | _, .fam (.ref A) => .val (.lam (.app (.val (.prim .drop))
      (.pair (.val (.lam (.app (dtorAt false A) (.var 0)))) (.var 0))))
  | _, .fam (.mut _ _) => .val (.lam (elet
      (.app (.val (.prim .idx)) (.pair (.var 0) (.val (Val.i32 0xFFFFFFFF))))
      (.case (.var 0) (.app forget (.var 0)) (.var 0))))
  | _, _ => forget

/-- At a thunk the destructor does not depend on the mode. -/
theorem dtorAt_thunk : ∀ (b : Bool) (C : CTy), dtorAt b (.thunk C) = dtorAt false (.thunk C)
  | _, .nu (.amp _ (.ret _)) | _, .nu (.amp _ (.arr _ _)) | _, .nu (.amp _ (.amp _ _))
  | _, .nu (.amp _ .top) | _, .nu (.amp _ (.all _ _ _)) | _, .nu (.amp _ (.nu _))
  | _, .nu (.amp _ (.eff _ _ _ _ _ _)) | _, .nu (.eff _ _ _ _ _ _) | _, .eff _ _ _ _ _ _
  | _, .nu (.ret _) | _, .nu (.arr _ _) | _, .nu .top | _, .nu (.all _ _ _) | _, .nu (.nu _)
  | _, .ret _ | _, .arr _ _ | _, .amp _ _ | _, .top | _, .all _ _ _ => rfl

/-- The destructor of `T`, a closed `λ`.  `[spec §12]` -/
abbrev dtorE : VTy → Expr := dtorAt false

/-- The `foldOwn` algebra of a `μ` body `T`: the destructor of `T[1/X]`. -/
abbrev algE : VTy → Expr := dtorAt true

/-- The algebra is the destructor of `T[1/X]`. -/
theorem algE_eq : ∀ A : VTy, algE A = dtorE ((toFShape A).resO .unit)
  | .tensor A B => by simp [dtorAt, toFShape, FShape.resO, algE_eq A, algE_eq B]
  | .sum A B => by simp [dtorAt, toFShape, FShape.resO, algE_eq A, algE_eq B]
  | .ref (.tvar 0) => rfl
  | .ref (.tvar (_ + 1)) => rfl
  | .tvar 0 => rfl
  | .tvar (_ + 1) => rfl
  | .unit => rfl
  | .zero => rfl
  | .thunk C => dtorAt_thunk true C
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
  | .ref (.opq _) => rfl
  | .ref (.fam _) => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ _ => rfl
  | .bang _ => rfl
  | .unk => rfl
  | .mu _ => rfl
  | .int _ => rfl
  | .opq _ => rfl
  | .fam L => by cases L <;> rfl

/-! ### Which types have one -/

/-- `T` has a destructor: `dtorE T` consumes a value of `T`.  `[spec §12]` -/
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
  /-- Codata `νX. C & F R` whose `close` returns a closed residual `R` with a destructor:
  `close`, then the destructor of `R`.  `[spec §7, §12]` -/
  | nu {C R} (hC : (CTy.amp C (.ret R)).NuOk) (hRc : R.Cl 0) (h : HasDtor R) :
      HasDtor (.thunk (.nu (.amp C (.ret R))))
  /-- An array: each element to the destructor of `A`, then the cells freed (`array_free`).
  `[spec §9, §12]` -/
  | array {A} (h : HasDtor A) : HasDtor (.fam (.ref A))
  /-- A family of leaf views, forgotten (`array_forget`).  `[spec §9, §12]` -/
  | arrayImm {a A} : HasDtor (.fam (.imm a A))
  /-- A family of `mut` leaves, forgotten: `slice_get_mut` at an index past every family's
  length (`2³² − 1`) consumes it, and `forget` ends the leaf it would hand out.  `[spec §9, §12]` -/
  | arrayMut {a A} : HasDtor (.fam (.mut a A))

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

/-- **Every destructor is a closed `CDerives` derivation**, at every lifetime context and every
dead context.  `[spec §12]` -/
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
  | @nu C R hC hRc _ ih =>
      intro Γ hΓ
      have hM := CDerives.proj₂ (Δ := Δ)
        (.nuOut hC (.force (C := .nu (.amp C (.ret R))) (.here hΓ.toP)))
      simp only [CTy.instT, VTy.inst, VTy.subst_closed0 hRc] at hM
      exact .thunkV rfl (.lam (.bind (.left (deadSplit hΓ)) hM
        (.ret (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (ih (.cons (.cons hΓ)))))))
  | array _ ih =>
      intro Γ hΓ
      exact .lamV (.lolliE (.left (deadSplit hΓ))
        (.tensorI (.right (deadSplit hΓ))
          (.bangThunkV (dead_noLive (Ctx.Dead.cons hΓ)) rfl
            (.lam (.ret (.lolliE (.left (.dead (deadSplit hΓ)))
              (.var (.here (Ctx.Dead.cons hΓ).toP)) (ih (.cons (.cons hΓ)))))))
          (.var (.here hΓ.toP)))
        (.bangE (.arrFree _ (Ctx.Dead.cons hΓ).toP)))
  | arrayImm => intro Γ hΓ; exact .bangE (.arrForget _ _ hΓ.toP)
  | arrayMut =>
      intro Γ hΓ
      exact .lamV (.eletV (.left (deadSplit hΓ))
        (.lolliE (.left (deadSplit hΓ))
          (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
            (.lit (.i32 0xFFFFFFFF) (Ctx.Dead.cons hΓ).toP))
          (.bangE (.sliceGetM _ _ (Ctx.Dead.cons hΓ).toP)))
        (.caseV (.left (deadSplit (Ctx.Dead.cons hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (.lolliE (.left (.dead (deadSplit (Ctx.Dead.cons hΓ))))
            (.var (.here (Ctx.Dead.cons (Ctx.Dead.cons hΓ)).toP))
            (.forgetMut (Ctx.Dead.cons (Ctx.Dead.cons (Ctx.Dead.cons hΓ))).toP))
          (.var (.here (Ctx.Dead.cons (Ctx.Dead.cons hΓ)).toP))))

/-! ### A borrow's destructor frees nothing -/

/-- At `Imm @a A` and `Mut @a A` the destructor is `forget = λx. ()`: dropping a borrow ends the
loan and deallocates nothing. -/
theorem dtorE_imm (a : Lifetime.Life) (A : VTy) : dtorE (.imm a A) = forget := rfl

theorem dtorE_mut (a : Lifetime.Life) (A : VTy) : dtorE (.mut a A) = forget := rfl

/-! ### Dropping a slot -/

/-- `dtorE T xᵢ; e`: the destructor of the variable `i` at `T`, before `e`. -/
def dropE (T : VTy) (i : Nat) (e : Expr) : Expr := .seq (.app (dtorE T) (.var i)) e

/-- **A drop is a `CDerives` derivation**: `unitE` over the destructor applied to the slot.
`[spec §12]` -/
theorem drop_derives {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {T : VTy} {e : Expr} {C : CTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (h : CDerives Δ Γ₂ e (.comp C)) : CDerives Δ Γ (dropE T i e) (.comp C) :=
  .unitE hs (.lolliE (split_kill' Γ₁).toP (.var hx) (dtor_wf hT (kill_dead Γ₁))) h

end BoCa.Fig16.LogRel.Core

end
