import Outlives.Compat

/-!
# Outlives — `LDerives`: `CDerives` with the two relaxed premises, its FP and adequacy

`LDerives` is `CDerives` (`Core/Fundamental.lean`) rule for rule, with two premises relaxed:

* `boxI`: `CtxOutL Δ Γ a` (the box rule of `Δ ⊢ T ⊐ @a` non-strict) for `CtxOutlives Δ Γ a`;
* `withbor2`: `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b` (`VOutLe`, all three rules non-strict) for
  `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊐ @b`;

and one more rule, `core`, embedding every `CDerives` derivation. Every other rule is copied
with `CDerives` renamed, so the relaxed rules may sit under any former.

`fundamentalL` is `fundamentalC`'s induction with the two relaxed cases sent to
`boxIL_compatC` and `withbor2Le_compatX`, and `core` to `fundamentalC`. `adequacyL` is
`corollary33` at it. Neither touches the model, the typed world or `wpTS`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Outlives
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `CDerives` with `[]I`'s and `withbor` (2)'s outlives premises relaxed, and `core`. -/
inductive LDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop where
  /-- Every `CDerives` derivation. -/
  | core {Δ Γ e j} (h : CDerives Δ Γ e j) : LDerives Δ Γ e j
  | var {Δ Γ i A} (h : Ctx.SoloP Γ i A) : LDerives Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : Ctx.DeadP Γ) : LDerives Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (h₁ : LDerives Δ Γ₁ e₁ (.val A)) (h₂ : LDerives Δ Γ₂ e₂ (.val B)) :
      LDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B))
  | sumI₁ {Δ Γ e A B} (h : LDerives Δ Γ e (.val A)) :
      LDerives Δ Γ (.inj₁ e) (.val (.sum A B))
  | sumI₂ {Δ Γ e A B} (h : LDerives Δ Γ e (.val B)) :
      LDerives Δ Γ (.inj₂ e) (.val (.sum A B))
  /-- `thunk M : U (F A)`, `M` under a dead binder. -/
  | thunkF {Δ Γ M A} (h : LDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      LDerives Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
  /-- `thunk V : U C` for a λ-value `V : C`, `C` not an `F`. -/
  | thunkV {Δ Γ N C} (hC : C.isRet = false) (h : LDerives Δ Γ (.val (.lam N)) (.comp C)) :
      LDerives Δ Γ (.val (.lam N)) (.val (.thunk C))
  /-- `return V : F A`. -/
  | ret {Δ Γ V A} (h : LDerives Δ Γ V (.val A)) : LDerives Δ Γ V (.comp (.ret A))
  /-- `M to x. N`, written `(λx. N) M`. -/
  | bind {Δ Γ Γ₁ Γ₂ M N A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : LDerives Δ Γ₁ M (.comp (.ret A))) (hN : LDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      LDerives Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.SoloP Γ i (.thunk C)) :
      LDerives Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : LDerives Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      LDerives Δ Γ (.val (.lam M)) (.comp (.arr A C))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : LDerives Δ Γ₁ M (.comp (.arr A C))) (hx : Ctx.SoloP Γ₂ i A) :
      LDerives Δ Γ (.app M (.var i)) (.comp C)
  /-- `⟨M, N⟩ : C & D`, both components in the same context. -/
  | withI {Δ Γ M N C D} (hM : LDerives Δ (withCtx Γ) M (.comp C))
      (hN : LDerives Δ (withCtx Γ) N (.comp D)) :
      LDerives Δ Γ (withPair M N) (.comp (.amp C D))
  | proj₁ {Δ Γ M C D} (h : LDerives Δ Γ M (.comp (.amp C D))) :
      LDerives Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M C D} (h : LDerives Δ Γ M (.comp (.amp C D))) :
      LDerives Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)
  /-- `⟨⟩ : ⊤` at any context. -/
  | topI {Δ Γ} : LDerives Δ Γ (.val .unit) (.comp .top)
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hV : LDerives Δ Γ₁ V (.val .unit)) (hM : LDerives Δ Γ₂ M (.comp C)) :
      LDerives Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : LDerives Δ Γp V (.val (.tensor A B)))
      (hM : LDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
      LDerives Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : LDerives Δ Γs V (.val (.sum A B)))
      (h₁ : LDerives Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
      (h₂ : LDerives Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
      LDerives Δ Γ (.case V M₁ M₂) (.comp C)
  /-- `absurd V : C` for `V : 0`, at any rest of the context. -/
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : LDerives Δ Γ₁ V (.val .zero)) :
      LDerives Δ Γ (absurdE V) (.comp C)
  /-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`; the binder's slot is dead, at any type. -/
  | allI {Δ Γ x b M S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : LDerives (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
      LDerives Δ Γ (.val (.lam M)) (.comp (.all x b C))
  /-- `M [] : C[@a/'x]`. -/
  | allE {Δ Γ M x b a C} (h : LDerives Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
      LDerives Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))
  /-- Promotion of `thunk M : U (F A)` over `!Γ`. -/
  | bangThunkF {Δ Γ M A} (hp : Persistent Γ)
      (h : LDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      LDerives Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))
  /-- Promotion of a λ-value `V : C` over `!Γ`. -/
  | bangThunkV {Δ Γ N C} (hp : Persistent Γ) (hC : C.isRet = false)
      (h : LDerives Δ Γ (.val (.lam N)) (.comp C)) :
      LDerives Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))
  /-- Dereliction. -/
  | bangE {Δ Γ e A} (h : LDerives Δ Γ e (.val (.bang A))) : LDerives Δ Γ e (.val A)
  | copyBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  /-- `[]I`, at the box-relaxed context condition. -/
  | boxI {Δ Γ e a A} (h : LDerives Δ Γ e (.val A)) (hΓ : CtxOutL Δ Γ a) :
      LDerives Δ Γ e (.val (.box a A))
  | boxE {Δ Γ e a A} (h : LDerives Δ Γ e (.val (.box a A))) : LDerives Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : LDerives Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      LDerives Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : LDerives Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      LDerives Δ Γ e (.val (.mut a A))
  /-- The borrow axioms, at arbitrary value-type payloads. -/
  | alloc {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ forget (.val axForgetUnkTy)
  /-- An integer literal at its width.  `[spec §8]` -/
  | lit {Δ Γ} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width))
  /-- A host operation at `!(A ⊸ F B)`, its signature in `SPEC.md` §8.  `[spec §8]` -/
  | hostOp {Δ Γ} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op)))
  /-- `array_new : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)`, the step `tab`.  `[spec §9]` -/
  | arrNew {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .tab)) (.val (arrNewTy A))
  /-- `array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)`, the step `drop`.  `[spec §9]` -/
  | arrFree {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A))
  /-- `array_size : !(Array A ⇒ Array A ⊗ I32)`.  `[spec §9]` -/
  | arrSize {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) : LDerives Δ Γ (.val sizeV) (.val (arrSizeTy A))
  /-- `array_replace : !(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))`.  `[spec §9]` -/
  | arrReplace {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val replaceV) (.val (arrReplaceTy A))
  /-- `array_len : !(ArrayImm @a A ⇒ I32)`.  `[spec §9]` -/
  | arrLen {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val arrLenV) (.val (arrLenTy a A))
  /-- `array_get : !(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | arrGet {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A))
  /-- `array_copy : !(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)`.  `[spec §9]` -/
  | arrCopy {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val copyV) (.val (arrCopyTy a A))
  /-- `array_forget : !(ArrayImm @a A ⇒ 1)`.  `[spec §9]` -/
  | arrForget {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val forgetV) (.val (arrForgetTy a A))
  /-- `count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`, the step `count`: the counted
  loop, total at every host.  `[spec §16]` -/
  | countFold {Δ Γ} (S : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .count)) (.val (countFoldTy S))
  /-- `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`, the step `countTry`: the
  counted loop with an exit, total at every host.  `[spec §16]` -/
  | countTry {Δ Γ} (S E : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .countTry)) (.val (countTryTy S E))
  /-- `bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`, the step
  `boundedFix`: the fixed point with a budget of depth, total at every host and every
  computation type.  `[spec §20]` -/
  | boundedFix {Δ Γ} (A : VTy) (C : CTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C))
  /-- `slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `mut` leaves, with no cell.  `[spec §9]` -/
  | sliceBorrowM {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))
  /-- `slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `imm` leaves, with no cell.  `[spec §9]` -/
  | sliceBorrowI {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))
  /-- `slice_get_mut : !([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | sliceGetM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A))
  /-- `slice_len_mut : !([Mut @a A] ⇒ [Mut @a A] ⊗ I32)`.  `[spec §9]` -/
  | sliceLenM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val sizeV) (.val (sliceLenMTy a A))
  /-- `slice_split_imm : !([Imm @a A] ⊗ I32 ⇒ ([Imm @a A] ⊗ [Imm @a A]) ⊕ [Imm @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A))
  /-- `slice_split_mut : !([Mut @a A] ⊗ I32 ⇒ ([Mut @a A] ⊗ [Mut @a A]) ⊕ [Mut @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A))
  /-- `slice_empty_imm : [Imm @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val emptyFamV) (.val (.arrayImm a A))
  /-- `slice_empty_mut : [Mut @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val emptyFamV) (.val (.sliceMut a A))
  /-- `slice_replace_mut : !([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))`, `array_replace`'s
  term.  `[spec §9]` -/
  | sliceReplaceM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A))
  /-- `slice_swap_mut : !([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])`.  `[spec §9]` -/
  | sliceSwapM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val swapV) (.val (sliceSwapMTy a A))
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  /-- `withbor` (2), at the non-strict side condition. -/
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      LDerives Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ withswap (.val (axWithswapTy a A B))
  /-- The unwinding form of `withbor` (1): `Ref A` lent as `Imm 'x A` to a callback at a row of
  abortive operations; when it unwinds, the finaliser `d` runs on the source.  `[spec §19]` -/
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : LDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      LDerives Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (2): `Ref A` lent as `Mut 'x A`.  `[spec §19]` -/
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : LDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      LDerives Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (3): `Mut @a A` reborrowed as `Mut 'x A`.  `[spec §19]` -/
  | withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : LDerives Δ Γ d (.val (.lolli (.mut a A) .unit))) :
      LDerives Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `withload`: its own term, the source consumed by the load.
  `[spec §19]` -/
  | withloadU {Δ Γ a A B} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) :
      LDerives Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_mut`: an owned array lent as a family of `mut` leaves.
  `[spec §19]` -/
  | sliceBorrowMU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : LDerives Δ Γ d (.val (.lolli (.array A) .unit))) :
      LDerives Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_imm`: an owned array lent as a family of `imm` leaves.
  `[spec §19]` -/
  | sliceBorrowIU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : LDerives Δ Γ d (.val (.lolli (.array A) .unit))) :
      LDerives Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S))
  -- Call-by-value derived forms: BoLo's application and `∀E` on arbitrary subterms, and the
  -- reading of a computation of `F A` as a value-judged expression at `A`.
  /-- Call-by-value application `f a`, both arbitrary, at `VTy.lolli` (`lolliE_compatX`).  `[spec §3]` -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (ha : LDerives Δ Γ₁ a (.val A)) (hf : LDerives Δ Γ₂ f (.val (.lolli A B))) :
      LDerives Δ Γ (.app f a) (.val B)
  /-- Call-by-value `∀E`: `e []` for `e` at `VTy.all x b A` (`allE_compatX`).  `[spec §3]` -/
  | allEV {Δ Γ e x b a A} (h : LDerives Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      LDerives Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  /-- A computation of `F A` is a value-judged expression at `A`: `SemV` is `SemC` at `F A`.  `[spec §3]` -/
  | ofRet {Δ Γ e A} (h : LDerives Δ Γ e (.comp (.ret A))) : LDerives Δ Γ e (.val A)
  /-- `roll`: a value of `A[μX. A/X]` is a value of `μX. A`, at a closed `μ` whose variable is
  outside `A`'s `Mut` payloads (`docs/scope-recursion.md` §2.2).  `[spec §6]` -/
  | roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : LDerives Δ Γ e (.val (VTy.inst (.mu A) A))) : LDerives Δ Γ e (.val (.mu A))
  /-- `unroll`: a value of `μX. A` is a value of `A[μX. A/X]`.  `[spec §6]` -/
  | unroll {Δ Γ e A} (h : LDerives Δ Γ e (.val (.mu A))) :
      LDerives Δ Γ e (.val (VTy.inst (.mu A) A))
  /-- The borrowed fold, a constant:
  `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)`, for `T` built by
  `⊗`/`⊕` from closed leaves, `Ref X` and `X` (not `X` itself), `A_R = Imm̲ 'y T` with `R` at
  every recursive position, `R` outliving every lifetime, `'y` free in neither `μX. T` nor
  `R`.  `[spec §6]` -/
  | foldImm {Δ Γ} (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
      (hF : F.WF) (hG : F.Guarded) (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R)
      (hR : ∀ Δ' a, VOutlives Δ' a R) :
      LDerives Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))
  /-- The owned fold, a constant: `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`, for `T` of the
  same class, `A′_R = T` with `R` at every recursive position, any `R`.  `[spec §6]` -/
  | foldOwn {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      LDerives Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))
  /-- The owned fold with reuse, a constant: `foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`,
  for `T` of the same class, `A″_R = T` with `R` at a head `X` and `Ref 1 ⊗ R` at every `Ref X`
  (the emptied cell and the result on its content), any `R`.  `[spec §6]` -/
  | foldReuse {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      LDerives Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))
  /-- `νX. C` is its unrolling `C[U(νX. C)/X]` (`cC_nu_iff`), on the same term, at a positive
  `C`.  `[spec §7]` -/
  | nuIn {Δ Γ e C} (hC : C.NuOk) (h : LDerives Δ Γ e (.comp C.unroll)) :
      LDerives Δ Γ e (.comp (.nu C))
  | nuOut {Δ Γ e C} (hC : C.NuOk) (h : LDerives Δ Γ e (.comp (.nu C))) :
      LDerives Δ Γ e (.comp C.unroll)
  /-- Coiteration, a constant: `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` (`Nu.lean`), at a
  positive `C`.  `[spec §7]` -/
  | unfoldN {Δ Γ} (C : CTy) (S : VTy) (hC : C.NuOk) (hΓ : Ctx.DeadP Γ) :
      LDerives Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
  /-- `[sub]`: `F_Σ A ≤ F_Σ′ A` for `Σ ⊆ Σ′`; `F A = F_∅ A`.  `[spec §19]` -/
  | effSub {Δ Γ e} {S S' : Row} {A : VTy} (hle : RowLe S S')
      (h : LDerives Δ Γ e (.comp (CTy.effOf S A))) : LDerives Δ Γ e (.comp (CTy.effOf S' A))
  /-- `[perform]`: a non-abortive operation of the row.  `[spec §19]` -/
  | effPerform {Δ Γ V} {S : Row} {o : OpSig} (hf : Row.find S o.n o.i = some o)
      (hna : o.abort = false) (h : LDerives Δ Γ V (.val o.A)) :
      LDerives Δ Γ (BoCa.BoLo.performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B))
  /-- `[raise]`: an abortive operation of the row, at any answer, its argument dropping.
  `[spec §19]` -/
  | effRaise {Δ Γ V} {S : Row} {o : OpSig} {B : VTy} (hf : Row.find S o.n o.i = some o)
      (ha : o.abort = true) (hd : o.A.Drop) (h : LDerives Δ Γ V (.val o.A)) :
      LDerives Δ Γ (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B))
  /-- `[let]`: `M to x. N` at a row; `N`'s context drops at a row with weakening and is
  persistent at an unrestricted row.  `[spec §19]` -/
  | effLet {Δ Γ Γ₁ Γ₂ M N A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hM : LDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : LDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
      LDerives Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B))
  /-- `[then]`: `M then x. N unwind D`, the finaliser at the row's abortive operations.
  `[spec §19]` -/
  | effThen {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ)
      (hUq : S.Uniq) (hU : S.Unr → Persistent Γ₂)
      (hM : LDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : LDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
      (hD : LDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf S.abortOnly .unit))) :
      LDerives Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
  /-- `[handle]`: `handle_n e with (h_ret, hs)`, `n` not in `Σ`.  `[spec §19]` -/
  | effHandle {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32}
      {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
      (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (he : LDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
      LDerives Δ Γ (hndTerm n ir ic e) (.comp (CTy.effOf S R))

/-- **Fundamental Property** of `LDerives`. -/
theorem fundamentalL {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : LDerives Δ Γ e j) : SemJ Δ Γ e j := by
  induction h with
  | core h => exact fundamentalC h
  | var h => exact var_compatC h
  | unitI h => exact unitI_compatC h
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatC hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatC ih
  | sumI₂ _ ih => exact sumI₂_compatC ih
  | thunkF _ ih => exact thunkF_compatC ih
  | thunkV hC _ ih => exact thunkV_compatC hC ih
  | ret _ ih => exact ret_compatC ih
  | bind hs _ _ ihM ihN => exact bind_compatC hs ihM ihN
  | force h => exact force_compatC h
  | lam _ ih => exact lam_compatC ih
  | app hs _ hx ih => exact app_compatC hs ih hx
  | withI _ _ ihM ihN => exact withI_compatC ihM ihN
  | proj₁ _ ih => exact proj₁_compatC ih
  | proj₂ _ ih => exact proj₂_compatC ih
  | topI => exact topI_compatC
  | unitE hs _ _ ihV ihM => exact unitE_compatC hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatC hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatC hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatC hs ihV
  | allI hbx hΔx hΓx _ ih =>
      exact allI_compatC hbx hΔx hΓx ((semC_liveEq (.dead (LiveEq.refl _))).mp ih)
  | allE _ hlt ih => exact allE_compatC ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatC hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatC hp hC ih
  | bangE _ ih => exact bangE_compatC ih
  | copyBang hΓ => exact copyBang_compatC hΓ
  | forgetBang hΓ => exact forgetBang_compatC hΓ
  | boxI _ hΓ ih => exact boxIL_compatC ih hΓ
  | boxE _ ih => exact boxE_compatC ih
  | immSub _ hle ih => exact immSub_compatC ih hle
  | mutSub _ hle ih => exact mutSub_compatC ih hle
  | alloc hΓ => exact alloc_compatX hΓ
  | free hΓ => exact free_compatX hΓ
  | swap hΓ => exact swap_compatX hΓ
  | copy hΓ => exact copy_compatX hΓ
  | forgetImm hΓ => exact forgetImm_compatX hΓ
  | forgetMut hΓ => exact forgetMut_compatX hΓ
  | forgetUnk hΓ => exact forgetUnk_compatX hΓ
  | lit c hΓ => exact lit_compatX c hΓ
  | hostOp op hΓ => exact hostOp_compatX op hΓ
  | arrNew _ hΓ => exact arrNew_compatX hΓ
  | arrFree _ hΓ => exact arrFree_compatX hΓ
  | arrSize _ hΓ => exact arrSize_compatX hΓ
  | arrReplace _ hΓ => exact arrReplace_compatX hΓ
  | arrLen _ _ hΓ => exact arrLen_compatX hΓ
  | arrGet _ _ hΓ => exact arrGet_compatX hΓ
  | arrCopy _ _ hΓ => exact arrCopy_compatX hΓ
  | arrForget _ _ hΓ => exact arrForget_compatX hΓ
  | countFold _ hΓ => exact countFold_compatX hΓ
  | countTry _ _ hΓ => exact countTry_compatX hΓ
  | boundedFix _ _ hΓ => exact boundedFix_compatX hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact sliceBorrowM_compatX x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact sliceBorrowI_compatX x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM _ _ hΓ => exact sliceGetM_compatX hΓ
  | sliceLenM _ _ hΓ => exact sliceLenM_compatX hΓ
  | sliceSplitI _ _ hΓ => exact sliceSplitI_compatX hΓ
  | sliceSplitM _ _ hΓ => exact sliceSplitM_compatX hΓ
  | sliceEmptyI _ _ hΓ => exact sliceEmptyI_compatX hΓ
  | sliceEmptyM _ _ hΓ => exact sliceEmptyM_compatX hΓ
  | sliceReplaceM _ _ hΓ => exact sliceReplaceM_compatX hΓ
  | sliceSwapM _ _ hΓ => exact sliceSwapM_compatX hΓ
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact withbor1_compatX x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2Le_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatX hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS hdc _ ihd => exact withbor1U_compatX x hΓ hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS hdc _ ihd =>
      exact withbor2U_compatX x hΓ hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ _ hf₁ hf₂ hS hdc _ ihd => exact withbor3U_compatX x hΓ hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ _ hf₁ hf₂ hS => exact withloadU_compatX x hΓ hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowMU_compatX x hΓ hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowIU_compatX x hΓ hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih
  | roll hA hc _ ih => exact roll_compatX hA hc ih
  | unroll _ ih => exact unroll_compatX ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact foldImm_compatX F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R hΓ hF hG => exact foldOwn_compatX F hF hG R hΓ
  | foldReuse F R hΓ hF hG => exact foldReuse_compatX F hF hG R hΓ
  | nuIn hC _ ih => exact nuIn_compatX hC ih
  | nuOut hC _ ih => exact nuOut_compatX hC ih
  | unfoldN C S hC hΓ => exact unfold_compatX hC S hΓ
  | effSub hle _ ih => exact sub_compatC hle ih
  | effPerform hf hna _ ih => exact perform_compatC hf hna ih
  | effRaise hf ha hd _ ih => exact raise_compatC hf ha (fun _ _ _ _ h => vC_noOwn_of_drop hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatC hs hW hU ihM ihN
  | effThen hs hNZ hUq hU _ _ _ ihM ihN ihD => exact then_compatC hs hNZ hUq hU ihM ihN ihD
  | effHandle hs hs₁ hr hc hn0 hnS hlen _ ih => exact handle_compatC hs hs₁ hr hc hn0 hnS hlen ih


/-- **Adequacy** of `LDerives`: a closed computation of `F 1` runs to `()` from the empty memory
and leaves the empty memory, by `corollary33` at `fundamentalL`. -/
theorem adequacyL {e : Expr} (h : LDerives LifeCtx.empty [] e (.comp (.ret .unit))) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamentalL h)

/-- A closed `LDerives` derivation at `F I32` runs to a literal and leaves the empty memory. -/
theorem runs_i32L {e : Expr} (h : LDerives LifeCtx.empty [] e (.comp (.ret .i32))) :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp₀ : wpTS [] e (fun ls v => vP .i32 ls LSub.empty v) (PMap.empty : WRes) := by
    have hwp := fundamentalL h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
    rwa [show substAll [] e = e from Adequacy.psub_nil 0 e] at hwp
  have hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (∃ n, v = Val.i32 n)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty hwp₀
    obtain ⟨rfl, n, rfl⟩ := hv
    exact ⟨rfl, n, rfl⟩
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32 e (fun v => ∃ n, v = Val.i32 n) hwp
  exact ⟨n, hsteps⟩

end BoCa.Fig16.LogRel.Core.Outlives

end
