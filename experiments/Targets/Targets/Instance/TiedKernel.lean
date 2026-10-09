import Core.Weaken
import Targets.Instance.J1Checks

/-!
# The Instance — Core's kernel with its inner rows tied to the effect context (decision R)

Decision D1 ties a program's row to the effect context `Ξ` (`RowAt`, `OCTy.TiedAt`): every
operation the row finds is a label's, at the signature `Ξ` declares.  Decision R ties the rows
inside a derivation the same way: **`CDerivesAt Ξ`** is Core's `CDerives` (SPEC §19, §24, §25)
with the premise `RowAt Ξ` at the three rules that read an operation's signature off a row —
`[perform]` and `[raise]` (the row the operation is found in) and `[handle]` (the handled row
`(n)↑E ⊙ Σ`, whose signature `E` is the handler's, and whose qualifiers are the handler value's
tags, SPEC §25).  Every other rule is Core's, verbatim.

* `CDerivesAt.toCDerives`: a tied derivation is one of Core's, so `fundamentalC` holds of it.
* `CDerivesAt.effHandle`: `[handle]` at two clause variables, as Core's `CDerives.effHandle`.
* `CDerivesAt.append_dead`: weakening by consumed slots at the end, as Core's
  `CDerives.append_dead`.

At a handler, the tie makes `E` a prefix of `Ξ n`, so the handler's tags are a prefix of `Ξ`'s
qualifiers of `n` (`hndTags_of_rowAt`).

**Inversions** (each one induction on the derivation; a rule whose premise has the conclusion's term
carries the claim through, every other rule is told apart by its conclusion's term, `cdat_terms`):
`[handle]` is the only rule whose conclusion is a handler term, so a tied derivation of
`hnd (n, (qs, H)) M` has `qs` a prefix of `Ξ`'s qualifiers of `n` and types `M` (`derAt_hnd`); a
`let` `(λx. N) M` types `N`, or `N` with the λ-value `M` in place, or the λ-value `λx. N`
(`derAt_let`); a λ-value whose body is an application types the body (`derAt_lam`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Core's kernel, its handlers' and operations' rows tied to `Ξ`** (decision R): `CDerives`'s
constructors (`Core/Fundamental.lean`) verbatim, with `RowAt Ξ` at `effPerform` and `effRaise` (on
the row `S`) and at `effHandleV` (on the handled row `Row.ofEff n E 0 ++ S`). -/
inductive CDerivesAt (Ξ : EffCtx) : LifeCtx → Ctx VTy → Expr → Jdg → Prop where
  | var {Δ Γ i A} (h : Ctx.SoloP Γ i A) : CDerivesAt Ξ Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (h₁ : CDerivesAt Ξ Δ Γ₁ e₁ (.val A)) (h₂ : CDerivesAt Ξ Δ Γ₂ e₂ (.val B)) :
      CDerivesAt Ξ Δ Γ (.pair e₁ e₂) (.val (.tensor A B))
  | sumI₁ {Δ Γ e A B} (h : CDerivesAt Ξ Δ Γ e (.val A)) :
      CDerivesAt Ξ Δ Γ (.inj₁ e) (.val (.sum A B))
  | sumI₂ {Δ Γ e A B} (h : CDerivesAt Ξ Δ Γ e (.val B)) :
      CDerivesAt Ξ Δ Γ (.inj₂ e) (.val (.sum A B))
  /-- `thunk M : U (F A)`, `M` under a dead binder. -/
  | thunkF {Δ Γ M A} (h : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
  /-- `thunk V : U C` for a λ-value `V : C`, `C` not an `F`. -/
  | thunkV {Δ Γ N C} (hC : C.isRet = false) (h : CDerivesAt Ξ Δ Γ (.val (.lam N)) (.comp C)) :
      CDerivesAt Ξ Δ Γ (.val (.lam N)) (.val (.thunk C))
  /-- `return V : F A`. -/
  | ret {Δ Γ V A} (h : CDerivesAt Ξ Δ Γ V (.val A)) : CDerivesAt Ξ Δ Γ V (.comp (.ret A))
  /-- `M to x. N`, written `(λx. N) M`. -/
  | bind {Δ Γ Γ₁ Γ₂ M N A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (.ret A))) (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.SoloP Γ i (.thunk C)) :
      CDerivesAt Ξ Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.comp (.arr A C))
  /-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B` with `x`'s slot dead.  `[spec §26]` -/
  | lamDead {Δ Γ M} {S : Row} {B : VTy}
      (h : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ) M (.comp (CTy.effOf S B))) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.comp (.arr .unit (CTy.effOf S B)))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (.arr A C))) (hx : Ctx.SoloP Γ₂ i A) :
      CDerivesAt Ξ Δ Γ (.app M (.var i)) (.comp C)
  /-- `⟨M, N⟩ : C & D`, both components in the same context. -/
  | withI {Δ Γ M N C D} (hM : CDerivesAt Ξ Δ (withCtx Γ) M (.comp C))
      (hN : CDerivesAt Ξ Δ (withCtx Γ) N (.comp D)) :
      CDerivesAt Ξ Δ Γ (withPair M N) (.comp (.amp C D))
  | proj₁ {Δ Γ M C D} (h : CDerivesAt Ξ Δ Γ M (.comp (.amp C D))) :
      CDerivesAt Ξ Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M C D} (h : CDerivesAt Ξ Δ Γ M (.comp (.amp C D))) :
      CDerivesAt Ξ Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)
  /-- `⟨⟩ : ⊤` at any context. -/
  | topI {Δ Γ} : CDerivesAt Ξ Δ Γ (.val .unit) (.comp .top)
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hV : CDerivesAt Ξ Δ Γ₁ V (.val .unit)) (hM : CDerivesAt Ξ Δ Γ₂ M (.comp C)) :
      CDerivesAt Ξ Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : CDerivesAt Ξ Δ Γp V (.val (.tensor A B)))
      (hM : CDerivesAt Ξ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
      CDerivesAt Ξ Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : CDerivesAt Ξ Δ Γs V (.val (.sum A B)))
      (h₁ : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
      (h₂ : CDerivesAt Ξ Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
      CDerivesAt Ξ Δ Γ (.case V M₁ M₂) (.comp C)
  /-- `absurd V : C` for `V : 0`, at any rest of the context. -/
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : CDerivesAt Ξ Δ Γ₁ V (.val .zero)) :
      CDerivesAt Ξ Δ Γ (absurdE V) (.comp C)
  /-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`; the binder's slot is dead, at any type. -/
  | allI {Δ Γ x b M S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : CDerivesAt Ξ (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.comp (.all x b C))
  /-- `M [] : C[@a/'x]`. -/
  | allE {Δ Γ M x b a C} (h : CDerivesAt Ξ Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
      CDerivesAt Ξ Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))
  /-- Promotion of `thunk M : U (F A)` over `!Γ`. -/
  | bangThunkF {Δ Γ M A} (hp : Persistent Γ)
      (h : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))
  /-- Promotion of a λ-value `V : C` over `!Γ`. -/
  | bangThunkV {Δ Γ N C} (hp : Persistent Γ) (hC : C.isRet = false)
      (h : CDerivesAt Ξ Δ Γ (.val (.lam N)) (.comp C)) :
      CDerivesAt Ξ Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))
  /-- Dereliction. -/
  | bangE {Δ Γ e A} (h : CDerivesAt Ξ Δ Γ e (.val (.bang A))) : CDerivesAt Ξ Δ Γ e (.val A)
  | copyBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  /-- `[]I`. -/
  | boxI {Δ Γ e a A} (h : CDerivesAt Ξ Δ Γ e (.val A)) (hΓ : CtxOutlives Δ Γ a) :
      CDerivesAt Ξ Δ Γ e (.val (.box a A))
  | boxE {Δ Γ e a A} (h : CDerivesAt Ξ Δ Γ e (.val (.box a A))) : CDerivesAt Ξ Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : CDerivesAt Ξ Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      CDerivesAt Ξ Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : CDerivesAt Ξ Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      CDerivesAt Ξ Δ Γ e (.val (.mut a A))
  /-- The borrow axioms, at arbitrary value-type payloads. -/
  | alloc {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ forget (.val axForgetUnkTy)
  /-- An integer literal at its width.  `[spec §8]` -/
  | lit {Δ Γ} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width))
  /-- A host operation at `!(A ⊸ F B)`, its signature in `SPEC.md` §8.  `[spec §8]` -/
  | hostOp {Δ Γ} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op)))
  /-- `array_new : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)`, the step `tab`.  `[spec §9]` -/
  | arrNew {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .tab)) (.val (arrNewTy A))
  /-- `array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)`, the step `drop`.  `[spec §9]` -/
  | arrFree {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A))
  /-- `array_size : !(Array A ⇒ Array A ⊗ I32)`.  `[spec §9]` -/
  | arrSize {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) : CDerivesAt Ξ Δ Γ (.val sizeV) (.val (arrSizeTy A))
  /-- `array_replace : !(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))`.  `[spec §9]` -/
  | arrReplace {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val replaceV) (.val (arrReplaceTy A))
  /-- `array_len : !(ArrayImm @a A ⇒ I32)`.  `[spec §9]` -/
  | arrLen {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val arrLenV) (.val (arrLenTy a A))
  /-- `array_get : !(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | arrGet {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A))
  /-- `array_copy : !(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)`.  `[spec §9]` -/
  | arrCopy {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val copyV) (.val (arrCopyTy a A))
  /-- `array_forget : !(ArrayImm @a A ⇒ 1)`.  `[spec §9]` -/
  | arrForget {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val forgetV) (.val (arrForgetTy a A))
  /-- `count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`, the step `count`: the counted
  loop, total at every host.  `[spec §16]` -/
  | countFold {Δ Γ} (S : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .count)) (.val (countFoldTy S))
  /-- `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`, the step `countTry`: the
  counted loop with an exit, total at every host.  `[spec §16]` -/
  | countTry {Δ Γ} (S E : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .countTry)) (.val (countTryTy S E))
  /-- `bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`, the step
  `boundedFix`: the fixed point with a budget of depth, total at every host and every
  computation type.  `[spec §20]` -/
  | boundedFix {Δ Γ} (A : VTy) (C : CTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C))
  /-- `slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `mut` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowM {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))
  /-- `slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `imm` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowI {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))
  /-- `slice_get_mut : !([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | sliceGetM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A))
  /-- `slice_len_mut : !([Mut @a A] ⇒ [Mut @a A] ⊗ I32)`.  `[spec §9]` -/
  | sliceLenM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val sizeV) (.val (sliceLenMTy a A))
  /-- `slice_split_imm : !([Imm @a A] ⊗ I32 ⇒ ([Imm @a A] ⊗ [Imm @a A]) ⊕ [Imm @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A))
  /-- `slice_split_mut : !([Mut @a A] ⊗ I32 ⇒ ([Mut @a A] ⊗ [Mut @a A]) ⊕ [Mut @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A))
  /-- `slice_empty_imm : [Imm @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val emptyFamV) (.val (.arrayImm a A))
  /-- `slice_empty_mut : [Mut @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val emptyFamV) (.val (.sliceMut a A))
  /-- `slice_replace_mut : !([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))`, `array_replace`'s
  term.  `[spec §9]` -/
  | sliceReplaceM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A))
  /-- `slice_swap_mut : !([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])`.  `[spec §9]` -/
  | sliceSwapM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val swapV) (.val (sliceSwapMTy a A))
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  /-- `withbor` (2): `Ref A` lent as `Mut 'x A`, its side condition `Δ ⊢ A ⊒ @b` non-strict.
  `[spec §23]` -/
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ withswap (.val (axWithswapTy a A B))
  /-- The unwinding form of `withbor` (1): `Ref A` lent as `Imm 'x A` to a callback at a row of
  abortive operations; when it unwinds, the finaliser `d` runs on the source.  `[spec §19]` -/
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (2): `Ref A` lent as `Mut 'x A`, its side condition
  non-strict.  `[spec §19, §23]` -/
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (3): `Mut @a A` reborrowed as `Mut 'x A`.  `[spec §19]` -/
  | withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.mut a A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `withload`: its own term, the source consumed by the load.
  `[spec §19]` -/
  | withloadU {Δ Γ a A B} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) :
      CDerivesAt Ξ Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_mut`: an owned array lent as a family of `mut` leaves.
  `[spec §19]` -/
  | sliceBorrowMU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_imm`: an owned array lent as a family of `imm` leaves.
  `[spec §19]` -/
  | sliceBorrowIU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S))
  -- Call-by-value derived forms: BoLo's application and `∀E` on arbitrary subterms, and the
  -- reading of a computation of `F A` as a value-judged expression at `A`.
  /-- Call-by-value application `f a`, both arbitrary, at `VTy.lolli` (`lolliE_compatX`).  `[spec §3]` -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (ha : CDerivesAt Ξ Δ Γ₁ a (.val A)) (hf : CDerivesAt Ξ Δ Γ₂ f (.val (.lolli A B))) :
      CDerivesAt Ξ Δ Γ (.app f a) (.val B)
  /-- Call-by-value `∀E`: `e []` for `e` at `VTy.all x b A` (`allE_compatX`).  `[spec §3]` -/
  | allEV {Δ Γ e x b a A} (h : CDerivesAt Ξ Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      CDerivesAt Ξ Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  /-- A computation of `F A` is a value-judged expression at `A`: `SemV` is `SemC` at `F A`.  `[spec §3]` -/
  | ofRet {Δ Γ e A} (h : CDerivesAt Ξ Δ Γ e (.comp (.ret A))) : CDerivesAt Ξ Δ Γ e (.val A)
  /-- `roll`: a value of `A[μX. A/X]` is a value of `μX. A`, at a closed `μ` whose variable is
  outside `A`'s `Mut` payloads (`docs/scope-recursion.md` §2.2).  `[spec §6]` -/
  | roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : CDerivesAt Ξ Δ Γ e (.val (VTy.inst (.mu A) A))) : CDerivesAt Ξ Δ Γ e (.val (.mu A))
  /-- `unroll`: a value of `μX. A` is a value of `A[μX. A/X]`.  `[spec §6]` -/
  | unroll {Δ Γ e A} (h : CDerivesAt Ξ Δ Γ e (.val (.mu A))) :
      CDerivesAt Ξ Δ Γ e (.val (VTy.inst (.mu A) A))
  /-- The borrowed fold, a constant:
  `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)`, for `T` built by
  `⊗`/`⊕` from closed leaves, `Ref X` and `X` (not `X` itself), `A_R = Imm̲ 'y T` with `R` at
  every recursive position, `R` outliving every lifetime, `'y` free in neither `μX. T` nor
  `R`.  `[spec §6]` -/
  | foldImm {Δ Γ} (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
      (hF : F.WF) (hG : F.Guarded) (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R)
      (hR : ∀ Δ' a, VOutlives Δ' a R) :
      CDerivesAt Ξ Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))
  /-- The owned fold, a constant: `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`, for `T` of the
  same class, `A′_R = T` with `R` at every recursive position, any `R`.  `[spec §6]` -/
  | foldOwn {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerivesAt Ξ Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))
  /-- The owned fold with reuse, a constant: `foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`,
  for `T` of the same class, `A″_R = T` with `R` at a head `X` and `Ref 1 ⊗ R` at every `Ref X`
  (the emptied cell and the result on its content), any `R`.  `[spec §6]` -/
  | foldReuse {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerivesAt Ξ Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))
  /-- `νX. C` is its unrolling `C[U(νX. C)/X]` (`cC_nu_iff`), on the same term, at a positive
  `C`.  `[spec §7]` -/
  | nuIn {Δ Γ e C} (hC : C.NuOk) (h : CDerivesAt Ξ Δ Γ e (.comp C.unroll)) :
      CDerivesAt Ξ Δ Γ e (.comp (.nu C))
  | nuOut {Δ Γ e C} (hC : C.NuOk) (h : CDerivesAt Ξ Δ Γ e (.comp (.nu C))) :
      CDerivesAt Ξ Δ Γ e (.comp C.unroll)
  /-- Coiteration, a constant: `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` (`Nu.lean`), at a
  positive `C`.  `[spec §7]` -/
  | unfoldN {Δ Γ} (C : CTy) (S : VTy) (hC : C.NuOk) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
  /-- `[sub]`: `F_Σ A ≤ F_Σ′ A` for `Σ ⊆ Σ′`; `F A = F_∅ A`.  `[spec §19]` -/
  | effSub {Δ Γ e} {S S' : Row} {A : VTy} (hle : RowLe S S')
      (h : CDerivesAt Ξ Δ Γ e (.comp (CTy.effOf S A))) : CDerivesAt Ξ Δ Γ e (.comp (CTy.effOf S' A))
  /-- `[perform]`: a non-abortive operation of the row, the row tied to `Ξ`.  `[spec §19]` -/
  | effPerform {Δ Γ V} {S : Row} {o : OpSig} (hAt : RowAt Ξ S) (hf : Row.find S o.n o.i = some o)
      (hna : o.abort = false) (h : CDerivesAt Ξ Δ Γ V (.val o.A)) :
      CDerivesAt Ξ Δ Γ (BoCa.BoLo.performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B))
  /-- `[raise]`: an abortive operation of the row, at any answer, its argument dropping, the row
  tied to `Ξ`.  `[spec §19]` -/
  | effRaise {Δ Γ V} {S : Row} {o : OpSig} {B : VTy} (hAt : RowAt Ξ S)
      (hf : Row.find S o.n o.i = some o)
      (ha : o.abort = true) (hd : o.A.Drop) (h : CDerivesAt Ξ Δ Γ V (.val o.A)) :
      CDerivesAt Ξ Δ Γ (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B))
  /-- `[let]`: `M to x. N` at a row; `N`'s context drops at a row with weakening and is
  persistent at an unrestricted row.  `[spec §19]` -/
  | effLet {Δ Γ Γ₁ Γ₂ M N A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
      CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B))
  /-- `[then]`: `M then x. N unwind D`, the finaliser at the pure row: its raises are handled
  inside it, so none escapes it (option A, Core's `CDerives.effThenA`).  `[spec §19, §24, §27]` -/
  | effThen {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ)
      (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂)
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
      (hD : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
      CDerivesAt Ξ Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
  /-- `[handle]`: `handle_n e with H`, the handler's pair `H = (h_ret, hs)` a value form over a
  part of the context whose live slots are persistent, `n` not in `Σ`.  At two variables it is
  `hndTerm` (`CDerivesAt.effHandle`).  `[spec §19, §24]` -/
  | effHandleV {Δ Γ Γ₁ Γ₂ H e} {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32}
      {A R : VTy} (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
      (hc : CDerivesAt Ξ Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E))))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
      CDerivesAt Ξ Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
  /-- `[let-poly]`: `let x = λy. b in N` for a closed λ-value, from `N` with the λ-value for `x`,
  `x`'s slot dead.  Each occurrence of the λ-value in `N` is typed on its own, at its own row: the
  kernel's row polymorphism, with the value restriction.  `[spec §24]` -/
  | letPoly {Δ Γ N C} {j : Jdg} (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true)
      (hV : CDerivesAt Ξ Δ [] (.val (.lam b)) j)
      (hN : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 (Val.lam b)).shift 1 0) (.comp C)) :
      CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) (.val (.lam b))) (.comp C)

/-- **Every tied derivation is one of Core's.** -/
theorem CDerivesAt.toCDerives {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : CDerives Δ Γ e j := by
  induction h with
  | var h => exact .var h
  | unitI h => exact .unitI h
  | tensorI hs _ _ ih1 ih2 => exact .tensorI hs ih1 ih2
  | sumI₁ _ ih1 => exact .sumI₁ ih1
  | sumI₂ _ ih1 => exact .sumI₂ ih1
  | thunkF _ ih1 => exact .thunkF ih1
  | thunkV hC _ ih1 => exact .thunkV hC ih1
  | ret _ ih1 => exact .ret ih1
  | bind hs _ _ ih1 ih2 => exact .bind hs ih1 ih2
  | force h => exact .force h
  | lam _ ih1 => exact .lam ih1
  | lamDead _ ih1 => exact .lamDead ih1
  | app hs _ hx ih1 => exact .app hs ih1 hx
  | withI _ _ ih1 ih2 => exact .withI ih1 ih2
  | proj₁ _ ih1 => exact .proj₁ ih1
  | proj₂ _ ih1 => exact .proj₂ ih1
  | topI => exact .topI
  | unitE hs _ _ ih1 ih2 => exact .unitE hs ih1 ih2
  | tensorE hs _ _ ih1 ih2 => exact .tensorE hs ih1 ih2
  | sumE hs _ _ _ ih1 ih2 ih3 => exact .sumE hs ih1 ih2 ih3
  | zeroE hs _ ih1 => exact .zeroE hs ih1
  | allI hbx hΔx hΓx _ ih1 => exact .allI hbx hΔx hΓx ih1
  | allE _ hlt ih1 => exact .allE ih1 hlt
  | bangThunkF hp _ ih1 => exact .bangThunkF hp ih1
  | bangThunkV hp hC _ ih1 => exact .bangThunkV hp hC ih1
  | bangE _ ih1 => exact .bangE ih1
  | copyBang hΓ => exact .copyBang hΓ
  | forgetBang hΓ => exact .forgetBang hΓ
  | boxI _ hΓ ih1 => exact .boxI ih1 hΓ
  | boxE _ ih1 => exact .boxE ih1
  | immSub _ hle ih1 => exact .immSub ih1 hle
  | mutSub _ hle ih1 => exact .mutSub ih1 hle
  | alloc hΓ => exact .alloc hΓ
  | free hΓ => exact .free hΓ
  | swap hΓ => exact .swap hΓ
  | copy hΓ => exact .copy hΓ
  | forgetImm hΓ => exact .forgetImm hΓ
  | forgetMut hΓ => exact .forgetMut hΓ
  | forgetUnk hΓ => exact .forgetUnk hΓ
  | lit c hΓ => exact .lit c hΓ
  | hostOp op hΓ => exact .hostOp op hΓ
  | arrNew A hΓ => exact .arrNew A hΓ
  | arrFree A hΓ => exact .arrFree A hΓ
  | arrSize A hΓ => exact .arrSize A hΓ
  | arrReplace A hΓ => exact .arrReplace A hΓ
  | arrLen a A hΓ => exact .arrLen a A hΓ
  | arrGet a A hΓ => exact .arrGet a A hΓ
  | arrCopy a A hΓ => exact .arrCopy a A hΓ
  | arrForget a A hΓ => exact .arrForget a A hΓ
  | countFold S hΓ => exact .countFold S hΓ
  | countTry S E hΓ => exact .countTry S E hΓ
  | boundedFix A C hΓ => exact .boundedFix A C hΓ
  | sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂ => exact .sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂
  | sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂ => exact .sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂
  | sliceGetM a A hΓ => exact .sliceGetM a A hΓ
  | sliceLenM a A hΓ => exact .sliceLenM a A hΓ
  | sliceSplitI a A hΓ => exact .sliceSplitI a A hΓ
  | sliceSplitM a A hΓ => exact .sliceSplitM a A hΓ
  | sliceEmptyI a A hΓ => exact .sliceEmptyI a A hΓ
  | sliceEmptyM a A hΓ => exact .sliceEmptyM a A hΓ
  | sliceReplaceM a A hΓ => exact .sliceReplaceM a A hΓ
  | sliceSwapM a A hΓ => exact .sliceSwapM a A hΓ
  | withbor1 x hΓ hx hsc₁ hfree₁ hfree₂ => exact .withbor1 x hΓ hx hsc₁ hfree₁ hfree₂
  | withbor2 x hΓ hx hside hfree₁ hfree₂ => exact .withbor2 x hΓ hx hside hfree₁ hfree₂
  | withbor3 x hΓ hx hfree₁ hfree₂ => exact .withbor3 x hΓ hx hfree₁ hfree₂
  | withload x hΓ hx hfree₁ hfree₂ => exact .withload x hΓ hx hfree₁ hfree₂
  | withswap hΓ => exact .withswap hΓ
  | withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc _ ih1 => exact .withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc ih1
  | withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc _ ih1 => exact .withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc ih1
  | withbor3U x hΓ hx hfree₁ hfree₂ hS hdc _ ih1 => exact .withbor3U x hΓ hx hfree₁ hfree₂ hS hdc ih1
  | withloadU x hΓ hx hfree₁ hfree₂ hS => exact .withloadU x hΓ hx hfree₁ hfree₂ hS
  | sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 => exact .sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc ih1
  | sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 => exact .sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc ih1
  | lolliE hs _ _ ih1 ih2 => exact .lolliE hs ih1 ih2
  | allEV _ hlt ih1 => exact .allEV ih1 hlt
  | ofRet _ ih1 => exact .ofRet ih1
  | roll hA hc _ ih1 => exact .roll hA hc ih1
  | unroll _ ih1 => exact .unroll ih1
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact .foldImm F y c R hΓ hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R hΓ hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R hΓ hF hG
  | nuIn hC _ ih1 => exact .nuIn hC ih1
  | nuOut hC _ ih1 => exact .nuOut hC ih1
  | unfoldN C S hC hΓ => exact .unfoldN C S hC hΓ
  | effSub hle _ ih1 => exact .effSub hle ih1
  | effPerform _ hf hna _ ih1 => exact .effPerform hf hna ih1
  | effRaise _ hf ha hd _ ih1 => exact .effRaise hf ha hd ih1
  | effLet hs hW hU _ _ ih1 ih2 => exact .effLet hs hW hU ih1 ih2
  | effThen hs hNZ hUq hU _ _ _ ih1 ih2 ih3 => exact CDerives.effThenA hs hNZ hUq hU ih1 ih2 ih3
  | effHandleV _ hs hd hH _ hn0 hnS hlen _ ihc ihe => exact .effHandleV hs hd hH ihc hn0 hnS hlen ihe
  | letPoly b hcl _ _ ihV ihN => exact .letPoly b hcl ihV ihN

/-- `[handle]` at two variables, tied: Core's `CDerives.effHandle` with the handled row tied to
`Ξ`.  `[spec §19]` -/
theorem CDerivesAt.effHandle {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen he

/-! ### What the tie gives at a handler -/

/-- A signature's row finds its `j`-th operation at the index `j`, below `2³²`. -/
theorem find_ofEff_at (n : UInt32) (E : List (Qual × VTy × VTy)) (j : Nat) (hj : j < E.length)
    (hlen : E.length ≤ 2 ^ 32) :
    Row.find (Row.ofEff n E 0) n (UInt32.ofNat j) = some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit⟩ := by
  have hj' : j < 2 ^ 32 := by omega
  have hi : (UInt32.ofNat j).toNat = 0 + j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp
    (Inst.find_ofEff_isSome n E 0 j (UInt32.ofNat j) hi (by omega) hj)
  obtain ⟨-, j', hj'', hij, rfl⟩ := Row.find_ofEff n E 0 _ n _ o ho
  have : j' = j := by
    have h2 := congrArg UInt32.toNat hij
    rw [hi, Nat.zero_add, Nat.zero_add,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h2
    exact h2.symm
  subst this
  rw [ho, Nat.zero_add]

/-- A signature's row at the signature the context declares, before a row tied to the context, is
tied to it. -/
theorem rowAt_ofEff_append {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (hE : Ξ n = E) (hn : n ≠ 0) (hlen : E.length ≤ 2 ^ 32) (hS : RowAt Ξ S) :
    RowAt Ξ (Row.ofEff n E 0 ++ S) := by
  subst hE
  exact rowAt_append (ofEff_wf Ξ n hn hlen) hS

/-- **A tied handler's signature is a prefix of the context's**: the handled row `(n)↑E ⊙ Σ`, tied
to `Ξ`, finds each operation of `E` at the signature `Ξ n` declares at its index. -/
theorem sig_prefix_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) : E <+: Ξ n := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < E.length
  · have hf : Row.find (Row.ofEff n E 0 ++ S) n (UInt32.ofNat j) =
        some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit⟩ := by
      rw [Row.find_append, find_ofEff_at n E j hj hlen, Option.some_or]
    obtain ⟨-, -, hg⟩ := h n _ _ hf
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hg
    rw [List.getElem?_take_of_lt hj, hg, List.getElem?_eq_getElem hj]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    simp only [List.length_take]
    omega

/-- **A tied handler's tags are a prefix of the context's qualifiers** of its name (SPEC §25: a
handler value carries its operations' qualifiers, `E.map Prod.fst`). -/
theorem hndTags_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) :
    E.map Prod.fst <+: (Ξ n).map Prod.fst :=
  (sig_prefix_of_rowAt h hlen).map Prod.fst

/-! ### Inversions: what the tied kernel types at a handler -/

/-- A list of qualifiers is told apart by its tags. -/
theorem qualsVal_inj : ∀ {qs qs' : List Qual}, (qualsVal qs).1 = (qualsVal qs').1 → qs = qs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [qualsVal, Val.unit, Val.pair] at h
  | _ :: _, [], h => by simp [qualsVal, Val.unit, Val.pair] at h
  | q :: qs, q' :: qs', h => by
      simp only [qualsVal, Val.pair, Val.i32, Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq,
        IntLit.i32.injEq] at h
      obtain ⟨hq, hqs⟩ := h
      rw [qualsVal_inj hqs]
      cases q <;> cases q' <;> first | rfl | exact absurd hq (by decide)

/-- The term constants of `CDerivesAt`'s conclusions, unfolded to their head constructors, so that
a rule whose conclusion's term has another head is told apart (`cdnu_terms`, with the handler at a
value form). -/
macro "cdat_terms" : tactic => `(tactic| (try simp_all [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, foldReuseV, unfoldV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, thenE, hndTerm, hndExpr, Expr.val, Val.lam, Val.prim, Val.unit,
    Val.i32, lam2, elet, unit']))

/-- `hnd` alone has no tied derivation. -/
theorem not_derAt_prim_hnd {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : e ≠ .prim .hnd := by
  induction h <;> intro he <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_derAt_prim_hnd' {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ (.prim .hnd) j := fun h => not_derAt_prim_hnd h rfl

/-- `hnd X` alone has no tied derivation. -/
theorem not_derAt_app_hnd {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ X, e ≠ .app (.prim .hnd) X := by
  induction h <;> intro X he <;> cdat_terms <;> (try simp_all [not_derAt_prim_hnd'])
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_derAt_app_hnd' {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ (.app (.prim .hnd) X) j := fun h => not_derAt_app_hnd h X rfl

/-- **A tied derivation of a handler term**: `[handle]` is the only rule whose conclusion's term is
`hnd (n, (Q, H)) M`; tags `Q` are a prefix of `Ξ`'s qualifiers of `n`, and the body `M` is typed. -/
theorem derAt_hnd {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ (n : UInt32) (Q H M : Expr),
      e = .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M →
      (∀ qs : List Qual, Q = (qualsVal qs).1 → qs <+: (Ξ n).map Prod.fst) ∧
        ∃ (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ Γ' M (.comp C) := by
  induction h <;> intro n Q H M he <;> cdat_terms <;> (try simp_all [not_derAt_app_hnd'])
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  case effHandleV _ _ _ _ _ e' S E n' A R hAt _ _ _ _ _ _ hlen he' _ _ =>
    obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := he
    refine ⟨fun qs hq => ?_, _, _, he'⟩
    rw [← qualsVal_inj hq]
    exact hndTags_of_rowAt hAt hlen

/-- **A tied derivation of a λ-value whose body is an application** types the body, at some
contexts: no term constant is such a λ-value. -/
theorem derAt_lam {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ N F A, e = .lam N → N = .app F A →
      ∃ (Δ' : LifeCtx) (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ' Γ' N (.comp C) := by
  induction h <;> intro N F A he hN <;> subst hN <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  all_goals (subst he; exact ⟨_, _, _, by assumption⟩)

/-- **A tied derivation of a `let`** `(λx. N) M`: its body is typed (`[let]`, `[let]` at a row), or
`M` is a λ-value and the body with it in place is typed (`[let-poly]`), or the λ-value `λx. N` is
typed (call-by-value application). -/
theorem derAt_let {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ N M, e = .app (.lam N) M →
      (∃ (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ Γ' N (.comp C)) ∨
      (∃ b, M = .lam b ∧ ∃ (Γ' : Ctx VTy) (C : CTy),
        CDerivesAt Ξ Δ Γ' ((N.subst 0 (Val.lam b)).shift 1 0) (.comp C)) ∨
      (∃ (Γ' : Ctx VTy) (j' : Jdg), CDerivesAt Ξ Δ Γ' (.lam N) j') := by
  induction h <;> intro N M he <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  all_goals first
    | exact .inl ⟨_, _, by assumption⟩
    | exact .inr (.inr ⟨_, _, by assumption⟩)
    | (obtain ⟨-, rfl⟩ := ‹_ ∧ _›; exact .inr (.inl ⟨_, rfl, _, _, by assumption⟩))

section Weaken
variable {Γ' : Ctx VTy}

/-- **Weakening by consumed slots at the end**, tied: Core's `CDerives.append_dead`. -/
theorem CDerivesAt.append_dead {Ξ : EffCtx} (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {j : Jdg} (h : CDerivesAt Ξ Δ Γ e j) : CDerivesAt Ξ Δ (Γ ++ Γ') e j := by
  induction h with
  | var hs => exact .var (soloP_append h' hs)
  | unitI hd => exact .unitI (deadP_append h' hd)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (splitP_append h' hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (splitP_append h' hs) ihM ihN
  | force hs => exact .force (soloP_append h' hs)
  | lam _ ih => exact .lam ih
  | lamDead _ ih => exact .lamDead ih
  | app hs _ hx ih => exact .app (splitP_append h' hs) ih (soloP_append h' hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (splitP_append h' hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (splitP_append h' hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (splitP_append h' hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (splitP_append h' hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append h' hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (persistent_append h' hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (persistent_append h' hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (deadP_append h' hΓ)
  | forgetBang hΓ => exact .forgetBang (deadP_append h' hΓ)
  | boxI _ hΓ ih => exact .boxI ih (ctxOutlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (deadP_append h' hΓ)
  | free hΓ => exact .free (deadP_append h' hΓ)
  | swap hΓ => exact .swap (deadP_append h' hΓ)
  | copy hΓ => exact .copy (deadP_append h' hΓ)
  | forgetImm hΓ => exact .forgetImm (deadP_append h' hΓ)
  | forgetMut hΓ => exact .forgetMut (deadP_append h' hΓ)
  | forgetUnk hΓ => exact .forgetUnk (deadP_append h' hΓ)
  | lit c hΓ => exact .lit c (deadP_append h' hΓ)
  | hostOp op hΓ => exact .hostOp op (deadP_append h' hΓ)
  | arrNew A hΓ => exact .arrNew A (deadP_append h' hΓ)
  | arrFree A hΓ => exact .arrFree A (deadP_append h' hΓ)
  | arrSize A hΓ => exact .arrSize A (deadP_append h' hΓ)
  | arrReplace A hΓ => exact .arrReplace A (deadP_append h' hΓ)
  | arrLen a A hΓ => exact .arrLen a A (deadP_append h' hΓ)
  | arrGet a A hΓ => exact .arrGet a A (deadP_append h' hΓ)
  | arrCopy a A hΓ => exact .arrCopy a A (deadP_append h' hΓ)
  | arrForget a A hΓ => exact .arrForget a A (deadP_append h' hΓ)
  | countFold S hΓ => exact .countFold S (deadP_append h' hΓ)
  | countTry S E hΓ => exact .countTry S E (deadP_append h' hΓ)
  | boundedFix A C hΓ => exact .boundedFix A C (deadP_append h' hΓ)
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact .sliceBorrowM x (deadP_append h' hΓ) hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      exact .sliceBorrowI x (deadP_append h' hΓ) hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => exact .sliceGetM a A (deadP_append h' hΓ)
  | sliceLenM a A hΓ => exact .sliceLenM a A (deadP_append h' hΓ)
  | sliceSplitI a A hΓ => exact .sliceSplitI a A (deadP_append h' hΓ)
  | sliceSplitM a A hΓ => exact .sliceSplitM a A (deadP_append h' hΓ)
  | sliceEmptyI a A hΓ => exact .sliceEmptyI a A (deadP_append h' hΓ)
  | sliceEmptyM a A hΓ => exact .sliceEmptyM a A (deadP_append h' hΓ)
  | sliceReplaceM a A hΓ => exact .sliceReplaceM a A (deadP_append h' hΓ)
  | sliceSwapM a A hΓ => exact .sliceSwapM a A (deadP_append h' hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (deadP_append h' hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x (deadP_append h' hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (deadP_append h' hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (deadP_append h' hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (deadP_append h' hΓ)
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor1U x (deadP_append h' hΓ) hx hsc hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor2U x (deadP_append h' hΓ) hx hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor3U x (deadP_append h' hΓ) hx hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ hx hf₁ hf₂ hS => exact .withloadU x (deadP_append h' hΓ) hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowMU x (deadP_append h' hΓ) hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowIU x (deadP_append h' hΓ) hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact .lolliE (splitP_append h' hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (deadP_append h' hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (deadP_append h' hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (deadP_append h' hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (deadP_append h' hΓ)
  | effSub hle _ ih => exact .effSub hle ih
  | effPerform hAt hf hna _ ih => exact .effPerform hAt hf hna ih
  | effRaise hAt hf ha hd _ ih => exact .effRaise hAt hf ha hd ih
  | effLet hs hW hU _ _ ihM ihN =>
      exact .effLet (splitP_append h' hs)
        (fun hw => live_append (P := fun s => s.ty.Drop) h' (hW hw))
        (fun hu => persistent_append h' (hU hu)) ihM ihN
  | effThen hs hNZ hUq hU _ _ _ ihM ihN ihD =>
      exact .effThen (splitP_append h' hs) hNZ hUq (fun hu => persistent_append h' (hU hu))
        ihM ihN ihD
  | effHandleV hAt hs hd hH _ hn0 hnS hlen _ ihc ihe =>
      exact .effHandleV hAt (splitP_append h' hs) (deadP_append h' hd) hH.append ihc hn0 hnS hlen
        ihe
  | letPoly b hcl hV _ _ ihN => exact .letPoly b hcl hV ihN

end Weaken

end Targets

end
