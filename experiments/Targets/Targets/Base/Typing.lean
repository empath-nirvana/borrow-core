import Core.Fundamental
import Targets.Base.Rows

/-!
# Base — the typing parameter (RESTRUCTURE §0, base; DESIGN §1.2)

A typing system is a judgement with a
row context (`Judgment`); Core's `VTy`/`CTy` have no row-variable former, so a type that mentions
row variables is the family of its closed instances (the Instance's open types,
`Targets/Instance/Types.lean`, add the row `∀` that families cannot express).

* `OutJ`: the outlives judgements a typing system consults.
* `tier1`: Core's `CDerives` at every admissible instance.  `CDerivesNU`: Core's rules with
  `Row.NU` at the five effect rules whose semantic case reads the protocol; `tier1NU`.
* `RulesClosed J R`, `Extends`, `ExtendsNU`; and their proofs at `tier1` (`rc_*_tier1`,
  `rc_*_tier1NU`, `extendsNU_tier1`, `outExtends_core`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore performE raiseE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The outlives judgments a typing system consults: `Δ ⊢ A ⊐ @a` (`lt`) and `Δ ⊢ A ⊒ @a`
(`le`).  Core's are `VOutlives` and `VOutlivesLe` (`Core/Types.lean`); neither has a rule at
`U C`, and whether tier 2 adds one is OQ-28. -/
structure OutJ where
  lt : LifeCtx → Lifetime.Life → VTy → Prop
  le : LifeCtx → Lifetime.Life → VTy → Prop

/-- Core's outlives judgments. -/
def OutJ.core : OutJ := ⟨VOutlives, VOutlivesLe⟩

/-- The judgments extend Core's, and `⊐` gives `⊒` (`VOutlives.toLe`). -/
def OutExtends (O : OutJ) : Prop :=
  (∀ Δ a A, VOutlives Δ a A → O.lt Δ a A) ∧ (∀ Δ a A, VOutlivesLe Δ a A → O.le Δ a A) ∧
  (∀ Δ a A, O.lt Δ a A → O.le Δ a A)

/-- `Δ ⊨ Γ ⊐ @a` at the outlives judgment `O` (`CtxOutlives` with `VOutlives` read as `O.lt`). -/
def CtxOutlivesJ (O : OutJ) (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → O.lt Δ a s.ty

/-- `Row.Unwind` (`Core/EffBorrow.lean`) with its `VOutlives` read as `O.lt`. -/
def Row.UnwindJ (O : OutJ) (x : LifeVar) (S : Row) : Prop :=
  ∀ o ∈ S, o.abort = true ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ ∀ Δ a, O.lt Δ a o.A

theorem ctxOutlivesJ_core {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} :
    CtxOutlivesJ OutJ.core Δ Γ a ↔ CtxOutlives Δ Γ a := Iff.rfl

theorem unwindJ_core {x : LifeVar} {S : Row} : Row.UnwindJ OutJ.core x S ↔ S.Unwind x := Iff.rfl

/-- A judgment `Θ; Δ; Γ ⊢ e : j`, with `Γ` and `j` families over the row environment. -/
abbrev Judgment := RowCtx → LifeCtx → (RowEnv → Ctx VTy) → Expr → (RowEnv → Jdg) → Prop

/-- **A typing system**: a judgment, and the outlives judgments its rules consult. -/
structure TypingJ where
  der : Judgment
  out : OutJ

instance : CoeFun TypingJ (fun _ => Judgment) := ⟨TypingJ.der⟩

/-- A judgment with no row variable. -/
def TypingJ.at (J : TypingJ) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  J [] Δ (fun _ => Γ) e (fun _ => j)

/-- A closed program at a computation type. -/
def TypingJ.closed (J : TypingJ) (e : Expr) (C : CTy) : Prop := J.at LifeCtx.empty [] e (.comp C)

/-- **Tier 1**: Core's `CDerives` at every admissible instance, at Core's outlives judgments.  It
has the `unr` rules, and is used only at Core σ=[]. -/
def tier1 : TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → CDerives Δ (Γ η) e (j η), OutJ.core⟩

/-- **Core's monomorphic rules without resuming `unr` operations.**  `CDerives`'s constructors
(`Core/Fundamental.lean`) verbatim but two, with the premise `Row.NU` added at five of them:
`effPerform` (on `S`), `effLet` and `effThen` (on `S`), `effSub` (on the target row `S'`), and
`effHandle` (on `Row.ofEff n E 0 ++ S`).  The two are SPEC §24's: the polymorphic let `letPoly` is
left out, and `[handle]` is its instance at two clause variables (`CDerives.effHandle`); the row
`∀` and the handler at clause values are `J₁`'s (`Targets/Instance/J1.lean`). -/
inductive CDerivesNU : LifeCtx → Ctx VTy → Expr → Jdg → Prop where
  | var {Δ Γ i A} (h : Ctx.SoloP Γ i A) : CDerivesNU Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : Ctx.DeadP Γ) : CDerivesNU Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (h₁ : CDerivesNU Δ Γ₁ e₁ (.val A)) (h₂ : CDerivesNU Δ Γ₂ e₂ (.val B)) :
      CDerivesNU Δ Γ (.pair e₁ e₂) (.val (.tensor A B))
  | sumI₁ {Δ Γ e A B} (h : CDerivesNU Δ Γ e (.val A)) :
      CDerivesNU Δ Γ (.inj₁ e) (.val (.sum A B))
  | sumI₂ {Δ Γ e A B} (h : CDerivesNU Δ Γ e (.val B)) :
      CDerivesNU Δ Γ (.inj₂ e) (.val (.sum A B))
  /-- `thunk M : U (F A)`, `M` under a dead binder. -/
  | thunkF {Δ Γ M A} (h : CDerivesNU Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerivesNU Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
  /-- `thunk V : U C` for a λ-value `V : C`, `C` not an `F`. -/
  | thunkV {Δ Γ N C} (hC : C.isRet = false) (h : CDerivesNU Δ Γ (.val (.lam N)) (.comp C)) :
      CDerivesNU Δ Γ (.val (.lam N)) (.val (.thunk C))
  /-- `return V : F A`. -/
  | ret {Δ Γ V A} (h : CDerivesNU Δ Γ V (.val A)) : CDerivesNU Δ Γ V (.comp (.ret A))
  /-- `M to x. N`, written `(λx. N) M`. -/
  | bind {Δ Γ Γ₁ Γ₂ M N A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerivesNU Δ Γ₁ M (.comp (.ret A))) (hN : CDerivesNU Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      CDerivesNU Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.SoloP Γ i (.thunk C)) :
      CDerivesNU Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : CDerivesNU Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      CDerivesNU Δ Γ (.val (.lam M)) (.comp (.arr A C))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerivesNU Δ Γ₁ M (.comp (.arr A C))) (hx : Ctx.SoloP Γ₂ i A) :
      CDerivesNU Δ Γ (.app M (.var i)) (.comp C)
  /-- `⟨M, N⟩ : C & D`, both components in the same context. -/
  | withI {Δ Γ M N C D} (hM : CDerivesNU Δ (withCtx Γ) M (.comp C))
      (hN : CDerivesNU Δ (withCtx Γ) N (.comp D)) :
      CDerivesNU Δ Γ (withPair M N) (.comp (.amp C D))
  | proj₁ {Δ Γ M C D} (h : CDerivesNU Δ Γ M (.comp (.amp C D))) :
      CDerivesNU Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M C D} (h : CDerivesNU Δ Γ M (.comp (.amp C D))) :
      CDerivesNU Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)
  /-- `⟨⟩ : ⊤` at any context. -/
  | topI {Δ Γ} : CDerivesNU Δ Γ (.val .unit) (.comp .top)
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hV : CDerivesNU Δ Γ₁ V (.val .unit)) (hM : CDerivesNU Δ Γ₂ M (.comp C)) :
      CDerivesNU Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : CDerivesNU Δ Γp V (.val (.tensor A B)))
      (hM : CDerivesNU Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
      CDerivesNU Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : CDerivesNU Δ Γs V (.val (.sum A B)))
      (h₁ : CDerivesNU Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
      (h₂ : CDerivesNU Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
      CDerivesNU Δ Γ (.case V M₁ M₂) (.comp C)
  /-- `absurd V : C` for `V : 0`, at any rest of the context. -/
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : CDerivesNU Δ Γ₁ V (.val .zero)) :
      CDerivesNU Δ Γ (absurdE V) (.comp C)
  /-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`; the binder's slot is dead, at any type. -/
  | allI {Δ Γ x b M S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : CDerivesNU (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
      CDerivesNU Δ Γ (.val (.lam M)) (.comp (.all x b C))
  /-- `M [] : C[@a/'x]`. -/
  | allE {Δ Γ M x b a C} (h : CDerivesNU Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
      CDerivesNU Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))
  /-- Promotion of `thunk M : U (F A)` over `!Γ`. -/
  | bangThunkF {Δ Γ M A} (hp : Persistent Γ)
      (h : CDerivesNU Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerivesNU Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))
  /-- Promotion of a λ-value `V : C` over `!Γ`. -/
  | bangThunkV {Δ Γ N C} (hp : Persistent Γ) (hC : C.isRet = false)
      (h : CDerivesNU Δ Γ (.val (.lam N)) (.comp C)) :
      CDerivesNU Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))
  /-- Dereliction. -/
  | bangE {Δ Γ e A} (h : CDerivesNU Δ Γ e (.val (.bang A))) : CDerivesNU Δ Γ e (.val A)
  | copyBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  /-- `[]I`. -/
  | boxI {Δ Γ e a A} (h : CDerivesNU Δ Γ e (.val A)) (hΓ : CtxOutlives Δ Γ a) :
      CDerivesNU Δ Γ e (.val (.box a A))
  | boxE {Δ Γ e a A} (h : CDerivesNU Δ Γ e (.val (.box a A))) : CDerivesNU Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : CDerivesNU Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      CDerivesNU Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : CDerivesNU Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      CDerivesNU Δ Γ e (.val (.mut a A))
  /-- The borrow axioms, at arbitrary value-type payloads. -/
  | alloc {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ forget (.val axForgetUnkTy)
  /-- An integer literal at its width.  `[spec §8]` -/
  | lit {Δ Γ} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width))
  /-- A host operation at `!(A ⊸ F B)`, its signature in `SPEC.md` §8.  `[spec §8]` -/
  | hostOp {Δ Γ} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op)))
  /-- `array_new : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)`, the step `tab`.  `[spec §9]` -/
  | arrNew {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .tab)) (.val (arrNewTy A))
  /-- `array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)`, the step `drop`.  `[spec §9]` -/
  | arrFree {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A))
  /-- `array_size : !(Array A ⇒ Array A ⊗ I32)`.  `[spec §9]` -/
  | arrSize {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) : CDerivesNU Δ Γ (.val sizeV) (.val (arrSizeTy A))
  /-- `array_replace : !(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))`.  `[spec §9]` -/
  | arrReplace {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val replaceV) (.val (arrReplaceTy A))
  /-- `array_len : !(ArrayImm @a A ⇒ I32)`.  `[spec §9]` -/
  | arrLen {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val arrLenV) (.val (arrLenTy a A))
  /-- `array_get : !(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | arrGet {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A))
  /-- `array_copy : !(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)`.  `[spec §9]` -/
  | arrCopy {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val copyV) (.val (arrCopyTy a A))
  /-- `array_forget : !(ArrayImm @a A ⇒ 1)`.  `[spec §9]` -/
  | arrForget {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val forgetV) (.val (arrForgetTy a A))
  /-- `count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`, the step `count`: the counted
  loop, total at every host.  `[spec §16]` -/
  | countFold {Δ Γ} (S : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .count)) (.val (countFoldTy S))
  /-- `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`, the step `countTry`: the
  counted loop with an exit, total at every host.  `[spec §16]` -/
  | countTry {Δ Γ} (S E : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .countTry)) (.val (countTryTy S E))
  /-- `bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`, the step
  `boundedFix`: the fixed point with a budget of depth, total at every host and every
  computation type.  `[spec §20]` -/
  | boundedFix {Δ Γ} (A : VTy) (C : CTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C))
  /-- `slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `mut` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowM {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))
  /-- `slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `imm` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowI {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))
  /-- `slice_get_mut : !([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | sliceGetM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A))
  /-- `slice_len_mut : !([Mut @a A] ⇒ [Mut @a A] ⊗ I32)`.  `[spec §9]` -/
  | sliceLenM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val sizeV) (.val (sliceLenMTy a A))
  /-- `slice_split_imm : !([Imm @a A] ⊗ I32 ⇒ ([Imm @a A] ⊗ [Imm @a A]) ⊕ [Imm @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A))
  /-- `slice_split_mut : !([Mut @a A] ⊗ I32 ⇒ ([Mut @a A] ⊗ [Mut @a A]) ⊕ [Mut @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A))
  /-- `slice_empty_imm : [Imm @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val emptyFamV) (.val (.arrayImm a A))
  /-- `slice_empty_mut : [Mut @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val emptyFamV) (.val (.sliceMut a A))
  /-- `slice_replace_mut : !([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))`, `array_replace`'s
  term.  `[spec §9]` -/
  | sliceReplaceM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A))
  /-- `slice_swap_mut : !([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])`.  `[spec §9]` -/
  | sliceSwapM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val swapV) (.val (sliceSwapMTy a A))
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  /-- `withbor` (2): `Ref A` lent as `Mut 'x A`, its side condition `Δ ⊢ A ⊒ @b` non-strict.
  `[spec §23]` -/
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesNU Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ withswap (.val (axWithswapTy a A B))
  /-- The unwinding form of `withbor` (1): `Ref A` lent as `Imm 'x A` to a callback at a row of
  abortive operations; when it unwinds, the finaliser `d` runs on the source.  `[spec §19]` -/
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesNU Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerivesNU Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (2): `Ref A` lent as `Mut 'x A`, its side condition
  non-strict.  `[spec §19, §23]` -/
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesNU Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerivesNU Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (3): `Mut @a A` reborrowed as `Mut 'x A`.  `[spec §19]` -/
  | withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesNU Δ Γ d (.val (.lolli (.mut a A) .unit))) :
      CDerivesNU Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `withload`: its own term, the source consumed by the load.
  `[spec §19]` -/
  | withloadU {Δ Γ a A B} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) :
      CDerivesNU Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_mut`: an owned array lent as a family of `mut` leaves.
  `[spec §19]` -/
  | sliceBorrowMU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesNU Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerivesNU Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_imm`: an owned array lent as a family of `imm` leaves.
  `[spec §19]` -/
  | sliceBorrowIU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesNU Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerivesNU Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S))
  /-- Call-by-value application `f a`, both arbitrary, at `VTy.lolli` (`lolliE_compatX`).  `[spec §3]` -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (ha : CDerivesNU Δ Γ₁ a (.val A)) (hf : CDerivesNU Δ Γ₂ f (.val (.lolli A B))) :
      CDerivesNU Δ Γ (.app f a) (.val B)
  /-- Call-by-value `∀E`: `e []` for `e` at `VTy.all x b A` (`allE_compatX`).  `[spec §3]` -/
  | allEV {Δ Γ e x b a A} (h : CDerivesNU Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      CDerivesNU Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  /-- A computation of `F A` is a value-judged expression at `A`: `SemV` is `SemC` at `F A`.  `[spec §3]` -/
  | ofRet {Δ Γ e A} (h : CDerivesNU Δ Γ e (.comp (.ret A))) : CDerivesNU Δ Γ e (.val A)
  /-- `roll`: a value of `A[μX. A/X]` is a value of `μX. A`, at a closed `μ` whose variable is
  outside `A`'s `Mut` payloads (`docs/scope-recursion.md` §2.2).  `[spec §6]` -/
  | roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : CDerivesNU Δ Γ e (.val (VTy.inst (.mu A) A))) : CDerivesNU Δ Γ e (.val (.mu A))
  /-- `unroll`: a value of `μX. A` is a value of `A[μX. A/X]`.  `[spec §6]` -/
  | unroll {Δ Γ e A} (h : CDerivesNU Δ Γ e (.val (.mu A))) :
      CDerivesNU Δ Γ e (.val (VTy.inst (.mu A) A))
  /-- The borrowed fold, a constant:
  `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)`, for `T` built by
  `⊗`/`⊕` from closed leaves, `Ref X` and `X` (not `X` itself), `A_R = Imm̲ 'y T` with `R` at
  every recursive position, `R` outliving every lifetime, `'y` free in neither `μX. T` nor
  `R`.  `[spec §6]` -/
  | foldImm {Δ Γ} (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
      (hF : F.WF) (hG : F.Guarded) (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R)
      (hR : ∀ Δ' a, VOutlives Δ' a R) :
      CDerivesNU Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))
  /-- The owned fold, a constant: `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`, for `T` of the
  same class, `A′_R = T` with `R` at every recursive position, any `R`.  `[spec §6]` -/
  | foldOwn {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerivesNU Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))
  /-- The owned fold with reuse, a constant: `foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`,
  for `T` of the same class, `A″_R = T` with `R` at a head `X` and `Ref 1 ⊗ R` at every `Ref X`
  (the emptied cell and the result on its content), any `R`.  `[spec §6]` -/
  | foldReuse {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerivesNU Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))
  /-- `νX. C` is its unrolling `C[U(νX. C)/X]` (`cC_nu_iff`), on the same term, at a positive
  `C`.  `[spec §7]` -/
  | nuIn {Δ Γ e C} (hC : C.NuOk) (h : CDerivesNU Δ Γ e (.comp C.unroll)) :
      CDerivesNU Δ Γ e (.comp (.nu C))
  | nuOut {Δ Γ e C} (hC : C.NuOk) (h : CDerivesNU Δ Γ e (.comp (.nu C))) :
      CDerivesNU Δ Γ e (.comp C.unroll)
  /-- Coiteration, a constant: `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` (`Nu.lean`), at a
  positive `C`.  `[spec §7]` -/
  | unfoldN {Δ Γ} (C : CTy) (S : VTy) (hC : C.NuOk) (hΓ : Ctx.DeadP Γ) :
      CDerivesNU Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
  /-- `[sub]`: `F_Σ A ≤ F_Σ′ A` for `Σ ⊆ Σ′`; `F A = F_∅ A`.  `[spec §19]` -/
  | effSub {Δ Γ e} {S S' : Row} {A : VTy} (hNU : Row.NU S') (hle : RowLe S S')
      (h : CDerivesNU Δ Γ e (.comp (CTy.effOf S A))) : CDerivesNU Δ Γ e (.comp (CTy.effOf S' A))
  /-- `[perform]`: a non-abortive operation of the row.  `[spec §19]` -/
  | effPerform {Δ Γ V} {S : Row} {o : OpSig} (hNU : Row.NU S) (hf : Row.find S o.n o.i = some o)
      (hna : o.abort = false) (h : CDerivesNU Δ Γ V (.val o.A)) :
      CDerivesNU Δ Γ (BoCa.BoLo.performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B))
  /-- `[raise]`: an abortive operation of the row, at any answer, its argument dropping.
  `[spec §19]` -/
  | effRaise {Δ Γ V} {S : Row} {o : OpSig} {B : VTy} (hf : Row.find S o.n o.i = some o)
      (ha : o.abort = true) (hd : o.A.Drop) (h : CDerivesNU Δ Γ V (.val o.A)) :
      CDerivesNU Δ Γ (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B))
  /-- `[let]`: `M to x. N` at a row; `N`'s context drops at a row with weakening and is
  persistent at an unrestricted row.  `[spec §19]` -/
  | effLet {Δ Γ Γ₁ Γ₂ M N A B} {S : Row} (hNU : Row.NU S) (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hM : CDerivesNU Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : CDerivesNU Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
      CDerivesNU Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B))
  /-- `[then]`: `M then x. N unwind D`, the finaliser at the pure row (option A, Core's
  `CDerives.effThenA`).  `[spec §19, §24, §27]` -/
  | effThen {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hNU : Row.NU S) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ)
      (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂)
      (hM : CDerivesNU Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : CDerivesNU Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
      (hD : CDerivesNU Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
      CDerivesNU Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
  /-- `[handle]`: `handle_n e with (h_ret, hs)`, `n` not in `Σ`.  `[spec §19]` -/
  | effHandle {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)} {n : UInt32}
      {A R : VTy} {ir ic : Nat} (hNU : Row.NU (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
      (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (he : CDerivesNU Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
      CDerivesNU Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R))

/-- Every `CDerivesNU` derivation is a `CDerives` one. -/
theorem CDerivesNU.toCDerives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : CDerives Δ Γ e j := by
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
  | effSub _ hle _ ih1 => exact .effSub hle ih1
  | effPerform _ hf hna _ ih1 => exact .effPerform hf hna ih1
  | effRaise hf ha hd _ ih1 => exact .effRaise hf ha hd ih1
  | effLet _ hs hW hU _ _ ih1 ih2 => exact .effLet hs hW hU ih1 ih2
  | effThen _ hs hNZ hUq hU _ _ _ ih1 ih2 ih3 => exact CDerives.effThenA hs hNZ hUq hU ih1 ih2 ih3
  | effHandle _ hs hs₁ hr hc hn0 hnS hlen _ ih1 => exact .effHandle hs hs₁ hr hc hn0 hnS hlen ih1

/-- The unr-free fragment of tier 1. -/
def tier1NU : TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → CDerivesNU Δ (Γ η) e (j η), OutJ.core⟩

/-- `J` holds every tier-1 judgment. -/
def Tier1Sub (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, tier1 Θ Δ Γ e j → J Θ Δ Γ e j

/-- `J` holds every judgment of the unr-free fragment of tier 1. -/
def Tier1SubNU (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, tier1NU Θ Δ Γ e j → J Θ Δ Γ e j

def RC_tensorI (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (e₁ e₂ : Expr) (A B : RowEnv → VTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ e₁ (fun η => .val (A η)) → J Θ Δ Γ₂ e₂ (fun η => .val (B η)) →
    J Θ Δ Γ (.pair e₁ e₂) (fun η => .val (.tensor (A η) (B η)))

def RC_sumI₁ (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A B : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (A η)) → J Θ Δ Γ (.inj₁ e) (fun η => .val (.sum (A η) (B η)))

def RC_sumI₂ (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A B : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (B η)) → J Θ Δ Γ (.inj₂ e) (fun η => .val (.sum (A η) (B η)))

def RC_thunkF (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (A : RowEnv → VTy),
    J Θ Δ (fun η => ⟨.unit, false⟩ :: Γ η) M (fun η => .comp (.ret (A η))) →
    J Θ Δ Γ (.val (.lam M)) (fun η => .val (.thunk (.ret (A η))))

def RC_thunkV (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (N : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → (C η).isRet = false) →
    J Θ Δ Γ (.val (.lam N)) (fun η => .comp (C η)) →
    J Θ Δ Γ (.val (.lam N)) (fun η => .val (.thunk (C η)))

def RC_ret (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (V : Expr) (A : RowEnv → VTy),
    J Θ Δ Γ V (fun η => .val (A η)) → J Θ Δ Γ V (fun η => .comp (.ret (A η)))

def RC_bind (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (M N : Expr) (A : RowEnv → VTy)
    (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ M (fun η => .comp (.ret (A η))) →
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γ₂ η) N (fun η => .comp (C η)) →
    J Θ Δ Γ (.app (.val (.lam N)) M) (fun η => .comp (C η))

def RC_lam (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (A : RowEnv → VTy)
    (C : RowEnv → CTy),
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γ η) M (fun η => .comp (C η)) →
    J Θ Δ Γ (.val (.lam M)) (fun η => .comp (.arr (A η) (C η)))

def RC_app (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (M : Expr) (i : Nat)
    (A : RowEnv → VTy) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ M (fun η => .comp (.arr (A η) (C η))) →
    (∀ η, Θ.Models η → Ctx.SoloP (Γ₂ η) i (A η)) →
    J Θ Δ Γ (.app M (.var i)) (fun η => .comp (C η))

def RC_withI (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M N : Expr) (C D : RowEnv → CTy),
    J Θ Δ (fun η => withCtx (Γ η)) M (fun η => .comp (C η)) →
    J Θ Δ (fun η => withCtx (Γ η)) N (fun η => .comp (D η)) →
    J Θ Δ Γ (withPair M N) (fun η => .comp (.amp (C η) (D η)))

def RC_proj₁ (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (C D : RowEnv → CTy),
    J Θ Δ Γ M (fun η => .comp (.amp (C η) (D η))) →
    J Θ Δ Γ (.app M (.val (.inj₁ .unit))) (fun η => .comp (C η))

def RC_proj₂ (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (C D : RowEnv → CTy),
    J Θ Δ Γ M (fun η => .comp (.amp (C η) (D η))) →
    J Θ Δ Γ (.app M (.val (.inj₂ .unit))) (fun η => .comp (D η))

def RC_unitE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (V M : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ V (fun _ => .val .unit) → J Θ Δ Γ₂ M (fun η => .comp (C η)) →
    J Θ Δ Γ (.seq V M) (fun η => .comp (C η))

def RC_tensorE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γp Γb : RowEnv → Ctx VTy) (V M : Expr) (A B : RowEnv → VTy)
    (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γp η) (Γb η)) →
    J Θ Δ Γp V (fun η => .val (.tensor (A η) (B η))) →
    J Θ Δ (fun η => ⟨B η, true⟩ :: ⟨A η, true⟩ :: Γb η) M (fun η => .comp (C η)) →
    J Θ Δ Γ (.letpair V M) (fun η => .comp (C η))

def RC_sumE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γs Γb : RowEnv → Ctx VTy) (V M₁ M₂ : Expr)
    (A B : RowEnv → VTy) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γs η) (Γb η)) →
    J Θ Δ Γs V (fun η => .val (.sum (A η) (B η))) →
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γb η) M₁ (fun η => .comp (C η)) →
    J Θ Δ (fun η => ⟨B η, true⟩ :: Γb η) M₂ (fun η => .comp (C η)) →
    J Θ Δ Γ (.case V M₁ M₂) (fun η => .comp (C η))

def RC_zeroE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (V : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ V (fun _ => .val .zero) → J Θ Δ Γ (absurdE V) (fun η => .comp (C η))

def RC_allI (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (x : LifeVar) (b : Lifetime.Life)
    (M : Expr) (S : RowEnv → VTy) (C : RowEnv → CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ η, Θ.Models η → ∀ s ∈ Γ η, s.live = true → ¬ VFree x s.ty) →
    J Θ (Δ.extend x b) (fun η => ⟨S η, false⟩ :: Γ η) M (fun η => .comp (C η)) →
    J Θ Δ Γ (.val (.lam M)) (fun η => .comp (.all x b (C η)))

def RC_allE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (x : LifeVar)
    (b a : Lifetime.Life) (C : RowEnv → CTy),
    J Θ Δ Γ M (fun η => .comp (.all x b (C η))) → Δ.EntailsLt a b →
    J Θ Δ Γ (.app M (.val .unit)) (fun η => .comp ((C η).instLife x a))

def RC_bangThunkF (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (M : Expr) (A : RowEnv → VTy),
    (∀ η, Θ.Models η → Persistent (Γ η)) →
    J Θ Δ (fun η => ⟨.unit, false⟩ :: Γ η) M (fun η => .comp (.ret (A η))) →
    J Θ Δ Γ (.val (.lam M)) (fun η => .val (.bang (.thunk (.ret (A η)))))

def RC_bangThunkV (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (N : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → Persistent (Γ η)) → (∀ η, Θ.Models η → (C η).isRet = false) →
    J Θ Δ Γ (.val (.lam N)) (fun η => .comp (C η)) →
    J Θ Δ Γ (.val (.lam N)) (fun η => .val (.bang (.thunk (C η))))

def RC_bangE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.bang (A η))) → J Θ Δ Γ e (fun η => .val (A η))

def RC_boxI (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (a : Lifetime.Life)
    (A : RowEnv → VTy),
    (∀ η, Θ.Models η → CtxOutlivesJ J.out Δ (Γ η) a) →
    J Θ Δ Γ e (fun η => .val (A η)) → J Θ Δ Γ e (fun η => .val (.box a (A η)))

def RC_boxE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (a : Lifetime.Life)
    (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.box a (A η))) → J Θ Δ Γ e (fun η => .val (A η))

def RC_immSub (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (a b : Lifetime.Life)
    (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.imm b (A η))) → Δ.EntailsLe a b →
    J Θ Δ Γ e (fun η => .val (.imm a (A η)))

def RC_mutSub (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (a b : Lifetime.Life)
    (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.mut b (A η))) → Δ.EntailsLe a b →
    J Θ Δ Γ e (fun η => .val (.mut a (A η)))

def RC_sliceBorrowM (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    J Θ Δ Γ withbor (fun η => .val (sliceBorrowMTy x Δ.meetOfDom (A η) (B η)))

def RC_sliceBorrowI (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → (∀ η, Θ.Models η → VScoped Δ (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    J Θ Δ Γ withbor (fun η => .val (sliceBorrowITy x Δ.meetOfDom (A η) (B η)))

def RC_withbor2 (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → Δ.find? x = none →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    J Θ Δ Γ withbor (fun η => .val (axWithbor2Ty x Δ.meetOfDom (A η) (B η)))

def RC_withbor1U (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (d : Expr)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → Δ.find? x = none →
    (∀ η, Θ.Models η → VScoped Δ (A η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.ref (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor1UTy x Δ.meetOfDom (A η) (B η) (S η)))

def RC_withbor2U (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (d : Expr)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → Δ.find? x = none →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.ref (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor2UTy x Δ.meetOfDom (A η) (B η) (S η)))

def RC_withbor3U (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (a : Lifetime.Life) (A B : RowEnv → VTy)
    (d : Expr) (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → Δ.find? x = none →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.mut a (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor3UTy a x Δ.meetOfDom (A η) (B η) (S η)))

def RC_withloadU (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (a : Lifetime.Life) (A B : RowEnv → VTy)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → Δ.find? x = none →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) →
    J Θ Δ Γ withload (fun η => .val (withloadUTy a x Δ.meetOfDom (A η) (B η) (S η)))

def RC_sliceBorrowMU (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (d : Expr)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.array (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (sliceBorrowMUTy x Δ.meetOfDom (A η) (B η) (S η)))

def RC_sliceBorrowIU (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (d : Expr)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → (∀ η, Θ.Models η → VScoped Δ (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) →
    (∀ η, Θ.Models η → ∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) →
    (∀ η, Θ.Models η → ¬ VFree x (A η)) → (∀ η, Θ.Models η → ¬ VFree x (B η)) →
    (∀ η, Θ.Models η → Row.UnwindJ J.out x (S η)) → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.array (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (sliceBorrowIUTy x Δ.meetOfDom (A η) (B η) (S η)))

def RC_lolliE (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (f a : Expr) (A B : RowEnv → VTy),
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    J Θ Δ Γ₁ a (fun η => .val (A η)) → J Θ Δ Γ₂ f (fun η => .val (.lolli (A η) (B η))) →
    J Θ Δ Γ (.app f a) (fun η => .val (B η))

def RC_allEV (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (x : LifeVar)
    (b a : Lifetime.Life) (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.all x b (A η))) → Δ.EntailsLt a b →
    J Θ Δ Γ (.app e (.val .unit)) (fun η => .val ((A η).instLife x a))

def RC_ofRet (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .comp (.ret (A η))) → J Θ Δ Γ e (fun η => .val (A η))

def RC_roll (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A : RowEnv → VTy),
    (∀ η, Θ.Models η → (A η).NoMut 0) → (∀ η, Θ.Models η → (VTy.mu (A η)).Cl 0) →
    J Θ Δ Γ e (fun η => .val (VTy.inst (.mu (A η)) (A η))) →
    J Θ Δ Γ e (fun η => .val (.mu (A η)))

def RC_unroll (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (A : RowEnv → VTy),
    J Θ Δ Γ e (fun η => .val (.mu (A η))) →
    J Θ Δ Γ e (fun η => .val (VTy.inst (.mu (A η)) (A η)))

def RC_foldImm (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (F : FShape) (y : LifeVar)
    (c : Lifetime.Life) (R : RowEnv → VTy),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η)) → F.WF → F.Guarded → ¬ VFree y (.mu F.ty) →
    (∀ η, Θ.Models η → ¬ VFree y (R η)) →
    (∀ η, Θ.Models η → ∀ Δ' a, J.out.lt Δ' a (R η)) →
    J Θ Δ Γ (.val (foldImmV F)) (fun η => .val (.lolli (algTy F y (R η)) (foldTy F y c (R η))))

def RC_nuIn (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → (C η).NuOk) → J Θ Δ Γ e (fun η => .comp (C η).unroll) →
    J Θ Δ Γ e (fun η => .comp (.nu (C η)))

def RC_nuOut (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (C : RowEnv → CTy),
    (∀ η, Θ.Models η → (C η).NuOk) → J Θ Δ Γ e (fun η => .comp (.nu (C η))) →
    J Θ Δ Γ e (fun η => .comp (C η).unroll)

def RC_effSub (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (e : Expr) (S S' : RowEnv → Row)
    (A : RowEnv → VTy),
    (∀ η, Θ.Models η → R (S' η)) → (∀ η, Θ.Models η → RowLe (S η) (S' η)) →
    J Θ Δ Γ e (fun η => .comp (CTy.effOf (S η) (A η))) →
    J Θ Δ Γ e (fun η => .comp (CTy.effOf (S' η) (A η)))

def RC_effPerform (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (V : Expr) (S : RowEnv → Row) (o : OpSig),
    (∀ η, Θ.Models η → R (S η)) → (∀ η, Θ.Models η → Row.find (S η) o.n o.i = some o) →
    o.abort = false → J Θ Δ Γ V (fun _ => .val o.A) →
    J Θ Δ Γ (performE (opArgE o.n o.i V)) (fun η => .comp (CTy.effOf (S η) o.B))

def RC_effRaise (J : TypingJ) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (V : Expr) (S : RowEnv → Row) (o : OpSig)
    (B : RowEnv → VTy),
    (∀ η, Θ.Models η → Row.find (S η) o.n o.i = some o) → o.abort = true → o.A.Drop →
    J Θ Δ Γ V (fun _ => .val o.A) →
    J Θ Δ Γ (raiseE (opArgE o.n o.i V)) (fun η => .comp (CTy.effOf (S η) (B η)))

def RC_effLet (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (M N : Expr) (A B : RowEnv → VTy)
    (S : RowEnv → Row),
    (∀ η, Θ.Models η → R (S η)) →
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    (∀ η, Θ.Models η → (S η).Weak → (Γ₂ η).Drops) →
    (∀ η, Θ.Models η → (S η).Unr → Persistent (Γ₂ η)) →
    J Θ Δ Γ₁ M (fun η => .comp (CTy.effOf (S η) (A η))) →
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γ₂ η) N (fun η => .comp (CTy.effOf (S η) (B η))) →
    J Θ Δ Γ (.app (.val (.lam N)) M) (fun η => .comp (CTy.effOf (S η) (B η)))

def RC_effThen (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ : RowEnv → Ctx VTy) (M N D : Expr) (A B : RowEnv → VTy)
    (S : RowEnv → Row),
    (∀ η, Θ.Models η → R (S η)) →
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η)) →
    (∀ η, Θ.Models η → (S η).NZ) → (∀ η, Θ.Models η → (S η).Uniq) →
    (∀ η, Θ.Models η → (S η).UnrD → Persistent (Γ₂ η)) →
    J Θ Δ Γ₁ M (fun η => .comp (CTy.effOf (S η) (A η))) →
    J Θ Δ (fun η => ⟨A η, true⟩ :: Γ₂ η) N (fun η => .comp (CTy.effOf (S η) (B η))) →
    J Θ Δ (fun η => ⟨.unit, false⟩ :: Γ₂ η) D (fun _ => .comp (.ret .unit)) →
    J Θ Δ Γ (thenE N D M) (fun η => .comp (CTy.effOf (S η) (B η)))

def RC_effHandle (J : TypingJ) (R : Row → Prop) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ Γ₁ Γ₂ Γr Γc : RowEnv → Ctx VTy) (e : Expr) (S : RowEnv → Row)
    (E : RowEnv → List (Qual × VTy × VTy)) (qs : List Qual) (n : UInt32) (A R' : RowEnv → VTy)
    (ir ic : Nat),
    (∀ η, Θ.Models η → (E η).map Prod.fst = qs) →
    (∀ η, Θ.Models η → R (Row.ofEff n (E η) 0 ++ S η)) →
    (∀ η, Θ.Models η → Ctx.SplitP (Γ η) (Γ₁ η) (Γ₂ η) ∧ Ctx.SplitP (Γ₁ η) (Γr η) (Γc η) ∧
      Ctx.SoloP (Γr η) ir (retTy (S η) (A η) (R' η)) ∧
      Ctx.SoloP (Γc η) ic (clausesTy (S η) (R' η) (E η)) ∧
      (∀ o ∈ S η, o.n ≠ n) ∧ (E η).length ≤ 2 ^ 32) →
    n ≠ 0 →
    J Θ Δ Γ₂ e (fun η => .comp (CTy.effOf (Row.ofEff n (E η) 0 ++ S η) (A η))) →
    J Θ Δ Γ (hndTerm n qs ir ic e) (fun η => .comp (CTy.effOf (S η) (R' η)))

/-- `J` is closed under every rule of `CDerives` that has a derivation premise or reads an outlives
judgment, the five effect rules `CDerivesNU` restricts asked their row predicate `R` (`Row.NU` for
the end state, `fun _ => True` for the full rule set). -/
def RulesClosed (J : TypingJ) (R : Row → Prop) : Prop :=
  RC_tensorI J ∧ RC_sumI₁ J ∧ RC_sumI₂ J ∧ RC_thunkF J ∧ RC_thunkV J ∧ RC_ret J ∧ RC_bind J ∧
  RC_lam J ∧ RC_app J ∧ RC_withI J ∧ RC_proj₁ J ∧ RC_proj₂ J ∧ RC_unitE J ∧ RC_tensorE J ∧
  RC_sumE J ∧ RC_zeroE J ∧ RC_allI J ∧ RC_allE J ∧ RC_bangThunkF J ∧ RC_bangThunkV J ∧
  RC_bangE J ∧ RC_boxI J ∧ RC_boxE J ∧ RC_immSub J ∧ RC_mutSub J ∧ RC_withbor1U J ∧
  RC_withbor2U J ∧ RC_withbor3U J ∧ RC_sliceBorrowMU J ∧ RC_sliceBorrowIU J ∧ RC_lolliE J ∧
  RC_allEV J ∧ RC_ofRet J ∧ RC_roll J ∧ RC_unroll J ∧ RC_nuIn J ∧ RC_nuOut J ∧ RC_effSub J R ∧
  RC_effPerform J R ∧ RC_effRaise J ∧ RC_effLet J R ∧ RC_effThen J R ∧ RC_effHandle J R ∧
  -- premise-free, with an outlives side condition
  RC_withbor2 J ∧ RC_sliceBorrowM J ∧ RC_sliceBorrowI J ∧ RC_withloadU J ∧ RC_foldImm J

/-- `J` extends Core's typing as a rule system. -/
def Extends (J : TypingJ) : Prop := Tier1Sub J ∧ RulesClosed J (fun _ => True)

/-- **The end state's pin**: `J` extends Core's unr-free rules and is closed under them. -/
def ExtendsNU (J : TypingJ) : Prop := Tier1SubNU J ∧ RulesClosed J Row.NU


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem rc_tensorI_tier1 : RC_tensorI tier1 :=
  fun _ _ _ _ _ _ _ _ _ hs h₁ h₂ η hη => CDerives.tensorI (hs η hη) (h₁ η hη) (h₂ η hη)

theorem rc_sumI₁_tier1 : RC_sumI₁ tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.sumI₁ (h η hη)

theorem rc_sumI₂_tier1 : RC_sumI₂ tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.sumI₂ (h η hη)

theorem rc_thunkF_tier1 : RC_thunkF tier1 :=
  fun _ _ _ _ _ h η hη => CDerives.thunkF (h η hη)

theorem rc_thunkV_tier1 : RC_thunkV tier1 :=
  fun _ _ _ _ _ hC h η hη => CDerives.thunkV (hC η hη) (h η hη)

theorem rc_ret_tier1 : RC_ret tier1 :=
  fun _ _ _ _ _ h η hη => CDerives.ret (h η hη)

theorem rc_bind_tier1 : RC_bind tier1 :=
  fun _ _ _ _ _ _ _ _ _ hs hM hN η hη => CDerives.bind (hs η hη) (hM η hη) (hN η hη)

theorem rc_lam_tier1 : RC_lam tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.lam (h η hη)

theorem rc_app_tier1 : RC_app tier1 :=
  fun _ _ _ _ _ _ _ _ _ hs hM hx η hη => CDerives.app (hs η hη) (hM η hη) (hx η hη)

theorem rc_withI_tier1 : RC_withI tier1 :=
  fun _ _ _ _ _ _ _ hM hN η hη => CDerives.withI (hM η hη) (hN η hη)

theorem rc_proj₁_tier1 : RC_proj₁ tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.proj₁ (h η hη)

theorem rc_proj₂_tier1 : RC_proj₂ tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.proj₂ (h η hη)

theorem rc_unitE_tier1 : RC_unitE tier1 :=
  fun _ _ _ _ _ _ _ _ hs hV hM η hη => CDerives.unitE (hs η hη) (hV η hη) (hM η hη)

theorem rc_tensorE_tier1 : RC_tensorE tier1 :=
  fun _ _ _ _ _ _ _ _ _ _ hs hV hM η hη => CDerives.tensorE (hs η hη) (hV η hη) (hM η hη)

theorem rc_sumE_tier1 : RC_sumE tier1 :=
  fun _ _ _ _ _ _ _ _ _ _ _ hs hV h₁ h₂ η hη => CDerives.sumE (hs η hη) (hV η hη) (h₁ η hη) (h₂ η hη)

theorem rc_zeroE_tier1 : RC_zeroE tier1 :=
  fun _ _ _ _ _ _ _ hs hV η hη => CDerives.zeroE (hs η hη) (hV η hη)

theorem rc_allI_tier1 : RC_allI tier1 :=
  fun _ _ _ _ _ _ _ _ hbx hΔx hΓx h η hη => CDerives.allI hbx hΔx (hΓx η hη) (h η hη)

theorem rc_allE_tier1 : RC_allE tier1 :=
  fun _ _ _ _ _ _ _ _ h hlt η hη => CDerives.allE (h η hη) hlt

theorem rc_bangThunkF_tier1 : RC_bangThunkF tier1 :=
  fun _ _ _ _ _ hp h η hη => CDerives.bangThunkF (hp η hη) (h η hη)

theorem rc_bangThunkV_tier1 : RC_bangThunkV tier1 :=
  fun _ _ _ _ _ hp hC h η hη => CDerives.bangThunkV (hp η hη) (hC η hη) (h η hη)

theorem rc_bangE_tier1 : RC_bangE tier1 :=
  fun _ _ _ _ _ h η hη => CDerives.bangE (h η hη)

theorem rc_boxI_tier1 : RC_boxI tier1 :=
  fun _ _ _ _ _ _ hΓ h η hη => CDerives.boxI (h η hη) (hΓ η hη)

theorem rc_boxE_tier1 : RC_boxE tier1 :=
  fun _ _ _ _ _ _ h η hη => CDerives.boxE (h η hη)

theorem rc_immSub_tier1 : RC_immSub tier1 :=
  fun _ _ _ _ _ _ _ h hle η hη => CDerives.immSub (h η hη) hle

theorem rc_mutSub_tier1 : RC_mutSub tier1 :=
  fun _ _ _ _ _ _ _ h hle η hη => CDerives.mutSub (h η hη) hle

theorem rc_withbor1U_tier1 : RC_withbor1U tier1 :=
  fun _ _ _ _ _ _ _ x hΓ hx hsc hf₁ hf₂ hS hdc hd η hη => CDerives.withbor1U x (hΓ η hη) hx (hsc η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_withbor2U_tier1 : RC_withbor2U tier1 :=
  fun _ _ _ _ _ _ _ x hΓ hx hside hf₁ hf₂ hS hdc hd η hη => CDerives.withbor2U x (hΓ η hη) hx (hside η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_withbor3U_tier1 : RC_withbor3U tier1 :=
  fun _ _ _ _ _ _ _ _ x hΓ hx hf₁ hf₂ hS hdc hd η hη => CDerives.withbor3U x (hΓ η hη) hx (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_sliceBorrowMU_tier1 : RC_sliceBorrowMU tier1 :=
  fun _ _ _ _ _ _ _ x hΓ hA hB hf₁ hf₂ hS hdc hd η hη => CDerives.sliceBorrowMU x (hΓ η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_sliceBorrowIU_tier1 : RC_sliceBorrowIU tier1 :=
  fun _ _ _ _ _ _ _ x hΓ hsc hA hB hf₁ hf₂ hS hdc hd η hη => CDerives.sliceBorrowIU x (hΓ η hη) (hsc η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_lolliE_tier1 : RC_lolliE tier1 :=
  fun _ _ _ _ _ _ _ _ _ hs ha hf η hη => CDerives.lolliE (hs η hη) (ha η hη) (hf η hη)

theorem rc_allEV_tier1 : RC_allEV tier1 :=
  fun _ _ _ _ _ _ _ _ h hlt η hη => CDerives.allEV (h η hη) hlt

theorem rc_ofRet_tier1 : RC_ofRet tier1 :=
  fun _ _ _ _ _ h η hη => CDerives.ofRet (h η hη)

theorem rc_roll_tier1 : RC_roll tier1 :=
  fun _ _ _ _ _ hA hc h η hη => CDerives.roll (hA η hη) (hc η hη) (h η hη)

theorem rc_unroll_tier1 : RC_unroll tier1 :=
  fun _ _ _ _ _ h η hη => CDerives.unroll (h η hη)

theorem rc_nuIn_tier1 : RC_nuIn tier1 :=
  fun _ _ _ _ _ hC h η hη => CDerives.nuIn (hC η hη) (h η hη)

theorem rc_nuOut_tier1 : RC_nuOut tier1 :=
  fun _ _ _ _ _ hC h η hη => CDerives.nuOut (hC η hη) (h η hη)

theorem rc_effSub_tier1 (R : Row → Prop) : RC_effSub tier1 R :=
  fun _ _ _ _ _ _ _ _ hle h η hη => CDerives.effSub (hle η hη) (h η hη)

theorem rc_effPerform_tier1 (R : Row → Prop) : RC_effPerform tier1 R :=
  fun _ _ _ _ _ _ _ hf hna h η hη => CDerives.effPerform (hf η hη) hna (h η hη)

theorem rc_effRaise_tier1 : RC_effRaise tier1 :=
  fun _ _ _ _ _ _ _ hf ha hd h η hη => CDerives.effRaise (hf η hη) ha hd (h η hη)

theorem rc_effLet_tier1 (R : Row → Prop) : RC_effLet tier1 R :=
  fun _ _ _ _ _ _ _ _ _ _ _ hs hW hU hM hN η hη => CDerives.effLet (hs η hη) (hW η hη) (hU η hη) (hM η hη) (hN η hη)

theorem rc_effThen_tier1 (R : Row → Prop) : RC_effThen tier1 R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hs hNZ hUq hU hM hN hD η hη => CDerives.effThenA (hs η hη) (hNZ η hη) (hUq η hη) (hU η hη) (hM η hη) (hN η hη) (hD η hη)

theorem rc_effHandle_tier1 (R : Row → Prop) : RC_effHandle tier1 R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hqs _ hside hn0 he η hη =>
    match hside η hη with
    | ⟨hs, hs₁, hr, hc, hnS, hlen⟩ =>
        hqs η hη ▸ CDerives.effHandle hs hs₁ hr hc hn0 hnS hlen (he η hη)

theorem rc_withbor2_tier1 : RC_withbor2 tier1 :=
  fun _ _ _ _ _ x hΓ hx hside hf₁ hf₂ η hη => CDerives.withbor2 x (hΓ η hη) hx (hside η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_sliceBorrowM_tier1 : RC_sliceBorrowM tier1 :=
  fun _ _ _ _ _ x hΓ hA hB hf₁ hf₂ η hη => CDerives.sliceBorrowM x (hΓ η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_sliceBorrowI_tier1 : RC_sliceBorrowI tier1 :=
  fun _ _ _ _ _ x hΓ hsc hA hB hf₁ hf₂ η hη => CDerives.sliceBorrowI x (hΓ η hη) (hsc η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_withloadU_tier1 : RC_withloadU tier1 :=
  fun _ _ _ _ _ _ _ x hΓ hx hf₁ hf₂ hS η hη => CDerives.withloadU x (hΓ η hη) hx (hf₁ η hη) (hf₂ η hη) (hS η hη)

theorem rc_foldImm_tier1 : RC_foldImm tier1 :=
  fun _ _ _ F y c R hΓ hF hG hyM hyR hR η hη => CDerives.foldImm F y c (R η) (hΓ η hη) hF hG hyM (hyR η hη) (hR η hη)

theorem rc_tensorI_tier1NU : RC_tensorI tier1NU :=
  fun _ _ _ _ _ _ _ _ _ hs h₁ h₂ η hη => CDerivesNU.tensorI (hs η hη) (h₁ η hη) (h₂ η hη)

theorem rc_sumI₁_tier1NU : RC_sumI₁ tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.sumI₁ (h η hη)

theorem rc_sumI₂_tier1NU : RC_sumI₂ tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.sumI₂ (h η hη)

theorem rc_thunkF_tier1NU : RC_thunkF tier1NU :=
  fun _ _ _ _ _ h η hη => CDerivesNU.thunkF (h η hη)

theorem rc_thunkV_tier1NU : RC_thunkV tier1NU :=
  fun _ _ _ _ _ hC h η hη => CDerivesNU.thunkV (hC η hη) (h η hη)

theorem rc_ret_tier1NU : RC_ret tier1NU :=
  fun _ _ _ _ _ h η hη => CDerivesNU.ret (h η hη)

theorem rc_bind_tier1NU : RC_bind tier1NU :=
  fun _ _ _ _ _ _ _ _ _ hs hM hN η hη => CDerivesNU.bind (hs η hη) (hM η hη) (hN η hη)

theorem rc_lam_tier1NU : RC_lam tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.lam (h η hη)

theorem rc_app_tier1NU : RC_app tier1NU :=
  fun _ _ _ _ _ _ _ _ _ hs hM hx η hη => CDerivesNU.app (hs η hη) (hM η hη) (hx η hη)

theorem rc_withI_tier1NU : RC_withI tier1NU :=
  fun _ _ _ _ _ _ _ hM hN η hη => CDerivesNU.withI (hM η hη) (hN η hη)

theorem rc_proj₁_tier1NU : RC_proj₁ tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.proj₁ (h η hη)

theorem rc_proj₂_tier1NU : RC_proj₂ tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.proj₂ (h η hη)

theorem rc_unitE_tier1NU : RC_unitE tier1NU :=
  fun _ _ _ _ _ _ _ _ hs hV hM η hη => CDerivesNU.unitE (hs η hη) (hV η hη) (hM η hη)

theorem rc_tensorE_tier1NU : RC_tensorE tier1NU :=
  fun _ _ _ _ _ _ _ _ _ _ hs hV hM η hη => CDerivesNU.tensorE (hs η hη) (hV η hη) (hM η hη)

theorem rc_sumE_tier1NU : RC_sumE tier1NU :=
  fun _ _ _ _ _ _ _ _ _ _ _ hs hV h₁ h₂ η hη => CDerivesNU.sumE (hs η hη) (hV η hη) (h₁ η hη) (h₂ η hη)

theorem rc_zeroE_tier1NU : RC_zeroE tier1NU :=
  fun _ _ _ _ _ _ _ hs hV η hη => CDerivesNU.zeroE (hs η hη) (hV η hη)

theorem rc_allI_tier1NU : RC_allI tier1NU :=
  fun _ _ _ _ _ _ _ _ hbx hΔx hΓx h η hη => CDerivesNU.allI hbx hΔx (hΓx η hη) (h η hη)

theorem rc_allE_tier1NU : RC_allE tier1NU :=
  fun _ _ _ _ _ _ _ _ h hlt η hη => CDerivesNU.allE (h η hη) hlt

theorem rc_bangThunkF_tier1NU : RC_bangThunkF tier1NU :=
  fun _ _ _ _ _ hp h η hη => CDerivesNU.bangThunkF (hp η hη) (h η hη)

theorem rc_bangThunkV_tier1NU : RC_bangThunkV tier1NU :=
  fun _ _ _ _ _ hp hC h η hη => CDerivesNU.bangThunkV (hp η hη) (hC η hη) (h η hη)

theorem rc_bangE_tier1NU : RC_bangE tier1NU :=
  fun _ _ _ _ _ h η hη => CDerivesNU.bangE (h η hη)

theorem rc_boxI_tier1NU : RC_boxI tier1NU :=
  fun _ _ _ _ _ _ hΓ h η hη => CDerivesNU.boxI (h η hη) (hΓ η hη)

theorem rc_boxE_tier1NU : RC_boxE tier1NU :=
  fun _ _ _ _ _ _ h η hη => CDerivesNU.boxE (h η hη)

theorem rc_immSub_tier1NU : RC_immSub tier1NU :=
  fun _ _ _ _ _ _ _ h hle η hη => CDerivesNU.immSub (h η hη) hle

theorem rc_mutSub_tier1NU : RC_mutSub tier1NU :=
  fun _ _ _ _ _ _ _ h hle η hη => CDerivesNU.mutSub (h η hη) hle

theorem rc_withbor1U_tier1NU : RC_withbor1U tier1NU :=
  fun _ _ _ _ _ _ _ x hΓ hx hsc hf₁ hf₂ hS hdc hd η hη => CDerivesNU.withbor1U x (hΓ η hη) hx (hsc η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_withbor2U_tier1NU : RC_withbor2U tier1NU :=
  fun _ _ _ _ _ _ _ x hΓ hx hside hf₁ hf₂ hS hdc hd η hη => CDerivesNU.withbor2U x (hΓ η hη) hx (hside η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_withbor3U_tier1NU : RC_withbor3U tier1NU :=
  fun _ _ _ _ _ _ _ _ x hΓ hx hf₁ hf₂ hS hdc hd η hη => CDerivesNU.withbor3U x (hΓ η hη) hx (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_sliceBorrowMU_tier1NU : RC_sliceBorrowMU tier1NU :=
  fun _ _ _ _ _ _ _ x hΓ hA hB hf₁ hf₂ hS hdc hd η hη => CDerivesNU.sliceBorrowMU x (hΓ η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_sliceBorrowIU_tier1NU : RC_sliceBorrowIU tier1NU :=
  fun _ _ _ _ _ _ _ x hΓ hsc hA hB hf₁ hf₂ hS hdc hd η hη => CDerivesNU.sliceBorrowIU x (hΓ η hη) (hsc η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη) (hS η hη) hdc (hd η hη)

theorem rc_lolliE_tier1NU : RC_lolliE tier1NU :=
  fun _ _ _ _ _ _ _ _ _ hs ha hf η hη => CDerivesNU.lolliE (hs η hη) (ha η hη) (hf η hη)

theorem rc_allEV_tier1NU : RC_allEV tier1NU :=
  fun _ _ _ _ _ _ _ _ h hlt η hη => CDerivesNU.allEV (h η hη) hlt

theorem rc_ofRet_tier1NU : RC_ofRet tier1NU :=
  fun _ _ _ _ _ h η hη => CDerivesNU.ofRet (h η hη)

theorem rc_roll_tier1NU : RC_roll tier1NU :=
  fun _ _ _ _ _ hA hc h η hη => CDerivesNU.roll (hA η hη) (hc η hη) (h η hη)

theorem rc_unroll_tier1NU : RC_unroll tier1NU :=
  fun _ _ _ _ _ h η hη => CDerivesNU.unroll (h η hη)

theorem rc_nuIn_tier1NU : RC_nuIn tier1NU :=
  fun _ _ _ _ _ hC h η hη => CDerivesNU.nuIn (hC η hη) (h η hη)

theorem rc_nuOut_tier1NU : RC_nuOut tier1NU :=
  fun _ _ _ _ _ hC h η hη => CDerivesNU.nuOut (hC η hη) (h η hη)

theorem rc_effSub_tier1NU : RC_effSub tier1NU Row.NU :=
  fun _ _ _ _ _ _ _ hR hle h η hη => CDerivesNU.effSub (hR η hη) (hle η hη) (h η hη)

theorem rc_effPerform_tier1NU : RC_effPerform tier1NU Row.NU :=
  fun _ _ _ _ _ _ hR hf hna h η hη => CDerivesNU.effPerform (hR η hη) (hf η hη) hna (h η hη)

theorem rc_effRaise_tier1NU : RC_effRaise tier1NU :=
  fun _ _ _ _ _ _ _ hf ha hd h η hη => CDerivesNU.effRaise (hf η hη) ha hd (h η hη)

theorem rc_effLet_tier1NU : RC_effLet tier1NU Row.NU :=
  fun _ _ _ _ _ _ _ _ _ _ hR hs hW hU hM hN η hη => CDerivesNU.effLet (hR η hη) (hs η hη) (hW η hη) (hU η hη) (hM η hη) (hN η hη)

theorem rc_effThen_tier1NU : RC_effThen tier1NU Row.NU :=
  fun _ _ _ _ _ _ _ _ _ _ _ hR hs hNZ hUq hU hM hN hD η hη => CDerivesNU.effThen (hR η hη) (hs η hη) (hNZ η hη) (hUq η hη) (hU η hη) (hM η hη) (hN η hη) (hD η hη)

theorem rc_effHandle_tier1NU : RC_effHandle tier1NU Row.NU :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hqs hR hside hn0 he η hη =>
    match hside η hη with
    | ⟨hs, hs₁, hr, hc, hnS, hlen⟩ =>
        hqs η hη ▸ CDerivesNU.effHandle (hR η hη) hs hs₁ hr hc hn0 hnS hlen (he η hη)

theorem rc_withbor2_tier1NU : RC_withbor2 tier1NU :=
  fun _ _ _ _ _ x hΓ hx hside hf₁ hf₂ η hη => CDerivesNU.withbor2 x (hΓ η hη) hx (hside η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_sliceBorrowM_tier1NU : RC_sliceBorrowM tier1NU :=
  fun _ _ _ _ _ x hΓ hA hB hf₁ hf₂ η hη => CDerivesNU.sliceBorrowM x (hΓ η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_sliceBorrowI_tier1NU : RC_sliceBorrowI tier1NU :=
  fun _ _ _ _ _ x hΓ hsc hA hB hf₁ hf₂ η hη => CDerivesNU.sliceBorrowI x (hΓ η hη) (hsc η hη) (hA η hη) (hB η hη) (hf₁ η hη) (hf₂ η hη)

theorem rc_withloadU_tier1NU : RC_withloadU tier1NU :=
  fun _ _ _ _ _ _ _ x hΓ hx hf₁ hf₂ hS η hη => CDerivesNU.withloadU x (hΓ η hη) hx (hf₁ η hη) (hf₂ η hη) (hS η hη)

theorem rc_foldImm_tier1NU : RC_foldImm tier1NU :=
  fun _ _ _ F y c R hΓ hF hG hyM hyR hR η hη => CDerivesNU.foldImm F y c (R η) (hΓ η hη) hF hG hyM (hyR η hη) (hR η hη)

/-- `tier1` is closed under every rule, at every row predicate. -/
theorem rulesClosed_tier1 (R : Row → Prop) : RulesClosed tier1 R :=
  ⟨rc_tensorI_tier1,
    rc_sumI₁_tier1,
    rc_sumI₂_tier1,
    rc_thunkF_tier1,
    rc_thunkV_tier1,
    rc_ret_tier1,
    rc_bind_tier1,
    rc_lam_tier1,
    rc_app_tier1,
    rc_withI_tier1,
    rc_proj₁_tier1,
    rc_proj₂_tier1,
    rc_unitE_tier1,
    rc_tensorE_tier1,
    rc_sumE_tier1,
    rc_zeroE_tier1,
    rc_allI_tier1,
    rc_allE_tier1,
    rc_bangThunkF_tier1,
    rc_bangThunkV_tier1,
    rc_bangE_tier1,
    rc_boxI_tier1,
    rc_boxE_tier1,
    rc_immSub_tier1,
    rc_mutSub_tier1,
    rc_withbor1U_tier1,
    rc_withbor2U_tier1,
    rc_withbor3U_tier1,
    rc_sliceBorrowMU_tier1,
    rc_sliceBorrowIU_tier1,
    rc_lolliE_tier1,
    rc_allEV_tier1,
    rc_ofRet_tier1,
    rc_roll_tier1,
    rc_unroll_tier1,
    rc_nuIn_tier1,
    rc_nuOut_tier1,
    rc_effSub_tier1 R,
    rc_effPerform_tier1 R,
    rc_effRaise_tier1,
    rc_effLet_tier1 R,
    rc_effThen_tier1 R,
    rc_effHandle_tier1 R,
    rc_withbor2_tier1,
    rc_sliceBorrowM_tier1,
    rc_sliceBorrowI_tier1,
    rc_withloadU_tier1,
    rc_foldImm_tier1⟩

/-- `tier1NU` is closed under every rule at unr-free rows. -/
theorem rulesClosed_tier1NU : RulesClosed tier1NU Row.NU :=
  ⟨rc_tensorI_tier1NU,
    rc_sumI₁_tier1NU,
    rc_sumI₂_tier1NU,
    rc_thunkF_tier1NU,
    rc_thunkV_tier1NU,
    rc_ret_tier1NU,
    rc_bind_tier1NU,
    rc_lam_tier1NU,
    rc_app_tier1NU,
    rc_withI_tier1NU,
    rc_proj₁_tier1NU,
    rc_proj₂_tier1NU,
    rc_unitE_tier1NU,
    rc_tensorE_tier1NU,
    rc_sumE_tier1NU,
    rc_zeroE_tier1NU,
    rc_allI_tier1NU,
    rc_allE_tier1NU,
    rc_bangThunkF_tier1NU,
    rc_bangThunkV_tier1NU,
    rc_bangE_tier1NU,
    rc_boxI_tier1NU,
    rc_boxE_tier1NU,
    rc_immSub_tier1NU,
    rc_mutSub_tier1NU,
    rc_withbor1U_tier1NU,
    rc_withbor2U_tier1NU,
    rc_withbor3U_tier1NU,
    rc_sliceBorrowMU_tier1NU,
    rc_sliceBorrowIU_tier1NU,
    rc_lolliE_tier1NU,
    rc_allEV_tier1NU,
    rc_ofRet_tier1NU,
    rc_roll_tier1NU,
    rc_unroll_tier1NU,
    rc_nuIn_tier1NU,
    rc_nuOut_tier1NU,
    rc_effSub_tier1NU,
    rc_effPerform_tier1NU,
    rc_effRaise_tier1NU,
    rc_effLet_tier1NU,
    rc_effThen_tier1NU,
    rc_effHandle_tier1NU,
    rc_withbor2_tier1NU,
    rc_sliceBorrowM_tier1NU,
    rc_sliceBorrowI_tier1NU,
    rc_withloadU_tier1NU,
    rc_foldImm_tier1NU⟩

/-- Tier 1 holds tier 1. -/
theorem tier1Sub_tier1 : Tier1Sub tier1 := fun _ _ _ _ _ h => h

/-- Tier 1 holds its unr-free fragment. -/
theorem tier1SubNU_tier1 : Tier1SubNU tier1 := fun _ _ _ _ _ h η hη => (h η hη).toCDerives

/-- **`Extends tier1`.** -/
theorem extends_tier1 : Extends tier1 := ⟨tier1Sub_tier1, rulesClosed_tier1 _⟩

/-- **`ExtendsNU tier1`.** -/
theorem extendsNU_tier1 : ExtendsNU tier1 := ⟨tier1SubNU_tier1, rulesClosed_tier1 _⟩

/-- **`ExtendsNU tier1NU`**: the unr-free fragment meets the end state's typing pin. -/
theorem extendsNU_tier1NU : ExtendsNU tier1NU := ⟨fun _ _ _ _ _ h => h, rulesClosed_tier1NU⟩

/-- **`OutExtends OutJ.core`.** -/
theorem outExtends_core : OutExtends OutJ.core :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => VOutlives.toLe h⟩

end Targets

end
