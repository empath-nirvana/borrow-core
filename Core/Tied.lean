import Core.Fundamental

/-!
# Core — decision R: a derivation tied to its program's effect context  `[spec §19]`

An **effect context** `Ξ` gives each operation name its signature: the `i`-th operation of the
name `n` is `(Ξ n)[i] = (q, A, B)`.  A row is **tied** to `Ξ` (`RowAt`) when every operation it
finds is of a nonzero name with at most `2³²` operations, at the signature `Ξ` gives it.

**`CDerivesAt Ξ`** is `CDerives` with the premise `RowAt Ξ` at the three rules that read an
operation's signature off a row: `[perform]` and `[raise]` (the row the operation is found in) and
`[handle]` (the handled row `(n)↑E ⊙ Σ`, whose qualifiers are the handler value's tags, §25).
Every other rule is `CDerives`'s verbatim, `[then]` with its finaliser's row and the cancel rows of
§27 among them; the tie reads no cancel row (`rowAt_ofEff_fs`).  So a name has one signature across
a derivation: every instance of a handler site has one protocol (§19 *Names*).

* `CDerivesAt.toCDerives`: a tied derivation is one of `CDerives`, so `fundamentalC` and the
  adequacy theorems hold of it.
* `CDerivesAt.ofEffFree`: a derivation of a term holding no `perform`, `raise` or `hnd`
  (`Expr.effFree`) is tied at every effect context.
* `CDerivesAt.effThenA`, `CDerivesAt.effHandle`: `CDerives.effThenA` and `CDerives.effHandle`,
  tied.
* At a handler the tie makes its signature `E` a prefix of `Ξ n` (`sig_prefix_of_rowAt`), so the
  handler value's tags are a prefix of `Ξ`'s qualifiers of `n` (`hndTags_of_rowAt`).
* `SigsAt Ξ S`: every entry of the list `S` is at `Ξ`'s signature; it ties every row whose
  entries are among `S`'s (`rowAt_of_sigsAt`).
* `EffCtx.NoUnrExn`: no operation of `Ξ` is unrestricted and answers `0`.  An abortive operation
  is affine (decision 63's restriction, §18); in a row tied to such a context an unrestricted
  operation resumes (`abort_false_of_rowAt`).
-/

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Effect contexts and tied rows -/

/-- An effect context: each name's signature, its operations numbered from `0`.  `[spec §19]` -/
abbrev EffCtx := UInt32 → List (Qual × VTy × VTy)

/-- **A row tied to the effect context**: every operation the row finds is of a nonzero name with
at most `2³²` operations, at the signature `Ξ` gives it.  `[spec §19]` -/
def RowAt (Ξ : EffCtx) (S : Row) : Prop :=
  ∀ n i o, Row.find S n i = some o →
    n ≠ 0 ∧ (Ξ n).length ≤ 2 ^ 32 ∧ (Ξ n)[i.toNat]? = some (o.q, o.A, o.B)

/-- A row tied to an effect context that gives `Div`'s name no operation does not hold `Div`. -/
theorem Row.divB_of_rowAt {Ξ : EffCtx} {S : Row} (hAt : RowAt Ξ S) (hΞ : Ξ divEff = []) :
    Row.divB S = false :=
  Row.divB_false_of_find fun o hf => by
    have := (hAt _ _ o hf).2.2
    rw [hΞ] at this
    simp at this

/-! ### The tied judgment -/

/-- **`CDerives` with its operations' and handlers' rows tied to `Ξ`** (decision R): the
constructors of `CDerives` verbatim, with `RowAt Ξ` at `effPerform` and `effRaise` (on the row
`S`) and at `effHandleV` and `effHandleVB` (on the handled row `Row.ofEff n E 0 fs ++ S`).
`[spec §19, §28]` -/
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
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (.ret A)))
      (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.SoloP Γ i (.thunk C)) :
      CDerivesAt Ξ Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      CDerivesAt Ξ Δ Γ (.val (.lam M)) (.comp (.arr A C))
  /-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B` with `x`'s slot dead, `M` not using it.  `[spec §26]` -/
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
  /-- `iterate` at a row holding `Div`, the row tied to `Ξ`.  `[spec §14]` -/
  | iterate {Δ Γ} (S : Row) (St B R : VTy) (hAt : RowAt Ξ S) (hS : Row.divB S = true)
      (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (.prim .iterate)) (.val (iterTy S St B R))
  /-- `div_fuel`, the handled row tied to `Ξ`.  `[spec §14]` -/
  | divFuel {Δ Γ} (S : Row) (A : VTy) (hAt : RowAt Ξ (tickSig :: S)) (hS : ∀ o ∈ S, o.n ≠ divEff)
      (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val divFuelV) (.val (divFuelTy S A))
  /-- `reify_res`, the handled row tied to `Ξ`.  `[spec §14]` -/
  | reify {Δ Γ} (S : Row) (B R : VTy) (res : Val) (hAt : RowAt Ξ (tickSig :: S))
      (hS : ∀ o ∈ S, o.n ≠ divEff) (hcl : closedAt 0 res.1 = true)
      (hres : CDerivesAt Ξ Δ [] (.val res) (.val (resTy S B R))) (hΓ : Ctx.DeadP Γ) :
      CDerivesAt Ξ Δ Γ (.val (reifyV res)) (.val (reifyTy S B R))
  /-- `slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `mut` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowM {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerivesAt Ξ Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))
  /-- `slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `imm` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowI {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
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
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerivesAt Ξ Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_imm`: an owned array lent as a family of `imm` leaves.
  `[spec §19]` -/
  | sliceBorrowIU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
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
  /-- `[then]`: `M then x. N unwind D`, `M` at `Σ_M ≤ Σ` and the finaliser at `Σ_D ≤ Σ`, each
  capturable operation of `Σ_M` with `Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`: what the finaliser may raise or
  perform when a continuation captured in `M` is cancelled is recorded in that operation's cancel
  row.  `Γ₂` is persistent where `Σ` has an unrestricted operation at some depth of its cancel
  rows (`Row.UnrD`), since the finaliser runs in the cancels below it, and the errors pending at the
  finaliser are persistent where `Σ_D` has one.  `[then]` at option A, the finaliser at `F 1`, is
  `CDerivesAt.effThenA`.  `[spec §19, §24, §27]` -/
  | effThen {Δ Γ Γ₁ Γ₂ M N D A B} {S SM SD : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ)
      (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂) (hMS : RowLe SM S) (hDS : RowLe SD S)
      (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
        capB o.q o.B = true → ThenLe o.fin SD o'.fin)
      (hP : SD.UnrD → SM.PendPers) (hSD : Row.divB SD = false)
      (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (CTy.effOf SM A)))
      (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
      (hD : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
      CDerivesAt Ξ Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
  /-- `[handle]`: `handle_n e with H`, the handler's pair `H = (h_ret, hs)` a value form over a
  part of the context whose live slots are persistent, `n` not in `Σ`, the handled row tied to
  `Ξ`.  The `j`-th operation's cancel row is `fs j`, and its clause's `κ` has its cancel branch at
  `cancelTy Σ (fs j)`.  At two variables and empty cancel rows it is `hndTerm`
  (`CDerivesAt.effHandle`).  `[spec §19, §24, §27]` -/
  | effHandleV {Δ Γ Γ₁ Γ₂ H e} {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {A R : VTy} (hAt : RowAt Ξ (Row.ofEff n E 0 fs ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
      (hc : CDerivesAt Ξ Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
      (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
      CDerivesAt Ξ Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
  /-- BOXED-κ, the handled row tied to `Ξ`.  `[spec §28]` -/
  | effHandleVB {Δ Γ Γ₁ Γ₂ H e} {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {A R : VTy} {d : Lifetime.Life} (hAt : RowAt Ξ (Row.ofEff n E 0 fs ++ S))
      (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
      (hc : CDerivesAt Ξ Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyB S R d E fs))))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
      (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)))
      (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S)) :
      CDerivesAt Ξ Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
  /-- `[handle]` at clauses that resume `κ` in tail position, the handled row tied to `Ξ`.
  `[spec §14, §19]` -/
  | effHandleT {Δ Γ Γ₁ Γ₂} {Hr Hc e : Expr} {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {c : Bool} {A R : VTy} (hAt : RowAt Ξ (Row.ofEff n E 0 fs c ++ S))
      (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
      (hc : CDerivesAt Ξ Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
      (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
      (hCN : c = true → ∀ o ∈ SN, o.call = true)
      (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs c ++ S) A))) :
      CDerivesAt Ξ Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
        (.comp (CTy.effOf S R))
  /-- `[let-poly]`: `let x = λy. b in N` for a closed λ-value, from `N` with the λ-value for `x`,
  `x`'s slot dead.  Each occurrence of the λ-value in `N` is typed on its own, at its own row: the
  kernel's row polymorphism, with the value restriction.  `[spec §24]` -/
  | letPoly {Δ Γ N C} {j : Jdg} (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true)
      (hV : CDerivesAt Ξ Δ [] (.val (.lam b)) j)
      (hN : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 (Val.lam b)).shift 1 0) (.comp C)) :
      CDerivesAt Ξ Δ Γ (.app (.val (.lam N)) (.val (.lam b))) (.comp C)

/-- **Every tied derivation is one of `CDerives`.**  `[spec §19]` -/
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
  | sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂
  | sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂
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
  | withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc ih1
  | withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc ih1
  | withbor3U x hΓ hx hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor3U x hΓ hx hfree₁ hfree₂ hS hdc ih1
  | withloadU x hΓ hx hfree₁ hfree₂ hS => exact .withloadU x hΓ hx hfree₁ hfree₂ hS
  | sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc ih1
  | sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc ih1
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
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ih1 ih2 ih3 =>
      exact .effThen hs hNZ hUq hU hMS hDS hfin hP hSD ih1 ih2 ih3
  | effHandleV _ hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact .effHandleV hs hd hH ihc hn0 hnS hlen hdv ihe
  | effHandleVB _ hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact .effHandleVB hs hd hH ihc hn0 hnS hlen hdv ihe hΓd hSd
  | effHandleT _ hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin hCN _ ihc ihe =>
      exact .effHandleT hs hd hHr hHc ihc hn0 hnd hnS hlen hSN hLin hCN ihe
  | iterate S St B R _ hS hΓ => exact .iterate S St B R hS hΓ
  | divFuel S A _ hS hΓ => exact .divFuel S A hS hΓ
  | reify S B R res _ hS hcl _ hΓ ih => exact .reify S B R res hS hcl ih hΓ
  | letPoly b hcl _ _ ihV ihN => exact .letPoly b hcl ihV ihN

/-- `[then]` with its finaliser at the pure row (§24, option A), tied: `effThen` at `Σ_M = Σ` and
`Σ_D = ∅`, as `CDerives.effThenA`.  `[spec §24, §27]` -/
theorem CDerivesAt.effThenA {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂)
    (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerivesAt Ξ Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  .effThen (SD := []) hs hNZ hUq hU (RowLe.refl S) (RowLe.nil S)
    (fun _ _ o _ hf hf' _ => by rw [hf] at hf'; cases hf'; exact ThenLe.nil o.fin)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) rfl hM hN hD

/-- `[handle]` at two variables, tied: `CDerives.effHandle` with the handled row tied to `Ξ`.
`[spec §19]` -/
theorem CDerivesAt.effHandle {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he

/-- BOXED-κ at two variables, tied: `CDerivesAt.effHandle` with the clauses at `clausesTyB`.
`[spec §28]` -/
theorem CDerivesAt.effHandleB {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat} {d : Lifetime.Life}
    (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTyB S R d E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)))
    (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 ++ S)) :
    CDerivesAt Ξ Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleVB hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R))
      (hc.deadP (clausesTyB_persistent S R d E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he
    hΓd hSd

/-! ### Tied rows -/

theorem rowAt_nil (Ξ : EffCtx) : RowAt Ξ [] := fun _ _ _ h => by simp [Row.find] at h

/-- Two rows tied to `Ξ` append to one. -/
theorem rowAt_append {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ S) (h' : RowAt Ξ S') :
    RowAt Ξ (S ++ S') := by
  intro n i o hf
  rw [Row.find_append] at hf
  cases hS : Row.find S n i with
  | none => rw [hS, Option.none_or] at hf; exact h' n i o hf
  | some o' => rw [hS, Option.some_or] at hf; cases hf; exact h n i o hS

/-- A row below a row tied to `Ξ` is tied to `Ξ`. -/
theorem rowAt_of_le {Ξ : EffCtx} {S S' : Row} (hle : RowLe S S') (h : RowAt Ξ S') :
    RowAt Ξ S := by
  intro n i o hf
  obtain ⟨o', hf', hs⟩ := RowLe.sig hle hf
  obtain ⟨h₁, h₂, h₃⟩ := h n i o' hf'
  exact ⟨h₁, h₂, by rw [hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2]; exact h₃⟩

/-- The front of a row tied to `Ξ` is tied to `Ξ`. -/
theorem rowAt_left {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ (S ++ S')) : RowAt Ξ S :=
  rowAt_of_le (RowLe.of_find fun n i o hf => by rw [Row.find_append, hf, Option.some_or]) h

/-- A name's row at the signature `Ξ` gives it is tied to `Ξ`. -/
theorem ofEff_wf (Ξ : EffCtx) (n : UInt32) (hn : n ≠ 0) (hlen : (Ξ n).length ≤ 2 ^ 32) :
    RowAt Ξ (Row.ofEff n (Ξ n) 0) := by
  intro m i o h
  obtain ⟨rfl, j, hj, rfl, rfl⟩ := Row.find_ofEff n (Ξ n) 0 finsNil m i o h
  refine ⟨hn, hlen, ?_⟩
  have hj' : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  rw [hj']
  simp [List.getElem?_eq_getElem hj]

/-- A signature's row finds each of its operations by index. -/
theorem find_ofEff_isSome (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k j : Nat) (i : UInt32),
    i.toNat = k + j → k + j < 2 ^ 32 → j < E.length → (Row.find (Row.ofEff n E k) n i).isSome
  | [], _, _, _, _, _, h => absurd h (by simp)
  | (q, A, B) :: E, k, 0, i, hi, hk, _ => by
      have hik : i = UInt32.ofNat k := by
        apply UInt32.toNat.inj
        rw [hi, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        rfl
      subst hik
      simp [Row.ofEff, Row.find]
  | (q, A, B) :: E, k, j + 1, i, hi, hk, hj => by
      have hne : i ≠ UInt32.ofNat k := by
        intro h
        rw [h, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hi
        omega
      have ih := find_ofEff_isSome n E (k + 1) j i (by omega) (by omega)
        (by simp only [List.length_cons] at hj; omega)
      unfold Row.find at ih ⊢
      rw [Row.ofEff, List.find?_cons_of_neg (by simp [hne])]
      exact ih

/-- A signature's row finds its `j`-th operation at the index `j`, below `2³²`. -/
theorem find_ofEff_at (n : UInt32) (E : List (Qual × VTy × VTy)) (j : Nat) (hj : j < E.length)
    (hlen : E.length ≤ 2 ^ 32) :
    Row.find (Row.ofEff n E 0) n (UInt32.ofNat j) =
      some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit, false⟩ := by
  have hj' : j < 2 ^ 32 := by omega
  have hi : (UInt32.ofNat j).toNat = 0 + j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp
    (find_ofEff_isSome n E 0 j (UInt32.ofNat j) hi (by omega) hj)
  obtain ⟨-, j', hj'', hij, rfl⟩ := Row.find_ofEff n E 0 _ n _ o ho
  have : j' = j := by
    have h2 := congrArg UInt32.toNat hij
    rw [hi, Nat.zero_add, Nat.zero_add,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h2
    exact h2.symm
  subst this
  rw [ho, Nat.zero_add]

/-- A name's row at the signature `Ξ` gives it, before a row tied to `Ξ`, is tied to `Ξ`. -/
theorem rowAt_ofEff_append {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (hE : Ξ n = E) (hn : n ≠ 0) (hlen : E.length ≤ 2 ^ 32) (hS : RowAt Ξ S) :
    RowAt Ξ (Row.ofEff n E 0 ++ S) := by
  subst hE
  exact rowAt_append (ofEff_wf Ξ n hn hlen) hS

/-- **An effect's row finds, at each key, operations of the same signature at any cancel rows.** -/
theorem find_ofEff_sig (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs fs' : Nat → CTy)
    (m i : UInt32) (o : OpSig), Row.find (Row.ofEff n E k fs) m i = some o →
      ∃ o', Row.find (Row.ofEff n E k fs') m i = some o' ∧ o.Sig o'
  | [], _, _, _, _, _, _, h => by simp [Row.ofEff, Row.find] at h
  | (q, A, B) :: E, k, fs, fs', m, i, o, h => by
      by_cases hk : m = n ∧ i = UInt32.ofNat k
      · have h₁ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs) m i =
            some ⟨n, UInt32.ofNat k, q, A, B, fs 0, false⟩ := by
          simp [Row.ofEff, Row.find, hk]
        have h₂ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs') m i =
            some ⟨n, UInt32.ofNat k, q, A, B, fs' 0, false⟩ := by
          simp [Row.ofEff, Row.find, hk]
        rw [h₁] at h; cases h
        exact ⟨_, h₂, rfl, rfl, rfl, rfl, rfl⟩
      · have hd : decide (m = n ∧ i = UInt32.ofNat k) = false := decide_eq_false hk
        have h₁ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs) m i =
            Row.find (Row.ofEff n E (k + 1) (fun j => fs (j + 1))) m i := by
          simp only [Row.ofEff, Row.find, List.find?_cons, hd]
        have h₂ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs') m i =
            Row.find (Row.ofEff n E (k + 1) (fun j => fs' (j + 1))) m i := by
          simp only [Row.ofEff, Row.find, List.find?_cons, hd]
        rw [h₁] at h; rw [h₂]
        exact find_ofEff_sig n E (k + 1) _ _ m i o h

/-- **The tie reads no cancel row**: an effect's row before a tied row is tied at any cancel rows
when it is at some. -/
theorem rowAt_ofEff_fs {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)}
    {fs fs' : Nat → CTy} {S : Row} (h : RowAt Ξ (Row.ofEff n E 0 fs ++ S)) :
    RowAt Ξ (Row.ofEff n E 0 fs' ++ S) := by
  intro m i o hf
  rw [Row.find_append] at hf
  cases hA : Row.find (Row.ofEff n E 0 fs') m i with
  | some o₁ =>
      rw [hA, Option.some_or] at hf
      have ho : o₁ = o := Option.some.inj hf
      subst ho
      obtain ⟨o', hf', hsig⟩ := find_ofEff_sig n E 0 fs' fs m i o₁ hA
      obtain ⟨h₁, h₂, h₃⟩ := h m i o' (by rw [Row.find_append, hf', Option.some_or])
      refine ⟨h₁, h₂, ?_⟩
      rw [h₃, hsig.2.2.1, hsig.2.2.2.1, hsig.2.2.2.2]
  | none =>
      rw [hA, Option.none_or] at hf
      have hB : Row.find (Row.ofEff n E 0 fs) m i = none := by
        cases hB : Row.find (Row.ofEff n E 0 fs) m i with
        | none => rfl
        | some o₂ =>
            obtain ⟨o', hf', -⟩ := find_ofEff_sig n E 0 fs fs' m i o₂ hB
            rw [hA] at hf'; cases hf'
      exact h m i o (by rw [Row.find_append, hB, Option.none_or, hf])

/-- **A tied handler's signature is a prefix of the context's**: the handled row `(n)↑E ⊙ Σ`, tied
to `Ξ`, finds each operation of `E` at the signature `Ξ n` gives at its index.  `[spec §19]` -/
theorem sig_prefix_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) : E <+: Ξ n := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < E.length
  · have hf : Row.find (Row.ofEff n E 0 ++ S) n (UInt32.ofNat j) =
        some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit, false⟩ := by
      rw [Row.find_append, find_ofEff_at n E j hj hlen, Option.some_or]
    obtain ⟨-, -, hg⟩ := h n _ _ hf
    rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hg
    rw [List.getElem?_take_of_lt hj, hg, List.getElem?_eq_getElem hj]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    simp only [List.length_take]
    omega

/-- **A tied handler's tags are a prefix of the context's qualifiers** of its name (§25: a handler
value carries its operations' qualifiers, `E.map Prod.fst`).  `[spec §19, §25]` -/
theorem hndTags_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) :
    E.map Prod.fst <+: (Ξ n).map Prod.fst :=
  (sig_prefix_of_rowAt h hlen).map Prod.fst

/-! ### Terms with no operation -/

/-- The term holds no `perform`, `raise`, `hnd` or `iterate`: none of its parts is typed by a rule
that reads an operation's signature off a row. -/
def _root_.BoCa.Expr.effFree : Expr → Bool
  | .prim p => p != .perform && p != .raise && p != .hnd && p != .iterate
  | .var _ | .unit | .loc _ => true
  | .pair a b | .seq a b | .letpair a b | .app a b => a.effFree && b.effFree
  | .inj₁ a | .inj₂ a | .lam a => a.effFree
  | .case a b c => a.effFree && b.effFree && c.effFree

theorem effFree_shift (d : Nat) (e : Expr) : ∀ c, (e.shift d c).effFree = e.effFree := by
  induction e with
  | var i => intro c; simp only [Expr.shift]; split <;> rfl
  | _ => intro c; simp_all [Expr.shift, Expr.effFree]

theorem effFree_subst (e : Expr) : ∀ (j : Nat) (s : Val), e.effFree = true → s.1.effFree = true →
    (e.subst j s).effFree = true := by
  induction e with
  | var i =>
      intro j s _ hs
      simp only [Expr.subst]
      split
      · exact hs
      · split <;> rfl
  | lam b ih =>
      intro j s he hs
      exact ih (j + 1) (s.shift 1 0) he (by rw [Val.val_shift, effFree_shift]; exact hs)
  | letpair a b iha ihb =>
      intro j s he hs
      simp only [Expr.effFree, Bool.and_eq_true] at he
      simp only [Expr.subst, Expr.effFree, Bool.and_eq_true]
      exact ⟨iha j s he.1 hs, ihb (j + 2) (s.shift 2 0) he.2
        (by rw [Val.val_shift, effFree_shift]; exact hs)⟩
  | case a b c iha ihb ihc =>
      intro j s he hs
      simp only [Expr.effFree, Bool.and_eq_true] at he
      have hs' : (s.shift 1 0).1.effFree = true := by rw [Val.val_shift, effFree_shift]; exact hs
      simp only [Expr.subst, Expr.effFree, Bool.and_eq_true]
      exact ⟨⟨iha j s he.1.1 hs, ihb (j + 1) _ he.1.2 hs'⟩, ihc (j + 1) _ he.2 hs'⟩
  | _ => intro j s he hs; simp_all [Expr.subst, Expr.effFree]

/-- The facts `effFree` gives about the parts of a term, for `CDerivesAt.ofEffFree`. -/
macro "eff_free" : tactic => `(tactic| (simp_all only [Expr.effFree, Expr.val, Val.lam, Val.prim,
    Val.unit, Val.inj₁, Val.inj₂, withPair, absurdE, thenE, withborUE, Bool.and_eq_true,
    bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, and_self, and_true, true_and]))

/-- **A derivation of a term with no operation is tied at every effect context**: the three rules
that read a signature off a row type a `perform`, a `raise` or a `hnd`, and every other rule is the
same in both judgments.  `[spec §19]` -/
theorem CDerivesAt.ofEffFree {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) (he : e.effFree = true) : CDerivesAt Ξ Δ Γ e j := by
  induction h with
  | var h => exact .var h
  | unitI h => exact .unitI h
  | tensorI hs _ _ ih1 ih2 => exact .tensorI hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | sumI₁ _ ih1 => exact .sumI₁ (ih1 (by eff_free))
  | sumI₂ _ ih1 => exact .sumI₂ (ih1 (by eff_free))
  | thunkF _ ih1 => exact .thunkF (ih1 (by eff_free))
  | thunkV hC _ ih1 => exact .thunkV hC (ih1 he)
  | ret _ ih1 => exact .ret (ih1 he)
  | bind hs _ _ ih1 ih2 => exact .bind hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | force h => exact .force h
  | lam _ ih1 => exact .lam (ih1 (by eff_free))
  | lamDead _ ih1 => exact .lamDead (ih1 (by eff_free))
  | app hs _ hx ih1 => exact .app hs (ih1 (by eff_free)) hx
  | withI _ _ ih1 ih2 => exact .withI (ih1 (by eff_free)) (ih2 (by eff_free))
  | proj₁ _ ih1 => exact .proj₁ (ih1 (by eff_free))
  | proj₂ _ ih1 => exact .proj₂ (ih1 (by eff_free))
  | topI => exact .topI
  | unitE hs _ _ ih1 ih2 => exact .unitE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | tensorE hs _ _ ih1 ih2 => exact .tensorE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | sumE hs _ _ _ ih1 ih2 ih3 =>
      exact .sumE hs (ih1 (by eff_free)) (ih2 (by eff_free)) (ih3 (by eff_free))
  | zeroE hs _ ih1 => exact .zeroE hs (ih1 (by eff_free))
  | allI hbx hΔx hΓx _ ih1 => exact .allI hbx hΔx hΓx (ih1 (by eff_free))
  | allE _ hlt ih1 => exact .allE (ih1 (by eff_free)) hlt
  | bangThunkF hp _ ih1 => exact .bangThunkF hp (ih1 (by eff_free))
  | bangThunkV hp hC _ ih1 => exact .bangThunkV hp hC (ih1 he)
  | bangE _ ih1 => exact .bangE (ih1 he)
  | copyBang hΓ => exact .copyBang hΓ
  | forgetBang hΓ => exact .forgetBang hΓ
  | boxI _ hΓ ih1 => exact .boxI (ih1 he) hΓ
  | boxE _ ih1 => exact .boxE (ih1 he)
  | immSub _ hle ih1 => exact .immSub (ih1 he) hle
  | mutSub _ hle ih1 => exact .mutSub (ih1 he) hle
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
  | sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂
  | sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂
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
  | withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hdc (ih1 (by eff_free))
  | withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor2U x hΓ hx hside hfree₁ hfree₂ hS hdc (ih1 (by eff_free))
  | withbor3U x hΓ hx hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .withbor3U x hΓ hx hfree₁ hfree₂ hS hdc (ih1 (by eff_free))
  | withloadU x hΓ hx hfree₁ hfree₂ hS => exact .withloadU x hΓ hx hfree₁ hfree₂ hS
  | sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS hdc (ih1 (by eff_free))
  | sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc _ ih1 =>
      exact .sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS hdc (ih1 (by eff_free))
  | lolliE hs _ _ ih1 ih2 => exact .lolliE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | allEV _ hlt ih1 => exact .allEV (ih1 (by eff_free)) hlt
  | ofRet _ ih1 => exact .ofRet (ih1 he)
  | roll hA hc _ ih1 => exact .roll hA hc (ih1 he)
  | unroll _ ih1 => exact .unroll (ih1 he)
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact .foldImm F y c R hΓ hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R hΓ hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R hΓ hF hG
  | nuIn hC _ ih1 => exact .nuIn hC (ih1 he)
  | nuOut hC _ ih1 => exact .nuOut hC (ih1 he)
  | unfoldN C S hC hΓ => exact .unfoldN C S hC hΓ
  | effSub hle _ ih1 => exact .effSub hle (ih1 he)
  | effPerform => simp [BoCa.BoLo.performE, Expr.effFree, Expr.val, Val.prim] at he
  | effRaise => simp [BoCa.BoLo.raiseE, Expr.effFree, Expr.val, Val.prim] at he
  | effLet hs hW hU _ _ ih1 ih2 => exact .effLet hs hW hU (ih1 (by eff_free)) (ih2 (by eff_free))
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ih1 ih2 ih3 =>
      exact .effThen hs hNZ hUq hU hMS hDS hfin hP hSD (ih1 (by eff_free)) (ih2 (by eff_free))
        (ih3 (by eff_free))
  | effHandleV | effHandleVB | effHandleT =>
      simp [hndExpr, Expr.effFree, Expr.val, Val.prim] at he
  | iterate => simp [Expr.effFree, Expr.val, Val.prim] at he
  | divFuel => simp [divFuelV, fuelH, BoCa.BoLo.hndVal, BoCa.BoLo.hndE, Expr.effFree, Expr.val, Val.prim,
      Val.lam] at he
  | reify => simp [reifyV, BoCa.BoLo.hndE, Expr.effFree, Expr.val, Val.prim, Val.lam] at he
  | @letPoly _ _ N _ _ b hcl _ _ ihV ihN =>
      simp only [Expr.effFree, Expr.val, Val.lam, Bool.and_eq_true] at he
      exact .letPoly b hcl (ihV he.2)
        (ihN (by rw [effFree_shift]; exact effFree_subst N 0 (Val.lam b) he.1 he.2))

/-! ### Signature lists -/

/-- The operation is at `Ξ`'s signature: of a nonzero name with at most `2³²` operations, whose
`o.i`-th is `o`'s qualifier, argument and answer. -/
def OpAt (Ξ : EffCtx) (o : OpSig) : Prop :=
  o.n ≠ 0 ∧ (Ξ o.n).length ≤ 2 ^ 32 ∧ (Ξ o.n)[o.i.toNat]? = some (o.q, o.A, o.B)

/-- Every entry of the list is at `Ξ`'s signature. -/
def SigsAt (Ξ : EffCtx) (S : Row) : Prop := ∀ o ∈ S, OpAt Ξ o

theorem sigsAt_nil (Ξ : EffCtx) : SigsAt Ξ [] := fun _ h => absurd h List.not_mem_nil

theorem SigsAt.left {Ξ : EffCtx} {S S' : Row} (h : SigsAt Ξ (S ++ S')) : SigsAt Ξ S :=
  fun o ho => h o (List.mem_append_left S' ho)

theorem SigsAt.right {Ξ : EffCtx} {S S' : Row} (h : SigsAt Ξ (S ++ S')) : SigsAt Ξ S' :=
  fun o ho => h o (List.mem_append_right S ho)

/-- **A row whose entries are among a list at `Ξ`'s signatures is tied to `Ξ`.** -/
theorem rowAt_of_sigsAt {Ξ : EffCtx} {S : Row} (h : SigsAt Ξ S) : RowAt Ξ S := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  exact h o hm

/-! ### No unrestricted abortive operation -/

/-- **No abortive operation is unrestricted**: every operation `Ξ` gives at `unr` answers
something other than `0`, so an abortive operation (answer `0` at a qualifier with weakening) is
affine.  Decision 63's restriction: `multi ctl op(…) -> never` is not provided.
`[spec §18, §19]` -/
def EffCtx.NoUnrExn (Ξ : EffCtx) : Prop := ∀ n, ∀ p ∈ Ξ n, p.1 = .unr → p.2.2.isZero = false

/-- At such a context no name's signature is one unrestricted abortive operation. -/
theorem EffCtx.NoUnrExn.ne_exn {Ξ : EffCtx} (h : Ξ.NoUnrExn) (n : UInt32) (A : VTy) :
    Ξ n ≠ [(.unr, A, .zero)] := by
  intro he
  have := h n (.unr, A, .zero) (by rw [he]; exact List.mem_singleton_self _) rfl
  simp [VTy.isZero] at this

/-- **In a row tied to such a context an unrestricted operation resumes**: it is not abortive.
`[spec §19]` -/
theorem abort_false_of_rowAt {Ξ : EffCtx} (hx : Ξ.NoUnrExn) {S : Row} (h : RowAt Ξ S)
    {n i : UInt32} {o : OpSig} (hf : Row.find S n i = some o) (hq : o.q = .unr) :
    o.abort = false := by
  obtain ⟨-, -, hget⟩ := h n i o hf
  have hz := hx n (o.q, o.A, o.B) (List.mem_of_getElem? hget) hq
  simp only [OpSig.abort, hz, Bool.false_and]

end BoCa.Fig16.LogRel.Core
