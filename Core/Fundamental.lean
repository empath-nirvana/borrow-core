import Core.Compat
import Core.Integers
import Core.Arrays
import Core.SliceOps
import Core.CountFold
import Core.BoundedFix
import Core.FoldReuse
import Core.Nu
import Core.EffFin
import Core.EffBorrow
import Core.EffLend
import Core.EffBoxed
import Core.PolyLet
import Core.DivHandle
import Support.LogicalRelation.Adequacy

/-!
# Core — Fundamental Property and adequacy  `[spec §3]`

`CDerives Δ Γ e j`: the CBPV typing judgment on BoLo expressions, with `j` a value judgment
`val A` or a computation judgment `comp C`, in A-normal form.  Beside the CBPV formers it has
the lifetime `∀` (`∀E` at every `C`), the `!` rules, `[]I`/`[]E` (`[]I` at every value type),
`⊑imm`/`⊑mut`, one constant per borrow axiom at arbitrary value-type payloads, three
call-by-value derived forms (`lolliE`, `allEV`, `ofRet`), `roll`/`unroll` at `μ`, and the
borrowed and owned folds `foldImm`, `foldOwn`, `foldReuse` (`FoldImm.lean`, `FoldOwn.lean`,
`FoldReuse.lean`), and `νX. C`'s `nuIn`/`nuOut` and coiteration `unfoldN` (`Nu.lean`), of which
the delay and stream types' rules are instances (`fixD`, `unfoldS`).  §19's effect rules, with
§24's polymorphic let (`letPoly`), its `[handle]` at a value form (`effHandleV`, of which the
two-variable `effHandle` is an instance) and its `[then]` at a finaliser of the pure row; §28's
BOXED-κ (`effHandleVB`: `[handle]` with each clause's continuation boxed at `@d`); §26's
`λ_. M` at `1 ⊸ F_Σ B` with its binder dead (`lamDead`).
`fundamentalC` proves every rule sound at `SemV`/`SemC`; `adequacyC` runs a closed `F 1`
computation to `()` from the empty memory.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### `roll` and `unroll`

Typing rules on the same term, as `!E` is: the machine has no `roll`/`unroll` step. -/

/-- `roll` is sound: the unroll equation at `vC true`, under `wpTS_mono`. -/
theorem roll_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (hA : A.NoMut 0)
    (hc : (VTy.mu A).Cl 0) (h : SemV Δ Γ e (VTy.inst (.mu A) A)) : SemV Δ Γ e (.mu A) :=
  fun δ γ ls ρ hδ hΓ => wpTS_mono (fun _ _ _ hv => vC_roll hA hc hv) ρ (h δ γ ls ρ hδ hΓ)

/-- `unroll` is sound. -/
theorem unroll_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemV Δ Γ e (.mu A)) : SemV Δ Γ e (VTy.inst (.mu A) A) :=
  fun δ γ ls ρ hδ hΓ => wpTS_mono (fun _ _ _ hv => (vC_unfold hv).2.2) ρ (h δ γ ls ρ hδ hΓ)

/-! ### `[λ-dead]`  `[spec §26]` -/

/-- A live slot of `1` gives the context relation with the slot dead: a value of `1` holds only
the empty resource. -/
theorem gDenC_unit_dead {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : gDenC ls δ (⟨.unit, true⟩ :: Γ) γ ρ) : gDenC ls δ (⟨.unit, false⟩ :: Γ) γ ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp h
  cases γ with
  | nil => exact absurd hlen (by simp)
  | cons v γ =>
      obtain ⟨-, hs'⟩ := gSepC_cons_persistent (T := .unit) rfl hs
      exact gDenC_dead_cons .unit v (gDenC_mk (by simpa using hlen) hs')

/-- `λx. M : 1 ⊸ C` with `x`'s slot dead: `[λ]` at the context with `x : 1` live, whose relation
gives the one with `x` dead.  `[spec §26]` -/
theorem lamDead_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemC Δ (⟨.unit, false⟩ :: Γ) M C) : SemC Δ Γ (.val (.lam M)) (.arr .unit C) :=
  lam_compatC fun δ γ ls ρ hδ hg => h δ γ ls ρ hδ (gDenC_unit_dead hg)

/-- A judgment form: a value at `A`, or a computation at `C`.  `[spec §3]` -/
inductive Jdg where
  | val (A : VTy)
  | comp (C : CTy)

/-- The CBPV typing judgment.  Its context premises are `Ctx.SplitP`, `Ctx.DeadP` and
`Ctx.SoloP`: a live slot of persistent type may be duplicated and dropped.  `[spec §3, §10]` -/
inductive CDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop where
  | var {Δ Γ i A} (h : Ctx.SoloP Γ i A) : CDerives Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : Ctx.DeadP Γ) : CDerives Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (h₁ : CDerives Δ Γ₁ e₁ (.val A)) (h₂ : CDerives Δ Γ₂ e₂ (.val B)) :
      CDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B))
  | sumI₁ {Δ Γ e A B} (h : CDerives Δ Γ e (.val A)) :
      CDerives Δ Γ (.inj₁ e) (.val (.sum A B))
  | sumI₂ {Δ Γ e A B} (h : CDerives Δ Γ e (.val B)) :
      CDerives Δ Γ (.inj₂ e) (.val (.sum A B))
  /-- `thunk M : U (F A)`, `M` under a dead binder. -/
  | thunkF {Δ Γ M A} (h : CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerives Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
  /-- `thunk V : U C` for a λ-value `V : C`, `C` not an `F`. -/
  | thunkV {Δ Γ N C} (hC : C.isRet = false) (h : CDerives Δ Γ (.val (.lam N)) (.comp C)) :
      CDerives Δ Γ (.val (.lam N)) (.val (.thunk C))
  /-- `return V : F A`. -/
  | ret {Δ Γ V A} (h : CDerives Δ Γ V (.val A)) : CDerives Δ Γ V (.comp (.ret A))
  /-- `M to x. N`, written `(λx. N) M`. -/
  | bind {Δ Γ Γ₁ Γ₂ M N A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerives Δ Γ₁ M (.comp (.ret A))) (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      CDerives Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.SoloP Γ i (.thunk C)) :
      CDerives Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : CDerives Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      CDerives Δ Γ (.val (.lam M)) (.comp (.arr A C))
  /-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B` with `x`'s slot dead, `M` not using it.  `[spec §26]` -/
  | lamDead {Δ Γ M} {S : Row} {B : VTy}
      (h : CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (CTy.effOf S B))) :
      CDerives Δ Γ (.val (.lam M)) (.comp (.arr .unit (CTy.effOf S B)))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : CDerives Δ Γ₁ M (.comp (.arr A C))) (hx : Ctx.SoloP Γ₂ i A) :
      CDerives Δ Γ (.app M (.var i)) (.comp C)
  /-- `⟨M, N⟩ : C & D`, both components in the same context. -/
  | withI {Δ Γ M N C D} (hM : CDerives Δ (withCtx Γ) M (.comp C))
      (hN : CDerives Δ (withCtx Γ) N (.comp D)) :
      CDerives Δ Γ (withPair M N) (.comp (.amp C D))
  | proj₁ {Δ Γ M C D} (h : CDerives Δ Γ M (.comp (.amp C D))) :
      CDerives Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M C D} (h : CDerives Δ Γ M (.comp (.amp C D))) :
      CDerives Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)
  /-- `⟨⟩ : ⊤` at any context. -/
  | topI {Δ Γ} : CDerives Δ Γ (.val .unit) (.comp .top)
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hV : CDerives Δ Γ₁ V (.val .unit)) (hM : CDerives Δ Γ₂ M (.comp C)) :
      CDerives Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : CDerives Δ Γp V (.val (.tensor A B)))
      (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
      CDerives Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : CDerives Δ Γs V (.val (.sum A B)))
      (h₁ : CDerives Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
      (h₂ : CDerives Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
      CDerives Δ Γ (.case V M₁ M₂) (.comp C)
  /-- `absurd V : C` for `V : 0`, at any rest of the context. -/
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : CDerives Δ Γ₁ V (.val .zero)) :
      CDerives Δ Γ (absurdE V) (.comp C)
  /-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`; the binder's slot is dead, at any type. -/
  | allI {Δ Γ x b M S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : CDerives (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
      CDerives Δ Γ (.val (.lam M)) (.comp (.all x b C))
  /-- `M [] : C[@a/'x]`. -/
  | allE {Δ Γ M x b a C} (h : CDerives Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
      CDerives Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))
  /-- Promotion of `thunk M : U (F A)` over `!Γ`. -/
  | bangThunkF {Δ Γ M A} (hp : Persistent Γ)
      (h : CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
      CDerives Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))
  /-- Promotion of a λ-value `V : C` over `!Γ`. -/
  | bangThunkV {Δ Γ N C} (hp : Persistent Γ) (hC : C.isRet = false)
      (h : CDerives Δ Γ (.val (.lam N)) (.comp C)) :
      CDerives Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))
  /-- Dereliction. -/
  | bangE {Δ Γ e A} (h : CDerives Δ Γ e (.val (.bang A))) : CDerives Δ Γ e (.val A)
  | copyBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  /-- `[]I`. -/
  | boxI {Δ Γ e a A} (h : CDerives Δ Γ e (.val A)) (hΓ : CtxOutlives Δ Γ a) :
      CDerives Δ Γ e (.val (.box a A))
  | boxE {Δ Γ e a A} (h : CDerives Δ Γ e (.val (.box a A))) : CDerives Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : CDerives Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      CDerives Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : CDerives Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      CDerives Δ Γ e (.val (.mut a A))
  /-- The borrow axioms, at arbitrary value-type payloads. -/
  | alloc {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ forget (.val axForgetUnkTy)
  /-- An integer literal at its width.  `[spec §8]` -/
  | lit {Δ Γ} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width))
  /-- A host operation at `!(A ⊸ F B)`, its signature in `SPEC.md` §8.  `[spec §8]` -/
  | hostOp {Δ Γ} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op)))
  /-- `array_new : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)`, the step `tab`.  `[spec §9]` -/
  | arrNew {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .tab)) (.val (arrNewTy A))
  /-- `array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)`, the step `drop`.  `[spec §9]` -/
  | arrFree {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A))
  /-- `array_size : !(Array A ⇒ Array A ⊗ I32)`.  `[spec §9]` -/
  | arrSize {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ (.val sizeV) (.val (arrSizeTy A))
  /-- `array_replace : !(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))`.  `[spec §9]` -/
  | arrReplace {Δ Γ} (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val replaceV) (.val (arrReplaceTy A))
  /-- `array_len : !(ArrayImm @a A ⇒ I32)`.  `[spec §9]` -/
  | arrLen {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val arrLenV) (.val (arrLenTy a A))
  /-- `array_get : !(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | arrGet {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A))
  /-- `array_copy : !(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)`.  `[spec §9]` -/
  | arrCopy {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val copyV) (.val (arrCopyTy a A))
  /-- `array_forget : !(ArrayImm @a A ⇒ 1)`.  `[spec §9]` -/
  | arrForget {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val forgetV) (.val (arrForgetTy a A))
  /-- `count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`, the step `count`: the counted
  loop, total at every host.  `[spec §16]` -/
  | countFold {Δ Γ} (S : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .count)) (.val (countFoldTy S))
  /-- `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`, the step `countTry`: the
  counted loop with an exit, total at every host.  `[spec §16]` -/
  | countTry {Δ Γ} (S E : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .countTry)) (.val (countTryTy S E))
  /-- `bounded_fix : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)`, the step
  `boundedFix`: the fixed point with a budget of depth, total at every host and every
  computation type.  `[spec §20]` -/
  | boundedFix {Δ Γ} (A : VTy) (C : CTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C))
  /-- `iterate : !U(!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R) ⊗ S ⊸ F_Σ(B ⊕ R))` at a row holding `Div`, the
  step `iterate`: the loop that ticks at each back edge.  `[spec §14]` -/
  | iterate {Δ Γ} (S : Row) (St B R : VTy) (hS : Row.divB S = true) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .iterate)) (.val (iterTy S St B R))
  /-- `div_fuel : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)`, `Σ` without `Div`'s name: the handler of
  `Div` that answers *next* to the first ticks, as many as the budget, and *close* after.
  `[spec §14]` -/
  | divFuel {Δ Γ} (S : Row) (A : VTy) (hS : ∀ o ∈ S, o.n ≠ divEff) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val divFuelV) (.val (divFuelTy S A))
  /-- `reify_res : !U(U(1 ⊸ F_{tick, Σ}(B ⊕ R)) ⊸ F_Σ U(Loop_Σ B R))`, `Σ` without `Div`'s name, at
  the residual of a result `res : !U(B ⊸ F_Σ R)`, a closed term: the handler of `Div` that makes
  a loop value of a computation.  `[spec §14]` -/
  | reify {Δ Γ} (S : Row) (B R : VTy) (res : Val) (hS : ∀ o ∈ S, o.n ≠ divEff)
      (hcl : closedAt 0 res.1 = true) (hres : CDerives Δ [] (.val res) (.val (resTy S B R)))
      (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (reifyV res)) (.val (reifyTy S B R))
  /-- `slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `mut` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowM {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))
  /-- `slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`, the term
  `withbor`'s: an owned array lent as a family of `imm` leaves, with no cell; its side conditions
  non-strict.  `[spec §9, §23]` -/
  | sliceBorrowI {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))
  /-- `slice_get_mut : !([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)`, the step `idx`.  `[spec §9]` -/
  | sliceGetM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A))
  /-- `slice_len_mut : !([Mut @a A] ⇒ [Mut @a A] ⊗ I32)`.  `[spec §9]` -/
  | sliceLenM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val sizeV) (.val (sliceLenMTy a A))
  /-- `slice_split_imm : !([Imm @a A] ⊗ I32 ⇒ ([Imm @a A] ⊗ [Imm @a A]) ⊕ [Imm @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A))
  /-- `slice_split_mut : !([Mut @a A] ⊗ I32 ⇒ ([Mut @a A] ⊗ [Mut @a A]) ⊕ [Mut @a A])`, the step
  `split`.  `[spec §9]` -/
  | sliceSplitM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A))
  /-- `slice_empty_imm : [Imm @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyI {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val emptyFamV) (.val (.arrayImm a A))
  /-- `slice_empty_mut : [Mut @a A]`, the family `(0, 0)`.  `[spec §9]` -/
  | sliceEmptyM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val emptyFamV) (.val (.sliceMut a A))
  /-- `slice_replace_mut : !([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))`, `array_replace`'s
  term.  `[spec §9]` -/
  | sliceReplaceM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val replaceV) (.val (sliceReplaceMTy a A))
  /-- `slice_swap_mut : !([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])`.  `[spec §9]` -/
  | sliceSwapM {Δ Γ} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val swapV) (.val (sliceSwapMTy a A))
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  /-- `withbor` (2): `Ref A` lent as `Mut 'x A`, its side condition `Δ ⊢ A ⊒ @b` non-strict.
  `[spec §23]` -/
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ withswap (.val (axWithswapTy a A B))
  /-- The unwinding form of `withbor` (1): `Ref A` lent as `Imm 'x A` to a callback at a row of
  abortive operations; when it unwinds, the finaliser `d` runs on the source.  `[spec §19]` -/
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Lend x)
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (2): `Ref A` lent as `Mut 'x A`, at a lend's row, its side
  condition non-strict.  `[spec §19, §23, §48]` -/
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Lend x)
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `withbor` (3): `Mut @a A` reborrowed as `Mut 'x A`.  `[spec §19]` -/
  | withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.mut a A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `withload`: its own term, the source consumed by the load.
  `[spec §19]` -/
  | withloadU {Δ Γ a A B} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) :
      CDerives Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_mut`: an owned array lent as a family of `mut` leaves.
  `[spec §19]` -/
  | sliceBorrowMU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))
  /-- The unwinding form of `slice_borrow_imm`: an owned array lent as a family of `imm` leaves.
  `[spec §19]` -/
  | sliceBorrowIU {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
      (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.array A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S))
  -- Call-by-value derived forms: BoLo's application and `∀E` on arbitrary subterms, and the
  -- reading of a computation of `F A` as a value-judged expression at `A`.
  /-- Call-by-value application `f a`, both arbitrary, at `VTy.lolli` (`lolliE_compatX`).  `[spec §3]` -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (ha : CDerives Δ Γ₁ a (.val A)) (hf : CDerives Δ Γ₂ f (.val (.lolli A B))) :
      CDerives Δ Γ (.app f a) (.val B)
  /-- Call-by-value `∀E`: `e []` for `e` at `VTy.all x b A` (`allE_compatX`).  `[spec §3]` -/
  | allEV {Δ Γ e x b a A} (h : CDerives Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      CDerives Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  /-- A computation of `F A` is a value-judged expression at `A`: `SemV` is `SemC` at `F A`.  `[spec §3]` -/
  | ofRet {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.ret A))) : CDerives Δ Γ e (.val A)
  /-- `roll`: a value of `A[μX. A/X]` is a value of `μX. A`, at a closed `μ` whose variable is
  outside `A`'s `Mut` payloads (`docs/scope-recursion.md` §2.2).  `[spec §6]` -/
  | roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : CDerives Δ Γ e (.val (VTy.inst (.mu A) A))) : CDerives Δ Γ e (.val (.mu A))
  /-- `unroll`: a value of `μX. A` is a value of `A[μX. A/X]`.  `[spec §6]` -/
  | unroll {Δ Γ e A} (h : CDerives Δ Γ e (.val (.mu A))) :
      CDerives Δ Γ e (.val (VTy.inst (.mu A) A))
  /-- The borrowed fold, a constant:
  `foldImm : !U(∀'y ⊏ ⊤. A_R ⊸ F R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F R)`, for `T` built by
  `⊗`/`⊕` from closed leaves, `Ref X` and `X` (not `X` itself), `A_R = Imm̲ 'y T` with `R` at
  every recursive position, `R` outliving every lifetime, `'y` free in neither `μX. T` nor
  `R`.  `[spec §6]` -/
  | foldImm {Δ Γ} (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : Ctx.DeadP Γ)
      (hF : F.WF) (hG : F.Guarded) (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R)
      (hR : ∀ Δ' a, VOutlives Δ' a R) :
      CDerives Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))
  /-- The owned fold, a constant: `foldOwn : !U(A′_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`, for `T` of the
  same class, `A′_R = T` with `R` at every recursive position, any `R`.  `[spec §6]` -/
  | foldOwn {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerives Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))
  /-- The owned fold with reuse, a constant: `foldReuse : !U(A″_R ⊸ F R) ⊸ !U(μX. T ⊸ F R)`,
  for `T` of the same class, `A″_R = T` with `R` at a head `X` and `Ref 1 ⊗ R` at every `Ref X`
  (the emptied cell and the result on its content), any `R`.  `[spec §6]` -/
  | foldReuse {Δ Γ} (F : FShape) (R : VTy) (hΓ : Ctx.DeadP Γ) (hF : F.WF) (hG : F.Guarded) :
      CDerives Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))
  /-- `νX. C` is its unrolling `C[U(νX. C)/X]` (`cC_nu_iff`), on the same term, at a positive
  `C`.  `[spec §7]` -/
  | nuIn {Δ Γ e C} (hC : C.NuOk) (h : CDerives Δ Γ e (.comp C.unroll)) :
      CDerives Δ Γ e (.comp (.nu C))
  | nuOut {Δ Γ e C} (hC : C.NuOk) (h : CDerives Δ Γ e (.comp (.nu C))) :
      CDerives Δ Γ e (.comp C.unroll)
  /-- Coiteration, a constant: `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` (`Nu.lean`), at a
  positive `C`.  `[spec §7]` -/
  | unfoldN {Δ Γ} (C : CTy) (S : VTy) (hC : C.NuOk) (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
  /-- `[sub]`: `F_Σ A ≤ F_Σ′ A` for `Σ ⊆ Σ′`; `F A = F_∅ A`.  `[spec §19]` -/
  | effSub {Δ Γ e} {S S' : Row} {A : VTy} (hle : RowLe S S')
      (h : CDerives Δ Γ e (.comp (CTy.effOf S A))) : CDerives Δ Γ e (.comp (CTy.effOf S' A))
  /-- `[perform]`: a non-abortive operation of the row.  `[spec §19]` -/
  | effPerform {Δ Γ V} {S : Row} {o : OpSig} (hf : Row.find S o.n o.i = some o)
      (hna : o.abort = false) (h : CDerives Δ Γ V (.val o.A)) :
      CDerives Δ Γ (BoCa.BoLo.performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B))
  /-- `[raise]`: an abortive operation of the row, at any answer, its argument dropping.
  `[spec §19]` -/
  | effRaise {Δ Γ V} {S : Row} {o : OpSig} {B : VTy} (hf : Row.find S o.n o.i = some o)
      (ha : o.abort = true) (hd : o.A.Drop) (h : CDerives Δ Γ V (.val o.A)) :
      CDerives Δ Γ (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B))
  /-- `[let]`: `M to x. N` at a row; `N`'s context drops at a row with weakening and is
  persistent at an unrestricted row.  `[spec §19]` -/
  | effLet {Δ Γ Γ₁ Γ₂ M N A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
      (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
      (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
      CDerives Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B))
  /-- `[then]`: `M then x. N unwind D`, `M` at `Σ_M ≤ Σ` and the finaliser at `Σ_D ≤ Σ`, each
  capturable operation of `Σ_M` with `Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`: what the finaliser may raise or
  perform when a continuation captured in `M` is cancelled is recorded in that operation's cancel
  row.  `Γ₂` is persistent where `Σ` has an unrestricted operation at some depth of its cancel
  rows (`Row.UnrD`), since the finaliser runs in the cancels below it, and the errors pending at the
  finaliser are persistent where `Σ_D` has one.  The finaliser's row does not hold `Div`: a
  finaliser must terminate (decision 69).  `[then]` at option A, the finaliser at `F 1`, is `CDerives.effThenA`.
  `[spec §14, §19, §24, §27]` -/
  | effThen {Δ Γ Γ₁ Γ₂ M N D A B} {S SM SD : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ)
      (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂) (hMS : RowLe SM S) (hDS : RowLe SD S)
      (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
        capB o.q o.B = true → ThenLe o.fin SD o'.fin)
      (hP : SD.UnrD → SM.PendPers) (hSD : Row.divB SD = false)
      (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)))
      (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
      (hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
      CDerives Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
  /-- `[handle]`: `handle_n e with H`, the handler's pair `H = (h_ret, hs)` a value form over a
  part of the context whose live slots are persistent, `n` not in `Σ`.  The `j`-th operation's
  cancel row is `fs j`, and its clause's `κ` has its cancel branch at `cancelTy Σ (fs j)`.  The
  handled row does not hold `Div`: a handler of `Div`, or of another name around a computation
  that ticks, is `effHandleT` (decision 68).  At two variables and empty cancel rows it is
  `hndTerm` (`CDerives.effHandle`).  `[spec §14, §19, §24, §27]` -/
  | effHandleV {Δ Γ Γ₁ Γ₂ H e} {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {A R : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
      (hc : CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
      CDerives Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
  /-- BOXED-κ: `[handle]` whose capturing clauses receive their continuation boxed, `κ : [@d] K`
  (the clauses at `clausesTyB Σ R d E fs`). The handled computation's context outlives `@d`, and
  so does the answer type of every non-abortive operation of its row, handled or forwarded.
  `[spec §28]` -/
  | effHandleVB {Δ Γ Γ₁ Γ₂ H e} {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {A R : VTy} {d : Lifetime.Life} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
      (hH : H.ValFormIn Γ₁)
      (hc : CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyB S R d E fs))))
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)))
      (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S)) :
      CDerives Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))
  /-- `[handle]` at clauses that resume `κ` in tail position: `handle_n e with (h_ret, gs)`, the
  clauses written out from a tuple `gs` of answering functions (`tailTuple`), each at a row `Σ_N`
  of linear operations below `Σ`; an abortive operation's clause is its function itself.  The
  handled row may hold `Div` (decision 68).  At the grade `c` the handled operations are
  call-graded and so is every operation of `Σ_N`: the only handler of a graded name.
  `[spec §14, §19, §48]` -/
  | effHandleT {Δ Γ Γ₁ Γ₂} {Hr Hc e : Expr} {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
      {n : UInt32} {c : Bool} {A R : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
      (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
      (hc : CDerives Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
      (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
      (hCN : c = true → ∀ o ∈ SN, o.call = true)
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs c ++ S) A))) :
      CDerives Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
        (.comp (CTy.effOf S R))
  /-- `[let-poly]`: `let x = λy. b in N` for a closed λ-value, from `N` with the λ-value for `x`,
  `x`'s slot dead.  Each occurrence of the λ-value in `N` is typed on its own, at its own row: the
  kernel's row polymorphism, with the value restriction.  `[spec §24]` -/
  | letPoly {Δ Γ N C} {j : Jdg} (b : Expr) (hcl : closedAt 0 (Val.lam b).1 = true)
      (hV : CDerives Δ [] (.val (.lam b)) j)
      (hN : CDerives Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 (Val.lam b)).shift 1 0) (.comp C)) :
      CDerives Δ Γ (.app (.val (.lam N)) (.val (.lam b))) (.comp C)

/-- `[then]` with its finaliser at the pure row (SPEC §24, option A): `effThen` at `Σ_M = Σ` and
`Σ_D = ∅`, since `F ⋈ ∅ ≤ F` (`ThenLe.nil`).  `[spec §24, §27]` -/
theorem CDerives.effThenA {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerives Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  .effThen (SD := []) hs hNZ hUq hU (RowLe.refl S) (RowLe.nil S)
    (fun _ _ o _ hf hf' _ => by rw [hf] at hf'; cases hf'; exact ThenLe.nil o.fin)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) rfl hM hN hD

/-- `[handle]` at two variables: `handle_n e with (h_ret, hs)`, `h_ret` and `hs` variables of
slots at their types.  An instance of `effHandleV`: `(h_ret, hs)` is a value form, typed by
`[⊗I]`, over slots that are persistent.  `[spec §19]` -/
theorem CDerives.effHandle {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerives Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he

/-! ### The delay, stream and finite iterator instances  `[spec §7]`

`D A`, `Stream A` and `Iter A R R'` are `νX. C` at fixed bodies (`CTy.delay`, `CTy.stream`,
`CTy.iter`), each positive and polynomial; their in/out rules and loops are `nuIn`, `nuOut` and
`unfoldN` there. -/

/-- The step's type of `fixD`, `S ⊸ F(A ⊕ S) & F 1`. -/
abbrev stepDC (A S : VTy) : CTy := .arr S (.amp (.ret (.sum A S)) (.ret .unit))

/-- `fixD`'s type, `!U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`. -/
abbrev fixDTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepDC A S))) (.bang (.thunk (.arr S (.delay A))))

/-- `fixD = unfold` at `D A`. -/
abbrev fixDV (A : VTy) : Val := unfoldV (CTy.delayBody A)

/-- The step's type of `unfoldS`, `S ⊸ F(A ⊗ S) & F 1`. -/
abbrev stepSC (A S : VTy) : CTy := .arr S (.amp (.ret (.tensor A S)) (.ret .unit))

/-- `unfoldS`'s type, `!U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`. -/
abbrev unfoldSTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepSC A S))) (.bang (.thunk (.arr S (.stream A))))

/-- `unfoldS = unfold` at `Stream A`. -/
abbrev unfoldSV (A : VTy) : Val := unfoldV (CTy.streamBody A)

theorem CDerives.delayIn {Δ Γ e A} (h : CDerives Δ Γ e (.comp (delayUnroll A))) :
    CDerives Δ Γ e (.comp (.delay A)) :=
  .nuIn (CTy.delayBody_nuOk A) (by rw [CTy.delay_unroll]; exact h)

theorem CDerives.delayOut {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.delay A))) :
    CDerives Δ Γ e (.comp (delayUnroll A)) := by
  rw [← CTy.delay_unroll]; exact .nuOut (CTy.delayBody_nuOk A) h

/-- Guarded recursion on the delay type: `fixD : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`. -/
theorem CDerives.fixD {Δ Γ} (A S : VTy) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (fixDV A)) (.val (fixDTy A S)) := by
  have h := CDerives.unfoldN (Δ := Δ) (CTy.delayBody A) S (CTy.delayBody_nuOk A) hΓ
  rwa [unfoldTy, CTy.delayBody_instT] at h

theorem CDerives.streamIn {Δ Γ e A} (h : CDerives Δ Γ e (.comp (streamUnroll A))) :
    CDerives Δ Γ e (.comp (.stream A)) :=
  .nuIn (CTy.streamBody_nuOk A) (by rw [CTy.stream_unroll]; exact h)

theorem CDerives.streamOut {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.stream A))) :
    CDerives Δ Γ e (.comp (streamUnroll A)) := by
  rw [← CTy.stream_unroll]; exact .nuOut (CTy.streamBody_nuOk A) h

/-- Coiteration on the stream type: `unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`. -/
theorem CDerives.unfoldS {Δ Γ} (A S : VTy) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (unfoldSV A)) (.val (unfoldSTy A S)) := by
  have h := CDerives.unfoldN (Δ := Δ) (CTy.streamBody A) S (CTy.streamBody_nuOk A) hΓ
  rwa [unfoldTy, CTy.streamBody_instT] at h

/-- The semantic judgment at a judgment form.  `[spec §3]` -/
def SemJ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .val A => SemV Δ Γ e A
  | .comp C => SemC Δ Γ e C

/-- **Fundamental Property** of the CBPV judgment over the typed world at CBPV types.  `[spec §3]` -/
theorem fundamentalC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : SemJ Δ Γ e j := by
  induction h with
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
  | lamDead _ ih => exact lamDead_compatC ih
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
  | boxI _ hΓ ih => exact boxI_compatC ih hΓ
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
  | iterate _ _ _ _ hS hΓ => exact iterate_compatX hS hΓ
  | divFuel _ _ hS hΓ => exact divFuel_compatX hS hΓ
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact reify_compatX hS hcl ihres hΓ
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
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatX hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS hdc _ ihd => exact withbor1L_compatX x hΓ hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS hdc _ ihd =>
      exact withbor2L_compatX x hΓ hside hf₁ hf₂ hS hdc ihd
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
  | effThen hs hNZ _ hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact then_compatC hs hNZ hU hMS hDS hfin hP hSD ihM ihN ihD
  | effHandleV hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact handleV_compatC hs hd hH ihc hn0 hnS hlen hdv ihe
  | effHandleVB hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact handleV_compatCB hs hd hH ihc hn0 hnS hlen hdv ihe hΓd hSd
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin hCN _ ihc ihe =>
      exact handleT_compatC hs hd hHr hHc ihc hn0 hnd hnS hlen hSN hLin hCN ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatC (Val.lam b) hcl ihN

/-- **The stop lemma** (BOXED-κ's premise, `[spec §28]`): a computation typed at `F_Σ A` under
`Γ`, with `Δ ⊨ Γ ⊐ @d` and every non-abortive answer type of `Σ` outliving `@d`, has the
continuation's share in `Res_{δ(d)}` at every stop, at every `δ`. No premise asks that no lend be
open at a stop: `CDerives` types a lend's callback at the pure row or at a row of abortive
operations, and `wpG`'s `↭` already excludes a lend open at a stop. -/
theorem stop_lemma {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hSd : Row.divB S = false) (hder : CDerives Δ Γ M (.comp (CTy.effOf S A)))
    (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d :=
  stop_sem hSd (fundamentalC hder) hΓ hS

/-! ### Adequacy -/

/-- `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅` (`Adequacy.reclaim`'s argument). -/
theorem reclaim (ρ : WRes) (hupd : ResU.UpdV PMap.empty ρ) (hno : NoOwn ρ) : ρ = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨σ, hσ⟩ := hupd.2.2
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hg
      have hfa : ρ.FlatAt l χ := (ResU.flatAt_iff hσ l χ).mpr hχ
      rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · have hko : ψ.kind = Kind.own := by rw [← hk]; exact CellU.kind_ownOf w
        have hr : (ρ.restrict Kind.own).get l = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hg, hko⟩
        rw [hno, PMap.empty_get] at hr
        simp at hr
      · have hemp := (hupd.1.1 l s w ξ hξ).mpr hfa
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hemp
        simp at hemp
      · obtain ⟨w', ξ', h', hP', hfa'⟩ := (hupd.1.2 l b P).mpr ⟨w, ξ, hξ, hP, hfa⟩
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hfa'
        simp at hfa'

/-- `[CONF]` Theorem 3.2 at this world's `wpTS`, at the empty list. -/
theorem theorem32 (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes)) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', -, -,
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, -, -, -, -, h12⟩ :=
    wpTS_angelic _ hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty
      (ResU.comp_empty_right _) TW.empty htg
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

/-- `[CONF]` Corollary 3.3 at `SemC … (F 1)`. -/
theorem corollary33 (e : Expr) (hsem : SemC LifeCtx.empty [] e (.ret .unit)) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have hwp' : wpTS [] e (fun _ v => Fig16.BoLo.pure (v = Val.unit)) (PMap.empty : WRes) := by
    have he : substAll [] e = e := Adequacy.psub_nil 0 e
    rw [he] at hwp
    exact hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp'
  subst hv
  exact hsteps

/-- **Adequacy**: a closed computation of type `F 1` runs from the empty memory to `()` and the
empty memory.  `[spec §3]` -/
theorem adequacyC {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit))) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamentalC h)

/-! ### A closed program through `U`, `&`, `⊤`, `force` and a projection -/

/-- `thunk ⟨return (), ⟨⟩⟩ to t. π₁ (force t) : F 1`.  The thunk of a `&` is the pair itself,
and forcing it is using it. -/
def exProg : Expr :=
  .app (.val (.lam (.app (.var 0) (.val (.inj₁ .unit))))) (withPair (.val .unit) (.val .unit))

theorem exProg_derives : CDerives LifeCtx.empty [] exProg (.comp (.ret .unit)) :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil
    (.ret (.thunkV rfl (.withI (.ret (.unitI (.cons (.cons .nil)))) .topI)))
    (.proj₁ (.force (C := .amp (.ret .unit) .top) (.here .nil)))

theorem exProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem exProg Adequacy.emptyMem (.val .unit) :=
  adequacyC exProg_derives

end BoCa.Fig16.LogRel.Core

end
