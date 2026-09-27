import Grades.Context

/-!
# Grades — the graded judgment, and its equivalence with `CDerives`

`GDerives P` is `CDerives` with its context premises graded: `Ctx.SplitP` becomes `GSplit P`,
`Ctx.DeadP` becomes `GDead P`, `Ctx.SoloP` becomes `GSolo P`, a live binder carries a live grade,
a dead binder is at `[0,0]`, and promotion concludes at `ω · Γ` (its only scaling).  Two rules
are present only when the profile has erasure: an erased abstraction `lam0` (its binder at
`[0,0]`) and an erased application `app0` (the argument mentioned at no cost).

* `GDerives.toCore`: a derivation under `Profile.core` is a `CDerives` derivation of the erasure.
* `CDerives.toGraded`: a `CDerives` derivation is a `Profile.core` derivation of the context
  graded by the defaults, and `erase_embed` takes it back.
* `GDerives.mono`: a derivation under a profile is one under every larger profile; in particular
  `Profile.core ≤ Profile.graded`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Graded
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Grades
open Grades.Grade

/-- `Ghost A = 1 ⊕ (0 ⊗ A)`: the run-time type of an erased parameter of type `A`.  Its only
value is `inj₁ ()`, at the empty resource; the type records `A` for the checker. -/
def ghost (A : VTy) : VTy := .sum .unit (.tensor .zero A)

/-- The erased argument: `inj₁ ()`. -/
def ghostV : Val := .inj₁ .unit

/-- `withCtx`, graded: the two dead binders of `⟨M, N⟩` at `[0,0]`. -/
abbrev gwithCtx (Γ : GCtx) : GCtx := ⟨.unit, .erased⟩ :: ⟨.sum .unit .unit, .erased⟩ :: Γ

/-- The graded CBPV judgment. -/
inductive GDerives (P : Profile) : LifeCtx → GCtx → Expr → Jdg → Prop where
  | var {Δ Γ i A} (h : GSolo P Γ i A) : GDerives P Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : GDead P Γ) : GDerives P Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : GSplit P Γ Γ₁ Γ₂)
      (h₁ : GDerives P Δ Γ₁ e₁ (.val A)) (h₂ : GDerives P Δ Γ₂ e₂ (.val B)) :
      GDerives P Δ Γ (.pair e₁ e₂) (.val (.tensor A B))
  | sumI₁ {Δ Γ e A B} (h : GDerives P Δ Γ e (.val A)) :
      GDerives P Δ Γ (.inj₁ e) (.val (.sum A B))
  | sumI₂ {Δ Γ e A B} (h : GDerives P Δ Γ e (.val B)) :
      GDerives P Δ Γ (.inj₂ e) (.val (.sum A B))
  | thunkF {Δ Γ M A} (h : GDerives P Δ (⟨.unit, .erased⟩ :: Γ) M (.comp (.ret A))) :
      GDerives P Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
  | thunkV {Δ Γ N C} (hC : C.isRet = false) (h : GDerives P Δ Γ (.val (.lam N)) (.comp C)) :
      GDerives P Δ Γ (.val (.lam N)) (.val (.thunk C))
  | ret {Δ Γ V A} (h : GDerives P Δ Γ V (.val A)) : GDerives P Δ Γ V (.comp (.ret A))
  | bind {Δ Γ Γ₁ Γ₂ M N A C} {g : Grade} (hs : GSplit P Γ Γ₁ Γ₂)
      (hM : GDerives P Δ Γ₁ M (.comp (.ret A))) (hg : g.live = true)
      (hN : GDerives P Δ (⟨A, g⟩ :: Γ₂) N (.comp C)) :
      GDerives P Δ Γ (.app (.val (.lam N)) M) (.comp C)
  | force {Δ Γ i C} (h : GSolo P Γ i (.thunk C)) :
      GDerives P Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} {g : Grade} (hg : g.live = true)
      (h : GDerives P Δ (⟨A, g⟩ :: Γ) M (.comp C)) :
      GDerives P Δ Γ (.val (.lam M)) (.comp (.arr A C))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : GSplit P Γ Γ₁ Γ₂)
      (hM : GDerives P Δ Γ₁ M (.comp (.arr A C))) (hx : GSolo P Γ₂ i A) :
      GDerives P Δ Γ (.app M (.var i)) (.comp C)
  | withI {Δ Γ M N C D} (hM : GDerives P Δ (gwithCtx Γ) M (.comp C))
      (hN : GDerives P Δ (gwithCtx Γ) N (.comp D)) :
      GDerives P Δ Γ (withPair M N) (.comp (.amp C D))
  | proj₁ {Δ Γ M C D} (h : GDerives P Δ Γ M (.comp (.amp C D))) :
      GDerives P Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M C D} (h : GDerives P Δ Γ M (.comp (.amp C D))) :
      GDerives P Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)
  | topI {Δ Γ} : GDerives P Δ Γ (.val .unit) (.comp .top)
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : GSplit P Γ Γ₁ Γ₂)
      (hV : GDerives P Δ Γ₁ V (.val .unit)) (hM : GDerives P Δ Γ₂ M (.comp C)) :
      GDerives P Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} {gA gB : Grade} (hs : GSplit P Γ Γp Γb)
      (hV : GDerives P Δ Γp V (.val (.tensor A B))) (hgA : gA.live = true) (hgB : gB.live = true)
      (hM : GDerives P Δ (⟨B, gB⟩ :: ⟨A, gA⟩ :: Γb) M (.comp C)) :
      GDerives P Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} {g₁ g₂ : Grade} (hs : GSplit P Γ Γs Γb)
      (hV : GDerives P Δ Γs V (.val (.sum A B))) (hg₁ : g₁.live = true) (hg₂ : g₂.live = true)
      (h₁ : GDerives P Δ (⟨A, g₁⟩ :: Γb) M₁ (.comp C))
      (h₂ : GDerives P Δ (⟨B, g₂⟩ :: Γb) M₂ (.comp C)) :
      GDerives P Δ Γ (.case V M₁ M₂) (.comp C)
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : GSplit P Γ Γ₁ Γ₂) (hV : GDerives P Δ Γ₁ V (.val .zero)) :
      GDerives P Δ Γ (absurdE V) (.comp C)
  | allI {Δ Γ x b M S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ GCtx.erase Γ, s.live = true → ¬ VFree x s.ty)
      (h : GDerives P (Δ.extend x b) (⟨S, .erased⟩ :: Γ) M (.comp C)) :
      GDerives P Δ Γ (.val (.lam M)) (.comp (.all x b C))
  | allE {Δ Γ M x b a C} (h : GDerives P Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
      GDerives P Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))
  /-- Promotion of `thunk M : U (F A)`: from `Γ`, at `ω · Γ`. -/
  | bangThunkF {Δ Γ M A} (hok : GOk P (GCtx.scale ω Γ)) (hp : PromOk P Γ)
      (h : GDerives P Δ (⟨.unit, .erased⟩ :: Γ) M (.comp (.ret A))) :
      GDerives P Δ (GCtx.scale ω Γ) (.val (.lam M)) (.val (.bang (.thunk (.ret A))))
  /-- Promotion of a λ-value `V : C`: from `Γ`, at `ω · Γ`. -/
  | bangThunkV {Δ Γ N C} (hok : GOk P (GCtx.scale ω Γ)) (hp : PromOk P Γ)
      (hC : C.isRet = false) (h : GDerives P Δ Γ (.val (.lam N)) (.comp C)) :
      GDerives P Δ (GCtx.scale ω Γ) (.val (.lam N)) (.val (.bang (.thunk C)))
  | bangE {Δ Γ e A} (h : GDerives P Δ Γ e (.val (.bang A))) : GDerives P Δ Γ e (.val A)
  | copyBang {Δ Γ A} (hΓ : GDead P Γ) :
      GDerives P Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : GDead P Γ) :
      GDerives P Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  | boxI {Δ Γ e a A} (h : GDerives P Δ Γ e (.val A)) (hΓ : CtxOutlives Δ (GCtx.erase Γ) a) :
      GDerives P Δ Γ e (.val (.box a A))
  | boxE {Δ Γ e a A} (h : GDerives P Δ Γ e (.val (.box a A))) : GDerives P Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : GDerives P Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      GDerives P Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : GDerives P Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      GDerives P Δ Γ e (.val (.mut a A))
  | alloc {Δ Γ A} (hΓ : GDead P Γ) :
      GDerives P Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : GDead P Γ) :
      GDerives P Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : GDead P Γ) : GDerives P Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : GDead P Γ) : GDerives P Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : GDead P Γ) : GDerives P Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : GDead P Γ) : GDerives P Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : GDead P Γ) : GDerives P Δ Γ forget (.val axForgetUnkTy)
  | lit {Δ Γ} (c : IntLit) (hΓ : GDead P Γ) :
      GDerives P Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width))
  | hostOp {Δ Γ} (op : HostOp) (hΓ : GDead P Γ) :
      GDerives P Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op)))
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : GDead P Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      GDerives P Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : GDead P Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      GDerives P Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : GDead P Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      GDerives P Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : GDead P Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      GDerives P Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : GDead P Γ) :
      GDerives P Δ Γ withswap (.val (axWithswapTy a A B))
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : GSplit P Γ Γ₁ Γ₂)
      (ha : GDerives P Δ Γ₁ a (.val A)) (hf : GDerives P Δ Γ₂ f (.val (.lolli A B))) :
      GDerives P Δ Γ (.app f a) (.val B)
  | allEV {Δ Γ e x b a A} (h : GDerives P Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      GDerives P Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  | ofRet {Δ Γ e A} (h : GDerives P Δ Γ e (.comp (.ret A))) : GDerives P Δ Γ e (.val A)
  | roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : GDerives P Δ Γ e (.val (VTy.inst (.mu A) A))) : GDerives P Δ Γ e (.val (.mu A))
  | unroll {Δ Γ e A} (h : GDerives P Δ Γ e (.val (.mu A))) :
      GDerives P Δ Γ e (.val (VTy.inst (.mu A) A))
  | foldImm {Δ Γ} (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy) (hΓ : GDead P Γ)
      (hF : F.WF) (hG : F.Guarded) (hyM : ¬ VFree y (.mu F.ty)) (hyR : ¬ VFree y R)
      (hR : ∀ Δ' a, VOutlives Δ' a R) :
      GDerives P Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))
  | foldOwn {Δ Γ} (F : FShape) (R : VTy) (hΓ : GDead P Γ) (hF : F.WF) (hG : F.Guarded) :
      GDerives P Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))
  | foldReuse {Δ Γ} (F : FShape) (R : VTy) (hΓ : GDead P Γ) (hF : F.WF) (hG : F.Guarded) :
      GDerives P Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))
  | nuIn {Δ Γ e C} (hC : C.NuOk) (h : GDerives P Δ Γ e (.comp C.unroll)) :
      GDerives P Δ Γ e (.comp (.nu C))
  | nuOut {Δ Γ e C} (hC : C.NuOk) (h : GDerives P Δ Γ e (.comp (.nu C))) :
      GDerives P Δ Γ e (.comp C.unroll)
  | unfoldN {Δ Γ} (C : CTy) (S : VTy) (hC : C.NuOk) (hΓ : GDead P Γ) :
      GDerives P Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))
  /-- Erased abstraction: the binder at `[0,0]`; at run time it receives `inj₁ ()`. -/
  | lam0 {Δ Γ M A C} (he : P.erasure = true)
      (h : GDerives P Δ (⟨A, .erased⟩ :: Γ) M (.comp C)) :
      GDerives P Δ Γ (.val (.lam M)) (.comp (.arr (ghost A) C))
  /-- Erased application: the argument `x_i : A` is mentioned at grade `0`, so it costs nothing
  (any grade, `[0,0]` included); at run time `inj₁ ()` is passed. -/
  | app0 {Δ : LifeCtx} {Γ : GCtx} {M : Expr} {i : Nat} {A : VTy} {C : CTy} (he : P.erasure = true)
      (hi : ∃ g : Grade, Γ[i]? = some (⟨A, g⟩ : GSlot))
      (hM : GDerives P Δ Γ M (.comp (.arr (ghost A) C))) :
      GDerives P Δ Γ (.app M (.val ghostV)) (.comp C)

/-! ### Graded to Core -/

theorem erase_cons_live {A : VTy} {g : Grade} {Γ : GCtx} (hg : g.live = true) :
    GCtx.erase (⟨A, g⟩ :: Γ) = ⟨A, true⟩ :: GCtx.erase Γ := by simp [hg]

/-- **Graded to Core.**  A derivation under `Profile.core` is a `CDerives` derivation of the
erasure. -/
theorem GDerives.toCore {Δ : LifeCtx} {Γ : GCtx} {e : Expr} {j : Jdg}
    (h : GDerives Profile.core Δ Γ e j) : CDerives Δ (GCtx.erase Γ) e j := by
  induction h with
  | var h => exact .var h.toSoloP
  | unitI h => exact .unitI h.toDeadP
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI hs.toSplitP ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ hg _ ihM ihN =>
      rw [erase_cons_live hg] at ihN; exact .bind hs.toSplitP ihM ihN
  | force h => exact .force h.toSoloP
  | lam hg _ ih => rw [erase_cons_live hg] at ih; exact .lam ih
  | app hs _ hx ih => exact .app hs.toSplitP ih hx.toSoloP
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE hs.toSplitP ihV ihM
  | tensorE hs _ hgA hgB _ ihV ihM =>
      rw [erase_cons_live hgB, erase_cons_live hgA] at ihM; exact .tensorE hs.toSplitP ihV ihM
  | sumE hs _ hg₁ hg₂ _ _ ihV ih₁ ih₂ =>
      rw [erase_cons_live hg₁] at ih₁; rw [erase_cons_live hg₂] at ih₂
      exact .sumE hs.toSplitP ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE hs.toSplitP ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx hΓx ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF _ hp _ ih => rw [erase_scale_ω]; exact .bangThunkF hp.toPersistent ih
  | bangThunkV _ hp hC _ ih => rw [erase_scale_ω]; exact .bangThunkV hp.toPersistent hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang hΓ.toDeadP
  | forgetBang hΓ => exact .forgetBang hΓ.toDeadP
  | boxI _ hΓ ih => exact .boxI ih hΓ
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc hΓ.toDeadP
  | free hΓ => exact .free hΓ.toDeadP
  | swap hΓ => exact .swap hΓ.toDeadP
  | copy hΓ => exact .copy hΓ.toDeadP
  | forgetImm hΓ => exact .forgetImm hΓ.toDeadP
  | forgetMut hΓ => exact .forgetMut hΓ.toDeadP
  | forgetUnk hΓ => exact .forgetUnk hΓ.toDeadP
  | lit c hΓ => exact .lit c hΓ.toDeadP
  | hostOp op hΓ => exact .hostOp op hΓ.toDeadP
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x hΓ.toDeadP hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x hΓ.toDeadP hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x hΓ.toDeadP hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x hΓ.toDeadP hx hf₁ hf₂
  | withswap hΓ => exact .withswap hΓ.toDeadP
  | lolliE hs _ _ iha ihf => exact .lolliE hs.toSplitP iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact .foldImm F y c R hΓ.toDeadP hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R hΓ.toDeadP hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R hΓ.toDeadP hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC hΓ.toDeadP
  | lam0 he => exact absurd he (by decide)
  | app0 he => exact absurd he (by decide)

/-! ### Core to graded -/

/-- **Core to graded.**  A `CDerives` derivation is a `Profile.core` derivation of the context
graded by the defaults. -/
theorem CDerives.toGraded {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : GDerives Profile.core Δ (GCtx.embed Γ) e j := by
  induction h with
  | var h => exact .var (SoloP.toGSolo h)
  | unitI h => exact .unitI (DeadP.toGDead h)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (SplitP.toGSplit hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (SplitP.toGSplit hs) ihM (dflt_live _) ihN
  | force h => exact .force (SoloP.toGSolo h)
  | lam _ ih => exact .lam (dflt_live _) ih
  | app hs _ hx ih => exact .app (SplitP.toGSplit hs) ih (SoloP.toGSolo hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (SplitP.toGSplit hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (SplitP.toGSplit hs) ihV (dflt_live _) (dflt_live _) ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      exact .sumE (SplitP.toGSplit hs) ihV (dflt_live _) (dflt_live _) ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (SplitP.toGSplit hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (by rw [erase_embed]; exact hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih =>
      obtain ⟨h₁, h₂, h₃⟩ := Persistent.toGraded hp
      exact h₁ ▸ GDerives.bangThunkF h₂ h₃ ih
  | bangThunkV hp hC _ ih =>
      obtain ⟨h₁, h₂, h₃⟩ := Persistent.toGraded hp
      exact h₁ ▸ GDerives.bangThunkV h₂ h₃ hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (DeadP.toGDead hΓ)
  | forgetBang hΓ => exact .forgetBang (DeadP.toGDead hΓ)
  | boxI _ hΓ ih => exact .boxI ih (by rw [erase_embed]; exact hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (DeadP.toGDead hΓ)
  | free hΓ => exact .free (DeadP.toGDead hΓ)
  | swap hΓ => exact .swap (DeadP.toGDead hΓ)
  | copy hΓ => exact .copy (DeadP.toGDead hΓ)
  | forgetImm hΓ => exact .forgetImm (DeadP.toGDead hΓ)
  | forgetMut hΓ => exact .forgetMut (DeadP.toGDead hΓ)
  | forgetUnk hΓ => exact .forgetUnk (DeadP.toGDead hΓ)
  | lit c hΓ => exact .lit c (DeadP.toGDead hΓ)
  | hostOp op hΓ => exact .hostOp op (DeadP.toGDead hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (DeadP.toGDead hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x (DeadP.toGDead hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (DeadP.toGDead hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (DeadP.toGDead hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (DeadP.toGDead hΓ)
  | lolliE hs _ _ iha ihf => exact .lolliE (SplitP.toGSplit hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (DeadP.toGDead hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (DeadP.toGDead hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (DeadP.toGDead hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (DeadP.toGDead hΓ)

/-- **The equivalence** on the fragment Core has: `CDerives` at `Γ` is `GDerives Profile.core`
at `Γ` graded by the defaults, and a `Profile.core` derivation at any graded context is a
`CDerives` derivation of its erasure. -/
theorem cderives_iff_graded {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} :
    CDerives Δ Γ e j ↔ GDerives Profile.core Δ (GCtx.embed Γ) e j :=
  ⟨CDerives.toGraded, fun h => erase_embed Γ ▸ h.toCore⟩

/-- The premise-level equivalences behind it. -/
theorem splitP_iff {Γ Γ₁ Γ₂ : Ctx VTy} :
    Ctx.SplitP Γ Γ₁ Γ₂ ↔ GSplit Profile.core (GCtx.embed Γ) (GCtx.embed Γ₁) (GCtx.embed Γ₂) :=
  ⟨SplitP.toGSplit, fun h => by
    have := h.toSplitP; rwa [erase_embed, erase_embed, erase_embed] at this⟩

theorem deadP_iff {Γ : Ctx VTy} : Ctx.DeadP Γ ↔ GDead Profile.core (GCtx.embed Γ) :=
  ⟨DeadP.toGDead, fun h => by have := h.toDeadP; rwa [erase_embed] at this⟩

theorem soloP_iff {Γ : Ctx VTy} {i : Nat} {T : VTy} :
    Ctx.SoloP Γ i T ↔ GSolo Profile.core (GCtx.embed Γ) i T :=
  ⟨SoloP.toGSolo, fun h => by have := h.toSoloP; rwa [erase_embed] at this⟩

theorem persistent_iff {Γ : Ctx VTy} :
    Persistent Γ ↔ (GCtx.scale ω (GCtx.embed Γ) = GCtx.embed Γ ∧
      GOk Profile.core (GCtx.scale ω (GCtx.embed Γ)) ∧ PromOk Profile.core (GCtx.embed Γ)) :=
  ⟨Persistent.toGraded, fun ⟨_, _, h⟩ => by have := h.toPersistent; rwa [erase_embed] at this⟩

/-! ### Profiles are ordered -/

/-- `P ≤ Q`: every type condition of `P` implies `Q`'s. -/
structure Profile.Le (P Q : Profile) : Prop where
  drop : ∀ T, P.drop T = true → Q.drop T = true
  prom : ∀ T, P.prom T = true → Q.prom T = true
  erasure : P.erasure = true → Q.erasure = true

theorem Profile.core_le_graded : Profile.core.Le Profile.graded :=
  ⟨fun _ h => VTy.forgettable_of_persistent h, fun _ h => VTy.persistent_of_isBang h,
    fun h => absurd h (by decide)⟩

section mono
variable {P Q : Profile}

theorem Profile.Le.ok (hPQ : P.Le Q) {g : Grade} {T : VTy} (h : P.Ok g T) : Q.Ok g T := by
  unfold Profile.Ok at *
  have hd := hPQ.drop T
  generalize P.drop T = f at h hd
  generalize Q.drop T = f' at hd ⊢
  generalize T.persistent = p at h ⊢
  revert h hd; cases f <;> cases f' <;> cases p <;> cases g <;> decide

theorem Profile.Le.split (hPQ : P.Le Q) : ∀ {Γ Γ₁ Γ₂ : GCtx}, GSplit P Γ Γ₁ Γ₂ → GSplit Q Γ Γ₁ Γ₂
  | _, _, _, .nil => .nil
  | _, _, _, .cons hg hok h => .cons hg (hPQ.ok hok) (Profile.Le.split hPQ h)

theorem Profile.Le.drop' (hPQ : P.Le Q) {s : GSlot} (h : GDrop P s) : GDrop Q s := ⟨h.1, hPQ.ok h.2⟩

theorem Profile.Le.dead (hPQ : P.Le Q) {Γ : GCtx} (h : GDead P Γ) : GDead Q Γ := fun s hs => hPQ.drop' (h s hs)

theorem Profile.Le.solo (hPQ : P.Le Q) : ∀ {Γ : GCtx} {i : Nat} {T : VTy}, GSolo P Γ i T → GSolo Q Γ i T
  | _, _, _, .here hl hok hd => .here hl (hPQ.ok hok) (hPQ.dead hd)
  | _, _, _, .there hs h => .there (hPQ.drop' hs) (Profile.Le.solo hPQ h)

theorem Profile.Le.gok (hPQ : P.Le Q) {Γ : GCtx} (h : GOk P Γ) : GOk Q Γ := fun s hs => hPQ.ok (h s hs)

theorem Profile.Le.promOk (hPQ : P.Le Q) {Γ : GCtx} (h : PromOk P Γ) : PromOk Q Γ :=
  fun s hs hl => hPQ.prom _ (h s hs hl)

/-- A derivation under `P` is one under every `Q ≥ P`. -/
theorem GDerives.mono (hPQ : P.Le Q) {Δ : LifeCtx} {Γ : GCtx} {e : Expr} {j : Jdg}
    (h : GDerives P Δ Γ e j) : GDerives Q Δ Γ e j := by
  induction h with
  | var h => exact .var (hPQ.solo h)
  | unitI h => exact .unitI (hPQ.dead h)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (hPQ.split hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ hg _ ihM ihN => exact .bind (hPQ.split hs) ihM hg ihN
  | force h => exact .force (hPQ.solo h)
  | lam hg _ ih => exact .lam hg ih
  | app hs _ hx ih => exact .app (hPQ.split hs) ih (hPQ.solo hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (hPQ.split hs) ihV ihM
  | tensorE hs _ hgA hgB _ ihV ihM => exact .tensorE (hPQ.split hs) ihV hgA hgB ihM
  | sumE hs _ hg₁ hg₂ _ _ ihV ih₁ ih₂ => exact .sumE (hPQ.split hs) ihV hg₁ hg₂ ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (hPQ.split hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx hΓx ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hok hp _ ih => exact .bangThunkF (hPQ.gok hok) (hPQ.promOk hp) ih
  | bangThunkV hok hp hC _ ih => exact .bangThunkV (hPQ.gok hok) (hPQ.promOk hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (hPQ.dead hΓ)
  | forgetBang hΓ => exact .forgetBang (hPQ.dead hΓ)
  | boxI _ hΓ ih => exact .boxI ih hΓ
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (hPQ.dead hΓ)
  | free hΓ => exact .free (hPQ.dead hΓ)
  | swap hΓ => exact .swap (hPQ.dead hΓ)
  | copy hΓ => exact .copy (hPQ.dead hΓ)
  | forgetImm hΓ => exact .forgetImm (hPQ.dead hΓ)
  | forgetMut hΓ => exact .forgetMut (hPQ.dead hΓ)
  | forgetUnk hΓ => exact .forgetUnk (hPQ.dead hΓ)
  | lit c hΓ => exact .lit c (hPQ.dead hΓ)
  | hostOp op hΓ => exact .hostOp op (hPQ.dead hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (hPQ.dead hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x (hPQ.dead hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (hPQ.dead hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (hPQ.dead hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (hPQ.dead hΓ)
  | lolliE hs _ _ iha ihf => exact .lolliE (hPQ.split hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact .foldImm F y c R (hPQ.dead hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (hPQ.dead hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (hPQ.dead hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (hPQ.dead hΓ)
  | lam0 he _ ih => exact .lam0 (hPQ.erasure he) ih
  | app0 he hi _ ih => exact .app0 (hPQ.erasure he) hi ih

end mono

end BoCa.Fig16.LogRel.Core.Graded

end
