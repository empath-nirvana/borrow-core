import CBPVCore.Axioms

/-!
# CBPVCore — Fundamental Property and adequacy

`CDerives Δ Γ e j`: the CBPV typing judgment on BoLo expressions, with `j` a value judgment
`val A` or a computation judgment `comp C`.  Values are typed in A-normal form: the scrutinee of
an elimination is a value, the argument of an application a variable.  Beside the CBPV formers
it has the lifetime `∀`, the `!` rules, `[]I`/`[]E`, `⊑imm`/`⊑mut`, and one constant per borrow
axiom at `cbv` of its BoCa type.  `fundamentalC` proves every rule sound at `SemV`/`SemC`;
`adequacyC` runs a closed `F 1` computation to `()`.
-/

namespace CBPVCore
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

/-- A judgment form: a value at `A`, or a computation at `C`. -/
inductive Jdg where
  | val (A : VTy)
  | comp (C : CTy)

/-- The CBPV typing judgment. -/
inductive CDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop where
  | var {Δ Γ i A} (h : Ctx.Solo Γ i A) : CDerives Δ Γ (.var i) (.val A)
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : CDerives Δ Γ (.val .unit) (.val .unit)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} (hs : Ctx.Split Γ Γ₁ Γ₂)
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
  | bind {Δ Γ Γ₁ Γ₂ M N A C} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (hM : CDerives Δ Γ₁ M (.comp (.ret A))) (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
      CDerives Δ Γ (.app (.val (.lam N)) M) (.comp C)
  /-- `force x`: `x ()` at `F A`, `x` itself at any other computation type. -/
  | force {Δ Γ i C} (h : Ctx.Solo Γ i (.thunk C)) :
      CDerives Δ Γ (forceE C (.var i)) (.comp C)
  | lam {Δ Γ M A C} (h : CDerives Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
      CDerives Δ Γ (.val (.lam M)) (.comp (.arr A C))
  | app {Δ Γ Γ₁ Γ₂ M i A C} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (hM : CDerives Δ Γ₁ M (.comp (.arr A C))) (hx : Ctx.Solo Γ₂ i A) :
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
  | unitE {Δ Γ Γ₁ Γ₂ V M C} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (hV : CDerives Δ Γ₁ V (.val .unit)) (hM : CDerives Δ Γ₂ M (.comp C)) :
      CDerives Δ Γ (.seq V M) (.comp C)
  | tensorE {Δ Γ Γp Γb V M A B C} (hs : Ctx.Split Γ Γp Γb)
      (hV : CDerives Δ Γp V (.val (.tensor A B)))
      (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
      CDerives Δ Γ (.letpair V M) (.comp C)
  | sumE {Δ Γ Γs Γb V M₁ M₂ A B C} (hs : Ctx.Split Γ Γs Γb)
      (hV : CDerives Δ Γs V (.val (.sum A B)))
      (h₁ : CDerives Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
      (h₂ : CDerives Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
      CDerives Δ Γ (.case V M₁ M₂) (.comp C)
  /-- `absurd V : C` for `V : 0`, at any rest of the context. -/
  | zeroE {Δ Γ Γ₁ Γ₂ V C} (hs : Ctx.Split Γ Γ₁ Γ₂) (hV : CDerives Δ Γ₁ V (.val .zero)) :
      CDerives Δ Γ (absurdE V) (.comp C)
  /-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`. -/
  | allI {Δ Γ x b M C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : CDerives (Δ.extend x b) (⟨.unit, false⟩ :: Γ) M (.comp C)) :
      CDerives Δ Γ (.val (.lam M)) (.comp (.all x b C))
  /-- `M [] : F (T[@a/'x])⁺`, at `F` of a translated type. -/
  | allE {Δ Γ M x b a} {T : Ty} (h : CDerives Δ Γ M (.comp (.all x b (.ret (cbv T)))))
      (hlt : Δ.EntailsLt a b) :
      CDerives Δ Γ (.app M (.val .unit)) (.comp (.ret (cbv (Ty.instLife x a T))))
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
  | copyBang {Δ Γ A} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit))))
  /-- `[]I`, at a translated type, at a context whose live slots are a translated context's. -/
  | boxI {Δ Γ e a} {Γ' : Ctx Ty} {T : Ty} (hE : LiveEq Γ (cbvCtx Γ'))
      (h : CDerives Δ Γ e (.val (cbv T))) (hΓ : Ctx.Outlives Δ Γ' a) :
      CDerives Δ Γ e (.val (.box a (cbv T)))
  | boxE {Δ Γ e a A} (h : CDerives Δ Γ e (.val (.box a A))) : CDerives Δ Γ e (.val A)
  | immSub {Δ Γ e a b A} (h : CDerives Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      CDerives Δ Γ e (.val (.imm a A))
  | mutSub {Δ Γ e a b A} (h : CDerives Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      CDerives Δ Γ e (.val (.mut a A))
  /-- The borrow axioms, each at `cbv` of its BoCa type. -/
  | alloc {Δ Γ} {T : Ty} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ (.val (.prim .alloc)) (.val (cbv (.lolli T (.ref T))))
  | free {Δ Γ} {T : Ty} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ (.val (.prim .free)) (.val (cbv (.lolli (.ref T) T)))
  | swap {Δ Γ} {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ swap (.val (cbv (axSwapTy T₁ T₂)))
  | copy {Δ Γ a} {T : Ty} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ copy (.val (cbv (axCopyTy a T)))
  | forgetImm {Δ Γ a} {T : Ty} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ forget (.val (cbv (axForgetImmTy a T)))
  | forgetMut {Δ Γ a} {T : Ty} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ forget (.val (cbv (axForgetMutTy a T)))
  | forgetUnk {Δ Γ} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val (cbv axForgetUnkTy))
  | withbor1 {Δ Γ} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hsc₁ : T₁.scopedB Δ = true) (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
      CDerives Δ Γ withbor (.val (cbv (axWithbor1Ty x Δ.meetOfDom T₁ T₂)))
  | withbor2 {Δ Γ} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ BoCa.Outlives Δ T₁ b)
      (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
      CDerives Δ Γ withbor (.val (cbv (axWithbor2Ty x Δ.meetOfDom T₁ T₂)))
  | withbor3 {Δ Γ a} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
      CDerives Δ Γ withbor (.val (cbv (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)))
  | withload {Δ Γ a} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
      CDerives Δ Γ withload (.val (cbv (axWithloadTy a x Δ.meetOfDom T₁ T₂)))
  | withswap {Δ Γ a} {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ withswap (.val (cbv (axWithswapTy a T₁ T₂)))

/-- The semantic judgment at a judgment form. -/
def SemJ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .val A => SemV Δ Γ e A
  | .comp C => SemC Δ Γ e C

/-- **Fundamental Property** of the CBPV judgment over the typed world. -/
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
  | app hs _ hx ih => exact app_compatC hs ih hx
  | withI _ _ ihM ihN => exact withI_compatC ihM ihN
  | proj₁ _ ih => exact proj₁_compatC ih
  | proj₂ _ ih => exact proj₂_compatC ih
  | topI => exact topI_compatC
  | unitE hs _ _ ihV ihM => exact unitE_compatC hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatC hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatC hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatC hs ihV
  | allI hbx hΔx hΓx _ ih => exact allI_compatC hbx hΔx hΓx ih
  | allE _ hlt ih => exact allE_compatC ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatC hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatC hp hC ih
  | bangE _ ih => exact bangE_compatC ih
  | copyBang hΓ => exact copyBang_compatC hΓ
  | forgetBang hΓ => exact forgetBang_compatC hΓ
  | boxI hE _ hΓ ih => exact boxI_compatC hE ih hΓ
  | boxE _ ih => exact boxE_compatC ih
  | immSub _ hle ih => exact immSub_compatC ih hle
  | mutSub _ hle ih => exact mutSub_compatC ih hle
  | alloc hΓ => exact alloc_compatC hΓ
  | free hΓ => exact free_compatC hΓ
  | swap hΓ => exact swap_compatC hΓ
  | copy hΓ => exact copy_compatC hΓ
  | forgetImm hΓ => exact forgetImm_compatC hΓ
  | forgetMut hΓ => exact forgetMut_compatC hΓ
  | forgetUnk hΓ => exact forgetUnk_compatC hΓ
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact withbor1_compatC x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2_compatC x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatC x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatC x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatC hΓ

/-- The call-by-value embedding, semantically: a BoLo derivation is a CBPV value at the
translation, at the translated context (6.151 at `SemX`, carried by `semX_iff_semV`). -/
theorem fundamentalCBV {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (hD : DerivesWf Δ Γ e T)
    (hΔ : Δ.Ok) (hΓ : Ctx.ScopedB Δ Γ) : SemV Δ (cbvCtx Γ) e (cbv T) :=
  (semX_iff_semV Δ Γ e T).mp (fundamental Δ Γ e T hD hΔ hΓ)

/-- At the empty context, `SemC … (F 1)` is the typed world's `SemX … 1`. -/
theorem semX_of_semC_unit {e : Expr} (h : SemC LifeCtx.empty [] e (.ret .unit)) :
    SemX LifeCtx.empty ([] : Ctx Ty) e .unit := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hs⟩ := gDenX_iff.mp hg
  have hs' : gSepC ls δ [] γ ρ := by cases γ <;> exact hs
  exact h δ γ ls ρ hδ (gDenC_mk hlen hs')

/-- **Adequacy**: a closed computation of type `F 1` runs from the empty memory to `()` and the
empty memory.  `fundamentalC` composed with the typed world's `corollary33`. -/
theorem adequacyC {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit))) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  Typed.corollary33 e (semX_of_semC_unit (fundamentalC h))

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

end
end CBPVCore
