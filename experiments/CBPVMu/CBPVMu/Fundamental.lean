import CBPVMu.Compat
import Support.LogicalRelation.Adequacy

/-!
# CBPVMu — Fundamental Property and adequacy

`CDerives Δ Γ e j`: the CBPV typing judgment on BoLo expressions, with `j` a value judgment
`val A` or a computation judgment `comp C`, in A-normal form.  Beside the CBPV formers it has
the lifetime `∀` (`∀E` at every `C`), the `!` rules, `[]I`/`[]E` (`[]I` at every value type),
`⊑imm`/`⊑mut`, one constant per borrow axiom at arbitrary value-type payloads, and three
call-by-value derived forms (`lolliE`, `allEV`, `ofRet`) that the embedding of BoLo uses.
`fundamentalC` proves every rule sound at `SemV`/`SemC`; `adequacyC` runs a closed `F 1`
computation to `()` from the empty memory.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

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
  | copyBang {Δ Γ A} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))))
  | forgetBang {Δ Γ A} (hΓ : Ctx.Dead Γ) :
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
  | alloc {Δ Γ A} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))
  | free {Δ Γ A} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))
  | swap {Δ Γ A B} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ swap (.val (axSwapTy A B))
  | copy {Δ Γ a A} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ copy (.val (axCopyTy a A))
  | forgetImm {Δ Γ a A} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val (axForgetImmTy a A))
  | forgetMut {Δ Γ a A} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val (axForgetMutTy a A))
  | forgetUnk {Δ Γ} (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val axForgetUnkTy)
  | withbor1 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))
  | withbor2 {Δ Γ A B} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))
  | withbor3 {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))
  | withload {Δ Γ a A B} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
      CDerives Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))
  | withswap {Δ Γ a A B} (hΓ : Ctx.Dead Γ) :
      CDerives Δ Γ withswap (.val (axWithswapTy a A B))
  -- Call-by-value derived forms: BoLo's application and `∀E` on arbitrary subterms, and the
  -- reading of a computation of `F A` as a value-judged expression at `A`.
  /-- Call-by-value application `f a`, both arbitrary, at `VTy.lolli` (`lolliE_compatX`). -/
  | lolliE {Δ Γ Γ₁ Γ₂ f a A B} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : CDerives Δ Γ₁ a (.val A)) (hf : CDerives Δ Γ₂ f (.val (.lolli A B))) :
      CDerives Δ Γ (.app f a) (.val B)
  /-- Call-by-value `∀E`: `e []` for `e` at `VTy.all x b A` (`allE_compatX`). -/
  | allEV {Δ Γ e x b a A} (h : CDerives Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
      CDerives Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))
  /-- A computation of `F A` is a value-judged expression at `A`: `SemV` is `SemC` at `F A`. -/
  | ofRet {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.ret A))) : CDerives Δ Γ e (.val A)

/-- The semantic judgment at a judgment form. -/
def SemJ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .val A => SemV Δ Γ e A
  | .comp C => SemC Δ Γ e C

/-- **Fundamental Property** of the CBPV judgment over the typed world at CBPV types. -/
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
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact withbor1_compatX x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatX hΓ
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih

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
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
      TW.empty htg
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
empty memory. -/
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

end BoCa.Fig16.LogRel.CBPVMu

end
