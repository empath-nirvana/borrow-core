import Affine.Dtor

/-!
# Affine — the affine judgment and its elaboration into `CDerives`

`ADerives Δ Γ e e' j` reads: the source term `e` is affinely typed at `j`, and `e'` is its
elaboration, `e` with a destructor call inserted at every discard. It is `CDerives` with one
more rule:

    drop:   Γ = Γ₁, Γ₂    Γ₁ = x : T    T droppable    Γ₂ ⊢ e ⤳ e' : C
            ───────────────────────────────────────────────────────────
            Γ ⊢ e ⤳ (dtorE T x; e') : C

and every rule of `CDerives` with a subderivation repeated at `ADerives` premises, so a discard
may sit under any former: at the end of a scope, in one arm of a `case`, inside a `λ`, a `thunk`
or a callback. `core` embeds every `CDerives` derivation unchanged.

**The elaboration theorem** (`ADerives.elab`): the elaborated term is a `CDerives` derivation.
The `drop` case is `unitE` over `lolliE` of `dtor_wf`; every other case is the rule it copies.
No case inverts `CDerives` (decision 21), and nothing is added to `CDerives` (decision 19).
Soundness and leak freedom are `fundamentalC` and `adequacyC` applied to the elaborated term
(`fundamentalA`, `adequacyA`, `runsA`): no model change and no new invariant.

**Borrows** (`owner_not_shared`, `dtorE_imm`, `dtorE_mut`). A lent owner is not in scope during
the loan: `withbor r cb` takes `r` by a context split, and a split sends a live `Ref A` to one
side only, so the callback's context, where a `drop` would have to find it, has it dead. A
borrow handed to the callback is droppable, and its destructor is `forget`: ending a loan early
frees nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Affine
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `dtorE T x; e`: the discard of the variable `i` at `T`, before `e`. -/
def dropE (T : VTy) (i : Nat) (e : Expr) : Expr := .seq (.app (dtorE T) (.var i)) e

/-- The affine judgment, with the elaborated term as its second index. -/
inductive ADerives : LifeCtx → Ctx VTy → Expr → Expr → Jdg → Prop where
  /-- Every `CDerives` derivation, with nothing inserted. -/
  | core {Δ Γ e j} (h : CDerives Δ Γ e j) : ADerives Δ Γ e e j
  /-- Discard a droppable live slot before a computation. -/
  | drop {Δ Γ Γ₁ Γ₂ i T e e' C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i T)
      (hT : HasDtor T) (h : ADerives Δ Γ₂ e e' (.comp C)) :
      ADerives Δ Γ e (dropE T i e') (.comp C)
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₁' e₂ e₂' A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (h₁ : ADerives Δ Γ₁ e₁ e₁' (.val A)) (h₂ : ADerives Δ Γ₂ e₂ e₂' (.val B)) :
      ADerives Δ Γ (.pair e₁ e₂) (.pair e₁' e₂') (.val (.tensor A B))
  | sumI₁ {Δ Γ e e' A B} (h : ADerives Δ Γ e e' (.val A)) :
      ADerives Δ Γ (.inj₁ e) (.inj₁ e') (.val (.sum A B))
  | sumI₂ {Δ Γ e e' A B} (h : ADerives Δ Γ e e' (.val B)) :
      ADerives Δ Γ (.inj₂ e) (.inj₂ e') (.val (.sum A B))
  | thunkF {Δ Γ M M' A} (h : ADerives Δ (⟨.unit, false⟩ :: Γ) M M' (.comp (.ret A))) :
      ADerives Δ Γ (.val (.lam M)) (.val (.lam M')) (.val (.thunk (.ret A)))
  | thunkV {Δ Γ N N' C} (hC : C.isRet = false)
      (h : ADerives Δ Γ (.val (.lam N)) (.val (.lam N')) (.comp C)) :
      ADerives Δ Γ (.val (.lam N)) (.val (.lam N')) (.val (.thunk C))
  | ret {Δ Γ V V' A} (h : ADerives Δ Γ V V' (.val A)) : ADerives Δ Γ V V' (.comp (.ret A))
  | bind {Δ Γ Γ₁ Γ₂ M M' N N' A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : ADerives Δ Γ₁ M M' (.comp (.ret A)))
      (hN : ADerives Δ (⟨A, true⟩ :: Γ₂) N N' (.comp C)) :
      ADerives Δ Γ (.app (.val (.lam N)) M) (.app (.val (.lam N')) M') (.comp C)
  | lam {Δ Γ M M' A C} (h : ADerives Δ (⟨A, true⟩ :: Γ) M M' (.comp C)) :
      ADerives Δ Γ (.val (.lam M)) (.val (.lam M')) (.comp (.arr A C))
  | app {Δ Γ Γ₁ Γ₂ M M' i A C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hM : ADerives Δ Γ₁ M M' (.comp (.arr A C))) (hx : Ctx.SoloP Γ₂ i A) :
      ADerives Δ Γ (.app M (.var i)) (.app M' (.var i)) (.comp C)
  | withI {Δ Γ M M' N N' C D} (hM : ADerives Δ (withCtx Γ) M M' (.comp C))
      (hN : ADerives Δ (withCtx Γ) N N' (.comp D)) :
      ADerives Δ Γ (withPair M N) (withPair M' N') (.comp (.amp C D))
  | proj₁ {Δ Γ M M' C D} (h : ADerives Δ Γ M M' (.comp (.amp C D))) :
      ADerives Δ Γ (.app M (.val (.inj₁ .unit))) (.app M' (.val (.inj₁ .unit))) (.comp C)
  | proj₂ {Δ Γ M M' C D} (h : ADerives Δ Γ M M' (.comp (.amp C D))) :
      ADerives Δ Γ (.app M (.val (.inj₂ .unit))) (.app M' (.val (.inj₂ .unit))) (.comp D)
  | unitE {Δ Γ Γ₁ Γ₂ V V' M M' C} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (hV : ADerives Δ Γ₁ V V' (.val .unit)) (hM : ADerives Δ Γ₂ M M' (.comp C)) :
      ADerives Δ Γ (.seq V M) (.seq V' M') (.comp C)
  | tensorE {Δ Γ Γp Γb V V' M M' A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : ADerives Δ Γp V V' (.val (.tensor A B)))
      (hM : ADerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M M' (.comp C)) :
      ADerives Δ Γ (.letpair V M) (.letpair V' M') (.comp C)
  | sumE {Δ Γ Γs Γb V V' M₁ M₁' M₂ M₂' A B C} (hs : Ctx.SplitP Γ Γs Γb)
      (hV : ADerives Δ Γs V V' (.val (.sum A B)))
      (h₁ : ADerives Δ (⟨A, true⟩ :: Γb) M₁ M₁' (.comp C))
      (h₂ : ADerives Δ (⟨B, true⟩ :: Γb) M₂ M₂' (.comp C)) :
      ADerives Δ Γ (.case V M₁ M₂) (.case V' M₁' M₂') (.comp C)
  | zeroE {Δ Γ Γ₁ Γ₂ V V' C} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : ADerives Δ Γ₁ V V' (.val .zero)) :
      ADerives Δ Γ (absurdE V) (absurdE V') (.comp C)
  | allI {Δ Γ x b M M' S C} (hbx : b.mentions x = false)
      (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
      (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
      (h : ADerives (Δ.extend x b) (⟨S, false⟩ :: Γ) M M' (.comp C)) :
      ADerives Δ Γ (.val (.lam M)) (.val (.lam M')) (.comp (.all x b C))
  | allE {Δ Γ M M' x b a C} (h : ADerives Δ Γ M M' (.comp (.all x b C)))
      (hlt : Δ.EntailsLt a b) :
      ADerives Δ Γ (.app M (.val .unit)) (.app M' (.val .unit)) (.comp (C.instLife x a))
  | bangThunkF {Δ Γ M M' A} (hp : Persistent Γ)
      (h : ADerives Δ (⟨.unit, false⟩ :: Γ) M M' (.comp (.ret A))) :
      ADerives Δ Γ (.val (.lam M)) (.val (.lam M')) (.val (.bang (.thunk (.ret A))))
  | bangThunkV {Δ Γ N N' C} (hp : Persistent Γ) (hC : C.isRet = false)
      (h : ADerives Δ Γ (.val (.lam N)) (.val (.lam N')) (.comp C)) :
      ADerives Δ Γ (.val (.lam N)) (.val (.lam N')) (.val (.bang (.thunk C)))
  | bangE {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.val (.bang A))) : ADerives Δ Γ e e' (.val A)
  | boxI {Δ Γ e e' a A} (h : ADerives Δ Γ e e' (.val A)) (hΓ : CtxOutlives Δ Γ a) :
      ADerives Δ Γ e e' (.val (.box a A))
  | boxE {Δ Γ e e' a A} (h : ADerives Δ Γ e e' (.val (.box a A))) : ADerives Δ Γ e e' (.val A)
  | immSub {Δ Γ e e' a b A} (h : ADerives Δ Γ e e' (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
      ADerives Δ Γ e e' (.val (.imm a A))
  | mutSub {Δ Γ e e' a b A} (h : ADerives Δ Γ e e' (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
      ADerives Δ Γ e e' (.val (.mut a A))
  | lolliE {Δ Γ Γ₁ Γ₂ f f' a a' A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
      (ha : ADerives Δ Γ₁ a a' (.val A)) (hf : ADerives Δ Γ₂ f f' (.val (.lolli A B))) :
      ADerives Δ Γ (.app f a) (.app f' a') (.val B)
  | allEV {Δ Γ e e' x b a A} (h : ADerives Δ Γ e e' (.val (.all x b A)))
      (hlt : Δ.EntailsLt a b) :
      ADerives Δ Γ (.app e (.val .unit)) (.app e' (.val .unit)) (.val (A.instLife x a))
  | ofRet {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.comp (.ret A))) : ADerives Δ Γ e e' (.val A)
  | roll {Δ Γ e e' A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
      (h : ADerives Δ Γ e e' (.val (VTy.inst (.mu A) A))) : ADerives Δ Γ e e' (.val (.mu A))
  | unroll {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.val (.mu A))) :
      ADerives Δ Γ e e' (.val (VTy.inst (.mu A) A))
  | delayIn {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.comp (delayUnroll A))) :
      ADerives Δ Γ e e' (.comp (.delay A))
  | delayOut {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.comp (.delay A))) :
      ADerives Δ Γ e e' (.comp (delayUnroll A))
  | streamIn {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.comp (streamUnroll A))) :
      ADerives Δ Γ e e' (.comp (.stream A))
  | streamOut {Δ Γ e e' A} (h : ADerives Δ Γ e e' (.comp (.stream A))) :
      ADerives Δ Γ e e' (.comp (streamUnroll A))

/-- The discard is `unitE` over the destructor applied to the slot. -/
theorem drop_derives {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {T : VTy} {e : Expr} {C : CTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (h : CDerives Δ Γ₂ e (.comp C)) : CDerives Δ Γ (dropE T i e) (.comp C) :=
  .unitE hs (.lolliE (split_kill' Γ₁).toP (.var hx) (dtor_wf hT (kill_dead Γ₁))) h

/-- **The elaboration is type-correct**: an affine derivation's elaborated term is a `CDerives`
derivation at the same context and judgment. -/
theorem ADerives.elab {Δ : LifeCtx} {Γ : Ctx VTy} {e e' : Expr} {j : Jdg}
    (h : ADerives Δ Γ e e' j) : CDerives Δ Γ e' j := by
  induction h with
  | core h => exact h
  | drop hs hx hT _ ih => exact drop_derives hs hx hT ih
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI hs ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind hs ihM ihN
  | lam _ ih => exact .lam ih
  | app hs _ hx ih => exact .app hs ih hx
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | unitE hs _ _ ihV ihM => exact .unitE hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE hs ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx hΓx ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF hp ih
  | bangThunkV hp hC _ ih => exact .bangThunkV hp hC ih
  | bangE _ ih => exact .bangE ih
  | boxI _ hΓ ih => exact .boxI ih hΓ
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | lolliE hs _ _ iha ihf => exact .lolliE hs iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | delayIn _ ih => exact .delayIn ih
  | delayOut _ ih => exact .delayOut ih
  | streamIn _ ih => exact .streamIn ih
  | streamOut _ ih => exact .streamOut ih

/-- Soundness of the affine judgment: the Fundamental Property at the elaborated term. -/
theorem fundamentalA {Δ : LifeCtx} {Γ : Ctx VTy} {e e' : Expr} {j : Jdg}
    (h : ADerives Δ Γ e e' j) : SemJ Δ Γ e' j :=
  fundamentalC h.elab

/-- Adequacy with leak freedom: a closed affine program at `F 1` elaborates to a term that runs
from the empty memory to `()` and the empty memory. -/
theorem adequacyA {e e' : Expr} (h : ADerives LifeCtx.empty [] e e' (.comp (.ret .unit))) :
    BoCa.BoLo.Steps Adequacy.emptyMem e' Adequacy.emptyMem (.val .unit) :=
  adequacyC h.elab

/-- At any result type: a closed affine program at `F R` elaborates to a term that runs from the
empty memory to a value of `R` and the empty memory. -/
theorem runsA {e e' : Expr} {R : VTy} {P : Val → Prop}
    (hP : ∀ ls v ρ, vP R ls LSub.empty v ρ → ρ = PMap.empty ∧ P v)
    (h : ADerives LifeCtx.empty [] e e' (.comp (.ret R))) :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem e' Adequacy.emptyMem (.val v) ∧ P v := by
  refine theorem32 e' P (wpTS_mono (fun ls v ρ hv => ?_) PMap.empty (wp_of_derives h.elab))
  obtain ⟨hρ, hPv⟩ := hP ls v ρ hv
  exact ⟨hρ, hPv⟩

/-! ### Borrows -/

/-- A context split sends a live owner to one side: the owner given to `withbor` is not also in
the callback's context, so no `drop` inside the loan can reach it. -/
theorem owner_not_shared (A : VTy) (Γ Γ₁ Γ₂ : Ctx VTy) :
    ¬ Ctx.SplitP (⟨.ref A, true⟩ :: Γ) (⟨.ref A, true⟩ :: Γ₁) (⟨.ref A, true⟩ :: Γ₂) := by
  intro h
  cases h with
  | dup hT _ => exact absurd hT (by simp [VTy.Persistent, VTy.persistent])

/-- A dead slot is not a solo slot: a `drop` cannot discard a slot its context has consumed. -/
theorem drop_needs_live (T : VTy) (Γ : Ctx VTy) : ¬ Ctx.SoloP (⟨T, false⟩ :: Γ) 0 T := by
  intro h
  cases h

end BoCa.Fig16.LogRel.Core.Affine

end
