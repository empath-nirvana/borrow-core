import Frontend.Check.Tied
import Frontend.Check.Weaken
import Frontend.Check.TLife

/-!
# Frontend — Check — tied derivations of the typed term  `[spec §19, §29]`

The checker returns a typed term with its derivation (`docs/compiler.md` §2.3). `TTied p s Δ Γ t j`
is `TiedDer` over the typed term: a `TDerivesP` derivation of `t`, and, when the list `p` of the
relaxed rules used is empty, a `TDerivesAt Ξ` one at every effect context `Ξ` at which the list `s`
is. Each rule below applies one typed rule at the node it builds, the same rule `TiedDer`'s builder
applies, and its lists are the ones that builder gives.

`TTied.tied`: a typed derivation is a `TiedDer` derivation of the typed term's erasure, by the
projections `TDerivesAt.erase` and `TDerivesP.erase`. So everything stated of `TiedDer` (decision
R, FP, adequacy, `PinLaw`'s theorems) holds of `t.erase`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives CDerivesAt CDerivesP Jdg EffCtx RowAt SigsAt Persistent
  CtxOutlives HasDtor dtorE dtor_wf rowAt_of_sigsAt)

/-- **A typed derivation tied at every effect context at which the list `s` is**.  `[spec §19]` -/
def TTiedAt (s : CRow) (Δ : LifeCtx) (Γ : Ctx CVTy) (t : TExpr) (j : Jdg) : Prop :=
  ∀ Ξ : EffCtx, SigsAt Ξ s → TDerivesAt Ξ Δ Γ t j

/-- **A typed derivation the checker returns**: of `TDerivesP`, and tied (`TTiedAt`) when it uses
no relaxed rule.  `[spec §19, §29]` -/
def TTied (p : Pins) (s : CRow) (Δ : LifeCtx) (Γ : Ctx CVTy) (t : TExpr) (j : Jdg) : Prop :=
  (p = [] → TTiedAt s Δ Γ t j) ∧ TDerivesP Δ Γ t j

/-- **The typed derivation is a `TiedDer` derivation of the erasure.** -/
theorem TTied.tied {p : Pins} {s : CRow} {Δ : LifeCtx} {Γ : Ctx CVTy} {t : TExpr} {j : Jdg}
    (h : TTied p s Δ Γ t j) : TiedDer p s Δ Γ t.erase j :=
  ⟨fun hp Ξ hΞ => (h.1 hp Ξ hΞ).erase, h.2.erase⟩

namespace TTied
variable {Δ : LifeCtx} {Γ : Ctx CVTy} (i : TInfo)

/-- A rule that reads no row, at a node with no premise: tied at every effect context. -/
theorem ofAt {t : TExpr} {j : Jdg} (h : ∀ Ξ, TDerivesAt Ξ Δ Γ t j) : TTied [] [] Δ Γ t j :=
  ⟨fun _ Ξ _ => h Ξ, (h fun _ => []).toP⟩

/-- A derivation that uses a relaxed rule: its tie is not claimed. -/
theorem pinned {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (q : Pin) (h : TDerivesP Δ Γ t j) :
    TTied (q :: p) s Δ Γ t j :=
  ⟨fun h' => absurd h' (List.cons_ne_nil _ _), h⟩

/-- A derivation tied at the contexts at which `s′` is, at a list `s` that ties at least those. -/
theorem of_sigs {p : Pins} {s s' : CRow} {t : TExpr} {j : Jdg}
    (hs : ∀ Ξ, SigsAt Ξ s → SigsAt Ξ s') (h : TTied p s' Δ Γ t j) : TTied p s Δ Γ t j :=
  ⟨fun hn Ξ hΞ => h.1 hn Ξ (hs Ξ hΞ), h.2⟩

/-! ### The rules -/

theorem var {k : Nat} {A : CVTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ k A) :
    TTied [] [] Δ Γ (.var i (.val A) k A) (.val A) :=
  ofAt fun _ => .var h

theorem unitI (h : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TTied [] [] Δ Γ (.unitI i (.val .unit)) (.val .unit) :=
  ofAt fun _ => .unitI h

theorem topI : TTied [] [] Δ Γ (.topI i (.comp .top)) (.comp .top) :=
  ofAt fun _ => .topI

theorem force {k : Nat} {C : CCTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ k (.thunk C)) :
    TTied [] [] Δ Γ (.force i (.comp C) k C) (.comp C) :=
  ofAt fun _ => .force h

theorem tensorI (u : Masks) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {t₁ t₂ : TExpr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (h₁ : TTied p₁ s₁ Δ Γ₁ t₁ (.val A))
    (h₂ : TTied p₂ s₂ Δ Γ₂ t₂ (.val B)) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.tensorI i (.val (.tensor A B)) A B u t₁ t₂)
      (.val (.tensor A B)) :=
  ⟨fun hn Ξ h => .tensorI hs hm (h₁.1 (nilL hn) Ξ (sigsAt_union_left h))
      (h₂.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .tensorI hs hm h₁.2 h₂.2⟩

theorem sumI₁ {p : Pins} {s : CRow} {t : TExpr} {A B : CVTy} (h : TTied p s Δ Γ t (.val A)) :
    TTied p s Δ Γ (.sumI₁ i (.val (.sum A B)) A B t) (.val (.sum A B)) :=
  ⟨fun hn Ξ hΞ => .sumI₁ (h.1 hn Ξ hΞ), .sumI₁ h.2⟩

theorem sumI₂ {p : Pins} {s : CRow} {t : TExpr} {A B : CVTy} (h : TTied p s Δ Γ t (.val B)) :
    TTied p s Δ Γ (.sumI₂ i (.val (.sum A B)) A B t) (.val (.sum A B)) :=
  ⟨fun hn Ξ hΞ => .sumI₂ (h.1 hn Ξ hΞ), .sumI₂ h.2⟩

theorem thunkF {p : Pins} {s : CRow} {t : TExpr} {A : CVTy}
    (h : TTied p s Δ (⟨.unit, false⟩ :: Γ) t (.comp (.ret A))) :
    TTied p s Δ Γ (.thunkF i (.val (.thunk (.ret A))) A t) (.val (.thunk (.ret A))) :=
  ⟨fun hn Ξ hΞ => .thunkF (h.1 hn Ξ hΞ), .thunkF h.2⟩

theorem thunkV {p : Pins} {s : CRow} {t : TExpr} {N : BoCa.Expr} {C : CCTy}
    (hC : C.isRet = false) (h : TTied p s Δ Γ t (.comp C)) (q : t.erase = .val (BoCa.Val.lam N)) :
    TTied p s Δ Γ (.thunkV i (.val (.thunk C)) C t) (.val (.thunk C)) :=
  ⟨fun hn Ξ hΞ => .thunkV hC (h.1 hn Ξ hΞ) q, .thunkV hC h.2 q⟩

theorem ret {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (h : TTied p s Δ Γ t (.val A)) :
    TTied p s Δ Γ (.ret i (.comp (.ret A)) A t) (.comp (.ret A)) :=
  ⟨fun hn Ξ hΞ => .ret (h.1 hn Ξ hΞ), .ret h.2⟩

theorem bind {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tM tN : TExpr} {A : CVTy}
    {C : CCTy} (u : Masks) (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂)
    (hM : TTied p₁ s₁ Δ Γ₁ tM (.comp (.ret A))) (hN : TTied p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) tN (.comp C)) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.bind i (.comp C) A C u tM tN) (.comp C) :=
  ⟨fun hn Ξ h => .bind hs hm (hM.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hN.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .bind hs hm hM.2 hN.2⟩

theorem lam {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} {C : CCTy}
    (h : TTied p s Δ (⟨A, true⟩ :: Γ) t (.comp C)) :
    TTied p s Δ Γ (.lam i (.comp (.arr A C)) A C t) (.comp (.arr A C)) :=
  ⟨fun hn Ξ hΞ => .lam (h.1 hn Ξ hΞ), .lam h.2⟩

/-- `[λ-dead]`.  `[spec §26]` -/
theorem lamDead {p : Pins} {s : CRow} {t : TExpr} {S : CRow} {B : CVTy}
    (h : TTied p s Δ (⟨.unit, false⟩ :: Γ) t (.comp (effOf S B))) :
    TTied p s Δ Γ (.lamDead i (.comp (.arr .unit (effOf S B))) S B t)
      (.comp (.arr .unit (effOf S B))) :=
  ⟨fun hn Ξ hΞ => .lamDead (h.1 hn Ξ hΞ), .lamDead h.2⟩

theorem app (u : Masks) {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tM : TExpr} {k : Nat} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hM : TTied p s Δ Γ₁ tM (.comp (.arr A C)))
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₂ k A) :
    TTied p s Δ Γ (.app i (.comp C) k A C u tM) (.comp C) :=
  ⟨fun hn Ξ hΞ => .app hs hm (hM.1 hn Ξ hΞ) hx, .app hs hm hM.2 hx⟩

theorem withI {p₁ p₂ : Pins} {s₁ s₂ : CRow} {tM tN : TExpr} {C D : CCTy}
    (hM : TTied p₁ s₁ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) tM (.comp C))
    (hN : TTied p₂ s₂ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) tN (.comp D)) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.withI i (.comp (.amp C D)) C D tM tN) (.comp (.amp C D)) :=
  ⟨fun hn Ξ h => .withI (hM.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hN.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .withI hM.2 hN.2⟩

theorem proj₁ {p : Pins} {s : CRow} {t : TExpr} {C D : CCTy}
    (h : TTied p s Δ Γ t (.comp (.amp C D))) :
    TTied p s Δ Γ (.proj₁ i (.comp C) C D t) (.comp C) :=
  ⟨fun hn Ξ hΞ => .proj₁ (h.1 hn Ξ hΞ), .proj₁ h.2⟩

theorem proj₂ {p : Pins} {s : CRow} {t : TExpr} {C D : CCTy}
    (h : TTied p s Δ Γ t (.comp (.amp C D))) :
    TTied p s Δ Γ (.proj₂ i (.comp D) C D t) (.comp D) :=
  ⟨fun hn Ξ hΞ => .proj₂ (h.1 hn Ξ hΞ), .proj₂ h.2⟩

theorem unitE (u : Masks) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tV tM : TExpr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hV : TTied p₁ s₁ Δ Γ₁ tV (.val .unit))
    (hM : TTied p₂ s₂ Δ Γ₂ tM (.comp C)) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.unitE i (.comp C) C u tV tM) (.comp C) :=
  ⟨fun hn Ξ h => .unitE hs hm (hV.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hM.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .unitE hs hm hV.2 hM.2⟩

theorem tensorE (u : Masks) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γp Γb : Ctx CVTy} {tV tM : TExpr} {A B : CVTy}
    {C : CCTy} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γp Γb) (hm : u.Rel Γp Γb)
    (hV : TTied p₁ s₁ Δ Γp tV (.val (.tensor A B)))
    (hM : TTied p₂ s₂ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) tM (.comp C)) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.tensorE i (.comp C) A B C u tV tM) (.comp C) :=
  ⟨fun hn Ξ h => .tensorE hs hm (hV.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hM.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .tensorE hs hm hV.2 hM.2⟩

theorem sumE (u : Masks) {p₁ p₂ p₃ : Pins} {s₁ s₂ s₃ : CRow} {Γs Γb : Ctx CVTy} {tV t₁ t₂ : TExpr}
    {A B : CVTy} {C : CCTy} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γs Γb) (hm : u.Rel Γs Γb)
    (hV : TTied p₁ s₁ Δ Γs tV (.val (.sum A B)))
    (h₁ : TTied p₂ s₂ Δ (⟨A, true⟩ :: Γb) t₁ (.comp C))
    (h₂ : TTied p₃ s₃ Δ (⟨B, true⟩ :: Γb) t₂ (.comp C)) :
    TTied (p₁ ++ (p₂ ++ p₃)) (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (.sumE i (.comp C) A B C u tV t₁ t₂) (.comp C) :=
  ⟨fun hn Ξ h => .sumE hs hm (hV.1 (nilL hn) Ξ (sigsAt_union_left h))
      (h₁.1 (nilL (nilR hn)) Ξ (sigsAt_union_left (sigsAt_union_right h)))
      (h₂.1 (nilR (nilR hn)) Ξ (sigsAt_union_right (sigsAt_union_right h))),
    .sumE hs hm hV.2 h₁.2 h₂.2⟩

theorem zeroE (u : Masks) {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tV : TExpr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hV : TTied p s Δ Γ₁ tV (.val .zero)) :
    TTied p s Δ Γ (.zeroE i (.comp C) C u tV) (.comp C) :=
  ⟨fun hn Ξ hΞ => .zeroE hs hm (hV.1 hn Ξ hΞ), .zeroE hs hm hV.2⟩

theorem allI {p : Pins} {s : CRow} {x : LifeVar} {b : CLife} {t : TExpr} {S : CVTy} {C : CCTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ BoCa.Fig16.LogRel.Core.VFree x s.ty)
    (h : TTied p s (Δ.extend x b) (⟨S, false⟩ :: Γ) t (.comp C)) :
    TTied p s Δ Γ (.allI i (.comp (.all x b C)) x b S C t) (.comp (.all x b C)) :=
  ⟨fun hn Ξ hΞ => .allI hbx hΔx hΓx (h.1 hn Ξ hΞ), .allI hbx hΔx hΓx h.2⟩

theorem allE {p : Pins} {s : CRow} {t : TExpr} {x : LifeVar} {b a : CLife} {C : CCTy}
    (h : TTied p s Δ Γ t (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    TTied p s Δ Γ (.allE i (.comp (C.instLife x a)) x b a C t) (.comp (C.instLife x a)) :=
  ⟨fun hn Ξ hΞ => .allE (h.1 hn Ξ hΞ) hlt, .allE h.2 hlt⟩

theorem bangThunkF {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (hp : Persistent Γ)
    (h : TTied p s Δ (⟨.unit, false⟩ :: Γ) t (.comp (.ret A))) :
    TTied p s Δ Γ (.bangThunkF i (.val (.bang (.thunk (.ret A)))) A t)
      (.val (.bang (.thunk (.ret A)))) :=
  ⟨fun hn Ξ hΞ => .bangThunkF hp (h.1 hn Ξ hΞ), .bangThunkF hp h.2⟩

theorem bangThunkV {p : Pins} {s : CRow} {t : TExpr} {N : BoCa.Expr} {C : CCTy}
    (hp : Persistent Γ) (hC : C.isRet = false) (h : TTied p s Δ Γ t (.comp C))
    (q : t.erase = .val (BoCa.Val.lam N)) :
    TTied p s Δ Γ (.bangThunkV i (.val (.bang (.thunk C))) C t) (.val (.bang (.thunk C))) :=
  ⟨fun hn Ξ hΞ => .bangThunkV hp hC (h.1 hn Ξ hΞ) q, .bangThunkV hp hC h.2 q⟩

theorem bangE {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (h : TTied p s Δ Γ t (.val (.bang A))) :
    TTied p s Δ Γ (.bangE i (.val A) A t) (.val A) :=
  ⟨fun hn Ξ hΞ => .bangE (h.1 hn Ξ hΞ), .bangE h.2⟩

theorem boxI {p : Pins} {s : CRow} {t : TExpr} {a : CLife} {A : CVTy} (h : TTied p s Δ Γ t (.val A))
    (hΓ : CtxOutlives Δ Γ a) : TTied p s Δ Γ (.boxI i (.val (.box a A)) a A t) (.val (.box a A)) :=
  ⟨fun hn Ξ hΞ => .boxI (h.1 hn Ξ hΞ) hΓ, .boxI h.2 hΓ⟩

theorem boxE {p : Pins} {s : CRow} {t : TExpr} {a : CLife} {A : CVTy}
    (h : TTied p s Δ Γ t (.val (.box a A))) : TTied p s Δ Γ (.boxE i (.val A) a A t) (.val A) :=
  ⟨fun hn Ξ hΞ => .boxE (h.1 hn Ξ hΞ), .boxE h.2⟩

theorem immSub {p : Pins} {s : CRow} {t : TExpr} {a b : CLife} {A : CVTy}
    (h : TTied p s Δ Γ t (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    TTied p s Δ Γ (.immSub i (.val (.imm a A)) a b A t) (.val (.imm a A)) :=
  ⟨fun hn Ξ hΞ => .immSub (h.1 hn Ξ hΞ) hle, .immSub h.2 hle⟩

theorem mutSub {p : Pins} {s : CRow} {t : TExpr} {a b : CLife} {A : CVTy}
    (h : TTied p s Δ Γ t (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    TTied p s Δ Γ (.mutSub i (.val (.mut a A)) a b A t) (.val (.mut a A)) :=
  ⟨fun hn Ξ hΞ => .mutSub (h.1 hn Ξ hΞ) hle, .mutSub h.2 hle⟩

theorem lolliE (u : Masks) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {ta tf : TExpr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (ha : TTied p₁ s₁ Δ Γ₁ ta (.val A))
    (hf : TTied p₂ s₂ Δ Γ₂ tf (.val (.lolli A B))) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.lolliE i (.val B) A B u ta tf) (.val B) :=
  ⟨fun hn Ξ h => .lolliE hs hm (ha.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hf.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .lolliE hs hm ha.2 hf.2⟩

theorem allEV {p : Pins} {s : CRow} {t : TExpr} {x : LifeVar} {b a : CLife} {A : CVTy}
    (h : TTied p s Δ Γ t (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    TTied p s Δ Γ (.allEV i (.val (A.instLife x a)) x b a A t) (.val (A.instLife x a)) :=
  ⟨fun hn Ξ hΞ => .allEV (h.1 hn Ξ hΞ) hlt, .allEV h.2 hlt⟩

theorem ofRet {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (h : TTied p s Δ Γ t (.comp (.ret A))) :
    TTied p s Δ Γ (.ofRet i (.val A) A t) (.val A) :=
  ⟨fun hn Ξ hΞ => .ofRet (h.1 hn Ξ hΞ), .ofRet h.2⟩

theorem roll {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (hA : A.NoMut 0)
    (hc : (BoCa.Fig16.LogRel.Core.VTy.mu A).Cl 0)
    (h : TTied p s Δ Γ t (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) :
    TTied p s Δ Γ (.roll i (.val (.mu A)) A t) (.val (.mu A)) :=
  ⟨fun hn Ξ hΞ => .roll hA hc (h.1 hn Ξ hΞ), .roll hA hc h.2⟩

theorem unroll {p : Pins} {s : CRow} {t : TExpr} {A : CVTy} (h : TTied p s Δ Γ t (.val (.mu A))) :
    TTied p s Δ Γ (.unroll i (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) A t)
      (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  ⟨fun hn Ξ hΞ => .unroll (h.1 hn Ξ hΞ), .unroll h.2⟩

theorem nuIn {p : Pins} {s : CRow} {t : TExpr} {C : CCTy} (hC : C.NuOk)
    (h : TTied p s Δ Γ t (.comp C.unroll)) : TTied p s Δ Γ (.nuIn i (.comp (.nu C)) C t) (.comp (.nu C)) :=
  ⟨fun hn Ξ hΞ => .nuIn hC (h.1 hn Ξ hΞ), .nuIn hC h.2⟩

theorem nuOut {p : Pins} {s : CRow} {t : TExpr} {C : CCTy} (hC : C.NuOk)
    (h : TTied p s Δ Γ t (.comp (.nu C))) : TTied p s Δ Γ (.nuOut i (.comp C.unroll) C t) (.comp C.unroll) :=
  ⟨fun hn Ξ hΞ => .nuOut hC (h.1 hn Ξ hΞ), .nuOut hC h.2⟩

/-! ### The effect rules -/

theorem effSub {p : Pins} {s : CRow} {t : TExpr} {S S' : CRow} {A : CVTy}
    (hle : BoCa.Fig16.LogRel.Core.RowLe S S') (h : TTied p s Δ Γ t (.comp (effOf S A))) :
    TTied p s Δ Γ (.effSub i (.comp (effOf S' A)) S S' A t) (.comp (effOf S' A)) :=
  ⟨fun hn Ξ hΞ => .effSub hle (h.1 hn Ξ hΞ), .effSub hle h.2⟩

/-- `[perform]` reads its row. -/
theorem effPerform {p : Pins} {s : CRow} {t : TExpr} {S : CRow} {o : COpSig}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (hna : o.abort = false)
    (h : TTied p s Δ Γ t (.val o.A)) :
    TTied p (S ∪ s) Δ Γ (.effPerform i (.comp (effOf S o.B)) S o t) (.comp (effOf S o.B)) :=
  ⟨fun hn Ξ hΞ => .effPerform (rowAt_of_union_left hΞ) hf hna (h.1 hn Ξ (sigsAt_union_right hΞ)),
    .effPerform hf hna h.2⟩

/-- `[raise]` reads its row. -/
theorem effRaise {p : Pins} {s : CRow} {t : TExpr} {S : CRow} {o : COpSig} {B : CVTy}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : o.A.Drop) (h : TTied p s Δ Γ t (.val o.A)) :
    TTied p (S ∪ s) Δ Γ (.effRaise i (.comp (effOf S B)) S o B t) (.comp (effOf S B)) :=
  ⟨fun hn Ξ hΞ => .effRaise (rowAt_of_union_left hΞ) hf ha hd (h.1 hn Ξ (sigsAt_union_right hΞ)),
    .effRaise hf ha hd h.2⟩

theorem effLet (u : Masks) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tM tN : TExpr} {A B : CVTy}
    {S : CRow} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops)
    (hU : S.Unr → Persistent Γ₂) (hM : TTied p₁ s₁ Δ Γ₁ tM (.comp (effOf S A)))
    (hN : TTied p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) tN (.comp (effOf S B))) :
    TTied (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.effLet i (.comp (effOf S B)) A B S u tM tN)
      (.comp (effOf S B)) :=
  ⟨fun hn Ξ h => .effLet hs hm hW hU (hM.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hN.1 (nilR hn) Ξ (sigsAt_union_right h)),
    .effLet hs hm hW hU hM.2 hN.2⟩

/-- `[then]` with its finaliser at the pure row, as `CDerivesAt.effThenA`.  `[spec §24, §27]` -/
theorem effThenA (u : Masks) {p₁ p₂ p₃ : Pins} {s₁ s₂ s₃ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tM tN tD : TExpr}
    {A B : CVTy} {S : CRow} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hNZ : S.NZ)
    (hUq : S.Uniq) (hU : S.UnrD → Persistent Γ₂) (hM : TTied p₁ s₁ Δ Γ₁ tM (.comp (effOf S A)))
    (hN : TTied p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) tN (.comp (effOf S B)))
    (hD : TTied p₃ s₃ Δ (⟨.unit, false⟩ :: Γ₂) tD (.comp (.ret .unit))) :
    TTied (p₁ ++ (p₂ ++ p₃)) (s₁ ∪ (s₂ ∪ s₃)) Δ Γ
      (.effThen i (.comp (effOf S B)) A B S S [] u tM tN tD) (.comp (effOf S B)) :=
  have hfin : ∀ n k o o', BoCa.Fig16.LogRel.Core.Row.find S n k = some o →
      BoCa.Fig16.LogRel.Core.Row.find S n k = some o' →
      BoCa.Fig16.LogRel.Core.capB o.q o.B = true →
      BoCa.Fig16.LogRel.Core.ThenLe o.fin [] o'.fin :=
    fun _ _ o _ hf hf' _ => by rw [hf] at hf'; cases hf'; exact BoCa.Fig16.LogRel.Core.ThenLe.nil o.fin
  have hP : BoCa.Fig16.LogRel.Core.Row.UnrD [] → S.PendPers :=
    fun ⟨_, h, _⟩ => absurd h List.not_mem_nil
  ⟨fun hn Ξ h => .effThen hs hm hNZ hUq hU (BoCa.Fig16.LogRel.Core.RowLe.refl S)
      (BoCa.Fig16.LogRel.Core.RowLe.nil S) hfin hP rfl (hM.1 (nilL hn) Ξ (sigsAt_union_left h))
      (hN.1 (nilL (nilR hn)) Ξ (sigsAt_union_left (sigsAt_union_right h)))
      (hD.1 (nilR (nilR hn)) Ξ (sigsAt_union_right (sigsAt_union_right h))),
    .effThen hs hm hNZ hUq hU (BoCa.Fig16.LogRel.Core.RowLe.refl S)
      (BoCa.Fig16.LogRel.Core.RowLe.nil S) hfin hP rfl hM.2 hN.2 hD.2⟩

/-- `[handle]` reads its handled row, as `CDerivesAt.effHandleV`: the handler's pair `tc` a value
form over a part `Γ₁` of the context whose live slots are persistent.  `[spec §19]` -/
theorem effHandle (u : Masks) (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind)
    (site : Option HSite) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tc te : TExpr}
    {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂)
    (hd : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ₁) (hH : tc.erase.ValFormIn Γ₁)
    (hc : TTied p₁ s₁ Δ Γ₁ tc (.val (.tensor (BoCa.Fig16.LogRel.Core.retTy S A R)
      (BoCa.Fig16.LogRel.Core.clausesTy S R E))))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TTied p₂ s₂ Δ Γ₂ te (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A))) :
    TTied (p₁ ++ p₂) ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (s₁ ∪ s₂)) Δ Γ
      (.effHandleV i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R u ks site
        te.erase.hin tc te)
      (.comp (effOf S R)) :=
  ⟨fun hn Ξ h => .effHandleV (rowAt_of_union_left h) hs hm hd hH
      (hc.1 (nilL hn) Ξ (sigsAt_union_left (sigsAt_union_right h))) hn0 hnS hlen hdv
      (he.1 (nilR hn) Ξ (sigsAt_union_right (sigsAt_union_right h))) rfl,
    .effHandleV hs hm hd hH hc.2 hn0 hnS hlen hdv he.2 rfl⟩

/-- BOXED-κ reads its handled row, as `CDerivesAt.effHandleB`.  `[spec §28]` -/
theorem effHandleB (u : Masks) (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind)
    (site : Option HSite) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {tc te : TExpr}
    {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {d : CLife}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂)
    (hd : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ₁) (hH : tc.erase.ValFormIn Γ₁)
    (hc : TTied p₁ s₁ Δ Γ₁ tc (.val (.tensor (BoCa.Fig16.LogRel.Core.retTy S A R)
      (BoCa.Fig16.LogRel.Core.clausesTyB S R d E))))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TTied p₂ s₂ Δ Γ₂ te (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hΓd : CtxOutlives Δ Γ₂ d)
    (hSd : BoCa.Fig16.LogRel.Core.Row.AnsOutlives Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S)) :
    TTied (p₁ ++ p₂) ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (s₁ ∪ s₂)) Δ Γ
      (.effHandleVB i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R d u ks site
        te.erase.hin tc te)
      (.comp (effOf S R)) :=
  ⟨fun hn Ξ h => .effHandleVB (rowAt_of_union_left h) hs hm hd hH
      (hc.1 (nilL hn) Ξ (sigsAt_union_left (sigsAt_union_right h))) hn0 hnS hlen hdv
      (he.1 (nilR hn) Ξ (sigsAt_union_right (sigsAt_union_right h))) hΓd hSd rfl,
    .effHandleVB hs hm hd hH hc.2 hn0 hnS hlen hdv he.2 hΓd hSd rfl⟩

/-- `iterate` reads its row, which holds `Div`.  `[spec §14]` -/
theorem iterate (S : CRow) (St B R : CVTy) (hS : BoCa.Fig16.LogRel.Core.Row.divB S = true)
    (hΓ : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TTied [] S Δ Γ (.iterate i (.val (BoCa.Fig16.LogRel.Core.iterTy S St B R)) S St B R)
      (.val (BoCa.Fig16.LogRel.Core.iterTy S St B R)) :=
  ⟨fun _ _ hΞ => .iterate S St B R (rowAt_of_sigsAt hΞ) hS hΓ, .iterate S St B R hS hΓ⟩

/-- `div_fuel` reads its handled row `tick, Σ`.  `[spec §14]` -/
theorem divFuel (S : CRow) (A : CVTy) (hS : ∀ o ∈ S, o.n ≠ divEff)
    (hΓ : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TTied [] (BoCa.Fig16.LogRel.Core.tickSig :: S) Δ Γ
      (.divFuel i (.val (BoCa.Fig16.LogRel.Core.divFuelTy S A)) S A)
      (.val (BoCa.Fig16.LogRel.Core.divFuelTy S A)) :=
  ⟨fun _ _ hΞ => .divFuel S A (rowAt_of_sigsAt hΞ) hS hΓ, .divFuel S A hS hΓ⟩

/-- `reify_res` reads its handled row `tick, Σ`, and its residual's premise.  `[spec §14]` -/
theorem reify {p : Pins} {s : CRow} {t : TExpr} (S : CRow) (B R : CVTy) (res : BoCa.Val)
    (hS : ∀ o ∈ S, o.n ≠ divEff) (hcl : BoCa.Fig16.LogRel.Core.closedAt 0 res.1 = true)
    (h : TTied p s Δ [] t (.val (BoCa.Fig16.LogRel.Core.resTy S B R))) (q : t.erase = .val res)
    (hΓ : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TTied p ((BoCa.Fig16.LogRel.Core.tickSig :: S) ∪ s) Δ Γ
      (.reify i (.val (BoCa.Fig16.LogRel.Core.reifyTy S B R)) S B R t)
      (.val (BoCa.Fig16.LogRel.Core.reifyTy S B R)) :=
  ⟨fun hn Ξ hΞ => .reify S B R res (rowAt_of_union_left hΞ) hS hcl
      (h.1 hn Ξ (sigsAt_union_right hΞ)) q hΓ,
    .reify S B R res hS hcl h.2 q hΓ⟩

/-- `[handle]` at clauses that resume `κ` in tail position reads its handled row, as
`CDerivesAt.effHandleT`.  `[spec §14, §19]` -/
theorem effHandleT (u : Masks) (site : Option HSite) {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy}
    {tc te : TExpr} {Hr Hc : BoCa.Expr} {S SN : CRow} {E : List (CQual × CVTy × CVTy)}
    {fs : Nat → CCTy} {n : UInt32} {c : Bool} {A R : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) (hd : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ₁)
    (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
    (hc : TTied p₁ s₁ Δ Γ₁ tc (.val (.tensor (BoCa.Fig16.LogRel.Core.retTy S A R)
      (BoCa.Fig16.LogRel.Core.ansesTy S SN R E))))
    (qc : tc.erase = .pair Hr Hc) (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hSN : BoCa.Fig16.LogRel.Core.RowLe SN S)
    (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (hCN : c = true → ∀ o ∈ SN, o.call = true)
    (he : TTied p₂ s₂ Δ Γ₂ te
      (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 fs c ++ S) A))) :
    TTied (p₁ ++ p₂) ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 fs c ++ S) ∪ (s₁ ∪ s₂)) Δ Γ
      (.effHandleT i (.comp (effOf S R)) S SN E fs n c A R u site te.erase.hin tc te)
      (.comp (effOf S R)) :=
  ⟨fun hn Ξ hΞ => .effHandleT (rowAt_of_union_left hΞ) hs hm hd hHr hHc
      (hc.1 (nilL hn) Ξ (sigsAt_union_left (sigsAt_union_right hΞ))) qc
      hn0 hnd hnS hlen hSN hLin hCN
      (he.1 (nilR hn) Ξ (sigsAt_union_right (sigsAt_union_right hΞ))) rfl,
    .effHandleT hs hm hd hHr hHc hc.2 qc hn0 hnd hnS hlen hSN hLin hCN he.2 rfl⟩

/-! ### Derived forms -/

/-- `dtorE T xᵢ; M`, as `drop_derives`: `unitE` over `lolliE` of the variable and the
destructor's derived node.  `[spec §12]` -/
theorem drop (ix : TInfo) (u₁ u₂ : List Bool) {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {k : Nat}
    {T : CVTy} {t : TExpr} {C : CCTy} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hm : SplitMasks Γ₁ Γ₂ u₁ u₂)
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₁ k T) (hT : HasDtor T)
    (hc : BoCa.Fig16.LogRel.Core.closedAt 0 (dtorE T) = true) (hE : (dtorE T).effFree = true)
    (h : TTied p s Δ Γ₂ t (.comp C)) :
    TTied p s Δ Γ (.unitE i (.comp C) C (Masks.of u₁ u₂)
        (.lolliE ix (.val .unit) T .unit (Masks.of u₁ (noUse u₁)) (.var ix (.val T) k T)
          (.dtor ix (.val (.lolli T .unit)) T)) t) (.comp C) := by
  have hd : TTied [] [] Δ (BoCa.Fig16.LogRel.Core.kill Γ₁) (.dtor ix (.val (.lolli T .unit)) T)
      (.val (.lolli T .unit)) :=
    ofAt fun _ => .dtor hT hc hE (BoCa.Fig16.LogRel.Core.kill_dead Γ₁)
  have hl := lolliE (Δ := Δ) ix (Masks.of u₁ (noUse u₁)) (BoCa.Fig16.LogRel.Core.split_kill' Γ₁).toP
    (SplitMasks.kill_right hm.left_live).rel_of (var ix hx) hd
  simpa using unitE i (Masks.of u₁ u₂) hs hm.rel_of hl h

/-- `⇓σ t` (`shortenE`) as typed nodes, at a borrow former `M` whose `⊑` node is `leaf`: the leaf's
`⊑` at a leaf, and `let (x, y) = t; return (⇓σ₁ x, ⇓σ₂ y)` at a node, as `shortenE_wfAt`. `u` is
`t`'s use mask; the components use the pair's two slots. `[spec §5]` -/
def shortenT (M : CLife → CVTy → CVTy) (leaf : TInfo → CLife → CLife → CVTy → TExpr → TExpr)
    (i : TInfo) (a b : CLife) : CShape → List Bool → TExpr → TExpr
  | .leaf A, _, t => leaf i a b A t
  | .node s₁ s₂, u, t =>
      let n := u.map fun _ => false
      .ofRet i (.val ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a))
        ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a)
        (.tensorE i (.comp (.ret ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a)))
          (s₁.famTy M b) (s₂.famTy M b) (.ret ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a))
          (Masks.of u n) t
          (.ret i (.comp (.ret ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a)))
            ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a)
            (.tensorI i (.val ((BoCa.Fig16.LogRel.Core.Shape.node s₁ s₂).famTy M a))
              (s₁.famTy M a) (s₂.famTy M a) (Masks.of (false :: true :: n) (true :: false :: n))
              (shortenT M leaf i a b s₁ (false :: true :: n)
                (.var i (.val (s₁.famTy M b)) 1 (s₁.famTy M b)))
              (shortenT M leaf i a b s₂ (true :: false :: n)
                (.var i (.val (s₂.famTy M b)) 0 (s₂.famTy M b))))))

/-- `⇓σ t` erases to `shortenE σ t.erase`, when the leaf's node erases to its child's. -/
theorem shortenT_erase {M : CLife → CVTy → CVTy} {leaf : TInfo → CLife → CLife → CVTy → TExpr → TExpr}
    (hl : ∀ i a b A t, (leaf i a b A t).erase = t.erase) (i : TInfo) (a b : CLife) :
    ∀ (σ : CShape) (u : List Bool) (t : TExpr),
      (shortenT M leaf i a b σ u t).erase = BoCa.Fig16.LogRel.Core.shortenE σ t.erase
  | .leaf _, _, t => hl _ _ _ _ t
  | .node s₁ s₂, u, t => by
      simp only [shortenT, TExpr.erase, BoCa.Fig16.LogRel.Core.shortenE,
        shortenT_erase hl i a b s₁, shortenT_erase hl i a b s₂]

/-- `⇓σ`, typed, as `shortenE_wfAt`: a family moved to a shorter lifetime, leaf by leaf, by the
former's `⊑` rule `sub`.  `[spec §5]` -/
theorem shorten {M : CLife → CVTy → CVTy} {leaf : TInfo → CLife → CLife → CVTy → TExpr → TExpr}
    (sub : ∀ {p : Pins} {s : CRow} {Δ : LifeCtx} {Γ : Ctx CVTy} {t : TExpr} {a b : CLife} {A : CVTy},
      TTied p s Δ Γ t (.val (M b A)) → Δ.EntailsLe a b → TTied p s Δ Γ (leaf i a b A t) (.val (M a A)))
    {a b : CLife} : ∀ {σ : CShape} (u : List Bool) {p : Pins} {s : CRow} {Γ : Ctx CVTy} {t : TExpr},
    UsedLive u Γ → TTied p s Δ Γ t (.val (σ.famTy M b)) → Δ.EntailsLe a b →
    TTied p s Δ Γ (shortenT M leaf i a b σ u t) (.val (σ.famTy M a))
  | .leaf _, _, _, _, _, _, _, h, hle => sub h hle
  | .node s₁ s₂, u, p, s, Γ, t, hu, h, hle => by
      have hk := BoCa.Fig16.LogRel.Core.kill_dead Γ
      have hl : (u.map fun _ => false).length = (BoCa.Fig16.LogRel.Core.kill Γ).length := by
        simp [BoCa.Fig16.LogRel.Core.kill, hu.1]
      have hn := SplitMasks.dead (u := u.map fun _ => false) hk hl
      have hn' : noUse (u.map fun _ => false) = u.map fun _ => false := by simp [noUse]
      rw [hn'] at hn
      have hr := ofRet i (tensorE i (Masks.of u (u.map fun _ => false))
        (BoCa.Fig16.LogRel.Core.split_kill' Γ).toP (SplitMasks.kill_right hu).rel_of h (ret i
        (tensorI i (Masks.of (false :: true :: u.map fun _ => false) (true :: false :: u.map fun _ => false))
          (.right (.left (BoCa.Fig16.LogRel.Core.deadSplit hk)))
          (SplitMasks.rel_of (.cons (by simp) (by simp) (by simp) (.cons (by simp) (by simp) (by simp) hn)))
          (shorten sub (σ := s₁) (false :: true :: u.map fun _ => false)
            ⟨by simpa using hl, fun k hk' => by
              match k, hk' with
              | 1, _ => rfl
              | k + 2, hk' => simp at hk'⟩
            (var i (.there (.here hk))) hle)
          (shorten sub (σ := s₂) (true :: false :: u.map fun _ => false)
            ⟨by simpa using hl, fun k hk' => by
              match k, hk' with
              | 0, _ => rfl
              | k + 2, hk' => simp at hk'⟩
            (var i (.here (.cons hk))) hle))))
      exact of_sigs (s' := s ∪ []) (fun _ hΞ o ho => hΞ o (by simpa using ho))
        (by simpa [shortenT, BoCa.Fig16.LogRel.Core.Shape.famTy] using hr)

/-- **A string literal's table** (SPEC §17): the derived node over the literal's typed term, whose
erasure is the table of the bytes `bs`. -/
theorem litFn {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} {bs : List Nat}
    (hb : t.erase = BoCa.Fig16.LogRel.Core.Check.litFnE bs)
    (hcl : BoCa.Fig16.LogRel.Core.closedAt 0 (BoCa.Fig16.LogRel.Core.Check.litFnE bs) = true)
    (h : TTied p s Δ Γ t j) : TTied p s Δ Γ (.litFn i j bs t) j :=
  ⟨fun hn Ξ hΞ => .litFn (h.1 hn Ξ hΞ) hb hcl, .litFn h.2 hb hcl⟩

/-- **A division by a literal at which it cannot fail** (SPEC §39): the derived node over the
scheme's typed term. -/
theorem divLit {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} {op : BoCa.HostOp} {c : BoCa.IntLit}
    (hb : divLitB op c t.erase = true) (hs : safeDivB op c = true) (h : TTied p s Δ Γ t j) :
    TTied p s Δ Γ (.divLit i j op c t) j :=
  ⟨fun hn Ξ hΞ => .divLit (h.1 hn Ξ hΞ) hb hs, .divLit h.2 hb hs⟩

/-- **A counted walk of a view** (SPEC §16): the derived node over the loop's typed term. -/
theorem walk {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (m read : Bool) (hb : walkB t.erase = true)
    (hr : read = true → walkReadB m t.erase = true)
    (h : TTied p s Δ Γ t j) : TTied p s Δ Γ (.walk i j m read t) j :=
  ⟨fun hn Ξ hΞ => .walk (h.1 hn Ξ hΞ) hb hr, .walk h.2 hb hr⟩

/-- **A walk's read of its view at its index** (SPEC §46). -/
theorem walkGet {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (m : Bool) (hb : walkGetB m t.erase = true)
    (h : TTied p s Δ Γ t j) : TTied p s Δ Γ (.walkGet i j m t) j :=
  ⟨fun hn Ξ hΞ => .walkGet (h.1 hn Ξ hΞ) hb, .walkGet h.2 hb⟩

/-- **A recursive group's self-reference read for a member** (SPEC §20). -/
theorem selfCall {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (k n : Nat)
    (hb : selfCallB t.erase = true) (h : TTied p s Δ Γ t j) :
    TTied p s Δ Γ (.selfCall i j k n t) j :=
  ⟨fun hn Ξ hΞ => .selfCall (h.1 hn Ξ hΞ) hb, .selfCall h.2 hb⟩

/-- **The lend of a cell allocated for it** (SPEC §35). -/
theorem lendCell {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (m : Bool)
    (hb : lendCellB t.erase = true) (h : TTied p s Δ Γ t j) : TTied p s Δ Γ (.lendCell i j m t) j :=
  ⟨fun hn Ξ hΞ => .lendCell (h.1 hn Ξ hΞ) hb, .lendCell h.2 hb⟩

/-- **Codata written as an η-thunk** (SPEC §45): the derived node over the thunk's typed term. -/
theorem nuEta {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (f : Nat) (sv : Option Nat)
    (hb : nuEtaB f sv t.erase = true) (h : TTied p s Δ Γ t j) : TTied p s Δ Γ (.nuEta i j f sv t) j :=
  ⟨fun hn Ξ hΞ => .nuEta (h.1 hn Ξ hΞ) hb, .nuEta h.2 hb⟩

/-- **A `def`'s body at its use**: the `use` node over the body, its absorption the body's.
`[spec §10]` -/
theorem use {p : Pins} {s : CRow} {t : TExpr} {j : Jdg} (name : String) (decl : Nat)
    (targs : List CVTy) (h : TTied p s Δ Γ t j) :
    TTied p s Δ Γ (.use i j name decl targs (t.absF Δ) t) j :=
  ⟨fun hn Ξ hΞ => .use (h.1 hn Ξ hΞ) rfl, .use h.2 rfl⟩

/-- **Weakening of a checked derivation** by slots inserted inside its context, every live one at a
type the term's absorption holds of (`TDerivesAt.weaken`, `TDerivesP.weaken`).  `[spec §10]` -/
theorem weaken {p : Pins} {s : CRow} {Γa Γb Γp : Ctx CVTy} {t : TExpr} {j : Jdg} {f : AbsF}
    (h : TTied p s Δ (Γa ++ Γb) t j) (hf : t.absF Δ = some f) (hp : LiveP f.eval Γp) :
    TTied p s Δ (Γa ++ Γp ++ Γb) (t.shift Γp.length Γa.length) j :=
  ⟨fun hn Ξ hΞ => ((h.1 hn Ξ hΞ).weaken Γa Γb Γp f rfl hf hp).1,
    (h.2.weaken Γa Γb Γp f rfl hf hp).1⟩

/-- **A checked derivation at a larger lifetime context** (`TDerivesAt.weakenΔ`,
`TDerivesP.weakenΔ`).  `[spec §10]` -/
theorem weakenΔ {p : Pins} {s : CRow} {Δ' : LifeCtx} {t : TExpr} {j : Jdg}
    (h : TTied p s Δ Γ t j) (he : ExtΔ Δ Δ' t.lifeBinders) (hd : t.domFree = true) :
    TTied p s Δ' Γ (t.reAb Δ') j :=
  ⟨fun hn Ξ hΞ => (h.1 hn Ξ hΞ).weakenΔ Δ' he hd, h.2.weakenΔ Δ' he hd⟩

end TTied

end Frontend.Check
