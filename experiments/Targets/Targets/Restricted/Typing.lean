import Targets.Defs.Typing

/-!
# Targets — tier 1 as a typing system: `Extends`, `ExtendsNU` (DESIGN §1.2, §9 items 3, 11)

`tier1` (Core's `CDerives` at every admissible instance) is closed under every rule at every row
predicate, and holds tier 1; so it meets `Extends` and `ExtendsNU`.  `tier1NU` (the unr-free
fragment, `CDerivesNU`) meets `ExtendsNU`.  Each closure is the constructor applied pointwise.
`OutExtends OutJ.core` is `VOutlives.toLe`.  `[prog]`
-/

noncomputable section

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
  fun _ _ _ _ _ _ _ _ _ _ _ _ hs hNZ hUq hU hM hN hD η hη => CDerives.effThen (hs η hη) (hNZ η hη) (hUq η hη) (hU η hη) (hM η hη) (hN η hη) (hD η hη)

theorem rc_effHandle_tier1 (R : Row → Prop) : RC_effHandle tier1 R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hside hn0 he η hη =>
    match hside η hη with
    | ⟨hs, hs₁, hr, hc, hnS, hlen⟩ => CDerives.effHandle hs hs₁ hr hc hn0 hnS hlen (he η hη)

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
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hside hn0 he η hη =>
    match hside η hη with
    | ⟨hs, hs₁, hr, hc, hnS, hlen⟩ => CDerivesNU.effHandle (hR η hη) hs hs₁ hr hc hn0 hnS hlen (he η hη)

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
