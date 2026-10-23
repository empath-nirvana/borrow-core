import Frontend.Check.Rules

/-!
# Frontend — Check — a node's source, set after its check  `[spec §54]`

A node's `TInfo` is what the checker records of its source; no typing rule reads it. So the root's
`TInfo` of a checked term can be set after the term is checked: `TExpr.setInfo` replaces it, and
the typed derivations and the tie are kept (`TDerivesAt.setInfo`, `TDerivesP.setInfo`,
`TTied.setInfo`). The checker's `ascribe` arms set `TInfo.asc` this way (`Res.withAsc`).
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core

/-- The node with the source `i`. -/
def TExpr.setInfo (i : TInfo) : TExpr → TExpr
  | .var _ a2 a3 a4 => .var i a2 a3 a4
  | .unitI _ a2 => .unitI i a2
  | .tensorI _ a2 a3 a4 a5 a6 a7 => .tensorI i a2 a3 a4 a5 a6 a7
  | .sumI₁ _ a2 a3 a4 a5 => .sumI₁ i a2 a3 a4 a5
  | .sumI₂ _ a2 a3 a4 a5 => .sumI₂ i a2 a3 a4 a5
  | .thunkF _ a2 a3 a4 => .thunkF i a2 a3 a4
  | .thunkV _ a2 a3 a4 => .thunkV i a2 a3 a4
  | .ret _ a2 a3 a4 => .ret i a2 a3 a4
  | .bind _ a2 a3 a4 a5 a6 a7 => .bind i a2 a3 a4 a5 a6 a7
  | .force _ a2 a3 a4 => .force i a2 a3 a4
  | .lam _ a2 a3 a4 a5 => .lam i a2 a3 a4 a5
  | .lamDead _ a2 a3 a4 a5 => .lamDead i a2 a3 a4 a5
  | .app _ a2 a3 a4 a5 a6 a7 => .app i a2 a3 a4 a5 a6 a7
  | .withI _ a2 a3 a4 a5 a6 => .withI i a2 a3 a4 a5 a6
  | .proj₁ _ a2 a3 a4 a5 => .proj₁ i a2 a3 a4 a5
  | .proj₂ _ a2 a3 a4 a5 => .proj₂ i a2 a3 a4 a5
  | .topI _ a2 => .topI i a2
  | .unitE _ a2 a3 a4 a5 a6 => .unitE i a2 a3 a4 a5 a6
  | .tensorE _ a2 a3 a4 a5 a6 a7 a8 => .tensorE i a2 a3 a4 a5 a6 a7 a8
  | .sumE _ a2 a3 a4 a5 a6 a7 a8 a9 => .sumE i a2 a3 a4 a5 a6 a7 a8 a9
  | .zeroE _ a2 a3 a4 a5 => .zeroE i a2 a3 a4 a5
  | .allI _ a2 a3 a4 a5 a6 a7 => .allI i a2 a3 a4 a5 a6 a7
  | .allE _ a2 a3 a4 a5 a6 a7 => .allE i a2 a3 a4 a5 a6 a7
  | .bangThunkF _ a2 a3 a4 => .bangThunkF i a2 a3 a4
  | .bangThunkV _ a2 a3 a4 => .bangThunkV i a2 a3 a4
  | .bangE _ a2 a3 a4 => .bangE i a2 a3 a4
  | .copyBang _ a2 a3 => .copyBang i a2 a3
  | .forgetBang _ a2 a3 => .forgetBang i a2 a3
  | .boxI _ a2 a3 a4 a5 => .boxI i a2 a3 a4 a5
  | .boxE _ a2 a3 a4 a5 => .boxE i a2 a3 a4 a5
  | .immSub _ a2 a3 a4 a5 a6 => .immSub i a2 a3 a4 a5 a6
  | .mutSub _ a2 a3 a4 a5 a6 => .mutSub i a2 a3 a4 a5 a6
  | .alloc _ a2 a3 => .alloc i a2 a3
  | .free _ a2 a3 => .free i a2 a3
  | .swap _ a2 a3 a4 => .swap i a2 a3 a4
  | .copy _ a2 a3 a4 => .copy i a2 a3 a4
  | .forgetImm _ a2 a3 a4 => .forgetImm i a2 a3 a4
  | .forgetMut _ a2 a3 a4 => .forgetMut i a2 a3 a4
  | .forgetUnk _ a2 => .forgetUnk i a2
  | .lit _ a2 a3 => .lit i a2 a3
  | .hostOp _ a2 a3 => .hostOp i a2 a3
  | .arrNew _ a2 a3 => .arrNew i a2 a3
  | .arrFree _ a2 a3 => .arrFree i a2 a3
  | .arrSize _ a2 a3 => .arrSize i a2 a3
  | .arrReplace _ a2 a3 => .arrReplace i a2 a3
  | .arrLen _ a2 a3 a4 => .arrLen i a2 a3 a4
  | .arrGet _ a2 a3 a4 => .arrGet i a2 a3 a4
  | .arrCopy _ a2 a3 a4 => .arrCopy i a2 a3 a4
  | .arrForget _ a2 a3 a4 => .arrForget i a2 a3 a4
  | .countFold _ a2 a3 => .countFold i a2 a3
  | .countTry _ a2 a3 a4 => .countTry i a2 a3 a4
  | .boundedFix _ a2 a3 a4 => .boundedFix i a2 a3 a4
  | .iterate _ a2 a3 a4 a5 a6 => .iterate i a2 a3 a4 a5 a6
  | .divFuel _ a2 a3 a4 => .divFuel i a2 a3 a4
  | .reify _ a2 a3 a4 a5 a6 => .reify i a2 a3 a4 a5 a6
  | .sliceBorrowM _ a2 a3 a4 a5 => .sliceBorrowM i a2 a3 a4 a5
  | .sliceBorrowI _ a2 a3 a4 a5 => .sliceBorrowI i a2 a3 a4 a5
  | .sliceGetM _ a2 a3 a4 => .sliceGetM i a2 a3 a4
  | .sliceLenM _ a2 a3 a4 => .sliceLenM i a2 a3 a4
  | .sliceSplitI _ a2 a3 a4 => .sliceSplitI i a2 a3 a4
  | .sliceSplitM _ a2 a3 a4 => .sliceSplitM i a2 a3 a4
  | .sliceEmptyI _ a2 a3 a4 => .sliceEmptyI i a2 a3 a4
  | .sliceEmptyM _ a2 a3 a4 => .sliceEmptyM i a2 a3 a4
  | .sliceReplaceM _ a2 a3 a4 => .sliceReplaceM i a2 a3 a4
  | .sliceSwapM _ a2 a3 a4 => .sliceSwapM i a2 a3 a4
  | .withbor1 _ a2 a3 a4 a5 => .withbor1 i a2 a3 a4 a5
  | .withbor2 _ a2 a3 a4 a5 => .withbor2 i a2 a3 a4 a5
  | .withbor3 _ a2 a3 a4 a5 a6 => .withbor3 i a2 a3 a4 a5 a6
  | .withload _ a2 a3 a4 a5 a6 => .withload i a2 a3 a4 a5 a6
  | .withswap _ a2 a3 a4 a5 => .withswap i a2 a3 a4 a5
  | .withbor1U _ a2 a3 a4 a5 a6 a7 => .withbor1U i a2 a3 a4 a5 a6 a7
  | .withbor2U _ a2 a3 a4 a5 a6 a7 => .withbor2U i a2 a3 a4 a5 a6 a7
  | .withbor3U _ a2 a3 a4 a5 a6 a7 a8 => .withbor3U i a2 a3 a4 a5 a6 a7 a8
  | .withloadU _ a2 a3 a4 a5 a6 a7 => .withloadU i a2 a3 a4 a5 a6 a7
  | .sliceBorrowMU _ a2 a3 a4 a5 a6 a7 => .sliceBorrowMU i a2 a3 a4 a5 a6 a7
  | .sliceBorrowIU _ a2 a3 a4 a5 a6 a7 => .sliceBorrowIU i a2 a3 a4 a5 a6 a7
  | .lolliE _ a2 a3 a4 a5 a6 a7 => .lolliE i a2 a3 a4 a5 a6 a7
  | .allEV _ a2 a3 a4 a5 a6 a7 => .allEV i a2 a3 a4 a5 a6 a7
  | .ofRet _ a2 a3 a4 => .ofRet i a2 a3 a4
  | .roll _ a2 a3 a4 => .roll i a2 a3 a4
  | .unroll _ a2 a3 a4 => .unroll i a2 a3 a4
  | .foldImm _ a2 a3 a4 a5 a6 => .foldImm i a2 a3 a4 a5 a6
  | .foldOwn _ a2 a3 a4 => .foldOwn i a2 a3 a4
  | .foldReuse _ a2 a3 a4 => .foldReuse i a2 a3 a4
  | .nuIn _ a2 a3 a4 => .nuIn i a2 a3 a4
  | .nuOut _ a2 a3 a4 => .nuOut i a2 a3 a4
  | .unfoldN _ a2 a3 a4 => .unfoldN i a2 a3 a4
  | .effSub _ a2 a3 a4 a5 a6 => .effSub i a2 a3 a4 a5 a6
  | .effPerform _ a2 a3 a4 a5 => .effPerform i a2 a3 a4 a5
  | .effRaise _ a2 a3 a4 a5 a6 => .effRaise i a2 a3 a4 a5 a6
  | .effLet _ a2 a3 a4 a5 a6 a7 a8 => .effLet i a2 a3 a4 a5 a6 a7 a8
  | .effThen _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => .effThen i a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  | .effHandleV _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 => .effHandleV i a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  | .effHandleVB _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => .effHandleVB i a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  | .effHandleT _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 => .effHandleT i a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  | .effHandleL _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => .effHandleL i a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  | .letPoly _ a2 a3 a4 a5 a6 => .letPoly i a2 a3 a4 a5 a6
  | .lendR _ a2 a3 a4 a5 a6 a7 a8 a9 => .lendR i a2 a3 a4 a5 a6 a7 a8 a9
  | .lendLoopR _ a2 a3 a4 a5 a6 a7 a8 a9 a10 => .lendLoopR i a2 a3 a4 a5 a6 a7 a8 a9 a10
  | .nilDead _ a2 a3 a4 => .nilDead i a2 a3 a4
  | .dtor _ a2 a3 => .dtor i a2 a3
  | .allocS _ a2 a3 => .allocS i a2 a3
  | .freeS _ a2 a3 => .freeS i a2 a3
  | .withborSM _ a2 a3 a4 a5 => .withborSM i a2 a3 a4 a5
  | .withborSI _ a2 a3 a4 a5 => .withborSI i a2 a3 a4 a5
  | .withborF2M _ a2 a3 a4 a5 a6 a7 a8 => .withborF2M i a2 a3 a4 a5 a6 a7 a8
  | .withborF2I _ a2 a3 a4 a5 a6 a7 a8 => .withborF2I i a2 a3 a4 a5 a6 a7 a8
  | .litFn _ a2 a3 a4 => .litFn i a2 a3 a4
  | .divLit _ a2 a3 a4 a5 => .divLit i a2 a3 a4 a5
  | .walk _ a2 a3 a4 a5 => .walk i a2 a3 a4 a5
  | .walkGet _ a2 a3 a4 => .walkGet i a2 a3 a4
  | .selfCall _ a2 a3 a4 a5 => .selfCall i a2 a3 a4 a5
  | .lendCell _ a2 a3 a4 => .lendCell i a2 a3 a4
  | .nuEta _ a2 a3 a4 a5 => .nuEta i a2 a3 a4 a5
  | .use _ a2 a3 a4 a5 a6 a7 => .use i a2 a3 a4 a5 a6 a7

theorem TExpr.setInfo_erase (i : TInfo) (t : TExpr) : (t.setInfo i).erase = t.erase := by
  cases t <;> rfl

theorem TDerivesAt.setInfo {Ξ : EffCtx} {Δ : Lifetime.LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (i : TInfo) (h : TDerivesAt Ξ Δ Γ t j) : TDerivesAt Ξ Δ Γ (t.setInfo i) j := by
  cases h
  case effHandleT =>
    constructor
    case qc => assumption
    case hs => assumption
    all_goals assumption
  case effHandleL =>
    constructor
    case qc => assumption
    case hs => assumption
    all_goals assumption
  all_goals (simp only [TExpr.setInfo]; constructor <;> assumption)

theorem TDerivesP.setInfo {Δ : Lifetime.LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (i : TInfo) (h : TDerivesP Δ Γ t j) : TDerivesP Δ Γ (t.setInfo i) j := by
  cases h
  case effHandleT =>
    constructor
    case qc => assumption
    case hs => assumption
    all_goals assumption
  case effHandleL =>
    constructor
    case qc => assumption
    case hs => assumption
    all_goals assumption
  all_goals (simp only [TExpr.setInfo]; constructor <;> assumption)

theorem TTied.setInfo {p : Frontend.Check.Pins} {s : Frontend.Check.CRow} {Δ : Lifetime.LifeCtx}
    {Γ : Ctx VTy} {t : TExpr} {j : Jdg} (i : TInfo) (h : Frontend.Check.TTied p s Δ Γ t j) :
    Frontend.Check.TTied p s Δ Γ (t.setInfo i) j :=
  ⟨fun hp Ξ hΞ => (h.1 hp Ξ hΞ).setInfo i, h.2.setInfo i⟩

end BoCa.Fig16.LogRel.Core.Check

namespace Frontend.Check
open BoCa.Fig16.LogRel.Core.Check

/-- The checked term, its root recording that the program ascribes it (`TInfo.asc`). -/
def Res.withAsc {Δ : BoCa.Lifetime.LifeCtx} {T : List CVTy} {j : BoCa.Fig16.LogRel.Core.Jdg}
    (r : Res Δ T j) : Res Δ T j :=
  ⟨r.t.setInfo { r.t.info with asc := true }, r.sigs, r.pins,
    r.F.map fun _ h => TTied.setInfo _ h⟩

end Frontend.Check
