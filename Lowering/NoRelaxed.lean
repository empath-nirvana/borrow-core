import Frontend.Check.TDerives

/-!
# Lowering — a typed derivation with no relaxed rule  `[spec §54]`

The relaxed rules of SPEC §29 (`lendR`, `lendLoopR`, `nilDead`) are the only `TDerivesP` rules
`CDerives` lacks. A typed term with none of their nodes (`relaxedFree`) has a `CDerives`
derivation of its erasure (`TDerivesP.toC`), so it is in the relation by the Fundamental Property
with no hypothesis. Its proof is `TDerivesP.erase`'s, read in `CDerives`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- **No relaxed rule** (`lendR`, `lendLoopR`, `nilDead`, SPEC §29) anywhere in the typed term. -/
def relaxedFree : TExpr → Bool
  | .lendR .. | .lendLoopR .. | .nilDead .. => false
  | .tensorI _ _ _ _ _ t₁ t₂ => relaxedFree t₁ && relaxedFree t₂
  | .sumI₁ _ _ _ _ t => relaxedFree t
  | .sumI₂ _ _ _ _ t => relaxedFree t
  | .thunkF _ _ _ t => relaxedFree t
  | .thunkV _ _ _ t => relaxedFree t
  | .ret _ _ _ t => relaxedFree t
  | .bind _ _ _ _ _ tM tN => relaxedFree tM && relaxedFree tN
  | .lam _ _ _ _ t => relaxedFree t
  | .lamDead _ _ _ _ t => relaxedFree t
  | .app _ _ _ _ _ _ tM => relaxedFree tM
  | .withI _ _ _ _ tM tN => relaxedFree tM && relaxedFree tN
  | .proj₁ _ _ _ _ t => relaxedFree t
  | .proj₂ _ _ _ _ t => relaxedFree t
  | .unitE _ _ _ _ tV tM => relaxedFree tV && relaxedFree tM
  | .tensorE _ _ _ _ _ _ tV tM => relaxedFree tV && relaxedFree tM
  | .sumE _ _ _ _ _ _ tV t₁ t₂ => relaxedFree tV && relaxedFree t₁ && relaxedFree t₂
  | .zeroE _ _ _ _ tV => relaxedFree tV
  | .allI _ _ _ _ _ _ t => relaxedFree t
  | .allE _ _ _ _ _ _ t => relaxedFree t
  | .bangThunkF _ _ _ t => relaxedFree t
  | .bangThunkV _ _ _ t => relaxedFree t
  | .bangE _ _ _ t => relaxedFree t
  | .boxI _ _ _ _ t => relaxedFree t
  | .boxE _ _ _ _ t => relaxedFree t
  | .immSub _ _ _ _ _ t => relaxedFree t
  | .mutSub _ _ _ _ _ t => relaxedFree t
  | .reify _ _ _ _ _ tres => relaxedFree tres
  | .withbor1U _ _ _ _ _ _ td => relaxedFree td
  | .withbor2U _ _ _ _ _ _ td => relaxedFree td
  | .withbor3U _ _ _ _ _ _ _ td => relaxedFree td
  | .sliceBorrowMU _ _ _ _ _ _ td => relaxedFree td
  | .sliceBorrowIU _ _ _ _ _ _ td => relaxedFree td
  | .lolliE _ _ _ _ _ ta tf => relaxedFree ta && relaxedFree tf
  | .allEV _ _ _ _ _ _ t => relaxedFree t
  | .ofRet _ _ _ t => relaxedFree t
  | .roll _ _ _ t => relaxedFree t
  | .unroll _ _ _ t => relaxedFree t
  | .nuIn _ _ _ t => relaxedFree t
  | .nuOut _ _ _ t => relaxedFree t
  | .effSub _ _ _ _ _ t => relaxedFree t
  | .effPerform _ _ _ _ t => relaxedFree t
  | .effRaise _ _ _ _ _ t => relaxedFree t
  | .effLet _ _ _ _ _ _ tM tN => relaxedFree tM && relaxedFree tN
  | .effThen _ _ _ _ _ _ _ _ tM tN tD => relaxedFree tM && relaxedFree tN && relaxedFree tD
  | .effHandleV _ _ _ _ _ _ _ _ _ _ _ _ tc te => relaxedFree tc && relaxedFree te
  | .effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ _ tc te => relaxedFree tc && relaxedFree te
  | .effHandleT _ _ _ _ _ _ _ _ _ _ _ _ tc te => relaxedFree tc && relaxedFree te
  | .effHandleL _ _ _ _ _ _ _ _ _ _ _ _ _ tc te => relaxedFree tc && relaxedFree te
  | .letPoly _ _ _ _ tV tN => relaxedFree tV && relaxedFree tN
  | .litFn _ _ _ t => relaxedFree t
  | .divLit _ _ _ _ t | .walk _ _ _ _ t | .walkGet _ _ _ t | .selfCall _ _ _ _ t | .lendCell _ _ _ t | .nuEta _ _ _ _ t => relaxedFree t
  | .use _ _ _ _ _ _ t => relaxedFree t
  | _ => true

/-- **A typed derivation with no relaxed rule is a `CDerives` derivation of its erasure.** -/
theorem TDerivesP.toC {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesP Δ Γ t j) : relaxedFree t = true → CDerives Δ Γ t.erase j := by
  induction h with
  | var a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.var a0
  | unitI a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.unitI a0
  | tensorI a0 a1 _ a2 a3 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.tensorI a0 ih0 ih1
  | sumI₁ a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.sumI₁ ih0
  | sumI₂ a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.sumI₂ ih0
  | thunkF a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.thunkF ih0
  | thunkV a0 a1 a2 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      rw [a2] at ih0
      rw [a2]
      exact CDerives.thunkV a0 ih0
  | ret a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.ret ih0
  | bind a0 a1 _ a2 a3 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.bind a0 ih0 ih1
  | force a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.force a0
  | lam a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.lam ih0
  | lamDead a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.lamDead ih0
  | app a0 a1 _ a2 a3 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.app a0 ih0 a3
  | withI a0 a1 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.withI ih0 ih1
  | proj₁ a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.proj₁ ih0
  | proj₂ a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.proj₂ ih0
  | topI =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.topI
  | unitE a0 a1 _ a2 a3 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.unitE a0 ih0 ih1
  | tensorE a0 a1 _ a2 a3 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.tensorE a0 ih0 ih1
  | sumE a0 a1 _ a2 a3 a4 ih0 ih1 ih2 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1.1
      have ih1 := ih1 hf.1.2
      have ih2 := ih2 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.sumE a0 ih0 ih1 ih2
  | zeroE a0 a1 _ a2 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.zeroE a0 ih0
  | allI a0 a1 a2 a3 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.allI a0 a1 a2 ih0
  | allE a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.allE ih0 a1
  | bangThunkF a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.bangThunkF a0 ih0
  | bangThunkV a0 a1 a2 a3 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      rw [a3] at ih0
      rw [a3]
      exact CDerives.bangThunkV a0 a1 ih0
  | bangE a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.bangE ih0
  | copyBang a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.copyBang a0
  | forgetBang a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.forgetBang a0
  | boxI a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.boxI ih0 a1
  | boxE a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.boxE ih0
  | immSub a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.immSub ih0 a1
  | mutSub a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.mutSub ih0 a1
  | alloc a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.alloc a0
  | free a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.free a0
  | swap a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.swap a0
  | copy a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.copy a0
  | forgetImm a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.forgetImm a0
  | forgetMut a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.forgetMut a0
  | forgetUnk a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.forgetUnk a0
  | lit a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.lit a0 a1
  | hostOp a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.hostOp a0 a1
  | arrNew a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrNew a0 a1
  | arrFree a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrFree a0 a1
  | arrSize a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrSize a0 a1
  | arrReplace a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrReplace a0 a1
  | arrLen a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrLen a0 a1 a2
  | arrGet a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrGet a0 a1 a2
  | arrCopy a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrCopy a0 a1 a2
  | arrForget a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.arrForget a0 a1 a2
  | countFold a0 a1 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.countFold a0 a1
  | countTry a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.countTry a0 a1 a2
  | boundedFix a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.boundedFix a0 a1 a2
  | iterate a0 a1 a2 a3 a4 a5 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.iterate a0 a1 a2 a3 a4 a5
  | divFuel a0 a1 a2 a3 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.divFuel a0 a1 a2 a3
  | reify a0 a1 a2 a3 a4 a5 a6 a7 a8 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      rw [a7] at ih0
      rw [a7]
      rw [Expr.toVal_val]
      exact CDerives.reify a0 a1 a2 a3 a4 a5 ih0 a8
  | sliceBorrowM a0 a1 a2 a3 a4 a5 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceBorrowM a0 a1 a2 a3 a4 a5
  | sliceBorrowI a0 a1 a2 a3 a4 a5 a6 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceBorrowI a0 a1 a2 a3 a4 a5 a6
  | sliceGetM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceGetM a0 a1 a2
  | sliceLenM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceLenM a0 a1 a2
  | sliceSplitI a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceSplitI a0 a1 a2
  | sliceSplitM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceSplitM a0 a1 a2
  | sliceEmptyI a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceEmptyI a0 a1 a2
  | sliceEmptyM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceEmptyM a0 a1 a2
  | sliceReplaceM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceReplaceM a0 a1 a2
  | sliceSwapM a0 a1 a2 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceSwapM a0 a1 a2
  | withbor1 a0 a1 a2 a3 a4 a5 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor1 a0 a1 a2 a3 a4 a5
  | withbor2 a0 a1 a2 a3 a4 a5 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor2 a0 a1 a2 a3 a4 a5
  | withbor3 a0 a1 a2 a3 a4 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor3 a0 a1 a2 a3 a4
  | withload a0 a1 a2 a3 a4 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withload a0 a1 a2 a3 a4
  | withswap a0 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withswap a0
  | withbor1U a0 a1 a2 a3 a4 a5 a6 a7 a8 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor1U a0 a1 a2 a3 a4 a5 a6 a7 ih0
  | withbor2U a0 a1 a2 a3 a4 a5 a6 a7 a8 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor2U a0 a1 a2 a3 a4 a5 a6 a7 ih0
  | withbor3U a0 a1 a2 a3 a4 a5 a6 a7 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.withbor3U a0 a1 a2 a3 a4 a5 a6 ih0
  | withloadU a0 a1 a2 a3 a4 a5 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.withloadU a0 a1 a2 a3 a4 a5
  | sliceBorrowMU a0 a1 a2 a3 a4 a5 a6 a7 a8 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceBorrowMU a0 a1 a2 a3 a4 a5 a6 a7 ih0
  | sliceBorrowIU a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.sliceBorrowIU a0 a1 a2 a3 a4 a5 a6 a7 a8 ih0
  | lolliE a0 a1 _ a2 a3 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.lolliE a0 ih0 ih1
  | allEV a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.allEV ih0 a1
  | ofRet a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.ofRet ih0
  | roll a0 a1 a2 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.roll a0 a1 ih0
  | unroll a0 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.unroll ih0
  | foldImm a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.foldImm a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  | foldOwn a0 a1 a2 a3 a4 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.foldOwn a0 a1 a2 a3 a4
  | foldReuse a0 a1 a2 a3 a4 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.foldReuse a0 a1 a2 a3 a4
  | nuIn a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.nuIn a0 ih0
  | nuOut a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.nuOut a0 ih0
  | unfoldN a0 a1 a2 a3 =>
      intro hf
      dsimp only [TExpr.erase]
      exact CDerives.unfoldN a0 a1 a2 a3
  | effSub a0 a1 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.effSub a0 ih0
  | effPerform a0 a1 a2 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.effPerform a0 a1 ih0
  | effRaise a0 a1 a2 a3 ih0 =>
      intro hf
      simp only [relaxedFree] at hf
      have ih0 := ih0 hf
      dsimp only [TExpr.erase]
      exact CDerives.effRaise a0 a1 a2 ih0
  | effLet a0 a1 _ a2 a3 a4 a5 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.effLet a0 a2 a3 ih0 ih1
  | effThen a0 a1 _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 ih0 ih1 ih2 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1.1
      have ih1 := ih1 hf.1.2
      have ih2 := ih2 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.effThen a0 a2 a3 a4 a5 a6 a7 a8 a9 ih0 ih1 ih2
  | effHandleV a0 a1 _ a2 a3 a4 a5 a6 a7 a8 a9 a10 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.effHandleV a0 a2 a3 ih0 a5 a6 a7 a8 ih1
  | effHandleVB a0 a1 _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      exact CDerives.effHandleVB a0 a2 a3 ih0 a5 a6 a7 a8 ih1 a10 a11
  | effHandleT a0 a1 _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      rw [a6] at ih0
      rw [a6]
      exact CDerives.effHandleT a0 a2 a3 a4 ih0 a7 a8 a9 a10 a11 a12 ih1
  | effHandleL a0 a1 _ a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      rw [a7] at ih0
      rw [a7]
      exact CDerives.effHandleL a0 a2 a3 a4 a5 ih0 a8 a9 a10 a11 a12 a13 a14 a15 a16 ih1
  | letPoly a0 a1 a2 a3 a4 a5 ih0 ih1 =>
      intro hf
      simp only [relaxedFree, Bool.and_eq_true] at hf
      have ih0 := ih0 hf.1
      have ih1 := ih1 hf.2
      dsimp only [TExpr.erase]
      rw [a3] at ih0
      rw [a5] at ih1
      rw [a3, a5, Expr.letBody_shift, Expr.lamBody_lam]
      exact CDerives.letPoly a0 a1 ih0 (by rw [subst_unfill a1]; exact ih1)
  | lendR a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 ih0 ih1 =>
      intro hf; simp [relaxedFree] at hf
  | lendLoopR a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 ih0 ih1 ih2 =>
      intro hf; simp [relaxedFree] at hf
  | nilDead a0 a1 ih0 =>
      intro hf; simp [relaxedFree] at hf
  | dtor hA _ _ hΓ =>
      intro hf
      exact (dtor_wf hA hΓ)
  | allocS σ _ hΓ =>
      intro hf
      exact (d_allocS σ hΓ)
  | freeS σ _ hΓ =>
      intro hf
      exact (d_freeS σ hΓ)
  | withborSM σ c _ hσ hT hΔ hc _ _ hΓ =>
      intro hf
      exact (withborSM_wf hσ c hT hΔ hc hΓ)
  | withborSI σ c _ hσ hT hΔ hc _ _ hΓ =>
      intro hf
      exact (withborSI_wf hσ c hT hΔ hc hΓ)
  | withborF2M s hA hBo hTo _ hΓ =>
      intro hf
      exact (withborM2_wf s hA hBo hTo hΓ)
  | withborF2I s hA hB hBo hTo _ hΓ =>
      intro hf
      exact (withborI2_wf s hA hB hBo hTo hΓ)
  | litFn _ _ _ ih =>
      intro hf
      simp only [relaxedFree] at hf
      have ih := ih hf
      exact ih
  | divLit _ _ _ ih | walk _ _ _ ih | walkGet _ _ ih | selfCall _ _ ih | lendCell _ _ ih | nuEta _ _ ih =>
      intro hf
      simp only [relaxedFree] at hf
      have ih := ih hf
      exact ih
  | use _ _ ih =>
      intro hf
      simp only [relaxedFree] at hf
      have ih := ih hf
      exact ih

end BoCa.Fig16.LogRel.Core.Check
