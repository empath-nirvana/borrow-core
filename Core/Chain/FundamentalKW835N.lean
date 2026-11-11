import Core.Chain.ConstKW835N
import Core.Chain.EffKW835N
import Core.Chain.LetKW835N
import Core.Chain.ThenKW835N
import Core.Chain.FuelKW835N
import Core.Chain.HandleTKW835N
import Core.Chain.HandleLKW835N
import Core.Chain.UnwindKW835N
import Core.Chain.NuKW835N
import Core.Chain.CountKW835N
import Core.Chain.FamKW835N
import Core.Chain.FamOpsKW835N
import Core.Chain.FamImmKW835N
import Core.Chain.MuKW835N
import Core.Chain.FoldGKW835N
import Core.Chain.FoldImmKW835N
import Core.Chain.BorrowKW835N
import Core.Chain.ImmLendKW835N
import Core.Chain.WithloadKW835N
import Core.Chain.RulesKW835N
import Core.Fundamental
import Core.Chain.CodeRulesKW835N
import Core.Chain.CodeNuOutKW835N

/-!
# `FundamentalN` assembled by induction on `CDerives`  `[spec §62]`

`docs/new-core/scope-835-tables.md` §10.13. `fundamentalN_all` is Core's `fundamentalC` at
`SemJN`, the relation at `KW`: one case per constructor of `CDerives`, in `fundamentalC`'s order
and with its case splits, each calling the rule's compatibility lemma at `cN`. The three rules with
no compatibility lemma are the conjuncts of `MissingN`, each stated as its `*_compatN` would be:
Core's lemma with `SemV`/`SemC` read as `SemJN`.

* `ReifyN` (Core's `reify_compatX`), `HandleVN` (Core's `handleV_compatC`), `HandleVBN` (Core's
  `handleV_compatCB`).
* `fundamentalN_all`: every derivation is in `SemJN`, from `MissingN`. No compatibility lemma takes
  a fragment premise.
* `fundamentalN_of`: `FundamentalN` read off it, the fragment premise unused.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (jdgC)

/-! ### The three rules with no chain lemma -/

/-- `reify_res` (Core's `reify_compatX`). -/
def ReifyN : Prop :=
  ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {B R : VTy} {res : Val},
    (∀ o ∈ S, o.n ≠ divEff) → closedAt 0 res.1 = true →
    SemJN (ℍ := ℍ) Δ [] (.val res) (.val (resTy S B R)) → Ctx.DeadP Γ →
    SemJN (ℍ := ℍ) Δ Γ (.val (reifyV res)) (.val (reifyTy S B R))

/-- `[handle]` at a value form (Core's `handleV_compatC`). -/
def HandleVN : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row} {E : List (Qual × VTy × VTy)}
    {fs : Nat → CTy} {n : UInt32} {A R : VTy},
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
    SemJN (ℍ := ℍ) Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))) →
    n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    Row.divB (Row.ofEff n E 0 fs ++ S) = false →
    SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) →
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))

/-- BOXED-κ `[handle]` (Core's `handleV_compatCB`). -/
def HandleVBN : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row} {E : List (Qual × VTy × VTy)}
    {fs : Nat → CTy} {n : UInt32} {A R : VTy} {d : Lifetime.Life},
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
    SemJN (ℍ := ℍ) Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyB S R d E fs))) →
    n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    Row.divB (Row.ofEff n E 0 fs ++ S) = false →
    SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) →
    CtxOutlives Δ Γ₂ d → Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S) →
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) H e) (.comp (CTy.effOf S R))

/-- **The rules the chain has no lemma for**, each as its `*_compatN` would be. -/
def MissingN : Prop :=
  HandleVN (ℍ := ℍ) ∧ HandleVBN (ℍ := ℍ) ∧ ReifyN (ℍ := ℍ)

/-! ### The induction -/

/-- **Every derivation is sound at `SemJN`**, from `MissingN`: Core's `fundamentalC`, case by
case. -/
theorem fundamentalN_all (hm : MissingN (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {j : Jdg} (h : CDerives Δ Γ e j) : SemJN (ℍ := ℍ) Δ Γ e j := by
  obtain ⟨hHV, hHVB, hReify⟩ := hm
  induction h with
  | var h => exact var_compatN h
  | unitI h => exact unitI_compatN h
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatN hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatN ih
  | sumI₂ _ ih => exact sumI₂_compatN ih
  | thunkF _ ih => exact thunkF_compatN ih
  | thunkV hC _ ih => exact thunkV_compatN hC ih
  | ret _ ih => exact ret_compatN ih
  | bind hs _ _ ihM ihN => exact bind_compatN hs ihM ihN
  | force h hT => exact force_compatN h hT
  | lam _ ih => exact lam_compatN ih
  | lamDead _ ih => exact lamDead_compatN ih
  | app hs _ hx ih => exact app_compatN hs ih hx
  | withI _ _ ihM ihN => exact withI_compatN ihM ihN
  | proj₁ _ ih => exact proj₁_compatN ih
  | proj₂ _ ih => exact proj₂_compatN ih
  | topI => exact topI_compatN
  | unitE hs _ _ ihV ihM => exact unitE_compatN hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatN hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatN hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatN hs ihV
  | allI hbx hΔx hΓx _ ih => exact allI_compatN hbx hΔx hΓx ih
  | allE _ hlt ih => exact allE_compatN ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatN hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatN hp hC ih
  | codeI _ hok ih => exact codeI_compatN ih hok
  | codeIB hp _ hok ih => exact codeIB_compatN hp ih hok
  | codeErase _ ih => exact codeErase_compatN ih
  | codeEraseB _ ih => exact codeEraseB_compatN ih
  | bangE _ ih => exact bangE_compatN ih
  | copyBang hΓ => exact copyBang_compatN hΓ
  | releaseBang hΓ => exact releaseBang_compatN hΓ
  | boxI _ hΓ ih => exact boxI_compatN ih hΓ
  | boxE _ ih => exact boxE_compatN ih
  | immSub _ hle ih => exact immSub_compatN ih hle
  | mutSub _ hle ih => exact mutSub_compatN ih hle
  | alloc hΓ => exact alloc_compatN hΓ
  | free hΓ => exact free_compatN hΓ
  | tokMint hΓ => exact tokMint_compatN hΓ
  | tokBurn hΓ => exact tokBurn_compatN hΓ
  | swap hΓ => exact swap_compatN hΓ
  | copy hΓ => exact copy_compatN hΓ
  | releaseImm hΓ => exact releaseImm_compatN hΓ
  | releaseMut hΓ => exact releaseMut_compatN hΓ
  | releaseUnk hΓ => exact releaseUnk_compatN hΓ
  | lit c hΓ => exact lit_compatN c hΓ
  | hostOp op hΓ => exact hostOp_compatN op hΓ
  | arrNew _ hΓ => exact arrNew_compatN hΓ
  | arrFree _ hΓ => exact arrFree_compatN hΓ
  | arrSize _ hΓ => exact arrSize_compatN hΓ
  | arrReplace _ hΓ => exact arrReplace_compatN hΓ
  | arrLen _ _ hΓ => exact arrLen_compatN hΓ
  | arrGet _ _ hΓ => exact arrGet_compatN hΓ
  | arrCopy _ _ hΓ => exact arrCopy_compatN hΓ
  | arrRelease _ _ hΓ => exact arrRelease_compatN hΓ
  | countFold _ hΓ => exact countFold_compatN hΓ
  | countTry _ _ hΓ => exact countTry_compatN hΓ
  | boundedFix _ _ hΓ => exact boundedFix_compatN hΓ
  | iterate _ _ _ _ hS hΓ => exact iterate_compatN hS hΓ
  | divFuel _ _ hS hΓ => exact divFuel_compatN hS hΓ
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact hReify hS hcl ihres hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact sliceBorrowM_compatN x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact sliceBorrowI_compatN x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM _ _ hΓ => exact sliceGetM_compatN hΓ
  | sliceLenM _ _ hΓ => exact sliceLenM_compatN hΓ
  | sliceSplitI _ _ hΓ => exact sliceSplitI_compatN hΓ
  | sliceSplitM _ _ hΓ => exact sliceSplitM_compatN hΓ
  | sliceEmptyI _ _ hΓ => exact sliceEmptyI_compatN hΓ
  | sliceEmptyM _ _ hΓ => exact sliceEmptyM_compatN hΓ
  | arrEmpty _ hΓ => exact arrEmpty_compatN hΓ
  | sliceReplaceM _ _ hΓ => exact sliceReplaceM_compatN hΓ
  | sliceSwapM _ _ hΓ => exact sliceSwapM_compatN hΓ
  | withbor1 x hΓ _ hsc₁ hf₁ hf₂ => exact withbor1_compatN x hΓ hsc₁ hf₁ hf₂
  | withbor2 x hΓ _ hside hf₁ hf₂ => exact withbor2_compatN x hΓ hside hf₁ hf₂
  | withbor3 x hΓ _ hf₁ hf₂ => exact withbor3_compatN x hΓ hf₁ hf₂
  | withload x hΓ _ hf₁ hf₂ => exact withload_compatN x hΓ hf₁ hf₂
  | withswap hΓ => exact withswap_compatN hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS _ ihd =>
      exact withbor1U_compatN x hΓ hsc₁ hf₁ hf₂ hS ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS _ ihd =>
      exact withbor2U_compatN x hΓ hside hf₁ hf₂ hS ihd
  | withbor3U x hΓ _ hf₁ hf₂ hS _ ihd => exact withbor3U_compatN x hΓ hf₁ hf₂ hS ihd
  | withloadU x hΓ _ hf₁ hf₂ hS => exact withloadU_compatN x hΓ hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowMU_compatN x hΓ hA hB hf₁ hf₂ hS ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowIU_compatN x hΓ hsc hA hB hf₁ hf₂ hS ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatN hs iha ihf
  | allEV _ hlt ih => exact allEV_compatN ih hlt
  | ofRet _ ih => exact ofRet_compatN ih
  | roll hA hc _ ih => exact roll_compatN hA hc ih
  | unroll _ ih => exact unroll_compatN ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact foldImm_compatN F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R hΓ hF hG => exact foldOwn_compatN F hF hG R hΓ
  | foldReuse F R hΓ hF hG => exact foldReuse_compatN F hF hG R hΓ
  | foldOwnG B Rs hΓ hB => exact foldOwnG_compatN B hB Rs hΓ
  | nuIn hC _ ih => exact nuIn_compatN hC ih
  | nuOut hC _ ih => exact nuOut_compatN hC ih
  | unfoldN C S hC hS hΓ => exact unfoldN_compatN hC S hS hΓ
  | unfoldK C G S hC hG hS hΓ => exact unfoldK_compatN hC hG hS hΓ
  | nuOutK hC hG hS hGf h => exact nuOutK_compatN hC hG hS hGf h
  | effSub hle _ ih => exact sub_compatN hle ih
  | effPerform hf hna _ _ ih => exact perform_compatN hf hna ih
  | effAwait hΓ hfa ha haA hfc hc =>
      exact semJN_dead .nil hΓ (fun γ γ' => by
          rw [show substAll γ (awaitE _) = _ from psub_closedAt _ γ awaitE_closed le_rfl,
            show substAll γ' (awaitE _) = _ from psub_closedAt _ γ' awaitE_closed le_rfl])
        (await_compatN hfa ha haA hfc hc)
  | effRaise hf ha _ hd _ ih =>
      exact raise_compatN hf ha (fun _ _ _ _ _ h => vN_noOwn_of_ownFree hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatN hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP _ _ _ _ ihM ihN ihD =>
      exact then_compatN hs hNZ hU hMS hDS
        (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP ihM ihN ihD
  | @effThenDiv _ _ _ _ _ _ _ _ _ _ SM SD hs hNZ _ hU hMS hDS hfin hP hcap _ _ _ ihM ihN ihD =>
      cases hSD : Row.divB SD
      · exact then_compatN hs hNZ hU hMS hDS
          (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP ihM ihN ihD
      · exact thenDiv_compatN hs hNZ hU hMS hDS hP hcap ihM ihN ihD
  | effHandleV hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact hHV hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semJN_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe)
  | effHandleVB hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact hHVB hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semJN_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe) hΓd
        (Row.ansOutlives_ofEff_rc hSd)
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatN hs hd hHr hHc ihc hnS hlen hSN hLin ihe
  | effHandleL hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatN hs hd hHr hHw hHn ihc hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatN (Val.lam b) hcl ihN
  | alpha _ hα ih => exact alpha_compatN hα ih

/-- **`FundamentalN` from `MissingN`**: `fundamentalN_all`, the fragment premise unused. -/
theorem fundamentalN_of (h : MissingN (ℍ := ℍ)) : FundamentalN (ℍ := ℍ) :=
  fun _ _ _ _ hder _ => fundamentalN_all h hder

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
