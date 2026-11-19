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
import Core.Chain.SliceCopyKW835N
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
# `fundamentalN_all` assembled by induction on `CDerives`  `[spec §62]`

`docs/new-core/scope-835-tables.md` §10.13. `fundamentalN_all` is Core's `fundamentalC` at
`SemJN`, the relation at `KW`: one case per constructor of `CDerives`, in `fundamentalC`'s order
and with its case splits, each calling the rule's compatibility lemma at `cN`. The three rules with
no compatibility lemma are the conjuncts of `MissingN`, each stated as its `*_compatN` would be:
Core's lemma with `SemV`/`SemC` read as `SemJN`.

* `ReifyN` (Core's `reify_compatX`), `HandleVN` (Core's `handleV_compatC`), `HandleVBN` (Core's
  `handleV_compatCB`).
* `fundamentalN_all`: every derivation is in `SemJN`, from `MissingN`. No compatibility lemma takes
  a fragment premise.
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

/-- **`[conv]` at `SemJN`**: each same-term step by its own `*_compatN`. -/
theorem conv_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {k : ConvKind} {j j' : Jdg}
    (hc : JConv Δ Γ k j j') (h : SemJN (ℍ := ℍ) Δ Γ e j) : SemJN (ℍ := ℍ) Δ Γ e j' := by
  cases hc with
  | ret => exact ret_compatN h
  | ofRet => exact ofRet_compatN h
  | bangE => exact bangE_compatN h
  | boxI hΓ => exact boxI_compatN h hΓ
  | boxE => exact boxE_compatN h
  | immSub hle => exact immSub_compatN h hle
  | mutSub hle => exact mutSub_compatN h hle
  | codeErase => exact codeErase_compatN h
  | codeEraseB => exact codeEraseB_compatN h
  | roll hA hc => exact roll_compatN hA hc h
  | unroll => exact unroll_compatN h
  | nuIn hC => exact nuIn_compatN hC h
  | nuOut hC => exact nuOut_compatN hC h
  | effSub hle => exact sub_compatN hle h
  | alpha hα => exact alpha_compatN hα h

/-! ### The induction -/

/-- **Every constant is sound at `SemJN`**: `constK` at each kind is its constant's `*_compatN`.
`[spec §3]` -/
theorem constK_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (k : ConstKind) (hk : k.OK Δ)
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ k.E (.val (k.ty Δ.meetOfDom)) := by
  cases k with
  | unitI => exact unitI_compatN hΓ
  | copyBang => exact copyBang_compatN hΓ
  | releaseBang => exact releaseBang_compatN hΓ
  | alloc => exact alloc_compatN hΓ
  | free => exact free_compatN hΓ
  | tokMint => exact tokMint_compatN hΓ
  | tokBurn => exact tokBurn_compatN hΓ
  | swap => exact swap_compatN hΓ
  | copy => exact copy_compatN hΓ
  | releaseImm => exact releaseImm_compatN hΓ
  | releaseMut => exact releaseMut_compatN hΓ
  | releaseUnk => exact releaseUnk_compatN hΓ
  | lit c => exact lit_compatN c hΓ
  | hostOp op => exact hostOp_compatN op hΓ
  | arrNew => exact arrNew_compatN hΓ
  | arrFree => exact arrFree_compatN hΓ
  | arrSize => exact arrSize_compatN hΓ
  | arrReplace => exact arrReplace_compatN hΓ
  | arrLen => exact arrLen_compatN hΓ
  | arrGet => exact arrGet_compatN hΓ
  | arrCopy => exact arrCopy_compatN hΓ
  | arrRelease => exact arrRelease_compatN hΓ
  | countFold => exact countFold_compatN hΓ
  | countTry => exact countTry_compatN hΓ
  | boundedFix => exact boundedFix_compatN hΓ
  | iterate => exact iterate_compatN hk hΓ
  | divFuel => exact divFuel_compatN hk hΓ
  | sliceBorrowM _ _ x =>
      obtain ⟨hA, hB, hf₁, hf₂⟩ := hk
      exact sliceBorrowM_compatN x hΓ hA hB hf₁ hf₂
  | sliceBorrowI _ _ x =>
      obtain ⟨hsc, hA, hB, hf₁, hf₂⟩ := hk
      exact sliceBorrowI_compatN x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM => exact sliceGetM_compatN hΓ
  | sliceLenM => exact sliceLenM_compatN hΓ
  | sliceSplitI => exact sliceSplitI_compatN hΓ
  | sliceSplitM => exact sliceSplitM_compatN hΓ
  | sliceEmptyI => exact sliceEmptyI_compatN hΓ
  | sliceEmptyM => exact sliceEmptyM_compatN hΓ
  | arrEmpty => exact arrEmpty_compatN hΓ
  | sliceReplaceM => exact sliceReplaceM_compatN hΓ
  | sliceSwapM => exact sliceSwapM_compatN hΓ
  | sliceCopyM => exact sliceCopyM_compatN hΓ hk
  | withbor1 _ _ x => obtain ⟨_, hsc₁, hf₁, hf₂⟩ := hk; exact withbor1_compatN x hΓ hsc₁ hf₁ hf₂
  | withbor2 _ _ x => obtain ⟨_, hside, hf₁, hf₂⟩ := hk; exact withbor2_compatN x hΓ hside hf₁ hf₂
  | withbor3 _ _ _ x => obtain ⟨_, hf₁, hf₂⟩ := hk; exact withbor3_compatN x hΓ hf₁ hf₂
  | withload _ _ _ x => obtain ⟨_, hf₁, hf₂⟩ := hk; exact withload_compatN x hΓ hf₁ hf₂
  | withswap => exact withswap_compatN hΓ
  | withloadU _ _ _ _ x => obtain ⟨_, hf₁, hf₂, hS⟩ := hk; exact withloadU_compatN x hΓ hf₁ hf₂ hS
  | foldImm F y c R =>
      obtain ⟨hF, hG, hyM, hyR, hR⟩ := hk
      exact foldImm_compatN F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R => obtain ⟨hF, hG⟩ := hk; exact foldOwn_compatN F hF hG R hΓ
  | foldReuse F R => obtain ⟨hF, hG⟩ := hk; exact foldReuse_compatN F hF hG R hΓ
  | foldOwnG B Rs => exact foldOwnG_compatN B hk Rs hΓ
  | unfoldN C S => obtain ⟨hC, hS⟩ := hk; exact unfoldN_compatN hC S hS hΓ
  | unfoldK C G S => obtain ⟨hC, hG, hS⟩ := hk; exact unfoldK_compatN hC hG hS hΓ


/-- **Every derivation is sound at `SemJN`**, from `MissingN`: Core's `fundamentalC`, case by
case. -/
theorem fundamentalN_all (hm : MissingN (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {j : Jdg} (h : CDerives Δ Γ e j) : SemJN (ℍ := ℍ) Δ Γ e j := by
  obtain ⟨hHV, hHVB, hReify⟩ := hm
  induction h using CDerives.induct with
  | var h => exact var_compatN h
  | constK k hk hΓ => exact constK_compatN k hk hΓ
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatN hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatN ih
  | sumI₂ _ ih => exact sumI₂_compatN ih
  | thunkFb b hp _ hT ih => subst hT; cases b; exacts [thunkF_compatN ih, bangThunkF_compatN (hp rfl) ih]
  | thunkVb b hp hC _ hT ih =>
      subst hT; cases b; exacts [thunkV_compatN hC ih, bangThunkV_compatN (hp rfl) hC ih]
  | conv _ _ hc ih => exact conv_compatN hc ih
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
  | codeIb b hp _ hok hT ih =>
      subst hT; cases b; exacts [codeI_compatN ih hok, codeIB_compatN (hp rfl) ih hok]
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact hReify hS hcl ihres hΓ
  | withborUD k x hΓ _ hk hf₁ hf₂ hS hMS hDS _ hP _ ihd =>
      exact withborUD_compatN k x hΓ hk hf₁ hf₂ hS hMS hDS hP ihd
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowMU_compatN x hΓ hA hB hf₁ hf₂ hS ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowIU_compatN x hΓ hsc hA hB hf₁ hf₂ hS ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatN hs iha ihf
  | allEV _ hlt ih => exact allEV_compatN ih hlt
  | nuOutK hC hG hS hGf h => exact nuOutK_compatN hC hG hS hGf h
  | @effOp _ _ _ _ _ _ ab hf hab _ hB hd _ ih =>
      cases ab
      · obtain rfl := hB rfl; exact perform_compatN hf hab ih
      · exact raise_compatN hf hab (fun _ _ _ _ _ h => vN_noOwn_of_ownFree (hd rfl) h) ih
  | effAwait hΓ hfa ha haA hfc hc =>
      exact semJN_dead .nil hΓ (fun γ γ' => by
          rw [show substAll γ (awaitE _) = _ from psub_closedAt _ γ awaitE_closed le_rfl,
            show substAll γ' (awaitE _) = _ from psub_closedAt _ γ' awaitE_closed le_rfl])
        (await_compatN hfa ha haA hfc hc)
  | effLet hs hW hU _ _ ihM ihN => exact let_compatN hs hW hU ihM ihN
  | @effThenF _ _ _ _ _ _ _ _ _ _ SM SD hs hNZ _ hU hMS hDS hfin hP hF _ _ _ ihM ihN ihD =>
      cases hSD : Row.divB SD
      · exact then_compatN hs hNZ hU hMS hDS
          (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP ihM ihN ihD
      · exact thenDiv_compatN hs hNZ hU hMS hDS hP (hF.resolve_left (by simp [hSD])) ihM ihN ihD
  | @effHandleVO _ _ _ _ _ _ _ _ _ _ _ _ _ d? hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      cases d? with
      | none =>
        exact hHV hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
          (semJN_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe)
      | some d =>
        exact hHVB hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
          (semJN_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe) (hΓd d rfl)
          (Row.ansOutlives_ofEff_rc (hSd d rfl))
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatN hs hd hHr hHc ihc hnS hlen hSN hLin ihe
  | effHandleL hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatN hs hd hHr hHw hHn ihc hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatN (Val.lam b) hcl ihN

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
