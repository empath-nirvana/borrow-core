import Spike743.Natural

/-!
# Spike743 — round 5: the two schemas without `LifeNatural`, error escape, `[await-c]`

Round P stated `LendFrame` and `LoopFrame` as `LifeNatural → <compat lemma>`; round P2 refuted
`LifeNatural` (`NaturalK2.not_lifeNatural`), so round P's derivations from it are vacuous. Here
the two schemas are read without that premise (`LendFrameN`, `LoopFrameN`): they are the asserted
compatibility lemmas of the `withborUV` lend over `LendForm` (`ref k`, `hold k y`, `fam`) and of
the per-observation lend.

* **The merge.** #750's rules (`[await-c]`, `Row.ResumeOC` at R1, `PinFin`) and the round-3/4
  rules: `PinStop` took `Row.ResumeOC`, which `Row.ResumeOT` (W-tick) does not include, so W-tick
  no longer gave R1, and #750's nursery row (`tick` beside `await` and `cancelled`) was admitted by
  neither (`Spike750.Round2.not_resumeOC_nursery`, `not_resumeOT_nursery` below). The resolution
  widens both rows to one: `Row.ResumeOE` (W-tick, W-hold) and `Row.ResumeOCE` (R1).
* **Error escape** is not a new field: it is `RowOf true` widened (`Natural.RowOf`, now
  `Row.ResumeOE`), an abortive operation of closed data (`OpSig.EscapeO`) admitted beside `tick`
  and the cancellable `await`. `errEscape_of_frame` derives its compatibility lemma from
  `LendFrameN`, at every `LendForm` with `tk = true`.
* **Depth.** `fundamentalC_of_framesN` is `fundamentalC_pin`'s induction with each relaxed rule's
  case a frame at the induction hypothesis of its callback: a lend nested at any depth is a case of
  the inner derivation. No statement here has a depth, a count of lends or a level index.

Nothing here is a proof of either schema.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Round5
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Spike743.Natural (LendForm RowOf LendFrame LoopFrame)

/-! ### The schemas without `LifeNatural` -/

/-- **`LendFrame` without `LifeNatural`**: the relaxed `withborUV` lend's compatibility lemma at
every `LendForm`, its callback typed and in the relation, at `RowOf` (widened: `Row.ResumeOE` at
`tk = true`). -/
def LendFrameN : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (P V B : VTy) (Δb : LifeCtx) (tk : Bool)
    (d M : Expr) (S : Row),
    LendForm Δ x b P V B Δb tk →
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x B → NoThunkT B → RowOf tk S x →
    closedAt 1 M = true → closedAt 0 (lendCb M).1 = true → closedAt 0 d = true →
    SemV (ℍ := ℍ) Δ [] d (.lolli P .unit) →
    CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δb [⟨V, true⟩] M (CTy.effOf S (.box (.var x) B)) →
    SemC (ℍ := ℍ) Δ [⟨P, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor P B))

theorem lendFrame_of_N (h : LendFrameN (ℍ := ℍ)) : LendFrame (ℍ := ℍ) := fun _ => h

/-- **`LoopFrame` without `LifeNatural`**: the per-observation lend's compatibility lemma. -/
def LoopFrameN : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (A S B R : VTy) (N K s0 : Expr),
    Δ.find? x = none → Δ.meetOfDom.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → ¬ VFree x R → NoThunkT B → NoThunkT R → VScoped Δ A →
    closedAt 1 N = true → closedAt 1 K = true → closedAt 0 s0 = true →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.ret (.sum B S)) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.ret R) →
    SemV (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [] s0 S →
    SemC (ℍ := ℍ) Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))

theorem loopFrame_of_N (h : LoopFrameN (ℍ := ℍ)) : LoopFrame (ℍ := ℍ) := fun _ => h

/-! ### Depth: the fundamental property from the two schemas and `PinFin` -/

/-- **The Fundamental Property from the two schemas** (and `PinFin`, `[then]` with `Div` in the
finaliser's row, which is not a lend). `fundamentalC_pin`'s induction; each relaxed rule's case is
`LendFrameN` or `LoopFrameN` at the induction hypothesis of its callback (and steps). -/
theorem fundamentalC_of_framesN (hF : LendFrameN (ℍ := ℍ))
    (hL : LoopFrameN (ℍ := ℍ)) (hFin : PinFin (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {j : Jdg} (h : CDerivesP Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j := by
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
  | lamDead _ ih => exact lamDead_compatC ih
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
  | lit c hΓ => exact lit_compatX c hΓ
  | tokMint hΓ => exact tokMint_compatX hΓ
  | tokBurn hΓ => exact tokBurn_compatX hΓ
  | hostOp op hΓ => exact hostOp_compatX op hΓ
  | arrNew _ hΓ => exact arrNew_compatX hΓ
  | arrFree _ hΓ => exact arrFree_compatX hΓ
  | arrSize _ hΓ => exact arrSize_compatX hΓ
  | arrReplace _ hΓ => exact arrReplace_compatX hΓ
  | arrLen _ _ hΓ => exact arrLen_compatX hΓ
  | arrGet _ _ hΓ => exact arrGet_compatX hΓ
  | arrCopy _ _ hΓ => exact arrCopy_compatX hΓ
  | arrForget _ _ hΓ => exact arrForget_compatX hΓ
  | countFold _ hΓ => exact countFold_compatX hΓ
  | countTry _ _ hΓ => exact countTry_compatX hΓ
  | boundedFix _ _ hΓ => exact boundedFix_compatX hΓ
  | iterate _ _ _ _ hS hΓ => exact iterate_compatX hS hΓ
  | divFuel _ _ hS hΓ => exact divFuel_compatX hS hΓ
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact reify_compatX hS hcl ihres hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact sliceBorrowM_compatX x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact sliceBorrowI_compatX x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM _ _ hΓ => exact sliceGetM_compatX hΓ
  | sliceLenM _ _ hΓ => exact sliceLenM_compatX hΓ
  | sliceSplitI _ _ hΓ => exact sliceSplitI_compatX hΓ
  | sliceSplitM _ _ hΓ => exact sliceSplitM_compatX hΓ
  | sliceEmptyI _ _ hΓ => exact sliceEmptyI_compatX hΓ
  | sliceEmptyM _ _ hΓ => exact sliceEmptyM_compatX hΓ
  | arrEmpty _ hΓ => exact arrEmpty_compatX hΓ
  | sliceReplaceM _ _ hΓ => exact sliceReplaceM_compatX hΓ
  | sliceSwapM _ _ hΓ => exact sliceSwapM_compatX hΓ
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact withbor1_compatX x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatX hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS hdc _ ihd => exact withbor1U_compatX x hΓ hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS hdc _ ihd =>
      exact withbor2U_compatX x hΓ hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ _ hf₁ hf₂ hS hdc _ ihd => exact withbor3U_compatX x hΓ hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ _ hf₁ hf₂ hS => exact withloadU_compatX x hΓ hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowMU_compatX x hΓ hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowIU_compatX x hΓ hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih
  | roll hA hc _ ih => exact roll_compatX hA hc ih
  | unroll _ ih => exact unroll_compatX ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact foldImm_compatX F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R hΓ hF hG => exact foldOwn_compatX F hF hG R hΓ
  | foldReuse F R hΓ hF hG => exact foldReuse_compatX F hF hG R hΓ
  | foldOwnG B₀ Rs hΓ hB => exact FoldP.foldOwnG_compatX B₀ hB Rs hΓ
  | nuIn hC _ ih => exact nuIn_compatX hC ih
  | nuOut hC _ ih => exact nuOut_compatX hC ih
  | unfoldN C S hC hΓ => exact unfold_compatX hC S hΓ
  | effSub hle _ ih => exact sub_compatC hle ih
  | effPerform hf hna _ _ ih => exact perform_compatC hf hna ih
  | effAwait hΓ hfa ha haA hfc hc hcA => exact semC_dead .nil hΓ (await_compatC hfa ha haA hfc hc hcA)
  | effRaise hf ha hd _ ih => exact raise_compatC hf ha (fun _ _ _ _ h => vC_noOwn_of_ownFree hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatC hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact then_compatC hs hNZ hU hMS hDS (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂
        (by simp [OpSig.finRead, hc])) hP hSD ihM ihN ihD
  | effThenDiv hs hNZ _ hU hMS hDS hfin hP hcap _ _ _ ihM ihN ihD =>
      exact hFin _ _ _ _ _ _ _ _ _ _ _ _ hs hNZ hU hMS hDS hfin hP hcap ihM ihN ihD
  | effHandleV hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact handleV_compatC hs hd hH ihc hn0 hnS hlen hdv ihe
  | effHandleVB hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact handleV_compatCB hs hd hH ihc hn0 hnS hlen hdv ihe hΓd hSd
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatC hs hd hHr hHc ihc hn0 hnd hnS hlen hSN hLin ihe
  | effHandleL hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatC hs hd hHr hHw hHn ihc hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatC (Val.lam b) hcl ihN
  | lendR hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF _ _ _ _ _ _ _ _ _ _ _ (.ref false hT (by simpa [LendSide] using hside))
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toE) hM1 hcb hdc ihd
        (by simpa [lendView] using hM) (by simpa [lendView, SemJ] using ihM)
  | lendRI hb hx hbx hΔx hT hB hBn hsc hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF _ _ _ _ _ _ _ _ _ _ _ (.ref true hT (by simpa [LendSide] using hsc))
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toCE.toE) hM1 hcb hdc ihd
        (by simpa [lendView] using hM) (by simpa [lendView, SemJ] using ihM)
  | lendRF hb hx hbx hΔx hA hB hBn hsideA hsideB hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF _ _ _ _ _ _ _ _ _ _ _ (.fam hA hsideA hsideB)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendRT k hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF _ _ _ _ _ _ _ _ _ _ _ (.ref k hT hside)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendRH k y hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF _ _ _ _ _ _ _ _ _ _ _ (.hold k y hT hyT hyB hside hy hΔy)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendLoopR hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0 ihN ihK ihs0 =>
      exact hL _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0
        ihN ihK ihs0
  | @nilDead _ _ _ j hΓ _ ih => cases j <;> exact semC_dead .nil hΓ ih

/-! ### Every lend field, and `PinLaw`, from the two schemas -/

section Fields
variable (hF : LendFrameN (ℍ := ℍ)) (hL : LoopFrameN (ℍ := ℍ)) (hFin : PinFin (ℍ := ℍ))
include hF hL hFin

/-- **W-tick** (with the cancel path and error escape): `LendFrameN` at `ref k`. -/
theorem tick_of_frames : PinStopTick (ℍ := ℍ) :=
  fun Δ x b T B d M S k hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM =>
    hF _ _ _ _ _ _ _ _ _ _ _ (.ref k hT hside) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesN hF hL hFin hM)

/-- **W-hold** (with the cancel path and error escape): `LendFrameN` at `hold k y`. -/
theorem hold_of_frames : PinStopHold (ℍ := ℍ) :=
  fun Δ x y b T B d M S k hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc hd hM =>
    hF _ _ _ _ _ _ _ _ _ _ _ (.hold k y hT hyT hyB hside hy hΔy) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesN hF hL hFin hM)

/-- **R1** at #750's widened row and error escape (`Row.ResumeOCE`): W-tick at `k = false`. -/
theorem stop_of_frames : PinStop (ℍ := ℍ) :=
  Spike743.Round3.pinStop_of_tick (tick_of_frames hF hL hFin)

theorem stopImm_of_frames : PinStopImm (ℍ := ℍ) :=
  Spike743.Round3.pinStopImm_of_tick (tick_of_frames hF hL hFin)

/-- **W-nest**: `LendFrameN` at `fam`. -/
theorem nest_of_frames : PinNest (ℍ := ℍ) :=
  fun Δ x b A B d M S hb hx hbx hΔx hA hB hBn hsideA hsideB hS hM1 hcb hdc hd hM =>
    hF _ _ _ _ _ _ _ _ _ _ _ (.fam hA hsideA hsideB) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesN hF hL hFin hM)

/-- **R2**: `LoopFrameN`. -/
theorem loop_of_frames : PinLoop (ℍ := ℍ) :=
  fun Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0 =>
    hL Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0
      (fundamentalC_of_framesN hF hL hFin hN') (fundamentalC_of_framesN hF hL hFin hK)
      (fundamentalC_of_framesN hF hL hFin hs0)

/-- **`PinLaw` from the two schemas and `PinFin`.** Six lend fields, two schemas: no field is
per depth, per holder or per program. -/
theorem pinLaw_of_frames : PinLaw (ℍ := ℍ) where
  stop := stop_of_frames hF hL hFin
  loop := loop_of_frames hF hL hFin
  stopImm := stopImm_of_frames hF hL hFin
  nest := nest_of_frames hF hL hFin
  tick := tick_of_frames hF hL hFin
  hold := hold_of_frames hF hL hFin
  fin := hFin

end Fields

/-! ### Error escape: an instance of `LendFrame`

The rule: a relaxed lend's callback may raise an abortive operation of closed data that does not
mention the lend (`OpSig.EscapeO`), whose handler is outside the lend. The unwind runs the
finalisers between the raise and the handler, the lend's own (`withborUE`'s `unwind d r`: the place
goes to its owner's destructor) among them, at every level the error crosses. At a nursery
(`hold k y`) the children are slots of the callback: `[let]`'s `hW` refuses a task live across an
abortive operation (`Spike750.Premises.not_drop_task`), so the program cancels them in a finaliser
(`[then]`) before the error crosses the lend. -/

/-- **Error escape, stated**: the relaxed lend of any `tk = true` form at a row holding escaping
errors (`Row.ResumeOE`) is in the relation. -/
def ErrEscape : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (P V B : VTy) (Δb : LifeCtx)
    (d M : Expr) (S : Row),
    LendForm Δ x b P V B Δb true →
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x B → NoThunkT B → Row.ResumeOE S x →
    closedAt 1 M = true → closedAt 0 (lendCb M).1 = true → closedAt 0 d = true →
    SemV (ℍ := ℍ) Δ [] d (.lolli P .unit) →
    CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δb [⟨V, true⟩] M (CTy.effOf S (.box (.var x) B)) →
    SemC (ℍ := ℍ) Δ [⟨P, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor P B))

/-- **Error escape is `LendFrameN` at `RowOf true`**: no third schema. -/
theorem errEscape_of_frame (h : LendFrameN (ℍ := ℍ)) : ErrEscape (ℍ := ℍ) :=
  fun Δ x b P V B Δb d M S hform hb hx hbx hΔx hB hBn hS hM1 hcb hdc hd hM hsem =>
    h Δ x b P V B Δb true d M S hform hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc
      hd hM hsem

/-- And conversely `LendFrameN` at `tk = true` is error escape: the two are the same statement. -/
theorem frame_true_of_errEscape (h : ErrEscape (ℍ := ℍ)) :
    ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (P V B : VTy) (Δb : LifeCtx)
      (d M : Expr) (S : Row),
      LendForm Δ x b P V B Δb true →
      Δ.Defines b → Δ.find? x = none → b.mentions x = false →
      (∀ y u, Δ.find? y = some u → u.mentions x = false) →
      ¬ VFree x B → NoThunkT B → RowOf true S x →
      closedAt 1 M = true → closedAt 0 (lendCb M).1 = true → closedAt 0 d = true →
      SemV (ℍ := ℍ) Δ [] d (.lolli P .unit) →
      CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B))) →
      SemC (ℍ := ℍ) Δb [⟨V, true⟩] M (CTy.effOf S (.box (.var x) B)) →
      SemC (ℍ := ℍ) Δ [⟨P, true⟩]
        (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
        (CTy.effOf S (.tensor P B)) :=
  fun Δ x b P V B Δb d M S hform hb hx hbx hΔx hB hBn hS hM1 hcb hdc hd hM hsem =>
    h Δ x b P V B Δb d M S hform hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc hd
      hM hsem

/-! ### The rows -/

/-- A cancellable `await : 1 ↠^lin 1 + 1` at the name `1`. -/
def await1 : OpSig := ⟨1, 0, .lin, .unit, .sum .unit .unit, .ret .unit⟩

/-- Its `cancelled : 1 ↠ 0`. -/
def cancelled1 : OpSig := ⟨1, 1, .cancel, .unit, .zero, .ret .unit⟩

/-- A completion wait `1 ↠^lin 1` at the name `1`, operation `2`: resuming, not cancellable. -/
def complete1 : OpSig := ⟨1, 2, .lin, .unit, .unit, .ret .unit⟩

/-- An error `raise : i32 ↠ 0` at the name `3` (`pinRaiseSig`). -/
abbrev raise3 : OpSig := pinRaiseSig

/-- **The nursery's row with error escape**: the children's `await`, its `cancelled`, the wait's
`tick`, the completion wait, and an error. -/
abbrev rowNE : Row := [await1, cancelled1, tickSig, complete1, raise3]

theorem lendO_await1 (x : LifeVar) : OpSig.LendO x await1 :=
  .inr (.inl ⟨rfl, by decide, fun h => by simp [await1, VFree] at h, fun _ _ => .unit, trivial⟩)

theorem escapeO_cancelled1 (x : LifeVar) : OpSig.EscapeO x cancelled1 :=
  ⟨rfl, by decide, fun h => by simp [cancelled1, VFree] at h, fun _ _ => .unit, trivial⟩

theorem escapeO_raise3 (x : LifeVar) : OpSig.EscapeO x raise3 :=
  ⟨rfl, by decide, fun h => by simp [pinRaiseSig, VFree] at h, fun _ _ => .int, trivial⟩

theorem lendO_complete1 (x : LifeVar) : OpSig.LendO x complete1 :=
  .inl ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [complete1, VFree] at h,
    fun _ _ => .unit, trivial⟩

/-- The completion wait is not cancellable: `[perform]` takes it, `[await-c]` does not. -/
theorem complete1_not_awaitB : complete1.awaitB = false := by decide

theorem resumeOE_rowNE (x : LifeVar) : Row.ResumeOE rowNE x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · exact .inr (lendO_await1 x)
  · exact .inr (.inr (.inr (escapeO_cancelled1 x)))
  · exact .inl rfl
  · exact .inr (lendO_complete1 x)
  · exact .inr (.inr (.inr (escapeO_raise3 x)))

/-- Round 3's row refuses it: `await` answers `1 + 1`, and `cancelled` and the error abort. -/
theorem not_resumeOT_rowNE (x : LifeVar) : ¬ Row.ResumeOT rowNE x := by
  intro h
  rcases h await1 (by simp) with h | h
  · exact absurd (congrArg OpSig.n h) (by simp [await1, tickSig, divEff])
  · exact absurd h.2.2.2.1 (by simp [await1])

/-- #750's row refuses it: `tick`. -/
theorem not_resumeOC_rowNE (x : LifeVar) : ¬ Row.ResumeOC rowNE x := by
  intro h
  rcases h tickSig (by simp) with h | h | h
  · exact absurd h.2.2.2.1 (by simp [tickSig, nextTy])
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)

/-- Without the error, the row #750's nursery needs (`Spike750.Round2.rowNursery`'s shape) is
refused by both rules and admitted by the merged one. -/
theorem not_resumeOT_nursery (x : LifeVar) : ¬ Row.ResumeOT [await1, cancelled1, tickSig] x := by
  intro h
  rcases h await1 (by simp) with h | h
  · exact absurd (congrArg OpSig.n h) (by simp [await1, tickSig, divEff])
  · exact absurd h.2.2.2.1 (by simp [await1])

theorem resumeOE_nursery (x : LifeVar) : Row.ResumeOE [await1, cancelled1, tickSig] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact .inr (lendO_await1 x)
  · exact .inr (.inr (.inr (escapeO_cancelled1 x)))
  · exact .inl rfl

/-- R1's row with an error and no `tick`: admitted by `Row.ResumeOCE`, refused by
`Row.ResumeOC` (the error is not a `cancelled`: operation `0`, at `i32`). -/
theorem resumeOCE_err (x : LifeVar) : Row.ResumeOCE [await1, cancelled1, raise3] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact lendO_await1 x
  · exact .inr (.inr (escapeO_cancelled1 x))
  · exact .inr (.inr (escapeO_raise3 x))

theorem not_resumeOC_err (x : LifeVar) : ¬ Row.ResumeOC [await1, cancelled1, raise3] x := by
  intro h
  rcases h raise3 (by simp) with h | h | h
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.2.1 (by decide)

/-- **What escape refuses.** An error carrying the view out: its argument mentions `'x`. -/
theorem not_escapeO_view (x : LifeVar) :
    ¬ OpSig.EscapeO x ⟨3, 0, .cancel, .imm (.var x) .unit, .zero, .ret .unit⟩ := by
  intro h
  exact h.2.2.1 (by simp [VFree, Lifetime.Life.mentions])

/-- An error carrying a closure: not `NoThunkT`. -/
theorem not_escapeO_thunk (x : LifeVar) (C : CTy) :
    ¬ OpSig.EscapeO x ⟨3, 0, .cancel, .thunk C, .zero, .ret .unit⟩ := by
  intro h
  exact h.2.2.2.2

end Spike743.Round5

end
