import Core.Examples

/-!
# Core — weakening by dead slots at the end of a context  `[spec §3]`

A derivation at `Γ` is one at `Γ ++ Γ'` when every slot of `Γ'` is consumed: the de Bruijn
indices of `Γ` are unchanged, and every rule's context premise (`SplitP`, `SoloP`, `DeadP`,
`CtxOutlives`, `∀I`'s freshness premise, `Ctx.Banged`) holds of the extended context.  It lets a
closed callback typed at `[]` sit beside a free variable.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {Γ' : Ctx VTy}

theorem deadP_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.DeadP (Γ ++ Γ')
  | [], _ => h'.toP
  | _ :: _, .cons h => .cons (deadP_append h' h)
  | _ :: _, .weaken hT h => .weaken hT (deadP_append h' h)

theorem splitP_append (h' : Ctx.Dead Γ') : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    Ctx.SplitP (Γ ++ Γ') (Γ₁ ++ Γ') (Γ₂ ++ Γ')
  | _, _, _, .nil => deadSplit h'
  | _, _, _, .left h => .left (splitP_append h' h)
  | _, _, _, .right h => .right (splitP_append h' h)
  | _, _, _, .dead h => .dead (splitP_append h' h)
  | _, _, _, .dup hT h => .dup hT (splitP_append h' h)

theorem soloP_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy} {i : Nat} {A : VTy}, Ctx.SoloP Γ i A →
    Ctx.SoloP (Γ ++ Γ') i A
  | _, _, _, .here h => .here (deadP_append h' h)
  | _, _, _, .there h => .there (soloP_append h' h)
  | _, _, _, .skip hS h => .skip hS (soloP_append h' h)

theorem dead_not_live : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ s ∈ Γ, s.live = false
  | [], _, _, hs => absurd hs (by simp)
  | _ :: _, .cons h, s, hs => by
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact dead_not_live h s hs

theorem live_append {P : Slot VTy → Prop} (h' : Ctx.Dead Γ') {Γ : Ctx VTy}
    (h : ∀ s ∈ Γ, s.live = true → P s) : ∀ s ∈ Γ ++ Γ', s.live = true → P s := by
  intro s hs hl
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs hl
  · rw [dead_not_live h' s hs] at hl; cases hl

theorem ctxOutlives_append (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    (h : CtxOutlives Δ Γ a) : CtxOutlives Δ (Γ ++ Γ') a :=
  ⟨h.1, live_append h' h.2⟩

theorem banged_append (h' : Ctx.Dead Γ') {Γ : Ctx VTy} (h : Ctx.Banged Γ) :
    Ctx.Banged (Γ ++ Γ') :=
  live_append (P := fun s => ∃ A, s.ty = .bang A) h' h

theorem flatLive_append (h' : Ctx.Dead Γ') {Γ : Ctx VTy} (h : Ctx.FlatLive Γ) :
    Ctx.FlatLive (Γ ++ Γ') :=
  live_append (P := fun s => s.ty.flat = true) h' h

theorem dead_append_dead {Γ Γ' : Ctx VTy} (h : Ctx.Dead Γ) (h' : Ctx.Dead Γ') :
    Ctx.Dead (Γ ++ Γ') := by
  induction h with
  | nil => exact h'
  | cons _ ih => exact .cons ih

/-- **Weakening** by consumed slots at the end, at every judgment index without the pin rules: R1
and R2 conclude at `r : Ref T` alone.  `[spec §83]` -/
theorem CDerivesX.append_dead {I : JIdx} (hpf : I.pin = false) {Γ' : Ctx VTy} (h' : Ctx.Dead Γ')
    {Δ : LifeCtx}
    {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesX I Δ Γ e j) : CDerivesX I Δ (Γ ++ Γ') e j := by
  induction h with
  | var hs => exact .var (soloP_append h' hs)
  | constK k hAt hk hΓ => exact .constK k hAt hk (deadP_append h' hΓ)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (splitP_append h' hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (splitP_append h' hs) ihM ihN
  | force hs hT => exact .force (soloP_append h' hs) hT
  | lam _ ih => exact .lam ih
  | lamDead _ ih => exact .lamDead ih
  | app hs _ hx ih => exact .app (splitP_append h' hs) ih (soloP_append h' hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (splitP_append h' hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (splitP_append h' hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (splitP_append h' hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (splitP_append h' hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append h' hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (flatLive_append h' hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (flatLive_append h' hp) hC ih
  | codeI _ hok ih =>
      obtain ⟨hok', hty⟩ := Ctx.CapOK.append (dead_not_live h') hok
      rw [← hty]; exact .codeI ih hok'
  | codeIB hp _ hok ih =>
      obtain ⟨hok', hty⟩ := Ctx.CapOK.append (dead_not_live h') hok
      rw [← hty]; exact .codeIB (flatLive_append h' hp) ih hok'
  | codeErase _ ih => exact .codeErase ih
  | codeEraseB _ ih => exact .codeEraseB ih
  | bangE _ ih => exact .bangE ih
  | boxI _ hΓ ih => exact .boxI ih (ctxOutlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | withborUD k x hΓ hx hk hf₁ hf₂ hS hMS hDS hSv hP _ ihd =>
      exact .withborUD k x (deadP_append h' hΓ) hx hk hf₁ hf₂ hS hMS hDS hSv hP ihd
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS _ ihd =>
      exact .sliceBorrowMU x (deadP_append h' hΓ) hA hB hf₁ hf₂ hS ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS _ ihd =>
      exact .sliceBorrowIU x (deadP_append h' hΓ) hsc hA hB hf₁ hf₂ hS ihd
  | lolliE hs _ _ iha ihf => exact .lolliE (splitP_append h' hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | nuOutK hC hG hS hGf hs => exact .nuOutK hC hG hS hGf (soloP_append h' hs)
  | effSub hle _ ih => exact .effSub hle ih
  | effPerform hAt hf hna hac _ ih => exact .effPerform hAt hf hna hac ih
  | effAwait hAt hΓ hfa ha haA hfc hc =>
      exact .effAwait hAt (dead_append_dead hΓ h') hfa ha haA hfc hc
  | effRaise hAt hf ha hrc hd _ ih => exact .effRaise hAt hf ha hrc hd ih
  | effLet hs hW hU _ _ ihM ihN =>
      exact .effLet (splitP_append h' hs)
        (fun hw => live_append (P := fun s => s.ty.OwnFree) h' (hW hw))
        (fun hu => banged_append h' (hU hu)) ihM ihN
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact .effThen (splitP_append h' hs) hNZ hUq (fun hu => banged_append h' (hU hu))
        hMS hDS hfin hP hSD ihM ihN ihD
  | effThenDiv hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact .effThenDiv (splitP_append h' hs) hNZ hUq (fun hu => banged_append h' (hU hu))
        hMS hDS hfin hP hSD ihM ihN ihD
  | effHandleV hAt hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact .effHandleV hAt (splitP_append h' hs) (deadP_append h' hd) hH.append ihc hn0 hnS hlen
        hdv ihe
  | effHandleVB hAt hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact .effHandleVB hAt (splitP_append h' hs) (deadP_append h' hd) hH.append ihc hn0 hnS hlen
        hdv ihe (ctxOutlives_append h' hΓd) hSd
  | effHandleT hAt hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact .effHandleT hAt (splitP_append h' hs) (deadP_append h' hd) hHr.append hHc.append ihc
        hn0 hnd hnS hlen hSN hLin ihe
  | effHandleL hAt hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact .effHandleL hAt (splitP_append h' hs) (deadP_append h' hd) hHr.append hHw.append
        hHn.append ihc hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin ihe
  | reify S B R res hAt hS hcl hres hΓ _ => exact .reify S B R res hAt hS hcl hres (deadP_append h' hΓ)
  | letPoly b hcl hV _ _ ihN => exact .letPoly b hcl hV ihN
  | alpha _ hα ih => exact .alpha ih hα
  | lendR hPin => exact absurd (hpf.symm.trans hPin) Bool.false_ne_true
  | lendLoopR hPin => exact absurd (hpf.symm.trans hPin) Bool.false_ne_true
  | nilDead hPin => exact absurd (hpf.symm.trans hPin) Bool.false_ne_true

/-- **Weakening** by consumed slots at the end. -/
theorem CDerives.append_dead (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : CDerives Δ (Γ ++ Γ') e j :=
  CDerivesX.append_dead rfl h' h

end BoCa.Fig16.LogRel.Core

end
