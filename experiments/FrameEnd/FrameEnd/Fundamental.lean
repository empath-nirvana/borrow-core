import Support.Dynamics.Machine
import Support.LogicalRelation.Adequacy
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Statics.Contexts
import Support.Statics.Presupposed
import FrameEnd.Compatibility

/-!
# FrameEnd — Fundamental

`[TR]` 6.151 at `SemX` and adequacy from a typing derivation, over the relaxed typed world
(`FrameLife`'s second conjunct non-strict).  The induction is `Paper/S6_8`'s `fundamental`
and the adequacy chain is `Paper/CONF/Results.lean`'s, each read at this directory's
`wpTS`/`SemX`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.FrameEnd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[TR]` 6.151 at the relaxed `SemX`: induction on the derivation, each node closed by its
`_compatX` lemma. -/
theorem fundamental :
    ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
      DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T := by
  intro Δ Γ e T hD
  induction hD with
  | var h => intro _ _; exact id_compatX h
  | unitI h => intro _ _; exact unitI_compatX h
  | unitE hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact unitE_compatX hs (ih₁ hΔ (hΓ.split_left hs)) (ih₂ hΔ (hΓ.split_right hs))
  | tensorI hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact tensorI_compatX hs (ih₁ hΔ (hΓ.split_left hs)) (ih₂ hΔ (hΓ.split_right hs))
  | tensorE hs hwf _ _ ihp ihb =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact tensorE_compatX hs (ihp hΔ (hΓ.split_left hs))
        (ihb hΔ (Ctx.ScopedB.cons (fun _ => h₂)
          (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs))))
  | sumI₁ _ ih => intro hΔ hΓ; exact sumI₁_compatX (ih hΔ hΓ)
  | sumI₂ _ ih => intro hΔ hΓ; exact sumI₂_compatX (ih hΔ hΓ)
  | sumE hs hwf _ _ _ ih₀ ih₁ ih₂ =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact sumE_compatX hs (ih₀ hΔ (hΓ.split_left hs))
        (ih₁ hΔ (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs)))
        (ih₂ hΔ (Ctx.ScopedB.cons (fun _ => h₂) (hΓ.split_right hs)))
  | lolliI hwf _ ih =>
      intro hΔ hΓ
      exact lolliI_compatX (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))
  | lolliE hs _ _ iha ihf =>
      intro hΔ hΓ
      exact lolliE_compatX hs (iha hΔ (hΓ.split_left hs)) (ihf hΔ (hΓ.split_right hs))
  | bangLamI hΓp hwf _ ih =>
      intro hΔ hΓ
      exact bangLamI_compatX hΓp (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))
  | bangAllI hΓp hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact bangAllI_compatX hΓp hx hside.1 hside.2.1 hside.2.2
        (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))
  | bangE _ ih => intro hΔ hΓ; exact bangE_compatX (ih hΔ hΓ)
  | copyBangAx hΓd => intro _ _; exact copyBang_compatX hΓd
  | forgetBangAx hΓd => intro _ _; exact forgetBang_compatX hΓd
  | allI hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact allI_compatX hx hside.1 hside.2.1 hside.2.2
        (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))
  | allE _ hlt ih => intro hΔ hΓ; exact allE_compatX (ih hΔ hΓ) hlt
  | boxIctx _ hΓo ih =>
      intro hΔ hΓ
      exact boxI_compatX (ih hΔ hΓ) hΓo
  | boxE _ ih => intro hΔ hΓ; exact boxE_compatX (ih hΔ hΓ)
  | immSub _ hle ih => intro hΔ hΓ; exact immSub_compatX (ih hΔ hΓ) hle
  | mutSub _ hle ih => intro hΔ hΓ; exact mutSub_compatX (ih hΔ hΓ) hle
  | allocAx hΓd => intro _ _; exact alloc_compatX hΓd
  | freeAx hΓd => intro _ _; exact free_compatX hΓd
  | swapAx hΓd => intro _ _; exact swap_compatX hΓd
  | copyAx hΓd => intro _ _; exact copy_compatX hΓd
  | forgetImmAx hΓd => intro _ _; exact forgetImm_compatX hΓd
  | forgetMutAx hΓd => intro _ _; exact forgetMut_compatX hΓd
  | forgetUnkAx hΓd => intro _ _; exact forgetUnk_compatX hΓd
  | withbor1Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor1Ty hwf
      have hside := withbor1Side_of_scopedB hx h₁ h₂
      exact withbor1_compatX x hΓd hx h₁ hside.1 hside.2
  | withbor2Ax hΓd x hx hs hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor2Ty hwf
      have hside := withbor2Side_of_scopedB hx h₁ h₂
      exact withbor2_compatX x hΓd hx hs hside.1 hside.2
  | withbor3Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor3Ty hwf
      have hside := withbor3Side_of_scopedB hx h₁ h₂
      exact withbor3_compatX x hΓd hx hside.1 hside.2
  | withloadAx hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithloadTy hwf
      exact withload_compatX x hΓd hx (not_lfree_of_scopedB hx h₁) (not_lfree_of_scopedB hx h₂)
  | withswapAx hΓd => intro _ _; exact withswap_compatX hΓd

/-- `[TR]` 6.151's statement at the relaxed `SemX`. -/
def FundamentalProperty : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
    DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T

theorem fundamentalProperty : FundamentalProperty := fundamental

/-- `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅` (`Paper/CONF/Results.lean`'s
`Adequacy.reclaim`, which is independent of the typed world). -/
theorem reclaim (ρ : WRes) (hupd : ResU.UpdV PMap.empty ρ) (hno : NoOwn ρ) :
    ρ = PMap.empty := by
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

theorem corollary33 (e : Expr) (hsem : SemX LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenX_nil _ _)
  rw [substAll, Adequacy.psub_nil] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp
  subst hv
  exact hsteps

/-- Adequacy from a typing derivation: a closed program `[TR]` p. 2 types at `1`
(`DerivesWf`) runs from the empty memory to `()` and the empty memory.  It is
`fundamental` (6.151 at `SemX`) composed with `corollary33`; at `Δ = Γ = ∅` the
hypotheses `⊧ Δ` and `Δ ⊢ Γ` hold outright.
`[about ours: [CONF] Lemma 3.1 composed with Corollary 3.3, at `SemX`]` -/
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamental _ _ _ _ hD ok_empty (fun s hs => absurd hs (by simp)))

end BoCa.Fig16.LogRel.FrameEnd

end
