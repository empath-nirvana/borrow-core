import CBPVCore.Agreement

/-!
# CBPVCore — the borrow axioms and the preimage rules

Each borrow axiom `c : T` of BoCa is a value of `U`-type `cbv T` at any consumed CBPV context:
its `_compatX` lemma, carried by `semX_iff_semV`.  `[]I` is `boxI_compatX` carried the same
way, at a translated context.  `∀E` is proved here at `F (cbv T)`, where `vX_tyEq` at
`TyEq.instLife` is the substitution lemma.
-/

namespace CBPVCore
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

variable {Δ : LifeCtx} {Γ : Ctx VTy}

/-- `alloc : U (T⁺ ⊸ F (Ref T⁺))`. -/
theorem alloc_compatC {T : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ (.val (.prim .alloc)) (cbv (.lolli T (.ref T))) :=
  semV_of_semX_nil hΓ (alloc_compatX .nil)

/-- `free : U (Ref T⁺ ⊸ F T⁺)`. -/
theorem free_compatC {T : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ (.val (.prim .free)) (cbv (.lolli (.ref T) T)) :=
  semV_of_semX_nil hΓ (free_compatX .nil)

theorem swap_compatC {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) : SemV Δ Γ swap (cbv (axSwapTy T₁ T₂)) :=
  semV_of_semX_nil hΓ (swap_compatX .nil)

theorem copy_compatC {a : Lifetime.Life} {T : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ copy (cbv (axCopyTy a T)) :=
  semV_of_semX_nil hΓ (copy_compatX .nil)

theorem forgetImm_compatC {a : Lifetime.Life} {T : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ forget (cbv (axForgetImmTy a T)) :=
  semV_of_semX_nil hΓ (forgetImm_compatX .nil)

theorem forgetMut_compatC {a : Lifetime.Life} {T : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ forget (cbv (axForgetMutTy a T)) :=
  semV_of_semX_nil hΓ (forgetMut_compatX .nil)

theorem forgetUnk_compatC (hΓ : Ctx.Dead Γ) : SemV Δ Γ forget (cbv axForgetUnkTy) :=
  semV_of_semX_nil hΓ (forgetUnk_compatX .nil)

/-- `withbor`, form (1), with `withbor1_compatX`'s hypotheses. -/
theorem withbor1_compatC {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hsc₁ : T₁.scopedB Δ = true) (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    SemV Δ Γ withbor (cbv (axWithbor1Ty x Δ.meetOfDom T₁ T₂)) :=
  semV_of_semX_nil hΓ (withbor1_compatX x .nil hx hsc₁ hfree₁ hfree₂)

/-- `withbor`, form (2), with its side condition. -/
theorem withbor2_compatC {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ BoCa.Outlives Δ T₁ b)
    (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    SemV Δ Γ withbor (cbv (axWithbor2Ty x Δ.meetOfDom T₁ T₂)) :=
  semV_of_semX_nil hΓ (withbor2_compatX x .nil hx hside hfree₁ hfree₂)

/-- `withbor`, form (3). -/
theorem withbor3_compatC {a : Lifetime.Life} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    SemV Δ Γ withbor (cbv (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)) :=
  semV_of_semX_nil hΓ (withbor3_compatX x .nil hx hfree₁ hfree₂)

theorem withload_compatC {a : Lifetime.Life} {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    SemV Δ Γ withload (cbv (axWithloadTy a x Δ.meetOfDom T₁ T₂)) :=
  semV_of_semX_nil hΓ (withload_compatX x .nil hx hfree₁ hfree₂)

theorem withswap_compatC {a : Lifetime.Life} {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) :
    SemV Δ Γ withswap (cbv (axWithswapTy a T₁ T₂)) :=
  semV_of_semX_nil hΓ (withswap_compatX .nil)

/-- `[]I` at a context whose live slots are a translated context's: `boxI_compatX`, whose
premise `Δ ⊨ Γ ⊐ @a` is read on the BoLo context. -/
theorem boxI_compatC {Γ' : Ctx Ty} {e : Expr} {T : Ty} {a : Lifetime.Life}
    (hE : LiveEq Γ (cbvCtx Γ')) (h : SemV Δ Γ e (cbv T)) (hΓ : Ctx.Outlives Δ Γ' a) :
    SemV Δ Γ e (.box a (cbv T)) :=
  (semC_liveEq hE).mpr ((semX_iff_semV Δ Γ' e (.box a T)).mp
    (boxI_compatX ((semX_iff_semV Δ Γ' e T).mpr ((semC_liveEq hE).mp h)) hΓ))

/-- `M [] : F (T[@a/'x])⁺` for `M : ∀'x ⊏ @b. F T⁺` and `Δ ⊨ @a ⊏ @b` (`allE_compatX`). -/
theorem allE_compatC {M : Expr} {x : LifeVar} {b a : Lifetime.Life} {T : Ty}
    (h : SemC Δ Γ M (.all x b (.ret (cbv T)))) (hlt : Δ.EntailsLt a b) :
    SemC Δ Γ (.app M (.val .unit)) (.ret (cbv (Ty.instLife x a T))) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have hsub : (fun ls'' => vC true (cbv (Ty.instLife x a T)) ls'' δ)
      = (fun ls'' => vC true (cbv T) ls'' (δ.extend x α)) :=
    funext fun ls'' => by
      rw [← vP_eq_vC, ← vP_eq_vC]
      exact vX_tyEq (TyEq.instLife x a T ha) true ls''
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  rw [he]
  show wpTS ls _ (fun ls'' => vC true (cbv (Ty.instLife x a T)) ls'' δ) ρ
  rw [hsub]
  exact h δ γ ls ρ hδ hg α PMap.empty ρ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right ρ)

end
end CBPVCore
