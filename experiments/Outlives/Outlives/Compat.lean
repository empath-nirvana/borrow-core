import Outlives.Judgment

/-!
# Outlives — the two relaxed rules are sound at `SemV`

* **`[]I` with the box rule non-strict** (`boxIL_compatC`): `boxI_compatX` with `vC_outlivesL`
  in place of `vC_outlives`. A slot `x : [@b] T` may be boxed at `@a ⊑ @b`, and in particular at
  `@b` itself: a value already in `Res_β` is in `Res_β`.
* **`withbor` (form 2) with its side condition non-strict** (`withbor2Le_compatX`):
  `withbor2_compatX` (`[TR]` 6.173) with the side condition `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b`. The
  printed proof reads the condition through 6.60 as `𝒱⟦A⟧δ ⊧ [@bδ] 𝒱⟦A⟧δ` and hands it to
  `MutFrame`, which uses it only to put the payload in `Res_A` for the borrow's own lifetime
  `A`, chosen inside the frame rule strictly below `@bδ` (`wpTS_M_frameX`, `hAβ`). Under the
  relaxed condition 6.60 gives every stratum strictly below `@bδ` (`vC_outlivesLe`), so
  `MutFrame` is applied at `↓@bδ` and chooses `A ⊏ ↓@bδ`. Nothing else in the proof changes.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Outlives
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `gSepC_outlives` at the box-relaxed judgment. -/
theorem gSepC_outlivesL {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} {ls : List SRec}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
      (∀ s ∈ Γ, s.live = true → VOutL Δ a s.ty) →
      gSepC ls δ Γ γ ρ → BoLo.Outlives ρ α := by
  intro Γ
  induction Γ with
  | nil =>
      rintro γ ρ - ⟨rfl, -⟩
      exact ResU.inStratum_empty α
  | cons s Γ ih =>
      intro γ ρ hT hg
      cases γ with
      | nil =>
          obtain ⟨rfl, -⟩ := hg
          exact ResU.inStratum_empty α
      | cons v γ =>
          have hT' : ∀ t ∈ Γ, t.live = true → VOutL Δ a t.ty :=
            fun t ht => hT t (List.mem_cons.mpr (Or.inr ht))
          by_cases hl : s.live = true
          · rw [gSepC, if_pos hl] at hg
            obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
            exact (outlives_comp hc α).mpr
              ⟨vC_outlivesL hδ ha (hT s (List.mem_cons.mpr (Or.inl rfl)) hl) true ls v ρ₁ hv,
               ih hT' hrest⟩
          · rw [gSepC, if_neg hl] at hg
            exact ih hT' hg

/-- **`[]I` at the box-relaxed context condition.** -/
theorem boxIL_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T : VTy} {a : Lifetime.Life}
    (h : SemV Δ Γ e T) (hΓ : CtxOutL Δ Γ a) :
    SemV Δ Γ e (.box a T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, ha⟩ := hΓ.1 δ hδ
  show wpTS ls (substAll γ e) (fun ls' => vP (.box a T) ls' δ) ρ
  have hv : (fun ls' => vP (.box a T) ls' δ) = fun ls' v => box α (vP T ls' δ v) := by
    funext ls' v
    exact atLife_eq ha _
  rw [hv]
  exact wpTS_box ls α _ _ ρ
    ⟨h δ γ ls ρ hδ hg, gSepC_outlivesL hδ ha hΓ.2 (gDenC_iff.mp hg).2⟩

/-- **`withbor` (form 2) at the non-strict side condition.**  `withbor2_compatX`, with
`MutFrame` applied one stratum below the side condition's lifetime. -/
theorem withbor2Le_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T₁ T₂ : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutLe Δ b T₁)
    (hfree₁ : ¬ VFree x T₁) (hfree₂ : ¬ VFree x T₂) :
    SemV Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  have hP₂ : vP T₁ ls₂ δ vℓ ρP := vC_local true T₁ (hext₂.right hcℓ) hP
  -- the side condition, through 6.60 at the non-strict judgment: every stratum below `@bδ`
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  have hβ : ∀ ls' w σ', vC true T₁ ls' δ w σ' → σ'.InStratum (Life.down β) :=
    fun ls' w σ' h => vC_outlivesLe hδ hb hO true ls' w σ' h _ (Life.down_sqsubset β)
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wpTS_M_frameX ℓ T₁ δ (Life.down β) hβ vℓ _ ls₂
    (fun ls' => vP (.tensor (.ref T₁) T₂) ls' δ) τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP₂, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  have hmut' : vP (.mut (.var x) T₁) ls₂ (δ.extend x α) (.loc ℓ) ρm := by
    have e : (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) = (fun ls₀ => vC true T₁ ls₀ δ) :=
      funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk rfl ?_⟩
    show ptoMutS ℓ α ls₂ (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) ρm
    rw [e]; exact hm'
  refine wpTS_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) ls₂ _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vP (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)) ls'' (δ.extend x α))
    (fun ls'' => vP (.mut (.var x) T₁) ls'' (δ.extend x α) (.loc ℓ)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (.loc ℓ) σ₂ σ'' hmut'' hcσ'')
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vP T₂ ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hT₂δ'; exact hT₂δ'
  refine wpTS_val ls''' (.pair (.loc ℓ) v'') _ ρ'' ?_
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hT₂'⟩⟩

end BoCa.Fig16.LogRel.Core.Outlives

end
