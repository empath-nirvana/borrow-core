import PositiveArrays.ImmFam
import PositiveArrays.K2Mut

/-!
# PositiveArrays — K2 at `Imm`: an owned array lent as a family of `imm` leaves

    slice_borrow : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

The term is `withbor`'s. `sliceBorrowI_compatX` is `withbor1_compatX` (`[TR]` 6.172) with
`wpTS_I_frameFam` in place of one `wpTS_I_frameX`. The family `[Imm 'x A]` is today's
`ArrayImm 'x A`, which `withload` gives only through a cell holding the handle (SPEC §9); here
there is no cell. The side conditions are `withbor1`'s plus `A` and `B` outliving a lifetime of
`Δ` (`ImmFam.lean`: the strata of the outer frames' postconditions).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. -/
def sliceBorrowITy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.array A)
    (.lolli (.all x bnd (.lolli (.arrayImm (.var x) A) (.box (.var x) B)))
      (.tensor (.array A) B))

/-- A leaf of the frames is a leaf of `[Imm 'x A]` at `δ['x ↦ α]`: `withbor1_compatX`'s step
from the frame's record and cell to `𝒱⟦Imm 'x A⟧`. -/
theorem immLeaf_to_vP {A : VTy} {x : LifeVar} (hfree : ¬ VFree x A) {ls : List SRec}
    {δ : LSub} {α : Life} {m : Loc} {ρ : WRes} (h : immLeaf A ls δ α m ρ) :
    vP (.imm (.var x) A) ls (δ.extend x α) (.loc m) ρ := by
  obtain ⟨⟨r, hr, hle, hT, hδr⟩, hm⟩ := h
  refine ⟨α, interp_ext_self δ x α, m, pure_sep_mk ⟨rfl, cohE_of_coh
    (Or.inl ⟨r, hr, hle.symm, hT.symm, fun y hy => ?_⟩)⟩ ?_⟩
  · rw [hδr]
    rw [hT] at hy
    exact find?_extend_ne δ α (fun e => by subst e; exact hfree hy)
  · exact ptoImmS_mono (fun ls₀ u σ h => by
      rw [vC_extend_of_not_free hfree]; exact vO_obs A h) hm

/-- **K2 at `Imm`.** -/
theorem sliceBorrowI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A) (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemV Δ Γ withbor (sliceBorrowITy x Δ.meetOfDom A B) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, -⟩ := vP_fam_iff.mp hv₁
  have hβ₁ : Expr.subst 0 (Val.arr ℓ n)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (Val.arr ℓ n))
          (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))) := by
    simp [Expr.subst, BoCa.v0, BoCa.v1, unit', shift_arr]
  refine wpTS_lolli _ _ (Val.arr ℓ n) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (Val.arr ℓ n)) (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))
      = Expr.pair (.val (Val.arr ℓ n))
          (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) := by
    simp [Expr.subst, BoCa.v0, unit', subst_arr]
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  obtain ⟨ℓ', n', he, hs⟩ := vP_fam_iff.mp (vC_local true (.array A) hext₂ hv₁)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  have hA := vC_outlives hδ hβA hOa true
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hB := vC_outlives hδ hβB hOb true
  let Φ : List SRec → Val → WProp := fun ls' v =>
    ex fun v'' => ⌜v = Val.pair (Val.arr ℓ n) v''⌝ ⋆ vP B ls' δ v''
  have hΦ : ∀ ls' v σ, Φ ls' v σ → BoLo.Outlives σ βB := by
    rintro ls' v σ ⟨v'', hk⟩
    exact hB ls' v'' σ (pure_sep_iff.mp hk).2
  have hΦext : ∀ ls₁ ls₂ w σ, Ext ls₁ ls₂ σ → Φ ls₁ w σ → Φ ls₂ w σ := by
    rintro ls₁ ls₂ w σ hk ⟨v'', hk'⟩
    obtain ⟨hw, hv''⟩ := pure_sep_iff.mp hk'
    exact ⟨v'', pure_sep_mk hw (vC_local true B hk hv'')⟩
  refine wpTS_mono (P := fun ls' v => sepRange (ownLeaf A ls' δ) ℓ n.toNat ⋆ Φ ls' v) ?_ τ
    (wpTS_I_frameFam A δ βA (fun ls' w σ h => hA ls' w σ h) (admWf_of_vScoped hsc hδ) _ Φ βB
      hΦ hΦext n.toNat ℓ ls₂ τ ⟨ρ₁, ρ₂, hc₂, hs, ?_⟩)
  · rintro ls' v σ ⟨σo, σB, hσ, ho, v'', hk⟩
    obtain ⟨rfl, hv''⟩ := pure_sep_iff.mp hk
    exact ⟨Val.arr ℓ n, v'', pure_sep_mk rfl ⟨σo, σB, hσ, vP_fam_mk ho, hv''⟩⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- the callback's list `ls′` is `Ext`-above `ls₂` at its resource `ρ₂`
  intro ls' hext ρm σ' hm' hcm
  have himm' : vP (.arrayImm (.var x) A) ls' (δ.extend x α) (Val.arr ℓ n) ρm :=
    vP_fam_mk (sepRange_mono' (fun k σ h => immLeaf_to_vP hfree₁ h) hm')
  refine wpTS_bind (.pairR (Val.arr ℓ n) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) ls' _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls' hext α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (Val.arr ℓ n)) (.app (.val vf) (.val .unit)) ls'
    (fun ls'' => vP (.lolli (.arrayImm (.var x) A) (.box (.var x) B)) ls'' (δ.extend x α))
    (fun ls'' => vP (.arrayImm (.var x) A) ls'' (δ.extend x α) (Val.arr ℓ n)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, himm'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, himm''⟩
  simp only [BoCa.BoLo.Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (Val.arr ℓ n) σ₂ σ'' himm'' hcσ'')
  obtain ⟨α', hα', hBδ', -⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hB' : vP B ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'
  exact wpTS_val ls''' (.pair (Val.arr ℓ n) v'') _ ρ'' ⟨v'', pure_sep_mk rfl hB'⟩

end BoCa.Fig16.LogRel.Core.PositiveArrays

end
