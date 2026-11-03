import Support.Model.Tree.World.Coherent

/-!
# `TIT` at the empty world and across an allocation

`[spec §62]`. `TIT` holds at `TWNT.empty` (`tit_empty`), and `TWNT.alloc` keeps it (`tit_alloc`). `TIT` reads the world only through its
aliasable walks (`AgWT W a`) and its `mut` cells at depth (`MutAtT W x`) (`TIT.congr`); a fresh
`ℓ ↦ own(v)` adds nothing to the aliasable walk and no `mut` cell, so both are unchanged.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- **`TIT` reads the world only through its aliasable walks and its `mut` cells at depth.** -/
theorem TIT.congr {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)}
    (hA : ∀ a, AgWT W' a ↔ AgWT W a) (hM : ∀ x, MutAtT W' x ↔ MutAtT W x)
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs := by
  unfold TIT ChainInvT DeepInvT JointAtT JointDeepT LeInvT NestLifeT NoMutT CoverageT at *
  simp only [hA, hM]
  exact h

/-- **`TIT` at the empty world.** -/
theorem tit_empty (Θ : CodeTy) : TIT K Θ PMap.empty [] [] := by
  refine ⟨⟨fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr,
    fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr⟩,
    fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr,
    fun r hr => by simp at hr, ⟨fun r hr => by simp at hr, fun r hr => by simp at hr⟩,
    fun x => by simp, ?_⟩
  intro a ha m ψ e
  obtain rfl := AgWT.functional ha agW_empty
  simp at e

/-- A fresh `own` cell keeps the aliasable walks. -/
theorem agWT_alloc_iff {W W' : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hW : ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W') (a : TRes K) :
    AgWT W' a ↔ AgWT W a := by
  constructor
  · intro ha
    obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgWT.split hW).mp ha
    obtain rfl := AgWT.functional h₂ (AgWT.single_own l v)
    rwa [← ResUT.eq_of_comp_empty_right hc]
  · intro ha
    exact (AgWT.split hW).mpr ⟨a, _, ha, AgWT.single_own l v, ResUT.compR_empty_right a⟩

/-- A fresh `own` cell keeps the `mut` cells at depth. -/
theorem mutAtT_alloc_iff {W W' : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hW : ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W') (x : BoCa.Loc) :
    MutAtT W' x ↔ MutAtT W x := by
  have hl : W.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm hW.1) (ResUT.single_get_self _ _)
      (by simp)
  have back : ∀ m (χ : TCell K), W'.get m = some χ → χ.kind ≠ Kind.own → W.get m = some χ := by
    intro m χ e hk
    by_cases hm : m = l
    · subst hm
      rw [(ResUT.CompS.get_right_of_ne_imm hW (ResUT.single_get_self _ _) (by simp)).2] at e
      cases Option.some.inj e; exact absurd rfl hk
    · rw [ResUT.Comp.get_of_right_none hW (ResUT.single_get_ne _ hm)] at e; exact e
  have fwd : ∀ m (χ : TCell K), W.get m = some χ → W'.get m = some χ := by
    intro m χ e
    have hm : m ≠ l := by rintro rfl; rw [hl] at e; cases e
    rw [ResUT.Comp.get_of_right_none hW (ResUT.single_get_ne _ hm)]; exact e
  constructor
  · intro h
    cases h with
    | top e hk => exact .top (back _ _ e (by rw [hk]; simp)) hk
    | nest e hk hw => exact .nest (back _ _ e hk) hk hw
  · intro h
    cases h with
    | top e hk => exact .top (fwd _ _ e) hk
    | nest e hk hw => exact .nest (fwd _ _ e) hk hw

/-- **`TWNT.alloc` keeps `TIT`.** -/
theorem tit_alloc {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)} {l : BoCa.Loc}
    {v : BoCa.Val} (hW : ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W')
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs :=
  TIT.congr (agWT_alloc_iff hW) (mutAtT_alloc_iff hW) h

end BoCa.Fig16.Tree.Wp

end
