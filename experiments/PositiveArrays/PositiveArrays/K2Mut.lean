import PositiveArrays.FrameFam

/-!
# PositiveArrays — K2 at `Mut`: an owned array lent as a family of `mut` leaves

    slice_borrow : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

The term is `withbor`'s own, `λa. λg. (a, g () a)`: the handle `(ℓ, n)` goes to the callback and
comes back. No cell holds the array, and nothing new runs: the `n` frames are proof only.

`sliceBorrowM_compatX` is `withbor2_compatX` (`[TR]` 6.173) with `wpTS_M_frameFam` in place of
one `wpTS_M_frameX`, and the family relation `vP_fam_mk` in place of `𝒱⟦Mut⟧` at one location.
Its side conditions are `withbor2`'s (`A` outlives a lifetime of `Δ`: `MutFrame`'s premise, by
6.60) plus one that `withbor2` does not need: `B` outlives a lifetime of `Δ` too. That is the
restriction `withborF2` already carries for its second leaf and result (SPEC §5): with more than
one frame, the callback runs at a lifetime strictly below every frame but the innermost, and its
result must be reboxed at each outer frame's lifetime.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[Mut 'c A]`. -/
abbrev VTy.sliceMut (a : Lifetime.Life) (A : VTy) : VTy := .fam (.mut a A)

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. -/
def sliceBorrowMTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.array A)
    (.lolli (.all x bnd (.lolli (VTy.sliceMut (.var x) A) (.box (.var x) B)))
      (.tensor (.array A) B))

/-- **K2 at `Mut`.** -/
theorem sliceBorrowM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemV Δ Γ withbor (sliceBorrowMTy x Δ.meetOfDom A B) := by
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
  -- the owned family at the callback's list
  obtain ⟨ℓ', n', he, hs⟩ := vP_fam_iff.mp (vC_local true (.array A) hext₂ hv₁)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  -- `MutFrame`'s premise from `A`'s side condition, and the rebox bound from `B`'s (6.60)
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  have hA := vC_outlives hδ hβA hOa true
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hB := vC_outlives hδ hβB hOb true
  -- the frames' postcondition: the handle beside a result of `B`
  let Φ : List SRec → Val → WProp := fun ls' v =>
    ex fun v'' => ⌜v = Val.pair (Val.arr ℓ n) v''⌝ ⋆ vP B ls' δ v''
  have hΦ : ∀ ls' v σ, Φ ls' v σ → BoLo.Outlives σ βB := by
    rintro ls' v σ ⟨v'', hk⟩
    exact hB ls' v'' σ (pure_sep_iff.mp hk).2
  refine wpTS_M_frameFam A δ βA (fun ls' w σ h => hA ls' w σ h) _ ls₂ Φ βB hΦ n.toNat ℓ
    (fun ls' => vP (.tensor (.array A) B) ls' δ) ?_ τ ⟨ρ₁, ρ₂, hc₂, hs, ?_⟩
  · -- the handle and the returned leaves are `Array A`
    rintro ls' v σ ⟨σo, σB, hσ, ho, v'', hk⟩
    obtain ⟨rfl, hv''⟩ := pure_sep_iff.mp hk
    exact ⟨Val.arr ℓ n, v'', pure_sep_mk rfl ⟨σo, σB, hσ, vP_fam_mk ho, hv''⟩⟩
  -- `⋔α` at `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  -- the `mut` leaves at `α` are the family `[Mut 'x A]` at `δ['x ↦ α]`
  have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
  have hmut' : vP (VTy.sliceMut (.var x) A) ls₂ (δ.extend x α) (Val.arr ℓ n) ρm := by
    refine vP_fam_mk (sepRange_mono' (fun k σ h => ?_) hm')
    refine ⟨α, interp_ext_self δ x α, k, pure_sep_mk rfl ?_⟩
    show ptoMutS k α ls₂ (fun ls₀ => vC true A ls₀ (δ.extend x α)) σ
    rw [e]; exact h
  refine wpTS_bind (.pairR (Val.arr ℓ n) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) ls₂ _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (Val.arr ℓ n)) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vP (.lolli (VTy.sliceMut (.var x) A) (.box (.var x) B)) ls'' (δ.extend x α))
    (fun ls'' => vP (VTy.sliceMut (.var x) A) ls'' (δ.extend x α) (Val.arr ℓ n)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [BoCa.BoLo.Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (Val.arr ℓ n) σ₂ σ'' hmut'' hcσ'')
  -- the callback's result, `[α] 𝒱⟦B⟧δ(v″)`; `Φ` keeps `𝒱⟦B⟧` only
  obtain ⟨α', hα', hBδ', -⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hB' : vP B ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'
  exact wpTS_val ls''' (.pair (Val.arr ℓ n) v'') _ ρ'' ⟨v'', pure_sep_mk rfl hB'⟩

end BoCa.Fig16.LogRel.Core.PositiveArrays

end
