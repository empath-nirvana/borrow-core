import CBPVMu.Fix

/-!
# CBPVMu — the witness-size measure and `withload` with a sized callback

* `dsize ρ`: the number of cells of a resource.  A piece `q ≤ σ` holding `l`, less `l`, is
  smaller than `σ` (`dsize_del_lt`).
* `rebChooseTW_sized`: a chooser whose payload input carries a predicate `K` of the witness
  also returns, with the chosen image, the witness it is an image of.
* `withload_sized`: `withload` at `Imm a T₁` whose callback is asked only at the views
  `χ ∈ reb_β(σ)` of a witness `σ` with `K σ`, at lifetimes `β` below a given `m`.
* `WitLt ℓ ρ n`: a borrow's cell witness has fewer than `n` cells; every borrow has a bound
  (`witLt_exists`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The measure -/

open Classical in
/-- The locations of a resource, as a finite set. -/
def rdom (ρ : WRes) : Finset Loc :=
  (Classical.choose ρ.finite).toFinset.filter (fun l => ρ.get l ≠ none)

theorem mem_rdom {ρ : WRes} {l : Loc} : l ∈ rdom ρ ↔ ρ.get l ≠ none := by
  classical
  unfold rdom
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (Classical.choose_spec ρ.finite l h), h⟩

/-- The number of cells of a resource. -/
def dsize (ρ : WRes) : Nat := (rdom ρ).card

/-- A resource whose cells are among `σ`'s, less one of `σ`'s, is smaller. -/
theorem dsize_lt {σ' σ : WRes} {l : Loc} (hl : σ.get l ≠ none)
    (h : ∀ m, σ'.get m ≠ none → σ.get m ≠ none ∧ m ≠ l) : dsize σ' < dsize σ := by
  classical
  have hsub : rdom σ' ⊆ (rdom σ).erase l := fun m hm => by
    obtain ⟨h₁, h₂⟩ := h m (mem_rdom.mp hm)
    exact Finset.mem_erase.mpr ⟨h₂, mem_rdom.mpr h₁⟩
  have hl' : l ∈ rdom σ := mem_rdom.mpr hl
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hl'] at this
  have hpos : 0 < (rdom σ).card := Finset.card_pos.mpr ⟨l, hl'⟩
  unfold dsize; omega

/-- A piece `q ≤ σ` holding `l`, less `l`, is smaller than `σ`. -/
theorem dsize_del_lt {q σ : WRes} {l : Loc} (hle : ResU.Le q σ) (hq : ∃ ψ, q.get l = some ψ) :
    dsize (q.del l) < dsize σ := by
  obtain ⟨τ, hτ⟩ := hle
  obtain ⟨ψ, eψ⟩ := hq
  obtain ⟨ψ', e', -⟩ := ResU.CompS.get_left hτ eψ
  refine dsize_lt (l := l) (by rw [e']; simp) (fun m hm => ?_)
  by_cases hml : m = l
  · subst hml; exact absurd (ResU.del_get_self q m) hm
  · have hqm : q.get m ≠ none := by
      have : (q.del l).get m = q.get m := by simp [ResU.del, hml]
      rwa [this] at hm
    obtain ⟨φ, eφ⟩ := Option.ne_none_iff_exists'.mp hqm
    obtain ⟨φ', eφ', -⟩ := ResU.CompS.get_left hτ eφ
    exact ⟨by rw [eφ']; simp, hml⟩

/-- The tail's resource beside an owned cell is smaller than the whole. -/
theorem dsize_tail_lt {ℓ : Loc} {v : Val} {R ρ τ : WRes}
    (hc : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) R ρ) (hle : ResU.Le τ R) :
    dsize τ < dsize ρ := by
  have hself := ResU.CompS.get_left_of_ne_imm hc (ResU.single_get_self ℓ _) (by simp)
  refine dsize_lt (l := ℓ) (by rw [hself.2]; simp) (fun m hm => ?_)
  obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hm
  obtain ⟨z, hz⟩ := hle
  obtain ⟨ψ', eψ', -⟩ := ResU.CompS.get_left hz eψ
  obtain ⟨ψ'', eψ'', -⟩ := ResU.CompS.get_right hc eψ'
  refine ⟨by rw [eψ'']; simp, fun hml => ?_⟩
  subst hml
  rw [hself.1] at eψ'; cases eψ'

/-! ### `withload` with the witness the view is an image of -/

/-- A chooser whose payload input also asks `K` of the cell's witness returns, with its image
`χ`, the witness `σ` it is an image of: `K σ`, the payload input at `σ`, and `χ ∈ reb_β(σ)`. -/
theorem rebChooseTW_sized {ls : List SRec} {l : Loc} {R : Val → WRes → Prop}
    {P₀ P : Life → Val → WProp} (K : WRes → Prop) (h : RebChooseTW ls l R P₀ P) :
    RebChooseTW ls l (fun w σ => R w σ ∧ K σ) P₀
      (fun β w χ => P β w χ ∧ ∃ σ, K σ ∧ R w σ ∧ ResU.Reb β σ χ) := by
  intro W F χ₀ σ ps β w s hs hT htg hβ hW hR hreb₀ hP₀
  obtain ⟨χ, hreb, hP, hag, hEF, hEI, hin, hout⟩ := h W F χ₀ σ ps β w s hs hT htg hβ hW hR.1 hreb₀ hP₀
  exact ⟨χ, hreb, ⟨hP, σ, hR.2, hR.1, hreb⟩, hag, hEF, hEI, hin, hout⟩

/-- **`withload` with a sized callback.**  `withload ℓ v_f` at a borrow `ℓ : Imm a T₁` whose
cell's witness has the property `K`, and a callback `v_f` asked only at the views
`χ ∈ 𝒱⟦Imm̲ 'x T₁⟧` that are images `χ ∈ reb_β(σ)` of a witness `σ` with `K σ` observable at
`T₁`.  The callback is asked at `β < m` only, as `withload_compatX` asks it at `β` below `⊓Δδ`.
`withload_compatX`'s proof (6.144, 6.134, 6.150), with the chooser of `rebChooseTW_sized`. -/
theorem withload_sized {T₁ : VTy} (x : LifeVar) (hfree₁ : ¬ VFree x T₁)
    {a : Lifetime.Life} {ls : List SRec} {δ : LSub} {ℓ : Loc} {vf : Val} {ρ₁ ρ₂ τ : WRes}
    (m : Life) (K : WRes → Prop) (Q : List SRec → Val → WProp)
    (hv : vP (.imm a T₁) ls δ (.loc ℓ) ρ₁)
    (hK : ∀ s u σ h, ρ₁ = ResU.single ℓ (CellU.immOf s u σ h) → K σ)
    (hc : ResU.CompS ρ₁ ρ₂ τ)
    (hcb : ∀ β w χ ρ', β < m → vC true (T₁.immReborrow (.var x)) ls (δ.extend x β) w χ →
        (∃ σ, K σ ∧ vC false T₁ ls δ w σ ∧ ResU.Reb β σ χ) → ResU.CompS ρ₂ χ ρ' →
        wpTS ls (.app (.app (.val vf) (.val .unit)) (.val w)) (fun ls' v => box β (Q ls' v)) ρ') :
    wpTS ls (.app (.app withload (.val (.loc ℓ))) (.val vf)) Q τ := by
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.app (.app BoCa.v0 unit') (.app load' BoCa.v1))))
      = Expr.val (Val.lam (.app (.app BoCa.v0 unit') (eLoad ℓ))) := by
    simp [eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit', load']
  have hβ₂ : Expr.subst 0 vf (Expr.app (.app BoCa.v0 unit') (eLoad ℓ))
      = Expr.app (.app (.val vf) (.val .unit)) (eLoad ℓ) := by
    simp [eLoad, Expr.subst, BoCa.v0, unit']
  refine wpTS_bind (.appL .hole vf) (.app (.val (Val.lam (.val (Val.lam
    (.app (.app BoCa.v0 unit') (.app load' BoCa.v1)))))) (.val (.loc ℓ))) ls Q τ ?_
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  simp only [Kont.plug]
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  obtain ⟨α₀, ha, ℓ', hs₂⟩ := hv
  obtain ⟨⟨hℓ', hcoh⟩, himm⟩ := pure_sep_iff.mp hs₂
  have hℓℓ : ℓ' = ℓ := by
    have := congrArg Subtype.val hℓ'; simpa using this.symm
  subst hℓℓ
  refine wpTS_bind (.appR (.app (.val vf) (.val .unit)) .hole) (eLoad ℓ') ls _ τ ?_
  have hcell₀ : ptoImm ℓ' α₀ (fun u σ => vC false T₁ ls δ u σ ∧ K σ) ρ₁ := by
    obtain ⟨s, u, σ, hs, hρ, hP, hαs⟩ := ptoImmO_toImm himm
    exact ⟨s, u, σ, hs, hρ, ⟨hP, hK s u σ hs hρ⟩, hαs⟩
  refine wpTS_load_I ls ℓ' α₀ (fun u σ => vC false T₁ ls δ u σ ∧ K σ) _ τ
    ⟨ρ₁, ρ₂, hc, hcell₀, ?_⟩
  intro vℓ ρc ρcomp hcell hccomp
  simp only [Kont.plug]
  have hesc₀ : RebChooseTW ls ℓ'
      (fun w σ => w = vℓ ∧ vC false T₁ ls δ w σ)
      (fun β w χ => vShape (T₁.immReborrow (.var x)) (δ.extend x β) w χ)
      (fun β w χ => (⌜vℓ = w⌝ ⋆ vC true (T₁.immReborrow (.var x)) ls (δ.extend x β) w) χ) := by
    obtain ⟨S₀, δ₀, he, hc⟩ := hcoh
    have hx₀ : ¬ VFree S₀.lifeBound S₀ := fun h => lt_irrefl _ (lt_vLifeBound h)
    have heβ : ∀ β : Life, TyEq (T₁.immReborrow (.var x)) (δ.extend x β)
        (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) := fun β =>
      TyEq.immReborrow (by rw [interp_ext_self, interp_ext_self])
        (TyEq.extend_left hx₀ β (TyEq.extend_left hfree₁ β he).symm).symm
    have eR : vC false T₁ ls δ = vC false S₀ ls δ₀ := vC_tyEq he false ls
    have eP₀ : ∀ β : Life, vShape (T₁.immReborrow (.var x)) (δ.extend x β)
        = vShape (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) :=
      fun β => vShape_tyEq (heβ β)
    have eP : ∀ β : Life, vC true (T₁.immReborrow (.var x)) ls (δ.extend x β)
        = vC true (S₀.immReborrow (.var S₀.lifeBound)) ls (δ₀.extend S₀.lifeBound β) :=
      fun β => vC_tyEq (heβ β) true ls
    simp only [eR, eP₀, eP]
    rcases hc with ⟨r, hr, rfl, rfl, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
    · exact rebChooseTW_pin vℓ (rebChooseTW_top hr hag hx₀)
    · exact rebChooseTW_pin vℓ (rebChooseTW_deep hr hch hag hx₀)
  have hesc := rebChooseTW_sized K hesc₀
  have hcell' : ptoImm ℓ' α₀ (fun v σ => ((v = vℓ ∧ vC false T₁ ls δ v σ) ∧ K σ) ∧
      fresh (fun b => reborrow b (vShape (T₁.immReborrow (.var x)) (δ.extend x b) v)) σ) ρc := by
    refine ptoImm_mono (fun u σ h => ?_) ρc hcell
    obtain ⟨he, hobs, hKσ⟩ := pure_sep_iff.mp h
    subst he
    exact ⟨⟨⟨rfl, hobs⟩, hKσ⟩, six132_shape_fresh hfree₁ δ vℓ σ (vC_vShape false T₁ hobs)⟩
  refine wpTS_reborrow ls ℓ' α₀ _ _ _ _ Q hesc ρcomp
    ⟨ρc, ρ₂, ResU.CompS.comm hccomp, hcell', ?_⟩
  obtain ⟨g₂, hg₂⟩ := ResU.exists_stratum ρ₂
  refine ⟨m ⊓ g₂, fun β hβ => ⟨?_, hg₂.mono (le_of_lt (lt_of_lt_of_le hβ inf_le_right))⟩⟩
  intro v σ ρpc hP hpc
  obtain ⟨hP₁, σ₀, hKσ₀, ⟨hvv₀, hobs₀⟩, hreb₀⟩ := hP
  obtain ⟨hvv, hreb⟩ := pure_sep_iff.mp hP₁
  subst hvv
  exact hcb β vℓ σ ρpc (lt_of_lt_of_le hβ inf_le_left) hreb ⟨σ₀, hKσ₀, hobs₀, hreb₀⟩ hpc



/-- A β-step inside an evaluation context. -/
theorem wpTS_beta_in (K : Kont) (b : Expr) (v : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (K.plug (b.subst 0 v)) Q) (wpTS ls (K.plug (.app (.val (.lam b)) (.val v))) Q) :=
  wpTS_step (step_in K (fun μ => Head.beta μ b v)) ls Q

/-! ### Witness bounds -/

/-- A borrow's cell witness has fewer than `n` cells. -/
def WitLt (ℓ : Loc) (ρ : WRes) (n : Nat) : Prop :=
  ∀ s u σ h, ρ = ResU.single ℓ (CellU.immOf s u σ h) → dsize σ < n


/-- Every borrow's cell witness has a size. -/
theorem witLt_exists {a : Lifetime.Life} {T : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc}
    {ρ : WRes} (hv : vP (.imm a T) ls δ (.loc ℓ) ρ) : ∃ n, WitLt ℓ ρ n := by
  obtain ⟨α₀, -, ℓ', hs⟩ := hv
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨s, u, σ, hσ, hρ, -⟩ := ptoImmO_toImm himm
  refine ⟨dsize σ + 1, fun s' u' σ' h' hρ' => ?_⟩
  have e : (ResU.single ℓ' (CellU.immOf s u σ hσ)).get ℓ' = ρ.get ℓ' := by rw [hρ]
  rw [hρ'] at e
  by_cases hl : ℓ' = ℓ
  · subst hl
    simp only [ResU.single_get_self] at e
    obtain ⟨-, -, hσσ⟩ := CellU.immOf_inj (Option.some.inj e)
    rw [← hσσ]; exact Nat.lt_succ_self _
  · have : (ResU.single ℓ (CellU.immOf s' u' σ' h')).get ℓ' = none := by
      simp [ResU.single, hl]
    rw [this] at e; simp at e


end BoCa.Fig16.LogRel.CBPVMu

end
