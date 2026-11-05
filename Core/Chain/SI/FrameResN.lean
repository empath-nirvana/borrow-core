import Core.Chain.SI.RebN

/-!
# `[TR]` 6.29, 6.38 and 6.39 at the step index: the Imm Frame's resource lemmas

`[TR]` 6.64's printed proof (`wpTS_I_frameX`) reads the run's update through 6.29, 6.38 and 6.39.
Each reads `↭` at its `imm` clause, at its two validity conjuncts, and, in 6.29, at its `mut`
clause backwards for the lifetime of a `mut` cell (*"every other borrow in `⦇ρ′⦈` is disjoint from
`α`"*). `UpdN`'s `imm` clause is the printed one and `MutStep` keeps `β`, so the printed proofs
carry over: the copies below change only the `mut` step's reading (`six29_borrows_offN`) and, in
6.39, the conclusion's form (`CellUpdN` at each location for `ResU.SimFormAt`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `[TR]` 6.29 at the index -/

/-- `ResU.six29_borrows_off` at the step index. -/
theorem six29_borrows_offN {Φ : LocFam} {n : Nat} {α : Life} {ρ ρv ρ' W ρρi σ' : ResU BoCa.Loc BoCa.Val}
    {l : BoCa.Loc} {v : BoCa.Val} {hv : ρv.InStratum (LSet.singleton α).join}
    (hα : ρ.InStratum α)
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hhash : ResU.Hash ρ W)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hupd : UpdVN Φ n ρρi ρ') (hσ' : ResU.Flat ρ' σ') :
    σ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) ∧
      ∀ m, m ≠ l → ∀ ψ, σ'.get m = some ψ → ψ.InStratum α := by
  have hcellk : (CellU.immOf (LSet.singleton α) v ρv hv).kind = Kind.imm :=
    CellU.kind_immOf _ _ _ _
  have himmi : ∀ m ψ,
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)).get m = some ψ →
      ψ.kind = Kind.imm := by
    intro m ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact hcellk
  -- `ℓ ∉ dom(⦇ρ⦈)` and `ℓ ∉ dom(⦇ρ_v⦈)`, from the printed `#`.
  obtain ⟨-, T, hT, hvT⟩ := hhash
  obtain ⟨σT, eT, aT, hexT, hagT, hcT⟩ := hvT
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hT).mp hexT
  obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split hT).mp hagT
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExS.split hW).mp he₂
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgW.split hW).mp ha₂
  have hownk : (CellU.ownOf (Loc := BoCa.Loc) v).kind ≠ Kind.imm := by simp
  have hf₂l : f₂.get l = some (CellU.ownOf v) := by
    rw [ExS.functional hf₂ (ExW.single_own l v)]
    exact ResU.single_get_self _ _
  have hf₁l : f₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hfc.1) hf₂l hownk
  have he₂l : e₂.get l = some (CellU.ownOf v) := by
    have := hfc.2 l; rw [hf₁l, hf₂l] at this; exact this
  have he₁l : e₁.get l = none :=
    ResU.CompatS.right_eq_none (ResU.CompatS.symm hec.1) he₂l hownk
  have heTl : eT.get l = some (CellU.ownOf v) := by
    have := hec.2 l; rw [he₁l, he₂l] at this; exact this
  have haTl : aT.get l = none :=
    ResU.CompatS.right_eq_none hcT.1 heTl hownk
  have ha₁l : a₁.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).1
  have ha₂l : a₂.get l = none := ((ResU.Comp.eq_none_iff hac l).mp haTl).2
  have hb₁l : b₁.get l = none := ((ResU.Comp.eq_none_iff hbc l).mp ha₂l).1
  -- `⦇ρ ● ρᵢ⦈(ℓ) = ρᵢ`, and everywhere else `⦇ρ ● ρᵢ⦈ ∈ Res_α`.
  obtain ⟨σ, hσ⟩ := hupd.2.1
  obtain ⟨E, A, hE, hA, hEA⟩ := hσ
  obtain ⟨E₁, E₂, hE₁, hE₂, hEc⟩ := (ExS.split hρi).mp hE
  obtain ⟨A₁, A₂, hA₁, hA₂, hAc⟩ := (AgW.split hρi).mp hA
  rw [ExS.functional hE₂ (ExW.empty_of_all_imm himmi)] at hEc
  rw [ResU.CompS.functional hEc (ResU.comp_empty_right E₁)] at hE hEA
  rw [ExS.functional hE₁ he₁] at hE hEA
  rw [AgW.functional hA₁ ha₁] at hAc
  obtain ⟨ev, av, p, hev, hav, hcp, hagi⟩ := AgW.single_imm_inv hA₂
  rw [ExR.functional hev (ExS.toExR hf₁)] at hcp
  rw [AgW.functional hav hb₁] at hcp
  have hpl : p.get l = none := by
    refine (ResU.Comp.eq_none_iff hcp l).mpr ⟨hf₁l, hb₁l⟩
  have hA₂l : A₂.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hagi.2 l; rw [ResU.single_get_self, hpl] at this; exact this
  have hAl : A.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hAc.2 l; rw [ha₁l, hA₂l] at this; exact this
  have hσl : σ.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) := by
    have := hEA.2 l; rw [he₁l, hAl] at this; exact this
  -- `Res_α` off `ℓ`.
  have hstratσ : ∀ m, m ≠ l → ∀ ψ, σ.get m = some ψ → ψ.InStratum α := by
    intro m hm ψ hg
    have hEs : e₁.InStratum α := BoLo.ExW.inStratum BoLo.compS_hC he₁ α hα
    have hA₁s : a₁.InStratum α := BoLo.AgW.inStratum ha₁ α hα
    have hps : p.InStratum α :=
      BoLo.inStratum_comp (BoLo.compR_hC α) hcp
        (BoLo.ExW.inStratum BoLo.compR_hC (ExS.toExR hf₁) α hv)
        (BoLo.AgW.inStratum hb₁ α hv)
    have hA₂s : ∀ ζ, A₂.get m = some ζ → ζ.InStratum α := by
      intro ζ hζ
      have := hagi.2 m
      rw [ResU.single_get_ne _ hm] at this
      cases hpm : p.get m with
      | none => rw [hpm] at this; rw [this] at hζ; exact absurd hζ (by simp)
      | some π => rw [hpm] at this; rw [this] at hζ
                  exact hps m ζ (by rw [hpm]; exact hζ)
    have hAs : ∀ ζ, A.get m = some ζ → ζ.InStratum α := by
      intro ζ hζ
      rcases hAc.get m with ⟨-, -, e⟩ | ⟨ξ, g₁, -, e⟩ | ⟨ξ, -, g₂, e⟩ |
          ⟨ξ₁, ξ₂, ξ, g₁, g₂, e, hC⟩
      · rw [e] at hζ; exact absurd hζ (by simp)
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]; exact hA₁s m ξ g₁
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]; exact hA₂s ξ g₂
      · rw [show ζ = ξ from Option.some.inj (hζ.symm.trans e)]
        exact BoLo.compR_hC α _ _ _ hC (hA₁s m ξ₁ g₁) (hA₂s ξ₂ g₂)
    rcases hEA.get m with ⟨-, -, e⟩ | ⟨ξ, g₁, -, e⟩ | ⟨ξ, -, g₂, e⟩ |
        ⟨ξ₁, ξ₂, ξ, g₁, g₂, e, hC⟩
    · rw [e] at hg; exact absurd hg (by simp)
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]; exact hEs m ξ g₁
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]; exact hAs ξ g₂
    · rw [show ψ = ξ from Option.some.inj (hg.symm.trans e)]
      exact BoLo.compS_hC α _ _ _ hC (hEs m ξ₁ g₁) (hAs ξ₂ g₂)
  -- Across `↭`.
  have hσ'l : σ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    (ResU.flatAt_iff hσ' l _).mp
      ((hupd.1.1 l (LSet.singleton α) v ρv hv).mp ⟨σ, ⟨e₁, A, hE, hA, hEA⟩, hσl⟩)
  have hstratσ' : ∀ m, m ≠ l → ∀ ψ, σ'.get m = some ψ → ψ.InStratum α := by
    intro m hm ψ hg
    rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨t, w, χ, hh, rfl⟩ | ⟨b, w, χ, hh, P, hw, rfl⟩
    · exact trivial
    · have : σ.get m = some (CellU.immOf t w χ hh) :=
        (ResU.flatAt_iff ⟨e₁, A, hE, hA, hEA⟩ m _).mp
          ((hupd.1.1 m t w χ hh).mpr ⟨σ', hσ', hg⟩)
      exact hstratσ m hm _ this
    · -- the `mut` clause at the index keeps `β` (`MutStep`)
      obtain ⟨ψ, hflat, hs⟩ := hupd.1.2.2 m _ ⟨σ', hσ', hg⟩ rfl
      have hmm : σ.get m = some ψ :=
        (ResU.flatAt_iff ⟨e₁, A, hE, hA, hEA⟩ m _).mp hflat
      exact CellU.inStratum_of_mutStep hs.1 hs.2.1 hs.2.2.1 (hstratσ m hm _ hmm)
  exact ⟨hσ'l, hstratσ'⟩

/-- **`[TR]` 6.29 at the step index**: if `@ρ ⊐ α`, `ρ # ρ_v ● ℓ ↦ own(v)` and
`ρ ● ℓ ↦ imm({α}, v, ρ_v) ↭ₙ ρ′`, then `ρ′ = ρ′/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`. The printed proof. -/
theorem six29N {Φ : LocFam} {n : Nat} {α : Life} {ρ ρv ρ' W ρρi : ResU BoCa.Loc BoCa.Val}
    {l : BoCa.Loc} {v : BoCa.Val} {hv : ρv.InStratum (LSet.singleton α).join}
    (hα : ρ.InStratum α)
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hhash : ResU.Hash ρ W)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hupd : UpdVN Φ n ρρi ρ') :
    ResU.CompS (ρ'.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ' := by
  have hcellk : (CellU.immOf (LSet.singleton α) v ρv hv).kind = Kind.imm :=
    CellU.kind_immOf _ _ _ _
  obtain ⟨σ', hσ'⟩ := hupd.2.2
  obtain ⟨hσ'l, hstratσ'⟩ := six29_borrows_offN hα hW hhash hρi hupd hσ'
  -- `ρ′(ℓ)` is defined.
  obtain ⟨ex', ag', hex', hag', hc'⟩ := hσ'
  have hdef : ∃ φ, ρ'.get l = some φ :=
    ResU.flat_imm_at_top ⟨ex', ag', hex', hag', hc'⟩ hσ'l rfl hstratσ'
  -- …and is the printed cell.
  obtain ⟨φ, hφ⟩ := hdef
  obtain ⟨χ, hχ, hkχ, heχ, hwχ⟩ := ResU.Flat.get ⟨ex', ag', hex', hag', hc'⟩ hφ
  obtain rfl : χ = CellU.immOf (LSet.singleton α) v ρv hv :=
    Option.some.inj (hχ.symm.trans hσ'l)
  have hkφ : φ.kind = Kind.imm := hkχ ▸ hcellk
  obtain ⟨s', hs', heta⟩ := CellU.imm_eta hkφ
  have hsub : ∀ x, s'.mem x → (LSet.singleton α).mem x :=
    fun x hx => ResU.Flat.get_ls_imm ⟨ex', ag', hex', hag', hc'⟩
      (hφ.trans (congrArg some heta)) hσ'l hx
  obtain ⟨y, hy⟩ := LSet.nonempty s'
  have hyα : y = α := hsub y hy
  have hseq : s' = LSet.singleton α := by
    refine LSet.ext (fun x => ⟨fun hx => hsub x hx, fun hx => ?_⟩)
    show s'.mem x
    have : x = α := hx
    rw [this, ← hyα]
    exact hy
  have heφ : φ.erase = v := by rw [← heχ, CellU.erase_immOf]
  have hwφ : φ.wit = ρv := by rw [← hwχ, CellU.wit_immOf]
  have hφ' : ρ'.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    hφ.trans (congrArg some
      (heta.trans (CellU.immOf_congr hseq heφ hwφ hs' hv)))
  exact ResU.del_compS hφ'

/-! ### `[TR]` 6.38 at the index -/

/-- `ResU.six38_steps_one_two` at the step index. -/
theorem six38_steps_one_twoN {Φ : LocFam} {n : Nat} {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h1 : ResU.Hash ρ W) (h2 : ResU.Hash ρ' ρp)
    (h3 : ρ.InStratum α) (h4 : ρ'.InStratum α)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hpp : ResU.CompS ρ' ρp ρ'ρp) (h6 : UpdVN Φ n ρρi ρ'ρp) :
    ResU.CompS ρ' (ρp.del l) (ρ'ρp.del l) ∧
      ResU.Hash (ρ'ρp.del l)
        (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ∧
      ResU.CompS (ρ'ρp.del l)
        (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp := by
  classical
  have h7 : ResU.CompS (ρ'ρp.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp :=
    six29N h3 hW h1 hρi h6
  have hcl : ρ'ρp.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    ResU.compS_single_get_self (ResU.CompS.comm h7) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame h4 hpp hcl
  obtain ⟨-, x, hx, hvx⟩ := h2
  rw [ResU.CompS.functional hx hpp] at hvx
  refine ⟨⟨fun m ψ₁ ψ₂ e₁ e₂ => ?_, fun m => ?_⟩, ⟨h7.1, ρ'ρp, h7, hvx⟩, h7⟩
  · by_cases hm : m = l
    · subst hm; rw [ResU.del_get_self] at e₂; exact absurd e₂ (by simp)
    · exact hpp.1 m ψ₁ ψ₂ e₁ (by rwa [ResU.del_get_ne ρp hm] at e₂)
  · by_cases hm : m = l
    · subst hm
      show OptComp CellU.CompS (ρ'.get m) ((ρp.del m).get m) ((ρ'ρp.del m).get m)
      rw [hρ'l, ResU.del_get_self, ResU.del_get_self]
      rfl
    · show OptComp CellU.CompS (ρ'.get m) ((ρp.del l).get m) ((ρ'ρp.del l).get m)
      rw [ResU.del_get_ne ρp hm, ResU.del_get_ne ρ'ρp hm]
      exact hpp.2 m

/-- `ResU.sixThirtyEightResidual` at the step index: 6.38's proof from *"Then in order to show
G1"* on. -/
theorem sixThirtyEightResidualN {Φ : LocFam} {n : Nat} {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp G : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h1 : ResU.Hash ρ W)
    (h3 : ρ.InStratum α)
    (h4 : ρ'.InStratum α)
    (_h5 : ρp.restrict Kind.own = PMap.empty)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hpp : ResU.CompS ρ' ρp ρ'ρp)
    (h6 : UpdVN Φ n ρρi ρ'ρp)
    (hG : ResU.CompS ρ' (ρp.del l) G)
    (hGi : ResU.Hash G (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)))
    (hGc : ResU.CompS G (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp) :
    ResU.Hash G W := by
  classical
  -- the borrow cell
  set ι : CellU BoCa.Loc BoCa.Val := CellU.immOf (LSet.singleton α) v ρv hv with hιdef
  have hιk : ι.kind = Kind.imm := CellU.kind_immOf _ _ _ _
  have himmi : ∀ m ψ, (ResU.single l ι).get m = some ψ → ψ.kind = Kind.imm := by
    intro m ψ h
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
    exact hιk
  -- `⦇ρ′ ● ρ⁺⦈`, and the first display for `ρ′ ● ρ⁺/ℓ ● ℓ ↦ imm({α}, v, ρ_v)`
  obtain ⟨σρρ, hσρρ⟩ := h6.2.2
  obtain ⟨eG, eI, e, aG, aI, a, heG, heI, hec, haG, haI, hac, hc⟩ :=
    (ResU.Flat.split hGc).mp hσρρ
  obtain rfl : eI = (PMap.empty : ResU BoCa.Loc BoCa.Val) :=
    ExS.functional heI (ExW.empty_of_all_imm himmi)
  obtain rfl : eG = e := ResU.eq_of_comp_empty_right hec
  -- `ag(ℓ ↦ imm({α}, v, ρ_v)) = ℓ ↦ imm({α}, v, ρ_v) ○ ex(ρ_v)_○ ○ ag(ρ_v)`
  obtain ⟨ev, av, p, hev, hav, hcp, hagi⟩ := AgW.single_imm_inv (χ := ρv) haI
  -- 6.35 with H1: `⦇ρ_v⦈` and `⦇ρ_v ● ℓ ↦ own(v)⦈` are defined
  obtain ⟨-, T, hT, hvT⟩ := id h1
  obtain ⟨hvρ, hvW⟩ := ResU.Valid.split hT hvT
  obtain ⟨hvρv, -⟩ := ResU.Valid.split hW hvW
  obtain ⟨σv, hσv⟩ := hvρv
  obtain ⟨exv, agv, hexv, hagv, hcv⟩ := hσv
  obtain rfl : av = agv := AgW.functional hav hagv
  -- 6.33: `⦇ρ_v⦈_○ = ⦇ρ_v⦈`, so `p = ex(ρ_v)_● ● ag(ρ_v)`
  obtain rfl : p = σv :=
    ResU.FlatR.functional ⟨av, ev, hav, hev, ResU.CompR.comm hcp⟩
      (ResU.six33 ⟨exv, av, hexv, hav, hcv⟩)
  -- The second display: `ex(W)_● = ex(ρ_v)_● ● ℓ ↦ own(v)` and `ag(W) = ag(ρ_v)`
  obtain ⟨σW, hσW⟩ := hvW
  obtain ⟨f₁, f₂, eW, b₁, b₂, aW, hf₁, hf₂, hfc, hb₁, hb₂, hbc, hWc⟩ :=
    (ResU.Flat.split hW).mp hσW
  obtain rfl : exv = f₁ := ExS.functional hexv hf₁
  obtain rfl : ResU.single l (CellU.ownOf v) = f₂ :=
    ExS.functional (ExW.single_own l v) hf₂
  obtain rfl : av = b₁ := AgW.functional hav hb₁
  obtain rfl : (PMap.empty : ResU BoCa.Loc BoCa.Val) = b₂ :=
    AgW.functional (AgW.single_own l v) hb₂
  obtain rfl : av = aW := ResU.eq_of_comp_empty_right hbc
  have heW : ExS W eW :=
    (ExS.split hW).mpr ⟨exv, _, hexv, ExW.single_own l v, hfc⟩
  have haW : AgW W av := (AgW.split hW).mpr ⟨av, _, hav, AgW.single_own l v, hbc⟩
  -- `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ℓ ↦ imm({α},v,ρ_v) ○ ex(ρ_v)_● ○ ag(ρ_v)` regrouped so
  -- that `ag(ρ′) ○ ag(ρ⁺/ℓ) ○ ag(ρ_v)` is one factor: `[TR]` 6.3 at `○`.
  have hcvR : ResU.CompR exv av p := ResU.CompS.toCompR hcv
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aG (ResU.single l ι) p a).mp ⟨aI, hagi, hac⟩
  obtain ⟨z, hz₁, hz₂⟩ := (ResU.CompR.assoc y exv av a).mp ⟨p, hcvR, hy₂⟩
  obtain ⟨Z, hZ, hZ₂⟩ :=
    (ResU.CompR.assoc aG (ResU.single l ι) exv z).mpr ⟨y, hy₁, hz₁⟩
  obtain ⟨A, hA₀, hAZ⟩ :=
    (ResU.CompR.assoc av aG Z a).mp ⟨z, hZ₂, ResU.CompR.comm hz₂⟩
  have hA : ResU.CompR aG av A := ResU.CompR.comm hA₀
  -- The three printed bullets: 6.30 and 6.36 at each `○`.
  have himmE : eG.ImmFree := ExS.immFree heG
  have himmE' : eG.restrict Kind.imm = PMap.empty :=
    (ResU.restrict_imm_empty_iff eG).mpr himmE
  obtain ⟨hcA, hcZ⟩ := ResU.CompatS.of_compR_left himmE' hAZ hc.1
  obtain ⟨hcι, hcexv⟩ := ResU.CompatS.of_compR_left himmE' hZ hcZ
  obtain ⟨hcaG, hcav⟩ := ResU.CompatS.of_compR_left himmE' hA hcA
  -- `⦇ρ⦈`, `⦇W⦈` and the disjointness H1 supplies
  obtain ⟨σT, hσT⟩ := hvT
  obtain ⟨e₁, e₂, eT, a₁, a₂, aT, he₁, he₂, hecT, ha₁, ha₂, hacT, hcT⟩ :=
    (ResU.Flat.split hT).mp hσT
  obtain rfl : eW = e₂ := ExS.functional heW he₂
  obtain rfl : av = a₂ := AgW.functional haW ha₂
  have himmW : eW.ImmFree := ExS.immFree heW
  have himmT : eT.ImmFree := ResU.ImmFree.compS hecT (ExS.immFree he₁) himmW
  obtain ⟨hcTa₁, -⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff eT).mpr himmT) hacT hcT.1
  obtain ⟨-, hcWa₁⟩ := ResU.CompatS.of_compS_left_immFree himmT hecT hcTa₁
  have hF1 : ∀ m, eW.get m = none ∨ a₁.get m = none :=
    ResU.CompatS.disjoint_of_immFree himmW hcWa₁
  have hF2 : ∀ m, eW.get m = none ∨ av.get m = none :=
    ResU.CompatS.disjoint_of_immFree himmW hWc.1
  -- `⦇G⦈` itself
  obtain ⟨σG, hσGc⟩ := (ResU.compS_defined_iff eG aG).mpr hcaG
  have hσG : ResU.Flat G σG := ⟨eG, aG, heG, haG, hσGc⟩
  -- `[TR]` 6.29's second sentence, at `ρ′ ● ρ⁺`
  obtain ⟨hσρρl, hstrat⟩ :=
    six29_borrows_offN (hv := hv) h3 hW h1 hρi h6 hσρρ
  have h7 : ResU.CompS (ρ'ρp.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ'ρp :=
    six29N h3 hW h1 hρi h6
  have hcl : ρ'ρp.get l = some (CellU.immOf (LSet.singleton α) v ρv hv) :=
    ResU.compS_single_get_self (ResU.CompS.comm h7) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame h4 hpp hcl
  have hGl : G.get l = none :=
    (ResU.Comp.eq_none_iff hG l).mpr ⟨hρ'l, ResU.del_get_self _ _⟩
  -- `ρ′ ● ρ⁺/ℓ ∈ Res_α`, hence so is `⦇ρ′ ● ρ⁺/ℓ⦈`
  have hGstrat : G.InStratum α := by
    intro m φ hφ
    by_cases hm : m = l
    · subst hm; rw [hGl] at hφ; simp at hφ
    · refine ResU.flat_inStratum_inv_at hσρρ (hstrat m hm) ?_
      exact (ResU.Comp.get_of_right_none hGc
        (ResU.single_get_ne _ hm)).trans hφ
  have hσGstrat : σG.InStratum α := BoLo.flat_inStratum hσG hGstrat
  -- `⦇ρ′ ● ρ⁺/ℓ⦈ = ⦇ρ′ ● ρ⁺⦈ ○ ⦇ℓ ↦ imm({α},v,ρ_v)⦈` read backwards at `ℓ`:
  -- the borrow is at the top level of `ρ′ ● ρ⁺` and nowhere else
  obtain ⟨σG', σI, hσG', hσI, hCompRG⟩ := BoLo.flat_compR hGc hσρρ
  obtain rfl : σG = σG' := ResU.Flat.functional hσG hσG'
  have hF3 : ∀ ψ, σG.get l = some ψ → ψ.kind ≠ Kind.imm := by
    intro ψ hψ hk
    obtain ⟨s₁, hs₁, heta⟩ := CellU.imm_eta hk
    have hψ' : σG.get l = some (CellU.immOf s₁ ψ.erase ψ.wit hs₁) :=
      hψ.trans (congrArg some heta)
    have hsub : ∀ x, s₁.mem x → (LSet.singleton α).mem x := fun x hx =>
      ResU.CompR.get_ls_imm hCompRG hψ' hσρρl hx
    obtain ⟨y, hy⟩ := LSet.nonempty s₁
    have hmem : s₁.mem α := by
      have hyα : y = α := hsub y hy
      exact hyα ▸ hy
    have hstr := hσGstrat l _ hψ'
    rw [CellU.inStratum_immOf] at hstr
    exact absurd (s₁.meet_least α hmem) (not_le_of_gt hstr)
  -- *"by H6"*: an `imm` cell of `⦇ρ′ ● ρ⁺/ℓ⦈` is one of `ag(ρ)`, one of
  -- `ag(ρ_v)`, or the borrow at `ℓ`
  obtain ⟨σρρi, hσρρi⟩ := h6.2.1
  obtain ⟨τρ, τI, hτρ, hτI, hCompRρ⟩ := BoLo.flat_compR hρi hσρρi
  obtain ⟨eρ, aρ, heρ, haρ, hcρ⟩ := hτρ
  obtain rfl : a₁ = aρ := AgW.functional ha₁ haρ
  obtain ⟨eI', aI', heI', haI', hcI'⟩ := hτI
  obtain rfl : (PMap.empty : ResU BoCa.Loc BoCa.Val) = eI' :=
    ExS.functional (ExW.empty_of_all_imm himmi) heI'
  obtain rfl : aI' = τI := ResU.eq_of_comp_empty_left hcI'
  obtain ⟨ev', av', p', hev', hav', hcp', hagi'⟩ := AgW.single_imm_inv (χ := ρv) haI'
  obtain rfl : p = p' :=
    ResU.FlatR.functional (ResU.six33 ⟨exv, av, hexv, hav, hcv⟩)
      ⟨av', ev', hav', hev', ResU.CompR.comm hcp'⟩
  have hF4 : ∀ m ψ, σG.get m = some ψ → ψ.kind = Kind.imm →
      m = l ∨ (∃ φ, a₁.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) ∨
        (∃ φ, av.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) := by
    intro m ψ hψ hk
    obtain ⟨χ₀, hχ₀, hkχ₀, heχ₀, hwχ₀⟩ := ResU.CompR.get_imm_left hCompRG hψ hk
    obtain ⟨s₀, hs₀, heta₀⟩ := CellU.imm_eta hkχ₀
    have hχ₀' : σρρ.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      hχ₀.trans (congrArg some heta₀)
    have hupd : σρρi.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      (ResU.flatAt_iff hσρρi m _).mp
        ((h6.1.1 m s₀ χ₀.erase χ₀.wit hs₀).mpr ⟨σρρ, hσρρ, hχ₀'⟩)
    rcases ResU.CompR.imm_source hCompRρ hupd with ⟨s₂, h₂, hg₂⟩ | ⟨s₃, h₃, hg₃⟩
    · refine Or.inr (Or.inl ⟨_, ResU.ag_eq_flat_at_imm heρ hcρ hg₂
        (CellU.kind_immOf _ _ _ _), CellU.kind_immOf _ _ _ _, ?_⟩)
      rw [CellU.wit_immOf]; exact hwχ₀
    · rcases ResU.CompR.imm_source hagi' hg₃ with ⟨s₄, h₄, hg₄⟩ | ⟨s₅, h₅, hg₅⟩
      · exact Or.inl (ResU.single_get_eq_some hg₄).1
      · refine Or.inr (Or.inr ⟨_, ResU.ag_eq_flat_at_imm hexv hcv hg₅
          (CellU.kind_immOf _ _ _ _), CellU.kind_immOf _ _ _ _, ?_⟩)
        rw [CellU.wit_immOf]; exact hwχ₀
  -- *"Assume for sake of contradiction that `ℓ′ ∈ dom(ex(ρ_v)_● ● ℓ ↦ own(v))`
  -- and `ℓ′ ∈ dom(ag(ρ′) ○ ag(ρ⁺/ℓ))`"*
  have hkey : ∀ m, eW.get m = none ∨ aG.get m = none := by
    intro m
    cases hmW : eW.get m with
    | none => exact Or.inl rfl
    | some ψW =>
      cases hmG : aG.get m with
      | none => exact Or.inr rfl
      | some ψG =>
        exfalso
        rcases AgW.dom_split haG hσG hmG with
          ⟨φ, hφ, hkφ⟩ | ⟨m', χc, f, hm', hkχ, hf, hsf⟩
        · rcases hF4 m φ hφ hkφ with rfl | ⟨φ', hφ', -, -⟩ | ⟨φ', hφ', -, -⟩
          · exact hF3 φ hφ hkφ
          · rcases hF1 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [h] at hφ'; simp at hφ'
          · rcases hF2 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [h] at hφ'; simp at hφ'
        · have hσGm' : σG.get m' = some χc :=
            ResU.CompS.get_right_of_immFree hσGc himmE hm'
          rcases hF4 m' χc hσGm' hkχ with
            rfl | ⟨φ', hφ', hkφ', hwφ'⟩ | ⟨φ', hφ', hkφ', hwφ'⟩
          · exact hF3 χc hσGm' hkχ
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le haρ m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rcases hF1 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [((ResU.Comp.eq_none_iff hz₀ m).mp h).1] at hsf; simp at hsf
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le hav m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rcases hF2 m with h | h
            · rw [h] at hmW; simp at hmW
            · rw [((ResU.Comp.eq_none_iff hz₀ m).mp h).1] at hsf; simp at hsf
  -- 6.37 with `⦇ρ_v ● ℓ ↦ own(v)⦈` defined
  have hceWaG : ResU.CompatS eW aG := ResU.Compat.of_disjoint hkey
  have hceWA : ResU.CompatS eW A := ResU.six37 hceWaG hWc.1 hA
  -- the third bullet's *"which implies … ▸◂ ℓ ↦ own(v)"*, and then `▸◂ ex(W)_●`
  have hEl : eG.get l = none := by
    rcases ResU.CompatS.disjoint_of_immFree himmE hcι l with h | h
    · exact h
    · rw [ResU.single_get_self] at h; simp at h
  have hceW : ResU.CompatS eG eW := ResU.Compat.of_disjoint (fun m => by
    by_cases hm : m = l
    · subst hm; exact Or.inl hEl
    · rcases ResU.CompatS.disjoint_of_immFree himmE hcexv m with h | h
      · exact Or.inl h
      · exact Or.inr ((ResU.Comp.eq_none_iff hfc m).mpr ⟨h, ResU.single_get_ne _ hm⟩))
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff eG eW).mpr hceW
  have hcEA : ResU.CompatS E A := ResU.Compat.of_disjoint (fun m => by
    rcases ResU.CompatS.disjoint_of_immFree himmE hcA m with h' | h'
    · rcases ResU.CompatS.disjoint_of_immFree himmW hceWA m with h'' | h''
      · exact Or.inl ((ResU.Comp.eq_none_iff hE m).mpr ⟨h', h''⟩)
      · exact Or.inr h''
    · exact Or.inr h')
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff E A).mpr hcEA
  -- the step-3 presupposition: `ρ′ ● ρ⁺/ℓ ▸◂ ρ_v ● ℓ ↦ own(v)`
  have hWm : ∀ m, m ≠ l → W.get m = ρv.get m := fun m hm =>
    ResU.Comp.get_of_right_none hW (ResU.single_get_ne _ hm)
  have hGW : ResU.CompatS G W := by
    intro m ψ₁ ψ₂ hg₁ hg₂
    by_cases hm : m = l
    · subst hm; rw [hGl] at hg₁; simp at hg₁
    · rw [hWm m hm] at hg₂
      by_cases hk₂ : ψ₂.kind = Kind.imm
      · obtain ⟨χ₂, hχ₂, hkχ₂, heχ₂, hwχ₂⟩ := AgW.get_imm hav hg₂ hk₂
        by_cases hk₁ : ψ₁.kind = Kind.imm
        · obtain ⟨χ₁, hχ₁, hkχ₁, heχ₁, hwχ₁⟩ := AgW.get_imm haG hg₁ hk₁
          obtain ⟨ξ, hξ⟩ := hA.1 m χ₁ χ₂ hχ₁ hχ₂
          obtain ⟨-, he₁', hw₁'⟩ := CellU.CompR.imm_left hξ hkχ₁
          obtain ⟨-, he₂', hw₂'⟩ := CellU.CompR.imm_left (CellU.CompR.comm hξ) hkχ₂
          exact CellU.compatS_iff.mpr ⟨hk₁, hk₂,
            heχ₁.symm.trans (he₁'.symm.trans (he₂'.trans heχ₂)),
            hwχ₁.symm.trans (hw₁'.symm.trans (hw₂'.trans hwχ₂))⟩
        · exfalso
          have hex₁ := ExS.get_of_ne_imm heG hg₁ hk₁
          rcases ResU.CompatS.disjoint_of_immFree himmE hcav m with h | h
          · rw [h] at hex₁; simp at hex₁
          · rw [h] at hχ₂; simp at hχ₂
      · exfalso
        have hex : exv.get m = some ψ₂ := ExS.get_of_ne_imm hexv hg₂ hk₂
        have heWm : eW.get m = some ψ₂ :=
          (ResU.Comp.get_of_right_none hfc (ResU.single_get_ne _ hm)).trans hex
        obtain ⟨χ₁, hχ₁, -, -, -⟩ := ResU.Flat.get hσG hg₁
        rcases ResU.CompatS.disjoint_of_immFree himmE hceW m with h | h
        · rcases hkey m with h' | h'
          · rw [h'] at heWm; simp at heWm
          · rw [(ResU.Comp.eq_none_iff hσGc m).mpr ⟨h, h'⟩] at hχ₁; simp at hχ₁
        · rw [h] at heWm; simp at heWm
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff G W).mpr hGW
  exact ⟨hGW, X, hX, σ, (ResU.Flat.split hX).mpr
    ⟨eG, eW, E, aG, av, A, heG, heW, hE, haG, haW, hA, hσ⟩⟩

/-- **`[TR]` 6.38 at the step index** (`ResU.six38`): (H1) `ρ # ρ_v ● ℓ ↦ own(v)`, (H2)
`ρ′ # ρ⁺`, (H3) `@ρ ⊐ α`, (H4) `@ρ′ ⊐ α`, (H5) `ρ⁺∣own = ∅`, (H6)
`ρ ● ℓ ↦ imm({α}, v, ρ_v) ↭ₙ ρ′ ● ρ⁺` give (G1) `ρ′ ● ρ⁺/ℓ # ρ_v ● ℓ ↦ own(v)`. -/
theorem six38N {Φ : LocFam} {n : Nat} {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp : ResU BoCa.Loc BoCa.Val}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h1 : ResU.Hash ρ W) (h2 : ResU.Hash ρ' ρp)
    (h3 : ρ.InStratum α) (h4 : ρ'.InStratum α)
    (h5 : ρp.restrict Kind.own = PMap.empty)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hpp : ResU.CompS ρ' ρp ρ'ρp) (h6 : UpdVN Φ n ρρi ρ'ρp) :
    ∃ G, ResU.CompS ρ' (ρp.del l) G ∧ ResU.Hash G W := by
  obtain ⟨hG, hGi, hGc⟩ := six38_steps_one_twoN hW h1 h2 h3 h4 hρi hpp h6
  exact ⟨ρ'ρp.del l, hG, sixThirtyEightResidualN hW h1 h3 h4 h5 hρi hpp h6 hG hGi hGc⟩

/-! ### `[TR]` 6.39 at the index -/

/-- **`[TR]` 6.39 at the step index**: (H1) `ρ # ℓ ↦ own(v) ● ρ_v`, (H2) `ρ′ # ℓ ↦ own(v) ● ρ_v`,
(H3) `ρ ● ℓ ↦ imm(α, v, ρ_v) ↭ₙ ρ′ ● ℓ ↦ imm(α, v, ρ_v)` give
`ρ ● ℓ ↦ own(v) ● ρ_v ↭ₙ ρ′ ● ℓ ↦ own(v) ● ρ_v`. The printed proof (`ResU.six39`): the `own` and
`imm` flattenings agree off `ℓ`, and at `ℓ` both `own` flattenings hold `own(v)`, no borrow. -/
theorem six39N {Φ : LocFam} {n : Nat} {l : Loc} {s : LSet} {v : Val}
    {ρ ρ' ρv ov iw iw' : WRes} {hstr : ρv.InStratum s.join}
    (hov : ResU.CompS (ResU.single l (CellU.ownOf v)) ρv ov)
    (h1 : ResU.Hash ρ ov) (h2 : ResU.Hash ρ' ov)
    (hi : ResU.CompS ρ (ResU.single l (CellU.immOf s v ρv hstr)) iw)
    (hi' : ResU.CompS ρ' (ResU.single l (CellU.immOf s v ρv hstr)) iw')
    (h3 : UpdVN Φ n iw iw') :
    ∃ w w', ResU.CompS ρ ov w ∧ ResU.CompS ρ' ov w' ∧ UpdVN Φ n w w' := by
  classical
  obtain ⟨-, w, hw, hvw⟩ := h1
  obtain ⟨-, w', hw', hvw'⟩ := h2
  obtain ⟨σof, hfof⟩ := hvw
  obtain ⟨σof', hfof'⟩ := hvw'
  obtain ⟨e₁, e₂, EX, a₁, a₂, AG, K, he₁, he₂, hEX, ha₁, ha₂, hAG, hK, hKσ⟩ :=
    ResU.flat_own_normal hov hw hfof
  obtain ⟨e₁', e₂', EX', a₁', a₂', AG', K', he₁', he₂', hEX', ha₁', ha₂', hAG',
    hK', hK'σ⟩ := ResU.flat_own_normal hov hw' hfof'
  rw [ExS.functional he₂' he₂] at hEX'
  rw [AgW.functional ha₂' ha₂] at hAG'
  have hnone : K.get l = none := ResU.compatS_single_own hKσ.1
  have hnone' : K'.get l = none := ResU.compatS_single_own hK'σ.1
  have hvv : ResU.Valid ρv :=
    (ResU.Valid.split hov (ResU.Valid.split hw ⟨σof, hfof⟩).2).2
  obtain ⟨σif, hfif⟩ := h3.2.1
  obtain ⟨σif', hfif'⟩ := h3.2.2
  have hiσ : ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) K σif :=
    ResU.flat_imm_normal hi hfif he₁ he₂ hEX ha₁ ha₂ hAG hK hnone hvv
  have hiσ' : ResU.CompS (ResU.single l (CellU.immOf s v ρv hstr)) K' σif' :=
    ResU.flat_imm_normal hi' hfif' he₁' he₂ hEX' ha₁' ha₂ hAG' hK' hnone' hvv
  have hoff : ∀ x : Loc, x ≠ l → σof.get x = σif.get x := fun x hx =>
    (ResU.compS_single_get_ne hKσ hx).trans (ResU.compS_single_get_ne hiσ hx).symm
  have hoff' : ∀ x : Loc, x ≠ l → σof'.get x = σif'.get x := fun x hx =>
    (ResU.compS_single_get_ne hK'σ hx).trans (ResU.compS_single_get_ne hiσ' hx).symm
  refine ⟨w, w', hw, hw', updN_of_flat hfof hfof' (fun x => ?_), ⟨σof, hfof⟩, ⟨σof', hfof'⟩⟩
  by_cases hx : x = l
  · subst hx
    rw [ResU.compS_single_get_self hKσ hnone, ResU.compS_single_get_self hK'σ hnone']
    refine ⟨fun s' w₀ χ hh => ⟨fun e => ?_, fun e => ?_⟩, fun ψ e hk => ?_, fun ψ e hk => ?_⟩
    · exact absurd (Option.some.inj e) CellU.ownOf_ne_immOf
    · exact absurd (Option.some.inj e) CellU.ownOf_ne_immOf
    · cases e; simp at hk
    · cases e; simp at hk
  · rw [hoff x hx, hoff' x hx]
    exact cellUpdN_of_updN h3.1 hfif hfif' x

end BoCa.Fig16.LogRel.Core.Chain.SI

end
