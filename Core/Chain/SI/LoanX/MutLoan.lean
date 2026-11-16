import Core.Chain.SI.LoanX.ErwpX
import Core.Chain.SI.IFrameN
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)
theorem flat_single_own_eq {l : Loc} {v : Val} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (CellU.ownOf v)) τ) :
    τ = ResU.single l (CellU.ownOf v) :=
  ResU.Flat.functional hτ (ResU.flat_single_own l v)

theorem maskShallow_single_own (L : Set Loc) (l : Loc) (v : Val) :
    MaskShallow L (ResU.single l (CellU.ownOf v)) := by
  intro m _ t u χ hh ⟨τ, hτ, hg⟩
  obtain rfl := flat_single_own_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact absurd (Option.some.inj hg) CellU.ownOf_ne_immOf
  · rw [ResU.single_get_ne _ hm] at hg; cases hg


theorem flatAt_off_swap {ρ₁ ρ₂ X A B : WRes} {l : Loc}
    (h₁ : ∀ τ, ResU.Flat ρ₁ τ → ∀ m, m ≠ l → τ.get m = none)
    (h₂ : ∀ τ, ResU.Flat ρ₂ τ → ∀ m, m ≠ l → τ.get m = none)
    (hA : ResU.CompS ρ₁ X A) (hB : ResU.CompS ρ₂ X B) (hvA : A.Valid) (hvB : B.Valid)
    {m : Loc} (hm : m ≠ l) (ψ : CellU Loc Val) : A.FlatAt m ψ ↔ B.FlatAt m ψ := by
  have key : ∀ {ρ₁ ρ₂ A B : WRes},
      (∀ τ, ResU.Flat ρ₁ τ → ∀ m, m ≠ l → τ.get m = none) →
      (∀ τ, ResU.Flat ρ₂ τ → ∀ m, m ≠ l → τ.get m = none) →
      ResU.CompS ρ₁ X A → ResU.CompS ρ₂ X B → B.Valid → A.FlatAt m ψ → B.FlatAt m ψ := by
    intro ρ₁ ρ₂ A B h₁ h₂ hA hB hvB ⟨σ, hσ, hg⟩
    obtain ⟨σ₁, σX, hσ₁, hσX, hR⟩ := flat_compR hA hσ
    obtain ⟨σB, hσB⟩ := hvB
    obtain ⟨σ₂, σX', hσ₂, hσX', hR'⟩ := flat_compR hB hσB
    obtain rfl := ResU.Flat.functional hσX' hσX
    refine ⟨σB, hσB, ?_⟩
    rw [ResU.Comp.get_of_left_none hR' (h₂ _ hσ₂ m hm), ← hg,
      ResU.Comp.get_of_left_none hR (h₁ _ hσ₁ m hm)]
  exact ⟨key h₁ h₂ hA hB hvB, key h₂ h₁ hB hA hvA⟩


theorem single_own_off {l : Loc} {v : Val} :
    ∀ τ, ResU.Flat (ResU.single l (CellU.ownOf v)) τ → ∀ m, m ≠ l → τ.get m = none := by
  intro τ hτ m hm
  rw [flat_single_own_eq hτ, ResU.single_get_ne _ hm]

/-- `↭` from a resource that flattens as another outside the mask. -/
theorem UpdVNm.of_flatAt_off {Φ : LocFam} {n : Nat} {L : Set Loc} {A B π : WRes}
    (h : UpdVNm Φ n L B π) (hvA : A.Valid)
    (hAB : ∀ m, m ∉ L → ∀ ψ, A.FlatAt m ψ ↔ B.FlatAt m ψ) : UpdVNm Φ n L A π := by
  refine ⟨⟨fun m hm s v χ hh => (hAB m hm _).trans (h.1.1 m hm s v χ hh),
    fun m hm ψ hψ hk => h.1.2.1 m hm ψ ((hAB m hm ψ).mp hψ) hk,
    fun m hm ψ' hψ hk => ?_⟩, hvA, h.2.2⟩
  obtain ⟨ψ, hψB, hs⟩ := h.1.2.2 m hm ψ' hψ hk
  exact ⟨ψ, (hAB m hm ψ).mpr hψB, hs⟩

/-- The lend masks `ℓ`. -/

theorem maskShallow_swap {S : Set Loc} {A B : WRes} (h : MaskShallow S B)
    (hAB : ∀ m, m ∈ S → ∀ ψ, A.FlatAt m ψ → B.FlatAt m ψ) : MaskShallow S A :=
  fun m hm s v χ hh hf => h m hm s v χ hh (hAB m hm _ hf)


theorem not_carries_single_own (l : Loc) (v : Val) (α : Life) :
    ¬ Carries (ResU.single l (CellU.ownOf v)) α := by
  rintro ⟨x, s, w, χ, hh, ⟨σ, hσ, hg⟩, -⟩
  obtain rfl := ResU.Flat.functional hσ (ResU.flat_single_own l v)
  by_cases hx : x = l
  · subst hx
    rw [ResU.single_get_self] at hg
    exact CellU.ownOf_ne_immOf (Option.some.inj hg)
  · rw [ResU.single_get_ne _ hx] at hg; cases hg


theorem flat_single_mut_eq {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) τ) :
    τ = ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain ⟨e₀, he₀, hce⟩ := ExW.single_mut_inv he
  obtain rfl : e₀ = PMap.empty := ExS.functional he₀ exW_empty
  obtain rfl : ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) = e :=
    ResU.eq_of_comp_empty_right hce
  obtain rfl : a = PMap.empty := AgW.functional (AgW.single_mut_inv ha) agW_empty
  exact (ResU.eq_of_comp_empty_right hc).symm

theorem single_mut_off {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} :
    ∀ τ, ResU.Flat (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) τ → ∀ m, m ≠ l →
      τ.get m = none := by
  intro τ hτ m hm
  rw [flat_single_mut_eq hτ, ResU.single_get_ne _ hm]

theorem maskShallow_single_mut (L : Set Loc) {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} :
    MaskShallow L (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) := by
  intro m _ t u χ hh ⟨τ, hτ, hg⟩
  obtain rfl := flat_single_mut_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact absurd (Option.some.inj hg) (Ne.symm CellU.immOf_ne_mutOf)
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

theorem not_carries_single_mut {l : Loc} {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} (α : Life) :
    ¬ Carries (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) α := by
  rintro ⟨m, t, u, χ, hh, ⟨τ, hτ, hg⟩, -⟩
  obtain rfl := flat_single_mut_eq hτ
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self] at hg
    exact CellU.immOf_ne_mutOf (Option.some.inj hg).symm
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

theorem Mask.locs_of_mem {M : Mask} {l : Loc} {a : Auth} (h : (l, a) ∈ M) : l ∈ M.locs :=
  ⟨a, h⟩

/-- **A `mut` loan opened at the start of a run, at a mask holding its authority.** -/
theorem rwpGX_mutLoanOpen {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {l : Loc}
    {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val} {hstr : ResU.InStratum β (PMap.empty : WRes)}
    {P : Val → SPropS Loc Val β} (hw : P v ⟨PMap.empty, hstr⟩) (e : Expr) (ls : List SRec)
    {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρ)
    (hbody : ∀ ρm, ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρm →
      rwpGX (ℍ := ℍ) Φ M Q n ls e (ρm, g)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH2 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  set ρf : WRes := xf.1 with hρfdef
  set mc : WRes := ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) with hmcdef
  set W : WRes := ResU.single l (CellU.ownOf v) with hWdef
  have hW : ResU.CompS (PMap.empty : WRes) W W := compS_empty_left _
  have hvW : ResU.Valid W := ResU.valid_single_own l v
  have hvm : ResU.Valid mc := ResU.valid_single_mut_of_wit hW hvW
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- `sρ = (ρ_f ● ρ_a) ● ℓ ↦ own(v)`
  obtain ⟨Z, hZ, hZo⟩ := (ResU.CompS.assoc ρf ρa W sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  have hZW : ResU.Hash Z W := ⟨hZo.1, sρ, hZo, hvsρ⟩
  have hZm : ResU.Hash Z mc := (ResU.six24 hW).mpr hZW
  obtain ⟨W', hW'c, hvW'⟩ := hZm.2
  -- the borrow cell beside `ρ_a`
  obtain ⟨ρm, hρm, hfm⟩ := (ResU.CompS.assoc ρf ρa mc W').mpr ⟨Z, hZ, hW'c⟩
  have hvρm : ResU.Valid ρm := (ResU.Valid.split hfm hvW').2
  have hHf : ResU.Hash ρf ρm := ⟨hfm.1, W', hfm, hvW'⟩
  have hX : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes) W :=
    ResU.comp_empty_right _
  have hTin : TWNC W' ps (rsOf ls) :=
    TWNC.mutFold hT hX (ResU.CompS.comm hZo) (ResU.CompS.comm hW'c) hvW'
  have htgin : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hX (ResU.CompS.comm hZo) (ResU.CompS.comm hW'c) a).mpr ha) htg
  have hlowin : ResU.Lower W' μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hW'c hZm hZo hZW).mpr hlow
  have hwxm : WFC (xf.2 + g).counted (ρm, g) := by
    intro α hα hc
    rcases carries_comp_split hρm hc with h | h
    · exact hwx α hα (carries_comp_right hcρ hvρ h)
    · exact absurd h (not_carries_single_mut α)
  have hshm : MaskShallow M.locs ρm :=
    maskShallow_comp hρm (maskShallow_right hcρ hvρ hsh) (maskShallow_single_mut _)
  have hr := hbody ρm (ResU.CompS.comm hρm) xf W' ps μ hHf hfm hv hwf hwxm hshm hau hoff hTin
    htgin hlowin hfd jr μ' e' hj hrun
  intro hfin
  obtain ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hSx, hFx, hq⟩ := hr hfin
  have hlM : l ∈ M.locs := Mask.locs_of_mem hl
  have hoffl : ∀ m, m ≠ l → ∀ ψ, ρ.FlatAt m ψ ↔ ρm.FlatAt m ψ := fun m hml ψ =>
    flatAt_off_swap single_own_off single_mut_off hcρ (ResU.CompS.comm hρm) hvρ hvρm hml ψ
  refine ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff,
    maskShallow_swap hSx (fun m hm ψ => (hoffl m (fun h => hm.2 (h ▸ hlM)) ψ).mp), hFx, hq⟩
  refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => hoffl m (fun h => hm ?_) ψ)
  rw [h, Mask.locs_union]; exact Or.inl hlM

/-- **A `mut` loan ended at the start of a run, at a mask holding its authority**: the borrow cell,
given back, unfolds into `ℓ ↦ own(v)`. -/
theorem rwpGX_mutLoanEnd {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {l : Loc}
    {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val} {hstr : ResU.InStratum β (PMap.empty : WRes)}
    {P : Val → SPropS Loc Val β} {hw : P v ⟨PMap.empty, hstr⟩} (e : Expr) (ls : List SRec)
    {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρ)
    (hbody : ∀ ρo, ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρo →
      rwpGX (ℍ := ℍ) Φ M Q n ls e (ρo, g)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH2 hsρ hv hwf hwx hsh hau hoff hT htg hlow hfd jr μ' e' hj hrun
  set ρf : WRes := xf.1 with hρfdef
  set mc : WRes := ResU.single l (CellU.mutOf β v PMap.empty hstr P hw) with hmcdef
  set W : WRes := ResU.single l (CellU.ownOf v) with hWdef
  have hW : ResU.CompS (PMap.empty : WRes) W W := compS_empty_left _
  have hvW : ResU.Valid W := ResU.valid_single_own l v
  have hvm : ResU.Valid mc := ResU.valid_single_mut_of_wit hW hvW
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- `sρ = (ρ_f ● ρ_a) ● ℓ ↦ mut(β, v, ∅, P̂)`
  obtain ⟨Z, hZ, hZm⟩ := (ResU.CompS.assoc ρf ρa mc sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  have hZmH : ResU.Hash Z mc := ⟨hZm.1, sρ, hZm, hvsρ⟩
  have hZW : ResU.Hash Z W := (ResU.six24 hW).mp hZmH
  obtain ⟨W', hW'c, hvW'⟩ := hZW.2
  obtain ⟨ρo, hρo, hfo⟩ := (ResU.CompS.assoc ρf ρa W W').mpr ⟨Z, hZ, hW'c⟩
  have hvρo : ResU.Valid ρo := (ResU.Valid.split hfo hvW').2
  have hHf : ResU.Hash ρf ρo := ⟨hfo.1, W', hfo, hvW'⟩
  have hX : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes) W :=
    ResU.comp_empty_right _
  have hTin : TWNC W' ps (rsOf ls) :=
    TWNC.mutUnfold hT (ResU.CompS.comm hZm) hX (ResU.CompS.comm hW'c) hvW'
  have htgin : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hX (ResU.CompS.comm hW'c) (ResU.CompS.comm hZm) a).mp ha) htg
  have hlowin : ResU.Lower W' μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hZm hZmH hW'c hZW).mp hlow
  have hwxo : WFC (xf.2 + g).counted (ρo, g) := by
    intro α hα hc
    rcases carries_comp_split hρo hc with h | h
    · exact hwx α hα (carries_comp_right hcρ hvρ h)
    · exact absurd h (not_carries_single_own l v α)
  have hsho : MaskShallow M.locs ρo :=
    maskShallow_comp hρo (maskShallow_right hcρ hvρ hsh) (maskShallow_single_own _ _ _)
  have hr := hbody ρo (ResU.CompS.comm hρo) xf W' ps μ hHf hfo hv hwf hwxo hsho hau hoff hTin
    htgin hlowin hfd jr μ' e' hj hrun
  intro hfin
  obtain ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff, hSx, hFx, hq⟩ := hr hfin
  have hlM : l ∈ M.locs := Mask.locs_of_mem hl
  have hoffl : ∀ m, m ≠ l → ∀ ψ, ρ.FlatAt m ψ ↔ ρo.FlatAt m ψ := fun m hml ψ =>
    flatAt_off_swap single_mut_off single_own_off hcρ (ResU.CompS.comm hρo) hvρ hvρo hml ψ
  refine ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, hNo, hT', htg',
    hps', hls', hV, hN, hW'', hWp, hS', hSπ, hAu, hOff,
    maskShallow_swap hSx (fun m hm ψ => (hoffl m (fun h => hm.2 (h ▸ hlM)) ψ).mp), hFx, hq⟩
  refine UpdVNm.of_flatAt_off hU hvρ (fun m hm ψ => hoffl m (fun h => hm ?_) ψ)
  rw [h, Mask.locs_union]; exact Or.inl hlM

theorem erwpX_mutLoanOpen {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat}
    {l : Loc} {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    (hw : P v ⟨PMap.empty, hstr⟩) (e : Expr) (ls : List SRec) {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρ)
    (hbody : ∀ ρm, ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρm →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρm, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mutLoanOpen hl hw e ls hcρ (fun ρm hρm => ?_)
  have hb := hbody ρm hρm
  rwa [erwpX_eq] at hb

theorem erwpX_mutLoanEnd {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat}
    {l : Loc} {κ : Life} (hl : (l, Auth.mloan κ) ∈ M) {β : Life} {v : Val}
    {hstr : ResU.InStratum β (PMap.empty : WRes)} {P : Val → SPropS Loc Val β}
    {hw : P v ⟨PMap.empty, hstr⟩} (e : Expr) (ls : List SRec) {ρa ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.mutOf β v PMap.empty hstr P hw)) ρa ρ)
    (hbody : ∀ ρo, ResU.CompS (ResU.single l (CellU.ownOf v)) ρa ρo →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρo, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mutLoanEnd hl e ls hcρ (fun ρo hρo => ?_)
  have hb := hbody ρo hρo
  rwa [erwpX_eq] at hb


end BoCa.Fig16.LogRel.Core.Chain.SI
end
