import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Singletons
import Support.Model.Surgery

/-!
# Support — Model — FrameSurgery

`[about ours]`.  The swaps §6.3's frame rules spend at both ends of the run: `ℓ ↦ own(v) ● ρ_P̂(v)` against the `mut` or `imm` cell that borrows it, under a frame, lowered and validated.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {Loc Val : Type}

/-- A valid `mut` cell does not hold its own location in its witness.
`[about ours: what `[TR]` 6.66's "assuming all compositions are defined" asks
of the borrowed cell, from `✓`]` -/
theorem ResU.wit_get_none_of_valid_mut {l : Loc} {b : Life} {v : Val} {σ : ResU Loc Val}
    {h : ResU.InStratum b σ} {P : Val → SPropS Loc Val b} {hw : P v ⟨σ, h⟩}
    (hv : ResU.Valid (ResU.single l (CellU.mutOf b v σ h P hw))) : σ.get l = none := by
  classical
  obtain ⟨F, e₂, a, he₂, ha, hc⟩ := hv
  obtain ⟨ev, hev, hcev⟩ := ExW.single_mut_inv he₂
  have hava : AgW σ a := AgW.single_mut_inv ha
  obtain ⟨τ, hτ₁, hτ₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.mutOf b v σ h P hw)) ev a F).mpr ⟨e₂, hcev, hc⟩
  have hFlatσ : ResU.Flat σ τ := ⟨ev, a, hev, hava, hτ₁⟩
  have hτl : τ.get l = none := ResU.compatS_single_mut hτ₂.1
  by_contra hne
  obtain ⟨ψ, hψ⟩ : ∃ ψ, σ.get l = some ψ := by
    cases hg : σ.get l with
    | none => exact absurd hg hne
    | some ψ => exact ⟨ψ, rfl⟩
  obtain ⟨χ, hχ, -⟩ := ResU.Flat.get hFlatσ hψ
  rw [hτl] at hχ
  simp at hχ

/-- `ρ_v ● ℓ ↦ own(v)` is defined whenever `ℓ ↦ mut(β, v, ρ_v, P̂)` is valid:
the `ρ_ℓ ● ρ_P̂(v)` of `[TR]` 6.66. -/
theorem ResU.compS_own_of_valid_mut {l : Loc} {b : Life} {v : Val} {σ : ResU Loc Val}
    {h : ResU.InStratum b σ} {P : Val → SPropS Loc Val b} {hw : P v ⟨σ, h⟩}
    (hv : ResU.Valid (ResU.single l (CellU.mutOf b v σ h P hw))) :
    ∃ W, ResU.CompS σ (ResU.single l (CellU.ownOf v)) W :=
  (ResU.compS_defined_iff _ _).mpr (ResU.Compat.of_disjoint (fun x => by
    by_cases hx : x = l
    · exact Or.inl (hx ▸ ResU.wit_get_none_of_valid_mut hv)
    · exact Or.inr (ResU.single_get_ne _ hx)))

/-- `[TR]` 6.66's H24, *"By lemmas 6.25 and 6.8 …"*: the `mut` cell and
`ρ_v ● ℓ ↦ own(v)` lower to the same memory under a frame. -/
theorem ResU.lower_swap_mut_own {l : Loc} {b : Life} {v : Val}
    {σ W F G frame : ResU Loc Val} {h : ResU.InStratum b σ}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨σ, h⟩} {w : Loc → Option Val}
    (hW : ResU.CompS σ (ResU.single l (CellU.ownOf v)) W)
    (hvm : ResU.Valid (ResU.single l (CellU.mutOf b v σ h P hw)))
    (hvW : ResU.Valid W)
    (hF : ResU.CompS frame (ResU.single l (CellU.mutOf b v σ h P hw)) F)
    (hHF : ResU.Hash frame (ResU.single l (CellU.mutOf b v σ h P hw)))
    (hG : ResU.CompS frame W G) (hHG : ResU.Hash frame W) :
    (F.Lower w ↔ G.Lower w) := by
  obtain ⟨σm, hσm⟩ := hvm
  have hLm : ResU.Lower (ResU.single l (CellU.mutOf b v σ h P hw))
      (fun x => (σm.get x).map CellU.erase) := ⟨σm, hσm, fun _ => rfl⟩
  have hLW : ResU.Lower W (fun x => (σm.get x).map CellU.erase) :=
    (ResU.six25 hW ⟨σm, hσm⟩ hvW).mp hLm
  exact ResU.Lower.congr hLm hLW hF hHF hG hHG

/-- `[TR]` 6.64's H34, *"By lemmas 6.26 and 6.8 …"*: the `imm` cell and
`ρ_v ● ℓ ↦ own(v)` lower to the same memory under a frame. -/
theorem ResU.lower_swap_imm_own {l : Loc} {s : LSet} {v : Val}
    {ρv W F G frame : ResU Loc Val} {hs : ρv.InStratum s.join}
    {w : Loc → Option Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hvi : ResU.Valid (ResU.single l (CellU.immOf s v ρv hs)))
    (hvW : ResU.Valid W)
    (hF : ResU.CompS frame (ResU.single l (CellU.immOf s v ρv hs)) F)
    (hHF : ResU.Hash frame (ResU.single l (CellU.immOf s v ρv hs)))
    (hG : ResU.CompS frame W G) (hHG : ResU.Hash frame W) :
    (F.Lower w ↔ G.Lower w) := by
  obtain ⟨σi, hσi⟩ := hvi
  have hLi : ResU.Lower (ResU.single l (CellU.immOf s v ρv hs))
      (fun x => (σi.get x).map CellU.erase) := ⟨σi, hσi, fun _ => rfl⟩
  have hLW : ResU.Lower W (fun x => (σi.get x).map CellU.erase) :=
    (ResU.six26 hW ⟨σi, hσi⟩ hvW).mp hLi
  exact ResU.Lower.congr hLi hLW hF hHF hG hHG

/-- `[TR]` 6.66's *"note since `ρ_m` is well formed, `ρ''_m` is as well"*. -/
theorem ResU.valid_single_mut_of_wit {l : Loc} {b : Life} {v : Val}
    {σ W : ResU Loc Val} {h : ResU.InStratum b σ}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨σ, h⟩}
    (hW : ResU.CompS σ (ResU.single l (CellU.ownOf v)) W) (hvW : ResU.Valid W) :
    ResU.Valid (ResU.single l (CellU.mutOf b v σ h P hw)) := by
  obtain ⟨-, s, hs, hv⟩ := ResU.six23 (ρ := PMap.empty) hW
    ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), W, ResU.comp_empty_left _, hvW⟩
  rwa [← ResU.eq_of_comp_empty_left hs] at hv

end BoCa.Fig16

end
