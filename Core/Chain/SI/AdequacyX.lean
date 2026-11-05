import Core.Chain.SI.LendX
import Core.Chain.SI.LoopN
import Core.Chain.SI.ErwpX0

/-!
# Adequacy at the one relation  `[spec §62]`

`erwpX_adequacy`: a closed program in `erwpX` at the empty mask and the table with no stop, from
`(∅, 0)` at every index, whose post owns no cell, is `OrDiverges`: every run goes on or reaches a
value, a value is reached at the empty memory, and every `free` finds its cell. `erwp_adequacy`'s
proof (`SI/LoopN.lean`) at the frame `(∅, 0)`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- The run of `e` from `(∅, 0)` at the frame `(∅, 0)`. -/
private theorem erwpX_end_empty {Φ : LocFam} {Q : PostX} {P₀ : Expr} {n : Nat}
    (h : erwpX (ℍ := ℍ) Φ ∅ TableX.none Q n [] P₀ ((PMap.empty : WRes), 0)) {j : Nat}
    {μ : Heap} {e : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j (fun _ => none) P₀ μ e)
    (hfin : Final (ℍ := ℍ) μ e) :
    EndOKX Φ ∅ (erwpXPost TableX.none Q (erwpXC (ℍ := ℍ) Φ ∅ TableX.none Q n)) (n - j) []
      ((PMap.empty : WRes), 0) ((PMap.empty : WRes), 0) [] μ e := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  rw [erwpX_eq] at h
  exact (h ((PMap.empty : WRes), 0) PMap.empty [] (fun _ => none) Fig16.LogRel.hash_empty
    (ResU.comp_empty_right _) (by simpa using GRes.valid_zero)
    (fun α hα _ => by simp [GRes.counted] at hα) (fun α hα _ => by simp [GRes.counted] at hα)
    (maskShallow_locs_empty _) (maskAuth_empty _) (maskOff_empty _) TWNC.empty htg Fig16.BoLo.lower_empty fd_empty
    j μ e hj hrun).2 hfin

/-- **Safety at the one relation.** -/
theorem erwpX_safe {Φ : LocFam} {Q : PostX} {P₀ : Expr}
    (hall : ∀ n, erwpX (ℍ := ℍ) Φ ∅ TableX.none Q n [] P₀ ((PMap.empty : WRes), 0))
    {j : Nat} {μ' : Heap} {e' : Expr}
    (hrun : StepsN (ℍ := ℍ) j (fun _ => none) P₀ μ' e') :
    IsVal e' ∨ ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'' := by
  classical
  by_cases hs : ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e''
  · exact .inr hs
  · have hfin : Final (ℍ := ℍ) μ' e' := fun μ'' e'' h => hs ⟨μ'', e'', h⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hq⟩ := erwpX_end_empty (hall (j + 1)) (by omega) hrun hfin
    rcases hq with ⟨v, rfl, -⟩ | h
    · exact .inl v.2
    · exact h.elim

/-- **Adequacy at the one relation**: safe or divergent, every value at the empty memory, every
`free` finding its cell. -/
theorem erwpX_adequacy {Φ : LocFam} {Q : PostX} {P₀ : Expr}
    (hQ : ∀ C k ls v (x : XRes), Q C k ls v x → x.1 = PMap.empty)
    (hall : ∀ n, erwpX (ℍ := ℍ) Φ ∅ TableX.none Q n [] P₀ ((PMap.empty : WRes), 0)) :
    OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have hp := erwpX_safe (Φ := Φ) hall hrun
  refine ⟨hp, fun hv => ?_, fun K ℓ he => ?_⟩
  · obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h1, h2, h3, h6, h7, h9, h10, h11, -, -,
      -, -, -, -, -, -, -, -, -, -, hq⟩ :=
      erwpX_end_empty (hall (j + 1)) (by omega) hrun (final_val μ ⟨e, hv⟩)
    rcases hq with ⟨v, -, hqv⟩ | h
    · obtain rfl : ρ' = PMap.empty := hQ _ _ _ _ _ hqv
      obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
      obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
      obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
      obtain rfl : ρp = PMap.empty := reclaimN ρp (updVNm_locs_empty_iff.mp h10) h11
      exact ResU.Lower.functional h7 Fig16.BoLo.lower_empty
    · exact h.elim
  · subst he
    rcases hp with hv | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hv
      simp [BoLo.freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
