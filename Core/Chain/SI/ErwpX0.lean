import Core.Chain.SI.ErwpX

/-!
# `erwp` is the one relation's ghost-free instance  `[spec §62]`

`erwp_iff_erwpX0`: `erwp Φ Tb Q n ls e ρ ↔ erwpX Φ ∅ Tb↑ Q↑ n ls e (ρ, 0)`, where `Q↑` and `Tb↑`
are `Q` and `Tb` with every part they describe ghost-free (`postUp`, `tableUp`). By induction on
the index; the continuations agree below it.

* **(→)** At a frame `(ρ_f, g_f)`, `erwp`'s run at `ρ_f` gives the end, with no ghost at the end
  or in the garbage. The start is `WF_C` with no token, so it carries no counted lifetime; `↭`
  keeps the `imm` cells, so neither does the end nor the garbage (`carries_of_updImmM`).
* **(←)** At the frame `(ρ_f, 0)`, where `WF_∅` is vacuous, the ghost-free post and table give
  the end's ghost `0`, and the empty mask reads `↭` as `UpdVN`.

The guard G is the same condition on both sides, `FrameKept` at the frame's world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- `Q↑`: `Q` at the ghost-free resources. -/
def postUp (Q : PostN) : PostX := fun _ k ls v x => x.2 = 0 ∧ Q k ls v x.1

/-- `Tb↑`: `Tb` at the ghost-free resources, owing its continuation at the ghost-free ones. -/
def tableUp (Tb : TableN) : TableX := fun _ k ls t Ψ x =>
  x.2 = 0 ∧ Tb k ls t (fun k' ls' e' ρ => Ψ k' ls' e' (ρ, 0)) x.1

/-- At the empty mask, `UpdVNm` is `UpdVN`. -/
theorem updVNm_locs_empty_iff {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ : WRes} :
    UpdVNm Φ n (∅ : Mask).locs ρ₁ ρ₂ ↔ UpdVN Φ n ρ₁ ρ₂ := by
  rw [Mask.locs_empty]; exact updVNm_empty_iff

/-- **`erwp` is `erwpX` at the empty mask and the empty ghost.** -/
theorem erwp_iff_erwpX0 (Φ : LocFam) (Tb : TableN) (Q : PostN) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ Tb Q n ls e ρ ↔
      erwpX (ℍ := ℍ) Φ ∅ (tableUp Tb) (postUp Q) n ls e (ρ, 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- the continuations owed below `n` agree
  have hC : (fun k' ls' e' ρ => erwpXC (ℍ := ℍ) Φ ∅ (tableUp Tb) (postUp Q) n k' ls' e' (ρ, 0)) =
      erwpC (ℍ := ℍ) Φ Tb Q n := by
    funext k' ls' e' ρ
    by_cases hk : k' < n
    · simp only [erwpXC, erwpC, hk, if_true]
      exact propext (ih k' hk ls' e' ρ).symm
    · simp only [erwpXC, erwpC, hk, if_false]
  intro ls e ρ
  rw [erwp_eq, erwpX_eq]
  constructor
  · intro h xf fρ ps μ hf hc hv _ hwx _ _ hT htg hl hfd j μ' e' hj hrun
    refine ⟨h.kept hf hc hT htg hl hfd hj hrun, fun hfin => ?_⟩
    obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
      h₁₃⟩ := h.run hf hc hT htg hl hfd hj hrun hfin
    -- the start carries no counted lifetime, so neither does what `↭` reaches
    have hno : ∀ α, α ∈ (xf.2 + 0).counted → ¬ Carries π α := by
      intro α hα hcπ
      have hcρ : Carries ρ α :=
        carries_of_updImmM (M := ∅) (fun l _ => h₇.1.1 l) hcπ (fun _ _ _ _ _ _ _ => by simp)
      have := hwx α hα hcρ
      simp at this
    have hvπ : π.Valid := h₇.2.2
    refine ⟨ρ', ρp, fρ', fρ'p, π, 0, 0, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆,
      updVNm_locs_empty_iff.mpr h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, by simpa using hv, ?_, ?_, ?_,
      maskShallow_locs_empty _, maskShallow_locs_empty _, maskAuth_empty _, ?_⟩
    · intro α h₁α h₂α; simp only [GRes.add_zero] at h₁α h₂α; exact absurd h₁α h₂α
    · intro α hα hcρ'
      simp only [GRes.add_zero] at hα
      exact absurd (carries_comp_left h₆ hvπ hcρ') (hno α (by simpa using hα))
    · intro α hα hcp
      simp only [GRes.add_zero] at hα
      exact absurd (carries_comp_right h₆ hvπ hcp) (hno α (by simpa using hα))
    · rcases h₁₃ with ⟨v, hv', hq⟩ | ht
      · exact Or.inl ⟨v, hv', rfl, hq⟩
      · refine Or.inr ⟨rfl, ?_⟩
        rw [hC]; exact ht
  · intro h ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
    have hr := h (ρf, 0) fρ ps μ hf hc (by simpa using GRes.valid_zero)
        (fun α hα _ => by simp [GRes.counted] at hα) (fun α hα _ => by simp [GRes.counted] at hα) (maskShallow_locs_empty _) (maskAuth_empty _) hT htg hl hfd
        j μ' e' hj hrun
    refine ⟨hr.1, fun hfin => ?_⟩
    obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
      h₁₁, h₁₂, -, -, -, -, -, -, -, h₂₀⟩ := hr.2 hfin
    refine ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆,
      updVNm_locs_empty_iff.mp h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, ?_⟩
    rcases h₂₀ with ⟨v, hv', -, hq⟩ | ⟨-, ht⟩
    · exact Or.inl ⟨v, hv', hq⟩
    · refine Or.inr ?_
      rw [← hC]; exact ht

end BoCa.Fig16.LogRel.Core.Chain.SI

end
