import Targets.I.Device
import Targets.B.BoLo

/-!
# The interaction — done's world conjuncts at Core σ=[] (RESTRUCTURE §3.3)

I's `Bounds` and `Interface` at `coreW`: `sliceShapeI_core`, `effInterp_core` (`cC_effOf`),
`shareMono_core` (`contShare`'s monotonicity), `adequateEvery_core` (`wpTS_demonic`'s replay at
`wpG`, with `arun_rest_irr`), `arises_core`, `exclusive_core` (`TW.valid`, `TW.inv`).
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `coreW`'s nil slice holds nothing and stops at R-T1, by unfolding. -/
theorem sliceShapeI_core : SliceShapeI (coreW (ℍ := ℍ)) :=
  ⟨fun _ => rfl, fun _ _ _ _ _ => Iff.rfl⟩



end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem effInterp_core : EffInterp (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro S R i δ e ρ _
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down, rowTabW_core]
  exact cC_effOf S R ls δ e ρ

theorem shareMono_core : ShareMono (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ Φ' ρ _ hΦ h
  obtain ⟨hu, hk⟩ := h
  exact ⟨hu, fun ls' he => ⟨fun w σ₁ σ₂ hB hc => hΦ _ _ _ ((hk ls' he).1 w σ₁ σ₂ hB hc),
    (hk ls' he).2⟩⟩

theorem arises_core : Arises (coreW (ℍ := ℍ)) := by
  intro fρ ps i h
  obtain ⟨hT, htg⟩ := h
  exact ⟨ps, i.1, fun p => by simp, fun x => by simp, hT, htg⟩

theorem exclusive_core : Exclusive (coreW (ℍ := ℍ)) := by
  intro fρ ps i h
  obtain ⟨hT, -⟩ := h
  exact ⟨TW.valid hT, ps, i.1, fun p => by simp, fun x => by simp, TW.inv hT⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`AdequateEvery coreW`.** -/
theorem adequateEvery_core : AdequateEvery (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro i fρ ρf ρ ps μ S A δ e _ hF hf hc hμ h μ₁ e₁ hs
  rcases i with ⟨ls, ⟨⟩⟩
  obtain ⟨hT, htg⟩ := hF
  have hw := ewp_unfold (opTable_mono _) ((cC_effOf S A ls δ e ρ).mp h)
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨_, _, _, _, _, t, μ₀, μ', _, _, _, _, _, h₄, _, _, ⟨k', h₈⟩, _, _, _, _, _, _, _, hQ⟩ :=
    hw ρf fρ ps hf hc hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₄ hμ
  have ht : IsVal t ∨ StopsIn S t := by
    rcases hQ with ⟨v, rfl, -⟩ | hQ
    · exact Or.inl v.2
    · right
      rcases hQ with ⟨K, n, j, v, en, hp⟩ | ⟨K, n, j, v, en, hp⟩
      · obtain ⟨⟨rfl, hK, hT', ha⟩, -⟩ := pure_sep_iff.mp hp
        obtain ⟨o, hf', rfl⟩ := Row.tab_some hT'
        exact Or.inl ⟨K, n, j, v, o, rfl, hK, hf', ha⟩
      · obtain ⟨⟨rfl, hK, hT', ha⟩, -⟩ := pure_sep_iff.mp hp
        obtain ⟨o, hf', rfl⟩ := Row.tab_some hT'
        exact Or.inr ⟨K, n, j, v, o, rfl, hK, hf', ha⟩
  have hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) (Alloc.replay cs) k' μ' t k₂ μ₂ e₂ := by
    intro k₂ μ₂ e₂ hstep
    rcases ht with hv | hst
    · exact BoCa.BoLo.no_step_val (w := ⟨t, hv⟩) hstep.toStep1
    · exact stop_irreducible hst hstep.toStep1
  exact ⟨μ', t, (arun_rest_irr hirr hrun h₈).toSteps, ht⟩

end Targets

end
