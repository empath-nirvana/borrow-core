import Targets.B.Guarantees

/-!
# System B — the run-end relation's laws where `Upd` is Core's (FIX-RUN-END §2.3)

At `BWorld`: where `Upd` is Core's `↭` at every index, the
run-end laws and the printed route's forms of `↭`'s lemmas hold, each from Core's lemma as Core's
proof reads it: `updRefl_of_core` (6.47), `updOwn_of_core`, `updSeq_of_core` (6.48 then 6.49),
`updReclaim_of_core` (`reclaim`), `updFrame_of_core` (6.48), `updOutlives_of_core` (6.50),
`updMutBack_of_core` (6.27, 6.28), `updImmBack_of_core` (6.29, 6.38, 6.39),
`updLendBack_of_core`; at `coreB` (`coreW_upd`, by `Iff.rfl`) each `upd*_core`.  Beside done:
`UpdSeq` and `UpdReclaim` are the device's `AdequateOfLaws` hypotheses.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `B.coreB`'s run-end relation is Core's `↭` at every index. -/
theorem coreW_upd : ∀ (i i' : Idx Unit) (ρ ρ' π : WRes),
    (B.coreB (ℍ := ℍ)).Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π := fun _ _ _ _ _ => Iff.rfl

/-- 6.47 (`ResU.updV_self_iff`), as `wpG_here` reads it, where `Upd` is Core's at every index. -/
theorem updRefl_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdRefl M :=
  fun _ _ ρ _ _ hf _ _ => (hC _ _ _ _ _).mpr ((ResU.updV_self_iff ρ).mpr (hash_valid hf).2)

/-- The own-cell step (`updV_compS_own`), as the alloc and free rules read it, where `Upd` is
Core's at every index. -/
theorem updOwn_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdOwn M :=
  ⟨fun _ _ _ _ _ _ _ _ hf _ _ ho hf₁ =>
    (hC _ _ _ _ _).mpr (updV_compS_own ho (hash_valid hf).2 (hash_valid hf₁).2),
   fun _ _ _ _ _ _ _ _ hf₁ _ _ ho =>
    (hC _ _ _ _ _).mpr (updV_compS_own ho (ResU.Valid.split ho (hash_valid hf₁).2).1
      (hash_valid hf₁).2).symm⟩

/-- 6.48 then 6.49, as `wpG_bind`'s last step composes two runs (`Core/EffWp.lean:910-911`),
where `Upd` is Core's at every index. -/
theorem updSeq_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdSeq M := by
  intro i i₁ i₂ ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π hu₁ hc₁ hu₂ hH hc
  have h₁ := (hC _ _ _ _ _).mp hu₁
  have h₂ := (hC _ _ _ _ _).mp hu₂
  have hvπ : ResU.Valid π := by
    obtain ⟨w, hw, hvw⟩ := hH.2
    rwa [ResU.CompS.functional hw hc] at hvw
  have hc₁' : ResU.CompS ρp₁ ρ'₁ π₁ := ResU.CompS.comm hc₁
  exact (hC _ _ _ _ _).mpr (ResU.UpdV.trans h₁
    (updV_frame hc₁' hc ⟨hc₁'.1, _, hc₁', h₁.2.2⟩ ⟨hc.1, _, hc, hvπ⟩ h₂))

/-- `reclaim`, at `theorem32D`'s end, where `Upd` is Core's at every index. -/
theorem updReclaim_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdReclaim M :=
  fun _ π hu hno => reclaim π ((hC _ _ _ _ _).mp hu) hno

/-- 6.48 (`updV_frame`), as `wpG_ramify` reads it, where `Upd` is Core's at every index. -/
theorem updFrame_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdFrame M :=
  fun _ _ _ _ _ _ _ _ _ hu hc hh hπ hhπ _ =>
    (hC _ _ _ _ _).mpr (updV_frame hc hπ hh hhπ ((hC _ _ _ _ _).mp hu))

/-- 6.50 (`updV_outlives`), as `wpTS_box` reads it, where `Upd` is Core's at every index. -/
theorem updOutlives_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdOutlives M :=
  fun _ _ _ _ _ _ ho hu => updV_outlives ho ((hC _ _ _ _ _).mp hu)

/-- 6.27 then 6.28 (`ResU.six27`, `ResU.six28`), as `wpG_M_frameX` reads them, where `Upd` is
Core's at every index. -/
theorem updMutBack_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdMutBack M := by
  intro i i' l α v ρv ρb BM ρ' π h P hw hout hBM hu
  have hu' := (hC _ _ _ _ _).mp hu
  obtain ⟨v', χ, h', hw', hsplit⟩ := ResU.six27 hout hBM hu'
  refine ⟨v', χ, h', hw', hsplit, fun W W' O O' ρ'' hW hW' hO hO' _ hvO hvO' => ?_⟩
  exact (hC _ _ _ _ _).mpr
    ⟨(ResU.six28 hW hW' hBM hsplit hO hO' hu'.2.1 hu'.2.2 hvO hvO').mp hu'.1, hvO, hvO'⟩

/-- 6.29, 6.38 and 6.39 (`ResU.six38_steps_one_two`, `ResU.six38`, `ResU.six39`), as
`wpG_I_frameX` reads them, where `Upd` is Core's at every index. -/
theorem updImmBack_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdImmBack M := by
  intro i i' l α v ρv ρb W BI ρ' ρp π h hW hH hout hout' hpp hno hBI hc hu
  have hu' := (hC _ _ _ _ _).mp hu
  obtain ⟨hGsplit, -, hGc⟩ := ResU.six38_steps_one_two hW hH hpp hout hout' hBI hc hu'
  obtain ⟨G₀, hG₀, hH28⟩ := ResU.six38 hW hH hpp hout hout' hno hBI hc hu'
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  refine ⟨hGc, hH28, fun O O' ρ'' hO hO' _ => ?_⟩
  obtain ⟨w, w', hw, hw', hupd⟩ := ResU.six39 (ResU.CompS.comm hW) hH hH28 hBI hGc hu'
  rw [ResU.CompS.functional hO hw, ResU.CompS.functional hO' hw']
  exact (hC _ _ _ _ _).mpr hupd

/-- The lend comes back, for both frame rules, where `Upd` is Core's at every index. -/
theorem updLendBack_of_core {M : B.BWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdLendBack M :=
  ⟨updMutBack_of_core hC, updImmBack_of_core hC⟩

theorem updRefl_core : UpdRefl (B.coreB (ℍ := ℍ)) := updRefl_of_core coreW_upd

theorem updOwn_core : UpdOwn (B.coreB (ℍ := ℍ)) := updOwn_of_core coreW_upd

theorem updSeq_core : UpdSeq (B.coreB (ℍ := ℍ)) := updSeq_of_core coreW_upd

theorem updReclaim_core : UpdReclaim (B.coreB (ℍ := ℍ)) := updReclaim_of_core coreW_upd

theorem updFrame_core : UpdFrame (B.coreB (ℍ := ℍ)) := updFrame_of_core coreW_upd

theorem updOutlives_core : UpdOutlives (B.coreB (ℍ := ℍ)) := updOutlives_of_core coreW_upd

theorem updLendBack_core : UpdLendBack (B.coreB (ℍ := ℍ)) := updLendBack_of_core coreW_upd

end Targets

end
