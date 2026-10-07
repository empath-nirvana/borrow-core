import Core.Totality
import Targets.B.Routes
import Targets.B.RunEnd
import Targets.B.Conservativity
import Targets.Base.Data

/-!
# System B — BoLo's guarantees at BoLo, by citation (RESTRUCTURE §2.2)

"Given" means at `coreB` and `tier1`, at the restrictions listed in `Targets/Status.lean`.  Each
holds by citing `Core` and `Paper`; none is re-proved.

* B1: `fl_core_tier1`, `fl_core_tier1NU` (`fundamentalC`, `Core/Fundamental.lean:434`; [TR] 6.151).
* B2: `adequateRetAt_core_none` (`theorem32D`; the platform with no operation, data answers).
* B3, B4: `soundRetAt_tier1_none`, from B1 and B2 (`adequacyD_safe`, `reclaim`).
* B6: `exclusiveB_core` (`TW.valid`).  B7: `lifetimeSound_core` (`vC_outlives`, `vC_outlivesLe`;
  [TR] 6.60).  B0: `extendsB_tier1`.  The bounds: `wBound_core`.
* P14: `wbCore` (a companion lemma), `conservative_core`, `conservativeWB_core` (`vC_local`).

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem extPre_core : ExtPre (B.coreB (ℍ := ℍ)) :=
  ⟨fun i ρ => Ext.refl i.1 ρ, fun _ _ _ _ h₁ h₂ => Ext.trans h₁ h₂⟩

theorem famEmpty_core : FamEmpty (B.coreB (ℍ := ℍ)) :=
  ⟨TW.empty, fun _ hx => absurd hx (by simp)⟩

theorem dataVals_core : DataVals (B.coreB (ℍ := ℍ)) :=
  fun _ _ _ _ _ _ hA => vC_data hA

theorem relElim_core : RelElim (B.coreB (ℍ := ℍ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C i δ v ρ h
    exact h i.1 (Ext.refl i.1 ρ)
  · intro A C i δ e ρ h
    exact h
  · intro C D i δ e ρ h
    exact h
  · intro x b C i δ e ρ h α hα
    exact h α PMap.empty ρ ⟨rfl, hα⟩ (ResU.comp_empty_right ρ)
  · intro C i δ e ρ hC h
    exact (cC_nu_iff hC i.1 δ e ρ).mp h
  · intro b A i δ v ρ h
    exact (vC_unfold h).2.2

theorem relShape_core : RelShape (B.coreB (ℍ := ℍ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b i δ v ρ h
    exact h
  · intro b A B i δ v ρ h
    obtain ⟨v₁, v₂, h⟩ := h
    obtain ⟨hv, h⟩ := pure_sep_iff.mp h
    exact ⟨v₁, v₂, hv, h⟩
  · intro b A B i δ v ρ h
    rcases h with ⟨w, h⟩ | ⟨w, h⟩
    · obtain ⟨hv, h⟩ := pure_sep_iff.mp h
      exact Or.inl ⟨w, hv, h⟩
    · obtain ⟨hv, h⟩ := pure_sep_iff.mp h
      exact Or.inr ⟨w, hv, h⟩
  · intro b A i δ v ρ h
    obtain ⟨ℓ, v', h⟩ := h
    obtain ⟨hv, h⟩ := pure_sep_iff.mp h
    exact ⟨ℓ, v', hv, h⟩
  · intro b A i δ v ρ h
    exact h
  · intro b a A i δ v ρ h
    exact h
  · intro b a A i δ v ρ h
    rcases i with ⟨ls, ⟨⟩⟩
    exact h
  · intro b a A i δ v ρ h
    rcases i with ⟨ls, ⟨⟩⟩
    obtain ⟨α, hα, ℓ, h⟩ := h
    obtain ⟨hv, hp⟩ := pure_sep_iff.mp h
    refine ⟨α, hα, ℓ, pure_sep_mk hv ?_⟩
    have e := ptoMutSW_core (ℍ := ℍ) ℓ α ls (fun ls₀ => vCE none true A ls₀ δ)
    exact e ▸ hp
  · intro b L i δ v ρ h
    obtain ⟨ℓ, c, h⟩ := h
    obtain ⟨⟨hv, hc⟩, hs⟩ := pure_sep_iff.mp h
    exact ⟨ℓ, c, hv, hc, hs⟩
  · intro b i δ v ρ h
    exact h.1
  · intro b w i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b k i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b n i δ v ρ h
    exact h

theorem relLaws_core : RelLaws (B.coreB (ℍ := ℍ)) := ⟨relElim_core, relShape_core⟩

/-- **`FL B.coreB tier1`**: `fundamentalC` at every admissible instance. -/
theorem fl_core_tier1 : FL (B.coreB (ℍ := ℍ)) tier1 :=
  fun _ _ _ _ _ h η hη => semW₀_core.mpr (fundamentalC (h η hη))

/-- `FL B.coreB tier1NU`: the unr-free fragment, through `CDerivesNU.toCDerives`. -/
theorem fl_core_tier1NU : FL (B.coreB (ℍ := ℍ)) tier1NU :=
  fun _ _ _ _ _ h η hη => semW₀_core.mpr (fundamentalC (h η hη).toCDerives)

theorem lifetimeSound_core : LifetimeSound (B.coreB (ℍ := ℍ)) OutJ.core :=
  ⟨fun _ _ _ _ _ b i v ρ hδ ha hT h => vC_outlives hδ ha hT b i.1 v ρ h,
   fun _ _ _ _ _ b i v ρ hδ ha hT h => vC_outlivesLe hδ ha hT b i.1 v ρ h⟩

theorem wbCore : WBCore (ℍ := ℍ) := by
  intro ls e Q ρ h ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hT',
    htg', hps, hls, hQ⟩ := h ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hT',
    htg', hps, hls, hQ, hls⟩

theorem conservative_core : Conservative (ℍ := ℍ) (B.coreB (ℍ := ℍ)) :=
  fun b A _ _ _ _ h _ he => vC_local b A he h

theorem conservativeWB_core : ConservativeWB (ℍ := ℍ) (B.coreB (ℍ := ℍ)) :=
  fun b A _ _ _ _ _ h _ he => vC_local b A he h


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `total_every_alloc` at `wpTS` at the empty world: under every allocator, from every allocation
count, the run from the empty memory reaches a value. -/
theorem every_alloc_of_wpTS {e : Expr} {Q : List SRec → Val → WProp}
    (hwp : wpTS (ℍ := ℍ) [] e Q (PMap.empty : WRes)) (Al : Alloc) (k : Nat) :
    ∃ (k' : Nat) (μ' : Heap) (v : Val), ARun (ℍ := ℍ) Al k Adequacy.emptyMem e k' μ' (.val v) := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨-, -, -, -, -, v, μ, μ', -, -, -, -, -, h4, -, -, ⟨k', hrun⟩, -⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Al k
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h4 Fig16.BoLo.lower_empty
  exact ⟨k', μ', v, hrun⟩

/-- `total_no_infinite_run` at `wpTS` at the empty world. -/
theorem no_infinite_of_wpTS {e : Expr} {Q : List SRec → Val → WProp}
    (hwp : wpTS (ℍ := ℍ) [] e Q (PMap.empty : WRes)) :
    ¬ ∃ f : ℕ → Heap × Expr, f 0 = (Adequacy.emptyMem, e) ∧
      ∀ n, Step1 (ℍ := ℍ) (f n).1 (f n).2 (f (n + 1)).1 (f (n + 1)).2 := by
  rintro ⟨f, h0, hf⟩
  obtain ⟨_, _, _, hv⟩ :=
    every_alloc_of_wpTS hwp (BoCa.Fig16.LogRel.Core.Alloc.ofRun (ℍ := ℍ) hf) 0
  refine BoCa.Fig16.LogRel.Core.ARun.no_infinite hv
    (fun n => ((InfRun.cnt hf n), (f n).1, (f n).2)) ?_ ?_
  · simp [InfRun.cnt, countTrue, h0]
  · intro n
    exact InfRun.astep hf n

/-- A row the empty platform answers is empty. -/
theorem row_nil_of_le {S : Row} (h : RowLe S Platform.none.ops) : S = [] := by
  cases S with
  | nil => rfl
  | cons o S =>
      exfalso
      have hf : Row.find (o :: S) o.n o.i = some o := by simp [Row.find]
      have := h o.n o.i o hf
      simp [Platform.none, Row.find] at this

/-- A step under the empty platform is a machine step. -/
theorem pstep_none {c c' : Conf Platform.none} (h : PStep (ℍ := ℍ) Platform.none c c') :
    Step1 (ℍ := ℍ) c.μ c.e c'.μ c'.e := by
  cases h with
  | mach h => exact h
  | plat _ ho _ => simp [Platform.none, Row.find] at ho

theorem psteps_none {c c' : Conf Platform.none} (h : PSteps (ℍ := ℍ) Platform.none c c') :
    Steps (ℍ := ℍ) c.μ c.e c'.μ c'.e := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hs ih => exact ih.trans (.one (pstep_none hs))

/-- **`AdequateRetAt B.coreB Platform.none`.** -/
theorem adequateRetAt_core_none : AdequateRetAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) Platform.none := by
  intro S A e hd hle h
  obtain rfl := row_nil_of_le hle
  have hwp : wpTS (ℍ := ℍ) [] e (fun _ v => Fig16.BoLo.pure (DataVal A v)) (PMap.empty : WRes) :=
    wpTS_mono (fun _ _ _ hv => by
      obtain ⟨rfl, hD⟩ := (vC_data hd).mp hv
      exact ⟨rfl, hD⟩) _ h
  have hrun : ∀ c, PSteps (ℍ := ℍ) Platform.none (init Platform.none e) c →
      ∃ v, Steps (ℍ := ℍ) c.μ c.e Adequacy.emptyMem (.val v) ∧ DataVal A v :=
    fun c hc => theorem32D e _ hwp (psteps_none hc)
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_⟩
  · obtain ⟨v, hs, hD⟩ := hrun c hc
    rcases c with ⟨μc, ec, sc⟩
    cases hs with
    | refl => exact Or.inl ⟨v, rfl, hD, rfl⟩
    | more h _ => exact Or.inr ⟨⟨_, _, sc⟩, .mach h⟩
  · obtain ⟨v, hs, hD⟩ := hrun c hc
    exact ⟨⟨Adequacy.emptyMem, .val v, c.s⟩, psteps_of_steps Platform.none c.s hs, v, rfl, hD, rfl⟩
  · rintro ⟨f, h0, hf⟩
    refine no_infinite_of_wpTS hwp ⟨fun n => ((f n).μ, (f n).e),
      by show ((f 0).μ, (f 0).e) = _; rw [h0]; rfl, fun n => pstep_none (hf n)⟩

/-- **`SoundRetAt tier1 Platform.none`**: T1's return conjunct for Core's typing, at the platform
with no operation.  PROVED AT A RESTRICTION. -/
theorem soundRetAt_tier1_none : SoundRetAt (ℍ := ℍ) tier1 Platform.none :=
  soundRetAt_of_FL fl_core_tier1 adequateRetAt_core_none


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **B6 at BoLo** (from `TW.valid`): `coreB.Fam` is `TW ∧ Tagged`. -/
theorem exclusiveB_core : B.ExclusiveB (B.coreB (ℍ := ℍ)) := fun _ _ _ h => TW.valid h.1

/-- `coreB`'s nil slice is Core's, by unfolding. -/
theorem sliceShapeB_core : B.SliceShapeB (B.coreB (ℍ := ℍ)) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl, fun _ => rfl⟩

/-- **The bounds at BoLo.** -/
theorem wBound_core : B.WBound (B.coreB (ℍ := ℍ)) :=
  ⟨sliceShapeB_core, extPre_core, famEmpty_core, dataVals_core, relShape_core, relElim_core⟩

/-- **B0 at BoLo**: a projection of `extendsNU_tier1`. -/
theorem extendsB_tier1 : B.ExtendsB tier1 :=
  ⟨extendsNU_tier1.1, B.borrowRulesClosed_of_rulesClosed extendsNU_tier1.2⟩


end Targets

end
