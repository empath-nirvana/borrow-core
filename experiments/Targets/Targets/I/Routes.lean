import Targets.I.Device
import Targets.B.Routes

/-!
# The interaction — the routes that read the interaction's world (RESTRUCTURE §3.7)

* `EffSafeOfFL`: `FL M J → FamEmpty M ∧ AdequateEvery M → EffSafe J` (the empty configuration and
  adequacy from every index; no `Mono`, which done does not hold);
* `EffSafeDriveOfFL`: the same for driven programs (stated, OPEN at a generic world; at Core's
  world it holds, `effSafeDrive_of_FL`);
* `SoundnessContractsOfFLWB`: FL, `EmbedsNil` and adequacy give the SPEC's row-abortive externs at
  Core's contract (the route reads only the nil index); `contractsW_of_meets`: through `EmbedsNil`,
  Core's contract gives W's at row-abortive types;
* `AdequateOfLaws` (stated, OPEN; its hypotheses `WLaws`, `ShareResume`, `UpdSeq`, `UpdReclaim`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Soundness with externs of row-abortive type, from FL** (the design's route), through `EmbedsNil`. -/
def SoundnessContractsOfFLWB : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → EmbedsNil (ℍ := ℍ) M →
    Adequate (ℍ := ℍ) M → SoundnessContractsAR (ℍ := ℍ) J

/-- **Effect safety from FL**, the empty configuration and adequacy from every index (over `FamEmpty ∧ AdequateEvery`, review [17]). -/
def EffSafeOfFL : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → FamEmpty M ∧ AdequateEvery (ℍ := ℍ) M → EffSafe (ℍ := ℍ) J

/-- **Effect safety of driven programs from FL** (TIER1-PLAN §3's route), over the empty
configuration and adequacy from every index.  OPEN at a generic world; at Core's world it holds
(`effSafeDrive_of_FL`), at the positive loop bodies `EffSafeDrive` asks (decision D2). -/
def EffSafeDriveOfFL : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → FamEmpty M → AdequateEvery (ℍ := ℍ) M →
    EffSafeDrive (ℍ := ℍ) J

/-- **Adequacy from the laws** (second wave), with the run-end relation's sequencing and reclaim
laws. -/
def AdequateOfLaws : Prop :=
  ∀ M : SemWorld, WLaws (ℍ := ℍ) M → ShareResume M → UpdSeq M → UpdReclaim M →
    Adequate (ℍ := ℍ) M


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`SoundnessContractsOfFLWB`**: the design's route, at externs of row-abortive type. -/
theorem soundnessContractsOfFLWB : SoundnessContractsOfFLWB (ℍ := ℍ) := by
  intro M J hFL hEmb hAd P hP Γ γ S A e hAR hd hle h hγ
  have hg := gDenW_of_meets (fun s hs v hv => hEmb true s.ty [] LSub.empty v PMap.empty
    (hAR s hs) (hv [] LSub.empty)) hγ
  exact (hAd P hP).1 S A (substAll γ e) hd hle
    (semWC_of_FL hFL h LSub.empty γ ([], M.nil) PMap.empty Adequacy.models_empty hg)

/-- **Core's extern contract gives W's at row-abortive types**, through the device's `EmbedsNil`
(the `→` direction only). -/
theorem contractsW_of_meets {M : SemWorld} (hE : EmbedsNil (ℍ := ℍ) M) {Γ : Ctx VTy} {γ : List Val}
    (hAR : ∀ s ∈ Γ, s.ty.AbortRows) (hγ : ExternsMeet (ℍ := ℍ) Γ γ) : B.ContractsW M.toBWorld Γ γ :=
  gDenW_of_meets (fun s hs v hv => hE true s.ty [] LSub.empty v PMap.empty (hAR s hs)
    (hv [] LSub.empty)) hγ

/-- **`EffSafeOfFL`**, generic: `AdequateEvery` at the empty configuration `FamEmpty`. -/
theorem effSafeOfFL : EffSafeOfFL (ℍ := ℍ) := by
  intro M J hFL hW e S A hNU h μ' e' hs
  have hc := comp_of_FL hFL h
  obtain ⟨hFam, hAE⟩ := hW
  obtain ⟨μ₂, e₂, hs₂, hve⟩ := hAE ([], M.nil) PMap.empty PMap.empty PMap.empty [] Adequacy.emptyMem
    S A LSub.empty e hNU hFam Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
    Fig16.BoLo.lower_empty hc μ' e' hs
  cases hs₂ with
  | refl => exact hve.elim Or.inl (fun h => Or.inr (Or.inr h))
  | more h _ => exact Or.inr (Or.inl ⟨_, _, h⟩)

end Targets

end
