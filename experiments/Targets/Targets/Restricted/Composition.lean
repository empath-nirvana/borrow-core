import Targets.Statements.Composition

/-!
# Targets — the generic composition lemmas, proved (DESIGN §4.1, §9 item 4)

For every world `M` and typing system `J`:

* `soundnessOfFL`: `FL M J → Adequate M → Soundness J`;
* `soundnessContractsOfFL`: `FL M J → ExtPre M → Conservative M → Adequate M →
  SoundnessContracts J` (the corrected form, DESIGN §Corrections C2);
* `soundnessContractsOfFLWB`: the design's route, at externs of row-abortive type;
* `effSafeOfFL`: `FL M J → WLaws M → EffSafe J`.

Each instantiates FL at the closed judgment, the empty instance, the empty lifetime substitution,
the nil index and the empty resource, and hands the result to adequacy.  Generic.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The empty row context admits every environment. -/
theorem models_nil (η : RowEnv) : RowCtx.Models [] η := fun _ _ h => absurd h (by simp)

/-- The empty context at the empty resource, in every world. -/
theorem gDenW_nil (M : SemWorld) (i : Idx M.Stk) (δ : LSub) : gDenW M i δ [] [] (PMap.empty : WRes) :=
  ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, by simp [Ctx.LiveWithin]⟩, ⟨rfl, trivial⟩⟩

/-- FL at a judgment in a context, at the empty instance. -/
theorem semWC_of_FL {M : SemWorld} {J : TypingJ} (hFL : FL M J) {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {C : CTy} (h : J.at Δ Γ e (.comp C)) : SemWC M Δ Γ e C :=
  hFL [] Δ (fun _ => Γ) e (fun _ => .comp C) h (fun _ => []) (models_nil _)

/-- FL at a closed program: the program is in W's relation at the nil index, the empty lifetime
substitution and the empty resource. -/
theorem comp_of_FL {M : SemWorld} {J : TypingJ} (hFL : FL M J) {e : Expr} {C : CTy}
    (h : J.closed e C) : M.comp C ([], M.nil) LSub.empty e (PMap.empty : WRes) := by
  have h₀ := semWC_of_FL hFL h LSub.empty [] ([], M.nil) PMap.empty Adequacy.models_empty
    (gDenW_nil M _ _)
  rwa [show substAll [] e = e from Adequacy.psub_nil 0 e] at h₀

/-- The return conjunct of T1 at one platform, from FL and adequacy there. -/
theorem soundRetAt_of_FL {M : SemWorld} {J : TypingJ} {P : Platform} (hFL : FL M J)
    (hA : AdequateRetAt (ℍ := ℍ) M P) : SoundRetAt (ℍ := ℍ) J P :=
  fun S A e hd hle h => hA S A e hd hle (comp_of_FL hFL h)

/-- The drive conjunct of T1 at one platform, from FL and adequacy there. -/
theorem soundDriveAt_of_FL {M : SemWorld} {J : TypingJ} {P : Platform} (hFL : FL M J)
    (hA : AdequateDriveAt (ℍ := ℍ) M P) : SoundDriveAt (ℍ := ℍ) J P :=
  fun S A B e hd hle h => hA S A B e hd hle (comp_of_FL hFL h)

/-- **`SoundnessOfFL`**, generic. -/
theorem soundnessOfFL : SoundnessOfFL (ℍ := ℍ) :=
  fun _ _ hFL hAd P hP => ⟨soundRetAt_of_FL hFL (hAd P hP).1, soundDriveAt_of_FL hFL (hAd P hP).2⟩

/-- Externs that meet Core's contracts, at types W's relation embeds, are in W's context relation
at the nil index and the empty resource. -/
theorem gDenW_of_meets {M : SemWorld} {Γ : Ctx VTy} {γ : List Val}
    (hT : ∀ s ∈ Γ, ∀ v, (∀ ls δ, vCE (ℍ := ℍ) none true s.ty ls δ v PMap.empty) →
      M.val true s.ty ([], M.nil) LSub.empty v PMap.empty)
    (h : ExternsMeet (ℍ := ℍ) Γ γ) : gDenW M ([], M.nil) LSub.empty Γ γ (PMap.empty : WRes) := by
  refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, ?_⟩, ?_⟩
  · clear hT
    induction h with
    | nil => trivial
    | cons _ _ _ ih => exact ih
  · induction h with
    | nil => exact ⟨rfl, trivial⟩
    | cons _ hv _ ih =>
        refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
          hT _ List.mem_cons_self _ hv, ih fun s hs => hT s (List.mem_cons_of_mem _ hs)⟩

/-- **`SoundnessContractsOfFL`** (corrected), generic. -/
theorem soundnessContractsOfFL : SoundnessContractsOfFL (ℍ := ℍ) := by
  intro M J hFL hExt hCons hAd P hP Γ γ S A e hd hle h hγ
  have hg := gDenW_of_meets (fun s _ v hv => hCons true s.ty [] LSub.empty v PMap.empty
    (hv [] LSub.empty) ([], M.nil) (hExt.1 _ _)) hγ
  exact (hAd P hP).1 S A (substAll γ e) hd hle
    (semWC_of_FL hFL h LSub.empty γ ([], M.nil) PMap.empty Adequacy.models_empty hg)

/-- **`SoundnessContractsOfFLWB`**: the design's route, at externs of row-abortive type. -/
theorem soundnessContractsOfFLWB : SoundnessContractsOfFLWB (ℍ := ℍ) := by
  intro M J hFL hExt hCons hAd P hP Γ γ S A e hAR hd hle h hγ
  have hg := gDenW_of_meets (fun s hs v hv => hCons true s.ty [] LSub.empty v PMap.empty
    (hAR s hs) (hv [] LSub.empty) ([], M.nil) (hExt.1 _ _)) hγ
  exact (hAd P hP).1 S A (substAll γ e) hd hle
    (semWC_of_FL hFL h LSub.empty γ ([], M.nil) PMap.empty Adequacy.models_empty hg)

/-- **`EffSafeOfFL`**, generic: `AdequateEvery` at the empty configuration. -/
theorem effSafeOfFL : EffSafeOfFL (ℍ := ℍ) := by
  intro M J hFL hW e S A hNU h μ' e' hs
  have hc := comp_of_FL hFL h
  obtain ⟨-, -, -, -, hFam, -, -, -, hAE⟩ := hW
  obtain ⟨μ₂, e₂, hs₂, hve⟩ := hAE ([], M.nil) PMap.empty PMap.empty PMap.empty [] Adequacy.emptyMem
    S A LSub.empty e hNU hFam Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
    Fig16.BoLo.lower_empty hc μ' e' hs
  cases hs₂ with
  | refl => exact hve.elim Or.inl (fun h => Or.inr (Or.inr h))
  | more h _ => exact Or.inr (Or.inl ⟨_, _, h⟩)

end Targets

end
