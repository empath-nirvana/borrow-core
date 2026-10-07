import Core.EffPrograms
import Targets.B.Guarantees
import Targets.B.Conservativity
import Targets.B.Release

/-!
# System B — the routes among B's guarantees (RESTRUCTURE §2.2, §3.7, §5.3)

Generic: each holds at every borrow world and typing system.  Each instantiates FL at the closed
judgement, the empty instance, the empty lifetime substitution, the nil index and the empty
resource, and hands the result to adequacy.

* `soundnessOfFL`: `FL M J → Adequate M → Soundness J` (B3, B4 from B1, B2);
* `soundContractsOfFL`: `FL M J → Adequate M → SoundContracts J M` (B4′, finding #7: externs carry
  W's contract as a hypothesis, no `Conservative`);
* `soundnessContractsOfFL`: the library's route with Core's contracts, through `ExtPre` and
  `Conservative` (kept as an alternative route);
* `releasedOnceReuse_of_bumpSim`: `BumpSim → SoundContracts J M → ReleasedOnceReuse J M` (B5 from
  B4′, given the step-for-step simulation, which is OPEN: OQ-43);
* `typedSound_of_soundness`, `releasedOnceReuse₀_of`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `SoundnessContracts` at externs of row-abortive type. -/
def SoundnessContractsAR (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    (∀ s ∈ Γ, s.ty.AbortRows) →
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    SafeRuns (ℍ := ℍ) P A (substAll γ e) ∧ Terminates (ℍ := ℍ) P A (substAll γ e)

/-- **Soundness is a corollary of FL and adequacy.** -/
def SoundnessOfFL : Prop :=
  ∀ (M : B.BWorld) (J : TypingJ), FL M J → Adequate (ℍ := ℍ) M → Soundness (ℍ := ℍ) J

/-- **Soundness with externs, from FL** (corrected: `ExtPre` and the every-type embedding). -/
def SoundnessContractsOfFL : Prop :=
  ∀ (M : B.BWorld) (J : TypingJ), FL M J → ExtPre M → Conservative (ℍ := ℍ) M →
    Adequate (ℍ := ℍ) M → SoundnessContracts (ℍ := ℍ) J


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The empty row context admits every environment. -/
theorem models_nil (η : RowEnv) : RowCtx.Models [] η := fun _ _ h => absurd h (by simp)

/-- The empty context at the empty resource, in every world. -/
theorem gDenW_nil (M : B.BWorld) (i : Idx M.Stk) (δ : LSub) : gDenW M i δ [] [] (PMap.empty : WRes) :=
  ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, by simp [Ctx.LiveWithin]⟩, ⟨rfl, trivial⟩⟩

/-- FL at a judgment in a context, at the empty instance. -/
theorem semWC_of_FL {M : B.BWorld} {J : TypingJ} (hFL : FL M J) {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {C : CTy} (h : J.at Δ Γ e (.comp C)) : SemWC M Δ Γ e C :=
  hFL [] Δ (fun _ => Γ) e (fun _ => .comp C) h (fun _ => []) (models_nil _)

/-- FL at a closed program: the program is in W's relation at the nil index, the empty lifetime
substitution and the empty resource. -/
theorem comp_of_FL {M : B.BWorld} {J : TypingJ} (hFL : FL M J) {e : Expr} {C : CTy}
    (h : J.closed e C) : M.comp C ([], M.nil) LSub.empty e (PMap.empty : WRes) := by
  have h₀ := semWC_of_FL hFL h LSub.empty [] ([], M.nil) PMap.empty Adequacy.models_empty
    (gDenW_nil M _ _)
  rwa [show substAll [] e = e from Adequacy.psub_nil 0 e] at h₀

/-- The return conjunct of T1 at one platform, from FL and adequacy there. -/
theorem soundRetAt_of_FL {M : B.BWorld} {J : TypingJ} {P : Platform} (hFL : FL M J)
    (hA : AdequateRetAt (ℍ := ℍ) M P) : SoundRetAt (ℍ := ℍ) J P :=
  fun S A e hd hle h => hA S A e hd hle (comp_of_FL hFL h)

/-- The drive conjunct of T1 at one platform, from FL and adequacy there. -/
theorem soundDriveAt_of_FL {M : B.BWorld} {J : TypingJ} {P : Platform} (hFL : FL M J)
    (hA : AdequateDriveAt (ℍ := ℍ) M P) : SoundDriveAt (ℍ := ℍ) J P :=
  fun S A B e hd hle hC h => hA S A B e hd hle hC (comp_of_FL hFL h)

/-- **`SoundnessOfFL`**, generic. -/
theorem soundnessOfFL : SoundnessOfFL (ℍ := ℍ) :=
  fun _ _ hFL hAd P hP => ⟨soundRetAt_of_FL hFL (hAd P hP).1, soundDriveAt_of_FL hFL (hAd P hP).2⟩

/-- Externs that meet Core's contracts, at types W's relation embeds, are in W's context relation
at the nil index and the empty resource. -/
theorem gDenW_of_meets {M : B.BWorld} {Γ : Ctx VTy} {γ : List Val}
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


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free')

/-- T1 gives `TypedSound` at a program closed at a data answer. -/
theorem typedSound_of_soundness {J : TypingJ} {e : Expr} {A : VTy}
    (hS : Soundness (ℍ := ℍ) J) (hA : A.Data) (h : J.closed e (.ret A)) :
    TypedSound (ℍ := ℍ) J e A :=
  ⟨h, fun P hP => (hS P hP).1 [] A e hA (fun _ _ _ h => by simp [Row.find] at h) h⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **B4′ from FL and adequacy** (finding #7): with externs carrying W's contract as an explicit
hypothesis, soundness with externs is a corollary of B1 and B2 alone.  `soundnessContractsOfFL`'s
proof without `Conservative`. -/
theorem soundContractsOfFL {M : B.BWorld} {J : TypingJ} (hFL : FL M J) (hAd : Adequate (ℍ := ℍ) M) :
    B.SoundContracts (ℍ := ℍ) J M :=
  fun P hP _ γ S A e hd hle h hγ =>
    (hAd P hP).1 S A (substAll γ e) hd hle
      (semWC_of_FL hFL h LSub.empty γ ([], M.nil) PMap.empty Adequacy.models_empty hγ)

/-- The contract at no extern holds at every world. -/
theorem contractsW_nil (M : B.BWorld) : B.ContractsW M [] [] := gDenW_nil M _ _

/-- B5 gives B5 at closed programs, which reads no world. -/
theorem releasedOnceReuse₀_of {J : TypingJ} {M : B.BWorld} (h : B.ReleasedOnceReuse (ℍ := ℍ) J M) :
    B.ReleasedOnceReuse₀ (ℍ := ℍ) J := by
  intro P hP S A e hd hle hJ cs hrun hfin
  have h₀ := h P hP [] [] S A e hd hle hJ (contractsW_nil M)
  rw [show substAll [] e = e from Adequacy.psub_nil 0 e] at h₀
  exact h₀ cs hrun hfin

/-- **B5 from B4′, given the step-for-step simulation** (RESTRUCTURE §2.4).  B4′'s `SafeRuns` holds
under every allocator, the bump allocator's among them, so the bump run from the same start is never
stuck where the given run steps; `BumpSim` makes its step the given step's preimage, so it follows
the given run to its end (`bump_follows`); it reuses nothing, so it releases each cell once
(`releasedOnce_of_ends`). -/
theorem releasedOnceReuse_of_bumpSim (hS : BumpSim (ℍ := ℍ)) {J : TypingJ} {M : B.BWorld}
    (hC : B.SoundContracts (ℍ := ℍ) J M) : B.ReleasedOnceReuse (ℍ := ℍ) J M := by
  intro P hP Γ γ S A e hD hle hJ hW cs hrun hF
  have hsafe := (hC P hP Γ γ S A e hD hle hJ hW).1
  obtain ⟨cs', gs, hlen, hrun', hbump, hF', hrel⟩ :=
    bump_follows hS hsafe cs _ _ id (locsOf (substAll γ e)).toFinset hrun hF (relAt_init _)
      (fun _ _ _ _ _ => rfl) .refl ⟨[], fun _ h => absurd rfl h⟩
      (fun _ hn => List.mem_toFinset.mpr (named_init hn))
  have hB : Bump (init P (substAll γ e) :: cs') := fun k ℓ hA => (hbump k ℓ hA).2
  exact ⟨cs', gs, hlen, hrun', hB,
    releasedOnce_of_ends (init_vacant _ cs') (final_vacant hF') (noReuse_of_bump hB), hF', hrel⟩


end Targets

end
