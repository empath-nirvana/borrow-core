import WorldW.Between
import WorldW.HandOn

/-!
# WorldW — non-vacuity of the proved negative statements (DESIGN §3.5, partly)

**World: resources and lifetimes.** `reentryInheritA`, `reentryFreshA`, `resumeOutOfOrder` and
`argBelowExtent` conclude a negation. Each instance below discharges the premises at one concrete
configuration, so none of them holds vacuously. The configuration is the first stop's share of
the between-lenders program read at the resource level: `κ`'s share is `e₂`'s view
`ℓ₂ ↦ imm({α₂}, (), ∅)`, `L₃`'s callback resource is that share, with `α₃ ⊏ α₂ ⊏ h`.

These are resource-level instances. They are not built from a `TW` history of the
between-lenders program (DESIGN §5); that history is not in this experiment.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The lifetimes: `h = 0`, `α₂ = 1`, `α₃ = 2` in `ℕᵒᵈ`, so `α₃ ⊏ α₂ ⊏ h`. -/
abbrev iH : Life := OrderDual.toDual 0
abbrev iα₂ : Life := OrderDual.toDual 1
abbrev iα₃ : Life := OrderDual.toDual 2
abbrev iH' : Life := OrderDual.toDual 3

theorem iα₂_hR : ResU.InStratum (LSet.singleton iα₂).join (PMap.empty : WRes) :=
  ResU.inStratum_empty _

/-- `e₂`'s record: `ℓ₂ = 0`, value `()`, payload `∅`, type `1`. -/
def ip₂ : FrameRec := ⟨0, Val.unit, PMap.empty, .unit, ⟨[]⟩⟩

/-- `e₂`'s view, `κ`'s share at the first stop. -/
def iView : WRes :=
  ResU.single ip₂.le (CellU.immOf (LSet.singleton iα₂) ip₂.v ip₂.R iα₂_hR)

/-- The view's closure: the owned place. -/
def iOwned : WRes := ResU.single ip₂.le (CellU.ownOf ip₂.v)

theorem iView_close : Close [.imm (ip₂, iα₂)] iView iOwned := by
  refine close_imm_iff.mpr ⟨iα₂_hR, iOwned, ResU.single_get_self _ _,
    ResU.comp_empty_right _, ?_, ResU.valid_single_own _ _⟩
  rw [show iView.del ip₂.le = PMap.empty from single_del_self _ _]
  exact compS_empty_left _

theorem iView_holds : Holds [.imm (ip₂, iα₂)] iView := ⟨iOwned, iView_close⟩

theorem iView_inStratum : iView.InStratum iα₃ := by
  intro k ψ e
  by_cases hk : k = ip₂.le
  · subst hk; rw [iView, ResU.single_get_self] at e; cases Option.some.inj e
    show iα₃ < iα₂; decide
  · rw [iView, single_get_none _ hk] at e; exact absurd e (by simp)

/-- Every closure of the view is the owned place, which lies in every stratum. -/
theorem iView_closures_inStratum (α : Life) :
    ∀ ρc, Close [.imm (ip₂, iα₂)] iView ρc → ρc.InStratum α := by
  intro ρc hρc
  obtain ⟨-, X, -, hX, hc, -⟩ := close_imm_iff.mp hρc
  rw [show iView.del ip₂.le = PMap.empty from single_del_self _ _] at hc
  have e₁ : ρc = X := eq_of_compS_empty_left hc
  have e₂ : X = iOwned := ResU.CompS.functional hX (ResU.comp_empty_right _)
  rw [e₁, e₂]
  exact ResU.inStratum_single_own α _ _

/-- **`ReentryInheritA` and `ResumeOutOfOrder` are not vacuous**: their premises hold at the first
stop's share. -/
theorem reentryInheritA_premises :
    Holds [.imm (ip₂, iα₂)] iView ∧ ResU.Le iView iView ∧ iView.InStratum iα₃ ∧ iα₂ ⊏ iH :=
  ⟨iView_holds, ResU.Le.refl _, iView_inStratum, by decide⟩

/-- **`ReentryFreshA` is not vacuous**: its premises hold, with the fresh extent `h′ = 3` below
`α₃` and the re-entry obligation met at the share. -/
theorem reentryFreshA_premises (ℓ₃ : BoCa.Loc) (S₃ : VTy) (δ : LSub) :
    Holds [.imm (ip₂, iα₂)] iView ∧ ResU.Le iView iView ∧ iView.InStratum iα₃ ∧
      ExtentOK iH' [.imm (ip₂, iα₂)] [.mut ℓ₃ iα₃ S₃ δ] [] iView := by
  refine ⟨iView_holds, ResU.Le.refl _, iView_inStratum,
    ⟨iView_closures_inStratum iH', fun x hx => absurd hx List.not_mem_nil⟩, ?_⟩
  intro e he β hβ
  rw [List.mem_singleton] at he
  subst he
  simp only [OEnt.ordLife?, OEnt.life?, Option.some.injEq] at hβ
  subst hβ
  show iH' < iα₃; decide

/-- **`ArgBelowExtent` is not vacuous**: its premises hold with the argument a copy of the view. -/
theorem argBelowExtent_premises :
    iα₂ ⊏ iH ∧ Holds [.imm (ip₂, iα₂)] iView ∧
    (∀ ρc, Close [.imm (ip₂, iα₂)] iView ρc → ρc.InStratum iH) ∧
    ∃ ρ, ResU.CompS iView iView ρ :=
  ⟨by decide, iView_holds, iView_closures_inStratum iH,
    ⟨_, ResU.compS_single_imm ip₂.le _ _ ip₂.v ip₂.R iα₂_hR iα₂_hR
      (ResU.InStratum.sup iα₂_hR iα₂_hR)⟩⟩

end WorldW

end
