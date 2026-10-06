import Targets.Restricted.EffectSafety
import Targets.Restricted.Interface

/-!
# Targets — the reduction laws, and P11 at Core σ=[] (DESIGN §6 P11)

`RedLaws M`: a pure head step `a ↦ a'` that allocates nothing, plugged into a context, neither adds
nor loses anything at `ewpW` under an operation table.  Backward is `ewpW_step`.  Forward: a run
from `K[a]` that ends at a value or at a stop the table allows takes at least one step, since
`K[a]` is neither (`no_step_val`, `opPlug_no_step`); under one allocator the machine is
deterministic (`AStep1.deterministic`), so that step is `K[a] ↦ K[a']` at the same count and
memory, and the rest of the run is one from `K[a']` (`arun_first`).

* `redLaws_of_mono`: generic, at every world whose operation tables are monotone in what they owe.
  PROVED (generic).
* `redLaws_core : RedLaws coreW`, `p11_core : P11 coreW`.  PROVED AT σ=[].
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 Step1N performE raiseE opPayload)

/-- A pure head step that allocates nothing is the first step of every run from its plugged redex
that does not end there. -/
theorem arun_first {A : Alloc} {k k' : Nat} {μ μ' : Heap} {K : Kont} {a a' t : Expr}
    (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false)
    (hr : ARun (ℍ := ℍ) A k μ (K.plug a) k' μ' t) (hne : t ≠ K.plug a) :
    ARun (ℍ := ℍ) A k μ (K.plug a') k' μ' t := by
  cases hr with
  | refl => exact absurd rfl hne
  | more s r =>
      have s₀ : AStep1 (ℍ := ℍ) A k μ (K.plug a) k μ (K.plug a') :=
        (Step1N.plug K (Step1N.head (hh μ) hn)).toAStep1 A k
      obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s₀
      exact r

/-- `wpGW` sheds the step `K[a] ↦ K[a']` when its postcondition rejects `K[a]`. -/
theorem wpGW_strip {M : SemWorld} {K : Kont} {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (hn : a.allocs = false) {i : Idx M.Stk} {Q : Idx M.Stk → Expr → WProp}
    (hQ : ∀ i' ρ', ¬ Q i' (K.plug a) ρ') {ρ : WRes} (h : wpGW (ℍ := ℍ) M i (K.plug a) Q ρ) :
    wpGW (ℍ := ℍ) M i (K.plug a') Q ρ := by
  intro ρf fρ ps h₁ h₂ h₃ A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆, ⟨k', hr⟩, a₈, a₉, a₁₀,
    a₁₁, a₁₂, a₁₃⟩ := h ρf fρ ps h₁ h₂ h₃ A k
  refine ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆,
    ⟨k', arun_first hh hn hr ?_⟩, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩
  rintro rfl
  exact hQ _ _ a₁₃

/-- A plugged redex is neither a value nor a stop of an operation table. -/
theorem plug_not_post {M : SemWorld} {K : Kont} {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (T : OpTabI (Idx M.Stk)) (Q : Idx M.Stk → Val → WProp) (P : Idx M.Stk → Expr → WProp)
    (i' : Idx M.Stk) (ρ' : WRes) :
    ¬ (valPostI Q i' (K.plug a) ρ' ∨ opTabW M T i' (K.plug a) P ρ') := by
  have hs : Step1 (ℍ := ℍ) (fun _ => none) (K.plug a) (fun _ => none) (K.plug a') :=
    ⟨K, a, a', rfl, rfl, hh _⟩
  rintro (⟨v, hv, -⟩ | ⟨K', n, j, v, en, hp⟩ | ⟨K', n, j, v, en, hp⟩)
  · rw [hv] at hs; exact BoCa.BoLo.no_step_val hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := false) (payloadName_opPayload n j v) hK hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := true) (payloadName_opPayload n j v) hK hs

/-- **`RedLaws`** at every world whose operation tables are monotone in what they owe. -/
theorem redLaws_of_mono {M : SemWorld} (hM : ∀ T, TableI.Mono (opTabW M T)) :
    RedLaws (ℍ := ℍ) M := by
  intro K a a' i T Q ρ hh hn
  constructor
  · intro h
    exact ewpW_fold (hM T) (wpGW_strip hh hn (fun i' ρ' => plug_not_post hh T Q _ i' ρ')
      (ewpW_unfold (hM T) h))
  · exact ewpW_step (hM T) (fun μ => Step1N.plug K (Step1N.head (hh μ) hn)) i Q ρ

/-- Core's operation tables are monotone in what they owe (`opTable_mono`). -/
theorem opTabW_mono_core (T : OpTabI (Idx Unit)) : TableI.Mono (opTabW (coreW (ℍ := ℍ)) T) := by
  intro i t Φ Φ' ρ hΦ h
  rcases i with ⟨ls, ⟨⟩⟩
  exact opTabW_core.mpr (opTable_mono _ ls t _ _ ρ (fun ls e ρ h => hΦ (ls, ()) e ρ h)
    (opTabW_core.mp h))

/-- **`RedLaws coreW`.** -/
theorem redLaws_core : RedLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) := redLaws_of_mono opTabW_mono_core

/-- **`P11 coreW`.** -/
theorem p11_core : P11 (ℍ := ℍ) (coreW (ℍ := ℍ)) := ⟨handleCompat_core, redLaws_core⟩

end Targets

end
