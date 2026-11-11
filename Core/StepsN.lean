import Core.EffCancelRuns

/-!
# Core — runs of a counted length, final configurations, and safety or divergence  `[spec §62]`

The machine facts the step-indexed relation over the tree world (`Core/TreeWp.lean`) reads:

* **Runs of a counted length** (`StepsN`): `j` machine steps. Every run has a length
  (`stepsN_of_steps`); a run keeps a memory's cells finitely many (`fd_stepsN`); a counted run of
  `K[e]` splits where `e` stops stepping (`stepsN_plug_split`, `steps_plug_split` counted).
* **Final configurations** (`Final`): no step. A value is final (`final_val`), and so is an
  operation whose context catches nothing of it (`final_opPlug`, from `opPlug_no_step`).
* **Safe, or it diverges** (`OrDiverges`): every configuration a run from the empty memory reaches
  goes on or is a value; a value is reached only at the empty memory; every release finds its
  cell. This is the adequacy statement of `Core/TreeCactus.lean`'s `cerwpT_adequacy`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Kont freeE)

/-! ### Runs of a counted length -/

/-- `j` machine steps. -/
inductive StepsN : Nat → Heap → Expr → Heap → Expr → Prop
  | refl (μ : Heap) (e : Expr) : StepsN 0 μ e μ e
  | more {j : Nat} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 (ℍ := ℍ) μ e μ₁ e₁) (t : StepsN j μ₁ e₁ μ' e') : StepsN (j + 1) μ e μ' e'

/-- **A counted run keeps a memory's cells finitely many.** -/
theorem fd_stepsN {j : Nat} {μ μ' : Heap} {e e' : Expr} (h : StepsN (ℍ := ℍ) j μ e μ' e')
    (hf : FinDom μ) : FinDom μ' := by
  induction h with
  | refl => exact hf
  | more h _ ih =>
      obtain ⟨_, _, _, -, -, hh⟩ := h
      exact ih (finDom_head hh hf)

/-- **Every run has a length.** -/
theorem stepsN_of_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e') :
    ∃ j, StepsN (ℍ := ℍ) j μ e μ' e' := by
  induction h with
  | refl => exact ⟨0, .refl _ _⟩
  | more h₁ _ ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨j + 1, .more h₁ hj⟩

/-- **Run splitting, counted** (`steps_plug_split`): a run of `K[e]` is `K` around a run of `e`,
or a run of `e` to a term that takes no step followed by a run from `K` around it. -/
theorem stepsN_plug_split (K : Kont) {j : Nat} {μ μ' : Heap} {e E : Expr}
    (hs : StepsN (ℍ := ℍ) j μ (K.plug e) μ' E) :
    (∃ e', E = K.plug e' ∧ StepsN (ℍ := ℍ) j μ e μ' e') ∨
    ∃ j₁ j₂ μ₁ t, j₁ + j₂ = j ∧ StepsN (ℍ := ℍ) j₁ μ e μ₁ t ∧
      (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ t₂) ∧ StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E := by
  generalize hE : K.plug e = E₀ at hs
  induction hs generalizing e with
  | refl μ E₀ => exact .inl ⟨e, hE.symm, .refl _ _⟩
  | @more j μ μ₁ μ' E₀ E₁ E' h t ih =>
      subst hE
      by_cases hst : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ e μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hst
        obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K h₂ h
        rcases ih rfl with ⟨e'', rfl, hs''⟩ | ⟨j₁, j₂, μ₃, t₃, hj, hs₃, hirr, hrest⟩
        · exact .inl ⟨e'', rfl, .more he' hs''⟩
        · exact .inr ⟨j₁ + 1, j₂, μ₃, t₃, by omega, .more he' hs₃, hirr, hrest⟩
      · simp only [not_exists] at hst
        exact .inr ⟨0, j + 1, μ, e, by omega, .refl _ _, hst, .more h t⟩

/-! ### Final configurations -/

/-- A configuration with no step. -/
def Final (μ : Heap) (e : Expr) : Prop := ∀ μ' e', ¬ Step1 (ℍ := ℍ) μ e μ' e'

theorem final_val (μ : Heap) (v : Val) : Final (ℍ := ℍ) μ v.1 :=
  fun _ _ h => BoLo.no_step_val h

/-- A stop of an operation is final at every memory. -/
theorem final_opPlug {K : Kont} {r : Bool} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK : OpFree r n K) (μ : Heap) :
    Final (ℍ := ℍ) μ (K.plug (opE r p)) :=
  fun _ _ h => opPlug_no_step hn hK h

/-- A stop of `cancelTo` is final at every memory: no handler of its name encloses it.
`[spec §51]` -/
theorem final_cancelToPlug {K : Kont} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK : K.HasHnd n = false) (μ : Heap) :
    Final (ℍ := ℍ) μ (K.plug (BoCa.BoLo.cancelToE (.val p))) :=
  fun _ _ h => cancelToPlug_no_step hn hK h

/-! ### Safe, or it diverges -/

/-- **Safe, or it diverges**: every configuration a run reaches goes on or is a value; a value is
reached at the empty memory (every cell freed); every release finds its cell. -/
def OrDiverges (P : Expr) : Prop :=
  ∀ {μ : Heap} {e : Expr}, Steps (ℍ := ℍ) Adequacy.emptyMem P μ e →
    (IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e') ∧
    (IsVal e → μ = Adequacy.emptyMem) ∧
    (∀ (K : Kont) (ℓ : Loc), e = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ ℓ = some u)

end BoCa.Fig16.LogRel.Core

end
