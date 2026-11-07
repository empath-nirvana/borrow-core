import Core.Chain.SI.Ewp
import Core.StepsN

/-!
# Step-indexed relation: adequacy

LinearActris's Theorem 5.4 at one thread: initialisation, preservation and progress.

* **Initialisation**: a closed program in `ewp` at every index, owning nothing, from the empty
  memory.
* **Preservation** (`ewp_steps`): along every run, the configuration stays in `ewp` at every index,
  owning the whole memory. At the top the frame is empty, so the fragment a step lands at is the
  memory itself, the same at every index: the existential of the step clause is determined.
* **Progress** (`ewp_progress`): at index `1`, a configuration that is not a value steps (the top
  protocol allows no stop), and a value owns the whole memory in a postcondition that owns
  nothing, so the memory is empty.

Termination is not claimed: a run may go on for ever, and every prefix of it is covered.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The protocol that allows no stop: a closed program's. -/
def Prot.none : Prot := ⟨fun _ _ => Option.none, fun _ _ => Option.none⟩

/-- At the top: a configuration in `ewp` at index `n + 1` that steps is in it at `n` after the
step, owning the memory it steps to. -/
theorem ewp_top_step {Q : Post} {n : Nat} {μ μ' : Heap} {e e' : Expr} (hf : FinDom μ)
    (h : ewp (ℍ := ℍ) Prot.none Q (n + 1) e μ) (hs : Step1 (ℍ := ℍ) μ e μ' e') :
    ewp (ℍ := ℍ) Prot.none Q n e' μ' := by
  rcases ewp_succ.1 h with ⟨v, rfl, -⟩ | ⟨K, m, i, v, s, -, -, hs', -⟩ | ⟨K, m, i, v, R, -, -, hR, -⟩ |
    ⟨-, hst⟩
  · exact absurd hs BoLo.no_step_val
  · cases hs'
  · cases hR
  · have hfd : FinDom (un μ emp) := by rwa [un_emp_right]
    rw [← un_emp_right μ] at hs
    obtain ⟨σ', -, rfl, h'⟩ := (hst emp (disj_emp_right μ) hfd).2 μ' e' hs
    rwa [un_emp_right]

/-- **Preservation**: every configuration a run reaches is in `ewp` at every index, owning the
whole memory, which has finitely many cells. -/
theorem ewp_steps {Q : Post} {μ μ' : Heap} {e e' : Expr} (hs : Steps (ℍ := ℍ) μ e μ' e') :
    FinDom μ → (∀ n, ewp (ℍ := ℍ) Prot.none Q n e μ) →
      FinDom μ' ∧ ∀ n, ewp (ℍ := ℍ) Prot.none Q n e' μ' := by
  induction hs with
  | refl => exact fun hf h => ⟨hf, h⟩
  | more h₁ _ ih =>
      intro hf h
      exact ih (fd_step1 h₁ hf) (fun n => ewp_top_step hf (h (n + 1)) h₁)

/-- **Progress**: in `ewp` at index `1`, a configuration that is not a value steps, and a value
owns the memory in the postcondition. -/
theorem ewp_progress {Q : Post} {μ : Heap} {e : Expr} (hf : FinDom μ)
    (h : ewp (ℍ := ℍ) Prot.none Q 1 e μ) :
    (∃ v : Val, e = v.1 ∧ Q 1 v μ) ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
  rcases ewp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨K, m, i, v, s, -, -, hs', -⟩ | ⟨K, m, i, v, R, -, -, hR, -⟩ |
    ⟨-, hst⟩
  · exact .inl ⟨v, rfl, hq⟩
  · cases hs'
  · cases hR
  · have hfd : FinDom (un μ emp) := by rwa [un_emp_right]
    obtain ⟨μ', e', hs⟩ := (hst emp (disj_emp_right μ) hfd).1
    rw [un_emp_right] at hs
    exact .inr ⟨μ', e', hs⟩

/-- **Adequacy**: a closed program in `ewp` at every index, owning nothing, at a postcondition
that owns nothing, is safe or diverges: every configuration a run reaches is a value or steps, a
value is reached only at the empty memory, and every `free` finds its cell. -/
theorem adequacy {Q : Post} {P₀ : Expr} (hQ : ∀ n v σ, Q n v σ → σ = emp)
    (h : ∀ n, ewp (ℍ := ℍ) Prot.none Q n P₀ emp) :
    OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨hf, he⟩ := ewp_steps hs fd_empty h
  have hp := ewp_progress hf (he 1)
  refine ⟨?_, ?_, ?_⟩
  · rcases hp with ⟨v, rfl, -⟩ | hst
    · exact .inl v.2
    · exact .inr hst
  · intro hv
    have := ewp_val_inv (v := ⟨e, hv⟩) (he 1)
    exact hQ _ _ _ this
  · intro K ℓ he'
    subst he'
    rcases hp with ⟨v, hv, -⟩ | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug (hv ▸ v.2)
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
