import Targets.Instance.Checks

/-!
# The Instance — `LiveOK` is met at a typing of one program

`LiveOK` (`Targets/Instance/Machine.lean`) is the hypothesis of the laws that assert a step: every
configuration a typed closed program reaches has a closed term and goes on.  It holds at `JnLog`,
the typing system that types `nLogOutside` alone, at its answer type
(`liveOK_JnLog`).  That program has a handler, an operation the handler catches and a continuation
its clause holds.  The run `look` computes is the only one under every runner (`rreach_chain_mem`):
each of its steps allocates nothing, so it is its configuration's only step.  The run's terms are
closed by `closed_steps`, and each of them steps, or is the answer (`goesOn_chain`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open Targets (RowForm EffCtx orowRF HeadChain lookRun lookEnd lookRun_sound HeapClosed closed_step1
  heapClosed_empty)

variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- Every configuration reached from the start of a chain of head steps that allocate nothing,
ending at a value, is one of the chain's, under every runner. -/
theorem rreach_chain_mem (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' → IsVal e' →
      ∀ c, (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((μ, e), s) c →
        ∃ t ∈ chainTerms e q, c = ((μ, t), s)
  | _, _, _, .nil, hv, c, h => by
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, ⟨ev, hst⟩, -⟩
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · exact (no_rstep_val R ⟨_, hv⟩ hst).elim
  | _, _, _, @HeadChain.cons _ _ K a a' e' q hh hn hq, hv, c, h => by
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, ⟨ev, hst⟩, hrest⟩
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨-, rfl⟩ := rstep_det (hh μ) hn hst
        obtain ⟨t, ht, rfl⟩ := rreach_chain_mem R hq hv c hrest
        refine ⟨t, ?_, rfl⟩
        simp only [chainTerms, List.map_cons, List.mem_cons] at ht ⊢
        exact .inr ht

/-- Each term of a chain ending at a value goes on. -/
theorem goesOn_chain {μ : Heap} : ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)},
    HeadChain (ℍ := ℍ) e q e' → IsVal e' → ∀ t ∈ chainTerms e q, GoesOn (ℍ := ℍ) RF Ξ (μ, t)
  | _, _, _, .nil, hv, t, ht => by
      simp only [chainTerms, List.map_nil, List.mem_singleton] at ht
      subst ht
      exact .inl ⟨⟨_, hv⟩, rfl⟩
  | _, _, _, .cons hh _ hq, hv, t, ht => by
      simp only [chainTerms, List.map_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact .inr (.inl ⟨_, _, OStep.mach (hh μ)⟩)
      · exact goesOn_chain hq hv t (by simpa [chainTerms] using ht)

/-- Each term of a chain from a closed term is closed. -/
theorem closedAt_chain : ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)},
    HeadChain (ℍ := ℍ) e q e' → closedAt 0 e = true → ∀ t ∈ chainTerms e q, closedAt 0 t = true
  | _, _, _, .nil, he, t, ht => by
      simp only [chainTerms, List.map_nil, List.mem_singleton] at ht
      subst ht; exact he
  | _, _, _, @HeadChain.cons _ _ K a a' e' q hh _ hq, he, t, ht => by
      have he' := (closed_step1 (ℍ := ℍ) ⟨K, a, a', rfl, rfl, hh Adequacy.emptyMem⟩ he
        heapClosed_empty).1
      simp only [chainTerms, List.map_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact he
      · exact closedAt_chain hq he' t (by simpa [chainTerms] using ht)

/-- `nLogOutside`'s answer type. -/
abbrev nLogTy : OCTy := OCTy.ofC (.ret (.tensor (.sum .zero .unit) Flag))

/-- **A typing system that types `nLogOutside` alone**, at its answer type. -/
def JnLog : OurTyping orowRF := ⟨fun _ _ _ e j => e = nLogOutside ∧ j = .comp nLogTy, OutJ.core,
  fun _ η => η⟩

/-- `nLogOutside`'s answer type is no loop sum: `JnLog` types no driven program. -/
theorem not_isLoopSum_nLogTy : ¬ IsLoopSum nLogTy := by
  intro h
  obtain ⟨S, S₀, A₀, -, hC⟩ := h (fun _ => [])
  cases S <;> simp [nLogTy, OCTy.ofC, OCTy.den, OVTy.ofV, OVTy.den, CTy.effOf] at hC

/-- **`LiveOK` holds at `JnLog`**, at every effect context. -/
theorem liveOK_JnLog : LiveOK (ℍ := ℍ) orowRF Ξ JnLog := by
  rintro c ⟨P, C, R, s, -, hP, hreach⟩
  have hP' : P = nLogOutside := by
    rcases hP with ⟨Θ, -, he, -⟩ | ⟨-, M, rfl, hC, Θ, -, hM, hj⟩
    · exact he
    · exfalso
      cases hj
      exact not_isLoopSum_nLogTy hC
  subst hP'
  have hchain := lookRun_sound (ℍ := ℍ) 20 nLogOutside
  have hv : IsVal (lookEnd 20 nLogOutside) := by rw [nLogRun_end]; exact .pair (.inj₂ .unit) (.inj₂ .unit)
  obtain ⟨t, ht, hcs⟩ := rreach_chain_mem R hchain hv (c, s) hreach
  obtain ⟨rfl, -⟩ := Prod.mk.inj hcs
  exact ⟨closedAt_chain hchain (by decide) t ht, goesOn_chain hchain hv t ht⟩

end Targets.Inst

end
