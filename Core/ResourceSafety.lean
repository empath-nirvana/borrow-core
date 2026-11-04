import Core.EffMachine
import Core.EffPrograms
import Core.DivRuntime
import Core.Closed

/-!
# Core — resource safety  `[spec §13, §14]`

**`resourceSafety`** is `adequacyD` read over cells. For every closed `CDerives` program at a
persistent answer, every run from the empty memory, under every allocator, continues to a value at
the empty memory (every cell it allocated is freed), and every `free ℓ` it reaches at an
evaluation position finds `ℓ` allocated (`step1_free_iff`), so its step removes `ℓ` and no cell is
freed twice. It sees memory only: a host resource counts as closed only if its handle owns a
cell and its type is linear with its close its one eliminator.

That each allocation is freed exactly once follows informally: an allocation picks a location
the memory does not hold (`step1_alloc_iff`), a `free` removes the cell it frees, and the run
starts and ends at the empty memory. No theorem counts frees.

**At `[tickSig]`** (`rtSafety`): under the runtime's handler, every configuration a run of a
closed program at the row `{tick}` reaches is a value or steps, and every `free` it reaches finds
its cell, on terminating and diverging runs alike (`runtime_every_run`): progress and no double
free, without leak freedom.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core.EffPrograms (adequacyD_obs)
open BoCa.BoLo (Heap Steps Step1 Head Kont freeE raiseE hndE opPayload cancelVal cfinE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Resource safety** of every closed program at a persistent answer, `adequacyD` read over
cells: every run from the empty memory continues to a value at the empty memory (every cell
allocated is freed), and every `free` it reaches finds its cell allocated (none is freed twice).
`[spec §13]` -/
theorem resourceSafety {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs hA h hs
  refine ⟨⟨v, hv⟩, fun K ℓ he => ?_⟩
  cases hv with
  | refl =>
      have hc : IsVal (K.plug (freeE (.val (Val.loc ℓ)))) := by rw [← he]; exact v.2
      have := K.isVal_of_plug hc
      cases this
  | more hst _ =>
      rw [he] at hst
      obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).mp hst
      exact ⟨u, hu⟩

/-- **Safety at `[tickSig]`, with no termination**: every configuration a run of `hnd rtH M`
reaches is a value or steps, and a `free` at an evaluation position finds its cell. Progress and
no double free; not leak freedom.  `[spec §14]` -/
theorem rtSafety {M : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty [] M (.comp (CTy.effOf [tickSig] A))) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (hndE DivRuntime.rtH M) μ₁ e₁) :
    (IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) := by
  have hgo := runtime_every_run h hs
  refine ⟨hgo, fun K ℓ he => ?_⟩
  subst he
  rcases hgo with hv | ⟨μ₂, e₂, hst⟩
  · have := K.isVal_of_plug hv
    cases this
  · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).mp hst
    exact ⟨u, hu⟩

end BoCa.Fig16.LogRel.Core

end
