import DtorUnwind.Safety
import Core.DivRuntime

/-!
# Stage 8: exit-conditional safety at a `Div` row, under the runtime's handler

`runtime_every_run` is the partial-correctness theorem the kernel has for unbudgeted programs: a
closed `M : F_{Div} A` under the runtime's handler `rtH` (every tick answered *next*) never
reaches a stuck configuration, whether or not it ends. Its proof is an invariant of
configurations over `cwp`'s segments (`DivRuntime.Good`/`PostD`), so it holds at a row with `Div`
and needs no termination.

`rtSafety` reads (i) off it: every configuration a run reaches goes on, and every `free` it
reaches finds its cell (`step1_free_iff`), so no cell is freed twice, on terminating and
diverging runs alike. Div-free programs keep `resourceSafety` unchanged: this file adds a theorem
and touches no rule or relation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.Partial
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Kont freeE hndE)
open BoCa.Lifetime (LifeCtx)

/-- **(i) at a `Div` row, with no termination**: every configuration a run of `hnd rtH M`
reaches is a value or steps, and a `free` at an evaluation position finds its cell. -/
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

open BoCa.Fig16.LogRel.Core.DtorUnwind in
/-- **`[let-dtor]` with destructors that may loop**: `effLetD` without `hSDd`, by `[then]`'s
`effThenDiv`, when the bound computation's row has no capturable operation (`hcap`): no cancel run
reaches the frame, and a raise reaches it on the ordinary unwind, at `Σ`, which then holds `Div`.
The destructors still never fail (`¬ Σ_D.Cancels`). -/
theorem effLetDDiv {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SD : Row} {ds : List (Option Expr)}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hcap : ∀ o ∈ S, capB o.q o.B = false)
    (hds : Dtors Δ SD Γ₂ ds)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDE ds N M) (.comp (CTy.effOf S B)) := by
  have hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) (dropCtxE ds 1) (.comp (CTy.effOf SD .unit)) :=
    dropCtx_derives hSDc hds (P := [⟨.unit, false⟩]) (.cons .nil)
  refine .effThenDiv (SM := S) (SD := SD) hs hNZ hUq hU (RowLe.refl S) hDS ?_ ?_ hcap hM hN hD
  · intro n i o o' hf hf' hr
    rw [hf] at hf'; cases hf'
    exact hfin n i o hf hr
  · exact fun h => absurd h (Row.not_unrD_of_not_cancels hSDc)

end BoCa.Fig16.LogRel.Core.DtorUnwind.Partial

end
