import Core.LetDtor
import Core.EffMachine
import Core.EffPrograms
import Core.DivRuntime

/-!
# Core — resource safety  `[spec §62]`

**`resourceSafety`.** For every closed `CDerives` program at a persistent answer, every run from
the empty memory, under every allocator:

1. continues to a value at the empty memory: every cell it allocated is freed;
2. never sticks; in particular, every `free ℓ` it reaches at an evaluation position finds `ℓ`
   allocated (`step1_free_iff`), and its step removes `ℓ`, so no cell is freed twice.

An allocation picks a location the memory does not hold (`step1_alloc_iff`) and a release removes
the one it frees, so (1) and (2) say each allocation is released exactly once. The exits are the
program's: a normal return, a raise caught by a handler, a cancel (a raise of name `0`, §29a), an
early close of a loop (a resume with *close*, §14). Each is a run of a closed program, and
`[let-dtor]` is a `CDerives` derivation (`CDerives.effLetD`), so every program it types is
covered. The proof is `adequacyD` at the derivation (`adequacyD_obs`).

**Order.** On a raise or a cancel, the `[let-dtor]` frame runs `drop_ctx` before the error goes on
(`letDE_finalise`, `letDE_finaliseCancel`), and `drop_ctx` runs the destructor of the slot bound
last first (`dropCtxE_some`). The file programs check the order by `eval`
(`Core/LetDtorFiles.lean`, `Core/LetDtorCancel.lean`, `Core/LetDtorSuspend.lean`). A program-wide
statement that every release follows the reverse order of allocation is not made: `CDerives` has
exchange (`Ctx.SplitP` interleaves freely), and a program may free its cells in any order it
writes.

**At a `Div` row** (`rtSafety`): under the runtime's handler, every configuration a run reaches is
a value or steps, and every `free` it reaches finds its cell, on terminating and diverging runs
alike (`runtime_every_run`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core.EffPrograms (adequacyD_obs)
open BoCa.BoLo (Heap Steps Step1 Head Kont freeE raiseE hndE opPayload cancelVal cfinE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Resource safety** of every closed program at a persistent answer: every run from the empty
memory continues to a value at the empty memory (every cell allocated is freed), and every release
it reaches finds its cell allocated (none is freed twice).  `[spec §62]` -/
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

/-- **The raise exit runs `drop_ctx`**: a raise `p` (not a cancel) reaching the `[let-dtor]` frame
through a context `K'` that catches nothing of its name steps to `drop_ctx`, then the same raise
(`[finalise]`).  `[spec §62]` -/
theorem letDE_finalise (μ : Heap) (ds : List (Option Expr)) (N : Expr) (n i : UInt32) (v : Val)
    (K K' : Kont) (hn : n ≠ 0) (hK : K'.Catches n = false) :
    Step1 (ℍ := ℍ) μ (K.plug (letDE ds N (K'.plug (raiseE (.val (opPayload n i v)))))) μ
      (K.plug (.seq (.app (.val (.lam (dropCtxE ds 1))) (.val .unit))
        (raiseE (.val (opPayload n i v))))) :=
  ⟨K, _, _, rfl, rfl, Head.ufin μ (.lam N) (.lam (dropCtxE ds 1)) n i v K' hn hK⟩

/-- **The cancel exit runs `drop_ctx`**: a cancel reaching the `[let-dtor]` frame runs `drop_ctx`
under `cfin`, which passes the cancel on when it returns (`[finalise-cancel]`).  `[spec §62]` -/
theorem letDE_finaliseCancel (μ : Heap) (ds : List (Option Expr)) (N : Expr) (err : Option Val)
    (K K' : Kont) (hK : K'.Catches 0 = false) :
    Step1 (ℍ := ℍ) μ (K.plug (letDE ds N (K'.plug (raiseE (.val (cancelVal err)))))) μ
      (K.plug (cfinE (cancelVal err) (.app (.val (.lam (dropCtxE ds 1))) (.val .unit)))) :=
  ⟨K, _, _, rfl, rfl, Head.ufinC μ (.lam N) (.lam (dropCtxE ds 1)) err K' hK⟩

/-- **Safety at a `Div` row, with no termination**: every configuration a run of `hnd rtH M`
reaches is a value or steps, and a `free` at an evaluation position finds its cell.
`[spec §14, §62]` -/
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
