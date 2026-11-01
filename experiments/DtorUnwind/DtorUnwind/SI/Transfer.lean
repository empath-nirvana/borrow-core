import DtorUnwind.SI.Programs

/-!
# Stage 2: what transfers at once

`OrDiverges` is a safety property, so every closed program the total relation already covers has
it: `resourceSafety` (stages 1–7) gives a run to a value at the empty memory from every reached
configuration, hence a step from every configuration that is not a value, and the empty memory at
every value reached. The stage 1–7 programs, at every budget, are instances.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind
open BoCa.BoLo (Heap Step1 Steps Kont freeE)
open BoCa.Lifetime (LifeCtx)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **Every closed program of the total relation is safe or diverges** (and here, never
diverges). -/
theorem orDiverges_of_derives {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) : LoopAwait.OrDiverges (ℍ := ℍ) e := by
  intro μ e₁ hs
  obtain ⟨⟨v, hv⟩, hfree⟩ := resourceSafety (ℍ := ℍ) hA h hs
  refine ⟨?_, fun hval => ?_, hfree⟩
  · cases hv with
    | refl => exact .inl v.2
    | more hst _ => exact .inr ⟨_, _, hst⟩
  · exact (BoLo.steps_val_inv (w := ⟨e₁, hval⟩) hv).1.symm

/-- Stage 7's programs at every budget. -/
theorem stage7_orDiverges (k : UInt32) :
    LoopAwait.OrDiverges (ℍ := ℍ) (LoopAwait.progRes k) ∧
    LoopAwait.OrDiverges (ℍ := ℍ) (LoopAwait.progDrop k) ∧
    LoopAwait.OrDiverges (ℍ := ℍ) (LoopAwait.progCancel k) :=
  ⟨orDiverges_of_derives (by decide) (LoopAwait.d_progRes k),
    orDiverges_of_derives (by decide) (LoopAwait.d_progDrop k),
    orDiverges_of_derives AwaitCancel.flag_persistent (LoopAwait.d_progCancel k)⟩

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
