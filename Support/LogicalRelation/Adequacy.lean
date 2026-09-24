import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Terms
import Support.LogicalRelation.Facts
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms

/-!
# Support — LogicalRelation — Adequacy

`[about ours]`.  The empty memory, and the judgment at `Δ = Γ = ∅` read at `δ = ∅`, `γ = []`, `ρ = ∅`.
-/

noncomputable section

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `∅` on the memory side of `(∅, e) →* (∅, v)`: `[TR]` p. 3's
`Mem ∋ μ : Loc ⇀ Val` at the empty map.
`[about ours: the empty `μ` of `[TR]` p. 3's `Mem` row]` -/
def emptyMem : Heap := fun _ => none

/-- `γ(e) = e` at the empty substitution, under any cutoff.
`[about ours: `[TR]` p. 4's `γ(e)` at `γ = []`]` -/
theorem psub_nil (k : Nat) (e : Expr) : Expr.psub k [] e = e := by
  induction e generalizing k with
  | var i =>
      show (if i < k then Expr.var i
            else match ([] : List Val)[i - k]? with
                 | some v => Expr.val (v.shift k 0)
                 | none   => Expr.var (i - ([] : List Val).length)) = _
      split <;> simp
  | _ => simp [Expr.psub, *]

/-- `δ ∈ ⟦∅⟧` at the empty substitution.
`[about ours: `[TR]` p. 4's `δ ∈ ⟦Δ⟧` at `Δ = ∅`]` -/
theorem models_empty : Lifetime.LifeCtx.Models Lifetime.LifeCtx.empty Lifetime.LSub.empty := by
  intro x u h
  exact absurd h (by simp [Lifetime.LifeCtx.empty, Lifetime.LifeCtx.find?, Lifetime.assocFind])

/-- `𝒢⟦∅⟧δ([])` holds of `∅`: the printed `⍟` over an empty context is `emp`.
`[about ours: `[TR]` p. 4's `𝒢⟦Γ⟧δ(γ)` at `Γ = γ = ∅`]` -/
theorem gDen_empty (δ : Lifetime.LSub) :
    Fig16.LogRel.gDen δ [] [] (PMap.empty : WRes) :=
  Fig16.LogRel.gDen_iff.mpr
    ⟨by simp [Ctx.LiveWithin], by simp only [Fig16.LogRel.gSep]; exact ⟨rfl, trivial⟩⟩

/-- `𝒱⟦1⟧δ = fun v => ⌜v = ()⌝`, pointwise.
`[about ours: `[TR]` p. 4's `𝒱⟦1⟧δ` as a pure predicate]` -/
theorem vDen_unit_eq (δ : Lifetime.LSub) :
    Fig16.LogRel.vDen Ty.unit δ = fun v => Fig16.BoLo.pure (v = Val.unit) := by
  funext v; exact Fig16.LogRel.vDen_unit δ v

end BoCa.Adequacy

end
