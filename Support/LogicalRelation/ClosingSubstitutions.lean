import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Substitution
import Support.Syntax.Terms

/-!
# Support — LogicalRelation — ClosingSubstitutions

`[about ours]`.  Closing substitutions `γ(e)`, free lifetime variables of a type, and the empty resource in every stratum.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.MutImmCell
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

theorem empty_inStratum (b : Life) :
    ResU.InStratum (Loc := BoCa.Loc) (Val := BoCa.Val) b PMap.empty :=
  fun _ _ e => absurd e (by simp)

end BoCa.Fig16.LogRel.MutImmCell

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `γ(e)` — the parallel substitution `Expr.psub`, for the reason
convention L5 (`docs/adjudications.md`) gives: a fold of `Expr.subst 0` is the closing
substitution only for a closed `γ`. -/
def substAll (γ : List Val) (e : Expr) : Expr := Expr.psub 0 γ e

/-- `'x` occurs free in `T`, with `∀'y ⊏ @b. T` binding `'y` in `T` and not in
`@b`.  `𝒱⟦T⟧δ` reads `δ` only at these variables. -/
def LFree (x : LifeVar) : Ty → Prop
  | .unit          => False
  | .unk           => False
  | .ref T         => LFree x T
  | .bang T         => LFree x T
  | .imm a T       => a.mentions x = true ∨ LFree x T
  | .mut a T       => a.mentions x = true ∨ LFree x T
  | .box a T       => a.mentions x = true ∨ LFree x T
  | .sum T₁ T₂     => LFree x T₁ ∨ LFree x T₂
  | .tensor T₁ T₂  => LFree x T₁ ∨ LFree x T₂
  | .lolli T₁ T₂   => LFree x T₁ ∨ LFree x T₂
  | .all y b T     => b.mentions x = true ∨ (x ≠ y ∧ LFree x T)

end BoCa.Fig16.LogRel

end
