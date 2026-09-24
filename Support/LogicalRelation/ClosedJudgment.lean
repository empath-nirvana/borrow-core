import Paper.S1_Syntax.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Statics.Contexts

/-!
# Support — LogicalRelation — ClosedJudgment

`[about ours]`.  The judgment `Δ; Γ ⊨ e : T` at the empty resource.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `Δ; Γ ⊨ e : T` as a proposition: a persistent proposition holds exactly when
it holds of `∅`. -/
noncomputable def Sem (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop :=
  SemTy Δ Γ e T PMap.empty

end BoCa.Fig16.LogRel

end
