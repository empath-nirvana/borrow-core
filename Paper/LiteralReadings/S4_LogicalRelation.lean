import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts

/-!
# Literal readings — [TR] §4

`MutImmCell` (row 4.17): the `imm` cell recording `{α₀, β}` that measures the
literal `α ⊑ ⊔β̄` of `ℓ ↦ Imm α P̂` (§12.67(a)).  Nothing depends on this file.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.MutImmCell
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### 4.17 · — no printed counterpart — · [TR] p. 4 · `[repair]`

An `imm` cell recording `{α₀, β}`, outside `Res_β`.  At row 5.30's `⊓β̄` it is in
`𝒱⟦Imm @b 1⟧δ` only where `@bδ ⊑ α₀ ⊓ β`; at the literal `⊔β̄` it empties
`𝒱⟦Mut @a (Imm @b 1)⟧δ` (§12.67(a)).
-/
/-- `β̄ = {α₀, β}`. -/
def lset (α₀ β : Life) : LSet := (LSet.singleton α₀).union (LSet.singleton β)

/-!
Row 4.17, continued.
-/
/-- The cell: an immutable borrow whose recorded set is `{α₀, β}`. -/
noncomputable def cell (α₀ β : Life) : WRes :=
  ResU.single 0 (CellU.immOf (lset α₀ β) .unit PMap.empty
    (empty_inStratum (lset α₀ β).join))

/-! `[about ours]` -/
theorem lset_meet (α₀ β : Life) : (lset α₀ β).meet = α₀ ⊓ β := rfl

/-!
Row 4.17, continued.
-/
/-- At `β = α₀` the cell is in `𝒱⟦Imm @b 1⟧δ`, `@bδ = α₀`. -/
theorem inRel_same {δ : LSub} {b : Lifetime.Life} {α₀ : Life} (hb : b.interp δ = some α₀) :
    vDen (.imm b .unit) δ (.loc 0) (cell α₀ α₀) := by
  refine ⟨α₀, hb, 0, pure_sep_mk rfl ?_⟩
  exact ⟨lset α₀ α₀, .unit, PMap.empty, empty_inStratum _, rfl, ⟨rfl, rfl⟩,
    by rw [lset_meet, inf_idem]⟩

end BoCa.Fig16.LogRel.MutImmCell

namespace BoCa.Fig16.LogRel.MutPayloadSubst
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
Row 4.17, continued.
-/
/-- `Mut ⊤ (Imm 'x 1)`: a `Mut` type whose payload mentions the variable `∀E`
substitutes. -/
def Tpayload : Ty := .mut .top (.imm (.var 0) .unit)

end BoCa.Fig16.LogRel.MutPayloadSubst

end
