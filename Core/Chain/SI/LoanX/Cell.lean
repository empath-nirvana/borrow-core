import Core.Chain.SI.LoanX.Algebra
import Core.Chain.SI.LoanX.MainBridge

noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

/-- Generic physical return permission; descriptor equality will be supplied by owned
registry agreement rather than an ad hoc per-program location side condition. -/
def cellOf : Loan → Val → WRes → Prop
  | .mut l β P, w, ρ => ∃ (u : Val) (h : ResU.InStratum β (PMap.empty : WRes))
      (hu : P u ⟨PMap.empty,h⟩), w = Val.loc l ∧
        ρ = ResU.single l (CellU.mutOf β u PMap.empty h P hu)
  | .imm _ _, _, _ => False

end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
