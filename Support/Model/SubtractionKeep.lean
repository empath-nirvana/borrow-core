import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Outlives
import Support.Model.Subtraction

/-!
# Support — Model — SubtractionKeep

`[about ours]`.  Lemma 6.52 at `SubKeep`, the form 6.150 spends.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- 6.52's `ρ⁺ ⊟ ρ_reb` on Definition 6.3's paragraph reading (§12.58), and the
only one.
`[about ours: `[TR]` 6.52's conclusion at `ResU.SubKeep`]` -/
theorem ResU.six52_keep {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : ResU.UpdV ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∃ ψ, ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) ψ ∧
      ResU.CompS ψ (ρ.restrictDom ρ'i.exclPart) ρp ∧ ψ.InStratum α := by
  obtain ⟨ψ, hsub, hcomp⟩ :=
    ResU.sub_of_le (ResU.reb_restrictDom_exclPart_empty hreb)
      (ResU.six52_H1 hreb hce hcp hupd hse hs')
  exact ⟨ψ, hsub, hcomp,
    ResU.six52_sub_inStratum hreb hce hcp hupd hse hs' ψ hsub.toSub⟩

end BoCa.Fig16

end
