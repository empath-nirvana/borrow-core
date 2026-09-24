import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Machine

/-!
# Support — Dynamics — PrintedWp

`[about ours]`.  `[TR]` p. 6's `wp` over `[TR]` §3's printed machine (`TR3.wp`), and the `∀`-wand `wp-ramify` reads.
-/

noncomputable section

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (sep wand all box top ptoOwn ptoMut ptoImm NoOwn noOwn_compS)

/-- `Res` at `[TR]` §3's `Loc` and `Val`. -/
abbrev WRes : Type := ResU BoCa.Loc BoCa.Val

/-- `SProp ≜ Res → ℙ` at those. -/
abbrev WProp : Type := SPropU BoCa.Loc BoCa.Val

/-- `wp(e){Q̂}` — `[TR]` p. 6's last-but-one row, over the printed machine:

    wp(e){Q̂}(ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v.
                     (⟦ρ_f ● ρ⟧, e) ↦* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v)
                   ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺|own = ∅ ∧ Q̂(v)(ρ′)

`Fig16.BoLo.wp` with `TR3.Steps` for `BoLo.Steps`; the partial `●`s and `⟦−⟧`s
appear as their graphs (G4).  `[as printed]` -/
def wp (e : Expr) (Q : Val → WProp) : WProp := fun ρ =>
  ∀ ρf : WRes, ResU.Hash ρf ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS ρf ρ fρ ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      Q v ρ'

/-- `∀v. P̂(v) ─⋆ Q̂(v)` — the ramification wand.  `[TR]` Lemma 6.146 prints
`(P̂ –⋆ Q̂)`, and this is the reading `Fig16.BoLo.wp_ramify` gives it at
`P̂, Q̂ : Val → SProp`.
`[about ours: the reading of 6.146's `(P̂ –⋆ Q̂)`]` -/
def wandAll (P Q : Val → WProp) : WProp := all fun v => wand (P v) (Q v)

end BoCa.TR3

end
