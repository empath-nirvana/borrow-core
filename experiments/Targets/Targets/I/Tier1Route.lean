import Targets.I.Combined
import Targets.I.OpenRel
import Targets.Instance.J1Checks
import Targets.Instance.Checks

/-!
# The interaction — tier 1 and the elaboration route (TIER1-PLAN §2)

TIER1-PLAN §2 reaches FL at `J₁` by elaborating each derivation of `J₁` into today's unr-free
kernel and applying `fundamentalC` unchanged.  At a closed judgement that elaboration says
`Inst.ElabClosed J₁`: the closed derivation is a `CDerivesNU` derivation of the same term.

`not_tier1_of_elabClosed`: no typing system with that property meets `I.Tier1`.  Tier 1 asks A's
(E) properties at every admissible effect context; E8's first program is a handler, which our
instance encodes as the run-time frame with its clauses as values; and no `CDerivesNU` derivation
has that frame (`Inst.not_der_handleK`).  So a `J₁` that meets tier 1 types a handler form that
today's kernel does not, and its FL needs more than `fundamentalC`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I

/-- **The elaboration route does not reach tier 1.** -/
theorem not_tier1_of_elabClosed {J₁ : Inst.OurTyping orowRF} (hE : Inst.ElabClosed J₁) :
    ¬ Tier1 (ℍ := ℍ) J₁ := by
  rintro ⟨hA, -⟩
  exact Inst.not_unwindPolicy_of_elabClosed hE
    (hA Inst.ΞA Inst.admEff_ΞA).2.2.2.2.2.2.2.2.1

end Targets.I

end
