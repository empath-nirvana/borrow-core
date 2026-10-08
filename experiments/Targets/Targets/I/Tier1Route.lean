import Targets.I.Combined
import Targets.I.OpenRel
import Targets.Instance.J1Checks
import Targets.Instance.Checks
import Targets.I.Restricted.InstanceSafety

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

**The restricted tier-1 reduction at today's kernel** (`tier1Core_of`): A's properties but S5 hold
at every admissible effect context (`sPropsNoCancel_tier1Open`: S0 and S4 from `LiveOK`, the let
law, S1, `DataDiv`, S2, S3), and B's guarantees hold (`tier1Core_guarantees`), so `I.Tier1Core`
follows from S5 there.
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

/-- **A's properties at today's kernel, S5 aside**, at every admissible effect context: S0 and S4
(from `LiveOK`, `Inst.liveOK_tier1Open`), the let law, S1, `DataDiv`, S2 and S3. -/
theorem sPropsNoCancel_tier1Open {Ξ : EffCtx} (hΞ : Inst.AdmEff Ξ) :
    (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).MachShape ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).LetLaw ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).RowAlgebra ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).DataDiv ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).Safety ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).EffSafe ∧
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).HandlerSem :=
  ⟨Inst.machShape_orow Inst.liveOK_tier1Open, Inst.letLaw_ourInst_tier1Open,
    Inst.rowAlgebra_ourInst_tier1Open hΞ.1, Inst.dataDiv_ourInst, Inst.safety_ourInst_tier1Open,
    Inst.effSafe_ourInst_tier1Open, Inst.handlerSem_orow Inst.liveOK_tier1Open⟩

/-- **The restricted tier-1 reduction, given S5 at today's kernel.** -/
theorem tier1Core_of
    (hC : ∀ Ξ, Inst.AdmEff Ξ → (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).Cancellation
      (Inst.ourInst (ℍ := ℍ) orowRF Ξ Inst.tier1Open).noFinRaise) : Tier1Core (ℍ := ℍ) := by
  obtain ⟨hB, hI, hD, hW⟩ := tier1Core_world (ℍ := ℍ)
  refine ⟨fun Ξ hΞ => ?_, tier1Core_guarantees, hB, hI, pins_tier1Open, hD, hW⟩
  obtain ⟨h0, hl, h1, hd, h2, h3, h4⟩ := sPropsNoCancel_tier1Open (ℍ := ℍ) hΞ
  exact ⟨h0, hl, h1, hd, h2, h3, h4, hC Ξ hΞ⟩

end Targets.I

end
