import Targets.I.Interface

/-!
# The interaction — OQ-56 (a), R-CLOSEDOP (RESTRUCTURE §3.5)

`admExtends_closedOp` and `rowSpan_abortive_iff_unwind`
(R-CLOSEDOP at abortive rows is `Row.Unwind`).  `Pins` and `SpanRulesAt`, which read the
Instance's typing systems, are in `Targets/I/Combined.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem admExtends_closedOp : AdmExtends admClosedOp := fun _ _ _ h => h

/-- R-CLOSEDOP at abortive rows is `Row.Unwind`. -/
theorem rowSpan_abortive_iff_unwind {Δ : LifeCtx} {x : LifeVar} {S : Row} :
    RowSpan admClosedOp Δ x S ∧ RowClass.abortive.Admits S ↔ S.Unwind x := by
  constructor
  · rintro ⟨hs, ha⟩ o ho
    obtain ⟨hn, -, hA, -, hO, -⟩ := hs o ho
    exact ⟨ha o ho, hn, hA, hO⟩
  · intro h
    refine ⟨fun o ho => ?_, fun o ho => (h o ho).1⟩
    obtain ⟨ha, hn, hA, hO⟩ := h o ho
    have hB := OpSig.B_zero ha
    refine ⟨hn, Or.inl ha, hA, by rw [hB]; exact id, hO, fun _ _ => by rw [hB]; exact .zero⟩

end Targets

end
