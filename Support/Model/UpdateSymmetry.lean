import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Update

/-!
# Support — Model — UpdateSymmetry

`[about ours]`.  `↭` is symmetric, and `ρ ↭ ρ` read off validity.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.UpdV.symm {ρ₁ ρ₂ : ResU Loc Val} (h : ρ₁.UpdV ρ₂) : ρ₂.UpdV ρ₁ :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- At `[TR]` p. 5's guarded `↭`, `ρ ↭ ρ` is `✓ρ` (`docs/adjudications.md` D3).
`[about ours: Lemma 6.47 at the guarded row]` -/
theorem ResU.updV_self_iff (ρ : ResU Loc Val) : ρ.UpdV ρ ↔ ρ.Valid :=
  ⟨fun h => h.2.1, fun h => ⟨ResU.Upd.refl ρ, h, h⟩⟩

end BoCa.Fig16

end
