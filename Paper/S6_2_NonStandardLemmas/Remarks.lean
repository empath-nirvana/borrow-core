import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.CellFacts
import Support.Model.Prelude
import Support.Model.Update

/-!
# [TR] §6.2 — remarks on Definition 6.2

Theorems about `ψ ∼ ψ′` (row 5.65) whose proofs use `[TR]` §6.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `∼` is transitive, as `[TR]` Lemma 6.44's proof asserts: *"imms are required
to be equal and muts are required to have"* the same lifetime and invariant.
`[about ours]` -/
theorem CellU.Sim.trans {ψ₁ ψ₂ ψ₃ : CellU Loc Val} (h₁ : CellU.Sim ψ₁ ψ₂)
    (h₂ : CellU.Sim ψ₂ ψ₃) : CellU.Sim ψ₁ ψ₃ := by
  rcases h₁ with ⟨a, P, hA, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, hC⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · rw [e₂] at e₃
      obtain rfl : a = a' := CellU.mutOf_at e₃
      obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj e₃
      exact Or.inl ⟨a, P, hA, hC⟩
    · exact absurd (e₃.symm.trans e₂) CellU.immOf_ne_mutOf
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, -⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · exact absurd (e₂.symm.trans e₃) CellU.immOf_ne_mutOf
    · rw [e₂] at e₃
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
      exact Or.inr ⟨s, v, χ, hh, e₁, e₄⟩

/-- `[CONF]` Fig. 18b's `↭` is `[TR]` §6's *"`dom(⦇ρ₁⦈|imm,mut) = dom(⦇ρ₂⦈|imm,mut)`
and pointwise `∼`"*, both flattenings named (G4).  `[about ours]` -/
theorem ResU.upd_iff_sim {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val}
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) :
    ResU.Upd ρ₁ ρ₂ ↔ ResU.SimForm σ₁ σ₂ := by
  constructor
  · intro h
    refine ⟨fun l => ⟨?_, ?_⟩, fun l ψ hb => ?_⟩
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h h₁ h₂ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h.symm h₂ h₁ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      exact ResU.sim_of_upd h h₁ h₂ hg hk
  · rintro ⟨hd, hs⟩
    have hback : ∀ (l : Loc) (ψ₂ : CellU Loc Val), σ₂.borrowPart.get l = some ψ₂ →
        ∃ ψ₁, σ₁.get l = some ψ₁ ∧ CellU.Sim ψ₂ ψ₁ := by
      intro l ψ₂ hb₂
      obtain ⟨ψ₁, hb₁⟩ := (hd l).mpr ⟨ψ₂, hb₂⟩
      obtain ⟨ψ₂', hg₂', hsim⟩ := hs l ψ₁ hb₁
      obtain ⟨hg₂, -⟩ := ResU.borrowPart_eq_some.mp hb₂
      rw [hg₂] at hg₂'
      cases Option.some.inj hg₂'
      exact ⟨ψ₁, (ResU.borrowPart_eq_some.mp hb₁).1, hsim.symm⟩
    refine ⟨fun l s v χ hh => ?_, fun l b P => ?_⟩
    · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]
      constructor
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
    · constructor
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₁] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₂ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₂] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₁ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf

end BoCa.Fig16

end
