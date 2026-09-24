import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Dynamics.Machine
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Notation

/-!
# Support — Model — Propositions

`[about ours]`.  The propositions of `[TR]` p. 6 as used by §6.2: entailment, `emp`, the outlives relation `@ρ ⊐ α` and the `wp` row at the unguarded `↭`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- `P ⊨ Q`. -/
def Entails (P Q : SPropU Loc Val) : Prop := ∀ ρ, P ρ → Q ρ

/-- `P ⫤⊨ Q`. -/
def BiEntails (P Q : SPropU Loc Val) : Prop := Entails P Q ∧ Entails Q P

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo

@[inherit_doc] scoped infix:25 " ⊨ " => Entails

@[inherit_doc] scoped infix:25 " ⫤⊨ " => BiEntails

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

theorem emp_empty : (emp : SPropU Loc Val) PMap.empty := ⟨rfl, trivial⟩

/-- `∅ ● ρ = ρ` — `[TR]` Lemma 6.4 with the operands transposed, which Lemma 6.2
licenses.  `[as printed]` -/
theorem compS_empty_left (ρ : ResU Loc Val) : ResU.CompS PMap.empty ρ ρ :=
  ResU.CompS.comm (ResU.comp_empty_right ρ)

theorem eq_of_compS_empty_left {ρ₂ ρ : ResU Loc Val} (h : ResU.CompS PMap.empty ρ₂ ρ) :
    ρ = ρ₂ :=
  ResU.CompS.functional h (compS_empty_left ρ₂)

/-- `P ⋆ (Q ⋆ R) ⊨ (P ⋆ Q) ⋆ R`, used by `[TR]` 6.65's proof before 6.112.
`[about ours: the converse of `[TR]`
6.91, which prints one direction]` -/
theorem sep_assoc' (P Q R : SPropU Loc Val) : (P ⋆ (Q ⋆ R)) ⊨ (P ⋆ Q) ⋆ R := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hp, ρ₃, ρ₄, hc₂, hq, hr⟩
  obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ₁ ρ₃ ρ₄ ρ).mp ⟨ρ₂, hc₂, hc⟩
  exact ⟨y, ρ₄, hy₂, ⟨ρ₁, ρ₃, hy₁, hp, hq⟩, hr⟩

/-- A bound on `@ρ` gives `@ρ ⊐ α`. -/
theorem outlives_of_atLife {ρ : ResU Loc Val} {a α : Life} (ha : ρ.AtLife a)
    (h : a ⊐ α) : Outlives ρ α := ResU.inStratum_of_atLife ha h

theorem Outlives.mono {ρ : ResU Loc Val} {α β : Life} (h : β ⊑ α) (ho : Outlives ρ α) :
    Outlives ρ β := ResU.InStratum.mono h ho

/-- The lifetime of a strict composite bounds each operand's and is bounded by
them — `[TR]` Lemma 6.45 read at `[α]`'s own conjunct.  `[as printed]` -/
theorem outlives_comp {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) (α : Life) :
    Outlives ρ α ↔ (Outlives ρ₁ α ∧ Outlives ρ₂ α) := by
  constructor
  · intro hρ
    constructor
    · intro l ψ₁ e₁
      rcases h.get l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
      · rw [e₁] at f₁; exact absurd f₁ (by simp)
      · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ l _ f
      · rw [e₁] at f₁; exact absurd f₁ (by simp)
      · rw [e₁] at f₁; cases Option.some.inj f₁
        exact ((CellU.CompS.inStratum hC α).mp (hρ l _ f)).1
    · intro l ψ₂ e₂
      rcases h.get l with ⟨-, f₂, -⟩ | ⟨χ, -, f₂, -⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, -, f₂, f, hC⟩
      · rw [e₂] at f₂; exact absurd f₂ (by simp)
      · rw [e₂] at f₂; exact absurd f₂ (by simp)
      · rw [e₂] at f₂; cases Option.some.inj f₂; exact hρ l _ f
      · rw [e₂] at f₂; cases Option.some.inj f₂
        exact ((CellU.CompS.inStratum hC α).mp (hρ l _ f)).2
  · rintro ⟨h₁, h₂⟩ l ψ e
    rcases h.get l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
    · rw [e] at f; exact absurd f (by simp)
    · rw [e] at f; cases Option.some.inj f; exact h₁ l _ f₁
    · rw [e] at f; cases Option.some.inj f; exact h₂ l _ f₂
    · rw [e] at f; cases Option.some.inj f
      exact (CellU.CompS.inStratum hC α).mpr ⟨h₁ l _ f₁, h₂ l _ f₂⟩

theorem ptoAny_of_own (l : Loc) (v : Val) : ptoOwn l v ⊨ ptoAny l := fun _ h => ⟨_, h⟩

/-- `ℓ ↦M_α P̂` holds of a `mut` cell at `ofS Q̂` for the cell's own invariant
`Q̂`. -/
theorem ptoMut_of_cell (l : Loc) (α b : Life) (hb : α ⊑ b) (v : Val)
    (σ : ResU Loc Val) (h : σ.InStratum b) (Q : Val → SPropS Loc Val b)
    (hw : Q v ⟨σ, h⟩) :
    ptoMut l α (ofS Q) (ResU.single l (CellU.mutOf b v σ h Q hw)) :=
  ⟨b, v, σ, h, Q, hw, hb, rfl, rfl⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- The composite `#` asserts is defined is valid, wherever it is named.
`[about ours: the second conjunct of the printed `#`, read at a named
composite]` -/
theorem hash_valid_comp {ρ₁ ρ₂ σ : WRes} (h : ResU.Hash ρ₁ ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ σ) : ResU.Valid σ := by
  obtain ⟨x, hx, hv⟩ := h.2
  cases ResU.CompS.functional hx hc
  exact hv

/-- `ρ₁ # ρ₂` gives `✓ρ₁` and `✓ρ₂` — `[TR]` Lemma 6.10 at the composite `#`
asserts is valid.  `[as printed]` (6.10, at the bundled `#`) -/
theorem hash_valid {ρ₁ ρ₂ : WRes} (h : ResU.Hash ρ₁ ρ₂) :
    ResU.Valid ρ₁ ∧ ResU.Valid ρ₂ := by
  obtain ⟨σ, hσ, hv⟩ := h.2
  exact ResU.Valid.split hσ hv

/-- The two readings of `↭` agree inside the `wp` row (`docs/adjudications.md`
D3).  `[about ours: the two printed `↭`s, read inside the printed
row]` -/
theorem wp_updV_iff_upd (e : Expr) (Q : Val → WProp) (ρ : WRes) :
    wp e Q ρ ↔ wpU e Q ρ := by
  constructor
  · intro hw ρf hf
    obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA, hB, hC⟩ := hw ρf hf
    exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA.1, hB, hC⟩
  · intro hw ρf hf
    obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA, hB, hC⟩ := hw ρf hf
    obtain ⟨-, hp'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
    exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      ⟨hA, (hash_valid hf).2, hash_valid_comp hp' h₉⟩, hB, hC⟩

end BoCa.Fig16.BoLo

end
