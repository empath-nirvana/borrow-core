import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Prelude
import Support.Model.Walks

/-!
# Support — Model — Flattening

`[about ours]`.  Validity and lowering: the pointwise facts behind Lemmas 6.7, 6.10 and 6.30, and the union of two memories.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `dom(ρ₁ ◐ ρ₂) = dom(ρ₁) ∪ dom(ρ₂)`, pointwise: a composite is undefined at
`ℓ` exactly when both operands are.
`[about ours: the step "unfolding ○, dom(ρ₁ ○ ρ₂) = dom(ρ₁) ∪ dom(ρ₂)" of
`[TR]` Lemma 6.30's proof, at the schema]` -/
theorem ResU.Comp.eq_none_iff {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) (l : Loc) :
    ρ.get l = none ↔ (ρ₁.get l = none ∧ ρ₂.get l = none) := by
  rcases ResU.Comp.get h l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, -⟩ <;> rw [e, e₁, e₂] <;> simp

/-- Where one operand is undefined, the composite is the other operand. -/
theorem ResU.Comp.get_of_left_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    (e : ρ₁.get l = none) : ρ.get l = ρ₂.get l := by
  rcases ResU.Comp.get h l with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
  · rw [f, f₂]
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f, f₂]
  · rw [f₁] at e; exact absurd e (by simp)

/-- The mirror of `ResU.Comp.get_of_left_none`. -/
theorem ResU.Comp.get_of_right_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    (e : ρ₂.get l = none) : ρ.get l = ρ₁.get l := by
  rcases ResU.Comp.get h l with ⟨f₁, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, -⟩ |
      ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
  · rw [f, f₁]
  · rw [f, f₁]
  · rw [f₂] at e; exact absurd e (by simp)
  · rw [f₂] at e; exact absurd e (by simp)

/-- `ex(ρ₁)_● ● ex(ρ₂)_●` is `imm`-free: the side condition 6.35's proof hands
to 6.30.
`[about ours: `ResU.ImmFree` is `[TR]` p. 5's `ρ|imm = ∅` written pointwise;
this closes it under `●`]` -/
theorem ResU.ImmFree.compS {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.ImmFree) (h₂ : ρ₂.ImmFree) : ρ.ImmFree :=
  ResU.ImmFree.comp (fun ψ₁ ψ₂ ψ hc k₁ _ => CellU.compS_ne_imm ψ₁ ψ₂ ψ hc k₁) h h₁ h₂

/-- `m₁ ∪ m₂` at one location: `m₁` off `dom(m₂)`, `m₂` off `dom(m₁)`, and on
the overlap the value both give. -/
def OptUnion {Val : Type} : Option Val → Option Val → Option Val → Prop
  | none, none, o => o = none
  | some v, none, o => o = some v
  | none, some v, o => o = some v
  | some v₁, some v₂, o => v₁ = v₂ ∧ o = some v₁

/-- `m₁ ∪ m₂ = m` on memories `Loc ⇀ Val`, location by location.
`[about ours: the union on the right of `[TR]` Lemma 6.7, as a graph (G4)]` -/
def MemUnion (m₁ m₂ m : Loc → Option Val) : Prop := ∀ l, OptUnion (m₁ l) (m₂ l) (m l)

/-- The union is single-valued. -/
theorem MemUnion.functional {m₁ m₂ m m' : Loc → Option Val}
    (h : MemUnion m₁ m₂ m) (h' : MemUnion m₁ m₂ m') : m = m' := by
  refine funext fun l => ?_
  have k := h l
  have k' := h' l
  cases e₁ : m₁ l <;> cases e₂ : m₂ l <;> rw [e₁, e₂] at k k'
  · rw [k, k']
  · rw [k, k']
  · rw [k, k']
  · rw [k.2, k'.2]

/-- Erasing a composition gives the union of the erasures, for a cell-level
composition over a common value. -/
theorem optUnion_map_erase {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.erase = ψ₂.erase ∧ ψ.erase = ψ₁.erase)
    {o₁ o₂ o : Option (CellU Loc Val)} (h : OptComp C o₁ o₂ o) :
    OptUnion (o₁.map CellU.erase) (o₂.map CellU.erase) (o.map CellU.erase) := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none => have e : o = none := h; subst e; exact rfl
      | some ψ => have e : o = some ψ := h; subst e; exact rfl
  | some ψ₁ =>
      cases o₂ with
      | none => have e : o = some ψ₁ := h; subst e; exact rfl
      | some ψ₂ =>
          obtain ⟨χ, e, hc⟩ := h
          obtain ⟨g₁, g₂⟩ := hC _ _ _ hc
          subst e
          exact ⟨g₁, congrArg some g₂⟩

end BoCa.Fig16

end
