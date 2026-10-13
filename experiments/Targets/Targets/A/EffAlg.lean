import Mathlib.Logic.Relation

/-!
# System A — the effect algebra (Yoshioka–Sekiyama–Igarashi Def. 3.5, Def. 5.1)

An effect algebra's data and its laws, kept apart, as Yoshioka–Sekiyama–Igarashi (arXiv
2404.16381) define them: Def. 3.5, "⟨Eff(Σ), ⊙, 0⟩ is a partial monoid under ∼", and "Typelike
substitution respecting well-formedness is a homomorphism for ⊙, (−)↑, and ∼"; Def. 5.1, "(1) For
any L, (L)↑ < 0 does not hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠ L′, then (L)↑ < ε′".

None of it mentions BoLo or Core.  Our row forms (`orowAlg`, `closedRowAlg`) are instances, in
`Targets/Instance/Rows.lean`.
-/

namespace Targets.A

/-- An effect algebra's data (Yoshioka–Sekiyama–Igarashi Def. 3.5): labels, effects, variables,
well-formedness under the variables in scope, `⊙` (partial), `0`, `(L)↑`, `∼` and
substitution. -/
structure EffAlg where
  Lab   : Type
  Eff   : Type
  Var   : Type
  /-- `Γ ⊢ ε : Eff`, `Γ` the row variables in scope. -/
  WF    : List Var → Eff → Prop
  WFLab : List Var → Lab → Prop
  /-- `⊙`, partial. -/
  comp  : Eff → Eff → Option Eff
  /-- `0`. -/
  unit  : Eff
  /-- `(L)↑`. -/
  lift  : Lab → Eff
  /-- `∼`. -/
  eqv   : Eff → Eff → Prop
  /-- `subst α S ε` is `ε[S/α]`. -/
  subst : Var → Eff → Eff → Eff

/-- `α ↦ S ⊢ εs : Eff`: the effects are well formed with `α` in scope, and `S` where `α` is. -/
def EffAlg.SubstOK (EA : EffAlg) (α : EA.Var) (S : EA.Eff) (εs : List EA.Eff) : Prop :=
  ∃ Γ₁ Γ₂, (∀ ε ∈ εs, EA.WF (Γ₁ ++ α :: Γ₂) ε) ∧ EA.WF Γ₁ S

/-- **Def. 3.5**: the data form an effect algebra. -/
structure EffAlg.Laws (EA : EffAlg) : Prop where
  -- first bullet: `⊙`, `0` and `(−)↑` preserve well-formedness; `∼` is an equivalence that
  -- preserves it
  comp_wf   : ∀ Γ ε₁ ε₂ ε, EA.WF Γ ε₁ → EA.WF Γ ε₂ → EA.comp ε₁ ε₂ = some ε → EA.WF Γ ε
  unit_wf   : ∀ Γ, EA.WF Γ EA.unit
  lift_wf   : ∀ Γ L, EA.WFLab Γ L → EA.WF Γ (EA.lift L)
  eqv_equiv : Equivalence EA.eqv
  eqv_wf    : ∀ ε₁ ε₂, EA.eqv ε₁ ε₂ → ∀ Γ, (EA.WF Γ ε₁ ↔ EA.WF Γ ε₂)
  -- second bullet: a partial monoid under `∼`
  unit_r : ∀ ε, ∃ ε', EA.comp ε EA.unit = some ε' ∧ EA.eqv ε' ε
  unit_l : ∀ ε, ∃ ε', EA.comp EA.unit ε = some ε' ∧ EA.eqv ε' ε
  assoc  : ∀ ε₁ ε₂ ε₃,
    ((∃ x y, EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y) ∨
     (∃ x y, EA.comp ε₂ ε₃ = some x ∧ EA.comp ε₁ x = some y)) →
    ∃ x y x' y', EA.comp ε₁ ε₂ = some x ∧ EA.comp x ε₃ = some y ∧
      EA.comp ε₂ ε₃ = some x' ∧ EA.comp ε₁ x' = some y' ∧ EA.eqv y y'
  -- third bullet: substitution respecting well-formedness is a homomorphism for `⊙`, `(−)↑`, `∼`
  subst_comp : ∀ α S ε₁ ε₂ ε, EA.SubstOK α S [ε₁, ε₂] → EA.comp ε₁ ε₂ = some ε →
    EA.comp (EA.subst α S ε₁) (EA.subst α S ε₂) = some (EA.subst α S ε)
  subst_lift : ∀ α S L, (∃ Γ₁ Γ₂, EA.WFLab (Γ₁ ++ α :: Γ₂) L ∧ EA.WF Γ₁ S) →
    EA.subst α S (EA.lift L) = EA.lift L
  subst_eqv : ∀ α S ε₁ ε₂, EA.SubstOK α S [ε₁, ε₂] → EA.eqv ε₁ ε₂ →
    EA.eqv (EA.subst α S ε₁) (EA.subst α S ε₂)

/-- `ε₁ < ε₂`: "`ε₁ ⊙ ε ∼ ε₂` for some `ε`". -/
def EffAlg.Sub (EA : EffAlg) (ε₁ ε₂ : EA.Eff) : Prop :=
  ∃ ε x, EA.comp ε₁ ε = some x ∧ EA.eqv x ε₂

/-- Yoshioka–Sekiyama–Igarashi Def. 5.1: the safety conditions of an effect algebra. -/
structure EffAlg.Safe (EA : EffAlg) : Prop where
  c1 : ∀ L, ¬ EA.Sub (EA.lift L) EA.unit
  c2 : ∀ L L' ε ε' x, EA.Sub (EA.lift L) ε → EA.comp (EA.lift L') ε' = some x → EA.eqv x ε →
         L ≠ L' → EA.Sub (EA.lift L) ε'

end Targets.A
