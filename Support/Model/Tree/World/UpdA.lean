import Support.Model.Tree.World.UpdXW

/-!
# `↭` along the walks: a given-up `imm` view accounted through its ancestor  `[spec §62]`

Departure D4, design (b), read with `[TR]` 6.48's ancestor technique (`docs/new-core/scope-806.md`).
`UpdA` relates a run's start `ρ` and end `ρ′` beside the end world `fρ′`. An `imm` cell is kept
(`XCell`) or given up to the end world (`CellAbs`), as in `UpdXW`. A `mut` cell is also read
through the `imm` cell it sits beneath (`Beneath`: an `imm` cell of the start's flattening at `m`
whose witness's `⦇−⦈_○` carries it): a start `mut` cell may leave with its ancestor when the end
world absorbs the ancestor, and an end `mut` cell may be one that sat beneath a start ancestor
(`AgWT.nonimm_beneath_imm` gives every non-`imm` cell of an aliasable walk such an ancestor).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-- **`ξ` sits beneath the `imm` cell `ζ` at `m` of `σ`, at `n`**: `ζ`'s witness's `⦇−⦈_○`
(`ex(χ)_○ ○ ag(χ)`) carries `ξ` at `n`. The shape `AgWT.nonimm_beneath_imm` returns. -/
def Beneath (σ : TRes K) (m : BoCa.Loc) (ζ : TCell K) (n : BoCa.Loc) (ξ : TCell K) : Prop :=
  σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧
    ∃ ev av p, ExRT ζ.wit ev ∧ AgWT ζ.wit av ∧ ResUT.CompR ev av p ∧ p.get n = some ξ

/-- **`↭` at `l`, along the walks.** `σ`, `σ′`, `τw`: the flattenings of the start, the end and
the end world; `E`, `E′`: the masks. -/
def XOptA (Θ : LocTy) (E E' : BoCa.Loc → Prop) (σ : TRes K) (σ' τw : TRes K') (l : BoCa.Loc) :
    Prop :=
  (∀ ψ, σ.get l = some ψ → ψ.kind ≠ Kind.own → ¬ E l → ¬ E' l ∧
    ((∃ ψ', σ'.get l = some ψ' ∧ XCell Θ ψ ψ') ∨
     (∃ χ, τw.get l = some χ ∧ CellAbs Θ ψ χ) ∨
     (ψ.kind = Kind.mut ∧ ∃ m ζ χ, ¬ E m ∧ Beneath σ m ζ l ψ ∧ τw.get m = some χ ∧
        CellAbs Θ ζ χ))) ∧
  (∀ ψ', σ'.get l = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' l → ¬ E l ∧
    ((∃ ψ, σ.get l = some ψ ∧ (XCell Θ ψ ψ' ∨ CellSub Θ ψ ψ')) ∨
     (ψ'.kind = Kind.mut ∧ ∃ m ζ ξ, Beneath σ m ζ l ξ ∧ XCell Θ ξ ψ')))

/-- **`UpdA`**: the start `ρ`, the end `ρ′`, the end world `fρ′`, `↭` along the walks at every
location. -/
def UpdA (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' fρ' : TRes K') : Prop :=
  ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
    ∀ l, XOptA Θ E E' σ σ' τw l

/-- The old clause implies `UpdA` at any valid end world. -/
theorem UpdX.toA {Θ : LocTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K} {ρ' fρ' : TRes K'}
    (h : UpdX Θ E E' ρ ρ') (hv : ResUT.Valid fρ') : UpdA Θ E E' ρ ρ' fρ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨τw, hτw⟩ := hv
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := (hx l).1 ψ e hk hE
    exact ⟨h₁, Or.inl h₂⟩
  · obtain ⟨h₁, ψ, e₀, hc⟩ := (hx l).2 ψ' e hk hE
    exact ⟨h₁, Or.inl ⟨ψ, e₀, Or.inl hc⟩⟩

/-- `UpdXW` implies `UpdA`. -/
theorem UpdXW.toA {Θ : LocTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K} {ρ' fρ' : TRes K'}
    (h : UpdXW Θ E E' ρ ρ' fρ') : UpdA Θ E E' ρ ρ' fρ' := by
  obtain ⟨σ, σ', τw, hσ, hσ', hτw, hx⟩ := h
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · obtain ⟨h₁, h₂ | h₂⟩ := (hx l).1 ψ e hk hE
    · exact ⟨h₁, Or.inl h₂⟩
    · exact ⟨h₁, Or.inr (Or.inl h₂)⟩
  · obtain ⟨h₁, ψ, e₀, hc⟩ := (hx l).2 ψ' e hk hE
    exact ⟨h₁, Or.inl ⟨ψ, e₀, hc⟩⟩

end BoCa.Fig16.Tree.Wp

end
