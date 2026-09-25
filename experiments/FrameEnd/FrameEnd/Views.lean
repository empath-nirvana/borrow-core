import FrameEnd.Projection

/-!
# FrameEnd — Views

Same-lifetime views of a borrowed pointee against `↭` (`[TR]` p. 5, row 5.27), with no typed
world and no `wp`.  A run's `wpTS` post-condition carries `ρ ↭ ρ′ ● ρ⁺`, so every cell of a
view the run returns is a cell of the right-hand side of a `↭` from the resource it started at.

- `imm_view_rejected`: a run that starts at `ℓ ↦ imm(s, v, m ↦ own(u))` cannot end at a
  resource holding an `imm` cell at `m`.  `⦇ρᵢ⦈(m) = own(u)`, the new cell puts an `imm` cell
  at `m` in the flattening of the right-hand side, and `↭`'s `imm` clause (`UpdImm`) asks the
  two flattenings to hold the same `imm` cells.
- `mut_view_rejected`: a run that starts at `ℓ ↦ mut(b, v, ρw, P̂)` with `ρw(m) = own(u)` cannot
  end at a resource holding a `mut` cell at `m`, at any lifetime and predicate.  `⦇ρ⦈(m) =
  own(u)` (the `mut` witness is walked by `ex`), and `↭`'s `mut` clause (`UpdMut`) asks the two
  flattenings to hold `mut` cells at the same locations with the same lifetime and predicate.

Neither lemma mentions a frame: the cell is excluded at the run that would return it, before
any frame ends.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.FrameEnd.Views
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.FrameEnd

theorem comp_get_of_left_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} (e : ρ₁.get l = none) : ρ.get l = ρ₂.get l := by
  rcases ResU.Comp.get h l with ⟨-, e₂, e⟩ | ⟨ψ, e₁, -, -⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, -, -, -⟩
  · rw [e, e₂]
  · rw [e] at e₁; cases e₁
  · rw [e, e₂]
  · rw [e] at e₁; cases e₁

/-- A top-level `imm` cell of `π` puts an `imm` cell in `⦇π⦈` at its location. -/
theorem flat_imm_of_top {π σ : WRes} (hσ : π.Flat σ) {m : Loc} {ψ : CellU Loc Val}
    (e : π.get m = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ : CellU Loc Val, σ.get m = some χ ∧ χ.kind = Kind.imm := by
  obtain ⟨ex, a, hex, ha, hc⟩ := hσ
  obtain ⟨χ, eχ, kχ, -, -⟩ := AgW.get_imm ha e hk
  have hexm : ex.get m = none := by
    cases e' : ex.get m with
    | none => rfl
    | some ζ =>
        have hζ : ζ.kind ≠ Kind.imm := ExS.immFree hex m ζ e'
        have := ResU.CompatS.right_eq_none hc.1 e' hζ
        rw [eχ] at this; cases this
  exact ⟨χ, (comp_get_of_left_none hc hexm).trans eχ, kχ⟩

/-- `⦇ℓ ↦ imm(s, v, m ↦ own(u))⦈(m) = own(u)`, for `ℓ ≠ m`. -/
theorem flat_imm_single_own {l m : Loc} {s : LSet} {v u : Val}
    {hs : (ResU.single m (CellU.ownOf u) : WRes).InStratum s.join} (hlm : l ≠ m) {σ : WRes}
    (hσ : (ResU.single l (CellU.immOf s v (ResU.single m (CellU.ownOf u)) hs) : WRes).Flat σ) :
    σ.get m = some (CellU.ownOf u) := by
  obtain ⟨ex, a, hex, ha, hc⟩ := hσ
  obtain ⟨e', a', p, hex', hag', hp, hσa⟩ := AgW.single_imm_inv ha
  cases ExR.functional hex' (ExW.single_own m u)
  cases AgW.functional hag' (AgW.single_own m u)
  cases ResU.CompR.functional hp (ResU.comp_empty_right _)
  have ham : a.get m = some (CellU.ownOf u) := by
    rw [comp_get_of_left_none hσa (ResU.single_get_ne _ (Ne.symm hlm))]
    exact ResU.single_get_self _ _
  exact ResU.flat_eq_ag_at hex hc ham (by simp)

/-- **`↭`'s `imm` clause rejects a same-lifetime `imm` view of an owned pointee.**  No resource
`π` that `ℓ ↦ imm(s, v, m ↦ own(u))` updates to holds an `imm` cell at `m`, at any lifetime set:
the cell would put an `imm` cell at `m` in `⦇π⦈`, and `⦇ℓ ↦ imm(s, v, m ↦ own(u))⦈(m)` is
`own(u)`. -/
theorem imm_view_rejected {l m : Loc} {s : LSet} {v u : Val}
    {hs : (ResU.single m (CellU.ownOf u) : WRes).InStratum s.join} (hlm : l ≠ m) {π : WRes}
    (hupd : ResU.UpdV (ResU.single l (CellU.immOf s v (ResU.single m (CellU.ownOf u)) hs)) π)
    {ψ : CellU Loc Val} (hπ : π.get m = some ψ) (hk : ψ.kind = Kind.imm) : False := by
  obtain ⟨⟨himm, -⟩, ⟨σ, hσ⟩, ⟨σπ, hσπ⟩⟩ := hupd
  obtain ⟨χ, eχ, kχ⟩ := flat_imm_of_top hσπ hπ hk
  obtain ⟨t, ht, hχ⟩ := CellU.imm_eta kχ
  rw [hχ] at eχ
  obtain ⟨σ', hσ', e'⟩ := (himm m t χ.erase χ.wit ht).mpr ⟨σπ, hσπ, eχ⟩
  rw [ResU.Flat.functional hσ' hσ, flat_imm_single_own hlm hσ] at e'
  cases e'

/-- **`↭`'s `mut` clause rejects a same-lifetime `mut` view of an owned pointee.**  No resource
`π` that `ℓ ↦ mut(b, v, ρw, P̂)` updates to, with `ρw(m) = own(u)`, holds a `mut` cell at `m`,
at any lifetime and predicate: the cell is in `⦇π⦈` (it is exclusive), and `⦇ℓ ↦ mut(b, v, ρw,
P̂)⦈(m)` is `own(u)`, `ex` walking the `mut` witness. -/
theorem mut_view_rejected {l m : Loc} {b b₁ : Life} {v u u₁ : Val} {ρw χ₁ : WRes}
    {hstr : ρw.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρw, hstr⟩}
    {h₁ : χ₁.InStratum b₁} {P₁ : Val → SPropS Loc Val b₁} {hw₁ : P₁ u₁ ⟨χ₁, h₁⟩}
    (hwm : ρw.get m = some (CellU.ownOf u)) {π : WRes}
    (hupd : ResU.UpdV (ResU.single l (CellU.mutOf b v ρw hstr P hw)) π)
    (hπ : π.get m = some (CellU.mutOf b₁ u₁ χ₁ h₁ P₁ hw₁)) : False := by
  obtain ⟨⟨-, hmut⟩, -, ⟨σπ, ex, a, hex, ha, hc⟩⟩ := hupd
  have hexm := ExS.get_of_ne_imm hex hπ (by simp)
  have hσm := (ResU.CompS.get_left_of_ne_imm hc hexm (by simp)).2
  obtain ⟨u₂, χ₂, h₂, hw₂, σ', ⟨ex', a', hex', ha', hc'⟩, e'⟩ :=
    (hmut m b₁ P₁).mpr ⟨u₁, χ₁, h₁, hw₁, σπ, ⟨ex, a, hex, ha, hc⟩, hσm⟩
  have hpath : XPath (ResU.single l (CellU.mutOf b v ρw hstr P hw)) [l] ρw := by
    have := XPath.cons (p := []) (ResU.single_get_self l (CellU.mutOf b v ρw hstr P hw))
      (by simp) (XPath.nil _)
    simpa using this
  have hown := xpath_ex hex' hpath hwm (by simp)
  rw [(ResU.CompS.get_left_of_ne_imm hc' hown (by simp)).2] at e'
  cases e'

end BoCa.Fig16.LogRel.FrameEnd.Views

end
