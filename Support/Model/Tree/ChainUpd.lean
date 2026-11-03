import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Tree.Port.Cells
import Support.Model.Tree.ChainRes

/-!
# `↭` along `chainEquiv`

`[spec §62]`. Row 5.27 at the tree-stratified carrier (`Tree/Port/Cells.lean`) is the printed row
at `WCactus.chain`: `chain_upd_iff`, `chain_updV_iff`. The `imm` clause reads a cell by its
lifetime set, value and witness, which `ΦU` keeps (`ΦU_immOf`, `ΨU_immOf`). The `mut` clause
fixes a lifetime and an invariant: a printed `mut(β, …, P̂)` is the image of the tree's
`mut({β}, …, P̂ ∘ ΨU⁻¹)` (`ΨU_mutOf`), and a tree `mut(β̄, …, P̂)` at the chain the image of the
printed `mut(⊔β̄, …, P̂ ∘ ΦU⁻¹)` (`ΦU_mutOf`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type}

/-! ### The `imm` clause -/

theorem chain_updImm_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.UpdImm ρ₁ ρ₂ ↔ ResU.UpdImm (ρ₁.map ΦU) (ρ₂.map ΦU) := by
  constructor
  · intro H l s v χ h
    rw [← ΦU_ΨU (CellU.immOf s v χ h), ← chain_flatAt_iff, ← chain_flatAt_iff, ΨU_immOf]
    exact H l _ v _ _
  · intro H l s v χ h
    rw [chain_flatAt_iff, chain_flatAt_iff, ΦU_immOf]
    exact H l _ v _ _

/-! ### The `mut` clause -/

/-- The tree's invariant `P̂ ∘ ΨU⁻¹` of a printed `mut` cell's image. -/
def predΨ {b : Life} (P : Val → SPropS Loc Val b) :
    Val → SPropST Loc Val WCactus.chain (TSet.single b) :=
  fun w r => ∃ (r₀ : ResU Loc Val) (h₀ : r₀.InStratum b), r₀.map ΨU = r.val ∧ P w ⟨r₀, h₀⟩

/-- The printed invariant `P̂ ∘ ΦU⁻¹` of a tree `mut` cell's image. -/
def predΦ {s : TSet} (P : Val → SPropST Loc Val WCactus.chain s) : Val → SPropS Loc Val s.jn :=
  fun w r => ∃ (r₀ : ResUT Loc Val WCactus.chain) (h₀ : r₀.InStratum s),
    r₀.map ΦU = r.val ∧ P w ⟨r₀, h₀⟩

/-- A printed `mut` cell at `⦇ρ⦈(ℓ)`, with value and witness free, is the image of the tree's. -/
theorem chain_flatAt_mut_printed {ρ : ResUT Loc Val WCactus.chain} {l : Loc} {b : Life}
    {P : Val → SPropS Loc Val b} :
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ResU.FlatAt (ρ.map ΦU) l (CellU.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : ResUT Loc Val WCactus.chain) (h : χ.InStratum (TSet.single b))
        (hw : predΨ P v ⟨χ, h⟩), ρ.FlatAt l (CellUT.mutOf (TSet.single b) v χ h (predΨ P) hw)) := by
  constructor
  · rintro ⟨v, χ, h, hw, fa⟩
    refine ⟨v, χ.map ΨU, ΨU_map_inStratum h, ⟨χ, h, rfl, hw⟩, ?_⟩
    rw [chain_flatAt_iff]
    have e := ΨU_mutOf b v χ h P hw
    rw [← ΦU_ΨU (CellU.mutOf b v χ h P hw), e] at fa
    exact fa
  · rintro ⟨v, χ', h', hw', fa⟩
    obtain ⟨r₀, h₀, e₀, hP⟩ := id hw'
    refine ⟨v, r₀, h₀, hP, ?_⟩
    have e : CellUT.mutOf (TSet.single b) v χ' h' (predΨ P) hw' =
        ΨU (CellU.mutOf b v r₀ h₀ P hP) := by
      rw [ΨU_mutOf]
      exact CellUT.mutOf_congr' rfl e₀.symm _ _ _ _ _ _ fun _ _ _ _ => Iff.rfl
    rw [e, chain_flatAt_iff, ΦU_ΨU] at fa
    exact fa

/-- A tree `mut` cell at `⦇ρ⦈(ℓ)`, with value and witness free, is the image of the printed. -/
theorem chain_flatAt_mut_tree {ρ : ResUT Loc Val WCactus.chain} {l : Loc} {s : TSet}
    [Fact (WCactus.chain.Anti s)] {P : Val → SPropST Loc Val WCactus.chain s} :
    (∃ (v : Val) (χ : ResUT Loc Val WCactus.chain) (h : χ.InStratum s) (hw : P v ⟨χ, h⟩),
        ρ.FlatAt l (CellUT.mutOf s v χ h P hw)) ↔
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.jn) (hw : predΦ P v ⟨χ, h⟩),
        ResU.FlatAt (ρ.map ΦU) l (CellU.mutOf s.jn v χ h (predΦ P) hw)) := by
  constructor
  · rintro ⟨v, χ, h, hw, fa⟩
    refine ⟨v, χ.map ΦU, ΦU_map_inStratum h, ⟨χ, h, rfl, hw⟩, ?_⟩
    rw [chain_flatAt_iff, ΦU_mutOf] at fa
    exact fa
  · rintro ⟨v, χ', h', hw', fa⟩
    obtain ⟨r₀, h₀, e₀, hP⟩ := id hw'
    refine ⟨v, r₀, h₀, hP, ?_⟩
    have e : CellU.mutOf s.jn v χ' h' (predΦ P) hw' =
        ΦU (CellUT.mutOf s v r₀ h₀ P hP) := by
      rw [ΦU_mutOf]
      exact CellU.mutOf_congr' rfl e₀.symm _ _ _ _ _ _ fun _ _ _ _ => Iff.rfl
    rw [e, ← chain_flatAt_iff] at fa
    exact fa

theorem chain_updMut_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.UpdMut ρ₁ ρ₂ ↔ ResU.UpdMut (ρ₁.map ΦU) (ρ₂.map ΦU) := by
  constructor
  · intro H l b P
    rw [chain_flatAt_mut_printed, chain_flatAt_mut_printed]
    exact H l (TSet.single b) (predΨ P)
  · intro H l s _ P
    rw [chain_flatAt_mut_tree, chain_flatAt_mut_tree]
    exact H l s.jn (predΦ P)

/-! ### `↭` -/

/-- **`↭` at the chain is the printed `↭`** ([CONF] Fig. 18b's form, row 5.62). -/
theorem chain_upd_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.Upd ρ₁ ρ₂ ↔ ResU.Upd (ρ₁.map ΦU) (ρ₂.map ΦU) :=
  and_congr chain_updImm_iff chain_updMut_iff

/-- **`↭` at the chain is the printed `↭`**, guarded by `✓` ([TR] p. 5, row 5.27). -/
theorem chain_updV_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.UpdV ρ₁ ρ₂ ↔ ResU.UpdV (ρ₁.map ΦU) (ρ₂.map ΦU) :=
  and_congr chain_upd_iff (and_congr chain_valid_iff chain_valid_iff)

theorem chain_exclPart (ρ : ResUT Loc Val WCactus.chain) :
    ρ.exclPart.map ΦU = ResU.exclPart (ρ.map ΦU) := chain_restrictOn ρ _

theorem chain_borrowPart (ρ : ResUT Loc Val WCactus.chain) :
    ρ.borrowPart.map ΦU = ResU.borrowPart (ρ.map ΦU) := chain_restrictOn ρ _

end BoCa.Fig16.Tree

end
