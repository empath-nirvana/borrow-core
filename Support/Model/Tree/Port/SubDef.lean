import Support.Model.Tree.Port.ReborrowLowering

/-!
# `⊟` (`[TR]` Definition 6.3, row 5.66) at the tree-stratified carrier

`Paper/S6_2_NonStandardLemmas/Definitions.lean`'s `ResU.SubClause`, `SubClauseL`, `Sub`, `SubL`
and `SubKeep`, read at `CellUT K`, with `Support/Model/Cells.lean`'s lifetime-set difference
(`LSet.Diff`, `LSet.DiffEmpty`) read on `TSet`. Nothing here compares lifetimes: `ᾱ ∖ β̄` is a
set difference, and a nonempty one is a `TSet`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- `ᾱ ∖ β̄ = ū`. -/
def TSet.Diff (s t u : TSet) : Prop := ∀ x, x ∈ u.set ↔ (x ∈ s.set ∧ x ∉ t.set)

/-- `ᾱ ∖ β̄ = ∅`. -/
def TSet.DiffEmpty (s t : TSet) : Prop := ∀ x, x ∈ s.set → x ∈ t.set

variable {Loc Val : Type} {K : WCactus}

/-- The fourth bullet of Definition 6.3, its second sub-case read as a constraint on `ρ″`. -/
def ResUT.SubClause (ρ ρ' ρ'' : ResUT Loc Val K) : Prop :=
  ∀ (l : Loc) (s s' : TSet) (v : Val) (ρi : ResUT Loc Val K)
    (h : ρi.InStratum s) (h' : ρi.InStratum s'),
    ρ.get l = some (CellUT.immOf s v ρi h) →
    ρ'.get l = some (CellUT.immOf s' v ρi h') →
    (TSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : TSet, TSet.Diff s s' u → ¬ TSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u, ρ''.get l = some (CellUT.immOf u v ρi hu))

/-- The same bullet as printed: the second sub-case constrains `ρ′`. -/
def ResUT.SubClauseL (ρ ρ' ρ'' : ResUT Loc Val K) : Prop :=
  ∀ (l : Loc) (s s' : TSet) (v : Val) (ρi : ResUT Loc Val K)
    (h : ρi.InStratum s) (h' : ρi.InStratum s'),
    ρ.get l = some (CellUT.immOf s v ρi h) →
    ρ'.get l = some (CellUT.immOf s' v ρi h') →
    (TSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : TSet, TSet.Diff s s' u → ¬ TSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u, ρ'.get l = some (CellUT.immOf u v ρi hu))

/-- Definition 6.3's bullets without the paragraph below them. -/
def ResUT.Sub (ρ ρ' χ : ResUT Loc Val K) : Prop :=
  ∃ ρ'' : ResUT Loc Val K,
    ρ'.exclPart = PMap.empty ∧
    ResUT.Le ρ'' (G.restrict CellUT.kind ρ Kind.imm) ∧
    (∀ l, (G.restrict CellUT.kind ρ Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l ≠ none) ∧
    ResUT.SubClause ρ ρ' ρ'' ∧
    ResUT.CompS ρ.exclPart ρ'' χ

/-- `ρ ⊟ ρ′ = χ` with the last sub-case literal. -/
def ResUT.SubL (ρ ρ' χ : ResUT Loc Val K) : Prop :=
  ∃ ρ'' : ResUT Loc Val K,
    ρ'.exclPart = PMap.empty ∧
    ResUT.Le ρ'' (G.restrict CellUT.kind ρ Kind.imm) ∧
    (∀ l, (G.restrict CellUT.kind ρ Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l ≠ none) ∧
    ResUT.SubClauseL ρ ρ' ρ'' ∧
    ResUT.CompS ρ.exclPart ρ'' χ

/-- `ρ ⊟ ρ′ = χ`, Definition 6.3: the bullets with the third read through the paragraph below
them. -/
def ResUT.SubKeep (ρ ρ' χ : ResUT Loc Val K) : Prop :=
  ∃ ρ'' : ResUT Loc Val K,
    ρ'.exclPart = PMap.empty ∧
    ResUT.Le ρ'' (G.restrict CellUT.kind ρ Kind.imm) ∧
    (∀ l, (G.restrict CellUT.kind ρ Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l = (G.restrict CellUT.kind ρ Kind.imm).get l) ∧
    ResUT.SubClause ρ ρ' ρ'' ∧
    ResUT.CompS ρ.exclPart ρ'' χ

end BoCa.Fig16.Tree

end
