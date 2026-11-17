import Core.Chain.SI.HeapN
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
def FrameKept (ρf : WRes) (μ' : Heap) : Prop :=
  ∀ (l : Loc) (ψ : CellU Loc Val), ρf.FlatAt l ψ → μ' l = some ψ.erase

/-- A `○`-composite holds a cell, of the same erasure, wherever its left part does. -/
theorem compR_get_erase {σ₁ σ₂ σ : WRes} (h : ResU.CompR σ₁ σ₂ σ) {l : Loc}
    {ψ : CellU Loc Val} (e : σ₁.get l = some ψ) :
    ∃ ψ', σ.get l = some ψ' ∧ ψ'.erase = ψ.erase := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁
    obtain rfl := Option.some.inj f₁
    exact ⟨_, f, rfl⟩
  · rw [e] at f₁; exact absurd f₁ (by simp)
  · rw [e] at f₁
    obtain rfl := Option.some.inj f₁
    exact ⟨χ, f, CellU.CompR.erase_left hC⟩

/-- **A part's flattening is covered by the composite's**, at the same erasure
(`⦇ρ₁ ● ρ₂⦈ = ⦇ρ₁⦈ ○ ⦇ρ₂⦈`, `flat_compR`). -/
theorem flatAt_cover {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid) {l : Loc}
    {ψ : CellU Loc Val} (h : ρ₁.FlatAt l ψ) : ∃ ψ', ρ.FlatAt l ψ' ∧ ψ'.erase = ψ.erase := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨σ₁, σ₂, h₁, -, hR⟩ := flat_compR hc hσ
  obtain ⟨σ', hσ', hg⟩ := h
  obtain rfl := ResU.Flat.functional hσ' h₁
  obtain ⟨ψ', e', he⟩ := compR_get_erase hR hg
  exact ⟨ψ', ⟨σ, hσ, e'⟩, he⟩

/-- **G passes to a part.** -/
theorem FrameKept.of_compS {ρ₁ ρ₂ ρ : WRes} {μ : Heap} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ρ.Valid) (h : FrameKept ρ μ) : FrameKept ρ₁ μ := by
  intro l ψ hψ
  obtain ⟨ψ', hψ', he⟩ := flatAt_cover hc hv hψ
  rw [h l ψ' hψ', he]

/-- A world keeps its own lowering. -/
theorem frameKept_lower {ρ : WRes} {μ : Heap} (hl : ResU.Lower ρ μ) : FrameKept ρ μ := by
  intro l ψ hψ
  obtain ⟨σ, hσ, hμ⟩ := hl
  obtain ⟨σ', hσ', hg⟩ := hψ
  obtain rfl := ResU.Flat.functional hσ' hσ
  rw [hμ l, hg]
  rfl

/-- **G at the start**: the frame of a world agrees with the memory the world lowers to. -/
theorem frameKept_of_lower {ρf ρ fρ : WRes} {μ : Heap} (hc : ResU.CompS ρf ρ fρ)
    (hl : ResU.Lower fρ μ) : FrameKept ρf μ :=
  (frameKept_lower hl).of_compS hc (by obtain ⟨σ, hσ, -⟩ := hl; exact ⟨σ, hσ⟩)


end BoCa.Fig16.LogRel.Core.Chain.SI
end
