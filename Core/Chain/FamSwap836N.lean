import Core.Chain.FamSlice836N

/-!
# Swapping two leaves of a `mut` slice at `SemJN₀`  `[spec §9]`

Core's `sliceSwapM_compatX` (`Core/SliceOps.lean`): both indices in range, the two picked leaves
are `Mut @a A` borrows. At one leaf (`i = j`) one Mut Anti-Frame opens the cell, which is read
twice and written twice; at two leaves each is opened by its own Mut Anti-Frame
(`sepRange_pick2N`), the two contents are read and written crosswise, and both leaves are sealed
again, each holding the other's content. On the chain each anti-frame is `erwp_M_antiFrame` at the
view, the leaf's cell at its view lifetime (`consistentX_get`), as in `sliceReplaceM_compatN₀`; the
inner anti-frame runs at the outer one's table (`erwp_mono`: the empty table stops nowhere). The
steps inside are taken at the index each one costs, and the content moved into the other cell keeps
its witness, which is in that cell's stratum (the leaf's uniformity clause).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- **Two distinct leaves of a range, `i < j`** (Core's `sepRange_pick2R`), the range rebuilt at
any weaker predicate: the rest is read at the weaker one. -/
theorem sepRange_pick2RW {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i < j) (hj : j < n)
    {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → Q (ℓ + i) σi →
          Q (ℓ + j) σj → sepRange Q ℓ n ρ' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
  obtain ⟨A, B, hAB, hA, ρj, C, hjC, hPj, hC⟩ := sepRange_split h
  obtain ⟨ρi, Ar, hiA, hPi, hbackA⟩ := sepRange_pickW hij hA
  obtain ⟨X, hX, hρ⟩ := compS_reassoc hiA hAB
  obtain ⟨Y, hY, hX'⟩ := compS_lcomm hjC hX
  refine ⟨ρi, ρj, Y, X, hX', hρ, hPi, hPj, fun Q hPQ σi σj σ₁ ρ' h₁ h₂ hPi' hPj' => ?_⟩
  obtain ⟨B', hB', hσ₁⟩ := compS_lcomm hY h₁
  obtain ⟨A', hA', hρ'⟩ := compS_reassoc' hσ₁ h₂
  exact sepRange_append hρ' (hbackA Q hPQ σi A' hA' hPi')
    ⟨σj, C, hB', hPj', sepRange_mono' hPQ hC⟩

/-- `sepRange_pick2RW` at two distinct leaves in either order (Core's `sepRange_pick2N`). -/
theorem sepRange_pick2NW {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i ≠ j) (hi : i < n)
    (hj : j < n) {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → Q (ℓ + i) σi →
          Q (ℓ + j) σj → sepRange Q ℓ n ρ' := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact sepRange_pick2RW hlt hj h
  · obtain ⟨ρj, ρi, ρr, ρ₁, h₁, h₂, hPj, hPi, hback⟩ := sepRange_pick2RW hgt hi h
    obtain ⟨ρ₁', h₁', h₂'⟩ := compS_lcomm h₁ h₂
    refine ⟨ρi, ρj, ρr, ρ₁', h₁', h₂', hPi, hPj, fun Q hPQ σi σj σ₁ ρ' k₁ k₂ kPi kPj => ?_⟩
    obtain ⟨σ₁', k₁', k₂'⟩ := compS_lcomm k₁ k₂
    exact hback Q hPQ σj σi σ₁' ρ' k₁' k₂' kPj kPi

/-- `swapV`'s body after the first β step. -/
theorem swap_body₁ (v : Val) :
    Expr.subst 0 v (.letpair (.var 0) (.letpair (.var 0)
      (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
        (.case (.app (.val (.prim .idx)) (.pair (.var 4) (.var 1))) slSwapCellsE (.var 5))
        (.var 4)))) =
      .letpair (.val v) (.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
          (.case (.app (.val (.prim .idx)) (.pair (.var 4) (.var 1))) slSwapCellsE (.var 5))
          (.var 4))) := by
  simp [Expr.subst, slSwapCellsE]

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
