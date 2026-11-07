import Core.Chain.Fam836N

/-!
# Picking a leaf of a range, for writes through a `mut` slice  `[spec §9]`

Core's `sliceReplaceM_compatX` (`Core/SliceOps.lean`) is `arrReplace_compatX` with the picked leaf
a `Mut @a A` borrow: the Mut Anti-Frame at the leaf (`wpTS_M_antiFrameX`) opens the cell for the
load and the store, and the leaf is sealed again holding the new element. On the chain the
anti-frame is `erwp_M_antiFrame` at the view, the leaf's cell at its view lifetime
(`consistentX_get`), as in `withswap_compatN`; the steps inside it are `arrReplace_compatN`'s,
each at the index it costs (the anti-frame's postcondition reads the cell's member at the index of
the end). This file holds the pick (`sepRange_pickW`); `sliceReplaceM_compatN` is in
`FamOpsKW835N`.
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

/-- **The leaf at `ℓ + i`, with the rest of the range framed** (`sepRange_pick`), the range
rebuilt at any weaker predicate: the rest is read at the weaker one. -/
theorem sepRange_pickW {P : Loc → WProp} {ℓ : Loc} {n i : Nat} (hi : i < n) {ρ : WRes}
    (h : sepRange P ℓ n ρ) :
    ∃ ρi ρr, ResU.CompS ρi ρr ρ ∧ P (ℓ + i) ρi ∧
      ∀ Q : Loc → WProp, (∀ m ρ, P m ρ → Q m ρ) →
        ∀ σ ρ', ResU.CompS σ ρr ρ' → Q (ℓ + i) σ → sepRange Q ℓ n ρ' := by
  have hn : n = i + ((n - i - 1) + 1) := by omega
  rw [hn] at h
  obtain ⟨ρa, ρb, hab, ha, ρi, ρc, hic, hi', hc⟩ := sepRange_split h
  obtain ⟨ρr, hr, hρ⟩ := compS_lcomm hic hab
  refine ⟨ρi, ρr, hρ, hi', fun Q hPQ σ ρ' hσ hP => ?_⟩
  obtain ⟨σc, hσc, hρ'⟩ := compS_lcomm hr hσ
  rw [hn]
  exact sepRange_append hρ' (sepRange_mono' hPQ ha) ⟨σ, ρc, hσc, hP, sepRange_mono' hPQ hc⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
