import Core.Chain.SI.RebStopN
import Core.Chain.SI.StopFrameN

/-!
# 6.150 across a stop: what bounds the resume frame

A condition on the list of tagged records a continuation is resumed at reads nothing of the
frame. `resume_frame_short` builds, from any typed world at any list, a typed world at the same
records and the same list whose frame holds one more cell
`ℓ ↦ mut(A′, v, ∅, ⊤)`, at any `A′`: a handler that lends a cell of its own at a fresh
`A′ ⊏ β` and resumes `κ` inside the lend. A `mut` lend adds no record (`TWN.mutFold`), so no
condition on the list can see it. At that world both of `TW`'s stratum premises of the reborrow
fail: `TW.reb`'s `StratumLe W β` at the re-entry, and `TW.rebEnd`'s `W′.InStratum β` at the
return of the resumed segment (`resume_frame_not_stratumLe`, `resume_frame_not_inStratum`).

`TWN` (`SI/TWN.lean`) reads its reborrow premises at records only (`RebRecLe`, `RebEndRec`), and
the handler's cell is in no record's lineage.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeVar)

/-- The stored predicate of the handler's cell: anything. -/
def predTop (A : Life) : Val → SPropS Loc Val A := fun _ _ => True

/-- The handler's `mut` cell at `A`, holding `v` and nothing else. -/
def shortCell (A : Life) (v : Val) : CellU Loc Val :=
  CellU.mutOf A v PMap.empty (ResU.inStratum_empty A) (predTop A) trivial

/-- **A resume frame may hold a cell at any lifetime.** From a typed, tagged world `W` at the
records `ps`, `rs` and the list `ls`, with a location its memory misses: `W ● ℓ ↦ mut(A, v, ∅, ⊤)`
is a typed, tagged world at the same records and list, over the memory with `ℓ ↦ v` (6.141 then
6.66's fold). The extra cell is outside every resource `W` holds, so it is a frame extension:
`rwpG` quantifies over it at every resource it quantifies over at `W`. -/
theorem resume_frame_short {W : WRes} {ps rs : List FrameRec} {ls : List SRec} {μ : Heap}
    {l : Loc} (hT : TWN W ps rs) (htg : Tagged W ps ls) (hL : ResU.Lower W μ) (hμ : μ l = none)
    (v : Val) (A : Life) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TWN W' ps rs ∧ Tagged W' ps ls ∧
      ResU.Lower W' (BoCa.BoLo.Heap.upd μ l v) ∧ ¬ W'.InStratum A := by
  obtain ⟨τ, hτ, hval⟩ := id hL
  have hWl : W.get l = none := get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hμ)
  obtain ⟨W1, hc⟩ := (ResU.compS_defined_iff W (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hWl)
  obtain ⟨σ', hσ', hH, hLσ'⟩ := hash_compS_own (ρf := PMap.empty) (ResU.comp_empty_left W) hL hμ hc
  obtain rfl : W1 = σ' := ResU.CompS.functional (ResU.comp_empty_left W1) hσ'
  have hv1 : ResU.Valid W1 := hash_valid_comp hH hσ'
  -- 6.141: the allocation
  have hT1 : TWN W1 ps rs := TWN.alloc hT hL hμ hc hv1
  have htg1 : Tagged W1 ps ls := tagged_of_ag (fun a ha => alloc_ag hc ha) htg
  -- 6.66's fold: `ℓ ↦ own(v) ● ∅` to `ℓ ↦ mut(A, v, ∅, ⊤)`
  have hown : ResU.CompS (PMap.empty : WRes) (ResU.single l (CellU.ownOf v))
      (ResU.single l (CellU.ownOf v)) := ResU.comp_empty_left _
  have hHown : ResU.Hash W (ResU.single l (CellU.ownOf v)) := ⟨hc.1, W1, hc, hv1⟩
  have hHmut : ResU.Hash W (ResU.single l (shortCell A v)) := (ResU.six24 hown).mpr hHown
  obtain ⟨W', hW', hvW'⟩ := hHmut.2
  have hvm : ResU.Valid (ResU.single l (shortCell A v)) := (ResU.Valid.split hW' hvW').2
  have hvo : ResU.Valid (ResU.single l (CellU.ownOf v)) := (ResU.Valid.split hc hv1).2
  have hT' : TWN W' ps rs :=
    TWN.mutFold hT1 (ResU.comp_empty_right _) (ResU.CompS.comm hc) (ResU.CompS.comm hW') hvW'
  have htg' : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.comp_empty_right _) (ResU.CompS.comm hc) (ResU.CompS.comm hW') a).mpr ha)
    htg1
  have hL' : ResU.Lower W' (BoCa.BoLo.Heap.upd μ l v) :=
    (ResU.lower_swap_mut_own hown hvm hvo hW' hHmut hc hHown).mpr hLσ'
  refine ⟨W', hW', hT', htg', hL', fun hA => ?_⟩
  have hk : (shortCell A v).kind ≠ Kind.imm := by
    simp only [shortCell]; exact fun c => Kind.noConfusion c
  have hW'l : W'.get l = some (shortCell A v) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hW') (ResU.single_get_self _ _) hk).2
  have hcon := hA l _ hW'l
  simp only [shortCell] at hcon
  exact lt_irrefl _ hcon

/-- At that world `TW.reb`'s premise fails for every `β` longer than the handler's cell. -/
theorem resume_frame_not_stratumLe {W : WRes} {A β : Life} (hA : A ⊏ β)
    (h : ¬ W.InStratum A) : ¬ StratumLe W β :=
  fun hs => h (hs A hA)

/-- …and `TW.rebEnd`'s, at every such `β`. -/
theorem resume_frame_not_inStratum {W : WRes} {A β : Life} (hA : A ⊏ β)
    (h : ¬ W.InStratum A) : ¬ W.InStratum β :=
  fun hs => h (fun m ψ e => CellU.InStratum.mono hA.le (hs m ψ e))


/-- **The handler's lend, at `TWN`.** At `resume_frame_short`'s world, whose frame holds the
handler's `mut` cell at `A ⊏ β`, `TW.reb`'s premise fails and `TWN.reb`'s holds. -/
theorem resume_frame_rebRecLe {W : WRes} {ps : List FrameRec} {ls : List SRec} {μ : Heap}
    {l : Loc} {β A : Life} (hT : TWN W ps (rsOf ls)) (htg : Tagged W ps ls)
    (hL : ResU.Lower W μ) (hμ : μ l = none) (hβ : ∀ y ∈ ls, y.2 ⊐ β) (hA : A ⊏ β) (v : Val)
    (w₀ : WRes) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TWN W' ps (rsOf ls) ∧
      Tagged W' ps ls ∧ ¬ StratumLe W' β ∧ RebRecLe W' ps w₀ β := by
  obtain ⟨W', hc, hT', htg', -, hnA⟩ := resume_frame_short hT htg hL hμ v A
  exact ⟨W', hc, hT', htg', resume_frame_not_stratumLe hA hnA, rebRecLe_of_tags hT' htg' hβ w₀⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
