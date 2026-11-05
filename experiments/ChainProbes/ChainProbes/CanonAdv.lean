import Core.Chain.SI.RebAcrossC

/-!
# The handler-lend and reborrow re-entry resume worlds at canonical images

* The handler-lend world (`resume_frame_short`): a handler lends a cell of its own at `A′ ⊏ β` and resumes
  the continuation inside the lend. `resume_frame_shortC` builds it at `TWNC`; there the re-entry's
  premise `RebRecLe` holds and the canonical image agrees with the world (`resume_round7C`).
* The reborrow re-entry world (`not_rebReentryAgreeN`): a handler reborrows the record with the other witness
  while the continuation is stored. At `TWNC` that reborrow's image is `canon r β` itself
  (`TWNC.reb`'s premise), and the agreement holds at every `TWNC` world (`cex_canon`,
  `canon_escrowAgree`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeVar)

theorem resume_frame_shortC {W : WRes} {ps rs : List FrameRec} {ls : List SRec} {μ : Heap}
    {l : Loc} (hT : TWNC W ps rs) (htg : Tagged W ps ls) (hL : ResU.Lower W μ) (hμ : μ l = none)
    (v : Val) (A : Life) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TWNC W' ps rs ∧ Tagged W' ps ls ∧
      ResU.Lower W' (BoCa.BoLo.Heap.upd μ l v) ∧ ¬ W'.InStratum A := by
  obtain ⟨τ, hτ, hval⟩ := id hL
  have hWl : W.get l = none := get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hμ)
  obtain ⟨W1, hc⟩ := (ResU.compS_defined_iff W (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hWl)
  obtain ⟨σ', hσ', hH, hLσ'⟩ := hash_compS_own (ρf := PMap.empty) (ResU.comp_empty_left W) hL hμ hc
  obtain rfl : W1 = σ' := ResU.CompS.functional (ResU.comp_empty_left W1) hσ'
  have hv1 : ResU.Valid W1 := hash_valid_comp hH hσ'
  -- 6.141: the allocation
  have hT1 : TWNC W1 ps rs := TWNC.alloc hT hL hμ hc hv1
  have htg1 : Tagged W1 ps ls := tagged_of_ag (fun a ha => alloc_ag hc ha) htg
  -- 6.66's fold: `ℓ ↦ own(v) ● ∅` to `ℓ ↦ mut(A, v, ∅, ⊤)`
  have hown : ResU.CompS (PMap.empty : WRes) (ResU.single l (CellU.ownOf v))
      (ResU.single l (CellU.ownOf v)) := ResU.comp_empty_left _
  have hHown : ResU.Hash W (ResU.single l (CellU.ownOf v)) := ⟨hc.1, W1, hc, hv1⟩
  have hHmut : ResU.Hash W (ResU.single l (shortCell A v)) := (ResU.six24 hown).mpr hHown
  obtain ⟨W', hW', hvW'⟩ := hHmut.2
  have hvm : ResU.Valid (ResU.single l (shortCell A v)) := (ResU.Valid.split hW' hvW').2
  have hvo : ResU.Valid (ResU.single l (CellU.ownOf v)) := (ResU.Valid.split hc hv1).2
  have hT' : TWNC W' ps rs :=
    TWNC.mutFold hT1 (ResU.comp_empty_right _) (ResU.CompS.comm hc) (ResU.CompS.comm hW') hvW'
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

/-- **The handler-lend resume world at `TWNC`.** At the world `resume_frame_shortC` builds (the handler's
`mut` cell at any `A′`, possibly shorter than `β`), the re-entry's premise holds and the canonical
image of every record of the list agrees with the world. -/
theorem resume_round7C {W : WRes} {ps : List FrameRec} {ls : List SRec} {μ : Heap} {l : Loc}
    {β A : Life} (hT : TWNC W ps (rsOf ls)) (htg : Tagged W ps ls) (hL : ResU.Lower W μ)
    (hμ : μ l = none) (hβ : ∀ y ∈ ls, y.2 ⊐ β) (v : Val) {r : FrameRec} (hr : r ∈ rsOf ls)
    (hex : ∃ c, TmplSpec r c) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TWNC W' ps (rsOf ls) ∧
      Tagged W' ps ls ∧ ¬ W'.InStratum A ∧ RebRecLe W' ps r.R β ∧
      ∀ a, AgW W' a → EscrowAgree r.R (canon r β) a := by
  obtain ⟨W', hc, hT', htg', -, hnA⟩ := resume_frame_shortC hT htg hL hμ v A
  exact ⟨W', hc, hT', htg', hnA, rebRecLe_of_tags hT'.toN htg' hβ r.R,
    canon_escrowAgree hT' hr (tmpl_spec hex) β⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
