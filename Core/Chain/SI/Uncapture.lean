import Core.Chain.SI.IStopN
import Core.Chain.SI.Erwp0

/-!
# Capture and uncapture: the world at a lend's entry and at its end in a later segment

`[TR]` 6.64's proof changes the world twice: at the entry, `TWNC.immFrame` (the lent cell becomes
`imm`, its record joins the records proper); at the end, `TWNC.immEnd`. In `rwpG_I_frameG` both
happen inside one run. A lend left open at a stop is ended in a later segment, under a frame the
resumer chose, so the two world changes are stated here apart from any run:

* `capture_world` is the entry of `rwpG_I_frameG`, verbatim, with the new record added to the
  records the computation owns.
* `uncapture_world` is the end of `rwpG_I_frameG` (`TWNC.immEnd`, the memory by 6.26 under a
  frame, the tags by `end_walks`), for a lend whose payload is empty, at a resumed segment: the
  resource holds the lent location's cell at the top level and the rest is compatible with
  `ℓ ↦ own(v)` (what 6.29 and 6.38 give at the borrowed run's end, `SI/CaptureScope.lean`), and
  the frame is compatible with `ℓ ↦ own(v)` (what the resumer guarantees). The record must be a
  record proper, which ownership gives; the tagged list loses the record's entries.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub)

/-! ### Small facts -/

/-- An `LSet` whose members are exactly `A` is `{A}`. -/
theorem lset_eq_singleton {s : LSet} {A : Life} (h₁ : s.mem A) (h₂ : ∀ x, s.mem x → x = A) :
    s = LSet.singleton A := by
  have hj : s.join = A := h₂ _ s.join_mem
  have hm : s.meet = A := h₂ _ s.meet_mem
  have hmem : s.mem = (LSet.singleton A).mem := by
    funext x
    exact propext ⟨fun h => h₂ x h, fun h => by
      have : x = A := h
      subst this; exact h₁⟩
  cases s
  simp only at hj hm hmem
  subst hj hm
  simp only [LSet.singleton] at hmem ⊢
  subst hmem
  rfl

/-- Deleting a location from the three resources of a composition. -/
theorem ResU.CompS.del {a b c : WRes} (h : ResU.CompS a b c) (l : Loc) :
    ResU.CompS (a.del l) (b.del l) (c.del l) := by
  refine ⟨fun m ψ₁ ψ₂ e₁ e₂ => ?_, fun m => ?_⟩
  · by_cases hm : m = l
    · subst hm; rw [ResU.del_get_self] at e₁; cases e₁
    · rw [ResU.del_get_ne _ hm] at e₁ e₂
      exact h.1 m ψ₁ ψ₂ e₁ e₂
  · by_cases hm : m = l
    · subst hm; rw [ResU.del_get_self, ResU.del_get_self, ResU.del_get_self]; rfl
    · rw [ResU.del_get_ne _ hm, ResU.del_get_ne _ hm, ResU.del_get_ne _ hm]
      exact h.2 m

/-- A record with an empty escrow has no proper sub-record in its lineage. -/
theorem descR_empty {p d : FrameRec} (hR : p.R = PMap.empty) (h : DescR p d) : d = p := by
  obtain ⟨path, hp⟩ := h
  cases hp with
  | nil => rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, eζ, -⟩ := hsub
      rw [hR, PMap.empty_get] at eζ
      cases eζ

/-! ### The entry -/

/-- **A lend's entry** (`rwpG_I_frameG` from the entry on to the borrowed run, verbatim): under
any frame, the world with `ℓ ↦ own(v) ● ρ_P ● ρ_b` becomes the world with `ρ_b ● ℓ ↦ imm(α, v,
ρ_P)`, the record `p` joins the records proper and the records the computation owns, the list
becomes `frameList p ds α ls`, and the memory is kept. -/
theorem capture_world (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    {A : Life} {ρP ρlP ρb ρ : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hshape : vShape T δ v ρP) {ds : List FrameRec}
    (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d)
    {ρf sρ : WRes} {ps O psF : List FrameRec} {ls : List SRec} {μ : BoCa.BoLo.Heap}
    (hH3 : ResU.Hash ρf ρ) (hsρ : ResU.CompS ρf ρ sρ) (hS : Split ps O psF)
    (hT : TWNC sρ ps (rsOf ls)) (htg : Tagged sρ ps ls) (hlow : ResU.Lower sρ μ) :
    ∃ BI fρ, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI ∧
      ResU.Hash ρf BI ∧ ResU.CompS ρf BI fρ ∧
      Split (⟨l, v, ρP, T, δ⟩ :: ps) (⟨l, v, ρP, T, δ⟩ :: O) psF ∧
      TWNC fρ (⟨l, v, ρP, T, δ⟩ :: ps) (rsOf (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)) ∧
      Tagged fρ (⟨l, v, ρP, T, δ⟩ :: ps) (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) ∧
      ResU.Lower fρ μ := by
  classical
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP := ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρi := ResU.six34 hlPcell hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρi := ResU.six34 hlPcell (ResU.hash_symm hlPf)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb ρi).mpr hH13.1
  have hH17 : ResU.Hash ρf BI :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  have hTin : TWNC fρ (p :: ps) (rsOf (frameList p ds A ls)) := by
    rw [rsOf_frameList]
    exact TWNC.immFrame T δ houtP hT hadm hclP (ResU.CompS.comm hFBl) hshape
      (ResU.CompS.comm hFBi) hvfρ hds
  obtain ⟨hFLnew, hFLold⟩ :=
    frameLife_frame T δ hvsρ hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBi) hTI
  have htgin : Tagged fρ (p :: ps) (frameList p ds A ls) := by
    intro x hx
    simp only [frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨d, hd, rfl⟩ | hx
    · exact ⟨p, List.mem_cons_self, DescR.refl p, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨p, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · obtain ⟨q, hq, hqd, hfq⟩ := htg x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hqd, hFLold q hq x.2 hfq⟩
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBI : ResU.Valid BI := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvi : ResU.Valid ρi := (ResU.Valid.split hBI hvBI).2
  have hFBiH : ResU.Hash FB ρi :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm
      (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mpr hlow
  have hpps : p ∉ ps := by
    intro hp
    obtain ⟨ψ, eψ, -⟩ := hTI.2.1 p hp aW haW
    have Wl : sρ.get l = some (CellU.ownOf v) :=
      (ResU.CompS.get_right_of_ne_imm hFBl (ResU.CompS.get_left_of_ne_imm hclP
        (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
    exact ex_ag_disjoint hvsρ heW haW (ExS.get_of_ne_imm heW Wl (by simp)) eψ
  refine ⟨BI, fρ, hBI, hH17, h4, ⟨fun q => ?_, fun q hq hqF => ?_⟩, hTin, htgin, hlowin⟩
  · rw [List.mem_cons, List.mem_cons, hS.1 q]; tauto
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact hpps ((hS.1 _).mpr (Or.inr hqF))
    · exact hS.2 q hq hqF

/-! ### The end, in a later segment -/

/-- **A lend's end in a resumed segment**, for a lend whose payload is empty: the record `p` a
record proper, the resource `S ● ℓ ↦ imm(s, v, ∅)` with `S` holding nothing at `ℓ` and compatible
with `ℓ ↦ own(v)`, the frame compatible with `ℓ ↦ own(v)`. The world becomes `ρ_f ● S ● ℓ ↦
own(v)` (`TWNC.immEnd`), the memory is kept (6.26 under a frame), `p` leaves the records proper,
and its entries leave the list (the tags of the others by `end_walks`, as `rwpG_I_frameG`'s exit
reads them). -/
theorem uncapture_world {l : Loc} {v : Val} {T : VTy} {δ : LSub} {s : LSet}
    {hs : ResU.InStratum s.join (PMap.empty : WRes)} {ρf S ρres W : WRes} {ps : List FrameRec}
    {ls : List SRec} {μ : BoCa.BoLo.Heap}
    (hp : (⟨l, v, PMap.empty, T, δ⟩ : FrameRec) ∈ ps)
    (hres : ResU.CompS S (ResU.single l (CellU.immOf s v PMap.empty hs)) ρres)
    (hW : ResU.CompS ρf ρres W) (hT : TWNC W ps (rsOf ls)) (htg : Tagged W ps ls)
    (hlow : ResU.Lower W μ)
    (hfo : ResU.Hash ρf (ResU.single l (CellU.ownOf v)))
    (hSo : ResU.Hash S (ResU.single l (CellU.ownOf v))) (ls' : List SRec)
    (hls' : ∀ x, x ∈ ls' ↔ x ∈ ls ∧ x.1 ≠ ⟨l, v, PMap.empty, T, δ⟩) :
    ∃ (ρres' W' : WRes) (ps' : List FrameRec),
      ResU.CompS S (ResU.single l (CellU.ownOf v)) ρres' ∧ ResU.Hash ρf ρres' ∧
      ResU.CompS ρf ρres' W' ∧
      (∀ q, q ∈ ps' ↔ q ∈ ps ∧ q ≠ ⟨l, v, PMap.empty, T, δ⟩) ∧
      TWNC W' ps' (rsOf ls') ∧ Tagged W' ps' ls' ∧ ResU.Lower W' μ := by
  classical
  set p : FrameRec := ⟨l, v, PMap.empty, T, δ⟩ with hpdef
  set ρl : WRes := ResU.single l (CellU.immOf s v PMap.empty hs) with hρl
  set ρo : WRes := ResU.single l (CellU.ownOf v) with hρo
  have hTI := hT.inv
  have hvW : ResU.Valid W := by obtain ⟨σ, hσ, -⟩ := hlow; exact ⟨σ, hσ⟩
  -- `W = (ρ_f ● S) ● ℓ ↦ imm(s, v, ∅)`
  obtain ⟨Y, hY, hYW⟩ := (ResU.CompS.assoc ρf S ρl W).mp ⟨ρres, hres, hW⟩
  have hfres : ResU.Hash ρf ρres := ⟨hW.1, W, hW, hvW⟩
  have hfS : ResU.Hash ρf S := (ResU.Hash.split hres (ResU.hash_symm hfres)).1 |> ResU.hash_symm
  have hoY : ResU.Hash ρo Y :=
    ResU.hash_of_pairwise (ResU.hash_symm hfo) hfS (ResU.hash_symm hSo) hY
  obtain ⟨W', hW'c, hvW'⟩ := (ResU.hash_symm hoY).2
  have hX' : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes) ρo :=
    ResU.comp_empty_right _
  have hcW : ResU.CompS ρl Y W := ResU.CompS.comm hYW
  have hp' : p ∈ ps := hp
  -- the records and the list after the end
  obtain ⟨ps', hps'⟩ : ∃ ps' : List FrameRec, ∀ q, q ∈ ps' ↔ q ∈ ps ∧ q ≠ p :=
    ⟨ps.filter (fun q => decide (q ≠ p)), fun q => by simp⟩
  have hR : p.R = PMap.empty := rfl
  have hrs' : ∀ d, d ∈ rsOf ls' ↔ ∃ q ∈ ps', DescR q d := by
    intro d
    constructor
    · intro hd
      obtain ⟨x, hx⟩ := mem_rsOf.mp hd
      obtain ⟨hxl, hxp⟩ := (hls' _).mp hx
      obtain ⟨q, hq, hqd⟩ := (hTI.2.2.2.2.2.2.1 d).mp (mem_rsOf.mpr ⟨x, hxl⟩)
      have hqp : q ≠ p := by
        rintro rfl
        exact hxp (descR_empty hR hqd)
      exact ⟨q, (hps' q).mpr ⟨hq, hqp⟩, hqd⟩
    · rintro ⟨q, hq, hqd⟩
      obtain ⟨hq, hqp⟩ := (hps' q).mp hq
      have hdrs : d ∈ rsOf ls := (hTI.2.2.2.2.2.2.1 d).mpr ⟨q, hq, hqd⟩
      obtain ⟨x, hx⟩ := mem_rsOf.mp hdrs
      have hdp : d ≠ p := by
        rintro rfl
        exact hqp (hT.properRoot p hp' q hq hqd)
      exact mem_rsOf.mpr ⟨x, (hls' _).mpr ⟨hx, hdp⟩⟩
  have hTout : TWNC W' ps' (rsOf ls') :=
    TWNC.immEnd p hT hp' hcW hX' (ResU.CompS.comm hW'c) hvW' hps' hrs'
  -- the tags of the records left
  obtain ⟨aF, haF⟩ := agW_of_valid hvW
  have backOut : ∀ a', AgW W' a' → ∀ m, ICpAt aF a' m := by
    intro a' ha' m
    obtain ⟨aσ, aY, eR', aR, pR, heR', -, hpR, hcp, hσY, hRY⟩ :=
      end_walks hcW hX' (ResU.CompS.comm hW'c) haF ha'
    exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have htgout : Tagged W' ps' ls' := by
    intro x hx
    obtain ⟨hxl, hxp⟩ := (hls' x).mp hx
    obtain ⟨q, hq, hqd, hfq⟩ := htg x hxl
    have hqp : q ≠ p := by
      rintro rfl
      exact hxp (descR_empty hR hqd)
    exact ⟨q, (hps' q).mpr ⟨hq, hqp⟩, hqd, frameLife_back hfq (fun a' ha' =>
      ⟨aF, haF, backOut a' ha' _, fun m _ => backOut a' ha' m⟩)⟩
  -- the memory, by 6.26 under a frame
  have hvl : ResU.Valid ρl := by
    obtain ⟨σ, hσ⟩ := hvW
    exact (ResU.Valid.split hcW ⟨σ, hσ⟩).1
  have hYl : ResU.Hash Y ρl := ⟨hYW.1, W, hYW, hvW⟩
  have hlow' : ResU.Lower W' μ :=
    (ResU.lower_swap_imm_own (compS_empty_left ρo) hvl (ResU.valid_single_own l v) hYW hYl
      hW'c (ResU.hash_symm hoY)).mp hlow
  -- the resource after the end
  obtain ⟨ρres', hρres'⟩ := (ResU.compS_defined_iff S ρo).mpr hSo.1
  obtain ⟨x, hx, hW''⟩ := (ResU.CompS.assoc ρf S ρo W').mpr ⟨Y, hY, hW'c⟩
  cases ResU.CompS.functional hx hρres'
  refine ⟨ρres', W', ps', hρres', ⟨hW''.1, W', hW'', hvW'⟩, hW'', hps', hTout,
    htgout, hlow'⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
