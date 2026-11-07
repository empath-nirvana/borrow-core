import Core.Chain.SI.FrameResN
import Core.Chain.SI.WpN
import Core.FrameRules

/-!
# The Imm Frame (`[TR]` 6.64) at the step index

`rwp_I_frame`: `wpTS_I_frameX`'s proof at `rwp`. The run of `e` under the frame is the inner
run at the world holding the fictional `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, over the same memory
(6.26 under a frame), so the inner `rwp` speaks of the same run at the same index; at its end
the printed proof runs unchanged, with 6.29, 6.38 and 6.39 at the index (`six38_steps_one_twoN`,
`six38N`, `six39N`).

The payload `P̂` is a parameter, as printed (`wpTS_I_frameX` fixes it at `vC⟦T⟧δ`); the proof
uses of it exactly what it uses of `vC`: that it is inside `vShape T δ` (`hPshape`, the record's
shape) and stable along `Ext` (`hPloc`). The imm cell is pinned by `↭`'s `imm` clause, so `Φ`
is the caller's throughout.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`[TR]` Theorem 6.64 (Imm Frame) at the step index**:

    ℓ ↦ v ⋆ P̂(ls)(v) ⋆ (⋔α. ∀ ls′ ⊇_α ls. Imm α P̂ ─⋆ rwpₙ(e){[α] (ℓ ↦ v ─⋆ P̂(v) ─⋆ Q̂)})
      ⊨  rwpₙ(e){Q̂}
-/
theorem rwp_I_frame {Φ : LocFam} (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (hadm : AdmWf T δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, Ext ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    (e : Expr) (ls : List SRec) (Q : PostN) {n : Nat}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) {ρ : WRes}
    (hH2 : (ptoOwn l v ⋆ P ls v ⋆
        fresh (fun α ρ => ∀ ls', AddAt ls ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
          (ptoImmS l α ls' P ─⋆
            rwp (ℍ := ℍ) Φ (fun k ls'' v' => box α (ptoOwn l v ─⋆ (P ls'' v ─⋆ Q k ls'' v')))
              n ls' e) ρ)) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  classical
  intro ρf sρ ps μ hH3 hsρ hT htg hI hlow hfd jr μ' e' hj hrun
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ P ls v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4, taken also below every tag of the list
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓γ) with hAdef
  have hAγ : A ⊏ γ := lt_of_le_of_lt inf_le_right (Life.down_sqsubset γ)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_le_of_lt inf_le_left (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  -- H10 and H11
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  -- the "fictional" `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, well formed by H10
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  -- H12-H17: the compatibility block
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρi := ResU.six34 hlPcell hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρi := ResU.six34 hlPcell (ResU.hash_symm hlPf)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb ρi).mpr hH13.1
  have hH17 : ResU.Hash ρf BI :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  -- the worlds at the two ends of the frame step
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- the record and its lineage
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  have hshape : vShape T δ v ρP := hPshape ls ρP hPv
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  obtain ⟨eR, heR, -, -⟩ := frame_ex hclP (ResU.CompS.comm hFBl) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := p) hshape hadm heR
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
  -- entry: `TWNC.immFrame`, and the tags
  have hTin : TWNC fρ (p :: ps) (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TWNC.immFrame T δ houtP hT hadm hclP (ResU.CompS.comm hFBl) hshape
      (ResU.CompS.comm hFBi) hvfρ hds
  obtain ⟨hFLnew, hFLold⟩ :=
    frameLife_frame T δ hvsρ hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBi) hTI
  have htgin : Tagged fρ (p :: ps) ls' := by
    intro x hx
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨d, hd, rfl⟩ | hx
    · exact ⟨p, List.mem_cons_self, DescR.refl p, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨p, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · obtain ⟨q, hq, hqd, hfq⟩ := htg x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hqd, hFLold q hq x.2 hfq⟩
  -- the borrow handed to the body is at the caller's list (`⊐ α`)
  have hcell : ptoImmS l A ls' P ρi := by
    refine ⟨LSet.singleton A, v, ρP, houtP, ls, rfl, hPv, le_refl _, fun x => ?_⟩
    refine ⟨fun hx => ⟨hadd.1 x hx, hAtag x hx⟩, fun ⟨hx, hxA⟩ => ?_⟩
    by_contra hn
    have := hadd.2 x hx hn
    rw [this] at hxA
    exact lt_irrefl _ hxA
  -- H18: the wand, at the fictional borrow, at the list with the frame's records
  have hrec : ∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ :=
    ⟨p, by rw [hls'def, rsOf_frameList]; exact List.mem_cons_self, rfl, rfl, rfl⟩
  have hwpBI := hwand ls' hadd hrec ρi BI hcell hBI
  -- the same memory, by 6.26 under a frame (6.8)
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
  obtain ⟨hval, hprog⟩ :=
    hwpBI ρf fρ (p :: ps) μ hH17 h4 hTin htgin
      (hI.of_sub fun r hr => by rw [hls'def]; simp [frameList, hr])
      hlowin hfd jr μ' e' hj hrun
  refine ⟨fun v' hv' => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'',
    h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ := hval v' hv'
  -- H24 and H25
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H27
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  -- H26: 6.29 with H11 and H12 and H21, then "by H24, `ℓ ∉ dom(ρ′)`"
  obtain ⟨hGsplit, hGiH, hGc⟩ :=
    six38_steps_one_twoN hlPcell hH12 hρ'p houtb houtρ' hBI h9 h10
  -- H28: 6.38 with H12 and H27 and H11 and H24 and H22 and H21
  obtain ⟨G₀, hG₀, hH28⟩ :=
    six38N hlPcell hH12 hρ'p houtb houtρ' h11 hBI h9 h10
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  -- `ρ⁺ = ρ⁺/ℓ ● ρᵢ`
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
  have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
  have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
  -- H29-H33: the second compatibility block
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρp)
  obtain ⟨hPDρ', -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'lPh, hPDlP⟩ := ResU.Hash.split hGsplit hH28
  have hflP : ResU.Hash ρf ρlP := ResU.hash_symm hlPf
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' ρlP).mpr hρ'lPh.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'lPh hflP hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hPDρ' hρ'lPh hPDlP hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ :=
    (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ :=
    (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- and at the other end of the run
  obtain ⟨FP, hFP, hFPi⟩ :=
    (ResU.CompS.assoc fρ' (ρp.del l) ρi fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' ρlP (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨D₁, hD₁, hDlP⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) ρlP RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : π.del l = D₁ := ResU.CompS.functional hGsplit hD₁
  obtain ⟨FPD, hFPD, hFPDlP⟩ :=
    (ResU.CompS.assoc ρf (π.del l) ρlP FRP).mp ⟨RP, hDlP, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : π.del l = FP₁ := ResU.CompS.functional hGsplit hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPDlP.1, FRP, hFPDlP, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPDlP hFPlH).mp h7
  -- H35: `ρ ↭ ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)`, by 6.39 with H12 and H28 and H21
  obtain ⟨w₁, w₂, hw₁, hw₂, hupdw⟩ := six39N hclP hH12 hH28 hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  obtain rfl : RP = w₂ := ResU.CompS.functional hDlP hw₂
  -- G6: `ρ⁺/ℓ` is still own-free
  have hno : BoLo.NoOwn (ρp.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((ρp.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (ρp.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11] at hcc
          simp at hcc
  -- the inner run's list has the frame's records; `p` is one of its records proper
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr (hadd.1 x hx),
     fun x hx hn => hadd.2 x ((hls'' x).mp hx) hn⟩
  obtain ⟨aF, haF⟩ := agW_of_valid hvfρ'p
  -- the frame cell `ρᵢ` sits in the final inner world, with its witness `ρ_P̂(v)`
  have hρiF : ResU.Le ρi fρ'p := ⟨FP, ResU.CompS.comm hFPi⟩
  obtain ⟨ζl, tl, eζl, htl, hAl⟩ := ag_ls_of_le hρiF haF (ResU.single_get_self _ _)
    (CellU.lsOf_immOf _ _ _ _) (show (LSet.singleton A).mem A from rfl)
  have hpps : p ∉ ps := by
    intro hp
    obtain ⟨ψ, eψ, -⟩ := hTI.2.1 p hp aW haW
    have Wl : sρ.get l = some (CellU.ownOf v) :=
      (ResU.CompS.get_right_of_ne_imm hFBl (ResU.CompS.get_left_of_ne_imm hclP
        (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
    exact ex_ag_disjoint hvsρ heW haW (ExS.get_of_ne_imm heW Wl (by simp)) eψ
  have hp'' : p ∈ ps'' := (hps'' p).mpr List.mem_cons_self
  obtain ⟨α', hα'⟩ := hT''.linLife p hp''
  have hαA : A = α' := frameLife_eq hα' haF eζl htl hAl
  subst hαA
  -- H36: the callback's wand, at the cell and the payload it gets back (`ext_add`)
  have hPv'' : P ls'' v ρP := hPloc ls ls'' ρP (ext_add hls''add houtP) hPv
  obtain ⟨X, hX, hXR⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
  have hQ'' : Q (n - jr) ls'' v' R := (hwand' _ X rfl hX) ρP R hPv'' hXR
  -- …carried back to the caller's list (`ext_drop`): `R` holds no view at `p`'s lineage
  have hRα : R.InStratum A := (outlives_comp hR A).mpr ⟨houtρ', houtlP⟩
  have hicpR : ∀ m, ICpAt aF R m := by
    intro m
    have hρ' : ICpAt aF ρ' m :=
      icpAt_trans (icpAt_right (ResU.CompS.toCompR h2) m)
        (icpAt_trans (icpAt_left (ResU.CompS.toCompR h6) m) (icpAt_agW haF m))
    obtain ⟨ψl, eψl, kψl, wψl, rψl⟩ := compS_get_right' hFPi (ResU.single_get_self _ _)
    obtain ⟨sl, hsl, hψl⟩ := CellU.imm_eta (kψl.trans (CellU.kind_immOf _ _ _ _))
    rw [hψl] at eψl
    obtain ⟨e₀, a₀, -, ha₀, icp₀⟩ := escrow_icp haF eψl
    have hwl : ψl.wit = ρP := wψl.trans (CellU.wit_immOf _ _ _ _)
    rw [hwl] at ha₀
    have hρP : ICpAt aF ρP m := icpAt_trans (icpAt_agW ha₀ m) (icp₀ m)
    exact icpAt_comp (ResU.CompS.toCompR hR) hρ'
      (icpAt_comp (ResU.CompS.toCompR hclP)
        (icpAt_of_immFree (fun x ψ e => by
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; simp) m) hρP)
  have hRl : ∀ ψ : CellU Loc Val, R.get p.le = some ψ → ψ.kind ≠ Kind.imm := by
    intro ψ eψ
    obtain ⟨ψ₁, eψ₁, kψ₁, -⟩ := compS_get_right' hR
      ((ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _) (by simp)).2)
    rw [eψ] at eψ₁; cases Option.some.inj eψ₁
    rw [kψ₁]; simp
  have hkeep : ∀ r ∈ rsOf ls'', Rel r R → r ∈ rsOf ls := by
    intro r hr hrel
    obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    have ht' := (hls'' _).mp ht
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at ht'
    rcases ht' with h | ⟨d, hd, h⟩ | h
    · cases h
      exact (not_rel_lineage hα' haF hicpR hRα hRl (DescR.refl p) hrel).elim
    · cases h
      obtain ⟨q, hq, hqd⟩ := (hds _).mp hd
      exact (not_rel_lineage hα' haF hicpR hRα hRl ⟨q, hqd⟩ hrel).elim
    · exact mem_rsOf.mpr ⟨t, h⟩
  have hQls : Q (n - jr) ls v' R := hQ (n - jr) ls'' ls v' R (ext_drop hls''add hRα hkeep) hQ''
  -- exit: `TWNC.immEnd` at `p`, back to the caller's records
  have hTout : TWNC FRP ps (rsOf ls) :=
    TWNC.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) hvFRP
      (fun r' => ⟨fun h => ⟨(hps'' r').mpr (List.mem_cons_of_mem _ h),
        fun e => hpps (e ▸ h)⟩, fun ⟨h, hne⟩ => by
          rcases List.mem_cons.mp ((hps'' r').mp h) with e | h'
          · exact absurd e hne
          · exact h'⟩)
      hTI.2.2.2.2.2.2.1
  obtain ⟨aOut, haOut⟩ := agW_of_valid hvFRP
  have backOut : ∀ a', AgW FRP a' → ∀ m, ICpAt aF a' m := by
    intro a' ha' m
    obtain ⟨aσ, aY, eR', aR, pR, heR', -, hpR, hcp, hσY, hRY⟩ :=
      end_walks (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) haF ha'
    exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have htgout : Tagged FRP ps ls := by
    intro x hx
    obtain ⟨q, hq, hqd, hfq⟩ := htg'' x ((hls'' x).mpr (hadd.1 x hx))
    have hqp : q ≠ p := by
      rintro rfl
      have := frameLife_eq hfq haF eζl htl hAl
      have hxA := hAtag x hx
      rw [← this] at hxA
      exact lt_irrefl _ hxA
    have hq' : q ∈ ps := by
      rcases List.mem_cons.mp ((hps'' q).mp hq) with e | h
      · exact absurd e hqp
      · exact h
    exact ⟨q, hq', hqd, frameLife_back hfq (fun a' ha' =>
      ⟨aF, haF, backOut a' ha' _, fun m _ => backOut a' ha' m⟩)⟩
  exact ⟨R, ρp.del l, FR, FRP, RP, ps, ls,
    ResU.hash_symm hfR, hFR, hPDFR, hFRP, hmem₂, hRP,
    hupdw, hno, hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, hQls⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
