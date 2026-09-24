import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_3_FrameAndAntiFrame.Lemmas
import Support.Dynamics.Machine
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Model.FrameSurgery
import Support.Model.Notation
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.TypedWorld.Images
import Support.TypedWorld.Invariant
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.RelationFacts
import Support.TypedWorld.World
import Support.TypedWorld.Wp

/-!
# Support — TypedWorld — FrameRules

`[about ours]`.  `[TR]` Theorems 6.64, 6.65 and 6.66 at `wpTS`, with the record list carried.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Theorem 6.64 (Imm Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/
/-- `[TR]` Theorem 6.64 (`Imm Frame`) at the tagged `wpTS`:

    ℓ ↦ v ⋆ 𝒱⟦T⟧(ls)δ(v) ⋆ (⋔α. ∀ ls′ ⊇_α ls. Imm α 𝒱⟦T⟧δ ─⋆ wp_{ls′}(e){[α] (ℓ ↦ v ─⋆
        𝒱⟦T⟧δ(v) ─⋆ Q̂)})  ⊨  wp_{ls}(e){Q̂}

`[variant: P̂ ≔ 𝒱X⟦T⟧δ, the record's type; `hadm` is `TW.immFrame`'s premise; `hQ` (`Q̂`
stable along `Ext`, which at the relation is `vX_local`) is added; the callee is also handed
the record its frame made]` -/
theorem wpTS_I_frameX (l : BoCa.Loc) (T : Ty) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q ls₁ w ρ → Q ls₂ w ρ) :
    Entails
      (ptoOwn l v ⋆ vX wpTS true T ls δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt ls ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
          (ptoImmS l α ls' (fun ls₀ => vX wpTS true T ls₀ δ) ─⋆
            wpTS ls' e (fun ls'' v' => box α (ptoOwn l v ─⋆ (vX wpTS true T ls'' δ v ─⋆ Q ls'' v')))) ρ))
      (wpTS ls e Q) := by
  classical
  intro ρ hH2 ρf sρ ps hH3 hsρ hT htg
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vX wpTS true T ls δ v) _ ρ
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
  have hshape : vShape T δ v ρP := vX_vShape true T hPv
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  obtain ⟨eR, heR, -, -⟩ := frame_ex hclP (ResU.CompS.comm hFBl) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := p) hshape hadm heR
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
  -- entry: `TW.immFrame`, and the tags
  have hTin : TW fρ (p :: ps) (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TW.immFrame T δ houtP hT hadm hclP (ResU.CompS.comm hFBl) hshape
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
  have hcell : ptoImmS l A ls' (fun ls₀ => vX wpTS true T ls₀ δ) ρi := by
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
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBI ρf fρ (p :: ps) hH17 h4 hTin htgin
  -- H24 and H25
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H27
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  -- H26: 6.29 with H11 and H12 and H21, then "by H24, `ℓ ∉ dom(ρ′)`"
  obtain ⟨hGsplit, hGiH, hGc⟩ :=
    ResU.six38_steps_one_two hlPcell hH12 hρ'p houtb houtρ' hBI h9 h10
  -- H28: 6.38 with H12 and H27 and H11 and H24 and H22 and H21
  obtain ⟨G₀, hG₀, hH28⟩ :=
    ResU.six38 hlPcell hH12 hρ'p houtb houtρ' h11 hBI h9 h10
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
  -- H34: the two memories, by 6.26 under a frame (6.8)
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
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mp h5
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
  obtain ⟨w₁, w₂, hw₁, hw₂, hupdw⟩ := ResU.six39 hclP hH12 hH28 hBI hGc h10
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
  have hPv'' : vX wpTS true T ls'' δ v ρP := vX_local true T (ext_add hls''add houtP) hPv
  obtain ⟨X, hX, hXR⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
  have hQ'' : Q ls'' v' R := (hwand' _ X rfl hX) ρP R hPv'' hXR
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
  have hQls : Q ls v' R := hQ ls'' ls v' R (ext_drop hls''add hRα hkeep) hQ''
  -- exit: `TW.immEnd` at `p`, back to the caller's records
  have hTout : TW FRP ps (rsOf ls) :=
    TW.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) hvFRP
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
  exact ⟨R, ρp.del l, FR, FRP, RP, v', μ, μ', ps, ls,
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    hupdw, hno, hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, hQls⟩

/-! ### Theorem 6.65 (Mut Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/
/-- `[TR]` Theorem 6.65 (`Mut Frame`) at the tagged `wpTS`: if `𝒱⟦T⟧δ ⊨ [β]𝒱⟦T⟧δ` at every
list, then

    ℓ ↦ v ⋆ 𝒱⟦T⟧(ls)δ(v) ⋆ (⋔α. Mut α 𝒱⟦T⟧δ ─⋆ wp_{ls}(e){[α] ∀v′. ℓ ↦ v′ ─⋆ 𝒱⟦T⟧δ(v′) ─⋆ Q̂})
      ⊨  wp_{ls}(e){Q̂}

`[variant: P̂ ≔ 𝒱X⟦T⟧δ; the premise `P̂ ⊨ [β]P̂` at every list, the family's reading]` -/
theorem wpTS_M_frameX (l : BoCa.Loc) (T : Ty) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vX wpTS true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ vX wpTS true T ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vX wpTS true T ls₀ δ) ─⋆
          wpTS ls e (fun ls'' v' =>
            box α (all fun w => ptoOwn l w ─⋆ (vX wpTS true T ls'' δ w ─⋆ Q ls'' v')))))
      (wpTS ls e Q) := by
  classical
  intro ρ hH2 ρf sρ ps hH3 hsρ hT htg
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vX wpTS true T ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime shorter than `γ`, `β` and every tag
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓(γ ⊓ β)) with hAdef
  have hAγ : A ⊏ γ :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left)
  have hAβ : A ⊏ β :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right)
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
  -- `P̂ ⊧ [β] P̂` is what puts `P̂`'s resources in `Res_A`
  have hunif : ∀ ls' w σ, vX wpTS true T ls' δ w σ → ResU.InStratum A σ := fun ls' w σ h m ψ hm =>
    CellU.InStratum.mono (le_of_lt hAβ) (hP ls' w σ h m ψ hm)
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A :=
    (fun (w : Val) (r : ResS BoCa.Loc BoCa.Val A) => vX wpTS true T ls δ w r.1) with hQs
  have hofS : BoLo.ofS Qs = fun w => vX wpTS true T ls δ w := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hunif ls w σ h, h⟩⟩
  -- the "fictional" `ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, well formed by H4
  obtain ⟨hwit, hcellm⟩ := ptoMutX_create (l := l) (α := A) (le_refl A) hofS hAtag
    hunif houtP hPv
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP Qs hwit) with hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- H12-H17: the compatibility block
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρm := (ResU.six24 hlPcell).mpr hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρm :=
    (ResU.six24 hlPcell).mpr (ResU.hash_symm hlPf)
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb ρm).mpr hH13.1
  have hH17 : ResU.Hash ρf BM :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBM
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- entry: `TW.mutFold`
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
  -- H18: the wand, at the fictional borrow
  have hwpBM := hwand ρm BM hcellm hBM
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBM ρf fρ ps hH17 h4 hTin htgin
  -- H24 and H25: unfolding `[α]`
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H26: 6.27 -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, hwit'', hsplit''⟩ := ResU.six27 houtb hBM h10
  have hπl : π.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rw [ResU.Comp.get_of_left_none hsplit'' (ResU.del_get_self _ _)]
    exact ResU.single_get_self _ _
  have hkm'' : (CellU.mutOf A v'' χ hχ Qs hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨hρ'ln, hppl⟩ :
      ρ'.get l = none ∧ ρp.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rcases ResU.CompS.get_split_of_ne_imm h9 hπl hkm'' with ⟨hg, -⟩ | ⟨hg, hp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    · exact ⟨hg, hp⟩
  have hpd : ResU.CompS (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) ρp := ResU.del_compS hppl
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) π).mp ⟨ρp, hpd, h9⟩
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' W'').mpr hρ'W''.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'W'' hfm'' hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hρ'PD hρ'W'' hPDW'' hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ := (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ := (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- H33: the two memories, by 6.25 under a frame (6.8)
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBM : ResU.Valid BM := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvmm : ResU.Valid ρm := (ResU.Valid.split hBM hvBM).2
  have hFBmH : ResU.Hash FB ρm :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mp h5
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc fρ' (ρp.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' W'' (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨RPD₁, hRPD₁, hRPDW⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) W'' RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : RPD = RPD₁ := ResU.CompS.functional hRPD hRPD₁
  obtain ⟨FPD, hFPD, hFPDW⟩ :=
    (ResU.CompS.assoc ρf RPD W'' FRP).mp ⟨RP, hRPDW, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : RPD = FP₁ := ResU.CompS.functional hRPD hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hvW'' : ResU.Valid W'' := by
    obtain ⟨-, s, hs, hv⟩ := hH27; exact (ResU.Valid.split hs hv).2
  have hFPmH : ResU.Hash FP (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hFPm.1, fρ'p, hFPm, hvfρ'p⟩
  have hFPWH : ResU.Hash FP W'' := ⟨hFPDW.1, FRP, hFPDW, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFPm hFPmH hFPDW hFPWH).mp h7
  -- H34: `ρ ↭ ρ′ ● ρ''_v ● ℓ ↦ own(v'') ● ρ⁺/ℓ`, by 6.28
  have hvRP : ResU.Valid RP := by
    obtain ⟨-, s, hs, hv⟩ := hH27
    exact ResU.CompS.functional hs hRPDW ▸ hv
  have hupd : ResU.Upd ρ RP :=
    (ResU.six28 hlPcell hW'' hBM hRPDm (ResU.CompS.comm hcρ) hRPDW
      hvBM hvπ hvρ hvRP).mp h10.1
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
  -- exit: `TW.mutUnfold`
  have hTout : TW FRP ps'' (rsOf ls'') :=
    TW.mutUnfold hT'' (ResU.CompS.comm hFPm) (ResU.CompS.comm hW'')
      (ResU.CompS.comm hFPDW) hvFRP
  have htgout : Tagged FRP ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFPDW) (ResU.CompS.comm hFPm) a).mp
      ha) htg''
  -- H35: the callback's wand, at the value the run leaves in the cell, read at the list the
  -- run returns
  have hχv : vX wpTS true T ls'' δ v'' χ :=
    vX_local true T (ext_of_same hls'' χ) (show vX wpTS true T ls δ v'' χ from hwit'')
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : Q ls'' v' R := (hwand' v'' _ y rfl hy₁) χ R hχv hy₂
  exact ⟨R, ρp.del l, FR, FRP, RP, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

/-! ### Theorem 6.66 (Anti Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/
/-- `[TR]` Theorem 6.66 (`Anti Frame`) at the tagged `wpTS`:

    ℓ ↦ Mut α 𝒱⟦T⟧δ ⋆ (∀v. ℓ ↦ v ─⋆ 𝒱⟦T⟧(ls)δ(v) ─⋆
        wp_{ls}(e){∃v. ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ⋆ (ℓ ↦ Mut α 𝒱⟦T⟧δ ─⋆ Q̂)})  ⊨  wp_{ls}(e){Q̂}

`[variant: P̂ ≔ 𝒱X⟦T⟧δ]` -/
theorem wpTS_M_antiFrameX (l : BoCa.Loc) (α : Life) (T : Ty) (δ : LSub) (e : Expr)
    (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails
      (ptoMutS l α ls (fun ls₀ => vX wpTS true T ls₀ δ) ⋆
        (all fun v => ptoOwn l v ─⋆ (vX wpTS true T ls δ v ─⋆
          wpTS ls e (fun ls'' v' => ex fun w =>
            ptoOwn l w ⋆ vX wpTS true T ls'' δ w ⋆
              (ptoMutS l α ls'' (fun ls₀ => vX wpTS true T ls₀ δ) ─⋆ Q ls'' v')))))
      (wpTS ls e Q) := by
  classical
  intro ρ hH1 ρf sρ ps hH2 hsρ hT htg
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  obtain ⟨ρm, ρa, hsplit, hM, hA⟩ := hH1
  obtain ⟨β, v, σP, hstr, Qs, hwit, ls₀, hαβ, hρm, hofS, hls₀, hunif⟩ := hM
  subst hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  obtain ⟨hvm, hva⟩ := ResU.Valid.split hsplit hvρ
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut hvm
  have hmaH : ResU.Hash (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) ρa :=
    ⟨hsplit.1, ρ, hsplit, hvρ⟩
  have haW : ResU.Hash ρa W := (ResU.six24 hW).mp (ResU.hash_symm hmaH)
  have hvW : ResU.Valid W := by
    obtain ⟨-, s, hs, hv⟩ := haW; exact (ResU.Valid.split hs hv).2
  obtain ⟨hmf, haf⟩ := ResU.Hash.split hsplit (ResU.hash_symm hH2)
  have hfW : ResU.Hash ρf W := (ResU.six24 hW).mp (ResU.hash_symm hmf)
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff ρa W).mpr haW.1
  have hfX : ResU.Hash ρf X := ResU.hash_of_pairwise (ResU.hash_symm haf) haW hfW hX
  -- the content handed out, read at the current list
  have hPv : vX wpTS true T ls δ v σP := by
    have h₀ : vX wpTS true T ls₀ δ v σP := by
      have : BoLo.ofS Qs v σP := ⟨hstr, hwit⟩
      rw [hofS] at this; exact this
    exact vX_local true T (ext_stored_current hstr le_rfl hls₀) h₀
  obtain ⟨A₁, hA₁, hA₂⟩ :=
    (ResU.CompS.assoc ρa (ResU.single l (CellU.ownOf v)) σP X).mp
      ⟨W, ResU.CompS.comm hW, hX⟩
  have hwpX := (hA v _ A₁ rfl hA₁) σP X hPv hA₂
  obtain ⟨fρ, h4, hvfρ⟩ := hfX.2
  -- the frame `ρ_f ● ρ_a` the first memory is read over
  obtain ⟨FA, hFA⟩ := (ResU.compS_defined_iff ρf ρa).mpr (ResU.hash_symm haf).1
  obtain ⟨FA₁, hFA₁, hFAmc⟩ :=
    (ResU.CompS.assoc ρf ρa (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) sρ).mp
      ⟨ρ, ResU.CompS.comm hsplit, hsρ⟩
  obtain rfl : FA = FA₁ := ResU.CompS.functional hFA hFA₁
  obtain ⟨FA₂, hFA₂, hFAWc⟩ := (ResU.CompS.assoc ρf ρa W fρ).mp ⟨X, hX, h4⟩
  obtain rfl : FA = FA₂ := ResU.CompS.functional hFA hFA₂
  -- entry: `TW.mutUnfold`
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutUnfold hT (ResU.CompS.comm hFAmc) (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) (ResU.CompS.comm hFAmc) a).mp
      ha) htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpX ρf fρ ps hfX h4 hTin htgin
  obtain ⟨v'', ρl'', rest, hcr, hl'', hrest⟩ := h12
  subst hl''
  obtain ⟨ρPv'', ρb, hcr2, hPv'', hb⟩ := hrest
  -- the content handed back: in `Res_β` by `P̂ : Val → SProp_β`, and written into the
  -- unchanged stored predicate
  have hstr'' : ResU.InStratum β ρPv'' := hunif ls'' v'' ρPv'' hPv''
  obtain ⟨W'', hW''₁, hW''₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v'')) ρPv'' ρb ρ').mp ⟨rest, hcr2, hcr⟩
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hleP : ResU.Le ρPv'' fρ'p :=
    (le_of_compS_right hW''₁).trans ((le_of_compS_left hW''₂).trans
      ((le_of_compS_right h2).trans (le_of_compS_left h6)))
  have hlb : LifeBound ls'' ρPv'' β := lifeBound_of_tagged hvfρ'p htg'' hleP hstr''
  have hls₀'' : ∀ x, x ∈ ls₀ ↔ (x ∈ ls'' ∧ x.2 ⊐ β) := fun x => by
    rw [hls₀ x, hls'' x]
  obtain ⟨hwit'', hcell''⟩ := ptoMutX_write (l := l) (Q := Qs) hαβ hofS hls₀'' hunif hstr''
    hPv'' hlb
  have hW'' : ResU.CompS ρPv'' (ResU.single l (CellU.ownOf v'')) W'' :=
    ResU.CompS.comm hW''₁
  have hvρ' : ResU.Valid ρ' := by
    obtain ⟨-, s, hs, hv⟩ := h1; exact (ResU.Valid.split hs hv).1
  have hvW'' : ResU.Valid W'' := (ResU.Valid.split hW''₂ hvρ').1
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    ResU.valid_single_mut_of_wit hW'' hvW''
  -- H20-H23: the compatibility results for the borrowed resource after the run
  have hW''b : ResU.Hash W'' ρb := ⟨hW''₂.1, ρ', hW''₂, hvρ'⟩
  have hbm'' : ResU.Hash ρb (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''b)
  obtain ⟨RB, hRB⟩ := (ResU.compS_defined_iff ρb
    (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit''))).mpr hbm''.1
  obtain ⟨hfp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hW''p, hbp⟩ := ResU.Hash.split hW''₂ hρ'p
  obtain ⟨hW''f, hbf⟩ := ResU.Hash.split hW''₂ h1
  have hpm'' : ResU.Hash ρp (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''p)
  have hfm'' : ResU.Hash ρf (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''f)
  have hfRB : ResU.Hash ρf RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbm'' hfm'' hRB
  obtain ⟨FRB, hFRB⟩ := (ResU.compS_defined_iff ρf RB).mpr hfRB.1
  obtain ⟨BP, hBP⟩ := (ResU.compS_defined_iff ρb ρp).mpr hbp.1
  have hpRB : ResU.Hash ρp RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbp) hbm'' hpm'' hRB
  have hpFRB : ResU.Hash ρp FRB :=
    ResU.hash_of_pairwise (ResU.hash_symm hfp) hfRB hpRB hFRB
  obtain ⟨FRBp, hFRBp⟩ := (ResU.compS_defined_iff FRB ρp).mpr (ResU.hash_symm hpFRB).1
  obtain ⟨π', hπ'⟩ := (ResU.compS_defined_iff RB ρp).mpr (ResU.hash_symm hpRB).1
  have hFAm : ResU.Hash FA (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) :=
    ResU.hash_symm (ResU.hash_of_pairwise hmf (ResU.hash_symm haf) hmaH hFA)
  have hFAW : ResU.Hash FA W :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hfW) (ResU.hash_symm haf)
      (ResU.hash_symm haW) hFA)
  obtain ⟨FW, hFW, hFWb⟩ := (ResU.CompS.assoc ρf W'' ρb fρ').mp ⟨ρ', hW''₂, h2⟩
  obtain ⟨BP₁, hBP₁, hFWBP⟩ := (ResU.CompS.assoc FW ρb ρp fρ'p).mpr ⟨fρ', hFWb, h6⟩
  obtain rfl : BP = BP₁ := ResU.CompS.functional hBP hBP₁
  obtain ⟨WBP, hWBP, hfWBP⟩ := (ResU.CompS.assoc ρf W'' BP fρ'p).mpr ⟨FW, hFW, hFWBP⟩
  obtain ⟨FB, hFB, hFBW⟩ :=
    (ResU.CompS.assoc ρf BP W'' fρ'p).mp ⟨WBP, ResU.CompS.comm hWBP, hfWBP⟩
  obtain ⟨π'₁, hπ'₁, hfπ'⟩ := (ResU.CompS.assoc ρf RB ρp FRBp).mpr ⟨FRB, hFRB, hFRBp⟩
  obtain rfl : π' = π'₁ := ResU.CompS.functional hπ' hπ'₁
  obtain ⟨MP, hMP, hbMP⟩ := (ResU.CompS.assoc ρb (ResU.single l
    (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) ρp π').mpr ⟨RB, hRB, hπ'⟩
  obtain ⟨BP₂, hBP₂, hBPm⟩ := (ResU.CompS.assoc ρb ρp
    (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) π').mp
      ⟨MP, ResU.CompS.comm hMP, hbMP⟩
  obtain rfl : BP = BP₂ := ResU.CompS.functional hBP hBP₂
  obtain ⟨FB₁, hFB₁, hFBm⟩ :=
    (ResU.CompS.assoc ρf BP (ResU.single l
      (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) FRBp).mp ⟨π', hBPm, hfπ'⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  have hfBP : ResU.Hash ρf BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbp hfp hBP
  have hmBP : ResU.Hash (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbm'') hbp
      (ResU.hash_symm hpm'') hBP
  have hFBm' : ResU.Hash FB (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    ResU.hash_symm (ResU.hash_of_pairwise
      (ResU.hash_symm hfm'') hfBP hmBP hFB)
  have hFBW' : ResU.Hash FB W'' := ⟨hFBW.1, fρ'p, hFBW, hvfρ'p⟩
  -- H24: the two memories, by 6.25 under a frame (6.8)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hFAmc hFAm hFAWc hFAW).mpr h5
  have hmem₂ : ResU.Lower FRBp μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFBm hFBm' hFBW hFBW').mpr h7
  -- H25: `ρ ↭ ρ_b ● ρ''_m ● ρ_p`, by 6.28
  obtain ⟨BPW, hBPW₁, hBPW₂⟩ := (ResU.CompS.assoc W'' ρb ρp π).mpr ⟨ρ', hW''₂, h9⟩
  obtain rfl : BP = BPW := ResU.CompS.functional hBP hBPW₁
  have hvπ' : ResU.Valid π' := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hpRB
    exact ResU.CompS.functional hs hπ' ▸ hv
  have hupd : ResU.Upd ρ π' :=
    (ResU.six28 hW hW'' (ResU.CompS.comm hsplit) hBPm hX (ResU.CompS.comm hBPW₂)
      hvρ hvπ' h10.2.1 h10.2.2).mpr h10.1
  -- exit: `TW.mutFold`
  have hvFRBp : ResU.Valid FRBp := by obtain ⟨σ, hσ, -⟩ := hmem₂; exact ⟨σ, hσ⟩
  have hTout : TW FRBp ps'' (rsOf ls'') :=
    TW.mutFold hT'' hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) hvFRBp
  have htgout : Tagged FRBp ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) a).mpr ha) htg''
  -- H26: the callback hands the borrow back
  have hQ : Q ls'' v' RB := hb _ RB hcell'' hRB
  exact ⟨RB, ρp, FRB, FRBp, π', v', μ, μ', ps'', ls'',
    ResU.hash_symm hfRB, hFRB, hpFRB, hmem₁, hFRBp, hmem₂, h8, hπ',
    ⟨hupd, hvρ, hvπ'⟩, h11, hTout, htgout, hps'', hls'', hQ⟩

end BoCa.Fig16.LogRel.Typed

end
