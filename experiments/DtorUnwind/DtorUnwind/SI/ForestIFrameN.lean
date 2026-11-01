import DtorUnwind.SI.IStopN

/-!
# 6.64 at any final term, the frame's lifetime only distinct from the list's tags

`rwpG_I_frameG` (`SI/IStopN.lean`) asks the frame lifetime `α` below every tag of the caller's
list (`[TR]` 6.64's fresh choice). That ordering compares the frame with every tag of the one
list, including frames a resumer opened in another branch. `rwpG_I_frameGD` asks only that no
tag of the list is at `α`; the proof is `rwpG_I_frameG`'s, with the one step that read the
ordering reading distinctness.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`rwpG_I_frameG` with the frame's lifetime distinct from the list's tags**, in place of
shorter than all of them. The proof reads the ordering once, to tell an outer tag from the
frame's own (`htgout`), and distinctness is what that step uses. Under one stack the fresh
choice gives the ordering; a frame re-entered after a resumer added frames of its own below it
has distinctness only. -/
theorem rwpG_I_frameGD {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    {A : Life} {ρP ρlP ρb ρ : WRes} (houtP : ρP.InStratum A) (houtb : ρb.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hshape : vShape T δ v ρP) {ls : List SRec} (hAne : ∀ x ∈ ls, x.2 ≠ A)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d)
    {Qin Qout : PostG} {n : Nat} {e : Expr}
    (hpost : ∀ k, k ≤ n → ∀ ls'' t (ρ' ρp π Y : WRes), Qin k ls'' t ρ' → NoOwn ρp →
      ResU.CompS ρ' ρp π → (∀ x, x ∈ ls'' ↔ x ∈ frameList ⟨l, v, ρP, T, δ⟩ ds A ls) →
      ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) π →
      (π.del l).InStratum A → ResU.CompS (π.del l) ρlP Y →
      (∀ R Z, ResU.CompS R Z Y → R.InStratum A →
        (∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm) → Ext ls'' ls R) →
      ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls t ρ'L)
    (hA : ∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
      rwpG (ℍ := ℍ) Φ Qin n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ := by
  classical
  intro ρf sρ ps μ hH3 hsρ hT htg hlow hfd jr μ' e' hj hrun hfin
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have houtlP : ρlP.InStratum A := inStratum_ownP hclP houtP
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
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- the record and the entry
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
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
  -- H18: the run under the frame
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ :=
    hA BI hBI ρf fρ (p :: ps) μ hH17 h4 hTin htgin hlowin hfd jr μ' e' hj hrun hfin
  have hvπ : ResU.Valid π := h10.2.2
  -- 6.29: `π = π/ℓ ● ρᵢ`, and every other cell of `⦇π⦈` outlives `α`
  have hGc : ResU.CompS (π.del l) ρi π := six29N houtb hlPcell hH12 hBI h10
  obtain ⟨σπ, hσπ⟩ := hvπ
  have hoff := (six29_borrows_offN houtb hlPcell hH12 hBI h10 hσπ).2
  have hπdA : (π.del l).InStratum A := by
    intro m ψ hm
    by_cases hml : m = l
    · subst hml; rw [ResU.del_get_self] at hm; exact absurd hm (by simp)
    · rw [ResU.del_get_ne _ hml] at hm
      exact ResU.flat_inStratum_inv_at hσπ (fun φ hφ => hoff m hml φ hφ) hm
  -- 6.38 at `ρ′ := π/ℓ`, `ρ⁺ := ρᵢ`
  have hidel : ρi.del l = PMap.empty := by
    refine PMap.ext fun m => ?_
    by_cases hml : m = l
    · subst hml; rw [ResU.del_get_self]; rfl
    · rw [ResU.del_get_ne _ hml, ResU.single_get_ne _ hml]; rfl
  obtain ⟨G₀, hG₀, hGW⟩ := six38N (ρ' := π.del l) (ρp := ρi) hlPcell hH12
    ⟨hGc.1, π, hGc, ⟨σπ, hσπ⟩⟩ houtb hπdA (noOwn_single_imm l _ _ _ _) hBI hGc h10
  rw [hidel] at hG₀
  obtain rfl : π.del l = G₀ := ResU.CompS.functional (ResU.comp_empty_right _) hG₀
  -- 6.39: `ρ ↭ π/ℓ ● ρ_ℓ ● ρ_P̂(v)`
  obtain ⟨w₁, Y, hw₁, hY, hupdw⟩ := six39N hclP hH12 hGW hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  -- the worlds at the end: `ρ_f ● π = (ρ_f ● π/ℓ) ● ρᵢ`, and `(ρ_f ● π/ℓ) ● ρ_ℓ ● ρ_P̂(v)`
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  obtain ⟨π₁, hπ₁, hfπ⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ'p).mpr ⟨fρ', h2, h6⟩
  obtain rfl : π = π₁ := ResU.CompS.functional h9 hπ₁
  obtain ⟨FP, hFP, hFPi⟩ := (ResU.CompS.assoc ρf (π.del l) ρi fρ'p).mp ⟨π, hGc, hfπ⟩
  have hfπH : ResU.Hash π ρf := ⟨(ResU.CompS.comm hfπ).1, fρ'p, ResU.CompS.comm hfπ, hvfρ'p⟩
  obtain ⟨hDf, -⟩ := ResU.Hash.split hGc hfπH
  have hflP : ResU.Hash ρf ρlP := ResU.hash_symm hlPf
  have hfY : ResU.Hash ρf Y := ResU.hash_of_pairwise (ResU.hash_symm hDf) hGW hflP hY
  obtain ⟨FY, hFY, hvFY⟩ := hfY.2
  obtain ⟨FP₁, hFP₁, hFPlP⟩ := (ResU.CompS.assoc ρf (π.del l) ρlP FY).mp ⟨Y, hY, hFY⟩
  obtain rfl : FP = FP₁ := ResU.CompS.functional hFP hFP₁
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPlP.1, FY, hFPlP, hvFY⟩
  have hmem₂ : ResU.Lower FY μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPlP hFPlH).mp h7
  -- the frame's record and its lifetime at the end
  obtain ⟨aF, haF⟩ := agW_of_valid hvfρ'p
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
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr (hadd.1 x hx),
     fun x hx hn => hadd.2 x ((hls'' x).mp hx) hn⟩
  -- the parts of `π/ℓ ● ρ_ℓ ● ρ_P̂(v)` hold no view of the frame's lineage (`ext_drop`)
  have hicpY : ∀ m, ICpAt aF Y m := by
    intro m
    have hD : ICpAt aF (π.del l) m :=
      icpAt_trans (icpAt_right (ResU.CompS.toCompR hFP) m)
        (icpAt_trans (icpAt_left (ResU.CompS.toCompR hFPi) m) (icpAt_agW haF m))
    obtain ⟨ψl, eψl, kψl, wψl, rψl⟩ := compS_get_right' hFPi (ResU.single_get_self _ _)
    obtain ⟨sl, hsl, hψl⟩ := CellU.imm_eta (kψl.trans (CellU.kind_immOf _ _ _ _))
    rw [hψl] at eψl
    obtain ⟨e₀, a₀, -, ha₀, icp₀⟩ := escrow_icp haF eψl
    have hwl : ψl.wit = ρP := wψl.trans (CellU.wit_immOf _ _ _ _)
    rw [hwl] at ha₀
    have hρP : ICpAt aF ρP m := icpAt_trans (icpAt_agW ha₀ m) (icp₀ m)
    exact icpAt_comp (ResU.CompS.toCompR hY) hD
      (icpAt_comp (ResU.CompS.toCompR hclP)
        (icpAt_of_immFree (fun x ψ e => by
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; simp) m) hρP)
  have hext : ∀ R Z, ResU.CompS R Z Y → R.InStratum A →
      (∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm) → Ext ls'' ls R := by
    intro R Z hRZ hRα hRl
    have hicpR : ∀ m, ICpAt aF R m := fun m =>
      icpAt_trans (icpAt_left (ResU.CompS.toCompR hRZ) m) (hicpY m)
    refine ext_drop hls''add hRα fun r hr hrel => ?_
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
  -- exit: `TWNC.immEnd` at `p`, back to the caller's records
  have hTout : TWNC FY ps (rsOf ls) :=
    TWNC.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPlP) hvFY
      (fun r' => ⟨fun h => ⟨(hps'' r').mpr (List.mem_cons_of_mem _ h),
        fun e => hpps (e ▸ h)⟩, fun ⟨h, hne⟩ => by
          rcases List.mem_cons.mp ((hps'' r').mp h) with e | h'
          · exact absurd e hne
          · exact h'⟩)
      hTI.2.2.2.2.2.2.1
  have backOut : ∀ a', AgW FY a' → ∀ m, ICpAt aF a' m := by
    intro a' ha' m
    obtain ⟨aσ, aY, eR', aR, pR, heR', -, hpR, hcp, hσY, hRY⟩ :=
      end_walks (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPlP) haF ha'
    exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have htgout : Tagged FY ps ls := by
    intro x hx
    obtain ⟨q, hq, hqd, hfq⟩ := htg'' x ((hls'' x).mpr (hadd.1 x hx))
    have hqp : q ≠ p := by
      rintro rfl
      have := frameLife_eq hfq haF eζl htl hAl
      exact hAne x hx (by first | exact this | exact this.symm)
    have hq' : q ∈ ps := by
      rcases List.mem_cons.mp ((hps'' q).mp hq) with e | h
      · exact absurd e hqp
      · exact h
    exact ⟨q, hq', hqd, frameLife_back hfq (fun a' ha' =>
      ⟨aF, haF, backOut a' ha' _, fun m _ => backOut a' ha' m⟩)⟩
  -- the lender's post-configuration
  obtain ⟨ρ'L, ρpL, hLY, hnoL, hQ⟩ :=
    hpost (n - jr) (by omega) ls'' e' ρ' ρp π Y h12 h11 h9 hls'' hGc hπdA hY hext
  obtain ⟨fL, hf1, hf2⟩ := (ResU.CompS.assoc ρf ρ'L ρpL FY).mp ⟨Y, hLY, hFY⟩
  have hvfL : ResU.Valid fL := (ResU.Valid.split hf2 hvFY).1
  exact ⟨ρ'L, ρpL, fL, FY, Y, ps, ls,
    ⟨(ResU.CompS.comm hf1).1, fL, ResU.CompS.comm hf1, hvfL⟩, hf1,
    ⟨(ResU.CompS.comm hf2).1, FY, ResU.CompS.comm hf2, hvFY⟩, hf2, hmem₂, hLY, hupdw, hnoL,
    hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-- The ordering gives distinctness. -/
theorem ne_of_tag_above {ls : List SRec} {A : Life} (h : ∀ x ∈ ls, x.2 ⊐ A) :
    ∀ x ∈ ls, x.2 ≠ A := fun x hx e => lt_irrefl A (e ▸ h x hx)

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
