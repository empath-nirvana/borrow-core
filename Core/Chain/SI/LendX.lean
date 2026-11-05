import Core.Chain.SI.ErwpX
import Core.Chain.SI.IFrameN

/-!
# A lend opened and ended inside one run, at `erwpX`  `[spec §62]`

`rwpGX_lend`: `rwp_I_frame`'s proof (`SI/IFrameN.lean`, `[TR]` 6.64 at the index) at the one
relation, with a lifetime token. The lend's two ends are this rule's two halves:

* **open**: `ℓ ↦ own(v)` becomes `ℓ ↦ imm({α}, v, ∅)` with its record (`TWNC.immFrame`) at a fresh
  `α` below the resource, the frame and every tag, and `[α]_1` is minted into the body's ghost;
* **end**: at the body's end, holding `[α]_1`, the record is ended (`TWNC.immEnd`), `ℓ ↦ own(v)`
  is back, and `[α]_1` is consumed.

The body runs at the outer mask: the end rebuilds `ℓ ↦ own(v)` from `↭` at `ℓ` through the body
(`six38N`, `six39N`), as Iris's mask-changing update is taken only around an atomic step. The
composite is the shape of `not_endpointMaskCompose`: its start and end hold no token, the middle
holds `[α]_1`, and the composite `↭` is unmasked.

The lent cell's payload is empty (`ρ_P = ∅`, the scope's restriction). The outer mask is empty:
the 6.38 lemmas read the body's `↭` at every location (`six29_borrows_offN`).
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

theorem maskShallow_locs_empty (ρ : WRes) : MaskShallow (∅ : Mask).locs ρ := by
  rw [Mask.locs_empty]; exact maskShallow_empty ρ

/-- A resource below `α` carries no `α`. -/
theorem not_carries_of_inStratum {ρ : WRes} {α : Life} (h : ρ.InStratum α) : ¬ Carries ρ α := by
  rintro ⟨l, s, v, χ, hh, ⟨σ, hσ, hg⟩, hm⟩
  have hc := flat_inStratum hσ h l _ hg
  simp only [CellU.inStratum_immOf] at hc
  exact absurd (lt_of_lt_of_le hc (s.meet_least α hm)) (lt_irrefl _)

theorem not_carries_single_own (l : Loc) (v : Val) (α : Life) :
    ¬ Carries (ResU.single l (CellU.ownOf v)) α := by
  rintro ⟨x, s, w, χ, hh, ⟨σ, hσ, hg⟩, -⟩
  obtain rfl := ResU.Flat.functional hσ (ResU.flat_single_own l v)
  by_cases hx : x = l
  · subst hx
    rw [ResU.single_get_self] at hg
    exact CellU.ownOf_ne_immOf (Option.some.inj hg)
  · rw [ResU.single_get_ne _ hx] at hg; cases hg

/-- `ℓ ↦ imm({α}, v, ∅)` carries only `α`. -/
theorem carries_single_imm {l : Loc} {A : Life} {v : Val}
    {h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes)} {α : Life}
    (hc : Carries (ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h)) α) : α = A := by
  obtain ⟨x, s, w, χ, hh, ⟨τ, hτ, hg⟩, hm⟩ := hc
  obtain ⟨e, a, he, ha, hc'⟩ := hτ
  have he0 : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm (fun y ψ hy => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hy; exact CellU.kind_immOf _ _ _ _))
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv ha
  obtain rfl : ev = PMap.empty := ExR.functional hev exW_empty
  obtain rfl : av = PMap.empty := AgW.functional hav agW_empty
  obtain rfl : p = PMap.empty := ResU.CompR.functional hp (ResU.comp_empty_right _)
  obtain rfl : a = ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h) :=
    ResU.CompR.functional hpa (ResU.comp_empty_right _)
  subst he0
  obtain rfl := eq_of_compS_empty_left hc'
  by_cases hx : x = l
  · subst hx
    rw [ResU.single_get_self] at hg
    obtain ⟨rfl, -, -⟩ := CellU.immOf_inj (Option.some.inj hg)
    exact hm
  · rw [ResU.single_get_ne _ hx] at hg; cases hg

/-- **A lend opened and ended inside one run.** `ℓ ↦ own(v)` with an empty payload is lent at a
fresh `α`; the body runs holding `ℓ ↦ imm({α}, v, ∅)` and `[α]_1`, at the list with the lend's
records (`AddAt`), and ends below `α` holding `[α]_1`; then the lend is ended, `[α]_1` consumed,
and `ℓ ↦ own(v)` is back. -/
theorem rwpGX_lend {Φ : LocFam} (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (hadm : AdmWf T δ) (v : Val) (hshape : vShape T δ v (PMap.empty : WRes))
    (e : Expr) (ls : List SRec) {n : Nat} {Q : PostX} {Q' : Life → PostX}
    {ρb ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρb ρ)
    (hbody : ∀ A : Life, ρb.InStratum A → (∀ x ∈ ls, x.2 ⊐ A) → g.tok A = 0 →
      ∀ ls', AddAt ls ls' A → ∀ (h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes))
        (BI : WRes),
        ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h)) BI →
        rwpGX (ℍ := ℍ) Φ ∅ (valPostX (Q' A)) n ls' e (BI, g + GRes.life A))
    (hend : ∀ A C k ls'' (w : Val) (ρ' : WRes) (g' : GRes), Q' A C k ls'' w (ρ', g') →
      ρ'.InStratum A ∧ ∃ g'', g' = g'' + GRes.life A ∧
        ∀ R, ResU.CompS ρ' (ResU.single l (CellU.ownOf v)) R → ∀ C₀, Q C₀ k ls w (R, g'')) :
    rwpGX (ℍ := ℍ) Φ ∅ (valPostX Q) n ls e (ρ, g) := by
  classical
  intro xf sρ ps μ hH3 hsρ hv hwf hwx _ _ hT htg hlow hfd jr μ' e' hj hrun hfin
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  have hvρ : ResU.Valid ρ := (hash_valid hH3).2
  set ρf : WRes := xf.1 with hρfdef
  -- the fresh lifetime: below `ρ_b`, the frame and every tag, with no token anywhere
  obtain ⟨ab, hab⟩ := ρb.exists_atLife
  obtain ⟨af, haf⟩ := ρf.exists_atLife
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  obtain ⟨A, hAlt, htokA⟩ := GRes.exists_fresh_life (hv := hv) (ab ⊓ af ⊓ b₀)
  have hAb : ab ⊐ A := lt_of_lt_of_le hAlt (le_trans inf_le_left inf_le_left)
  have hAf : af ⊐ A := lt_of_lt_of_le hAlt (le_trans inf_le_left inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_lt_of_le
    (lt_of_lt_of_le hAlt inf_le_right) (le_of_lt (hb₀ x hx))
  have houtb : ResU.InStratum A ρb := outlives_of_atLife hab hAb
  have houtf : ResU.InStratum A ρf := outlives_of_atLife haf hAf
  have htokg : g.tok A = 0 := by
    have := htokA; simp only [GRes.tok_add] at this
    exact (add_eq_zero.mp this).2
  have htokf : xf.2.tok A = 0 := by
    have := htokA; simp only [GRes.tok_add] at this
    exact (add_eq_zero.mp this).1
  -- the lend's parts: `ρ_ℓ = ℓ ↦ own(v)`, `ρ_P̂ = ∅`
  set ρP : WRes := PMap.empty with hρPdef
  set ρlP : WRes := ResU.single l (CellU.ownOf v) with hρlPdef
  have hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP := ResU.comp_empty_right _
  have houtP : ResU.InStratum (LSet.singleton A).join ρP := ResU.inStratum_empty _
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
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
  -- the record and its lineage
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  obtain ⟨eR, heR, -, -⟩ := frame_ex hclP (ResU.CompS.comm hFBl) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := p) hshape hadm heR
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
  -- open: `TWNC.immFrame`, and the tags
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
  have hwpBI := hbody A houtb hAtag htokg ls' hadd houtP BI hBI
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv'⟩ := hH12; exact (ResU.Valid.split hs hv').2
  have hvBI : ResU.Valid BI := by
    obtain ⟨-, s, hs, hv'⟩ := hH17; exact (ResU.Valid.split hs hv').2
  have hvi : ResU.Valid ρi := (ResU.Valid.split hBI hvBI).2
  have hFBiH : ResU.Hash FB ρi :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm
      (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mpr hlow
  -- the body's ghost premises: `[α]_1` minted at the fresh `α`
  have hVin : (xf.2 + (g + GRes.life A)).Valid := by
    rw [← GRes.add_assoc]; exact GRes.valid_add_life hv htokA
  have hcin : ∀ α, α ∈ (xf.2 + (g + GRes.life A)).counted → α ≠ A →
      α ∈ (xf.2 + g).counted := by
    intro α hα hne
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, GRes.tok_life, if_neg hne,
      _root_.add_zero] at hα ⊢
    exact hα
  have hWfin : WFC (xf.2 + (g + GRes.life A)).counted (ρf, xf.2) := by
    intro α hα hc
    by_cases hαA : α = A
    · subst hαA; exact absurd hc (not_carries_of_inStratum houtf)
    · exact hwf α (hcin α hα hαA) hc
  have hWxin : WFC (xf.2 + (g + GRes.life A)).counted (BI, g + GRes.life A) := by
    intro α hα hc
    show 0 < g.tok α + (GRes.life A).tok α
    by_cases hαA : α = A
    · subst hαA; simp
    · rcases carries_comp_split hBI hc with hc' | hc'
      · exact lt_of_lt_of_le (hwx α (hcin α hα hαA) (carries_comp_right hcρ hvρ hc'))
          le_self_add
      · exact absurd (carries_single_imm hc') hαA
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps'', ls'', h1, h2, h3, h6, h7, h9, h10m, h11, hT'',
    htg'', hps'', hls'', hV, hN, hW', hWp, -, -, -, hpost⟩ :=
    hwpBI (ρf, xf.2) fρ (p :: ps) μ hH17 h4 hVin hWfin hWxin (maskShallow_locs_empty _)
      (maskAuth_empty _) hTin htgin hlowin hfd jr μ' e' hj hrun hfin
  have h10 : UpdVN Φ (n - jr) BI π := updVNm_empty_iff.mp (by simpa using h10m)
  obtain ⟨v', rfl, hq⟩ := hpost
  obtain ⟨houtρ', g'', rfl, hQend⟩ := hend A _ _ _ _ _ _ hq
  -- end: 6.38 and 6.39 at the index, as `rwp_I_frame`
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hGsplit, hGiH, hGc⟩ :=
    six38_steps_one_twoN hlPcell hH12 hρ'p houtb houtρ' hBI h9 h10
  obtain ⟨G₀, hG₀, hH28⟩ :=
    six38N hlPcell hH12 hρ'p houtb houtρ' h11 hBI h9 h10
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
  have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
  have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
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
    obtain ⟨-, s, hs, hv'⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv'
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPDlP.1, FRP, hFPDlP, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPDlP hFPlH).mp h7
  obtain ⟨w₁, w₂, hw₁, hw₂, hupdw⟩ := six39N hclP hH12 hH28 hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  obtain rfl : RP = w₂ := ResU.CompS.functional hDlP hw₂
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
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr (hadd.1 x hx),
     fun x hx hn => hadd.2 x ((hls'' x).mp hx) hn⟩
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
  have hTout : TWNC FRP ps (rsOf ls) :=
    TWNC.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) hvFRP
      (fun r' => ⟨fun h => ⟨(hps'' r').mpr (List.mem_cons_of_mem _ h),
        fun e => hpps (e ▸ h)⟩, fun ⟨h, hne⟩ => by
          rcases List.mem_cons.mp ((hps'' r').mp h) with e | h'
          · exact absurd e hne
          · exact h'⟩)
      hTI.2.2.2.2.2.2.1
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
  -- the ghost at the end: `[α]_1` consumed
  have hVt := hV.tok A
  simp only [GRes.tok_add, GRes.tok_life] at hVt
  have hzero : xf.2.tok A + g''.tok A + gp.tok A = 0 := by
    have h' : xf.2.tok A + g''.tok A + gp.tok A + 1 ≤ 0 + 1 := by
      calc xf.2.tok A + g''.tok A + gp.tok A + 1 = xf.2.tok A + (g''.tok A + 1 + gp.tok A) := by
            ring
        _ ≤ 1 := hVt
        _ = 0 + 1 := by simp
    exact le_antisymm (le_of_add_le_add_right h') (by positivity)
  have hcout : ∀ α, α ∈ (xf.2 + (g'' + gp)).counted →
      α ∈ (xf.2 + (g'' + GRes.life A + gp)).counted := by
    intro α hα
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add] at hα ⊢
    exact lt_of_lt_of_le hα (by gcongr; exact le_self_add)
  have hAout : A ∉ (xf.2 + (g'' + gp)).counted := by
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, not_lt, nonpos_iff_eq_zero]
    rw [← _root_.add_assoc]; exact hzero
  have hvρp : ρp.Valid := (hash_valid h3).1
  refine ⟨R, ρp.del l, FR, FRP, RP, g'', gp, ps, ls, ResU.hash_symm hfR, hFR, hPDFR, hFRP,
    hmem₂, hRP, ?_, hno, hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_, ?_, ?_,
    maskShallow_locs_empty _, maskShallow_locs_empty _, maskAuth_empty _, ⟨v', rfl, hQend R hR _⟩⟩
  · simpa using updVNm_empty_iff.mpr hupdw
  · have : xf.2 + (g'' + GRes.life A + gp) = xf.2 + (g'' + gp) + GRes.life A := by
      rw [GRes.add_right_comm g'' (GRes.life A) gp, ← GRes.add_assoc]
    rw [this] at hV
    exact hV.left
  · intro α hα hα₀
    have hαA : α ≠ A := fun h => hAout (h ▸ hα)
    have : α ∉ (xf.2 + (g + GRes.life A)).counted := fun h => hα₀ (hcin α h hαA)
    exact hN α (hcout α hα) this
  · intro α hα hc
    rcases carries_comp_split hR hc with hc' | hc'
    · have hαA : α ≠ A := fun h => not_carries_of_inStratum houtρ' (h ▸ hc')
      have := hW' α (hcout α hα) hc'
      simpa [GRes.tok_life, hαA] using this
    · exact absurd hc' (not_carries_single_own l v α)
  · intro α hα hc
    exact hWp α (hcout α hα) (carries_comp_left hpd hvρp hc)

/-- The table with no stop. -/
def TableX.none : TableX := fun _ _ _ _ _ _ => False

theorem TableX.none_local : TableX.none.Local := fun _ _ _ _ _ _ _ _ h => h

/-- **`rwpGX_lend` at `erwpX`**: a body that does not stop, around any table. -/
theorem erwpX_lend {Φ : LocFam} (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (hadm : AdmWf T δ) (v : Val) (hshape : vShape T δ v (PMap.empty : WRes))
    (e : Expr) (ls : List SRec) {n : Nat} {Tb : TableX} {Q : PostX} {Q' : Life → PostX}
    {ρb ρ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρb ρ)
    (hbody : ∀ A : Life, ρb.InStratum A → (∀ x ∈ ls, x.2 ⊐ A) → g.tok A = 0 →
      ∀ ls', AddAt ls ls' A → ∀ (h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes))
        (BI : WRes),
        ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty h)) BI →
        erwpX (ℍ := ℍ) Φ ∅ TableX.none (Q' A) n ls' e (BI, g + GRes.life A))
    (hend : ∀ A C k ls'' (w : Val) (ρ' : WRes) (g' : GRes), Q' A C k ls'' w (ρ', g') →
      ρ'.InStratum A ∧ ∃ g'', g' = g'' + GRes.life A ∧
        ∀ R, ResU.CompS ρ' (ResU.single l (CellU.ownOf v)) R → ∀ C₀, Q C₀ k ls w (R, g'')) :
    erwpX (ℍ := ℍ) Φ ∅ Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_mono (fun C k ls' t x h => Or.inl h) ?_
  refine rwpGX_lend l T δ hadm v hshape e ls hcρ (fun A h₁ h₂ h₃ ls' h₄ h BI hBI => ?_) hend
  have hb := hbody A h₁ h₂ h₃ ls' h₄ h BI hBI
  rw [erwpX_eq] at hb
  exact rwpGX_mono (fun C k ls'' t x h => h.elim id (fun h' => h'.elim)) hb

end BoCa.Fig16.LogRel.Core.Chain.SI

end
