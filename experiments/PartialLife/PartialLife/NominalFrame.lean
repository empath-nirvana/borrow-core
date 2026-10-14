import Core.FrameRules

/-!
# PartialLife — 6.65 with its fresh lifetime taken from a set

`[TR]` 6.65 (`Mut Frame`, `Core/FrameRules.lean`'s `wpTS_M_frameX`) asks its callback at a fresh
lifetime through `И α. …` (`BoLo.fresh`: `∃ β. ∀ α ⊏ β. [α] …`), at **every** lifetime below some
bound, and its proof uses **one**: a lifetime below the bound, below `β` and below every record's tag.
`wpTS_M_frameOn` is 6.65 with `И` ranging only over a set `S` of lifetimes that has a member below
every lifetime (`freshOn S`): Core's proof with the fresh lifetime chosen in `S`, every other step
unchanged. Core's statement is the case `S = ⊤` (`wpTS_M_frameX_of_on`).

This is the freshness a nominal re-making asks for (problem B): over a partial order of lifetimes read
from Core's slots, the borrow rules can instantiate their callback only at slots read beneath the
borrower's context, which no slot bound collects (`no_fresh_bound`) and which have a member below any
finitely many slots (`fresh_on_branch`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `И_S P̂ ≜ ∃ β. ∀ α ∈ S. α ⊏ β → [α] P̂(α)`: freshness over the lifetimes of `S`. -/
def freshOn (S : Life → Prop) (P : Life → WProp) : WProp :=
  fun ρ => ∃ β, ∀ α, S α → α ⊏ β → box α (P α) ρ

/-- Core's `И` is freshness over every lifetime. -/
theorem fresh_eq_freshOn_top (P : Life → WProp) : fresh P = freshOn (fun _ => True) P := by
  funext ρ
  exact propext ⟨fun ⟨β, h⟩ => ⟨β, fun α _ hα => h α hα⟩, fun ⟨β, h⟩ => ⟨β, fun α hα => h α trivial hα⟩⟩

/-- `[TR]` 6.112 (`⋔f`) over a set. -/
theorem freshOn_frame (S : Life → Prop) (P : WProp) (Q : Life → WProp) :
    (P ⋆ freshOn S Q) ⊨ freshOn S (fun α => box α P ⋆ Q α) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hP, ⟨β, hβ⟩⟩
  obtain ⟨a, ha⟩ := ρ₁.exists_atLife
  refine ⟨a ⊓ β, fun α hSα hα => ?_⟩
  have k₁ : a ⊐ α := lt_of_lt_of_le hα inf_le_left
  obtain ⟨hQ, o₂⟩ := hβ α hSα (lt_of_lt_of_le hα inf_le_right)
  exact ⟨⟨ρ₁, ρ₂, hc, ⟨hP, outlives_of_atLife ha k₁⟩, hQ⟩,
    (outlives_comp hc α).mpr ⟨outlives_of_atLife ha k₁, o₂⟩⟩

/-- **6.65 with its fresh lifetime taken from `S`**, for any `S` with a member below every lifetime:

    ℓ ↦ v ⋆ 𝒱⟦T⟧(ls)δ(v) ⋆ (И_S α. Mut α 𝒱⟦T⟧δ ─⋆ wp_{ls}(e){[α] ∀v′. ℓ ↦ v′ ─⋆ 𝒱⟦T⟧δ(v′) ─⋆ Q̂})
      ⊨  wp_{ls}(e){Q̂} -/
theorem wpTS_M_frameOn (S : Life → Prop) (hS : ∀ b : Life, ∃ α, S α ∧ α ≤ b)
    (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        freshOn S (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
          wpTS ls e (fun ls'' v' =>
            box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ Q ls'' v')))))
      (wpTS ls e Q) := by
  classical
  intro ρ hH2 ρf sρ ps hH3 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := freshOn_frame S (ptoOwn l v ⋆ vC true T ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime of `S` shorter than `γ`, `β` and every tag
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  obtain ⟨A, hSA, hAle⟩ := hS (b₀ ⊓ (↓(γ ⊓ β)))
  have hAγ : A ⊏ γ :=
    lt_of_le_of_lt (le_trans hAle inf_le_right)
      (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left)
  have hAβ : A ⊏ β :=
    lt_of_le_of_lt (le_trans hAle inf_le_right)
      (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx =>
    lt_of_le_of_lt (le_trans hAle inf_le_left) (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hSA hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  -- H10 and H11
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  -- `P̂ ⊧ [β] P̂` is what puts `P̂`'s resources in `Res_A`
  have hunif : ∀ ls' w σ, vC true T ls' δ w σ → ResU.InStratum A σ := fun ls' w σ h m ψ hm =>
    CellU.InStratum.mono (le_of_lt hAβ) (hP ls' w σ h m ψ hm)
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A :=
    (fun (w : Val) (r : ResS BoCa.Loc BoCa.Val A) => vC true T ls δ w r.1) with hQs
  have hofS : BoLo.ofS Qs = fun w => vC true T ls δ w := by
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
    hwpBM ρf fρ ps hH17 h4 hTin htgin alc kc
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
  have hχv : vC true T ls'' δ v'' χ :=
    vC_local true T (ext_of_same hls'' χ) (show vC true T ls δ v'' χ from hwit'')
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : Q ls'' v' R := (hwand' v'' _ y rfl hy₁) χ R hχv hy₂
  exact ⟨R, ρp.del l, FR, FRP, RP, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

/-- Core's 6.65 is the case `S = ⊤`. -/
theorem wpTS_M_frameX_of_on (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
          wpTS ls e (fun ls'' v' =>
            box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ Q ls'' v')))))
      (wpTS ls e Q) := by
  rw [fresh_eq_freshOn_top]
  exact wpTS_M_frameOn (ℍ := ℍ) (fun _ => True) (fun b => ⟨b, trivial, le_rfl⟩) l T δ β hP v e ls Q

end PartialLife

end
