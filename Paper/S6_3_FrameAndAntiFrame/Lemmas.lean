import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Dynamics.Machine
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.FrameSurgery
import Support.Model.Notation
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.WalkSplitting

/-!
# [TR] §6.3 Frame and Anti-Frame (pp. 22–27), Theorems 6.64–6.66

The three frame rules at the printed `wp` (`[TR]` p. 6): Imm Frame (6.64), Mut Frame
(6.65) and Anti Frame (6.66).  Each proof builds a *"fictional"* borrow cell —
`ℓ ↦ imm({α}, v, ρ_P̂(v))` or `ℓ ↦ mut(α, v, ρ_P̂(v), P̂)` — in place of
`ℓ ↦ own(v) ● ρ_P̂(v)`, runs `e` against it, and trades it back with the surgery
lemmas of §6.2 (6.24–6.29, 6.34, 6.38, 6.39).  Lemma 6.112 (`Иf`, §6.5), with which
the proofs of 6.64 and 6.65 open, is declared here.

Records as in `Paper/S6_1_StandardLemmas/Lemmas.lean`.  A record's *Typed-world
version* names the same result at `wpTS` (row 5.33's repair), declared in
`Support/TypedWorld/`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### Lemma 6.112 (Иf), ahead of its subsection

Printed in §6.5 (p. 31); its record and alias are in `Paper/S6_5_NonStandardEntailments/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.112 (`⋔f`, p. 31).  The bound `@ρ_P ⊓ β_Q` is what the printed
chain 6.101, 6.99, 6.100, 6.111 computes.  `[as printed]` -/
theorem fresh_frame (P : SPropU Loc Val) (Q : Life → SPropU Loc Val) :
    (P ⋆ fresh Q) ⊨ fresh (fun α => box α P ⋆ Q α) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hP, ⟨β, hβ⟩⟩
  obtain ⟨a, ha⟩ := ρ₁.exists_atLife
  refine ⟨a ⊓ β, fun α hα => ?_⟩
  have k₁ : a ⊐ α := lt_of_lt_of_le hα inf_le_left
  obtain ⟨hQ, o₂⟩ := hβ α (lt_of_lt_of_le hα inf_le_right)
  exact ⟨⟨ρ₁, ρ₂, hc, ⟨hP, outlives_of_atLife ha k₁⟩, hQ⟩,
    (outlives_comp hc α).mpr ⟨outlives_of_atLife ha k₁, o₂⟩⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Theorem 6.64 (Imm Frame) · `[TR]` p. 22 · `proved`

> ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Imm α P̂ –⋆ wp(e){[α](ℓ ↦ v –⋆ P̂(v) –⋆ Q̂)}) ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Let `ρ` satisfy the left side (H1).  By Lemma 6.112, `Иα. ρ ∈ ℓ ↦ v ⋆ P̂(v) ⋆ (Imm α P̂ –⋆ wp(e){[α](ℓ ↦ v –⋆ P̂(v) –⋆ Q̂)})` (H2).  Unfolding `wp` in the goal (G1), let `ρ_f # ρ` (H3); the goals are `ρ′ # ρ_f` (G2), `ρ⁺ # ρ′ ● ρ_f` (G3), `(⟦ρ_f ● ρ⟧, e) ⇓ (⟦ρ_f ● ρ′ ● ρ⁺⟧, v)` (G4), `ρ ↭ ρ′ ● ρ⁺` (G5), `ρ⁺|own = ∅` (G6), `ρ′ ∈ Q̂(v)` (G7).  Unfolding `И` in H2 gives `β` with `∀α ⊏ β. ρ ∈ [α](…)`; take `α ⊏ β` (H4) — *"such an `α` always exists because for any lifetime, the set of lifetimes shorter than it is infinite"* — and specialise (H5).  Lemma 6.104 splits the box (H6), and unfolding `⋆` and `[α]` gives `ρ = ρ_ℓ ● ρ_P̂(v) ● ρ_b` with `ρ_ℓ ∈ ℓ ↦ v` (H7), `ρ_P̂(v) ∈ P̂(v)` (H8), `ρ_b ∈ Imm α P̂ –⋆ wp(e){…}` (H9), `@ρ_P̂(v) ⊐ α` (H10), `@ρ_b ⊐ α` (H11).  Let the *"fictional"* `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, well formed by H10.  Compatibilities: `ρ_b # ρ_ℓ ● ρ_P̂(v)` (H12: `▸◂` from `ρ`'s decomposition, `✓ρ` by Lemma 6.10 with H3); `ρ_b # ρᵢ` (H13) and `ρ_f # ρᵢ` (H15) by Lemma 6.34; `ρ_f # ρ_ℓ ● ρ_P̂(v)` (H14) and `ρ_f # ρ_b` (H16) by Lemma 6.11; `ρ_f # ρ_b ● ρᵢ` (H17) by Lemma 6.15.  By `–⋆` with H9 and H13, `ρ_b ● ρᵢ ∈ wp(e){[α](…)}`; unfolding `wp` at `ρ_f` gives `ρ′ # ρ_f` (H18), `ρ⁺ # ρ′ ● ρ_f` (H19), the run from `⟦ρ_f ● ρ_b ● ρᵢ⟧` (H20), `ρ_b ● ρᵢ ↭ ρ′ ● ρ⁺` (H21), `ρ⁺|own = ∅` (H22) and `ρ′ ∈ [α](ℓ ↦ v –⋆ P̂(v) –⋆ Q̂)(v′)` (H23), i.e. `@ρ′ ⊐ α` (H24) and `ρ′ ∈ ℓ ↦ v –⋆ P̂(v) –⋆ Q̂(v′)` (H25).  By Lemma 6.29 with H11, H12 and H21, `ρ′ ● ρ⁺ = (ρ′ ● ρ⁺)/ℓ ● ρᵢ`; by H24 `ℓ ∉ dom(ρ′)`, so `ρ′ ● ρ⁺ = ρ′ ● ρ⁺/ℓ ● ρᵢ` (H26).  Then `ρ′ # ρ⁺` (H27, Lemma 6.11); `ρ′ ● ρ⁺/ℓ # ρ_ℓ ● ρ_P̂(v)` (H28, **Lemma 6.38** with H12, H27, H11, H24, H22 and H21); `ρ′ ● ρ⁺/ℓ # ρ_f` (H29, 6.11); `ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v) # ρ_f` (H30, 6.15 with H28, H29, H14); `ρ′ ● ρ_ℓ ● ρ_P̂(v) # ρ_f` (H31, 6.11); `ρ⁺/ℓ # ρ′ ● ρ_ℓ ● ρ_P̂(v) ● ρ_f` (H32, by H30); `ρ′ # ρ_ℓ ● ρ_P̂(v)` (H33, 6.11).  Lemmas 6.26 and 6.8 with H12, H28 and H20 give `(⟦ρ_f ● ρ⟧, e) ⇓ (⟦ρ_f ● ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)⟧, v′)` (H34); Lemma 6.39 with H12, H28 and H21 gives `ρ ↭ ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)` (H35); `–⋆` gives `ρ′ ● ρ_ℓ ● ρ_P̂(v) ∈ Q̂(v′)` (H36).  Setting `ρ′ ≔ ρ′ ● ρ_ℓ ● ρ_P̂(v)` and `ρ⁺ ≔ ρ⁺/ℓ`: G2 by H31, G3 by H32, G4 by H34, G5 by H35, G6 by H22, G7 by H36.

**Lean.** `BoCa.Fig16.LogRel.wp_I_frame`, aliases `TR.lemma_6_64`, `TR.«Imm Frame»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_I_frameX`, in `Support/TypedWorld/FrameRules.lean`, `[variant: `P̂ ≔ 𝒱X⟦T⟧δ`, `TW.immFrame`'s `AdmWf` premise, `Q̂` stable along `Typed.Ext`]` (§12.70, §12.72).

**Note.** The bare `Q̂` under the inner `─⋆` is the postcondition at the run's own result, as 6.172 (p. 45) applies it.
-/
/-- `[TR]` Theorem 6.64 (`Imm Frame`, p. 22).
`[as printed]` (at this file's `wp`, `Fig16Wp`'s row over `BoLo.Steps`) -/
theorem wp_I_frame (l : BoCa.Loc) (P : Val → WProp) (v : Val) (e : Expr)
    (Q : Val → WProp) :
    Entails
      (ptoOwn l v ⋆ P v ⋆
        fresh (fun α => ptoImm l α P ─⋆
          wp e (fun v' => box α (ptoOwn l v ─⋆ (P v ─⋆ Q v')))))
      (wp e Q) := by
  classical
  intro ρ hH2 ρf hH3
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ P v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4
  obtain ⟨A, hAγ⟩ : ∃ A : Life, A ⊏ γ := ⟨↓γ, Life.down_sqsubset _⟩
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
  -- ✓ρ, by 6.10 with ✓(ρ_f ● ρ) from H3
  obtain ⟨-, sρ, hsρ, hvsρ⟩ := id hH3
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
  -- H18: the wand, at the fictional borrow
  have hwpBI := hwand ρi BI
    ⟨LSet.singleton A, v, ρP, houtP, rfl, hPv, le_refl _⟩ hBI
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v', μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwpBI ρf hH17
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
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
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
  -- H36: the callback's wand, at the cell and the payload it gets back
  obtain ⟨X, hX, hXR⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
  have hQ : Q v' R := (hwand' _ X rfl hX) ρP R hPv hXR
  exact ⟨R, ρp.del l, sρ, FR, FRP, RP, v', μ, μ',
    ResU.hash_symm hfR, hFR, hPDFR, hsρ, hmem₁, hFRP, hmem₂, h8, hRP,
    hupdw, hno, hQ⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_64 := BoCa.Fig16.LogRel.wp_I_frame
alias TR.«Imm Frame» := BoCa.Fig16.LogRel.wp_I_frame

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Theorem 6.65 (Mut Frame) · `[TR]` p. 24 · `proved`

> If P̂ ⊨ [β]P̂, then ℓ ↦ v ⋆ P̂(v) ⋆ (Иα. Mut α P̂ –⋆ wp(e){[α] ∀v′. ℓ ↦ v′ –⋆ P̂(v′) –⋆ Q̂}) ⊨ wp(e){Q̂}

**Printed proof, transcribed.** The shape of Theorem 6.64's, with `Mut` for `Imm`.  By Lemma 6.112 (H2); unfold `wp` at `ρ_f # ρ` (H3; goals G1–G7 as there).  Unfolding `И` gives `γ`; take `α ⊏ γ ⊓ β` (H4), which always exists, and specialise (H5); Lemma 6.104 splits the box (H6), giving `ρ = ρ_ℓ ● ρ_P̂(v) ● ρ_b` with H7–H11 as in 6.64.  Let `ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, well formed by H4.  `ρ_b # ρ_ℓ ● ρ_P̂(v)` (H12, Lemma 6.10 with H3); `ρ_b # ρ_m` (H13) and `ρ_f # ρ_m` (H15) by **Lemma 6.24**; `ρ_f # ρ_ℓ ● ρ_P̂(v)` (H14) and `ρ_f # ρ_b` (H16) by 6.11; `ρ_f # ρ_b ● ρ_m` (H17) by 6.15.  By `–⋆` with H9 and H13, `ρ_b ● ρ_m ∈ wp(e){…}`; unfolding at `ρ_f` gives H18–H25 as in 6.64.  By **Lemma 6.27** with H11 and H21, `ρ′ ● ρ⁺ = (ρ′ ● ρ⁺)/ℓ ● ρ_m`, and by H24 `ρ′ ● ρ⁺ = ρ′ ● ρ⁺/ℓ ● ρ_m` (H26).  `ρ′ ● ρ⁺/ℓ # ρ_ℓ ● ρ_P̂(v)` (H27, Lemma 6.24 with `✓(ρ′ ● ρ⁺)` from H19 and H26); H28–H32 by 6.11 and 6.15 as there; Lemmas 6.25 and 6.8 with H12, H27 and H20 give the run (H33); **Lemma 6.28** with H12, H27 and H21 gives `ρ ↭ ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)` (H34); `–⋆` gives `ρ′ ● ρ_ℓ ● ρ_P̂(v) ∈ Q̂(v′)` (H35).  At `ρ′ ≔ ρ′ ● ρ_ℓ ● ρ_P̂(v)`, `ρ⁺ ≔ ρ⁺/ℓ`: G2 by H30, G3 by H31, G4 by H33, G5 by H34, G6 by H22, G7 by H35.

**Lean.** `BoCa.Fig16.LogRel.wp_M_frame`, aliases `TR.lemma_6_65`, `TR.«Mut Frame»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_M_frameX`, in `Support/TypedWorld/FrameRules.lean`, with the premise `P̂ ⊨ [β]P̂` taken at every record list (§12.70).

**Note.** The display's borrow `Mut α P̂` is the cell assertion `ℓ ↦ Mut α P̂` (`ptoMut l α P`), as the proof's `ρ_m` and 6.66's display write it; the premise `P̂ ⊨ [β]P̂` is taken at each value, as `[CONF]` Fig. 13a prints it; the bare `Q̂` is the postcondition at the run's own result, as 6.173 (p. 46) writes it.
-/
/-- `[TR]` Theorem 6.65 (`Mut Frame`, p. 24).
`[as printed]` (at this file's `wp`, `Fig16Wp`'s row over `BoLo.Steps`) -/
theorem wp_M_frame (l : BoCa.Loc) (β : Life) (P : Val → WProp)
    (hP : ∀ v, Entails (P v) (box β (P v))) (v : Val) (e : Expr) (Q : Val → WProp) :
    Entails
      (ptoOwn l v ⋆ P v ⋆
        fresh (fun α => ptoMut l α P ─⋆
          wp e (fun v' => box α (all fun w => ptoOwn l w ─⋆ (P w ─⋆ Q v')))))
      (wp e Q) := by
  classical
  intro ρ hH2 ρf hH3
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `N`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ P v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime shorter than both `γ` and `β` -- one always exists
  obtain ⟨A, hAγ, hAβ⟩ : ∃ A : Life, A ⊏ γ ∧ A ⊏ β :=
    ⟨↓(γ ⊓ β), lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left,
      lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right⟩
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
  have hPstrat : ∀ (w : Val) (σ : ResU BoCa.Loc BoCa.Val), P w σ → ResU.InStratum A σ := by
    intro w σ hσ m ψ hm
    exact CellU.InStratum.mono (le_of_lt hAβ) ((hP w σ hσ).2 m ψ hm)
  have hofS : BoLo.ofS (fun (w : Val) (r : ResS BoCa.Loc BoCa.Val A) => P w r.1) = P := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hPstrat w σ h, h⟩⟩
  -- the "fictional" `ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, well formed by H4
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A :=
    (fun (w : Val) (r : ResS BoCa.Loc BoCa.Val A) => P w r.1) with hQs
  have hwit : Qs v ⟨ρP, houtP⟩ := hPv
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP Qs hwit) with hρm
  have hkm : (CellU.mutOf A v ρP houtP Qs hwit).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  -- ✓ρ, by 6.10 with ✓(ρ ● ρ_f) from H3
  obtain ⟨-, sρ, hsρ, hvsρ⟩ := id hH3
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
  -- H18: the wand, at the fictional borrow
  have hwpBM := hwand ρm BM ⟨A, v, ρP, houtP, Qs, hwit, le_refl _, rfl, hofS⟩ hBM
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v', μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwpBM ρf hH17
  -- H24 and H25: unfolding `[α]`
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H26: 6.27 -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, hwit'', hsplit''⟩ := ResU.six27 houtb hBM h10
  -- `ℓ ∉ dom(ρ′)`, by H24: everything in `ρ′` strictly outlives `A`
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
  -- `ρ⁺ = ρ⁺/ℓ ● ρ''_m`
  have hpd : ResU.CompS (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) ρp := ResU.del_compS hppl
  -- `ρ′ ● ρ⁺/ℓ`, and `π = (ρ′ ● ρ⁺/ℓ) ● ρ''_m`
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) π).mp ⟨ρp, hpd, h9⟩
  have hvπ : ResU.Valid π := h10.2.2
  -- `ρ''_v ● ℓ ↦ own(v'')` is defined
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  -- H27 and its companions, by 6.24 and 6.11
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  -- the goal's `ρ′ = ρ′ ● ρ''_v ● ℓ ↦ own(v'')`
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
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
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
  -- and at the other end of the run
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc fρ' (ρp.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) fρ'p).mp ⟨ρp, hpd, h6⟩
  -- `FP ● ρ''_v ● ℓ ↦ own(v'')` is the goal's own frame, regrouped
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
  -- the validities the swap needs
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
  -- `ρ⁺/ℓ` is still own-free
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
  -- H35: the callback's wand, at the value the run leaves in the cell
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : Q v' R := (hwand' v'' _ y rfl hy₁) χ R hwit'' hy₂
  exact ⟨R, ρp.del l, sρ, FR, FRP, RP, v', μ, μ',
    ResU.hash_symm hfR, hFR, hPDFR, hsρ, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hQ⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_65 := BoCa.Fig16.LogRel.wp_M_frame
alias TR.«Mut Frame» := BoCa.Fig16.LogRel.wp_M_frame

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Theorem 6.66 (Anti Frame) · `[TR]` p. 25 · `proved`

> ℓ ↦ Mut α P̂ ⋆ (∀v. ℓ ↦ v –⋆ P̂(v) –⋆ wp(e){∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂)}) ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Let `ρ` satisfy the left side (H1); unfold `wp` at `ρ_f # ρ` (H2; goals G1–G7 as in 6.64).  Unfolding `⋆`, `ρ = ρ_m ● ρ_a` with `ρ_m ∈ ℓ ↦ Mut α P̂` (H3) and `ρ_a` in the wand (H4); unfolding `ℓ ↦ Mut`, `ρ_m = ℓ ↦ mut(β, v, ρ_P̂(v), P̂)` for some `β ⊒ α`, `v` and `ρ_P̂(v) ∈ P̂(v)` (H5).  Specialise H4 to `v` (H6).  By 6.11 with H2, `ρ_m # ρ_a`; with `ρ_ℓ = ℓ ↦ own(v)`, Lemma 6.24 gives `ρ_a # ρ_ℓ ● ρ_P̂(v)` (H7); likewise `ρ_m # ρ_f`, so `ρ_f # ρ_ℓ ● ρ_P̂(v)` (H8).  By `–⋆` with H6, `ρ_a ● ρ_ℓ ● ρ_P̂(v) ∈ wp(e){…}` (H9); unfolding at `ρ_f` with H8 gives `ρ′ # ρ_f` (H10), `ρ⁺ # ρ′ ● ρ_f` (H11), the run (H12), `ρ_a ● ρ_ℓ ● ρ_P̂(v) ↭ ρ′ ● ρ⁺` (H13), `ρ⁺|own = ∅` (H14), and `ρ′ ∈ ∃v. ℓ ↦ v ⋆ P̂(v) ⋆ (ℓ ↦ Mut α P̂ –⋆ Q̂(v′))` (H15).  Unfolding, `ρ′ = ρ″_ℓ ● ρ_P̂(v″) ● ρ_b` (H16) with `ρ″_ℓ ∈ ℓ ↦ v″` (H17), `ρ_P̂(v″) ∈ P̂(v″)` (H18), `ρ_b ∈ ℓ ↦ Mut α P̂ –⋆ Q̂(v′)` (H19).  Let `ρ″_m = ℓ ↦ mut(β, v″, ρ_P̂(v″), P̂)`, well formed since `ρ_m` is.  `ρ_b ● ρ⁺ # ρ″_m` (H20, 6.11 with H11, then 6.24); `ρ_f # ρ_b ● ρ⁺ ● ρ″_m` (H21, H11 and 6.24); `ρ_b # ρ″_m` (H22) and `ρ_b ● ρ″_m # ρ_f` (H23) by 6.11 with H21.  Lemmas 6.25 and 6.8 with H21 and H12 give the run to `⟦ρ_f ● ρ_b ● ρ⁺ ● ρ″_m⟧` (H24); Lemma 6.28 with H20 and H13 gives `ρ ↭ ρ_b ● ρ⁺ ● ρ″_m` (H25); `–⋆` with H22 gives `ρ_b ● ρ″_m ∈ Q̂(v′)` (H26).  At `ρ′ ≔ ρ_b ● ρ″_m`, `ρ⁺ ≔ ρ⁺`: G2 by H23, G3 by H21, G4 by H24, G5 by H25, G6 by H14, G7 by H26.

**Lean.** `BoCa.Fig16.LogRel.wp_M_antiFrame`, aliases `TR.lemma_6_66`, `TR.«Anti Frame»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_M_antiFrameX`, in `Support/TypedWorld/FrameRules.lean` (§12.70).

**Note.** The bare `Q̂` under the inner `─⋆` is the postcondition at the run's own result, as the proof's `Q̂(v′)` and 6.174 (p. 47) read it.
-/
/-- `[TR]` Theorem 6.66 (`Anti Frame`, p. 25).
`[as printed]` (at this file's `wp`, `Fig16Wp`'s row over `BoLo.Steps`) -/
theorem wp_M_antiFrame (l : BoCa.Loc) (α : Life) (P : Val → WProp) (e : Expr)
    (Q : Val → WProp) :
    Entails
      (ptoMut l α P ⋆
        (all fun v => ptoOwn l v ─⋆ (P v ─⋆
          wp e (fun v' => ex fun w =>
            ptoOwn l w ⋆ P w ⋆ (ptoMut l α P ─⋆ Q v')))))
      (wp e Q) := by
  classical
  intro ρ hH1 ρf hH2
  obtain ⟨ρm, ρa, hsplit, hM, hA⟩ := hH1
  obtain ⟨β, v, σP, hstr, Qs, hwit, hαβ, hρm, hofS⟩ := hM
  subst hρm
  obtain ⟨-, sρ, hsρ, hvsρ⟩ := id hH2
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
  have hPv : P v σP := by rw [← hofS]; exact ⟨hstr, hwit⟩
  obtain ⟨A₁, hA₁, hA₂⟩ :=
    (ResU.CompS.assoc ρa (ResU.single l (CellU.ownOf v)) σP X).mp
      ⟨W, ResU.CompS.comm hW, hX⟩
  have hwpX := (hA v _ A₁ rfl hA₁) σP X hPv hA₂
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v', μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwpX ρf hfX
  obtain ⟨v'', ρl'', rest, hcr, hl'', hrest⟩ := h12
  subst hl''
  obtain ⟨ρPv'', ρb, hcr2, hPv'', hb⟩ := hrest
  obtain ⟨hstr'', hwit''⟩ : ∃ hh : ResU.InStratum β ρPv'', Qs v'' ⟨ρPv'', hh⟩ := by
    rw [← hofS] at hPv''; exact hPv''
  obtain ⟨W'', hW''₁, hW''₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v'')) ρPv'' ρb ρ').mp ⟨rest, hcr2, hcr⟩
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
  -- the goal's `ρ′ = ρ_b ● ρ''_m`, and the frames over it
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
  -- `ρ_f ● ρ_a`, the frame the first memory is read over
  obtain ⟨FA, hFA⟩ := (ResU.compS_defined_iff ρf ρa).mpr (ResU.hash_symm haf).1
  have hFAm : ResU.Hash FA (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) :=
    ResU.hash_symm (ResU.hash_of_pairwise hmf (ResU.hash_symm haf) hmaH hFA)
  have hFAW : ResU.Hash FA W :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hfW) (ResU.hash_symm haf)
      (ResU.hash_symm haW) hFA)
  obtain ⟨FA₁, hFA₁, hFAmc⟩ :=
    (ResU.CompS.assoc ρf ρa (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) sρ).mp
      ⟨ρ, ResU.CompS.comm hsplit, hsρ⟩
  obtain rfl : FA = FA₁ := ResU.CompS.functional hFA hFA₁
  obtain ⟨FA₂, hFA₂, hFAWc⟩ := (ResU.CompS.assoc ρf ρa W fρ).mp ⟨X, hX, h4⟩
  obtain rfl : FA = FA₂ := ResU.CompS.functional hFA hFA₂
  -- `ρ_f ● (ρ_b ● ρ_p)`, the frame the second memory is read over
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
  -- the two `#`s the frame needs
  have hfBP : ResU.Hash ρf BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbp hfp hBP
  have hmBP : ResU.Hash (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbm'') hbp
      (ResU.hash_symm hpm'') hBP
  have hFBm' : ResU.Hash FB (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    ResU.hash_symm (ResU.hash_of_pairwise
      (ResU.hash_symm hfm'') hfBP hmBP hFB)
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
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
  -- H26: the callback hands the borrow back
  have hQ : Q v' RB :=
    hb _ RB ⟨β, v'', ρPv'', hstr'', Qs, hwit'', hαβ, rfl, hofS⟩ hRB
  exact ⟨RB, ρp, sρ, FRB, FRBp, π', v', μ, μ',
    ResU.hash_symm hfRB, hFRB, hpFRB, hsρ, hmem₁, hFRBp, hmem₂, h8, hπ',
    ⟨hupd, hvρ, hvπ'⟩, h11, hQ⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_66 := BoCa.Fig16.LogRel.wp_M_antiFrame
alias TR.«Anti Frame» := BoCa.Fig16.LogRel.wp_M_antiFrame

end
