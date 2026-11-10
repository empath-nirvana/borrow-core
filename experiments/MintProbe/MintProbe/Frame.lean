import MintProbe.Mint

/-!
# Views — the frame rule at a mint

`wp_mint_frame` is `[TR]` 6.64 (Imm Frame) with the one cell `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`
replaced by any resource `Y` of `imm` cells at the frame's fresh `α` minted over the owned
resource (`Mint α ρₒ Y`).  The proof is `Fig16.LogRel.wp_I_frame`'s, step for step; where it
cites 6.34, 6.26 with 6.8, 6.29 with 6.38, and 6.39, it cites `Mint.hash`, `Mint.lower_iff`,
`Mint.post_hash` and `Mint.upd`.

`wp` is `[TR]` p. 6's `Fig16.BoLo.wp`, unchanged, and so is `↭`.  The minted cells exist in the
resource the body starts from, and its `↭` preserves them exactly; the frame's end removes
them (`Mint.post_hash`'s `ρ⁺ \ dom(Y)`) and gives the owned resource back.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.MintProbe
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps)

/-- `ρ⁺ \ dom(Y)` keeps `ρ⁺|own = ∅`. -/
theorem noOwn_delDom {ρp Y : WRes} (h : NoOwn ρp) : NoOwn (ρp.delDom Y) := by
  refine noOwn_iff.mpr fun l ψ hl => ?_
  cases eY : Y.get l with
  | none => rw [ResU.delDom_get_of_none eY] at hl; exact noOwn_iff.mp h l ψ hl
  | some ζ => rw [ResU.delDom_get_of_some eY] at hl; cases hl

/-- **The frame rule at a mint.**  If every valid owned resource `P` holds of can mint, at any `α`
it outlives, an `S α` over itself, then

    P ⋆ (Иα. S α ─⋆ wp(e){[α](P ─⋆ Q̂)})  ⊨  wp(e){Q̂}.

`[TR]` 6.64 is the instance `P = ℓ ↦ v ⋆ P̂(v)`, `S α = ℓ ↦ Imm α P̂` (one minted cell).
`[about ours: `[TR]` 6.64's proof at a mint]` -/
theorem wp_mint_frame (P : WProp) (S : Life → WProp) (e : Expr) (Q : Val → WProp)
    (hmint : ∀ (α : Life) (ρo : WRes), P ρo → ρo.InStratum α → ResU.Valid ρo →
      ∃ Y, Mint α ρo Y ∧ S α Y) :
    Entails (P ⋆ fresh (fun α => S α ─⋆ wp e (fun v' => box α (P ─⋆ Q v')))) (wp e Q) := by
  classical
  intro ρ hH2 ρf hH3
  -- 6.112 pulls `P` inside the `И`
  obtain ⟨γ, hγ⟩ := fresh_frame P _ ρ hH2
  -- H4
  obtain ⟨A, hAγ⟩ : ∃ A : Life, A ⊏ γ := ⟨↓γ, Life.down_sqsubset _⟩
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  obtain ⟨ρo, ρb, hcρ, hPo, hwand⟩ := hbody
  obtain ⟨hPv, houto⟩ := hPo
  -- H10 and H11
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  -- ✓ρ
  obtain ⟨-, sρ, hsρ, hvsρ⟩ := id hH3
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- the minted resource, in place of 6.64's `ρᵢ`
  obtain ⟨Y, hM, hSY⟩ := hmint A ρo hPv houto (ResU.Valid.split hcρ hvρ).1
  -- H12-H17: the compatibility block
  have hH12 : ResU.Hash ρb ρo := ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb Y := hM.hash hH12
  obtain ⟨hof, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf Y := hM.hash (ResU.hash_symm hof)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb Y).mpr hH13.1
  have hH17 : ResU.Hash ρf BI := ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  -- H18: the wand, at the minted resource
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v', μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwand Y BI hSY hBI ρf hH17
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H26 and H28, at the mint
  obtain ⟨G, hpd, hG, hGY, hH28⟩ :=
    hM.post_hash houtb houto (ResU.CompS.comm hcρ) hvρ hBI h9 houtρ' h10
  -- H27 and H29-H33: the second compatibility block
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρp)
  obtain ⟨hPDρ', -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'oH, hPDo⟩ := ResU.Hash.split hG hH28
  have hfo : ResU.Hash ρf ρo := ResU.hash_symm hof
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' ρo).mpr hρ'oH.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'oH hfo hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.delDom Y) R :=
    ResU.hash_of_pairwise hPDρ' hρ'oH hPDo hR
  have hPDFR : ResU.Hash (ρp.delDom Y) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ :=
    (ResU.compS_defined_iff FR (ρp.delDom Y)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ :=
    (ResU.compS_defined_iff R (ρp.delDom Y)).mpr (ResU.hash_symm hPDR).1
  -- H34: the two memories, by `Mint.lower_iff` under a frame
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb Y fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρo sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  have hmem₁ : ResU.Lower sρ μ :=
    (hM.lower_iff hFBl ⟨_, (id hvsρ).choose_spec⟩ hFBi μ).mp h5
  -- and at the other end of the run
  obtain ⟨FP, hFP, hFPi⟩ :=
    (ResU.CompS.assoc fρ' (ρp.delDom Y) Y fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ :=
    (ResU.CompS.assoc ρf R (ρp.delDom Y) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' ρo (ρp.delDom Y) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨D₁, hD₁, hDo⟩ :=
    (ResU.CompS.assoc ρ' (ρp.delDom Y) ρo RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : G = D₁ := ResU.CompS.functional hG hD₁
  obtain ⟨FPD, hFPD, hFPDo⟩ := (ResU.CompS.assoc ρf G ρo FRP).mp ⟨RP, hDo, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ :=
    (ResU.CompS.assoc ρf ρ' (ρp.delDom Y) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : G = FP₁ := ResU.CompS.functional hG hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hmem₂ : ResU.Lower FRP μ' := (hM.lower_iff hFPDo hvFRP hFPi μ').mp h7
  -- H35: `ρ ↭ ρ′ ● ρ⁺ \ dom(Y) ● ρₒ`, by `Mint.upd`
  have hvRP : ResU.Valid RP := (ResU.Valid.split hfRP hvFRP).2
  have hupd : ResU.UpdV ρ RP :=
    hM.upd (ResU.CompS.comm hcρ) hvρ hDo hvRP hBI hGY h10
  -- G6
  have hno : NoOwn (ρp.delDom Y) := noOwn_delDom h11
  -- H36: the callback's wand, at the owned resource it gets back
  have hQ : Q v' R := hwand' ρo R hPv hR
  exact ⟨R, ρp.delDom Y, sρ, FR, FRP, RP, v', μ, μ',
    ResU.hash_symm hfR, hFR, hPDFR, hsρ, hmem₁, hFRP, hmem₂, h8, hRP,
    hupd, hno, hQ⟩

end BoCa.MintProbe

end
