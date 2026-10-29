import SuspSpike.Scope

/-!
# SuspSpike — `[TR]` 6.65 at a given lifetime, exactly

`wpG_M_frameX` (`Core/EffWp.lean`) is 6.65 at `wpG`: the lender chooses the lend's lifetime (H4),
lends `ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, runs the callback, and at its end (a value or a stop) turns the
cell back into `ℓ ↦ own(v″) ● χ` (6.27, 6.28). `wpG_M_frameAt` is the same printed proof with two
changes, so that a frame can lend again **at the lifetime it lent before, with the cell the stop
held**:

* **the lifetime is given**, not chosen: `A ⊏ β` and the resources in `Res_A` are hypotheses, the
  conditions H4 establishes. No other step reads how `A` was found;
* **the callback is given the cell the entry builds**, `viewCell` (no `ptoMutS` wand);
* **the end reports the cell's content**: the post (`ExitPost`) names the value `v″` and the
  payload `χ` handed back, and says whether the share at the end held the cell (then it is that
  cell, `ℓ ↦ mut(A, v″, χ, P̂)`) or had left it behind.

When the share holds the cell (a stop with the view live), the cell joins the leftover first, as
`wpG_garbage` does, and the exit is the printed one.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Alloc ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The predicate a lend of `ℓ : Ref T` stores, at the list `ls` and lifetime `A`. -/
def QsAt (T : VTy) (δ : LSub) (ls : List SRec) (A : Life) : Val → SPropS BoCa.Loc BoCa.Val A :=
  fun w r => vC true T ls δ w r.1

/-- The cell a lend of `ℓ` at `A` holds: `ℓ ↦ mut(A, v, ρ_P, 𝒱⟦T⟧δ)`. -/
def viewCell (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) (A : Life) (v : Val)
    (ρP : WRes) (h : ρP.InStratum A) (hw : vC true T ls δ v ρP) : WRes :=
  ResU.single l (CellU.mutOf A v ρP h (QsAt T δ ls A) hw)

/-- What the end of a lent run hands the frame: the callback's post `Y` at its share `ρ′`; the
value `v″` and payload `χ` the lend leaves in the cell; the share less the cell, `ρ₁`, which is
`ρ′` when the share no longer holds the cell; and the frame's resource `ρ₁ ● ℓ ↦ own(v″) ● χ`. -/
def ExitPost (l : BoCa.Loc) (T : VTy) (δ : LSub) (A : Life) (ls : List SRec)
    (Y : List SRec → Expr → WProp) : List SRec → Expr → WProp := fun ls'' t R =>
  ∃ (ρ' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A) (hw : QsAt T δ ls A v'' ⟨χ, hχ⟩)
    (ρ₁ y : WRes),
    Y ls'' t ρ' ∧ vC true T ls'' δ v'' χ ∧
    ((ρ'.get l = none ∧ ρ₁ = ρ') ∨
      ResU.CompS ρ₁ (ResU.single l (CellU.mutOf A v'' χ hχ (QsAt T δ ls A) hw)) ρ') ∧
    ResU.CompS ρ₁ (ResU.single l (CellU.ownOf v'')) y ∧ ResU.CompS y χ R

/-- A single `mut` cell carries no `own` cell. -/
theorem noOwn_single_mut (l : BoCa.Loc) (ψ : CellU BoCa.Loc BoCa.Val) (hk : ψ.kind ≠ Kind.own) :
    NoOwn (ResU.single l ψ) := by
  refine noOwn_iff.mpr fun m φ hm => ?_
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    exact hk
  · rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)

/-- **`[TR]` 6.65 at `wpG`, at a given lifetime, exactly.** The printed proof of `wpG_M_frameX`
with H4's lifetime `A` given (`hAβ`, `houtP`, `houtb` are what H4 establishes), the callback run
from the cell the entry builds, and the end reporting what the lend hands back (`ExitPost`). -/
theorem wpG_M_frameAt (l : BoCa.Loc) (T : VTy) (δ : LSub) (A β : Life) (hAβ : A ⊏ β)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (ρP ρb ρlP ρ : WRes) (hPv : vC true T ls δ v ρP) (houtP : ρP.InStratum A)
    (houtb : ρb.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (Y : List SRec → Expr → WProp)
    (hcb : ∀ BM, ResU.CompS ρb (viewCell l T δ ls A v ρP houtP hPv) BM → wpG ls e Y BM) :
    wpG ls e (ExitPost l T δ A ls Y) ρ := by
  classical
  intro ρf sρ ps hH3 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A := QsAt T δ ls A with hQs
  have hwit : Qs v ⟨ρP, houtP⟩ := hPv
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
  have hwpBM := hcb BM hBM
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBM ρf fρ ps hH17 h4 hTin htgin alc kc
  -- H26: 6.27 -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, hwit'', hsplit''⟩ := ResU.six27 houtb hBM h10
  have hπl : π.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rw [ResU.Comp.get_of_left_none hsplit'' (ResU.del_get_self _ _)]
    exact ResU.single_get_self _ _
  have hkm'' : (CellU.mutOf A v'' χ hχ Qs hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  -- the share keeps the view or has left it behind; either way it goes to the leftover
  obtain ⟨ρ₁, ρ₂, hc₁₂, hno₂, hρ₁l, hcase⟩ : ∃ ρ₁ ρ₂ : WRes, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
      ρ₁.get l = none ∧ ((ρ'.get l = none ∧ ρ₁ = ρ') ∨
        ResU.CompS ρ₁ (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) ρ') := by
    cases hg : ρ'.get l with
    | none => exact ⟨ρ', PMap.empty, ResU.CompS.comm (compS_empty_left ρ'), noOwn_empty, hg,
        Or.inl ⟨rfl, rfl⟩⟩
    | some c =>
        have hk : c.kind ≠ Kind.imm := by
          rcases ResU.CompS.get_split_of_ne_imm h9 hπl hkm'' with ⟨hg', -⟩ | ⟨hg', -⟩
          · rw [hg] at hg'; cases Option.some.inj hg'; exact hkm''
          · rw [hg] at hg'; cases hg'
        have hcπ := (ResU.CompS.get_left_of_ne_imm h9 hg hk).2
        rw [hπl] at hcπ
        cases Option.some.inj hcπ
        exact ⟨ρ'.del l, _, ResU.del_compS hg, noOwn_single_mut _ _ (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c), ResU.del_get_self _ _,
          Or.inr (ResU.del_compS hg)⟩
  -- the leftover with the view: `wpG_garbage`'s reassociation
  obtain ⟨hf₁, -⟩ := ResU.Hash.split hc₁₂ h1
  obtain ⟨F₁, hF₁, hF₁₂⟩ := (ResU.CompS.assoc ρf ρ₁ ρ₂ fρ').mp ⟨ρ', hc₁₂, h2⟩
  obtain ⟨Z, hZ, hFZ⟩ := (ResU.CompS.assoc F₁ ρ₂ ρp fρ'p).mpr ⟨fρ', hF₁₂, h6⟩
  obtain ⟨Z', hZ', h₁Z⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρp π).mpr ⟨ρ', hc₁₂, h9⟩
  cases ResU.CompS.functional hZ' hZ
  have hvf : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have h3' : ResU.Hash Z F₁ := ⟨(ResU.CompS.comm hFZ).1, fρ'p, ResU.CompS.comm hFZ, hvf⟩
  have h11' : NoOwn Z := noOwn_compS hZ hno₂ h11
  have hppl : Z.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rcases ResU.CompS.get_split_of_ne_imm h₁Z hπl hkm'' with ⟨hg, -⟩ | ⟨-, hp⟩
    · rw [hρ₁l] at hg; cases hg
    · exact hp
  have hpd : ResU.CompS (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) Z := ResU.del_compS hppl
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ₁ (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) π).mp ⟨Z, hpd, h₁Z⟩
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split hF₁ (ResU.hash_symm h3')
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ₁ W'').mpr hρ'W''.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm hf₁) hρ'W'' hfm'' hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (Z.del l) R :=
    ResU.hash_of_pairwise hρ'PD hρ'W'' hPDW'' hR
  have hPDFR : ResU.Hash (Z.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ := (ResU.compS_defined_iff FR (Z.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ := (ResU.compS_defined_iff R (Z.del l)).mpr (ResU.hash_symm hPDR).1
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
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc F₁ (Z.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) fρ'p).mp ⟨Z, hpd, hFZ⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (Z.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ₁ W'' (Z.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨RPD₁, hRPD₁, hRPDW⟩ :=
    (ResU.CompS.assoc ρ₁ (Z.del l) W'' RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : RPD = RPD₁ := ResU.CompS.functional hRPD hRPD₁
  obtain ⟨FPD, hFPD, hFPDW⟩ :=
    (ResU.CompS.assoc ρf RPD W'' FRP).mp ⟨RP, hRPDW, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ₁ (Z.del l) FP).mpr ⟨F₁, hF₁, hFP⟩
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
  have hno : BoLo.NoOwn (Z.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((Z.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (Z.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11'] at hcc
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
    (ResU.CompS.assoc ρ₁ (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : ExitPost l T δ A ls Y ls'' v' R :=
    ⟨ρ', v'', χ, hχ, hwit'', ρ₁, y, h12, hχv, hcase, hy₁, hy₂⟩
  exact ⟨R, Z.del l, FR, FRP, RP, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

end SuspSpike

end
