import Core.Chain.SI.BindN
import Core.Chain.SI.ExtF

/-!
# Unknown 1: a `mut` lend live across a stop, at `erwp`

**Not a transcription.** `[TR]` 6.65 is a lemma about a run that returns. `rwpG` asks its
post-configuration, `ρ ↭ₙ π`, at every final configuration, stops included; at a stop inside a
Mut Frame the lent cell is `mut` in `π` and `own` in `ρ`, and `↭`'s `mut` clause fails from right
to left. `Core`'s frames over `ewpTS` are for that reason restricted to abortive tables, where the
stop ends the lend (`ewpTS_M_frameU`).

## The design: fold at the stop, re-lend at the resume

At a stop the lender does at the stop what `[TR]` 6.65's proof does at the return: 6.27 finds the
borrow at the top level of `π` (`six27Nd`), and the lender folds it back, `ℓ ↦ mut(A, v″, χ, P̂″)`
replaced by `ℓ ↦ own(v″) ● χ` (`rwpG_M_frameG`, the printed proof's H26–H34 at any final term).
Folding changes nothing in the memory (`ResU.lower_swap_mut_own`, 6.25 under a frame), and `↭`
holds by 6.28 at the index (`six28N_fwd`) exactly as at a return. The folded cell goes into the
continuation's share. When the continuation is resumed at `k′ < k`, the lender lends the cell
again (`erwp_M_frame` at `k′`, by induction on the index) with the stored predicate `P̂″` the
borrowed continuation holds, which lies in `F k` by the step from the first lend
(`PredStep`), so the read-back at the end still finds the content in the family.

This is the program's segmentation at its stops done in the logic instead of in the program: the
term is not cut,
and the lend's lifetime `A` is the same in every segment.

## What is new, and the conditions it needs

* The frame's table: every entry is non-abortive and must-resume (`OpTabN.LendOK`). An abortive
  stop would return the folded cell with a `raise`, which owns nothing (`raiseStopN`); an
  unrestricted continuation owns nothing; a cancellable one owes a cancel run that cannot return
  the lender's cell. Those three need a finaliser frame around the lend (step 3).
* The payload passed out does not hold the borrow (`PA` in `Res_A`), and the answer passed in
  holds nothing shorter than the lend (`PB` in `Res_{↓A}`): what crosses a lend's boundary
  outlives the lend, as the returned value does in 6.65 (`[α]`).
* The world condition of the continuation (`OpEntN.wc`) is `extF` (`SI/ExtF.lean`): the
  continuation is resumed at any list that keeps the records its share's frozen locations name.
  The fold moves the borrow's content `χ` from the cell's witness to the top of the share, so it
  keeps every frozen location (`extF_fold`): what the handler keeps at the lender's share, the
  borrowed continuation's share needs. `Core`'s `Ext` would not do: its lifetime clause reads
  the share's cells, and the folded share has no cell at `A` (`not_extFoldTransfer`).

## Soundness

The lender's post-configuration at a stop is `wpTS`'s, unchanged: its resource lowers to the
memory, `ρ ↭ π` holds, and the stop is the table's at the lender's resource. The only resource
moved is the lent cell, from `mut` back to `own`, and that move is the one 6.65 makes at a
return. What the borrowed continuation needs at its resume is exactly what the lender supplies
again: the same `mut` cell, at a frame whose other cells outlive `A`, at a list keeping every
record the borrowed continuation's views name.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- A composite with a non-`imm` singleton determines the other factor. -/
theorem compS_single_cancel {D D' X : WRes} {l : Loc} {ψ : CellU Loc Val}
    (hk : ψ.kind ≠ Kind.imm) (h : ResU.CompS D (ResU.single l ψ) X)
    (h' : ResU.CompS D' (ResU.single l ψ) X) : D = D' := by
  refine PMap.ext fun m => ?_
  by_cases hm : m = l
  · subst hm
    rw [(ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h) (ResU.single_get_self _ _) hk).1,
      (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h') (ResU.single_get_self _ _) hk).1]
  · rw [← ResU.Comp.get_of_right_none h (ResU.single_get_ne ψ hm),
      ← ResU.Comp.get_of_right_none h' (ResU.single_get_ne ψ hm)]

/-- `six27N` with the frame in `Res_{↓α}`: the step of its proof that reads `hout` asks only
that. -/
theorem six27Nd {Φ : LocFam} {k : Nat} {l : Loc} {α : Life} {v : Val} {ρ ρv M ρ' : WRes}
    {h : ResU.InStratum α ρv} {P : Val → SPropS Loc Val α} {hw : P v ⟨ρv, h⟩}
    (hout : ResU.InStratum (↓α) ρ)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M)
    (hu : UpdVN Φ k M ρ') :
    ∃ (v' : Val) (χ : WRes) (h' : ResU.InStratum α χ) (P' : Val → SPropS Loc Val α)
      (hw' : P' v' ⟨χ, h'⟩),
      MutStep Φ k l (CellU.mutOf α v ρv h P hw) (CellU.mutOf α v' χ h' P' hw') ∧
      ResU.CompS (ρ'.del l) (ResU.single l (CellU.mutOf α v' χ h' P' hw')) ρ' := by
  classical
  have hkm : (CellU.mutOf α v ρv h P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hMl : M.get l = some (CellU.mutOf α v ρv h P hw) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM)
      (ResU.single_get_self _ _) hkm).2
  have hσl : σ.get l = some (CellU.mutOf α v ρv h P hw) :=
    ResU.flat_get_of_ne_imm hσ hMl hkm
  obtain ⟨ψ', hfa', hs⟩ := hu.1.2.1 l _ ⟨σ, hσ, hσl⟩ rfl
  rcases CellU.rep ψ' with ⟨u, rfl⟩ | ⟨s', u, τ, m, rfl⟩ | ⟨b', v', χ, h', P', hw', rfl⟩
  · exact absurd hs.2.1 (by simp)
  · exact absurd hs.2.1 (by simp)
  have hb' : α = b' := hs.2.2.1
  subst hb'
  have hflat := (ResU.flatAt_iff hσ' _ _).mp hfa'
  have hdM : M.InStratum (↓α) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓α)) hM
      hout
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓α) α v ρv h P hw).mpr
        (Life.down_sqsubset α)))
  have hd' : ρ'.InStratum (↓α) := updVN_inStratum hdM hu
  have hρ'l : ρ'.get l ≠ none := by
    intro hnone
    have hcon := ResU.flat_inStratum_at hσ' hd'
      (fun φ e => absurd (hnone ▸ e) (by simp)) hflat
    rw [CellU.inStratum_mutOf] at hcon
    exact absurd hcon (lt_irrefl _)
  obtain ⟨φ, hφ⟩ : ∃ φ, ρ'.get l = some φ := by
    cases hg : ρ'.get l with
    | none => exact absurd hg hρ'l
    | some φ => exact ⟨φ, rfl⟩
  obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResU.Flat.get hσ' hφ
  rw [hflat] at hχ₀
  obtain rfl : χ₀ = CellU.mutOf α v' χ h' P' hw' := (Option.some.inj hχ₀).symm
  have hkφ : φ.kind ≠ Kind.imm := by
    rw [← hk₀, CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hgg : σ'.get l = some φ := ResU.flat_get_of_ne_imm hσ' hφ hkφ
  rw [hflat] at hgg
  obtain rfl : φ = CellU.mutOf α v' χ h' P' hw' := (Option.some.inj hgg).symm
  exact ⟨v', χ, h', P', hw', hs, ResU.del_compS hφ⟩


/-! ### The fold, at any final term -/

/-- **The lender's side of a Mut Frame at any final term** (`[TR]` 6.65's proof at `rwpG`). The
borrowed run, at `Φ[ℓ ↦ (A, F)]` from `ρ_b ● ℓ ↦ mut(A, v, ρ_P, P̂)`, ends at a final term;
6.27 at the index finds the borrow at the top level of `π`, now `mut(A, v″, χ, P̂″)` with
`P̂″ ⊆ F k`; the lender's resource is `π/ℓ ● χ ● ℓ ↦ own(v″)`, split by `hpost` into the
post-configuration's two parts. The memory, the typed world and `↭` are the printed proof's
(H33, exit, H34). -/
theorem rwpG_M_frameG {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {Qin Qout : PostG} {n j : Nat}
    (hjn : n ≤ j) {ls : List SRec} {e : Expr} {v : Val} {ρP ρlP ρb ρ : WRes}
    (houtP : ρP.InStratum A) (houtb : ρb.InStratum (↓A))
    {P : Val → SPropS Loc Val A} (hPF : ∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r)
    (hwit : P v ⟨ρP, houtP⟩)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hpost : ∀ k, k ≤ n → ∀ ls' t (ρ' ρp X : WRes), Qin k ls' t ρ' → NoOwn ρp →
      ResU.CompS ρ' ρp X → X.InStratum (↓A) →
      ∀ (v'' : Val) (χ : WRes) (hχ : χ.InStratum A) (P'' : Val → SPropS Loc Val A)
        (hw'' : P'' v'' ⟨χ, hχ⟩), (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
      ResU.CompS (X.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X →
      ∀ W'', ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' →
      ∀ Y, ResU.CompS (X.del l) W'' Y →
      ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls' t ρ'L)
    (hA : ∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
      rwpG (ℍ := ℍ) (Φ.set l A F) Qin n ls e BM) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ := by
  classical
  intro ρf sρ ps μ hH3 hsρ hT htg hI hlow hfd jr μ' e' hj hrun hfin
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP P hwit) with hρm
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
  -- entry: `TWNC.mutFold`, and the same memory (6.25 under a frame)
  have hTin : TWNC fρ ps (rsOf ls) :=
    TWNC.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
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
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mpr hlow
  -- H18: the borrowed run, at `Φ[ℓ ↦ (A, F)]`
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ := hA BM hBM ρf fρ ps μ hH17 h4 hTin htgin hI hlowin hfd jr μ' e' hj hrun hfin
  -- H26: 6.27 at the index
  have hdBM : BM.InStratum (↓A) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓A)) hBM houtb
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓A) A v ρP houtP P hwit).mpr
        (Life.down_sqsubset A)))
  have hdπ : π.InStratum (↓A) := updVN_inStratum hdBM h10
  obtain ⟨v'', χ, hχ, P'', hwit'', hstep, hsplit''⟩ := six27Nd houtb hBM h10
  -- the stored predicate after the run lies in the family's member at the index left
  have hFl : Φ.set l A F l = some ⟨A, F⟩ := by simp [LocFam.set]
  have hPk : ∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F (n - jr) u) r := by
    intro u r hu
    rcases hstep.2.2.2.2 A F hFl u r ((mpred_mutOf u r).mpr hu) with h | h
    · obtain ⟨hs, hj'⟩ := hPF u r ((mpred_mutOf u r).mp h)
      exact ⟨hs, hF.le (by omega) u _ hj'⟩
    · exact h
  -- the folded resource `π/ℓ ● χ ● ℓ ↦ own(v″)`
  have hvπ : ResU.Valid π := h10.2.2
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    (ResU.Valid.split hsplit'' hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash (π.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    ⟨hsplit''.1, π, hsplit'', hvπ⟩
  have hH27 : ResU.Hash (π.del l) W'' := (ResU.six24 hW'').mp hRPDmH
  have hvW'' : ResU.Valid W'' := by
    obtain ⟨-, s, hs, hv⟩ := hH27; exact (ResU.Valid.split hs hv).2
  obtain ⟨Y, hY⟩ := (ResU.compS_defined_iff (π.del l) W'').mpr hH27.1
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  obtain ⟨π₁, hπ₁, hfπ⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ'p).mpr ⟨fρ', h2, h6⟩
  obtain rfl : π = π₁ := ResU.CompS.functional h9 hπ₁
  have hfπH : ResU.Hash π ρf := ⟨(ResU.CompS.comm hfπ).1, fρ'p, ResU.CompS.comm hfπ, hvfρ'p⟩
  obtain ⟨hDf, hmf⟩ := ResU.Hash.split hsplit'' hfπH
  have hfm'' : ResU.Hash ρf W'' := (ResU.six24 hW'').mp (ResU.hash_symm hmf)
  have hfY : ResU.Hash ρf Y := ResU.hash_of_pairwise (ResU.hash_symm hDf) hH27 hfm'' hY
  obtain ⟨FY, hFY, hvFY⟩ := hfY.2
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc ρf (π.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) fρ'p).mp ⟨π, hsplit'', hfπ⟩
  obtain ⟨FP₁, hFP₁, hFPW⟩ := (ResU.CompS.assoc ρf (π.del l) W'' FY).mp ⟨Y, hY, hFY⟩
  obtain rfl : FP = FP₁ := ResU.CompS.functional hFP hFP₁
  have hFPmH : ResU.Hash FP (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    ⟨hFPm.1, fρ'p, hFPm, hvfρ'p⟩
  have hFPWH : ResU.Hash FP W'' := ⟨hFPW.1, FY, hFPW, hvFY⟩
  -- H33: the memory, by 6.25 under a frame
  have hmem₂ : ResU.Lower FY μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFPm hFPmH hFPW hFPWH).mp h7
  -- H34: `ρ ↭ₖ π/ℓ ● χ ● ℓ ↦ own(v″)`, by 6.28 at the index
  have hvY : ResU.Valid Y := (ResU.Valid.split hFY hvFY).2
  have hupd : UpdN Φ (n - jr) ρ Y :=
    six28N_fwd (Φ.set_agree l A F) hlPcell hW'' hBM hsplit'' (ResU.CompS.comm hcρ) hY
      hvBM hvπ hvρ hvY h10.1
  -- exit: `TWNC.mutUnfold`
  have hTout : TWNC FY ps'' (rsOf ls'') :=
    TWNC.mutUnfold hT'' (ResU.CompS.comm hFPm) (ResU.CompS.comm hW'')
      (ResU.CompS.comm hFPW) hvFY
  have htgout : Tagged FY ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFPW) (ResU.CompS.comm hFPm) a).mp
      ha) htg''
  -- the lender's post-configuration
  obtain ⟨ρ'L, ρpL, hLY, hnoL, hQ⟩ := hpost (n - jr) (by omega) ls'' e' ρ' ρp π h12 h11 h9 hdπ
    v'' χ hχ P'' hwit'' hPk hsplit'' W'' hW'' Y hY
  obtain ⟨fL, hf1, hf2⟩ := (ResU.CompS.assoc ρf ρ'L ρpL FY).mp ⟨Y, hLY, hFY⟩
  have hvfL : ResU.Valid fL := (ResU.Valid.split hf2 hvFY).1
  exact ⟨ρ'L, ρpL, fL, FY, Y, ps'', ls'', ⟨(ResU.CompS.comm hf1).1, fL, ResU.CompS.comm hf1, hvfL⟩,
    hf1, ⟨(ResU.CompS.comm hf2).1, FY, ResU.CompS.comm hf2, hvFY⟩, hf2, hmem₂, hLY,
    ⟨hupd, hvρ, hvY⟩, hnoL, hTout, htgout, hps'', hls'', hQ⟩

/-! ### The frame rule across stops -/

/-- **`extF` across the fold.** The continuation's share `ρ_k` is a part of `Z`, whose cell at
`ℓ` is the borrow `ℓ ↦ mut(A, v″, χ)`; the lender's share is `Z/ℓ ● W″`, `W″ = χ ● ℓ ↦ own(v″)`. A
location frozen in `ρ_k` is frozen in `Z/ℓ` or in `χ` (`Frz.del_or`), so in the lender's share:
what the lender's resumption keeps, the borrowed continuation's does. -/
theorem extF_fold {ls ls' : List SRec} {ρk ρp Z W'' ρkL χ : WRes} {l : Loc} {v : Val}
    {ψ : CellU Loc Val} (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some ψ)
    (hk : ψ.kind = Kind.mut) (hwit : ψ.wit = χ)
    (hW'' : ResU.CompS χ (ResU.single l (CellU.ownOf v)) W'')
    (hkL : ResU.CompS (Z.del l) W'' ρkL) (h : extF ls ls' ρkL) : extF ls ls' ρk := by
  intro r hr ⟨m, hf, hm⟩
  refine h r hr ⟨m, ?_, hm⟩
  rcases (hf.of_compS_left hZ).del_or (l := l) with hd | ⟨φ, eφ, hφ⟩
  · exact hd.of_compS_left hkL
  · rw [hZl] at eφ; cases Option.some.inj eφ
    rcases hφ with ⟨ki, -⟩ | ⟨-, hw⟩
    · rw [hk] at ki; cases ki
    · rw [hwit] at hw
      exact (hw.of_compS_left hW'').of_compS_right hkL

/-- **A table whose stops may be taken under a live `mut` lend at `A`.** Every entry is
non-abortive and must-resume, resumed under `extF`; what it passes out outlives `A`, and
what it passes in holds nothing shorter than `A`. -/
structure OpTabN.LendOK (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

theorem noOwn_del {ρ : WRes} (h : NoOwn ρ) (l : Loc) : NoOwn (ρ.del l) := by
  classical
  refine PMap.ext fun x => ?_
  cases hgg : ((ρ.del l).restrict Kind.own).get x with
  | none => simp
  | some ψ =>
      exfalso
      obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
      by_cases hx : x = l
      · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
      · rw [ResU.del_get_ne _ hx] at hdd
        have hcc : (ρ.restrict Kind.own).get x = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
        rw [h] at hcc
        simp at hcc

/-- **Mut Frame at `erwp`, across stops.** `ℓ ↦ v ⋆ ρ_P ⋆ ρ_b`, lent at `A` with the stored
predicate `P̂ ⊆ F j`, `j ≥ n`, to a computation in `erwp` at `Φ[ℓ ↦ (A, F)]` that may stop at a
`LendOK` table with the lend live: the computation is in `erwp` at `Φ`. At a return, 6.65; at a
stop, the cell folded into the continuation's share; at the resume, lent again at the index the
resume is at, by induction on the index. -/
theorem erwp_M_frame {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.65's end -- the borrow is garbage, the content read back in `F k`
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow is in the continuation's share; fold it there
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    -- the frame of the second segment: `Z/ℓ ● σ_B`
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    -- the borrowed continuation, at the frame, with the garbage `ρ⁺` added
    have he' : en.wc ls' ls'' ρk := by
      rw [hwc] at he ⊢
      exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ := (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkp hnoρp hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
