import Core.Chain.SI.RebChooseC
import Core.Chain.SI.IStopN
import Core.Chain.SI.LinDisj

/-!
# `[TR]` 6.150 at any final term, at a canonical image

**Not a transcription.** `rwpG_rebG` is `rwp_reborrow`'s proof (H1–H33) at `rwpG`, at a lifetime
`β` and an image `canon r β` the caller fixes, ending at whatever final term. Its changes:

* **The image is the canonical one** (`SI/TWNC.lean`): `χ := canon r β`, and the agreement 6.55
  needs is `canon_escrowAgree` at the entry world, lifted to the frame and to the cell. The
  chooser's other outputs are read off the template (`canon_reb`, `agW_relRes`), and the entry is
  `TWNC.reb` with `RebRecLe` read off the world (`rebRecLe_global`).
* **`β` is not below the frame.** H11 chooses `β` below the world `ρ_f ● ρ`; here `β` is fixed
  before the frame is known (at a resume the frame, and the list, are whatever the handler
  holds). H11 is read in two places in `rwp_reborrow`: the chooser's entry premise, replaced by
  `RebRecLe` from `β ⊑ s` (`hβs`, the part of H11 that reads the record's cell) and the
  disjointness of lineages (`rebRecLe_global`), and the exit's `W″ ∈ Res_β`, replaced by
  `RebEndRec` from 6.59 and 6.48 (`rebEndRec_of_updImm`): the entry world and the exit world are
  related by the `imm` clause of `↭`, which is what `rebEnd`'s premise reads.
* **6.52 and 6.59 at a split the caller names.** The printed proof applies 6.52 at `ρ″ :=` the
  returned resource and `ρ⁺ :=` the garbage. `hpost` splits the inner run's final resource
  `ρ′ = ρₒ ● ρₖ` with `ρₒ ∈ Res_β`; 6.52 and 6.59 are applied at `ρ″ := ρₒ`, `ρ⁺ := ρₖ ● ρ⁺`. At a
  return `ρₖ = ∅` and this is the printed step. At a stop `ρₒ` is the payload and `ρₖ` the
  continuation's share: the reborrow's exclusive part is split off the share (6.52's `ψ`), which
  is the fold.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)
open BoCa.Lifetime (LSub LifeVar)

/-- The agreement `[TR]` 6.55 asks for, at the frame and at the cell, from `canon_escrowAgree`
at the world they compose. -/
theorem canon_agree_split {W F : WRes} {ps rs : List FrameRec} {r : FrameRec} {le : Loc}
    {s : LSet} {hs : r.R.InStratum s.join} (hT : TWNC W ps rs) (hr : r ∈ rs)
    (hS : TmplSpec r (tmpl r)) (β : Life)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W) :
    (∀ a, AgW F a → EscrowAgree r.R (canon r β) a) ∧
      (∀ a, AgW (ResU.single le (CellU.immOf s r.v r.R hs)) a →
        EscrowAgree r.R (canon r β) a) := by
  obtain ⟨-, e, aW, -, haW, -⟩ := hT.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  have hW_agree := canon_escrowAgree hT hr hS β
  have liftG : ∀ G, (G = F ∨ G = ResU.single le (CellU.immOf s r.v r.R hs)) →
      ∀ a, AgW G a → EscrowAgree r.R (canon r β) a := by
    rintro G hG a ha l v ψ ψf hown hψ hψf hk hkf
    have hlift : ∃ ψ', aW.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ'.wit = ψf.wit := by
      rcases hG with rfl | rfl
      · rw [AgW.functional ha h₂] at hψf; exact lift_view hc.comm hψf hkf
      · rw [AgW.functional ha h₁] at hψf; exact lift_view hc hψf hkf
    obtain ⟨ψ', e', k', w'⟩ := hlift
    exact w'.symm.trans (hW_agree aW haW l v ψ ψ' hown hψ e' hk k')
  exact ⟨liftG F (Or.inl rfl), liftG _ (Or.inr rfl)⟩

/-- **`[TR]` 6.150 at any final term, at a canonical image.** The lender holds the record's cell
`ρᵢ` and `ρ_b ∈ Res_β`; the borrowed run is handed `ρ_b ● canon r β`. At the end, `hpost` splits
the run's resource `ρ′ = ρₒ ● ρₖ`, `ρₒ ∈ Res_β`, and is given 6.52's `ψ`
(`ψ ● (canon r β)|dom(ρ′|mut,own) = ρₖ ● ρ⁺`, `ψ ∈ Res_β`); it splits `ρₒ ● ψ ● ρᵢ` for the
lender. -/
theorem rwpG_rebG {Φ : LocFam} (r : FrameRec) (x : LifeVar) (hx : ¬ VFree x r.T) {β : Life}
    {s : LSet} {hs : r.R.InStratum s.join} (hS : TmplSpec r (tmpl r))
    (hRβ : r.R.InStratum β)
    (hshape : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β))
    {ρb ρ : WRes} (hc : ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρb ρ)
    (h15 : ρb.InStratum β) {ls : List SRec} (hr : r ∈ rsOf ls) (hβs : ∀ y, s.mem y → β ⊑ y)
    {Qin Qout : PostG} {n : Nat} {e : Expr}
    (hpost : ∀ k, k ≤ n → ∀ ls'' t (ρ' : WRes), Qin k ls'' t ρ' → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
        ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
          ResU.SubKeep w ((canon r β).restrictDom r.R.exclPart) ψ →
          ResU.CompS ψ ((canon r β).restrictDom r.R.exclPart) w → ψ.InStratum β →
          ResU.CompS ρo ψ Yo →
          ResU.CompS Yo (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y →
          ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls'' t ρ'L)
    (hA : ∀ Bχ, ResU.CompS ρb (canon r β) Bχ → rwpG (ℍ := ℍ) Φ Qin n ls e Bχ) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hl hfd jr μ' e' hj hrun hfin
  set χ : WRes := canon r β with hχdef
  set ρi : WRes := ResU.single r.le (CellU.immOf s r.v r.R hs) with hρidef
  have hreb : ResU.Reb β r.R χ := canon_reb hS hRβ
  have hagχ : ∃ A, AgW χ A := by
    obtain ⟨β₀, x₀, -, hreb₀, -, hA₀⟩ := hS
    obtain ⟨A₀, hA₀⟩ := hA₀
    exact agW_relRes (fun m ψ e => (reb_cell hreb₀ e).1) hA₀
  obtain ⟨A, hagχ⟩ := hagχ
  -- H18
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  have h18 : ResU.Hash ρi ρb := ⟨hc.1, ρ, hc, hvρ⟩
  have hbi : ResU.Hash ρb ρi := ResU.hash_symm h18
  obtain ⟨ρbf, hbf, hbfi⟩ :=
    (hash_shift ρf ρb ρi).mp ⟨ρ, ResU.CompS.comm hc, hf⟩
  have hWcell : ResU.CompS ρi ρbf fρ := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' (ResU.CompS.comm hc) hcf
    rw [ResU.CompS.functional hab hbf] at hab'
    exact ResU.CompS.comm hab'
  -- the canonical image agrees with the frame and with the cell (6.55's input)
  obtain ⟨hEF, hEI⟩ := canon_agree_split hT hr hS β hWcell
  have h19' : ResU.Hash ρbf χ := ResU.six55 hreb hEF hagχ hbfi
  have h19 : ResU.Hash ρb χ := (ResU.Hash.split hbf h19').2
  obtain ⟨ρbχ, hbχ⟩ := (ResU.compS_defined_iff ρb χ).mpr h19.1
  have hvi : ResU.Valid ρi := (hash_valid hbi).2
  have h55self : ResU.Hash χ ρi :=
    ResU.six55_self hreb hEI hagχ (ResU.hash_self_single_imm hvi)
  have hiρbf : ResU.Hash ρi ρbf := ResU.hash_symm hbfi
  have h20 : ResU.Hash χ fρ := ResU.hash_of_pairwise h55self hiρbf (ResU.hash_symm h19') hWcell
  obtain ⟨ρF, hF, hFb⟩ := compS_reassoc' hbf hWcell
  have hFbχ : ResU.Hash ρF ρbχ := by
    obtain ⟨x, hx, hxh⟩ := (hash_shift ρF ρb χ).mpr ⟨fρ, hFb, ResU.hash_symm h20⟩
    rwa [ResU.CompS.functional hx hbχ] at hxh
  obtain ⟨Win, hWin, hvWin⟩ := hFbχ.2
  have hfχ : ResU.CompS fρ χ Win := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hbχ hWin
    rwa [ResU.CompS.functional hab hFb] at hab'
  -- entry: `TWNC.reb` at the canonical image, `RebRecLe` read off the world
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hWcell
  have hrebLe := rebRecLe_global hT hr ⟨ρbf, hWcell⟩ hβs
  have hTin : TWNC Win ps (rsOf ls) :=
    TWNC.reb r x hT hr hle hx hreb hshape hrebLe rfl hfχ hvWin
  have htgin : Tagged Win ps ls := tagged_rebN hT.toN hr hle hreb hrebLe hfχ htg
  -- the inner run
  obtain ⟨t1, ht1, ht1'⟩ := compS_reassoc hF hWin
  obtain ⟨u1, hu1, hu1'⟩ := compS_reassoc' hbχ ht1
  rw [ResU.CompS.functional hu1 hbf] at hu1'
  obtain ⟨Y58, hY58⟩ := (ResU.compS_defined_iff ρbf ρi).mpr hbfi.1
  have h58L := ResU.six58_left hreb hEI hagχ (ResU.hash_symm h19')
    hbfi (ResU.CompS.comm hu1') (ResU.CompS.comm ht1') hY58
  obtain ⟨ac, hac, hac'⟩ := compS_exch hbf hY58
  obtain ⟨t2, ht2, ht2'⟩ := compS_reassoc hac hac'
  rw [ResU.CompS.functional ht2 hc] at ht2'
  rw [ResU.CompS.functional ht2' hcf] at h58L
  have g5 : ResU.Lower Win μ := (h58L μ).mpr hl
  obtain ⟨ρQ, ρp, fρ', fρ'p, π, ps', ls', g1, g2, g3, g6, g7, g9, gA, gB,
    gT, gtg, gps, gls, gC⟩ :=
    hA ρbχ hbχ ρF Win ps μ hFbχ hWin hTin htgin g5 hfd jr μ' e' hj hrun hfin
  -- the caller's split `ρ′ = ρₒ ● ρₖ`, and `π = ρₒ ● (ρₖ ● ρ⁺)`
  obtain ⟨ρo, ρk, hok, hoβ, hcont⟩ := hpost (n - jr) (by omega) ls' e' ρQ gC gls
  obtain ⟨w, hw, hπ⟩ := compS_reassoc hok g9
  obtain ⟨fρo, g2', g2''⟩ := compS_reassoc' hok g2
  obtain ⟨u, hu, hfρ'p⟩ := compS_reassoc g2'' g6
  rw [ResU.CompS.functional hu hw] at hfρ'p
  -- 6.52 at `ρ″ := ρₒ`, `ρ⁺ := ρₖ ● ρ⁺`
  obtain ⟨ψ, hsubK, hsplit, hψβ⟩ :=
    six52_keepN hreb (ResU.CompS.comm hbχ) hπ gA h15 hoβ
  have hvfp : ResU.Valid fρ'p := by obtain ⟨τ, hτ, -⟩ := g7; exact ⟨τ, hτ⟩
  have hvfo : ResU.Valid fρo := (ResU.Valid.split hfρ'p hvfp).1
  have g1' : ResU.Hash ρo ρF := ResU.hash_symm ⟨g2'.1, fρo, g2', hvfo⟩
  have g3' : ResU.Hash w fρo := ResU.hash_symm ⟨hfρ'p.1, fρ'p, hfρ'p, hvfp⟩
  have g6' : ResU.CompS fρo w fρ'p := hfρ'p
  -- 6.11 at the `#`s the inner `wp` produced.
  obtain ⟨hiQ, hfQ⟩ := ResU.Hash.split hF (ResU.hash_symm g1')
  obtain ⟨hFp, hQp⟩ := ResU.Hash.split g2' (ResU.hash_symm g3')
  obtain ⟨hip, hfp⟩ := ResU.Hash.split hF hFp
  obtain ⟨hψQ, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hQp)
  obtain ⟨hψi, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hip)
  have hvfp' : ResU.Valid fρ'p := hvfp
  -- The target memory: `⟦ρᵢ ● ρ_f ● ρ_Q ● ρ⁺⟧` regrouped as 6.58's `ρ′ ● ρ⁺ ● ρᵢ`.
  obtain ⟨t3, ht3, ht3'⟩ := compS_reassoc hF g2'
  obtain ⟨u3, hu3, hu3'⟩ := compS_reassoc ht3' g6'
  have hiu3 : ResU.Hash (ResU.single r.le (CellU.immOf s r.v r.R hs)) u3 :=
    ⟨hu3'.1, fρ'p, hu3', hvfp⟩
  have hvu3 : ResU.Valid u3 := (ResU.Valid.split hu3' hvfp).2
  have ht3p : ResU.Hash t3 w := ⟨hu3.1, u3, hu3, hvu3⟩
  obtain ⟨hψt3, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm ht3p)
  obtain ⟨ρ'χ, hρ'χ⟩ := (ResU.compS_defined_iff t3 ψ).mpr (ResU.hash_symm hψt3).1
  obtain ⟨ht3i, -⟩ := ResU.Hash.split hu3 (ResU.hash_symm hiu3)
  have hiρ'χ : ResU.Hash (ResU.single r.le (CellU.immOf s r.v r.R hs)) ρ'χ :=
    ResU.hash_of_pairwise (ResU.hash_symm ht3i) (ResU.hash_symm hψt3)
      (ResU.hash_symm hψi) hρ'χ
  obtain ⟨Q58, hQ58⟩ :=
    (ResU.compS_defined_iff ρ'χ (ResU.single r.le (CellU.immOf s r.v r.R hs))).mpr
      (ResU.hash_symm hiρ'χ).1
  -- *"…with lemma 6.58"* — the second conclusion.
  have h58R := ResU.six58_right hreb hEI hagχ (ResU.hash_symm hiu3)
    hu3 hsubK.toSub hsplit hρ'χ (ResU.CompS.comm hu3') hQ58
  have hLQ : ResU.Lower Q58 μ' := (h58R μ').mp g7
  -- H33, by lemma 6.59.
  have hiπ : ResU.Hash (ResU.single r.le (CellU.immOf s r.v r.R hs)) π :=
    ResU.hash_of_pairwise hiQ hQp hip hπ
  obtain ⟨w59, hw59⟩ := (ResU.compS_defined_iff ρo ψ).mpr (ResU.hash_symm hψQ).1
  have hiw59 : ResU.Hash (ResU.single r.le (CellU.immOf s r.v r.R hs)) w59 :=
    ResU.hash_of_pairwise hiQ (ResU.hash_symm hψQ) (ResU.hash_symm hψi) hw59
  obtain ⟨Y59, hY59⟩ :=
    (ResU.compS_defined_iff w59 (ResU.single r.le (CellU.immOf s r.v r.R hs))).mpr
      (ResU.hash_symm hiw59).1
  have hvY59 : ResU.Valid Y59 := hash_valid_comp (ResU.hash_symm hiw59) hY59
  obtain ⟨σX, hσX⟩ := id hvρ
  obtain ⟨σY, hσY⟩ := id hvY59
  have h59 : UpdN Φ (n - jr) ρ Y59 :=
    six59N hreb (ResU.CompS.comm hbχ) hπ gA h15 hoβ (ResU.hash_symm h18)
      (ResU.hash_symm hiπ) hsubK hc ⟨w59, hw59, hY59⟩ hσX hσY
  -- the caller's split of `ρₒ ● ψ ● ρᵢ`
  obtain ⟨ρ'L, ρpL, hLY, hnoL, hQout⟩ := hcont ρp w ψ w59 Y59 gB hw hsubK hsplit hψβ hw59 hY59
  -- the final world is `ρ_f ● Y`
  obtain ⟨X1, hX1, hX1'⟩ := compS_reassoc ht3 hρ'χ
  have hFY : ResU.CompS ρf Y59 Q58 := by
    obtain ⟨X2, hX2, hX2'⟩ := compS_reassoc hX1' hQ58
    obtain rfl : w59 = X1 := ResU.CompS.functional hw59 hX1
    rwa [ResU.CompS.functional hX2 hY59] at hX2'
  have hvQ : ResU.Valid Q58 := by obtain ⟨τ, hτ, -⟩ := hLQ; exact ⟨τ, hτ⟩
  -- exit: `TWNC.rebEnd`, its premise from 6.59 and 6.48 (`rebEndRec_of_updImm`)
  have hexW : ResU.CompS Q58 (χ.restrictDom r.R.exclPart) fρ'p := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hsplit hu3
    rw [ResU.CompS.functional hab hρ'χ] at hab'
    obtain ⟨ab', hab₂, hab₂'⟩ := compS_reassoc' hab' hu3'
    rwa [ResU.CompS.functional hab₂ (ResU.CompS.comm hQ58)] at hab₂'
  obtain ⟨s'', hs'', hcellQ⟩ := cell_of_compS_single (ResU.CompS.comm hQ58)
  have hupdF : UpdVN Φ (n - jr) fρ Q58 :=
    updVN_frame hcf hFY hf ⟨hFY.1, Q58, hFY, hvQ⟩ ⟨h59, hvρ, hvY59⟩
  have hEnd₀ := rebEndRec_of_updImm hT.toN hvQ hupdF.1.1 r.R β
  have hEnd : RebEndRec Q58 (rsOf ls') r.R β := by
    intro r' hr' l₀ m S u hc hex a' ha' ψ' s₁ e₁ hs₁ y hy hyβ
    have hr'' : r' ∈ rsOf ls := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr'; exact mem_rsOf.mpr ⟨t, (gls _).mp ht⟩
    exact hEnd₀ r' hr'' l₀ m S u hc hex a' ha' ψ' s₁ e₁ hs₁ y hy hyβ
  have hr' : r ∈ rsOf ls' := by
    obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (gls _).mpr ht⟩
  have hTout : TWNC Q58 ps' (rsOf ls') := TWNC.rebEnd r gT hr' hcellQ hreb hexW hEnd
  have htgout : Tagged Q58 ps' ls' := tagged_rebEndN gT.toN hexW gtg
  obtain ⟨fL, hf1, hf2⟩ := (ResU.CompS.assoc ρf ρ'L ρpL Q58).mp ⟨Y59, hLY, hFY⟩
  have hvfL : ResU.Valid fL := (ResU.Valid.split hf2 hvQ).1
  exact ⟨ρ'L, ρpL, fL, Q58, Y59, ps', ls',
    ⟨(ResU.CompS.comm hf1).1, fL, ResU.CompS.comm hf1, hvfL⟩, hf1,
    ⟨(ResU.CompS.comm hf2).1, Q58, ResU.CompS.comm hf2, hvQ⟩, hf2, hLQ, hLY,
    ⟨h59, hvρ, hvY59⟩, hnoL, hTout, htgout, gps, gls, hQout⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
