import Core.Chain.SI.RebAcrossC
import Core.Chain.SI.CanonDeep

/-!
# `[TR]` 6.150 at a chain view, across stops, at a canonical image

`rwpG_rebG` and `erwp_reborrow` (`SI/RebStopC.lean`, `SI/RebAcrossC.lean`) at a chain view: the
cell `ℓ₀ ↦ imm(s, u₀, w₀)` is a view at a chain position of a record (`Chain r.R r.T r.v p₀ ℓ₀ S₀ u₀`),
reached by loading through reborrows; the image is `canonD r S₀ u₀ w₀ β`; entry `TWNC.rebDeep`,
exit `TWNC.rebEndDeep`. The changes from the root case are the cell, the image and the
agreement, which is `canonD_escrowAgree` (`SI/CanonDeep.lean`) where the root case has
`canon_escrowAgree`. `rebDeep`'s cell premise (`hβc`: the view is longer than `β`) is the place
`TW.rebDeep`'s `W ∈ Res_β` is read (`ti_rebDeepN`), and it holds at a re-entry, since the view is
the same cell.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeVar)

/-- `tagged_rebN` at a chain view. -/
theorem tagged_rebDeepN {W W' c : WRes} {ps rs : List FrameRec} {ls : List SRec} {r : FrameRec}
    {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes}
    {hs : w₀.InStratum s.join} {β : Life}
    (hW₀ : TWN W ps rs) (hr : r ∈ rs) (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀)
    (hle : W.get l₀ = some (CellU.immOf s u₀ w₀ hs))
    (hreb : ResU.Reb β w₀ c) (hβ : RebRecLe W ps w₀ β) (hW : ResU.CompS W c W')
    (htag : Tagged W ps ls) : Tagged W' ps ls := by
  have hTI := hW₀.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hW₀.valid
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  obtain ⟨-, -, hw₀own, -, -⟩ := hTI.1.1 r hr p₀ l₀ S₀ u₀ hch aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀own
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
  refine ⟨p, hp, hd, frameLife_reb_rec hW₀.valid hle hreb hW (fun ζ e => ?_)
    (hβ p hp y.2 hα) hα⟩
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
  · exact (hTI.2.2.2.1 p hpR r hr u (hw₀own _ u e)).elim
  · exact CellU.kind_immOf _ _ _ _
  · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hle (MutAt.top e (by simp)))).elim

/-- The canonical image of a chain view is an image at every `β` the escrow lies above. -/
theorem canonD_reb {r : FrameRec} {S₀ : VTy} {u₀ : Val} {w₀ : WRes} {β : Life}
    (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀)) (hRβ : w₀.InStratum β) :
    ResU.Reb β w₀ (canonD r S₀ u₀ w₀ β) := by
  obtain ⟨β₀, -, -, hreb, -⟩ := hS
  exact relabel_reb hRβ hreb

/-- The agreement `[TR]` 6.55 asks for at a chain view, at the frame and at the cell. -/
theorem canonD_agree_split {W F : WRes} {ps rs : List FrameRec} {r : FrameRec}
    (hT : TWNC W ps rs) (hr : r ∈ rs) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val}
    (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀)) (β : Life)
    (hW : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) F W) :
    (∀ a, AgW F a → EscrowAgree w₀ (canonD r S₀ u₀ w₀ β) a) ∧
      (∀ a, AgW (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) a →
        EscrowAgree w₀ (canonD r S₀ u₀ w₀ β) a) := by
  obtain ⟨-, e, aW, -, haW, -⟩ := hT.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  have hW_agree := canonD_escrowAgree hT hr hch₀ hle hS β
  have liftG : ∀ G, (G = F ∨ G = ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) →
      ∀ a, AgW G a → EscrowAgree w₀ (canonD r S₀ u₀ w₀ β) a := by
    rintro G hG a ha l v ψ ψf hown hψ hψf hk hkf
    have hlift : ∃ ψ', aW.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ'.wit = ψf.wit := by
      rcases hG with rfl | rfl
      · rw [AgW.functional ha h₂] at hψf; exact lift_view hc.comm hψf hkf
      · rw [AgW.functional ha h₁] at hψf; exact lift_view hc hψf hkf
    obtain ⟨ψ', e', k', w'⟩ := hlift
    exact w'.symm.trans (hW_agree aW haW l v ψ ψ' hown hψ e' hk k')
  exact ⟨liftG F (Or.inl rfl), liftG _ (Or.inr rfl)⟩

/-- **`[TR]` 6.150 at a chain view, at any final term, at a canonical image.** `hpost` is also
handed the validity of `w` and `Y`. -/
theorem rwpG_rebDeepGV {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar) (hx : ¬ VFree x S₀) {β : Life}
    {s : LSet} {hs : w₀.InStratum s.join} (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀))
    (hRβ : w₀.InStratum β) (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β))
    {ρb ρ : WRes} (hc : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) ρb ρ)
    (h15 : ρb.InStratum β) {ls : List SRec} (hr : r ∈ rsOf ls)
    {Qin Qout : PostG} {n : Nat} {e : Expr}
    (hpost : ∀ k, k ≤ n → ∀ ls'' t (ρ' : WRes), Qin k ls'' t ρ' → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
        ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
          ResU.SubKeep w ((canonD r S₀ u₀ w₀ β).restrictDom w₀.exclPart) ψ →
          ResU.CompS ψ ((canonD r S₀ u₀ w₀ β).restrictDom w₀.exclPart) w → ψ.InStratum β →
          ResU.CompS ρo ψ Yo →
          ResU.CompS Yo (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) Y → ResU.Valid w → ResU.Valid Y →
          ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls'' t ρ'L)
    (hA : ∀ Bχ, ResU.CompS ρb (canonD r S₀ u₀ w₀ β) Bχ → rwpG (ℍ := ℍ) Φ Qin n ls e Bχ) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd jr μ' e' hj hrun hfin
  set χ : WRes := canonD r S₀ u₀ w₀ β with hχdef
  set ρi : WRes := ResU.single l₀ (CellU.immOf s u₀ w₀ hs) with hρidef
  have hreb : ResU.Reb β w₀ χ := canonD_reb hS hRβ
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
  obtain ⟨hEF, hEI⟩ := canonD_agree_split hT hr hch₀ hS β hWcell
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
  -- entry: `TWNC.reb` at the canonical image, `RebRecLe` from the tags
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hWcell
  have hrebLe := rebRecLe_globalD hT hr hch₀ ⟨ρbf, hWcell⟩
    (le_of_lt (CellU.sqsupset_of_lsOf (CellU.lsOf_immOf _ _ _ _) hβc))
  have hcellLe : RebCellLe fρ l₀ β := fun a ha => by
    obtain ⟨a1, a2, h1, -, hcomp⟩ := (AgW.split hWcell).mp ha
    obtain ⟨ξ, t, eξ, ht, hy⟩ := (icp_trans (icpAt_agW h1 l₀ _ (ResU.single_get_self _ _))
      (icpAt_left hcomp l₀)).ls (CellU.lsOf_immOf _ _ _ _) (LSet.meet_mem _)
    exact ⟨ξ, t, _, eξ, ht, hy, CellU.sqsupset_of_lsOf (CellU.lsOf_immOf _ _ _ _) hβc⟩
  have hTin : TWNC Win ps (rsOf ls) :=
    TWNC.rebDeep r x hT hr hch₀ hle hx hreb hshape hcellLe hrebLe rfl hfχ hvWin
  have htgin : Tagged Win ps ls := tagged_rebDeepN hT.toN hr hch₀ hle hreb hrebLe hfχ htg
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
    hA ρbχ hbχ ρF Win ps μ hFbχ hWin hTin htgin hI g5 hfd jr μ' e' hj hrun hfin
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
  have hiu3 : ResU.Hash (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) u3 :=
    ⟨hu3'.1, fρ'p, hu3', hvfp⟩
  have hvu3 : ResU.Valid u3 := (ResU.Valid.split hu3' hvfp).2
  have ht3p : ResU.Hash t3 w := ⟨hu3.1, u3, hu3, hvu3⟩
  obtain ⟨hψt3, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm ht3p)
  obtain ⟨ρ'χ, hρ'χ⟩ := (ResU.compS_defined_iff t3 ψ).mpr (ResU.hash_symm hψt3).1
  obtain ⟨ht3i, -⟩ := ResU.Hash.split hu3 (ResU.hash_symm hiu3)
  have hiρ'χ : ResU.Hash (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) ρ'χ :=
    ResU.hash_of_pairwise (ResU.hash_symm ht3i) (ResU.hash_symm hψt3)
      (ResU.hash_symm hψi) hρ'χ
  obtain ⟨Q58, hQ58⟩ :=
    (ResU.compS_defined_iff ρ'χ (ResU.single l₀ (CellU.immOf s u₀ w₀ hs))).mpr
      (ResU.hash_symm hiρ'χ).1
  -- *"…with lemma 6.58"* — the second conclusion.
  have h58R := ResU.six58_right hreb hEI hagχ (ResU.hash_symm hiu3)
    hu3 hsubK.toSub hsplit hρ'χ (ResU.CompS.comm hu3') hQ58
  have hLQ : ResU.Lower Q58 μ' := (h58R μ').mp g7
  -- H33, by lemma 6.59.
  have hiπ : ResU.Hash (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) π :=
    ResU.hash_of_pairwise hiQ hQp hip hπ
  obtain ⟨w59, hw59⟩ := (ResU.compS_defined_iff ρo ψ).mpr (ResU.hash_symm hψQ).1
  have hiw59 : ResU.Hash (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) w59 :=
    ResU.hash_of_pairwise hiQ (ResU.hash_symm hψQ) (ResU.hash_symm hψi) hw59
  obtain ⟨Y59, hY59⟩ :=
    (ResU.compS_defined_iff w59 (ResU.single l₀ (CellU.immOf s u₀ w₀ hs))).mpr
      (ResU.hash_symm hiw59).1
  have hvY59 : ResU.Valid Y59 := hash_valid_comp (ResU.hash_symm hiw59) hY59
  obtain ⟨σX, hσX⟩ := id hvρ
  obtain ⟨σY, hσY⟩ := id hvY59
  have h59 : UpdN Φ (n - jr) ρ Y59 :=
    six59N hreb (ResU.CompS.comm hbχ) hπ gA h15 hoβ (ResU.hash_symm h18)
      (ResU.hash_symm hiπ) hsubK hc ⟨w59, hw59, hY59⟩ hσX hσY
  -- the caller's split of `ρₒ ● ψ ● ρᵢ`
  obtain ⟨ρ'L, ρpL, hLY, hnoL, hQout⟩ := hcont ρp w ψ w59 Y59 gB hw hsubK hsplit hψβ hw59 hY59
    (ResU.Valid.split hfρ'p hvfp).2 hvY59
  -- the final world is `ρ_f ● Y`
  obtain ⟨X1, hX1, hX1'⟩ := compS_reassoc ht3 hρ'χ
  have hFY : ResU.CompS ρf Y59 Q58 := by
    obtain ⟨X2, hX2, hX2'⟩ := compS_reassoc hX1' hQ58
    obtain rfl : w59 = X1 := ResU.CompS.functional hw59 hX1
    rwa [ResU.CompS.functional hX2 hY59] at hX2'
  have hvQ : ResU.Valid Q58 := by obtain ⟨τ, hτ, -⟩ := hLQ; exact ⟨τ, hτ⟩
  -- exit: `TWNC.rebEnd`, its premise from 6.59 and 6.48 (`rebEndRec_of_updImm`)
  have hexW : ResU.CompS Q58 (χ.restrictDom w₀.exclPart) fρ'p := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hsplit hu3
    rw [ResU.CompS.functional hab hρ'χ] at hab'
    obtain ⟨ab', hab₂, hab₂'⟩ := compS_reassoc' hab' hu3'
    rwa [ResU.CompS.functional hab₂ (ResU.CompS.comm hQ58)] at hab₂'
  obtain ⟨s'', hs'', hcellQ⟩ := cell_of_compS_single (ResU.CompS.comm hQ58)
  have hupdF : UpdVN Φ (n - jr) fρ Q58 :=
    updVN_frame hcf hFY hf ⟨hFY.1, Q58, hFY, hvQ⟩ ⟨h59, hvρ, hvY59⟩
  have hEnd₀ := rebEndRec_of_updImm hT.toN hvQ hupdF.1.1 w₀ β
  have hEnd : RebEndRec Q58 (rsOf ls') w₀ β := by
    intro r' hr' l₀ m S u hc hex a' ha' ψ' s₁ e₁ hs₁ y hy hyβ
    have hr'' : r' ∈ rsOf ls := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr'; exact mem_rsOf.mpr ⟨t, (gls _).mp ht⟩
    exact hEnd₀ r' hr'' l₀ m S u hc hex a' ha' ψ' s₁ e₁ hs₁ y hy hyβ
  have hr' : r ∈ rsOf ls' := by
    obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (gls _).mpr ht⟩
  have hTout : TWNC Q58 ps' (rsOf ls') := TWNC.rebEndDeep r gT hr' hch₀ hcellQ hreb hexW hEnd
  have htgout : Tagged Q58 ps' ls' := tagged_rebEndN gT.toN hexW gtg
  obtain ⟨fL, hf1, hf2⟩ := (ResU.CompS.assoc ρf ρ'L ρpL Q58).mp ⟨Y59, hLY, hFY⟩
  have hvfL : ResU.Valid fL := (ResU.Valid.split hf2 hvQ).1
  exact ⟨ρ'L, ρpL, fL, Q58, Y59, ps', ls',
    ⟨(ResU.CompS.comm hf1).1, fL, ResU.CompS.comm hf1, hvfL⟩, hf1,
    ⟨(ResU.CompS.comm hf2).1, Q58, ResU.CompS.comm hf2, hvQ⟩, hf2, hLQ, hLY,
    ⟨h59, hvρ, hvY59⟩, hnoL, hTout, htgout, gps, gls, hQout⟩

/-- `rwpG_rebDeepGV`, the validity it hands `hpost` not read. -/
theorem rwpG_rebDeepG {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar) (hx : ¬ VFree x S₀) {β : Life}
    {s : LSet} {hs : w₀.InStratum s.join} (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀))
    (hRβ : w₀.InStratum β) (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β))
    {ρb ρ : WRes} (hc : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) ρb ρ)
    (h15 : ρb.InStratum β) {ls : List SRec} (hr : r ∈ rsOf ls)
    {Qin Qout : PostG} {n : Nat} {e : Expr}
    (hpost : ∀ k, k ≤ n → ∀ ls'' t (ρ' : WRes), Qin k ls'' t ρ' → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ∃ ρo ρk, ResU.CompS ρo ρk ρ' ∧ ρo.InStratum β ∧
        ∀ (ρp w ψ Yo Y : WRes), NoOwn ρp → ResU.CompS ρk ρp w →
          ResU.SubKeep w ((canonD r S₀ u₀ w₀ β).restrictDom w₀.exclPart) ψ →
          ResU.CompS ψ ((canonD r S₀ u₀ w₀ β).restrictDom w₀.exclPart) w → ψ.InStratum β →
          ResU.CompS ρo ψ Yo →
          ResU.CompS Yo (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) Y →
          ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls'' t ρ'L)
    (hA : ∀ Bχ, ResU.CompS ρb (canonD r S₀ u₀ w₀ β) Bχ → rwpG (ℍ := ℍ) Φ Qin n ls e Bχ) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ :=
  rwpG_rebDeepGV r hch₀ x hx hS hRβ hβc hshape hc h15 hr
    (fun k hk ls'' t ρ' hQ hls => by
      obtain ⟨ρo, ρk, h1, h2, h3⟩ := hpost k hk ls'' t ρ' hQ hls
      exact ⟨ρo, ρk, h1, h2, fun ρp w ψ Yo Y a b c d e f g _ _ => h3 ρp w ψ Yo Y a b c d e f g⟩) hA

/-- **`[TR]` 6.150 at a chain view, at `erwp`, across stops**, at the canonical image
`canonD r S₀ u₀ w₀ β`. -/
theorem erwp_reborrowDeep {Φ : LocFam} (r : FrameRec) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} (x : LifeVar) (hx : ¬ VFree x S₀)
    {β : Life} {s : LSet} {hs : w₀.InStratum s.join} (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀))
    (hRβ : w₀.InStratum β) (hβc : (CellU.immOf s u₀ w₀ hs).InStratum β)
    (hshape : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ (canonD r S₀ u₀ w₀ β))
    {Tb : OpTabN} (hT : Tb.RebOK β) {Q : PostN} :
    ∀ n ls e (ρb ρ : WRes),
      ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) ρb ρ → ρb.InStratum β →
      r ∈ rsOf ls →
      (∀ Bχ, ResU.CompS ρb (canonD r S₀ u₀ w₀ β) Bχ →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (RebPost β Q) n ls e Bχ) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ hc hb hr hA
  set χ : WRes := canonD r S₀ u₀ w₀ β with hχdef
  set ρi : WRes := ResU.single l₀ (CellU.immOf s u₀ w₀ hs) with hρidef
  have hreb : ResU.Reb β w₀ χ := canonD_reb hS hRβ
  -- `χ = χ|imm ● χ|excl`, the first part `imm` cells only
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (w₀.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  rw [erwp_eq]
  refine rwpG_rebDeepG r hch₀ x hx hS hRβ hβc hshape hc hb hr ?_ (fun Bχ hBχ => by
    have h := hA Bχ hBχ
    rw [erwp_eq] at h
    exact h)
  intro k hk ls'' t ρ' hQin hls''
  rcases hQin with ⟨w, rfl, hbox⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.150's exit as printed
    obtain ⟨hQ, hρ'β⟩ := hbox
    refine ⟨ρ', PMap.empty, ResU.comp_empty_right _, hρ'β, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain rfl : w' = ρp := ResU.CompS.functional hkw (ResU.comp_empty_left _)
    obtain ⟨g, hg, hρ'g⟩ := compS_reassoc hYo hY
    exact ⟨ρ', g, hρ'g, noOwn_compS hg (noOwn_subKeep hsubK hnp) (noOwn_single_imm _ _ _ _ _),
      Or.inl ⟨w, rfl, hQ⟩⟩
  · -- a stop: the fold
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    refine ⟨ρa, ρk, hcak, hT.pa m i en hTe _ _ _ _ hPA, ?_⟩
    intro ρp w' ψ Yo Y hnp hkw hsubK hsplit hψβ hYo hY
    obtain ⟨Ks, hKs, haKs⟩ := compS_reassoc hYo hY
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, Ks, haKs, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    have he' : extF ls'' lsO Ks := by rw [hwc] at he; exact he
    have hσBβ : σB.InStratum β := hT.pb m i en hTe _ _ _ _ hB
    -- the lender's next segment: `ρᵢ ● (ψ ● σ_B)`
    obtain ⟨ρb', hψσ, hXB'⟩ := compS_reassoc (ResU.CompS.comm hKs) hXB
    have hb' : ρb'.InStratum β := inStratum_compS hψσ hψβ hσBβ
    -- the record is kept: the lender's share holds a view at one of its chain positions
    have hr' : r ∈ rsOf lsO := by
      obtain ⟨t', ht⟩ := mem_rsOf.mp hr
      exact he' r (mem_rsOf.mpr ⟨t', (hls'' _).mpr ht⟩)
        ⟨l₀, Frz.of_compS_right hKs (Frz.imm (ResU.single_get_self _ _) (by simp)),
          Or.inr ⟨p₀, S₀, u₀, hch₀⟩⟩
    refine ih k' (by omega) lsO _ ρb' XB hXB' hb' hr' (fun Bχ hBχ => ?_)
    -- the borrowed continuation at `ρₖ ● σ_B`, with the garbage `ρ⁺ ● χ|imm`
    obtain ⟨ψχ, hψχ, hψχσ⟩ := compS_exch hψσ hBχ
    obtain ⟨w₁, hw₁, hw₁χ⟩ := compS_reassoc' (ResU.CompS.comm hχsplit) hψχ
    obtain rfl : w₁ = w' := ResU.CompS.functional hw₁ hsplit
    obtain ⟨g, hg, hkg⟩ := compS_reassoc hkw hw₁χ
    obtain ⟨Xk, hXk, hXkg⟩ := compS_exch hkg hψχσ
    have hwc' : en.wc ls'' lsO ρk := by rw [hwc]; exact extF_reb hkw hsplit hreb hKs he'
    have hc := (hcont lsO hwc').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkg (noOwn_compS hg hnp hχimm) hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
