import Core.Chain.SI.IFrameN
import Core.Reborrow

/-!
# The `↺` rule (`[TR]` 6.150) at the step index

`rwp_reborrow`: `wpG_reborrow`'s proof, H1–H33, at `rwp`. The inner run starts at the world
`ρ_f ● ρ ● ρ_P̂(v′)`, whose memory is the outer one by 6.58's first conclusion (*"by rewriting in
H24 with lemma 6.58"*, read right to left), so the inner `rwp` speaks of the outer run at the
same index. At its end the printed proof runs unchanged, with 6.52 and 6.59 at the index
(`six52_keepN`, `six59N`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)

/-- `RebChooseTW` at `TWNC`: 6.150's reborrow, chosen at the tagged world.  Given the handed `χ₀ ∈ reb_β(ρ′)` with
`P̂₀(β)(w)(χ₀)` (H16/H17), a world `W` holding the cell `ℓ ↦ imm(s̄, w, ρ′)` with frame `F`,
and `β` below `W`: some `χ ∈ reb_β(ρ′)` with `P̂(β)(w)(χ)`, the two inputs `[TR]` 6.55 adds
(`ag(χ)` defined and `EscrowAgree` at `F` and at the cell), the world `W ● χ` typed (entry), and
every world `W″` with `W″ ● χ|dom(ρ′|mut,own)` typed, holding the cell and in `Res_β`, typed
(exit).  `[about ours: our chooser at the typed world]` -/
def RebChooseTWN (ls : List SRec) (l : Loc) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) : Prop :=
  ∀ (W F χ₀ σ : WRes) (ps : List FrameRec) (β : Life) (w : Val) (s : LSet)
    (hs : σ.InStratum s.join),
    TWNC W ps (rsOf ls) → Tagged W ps ls → W.InStratum β →
    ResU.CompS (ResU.single l (CellU.immOf s w σ hs)) F W → R w σ →
    ResU.Reb β σ χ₀ → P₀ β w χ₀ →
    ∃ χ, ResU.Reb β σ χ ∧ P β w χ ∧ (∃ A, AgW χ A) ∧
      (∀ a, AgW F a → EscrowAgree σ χ a) ∧
      (∀ a, AgW (ResU.single l (CellU.immOf s w σ hs)) a → EscrowAgree σ χ a) ∧
      (∀ W', ResU.CompS W χ W' → ResU.Valid W' → TWNC W' ps (rsOf ls) ∧ Tagged W' ps ls) ∧
      (∀ (ps' : List FrameRec) (ls' : List SRec) (Wp W'' : WRes),
        (∀ p, p ∈ ps' ↔ p ∈ ps) → (∀ x, x ∈ ls' ↔ x ∈ ls) →
        TWNC Wp ps' (rsOf ls') → Tagged Wp ps' ls' →
        (∃ (s' : LSet) (hs' : σ.InStratum s'.join), W''.get l = some (CellU.immOf s' w σ hs')) →
        ResU.CompS W'' (χ.restrictDom σ.exclPart) Wp → W''.InStratum β →
        TWNC W'' ps' (rsOf ls') ∧ Tagged W'' ps' ls')

/-- `ResU.six52_keep` at the step index. -/
theorem six52_keepN {Φ : LocFam} {n : Nat} {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : WRes}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : UpdVN Φ n ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∃ ψ, ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) ψ ∧
      ResU.CompS ψ (ρ.restrictDom ρ'i.exclPart) ρp ∧ ψ.InStratum α := by
  obtain ⟨ψ, hsub, hcomp⟩ :=
    ResU.sub_of_le (ResU.reb_restrictDom_exclPart_empty hreb)
      (six52_H1N hreb hce hcp hupd hse hs')
  exact ⟨ψ, hsub, hcomp,
    six52_sub_inStratumN hreb hce hcp hupd hse hs' ψ hsub.toSub⟩

/-- **`[TR]` Theorem 6.150 (`↺` rule) at the step index**:

    ℓ ↦ Imm α (R ∧ Иβ. ↺_β P̂₀) ⋆ (Иβ. ∀v. P̂(v) ─⋆ rwpₙ(e){[β]Q̂}) ⊧ rwpₙ(e){Q̂}

with the chooser `RebChooseTWN`, `RebChooseTW` at `TWNC`. -/
theorem rwp_reborrow {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (α : Life)
    (R : Val → WRes → Prop) (P₀ P : Life → BoCa.Val → WProp) (e : Expr) (Q : PostN) {n : Nat}
    (hesc : RebChooseTWN ls l R P₀ P) {ρ : WRes}
    (hH : (ptoImm l α (fun v σ => R v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ) ⋆
        (fresh fun b => all fun v => P b v ─⋆
          rwp (ℍ := ℍ) Φ (fun k ls' v' => box b (Q k ls' v')) n ls e)) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  obtain ⟨ρi, ρb, hc, hpi, hpb⟩ := hH
  intro ρf fρ ps μ hf hcf hT htg hl hfd jr μ' e' hj hrun
  -- H4 unfolded: `ρᵢ = ℓ ↦ imm(ᾱ, v′, ρ′)`, H7 and H8.
  obtain ⟨s, v', σ, hs, hρi, ⟨hRv, hP7⟩, hα⟩ := hpi
  subst hρi
  -- H9 and H10 — the two `И` bounds.
  obtain ⟨gi, hP9⟩ := hP7
  obtain ⟨gb, hP10⟩ := hpb
  -- H11, with `β` also below the world.
  obtain ⟨γW, hγW⟩ := ResU.exists_stratum fρ
  obtain ⟨β, hβi', hβb⟩ := exists_shorter (gi ⊓ γW) gb
  have hβi : β ⊏ gi := lt_of_lt_of_le hβi' inf_le_left
  have hβW : fρ.InStratum β := hγW.mono (le_of_lt (lt_of_lt_of_le hβi' inf_le_right))
  obtain ⟨⟨χ₀, hreb₀, hPχ₀⟩, h13⟩ := hP9 β hβi
  obtain ⟨hwand0, h15⟩ := hP10 β hβb
  have hwand := hwand0 v'
  -- H18: by 6.10 with H2, `✓ρ`, and therefore `ρᵢ # ρ_b`.
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  have h18 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρb := ⟨hc.1, ρ, hc, hvρ⟩
  have hbi : ResU.Hash ρb (ResU.single l (CellU.immOf s v' σ hs)) := ResU.hash_symm h18
  obtain ⟨ρbf, hbf, hbfi⟩ :=
    (hash_shift ρf ρb (ResU.single l (CellU.immOf s v' σ hs))).mp ⟨ρ, ResU.CompS.comm hc, hf⟩
  -- the world is `ρᵢ ● (ρ_f ● ρ_b)`
  have hWcell : ResU.CompS (ResU.single l (CellU.immOf s v' σ hs)) ρbf fρ := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' (ResU.CompS.comm hc) hcf
    rw [ResU.CompS.functional hab hbf] at hab'
    exact ResU.CompS.comm hab'
  -- choose the reborrow, now that the frame `ρ_b ● ρ_f` and the world are known.
  obtain ⟨χ, hreb, hPχ, ⟨A, hagχ⟩, hEF, hEI, hentry, hexit⟩ :=
    hesc fρ ρbf χ₀ σ ps β v' s hs hT htg hβW hWcell hRv hreb₀ hPχ₀
  -- *"By similar reasoning, we have `ρ_P̂(v′) # ρ_b ● ρ_f`."*
  have h19' : ResU.Hash ρbf χ := ResU.six55 hreb hEF hagχ hbfi
  -- H19, by 6.11 from the line above.
  have h19 : ResU.Hash ρb χ := (ResU.Hash.split hbf h19').2
  obtain ⟨ρbχ, hbχ⟩ := (ResU.compS_defined_iff ρb χ).mpr h19.1
  -- *"By lemma 6.55, `ρᵢ # ρ_P̂(v)`."*
  have hvi : ResU.Valid (ResU.single l (CellU.immOf s v' σ hs)) := (hash_valid hbi).2
  have h55self : ResU.Hash χ (ResU.single l (CellU.immOf s v' σ hs)) :=
    ResU.six55_self hreb hEI hagχ (ResU.hash_self_single_imm hvi)
  -- H20: *"therefore by lemma 6.15 with H2, `ρ_P̂(v′) # ρᵢ ● ρ_b ● ρ_f`."*
  have hiρbf : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρbf := ResU.hash_symm hbfi
  have h20 : ResU.Hash χ fρ := ResU.hash_of_pairwise h55self hiρbf (ResU.hash_symm h19') hWcell
  -- *"setting `ρ_f = ρᵢ ● ρ_f`, with the compatibility constraint from H20"*
  obtain ⟨ρF, hF, hFb⟩ := compS_reassoc' hbf hWcell
  have hFbχ : ResU.Hash ρF ρbχ := by
    obtain ⟨x, hx, hxh⟩ := (hash_shift ρF ρb χ).mpr ⟨fρ, hFb, ResU.hash_symm h20⟩
    rwa [ResU.CompS.functional hx hbχ] at hxh
  -- the world the inner run starts at: `ρ_f ● ρ ● χ`, typed by the chooser's entry
  obtain ⟨Win, hWin, hvWin⟩ := hFbχ.2
  have hfχ : ResU.CompS fρ χ Win := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hbχ hWin
    rwa [ResU.CompS.functional hab hFb] at hab'
  obtain ⟨hTin, htgin⟩ := hentry Win hfχ hvWin
  -- H21: by the definition of `─⋆`.
  have h21 : rwp (ℍ := ℍ) Φ (fun k ls' v' => box β (Q k ls' v')) n ls e ρbχ :=
    hwand χ ρbχ hPχ hbχ
  have g4 : ResU.CompS ρF ρbχ Win := hWin
  -- The source memory: `⟦ρᵢ ● ρ_f ● ρ_P̂(v′) ● ρ_b⟧` regrouped as 6.58's `ρ ● ρ_b ● ρᵢ`.
  obtain ⟨t1, ht1, ht1'⟩ := compS_reassoc hF g4
  obtain ⟨u1, hu1, hu1'⟩ := compS_reassoc' hbχ ht1
  rw [ResU.CompS.functional hu1 hbf] at hu1'
  obtain ⟨Y58, hY58⟩ :=
    (ResU.compS_defined_iff ρbf (ResU.single l (CellU.immOf s v' σ hs))).mpr hbfi.1
  -- *"By rewriting in H24 with lemma 6.58"* — the first conclusion.
  have h58L := ResU.six58_left hreb hEI hagχ (ResU.hash_symm h19')
    hbfi (ResU.CompS.comm hu1') (ResU.CompS.comm ht1') hY58
  -- `ρ_b ● ρ_f ● ρᵢ = ρ_f ● ρ`, which is the source H30 names.
  obtain ⟨ac, hac, hac'⟩ := compS_exch hbf hY58
  obtain ⟨t2, ht2, ht2'⟩ := compS_reassoc hac hac'
  rw [ResU.CompS.functional ht2 hc] at ht2'
  rw [ResU.CompS.functional ht2' hcf] at h58L
  -- the inner run's memory is the outer one
  have g5 : ResU.Lower Win μ := (h58L μ).mpr hl
  obtain ⟨hval, hprog⟩ := h21 ρF Win ps μ hFbχ hWin hTin htgin g5 hfd jr μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρQ, ρp, fρ', fρ'p, π, ps', ls', g1, g2, g3, g6, g7, g9, gA, gB,
    gT, gtg, gps, gls, gC⟩ := hval v hv
  -- H28 and H29, by unfolding `[β]` in H27.
  obtain ⟨h28, h29⟩ := gC
  -- *"Let `ρ⁺′ = ρ⁺ ⊟ ρ_P̂(v′)|dom(ρ′|mut,own)`"* — `[TR]` 6.52 at that `⊟`.
  obtain ⟨ψ, hsubK, hsplit, hψβ⟩ :=
    six52_keepN hreb (ResU.CompS.comm hbχ) g9 gA h15 h29
  -- 6.11 at the `#`s the inner `wp` produced.
  obtain ⟨hiQ, hfQ⟩ := ResU.Hash.split hF (ResU.hash_symm g1)
  obtain ⟨hFp, hQp⟩ := ResU.Hash.split g2 (ResU.hash_symm g3)
  obtain ⟨hip, hfp⟩ := ResU.Hash.split hF hFp
  obtain ⟨hψQ, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hQp)
  obtain ⟨hψi, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hip)
  have hvfp : ResU.Valid fρ'p := by obtain ⟨τ, hτ, -⟩ := g7; exact ⟨τ, hτ⟩
  -- The target memory: `⟦ρᵢ ● ρ_f ● ρ_Q ● ρ⁺⟧` regrouped as 6.58's `ρ′ ● ρ⁺ ● ρᵢ`.
  obtain ⟨t3, ht3, ht3'⟩ := compS_reassoc hF g2
  obtain ⟨u3, hu3, hu3'⟩ := compS_reassoc ht3' g6
  have hiu3 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) u3 :=
    ⟨hu3'.1, fρ'p, hu3', hvfp⟩
  have hvu3 : ResU.Valid u3 := (ResU.Valid.split hu3' hvfp).2
  have ht3p : ResU.Hash t3 ρp := ⟨hu3.1, u3, hu3, hvu3⟩
  obtain ⟨hψt3, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm ht3p)
  obtain ⟨ρ'χ, hρ'χ⟩ := (ResU.compS_defined_iff t3 ψ).mpr (ResU.hash_symm hψt3).1
  obtain ⟨ht3i, -⟩ := ResU.Hash.split hu3 (ResU.hash_symm hiu3)
  have hiρ'χ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρ'χ :=
    ResU.hash_of_pairwise (ResU.hash_symm ht3i) (ResU.hash_symm hψt3)
      (ResU.hash_symm hψi) hρ'χ
  obtain ⟨Q58, hQ58⟩ :=
    (ResU.compS_defined_iff ρ'χ (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiρ'χ).1
  -- *"…with lemma 6.58"* — the second conclusion.
  have h58R := ResU.six58_right hreb hEI hagχ (ResU.hash_symm hiu3)
    hu3 hsubK.toSub hsplit hρ'χ (ResU.CompS.comm hu3') hQ58
  have hLQ : ResU.Lower Q58 μ' := (h58R μ').mp g7
  -- `ρ′ ● ρ⁺′ ● ρᵢ = (ρ_f ● ρ_Q) ● (ρᵢ ● ρ⁺′)`, the shape the goal's row takes.
  obtain ⟨bc, hbc, hbc'⟩ := compS_exch hρ'χ hQ58
  obtain ⟨ρpG, hρpG, hρpG'⟩ := compS_reassoc hbc hbc'
  -- H33, by lemma 6.59.
  have hiπ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) π :=
    ResU.hash_of_pairwise hiQ hQp hip g9
  obtain ⟨w59, hw59⟩ := (ResU.compS_defined_iff ρQ ψ).mpr (ResU.hash_symm hψQ).1
  have hiw59 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) w59 :=
    ResU.hash_of_pairwise hiQ (ResU.hash_symm hψQ) (ResU.hash_symm hψi) hw59
  obtain ⟨Y59, hY59⟩ :=
    (ResU.compS_defined_iff w59 (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiw59).1
  have hvY59 : ResU.Valid Y59 := hash_valid_comp (ResU.hash_symm hiw59) hY59
  obtain ⟨σX, hσX⟩ := id hvρ
  obtain ⟨σY, hσY⟩ := id hvY59
  have h59 : UpdN Φ (n - jr) ρ Y59 :=
    six59N hreb (ResU.CompS.comm hbχ) g9 gA h15 h29 (ResU.hash_symm h18)
      (ResU.hash_symm hiπ) hsubK hc ⟨w59, hw59, hY59⟩ hσX hσY
  -- `ρ_Q ● ρᵢ ● ρ⁺′` is `ρ_Q ● (ρᵢ ● ρ⁺′)` — 6.59's `Y` at the goal's bracketing.
  obtain ⟨bc59, hbc59, hbc59'⟩ := compS_reassoc hw59 hY59
  rw [ResU.CompS.functional (ResU.CompS.comm hbc59) hρpG] at hbc59'
  -- The final world, typed by the chooser's exit: `W″ ● ρ_P̂(v′)|dom(ρ′|mut,own)` is the inner
  -- run's final world.
  have hexW : ResU.CompS Q58 (χ.restrictDom σ.exclPart) fρ'p := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hsplit hu3
    rw [ResU.CompS.functional hab hρ'χ] at hab'
    obtain ⟨ab', hab₂, hab₂'⟩ := compS_reassoc' hab' hu3'
    rwa [ResU.CompS.functional hab₂ (ResU.CompS.comm hQ58)] at hab₂'
  have hcellQ : ∃ (s' : LSet) (hs' : σ.InStratum s'.join),
      Q58.get l = some (CellU.immOf s' v' σ hs') := cell_of_compS_single (ResU.CompS.comm hQ58)
  have hQβ : Q58.InStratum β := by
    have hfβ : ρf.InStratum β := ResU.CompS.inStratum_left hcf hβW
    have hρβ : ρ.InStratum β := ResU.CompS.inStratum_right hcf hβW
    have hiβ : (ResU.single l (CellU.immOf s v' σ hs)).InStratum β :=
      ResU.CompS.inStratum_left hc hρβ
    exact ResU.CompS.inStratum hQ58
      (ResU.CompS.inStratum hρ'χ (ResU.CompS.inStratum ht3 hfβ h29) hψβ) hiβ
  obtain ⟨hTout, htgout⟩ := hexit ps' ls' fρ'p Q58 gps gls gT gtg hcellQ hexW hQβ
  -- G2–G7.
  refine ⟨ρQ, ρpG, t3, Q58, Y59, ps', ls', ResU.hash_symm hfQ, ht3, ?_,
    hρpG', hLQ, hbc59', ⟨h59, hvρ, hvY59⟩, ?_, hTout, htgout, gps, gls, h28⟩
  · exact ResU.hash_symm
      (ResU.hash_of_pairwise ht3i (ResU.hash_symm hψi) (ResU.hash_symm hψt3) hρpG)
  · exact noOwn_compS hρpG (noOwn_single_imm l s v' σ hs) (noOwn_subKeep hsubK gB)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
