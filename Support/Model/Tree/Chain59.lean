import Support.Model.Tree.Port.Six53to59
import Support.Model.Tree.ChainRebSub

/-!
# `[TR]` Lemma 6.59 at the chain

`[spec §62]`. The printed statement of 6.59 (`Paper/S6_2_NonStandardLemmas/Lemmas.lean`,
`ResU.six59`) is the chain instance of the tree's (`ResUT.six59`): every resource is the image
of one at `WCactus.chain` (`exists_map_ΦU`), every hypothesis is read back along `ΦU` (`●`, `#`,
`⦇−⦈`, `Res_β`, `↭`, `reb_β`, `⊟`, `ρ∣dom(−)`, `ρ∣own,mut`), the tree's `↓β` hypothesis is the
printed `↓β` (`WCactus.chain_downOf`), and the tree's `↭` is the printed one
(`chain_upd_iff`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- `ℓ ↦ imm(ᾱ, v, ρ)` read back along `ΦU`. -/
theorem chain_single_immOf {Loc Val : Type} (l : Loc) (s : LSet) (v : Val)
    (τ : ResUT Loc Val WCactus.chain) (hs : ResU.InStratum s.join (τ.map ΦU)) :
    ResU.single l (CellU.immOf s v (τ.map ΦU) hs) =
      (ResUT.single l (CellUT.immOf (TSet.ofLSet s) v τ (inStratum_ofLSet_iff.mpr hs))).map ΦU := by
  rw [chain_single, ΦU_immOf_eq (TSet.toLSet_ofLSet s) rfl]

/-- **`[TR]` Lemma 6.59 at the chain**: the printed statement (`ResU.six59`), obtained from
`ResUT.six59` at `WCactus.chain` with `↓β` the printed one. -/
theorem chain_six59
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    ResU.Upd Xi Y := by
  obtain ⟨ρ'i, rfl⟩ := exists_map_ΦU ρ'i
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρb, rfl⟩ := exists_map_ΦU ρb
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρp, rfl⟩ := exists_map_ΦU ρp
  obtain ⟨χ, rfl⟩ := exists_map_ΦU χ
  obtain ⟨ρρb, rfl⟩ := exists_map_ΦU ρρb
  obtain ⟨ρ'p, rfl⟩ := exists_map_ΦU ρ'p
  obtain ⟨Xi, rfl⟩ := exists_map_ΦU Xi
  obtain ⟨Y, rfl⟩ := exists_map_ΦU Y
  obtain ⟨σX, rfl⟩ := exists_map_ΦU σX
  obtain ⟨σY, rfl⟩ := exists_map_ΦU σY
  obtain ⟨w, hw₁, hw₂⟩ := hYc
  obtain ⟨w, rfl⟩ := exists_map_ΦU w
  rw [chain_single_immOf] at hh1 hh2 hXc hw₂
  rw [← chain_exclPart, ← chain_restrictDom] at hsub
  exact chain_upd_iff.mp (ResUT.six59 (WCactus.chain_downOf β) (chain_reb_iff.mpr hreb)
    (chain_resCompS_iff.mpr hce) (chain_resCompS_iff.mpr hcp) (chain_updV_iff.mpr hupd)
    (chain_inStratum_iff.mpr hsb) (chain_inStratum_iff.mpr hs') (chain_hash_iff.mpr hh1)
    (chain_hash_iff.mpr hh2) (chain_subKeep_iff.mpr hsub) (chain_resCompS_iff.mpr hXc)
    ⟨w, chain_resCompS_iff.mpr hw₁, chain_resCompS_iff.mpr hw₂⟩ (chain_flat_iff.mpr hfX)
    (chain_flat_iff.mpr hfY))

end BoCa.Fig16.Tree

end
