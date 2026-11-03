import Support.Model.Tree.Chain59
import Support.Model.Tree.Port.Six34to39
import Support.Model.Tree.Port.Six48

/-!
# `[TR]` Lemmas 6.34–6.57 at the chain

`[spec §62]`. The printed statements of `[TR]` Lemmas 6.34, 6.37–6.39, 6.46–6.52, 6.54 and
6.57 (`Paper/S6_2_NonStandardLemmas/Lemmas.lean`) are the chain instances of the tree's: every
printed resource is the image of one at `WCactus.chain` (`exists_map_ΦU`), every hypothesis is
read back along `ΦU` (`●`, `○`, `▶◀`, `#`, `✓`, `⦇−⦈`, `⦇−⦈_○`, `ag`, `Res_α`, `↭`, `reb_α`,
`⊟`, `ρ∣dom(−)`, `ρ∣ι`, `ρ/ℓ`, `ℓ ↦ ψ`), the tree lemma is applied at `WCactus.chain`, and its
conclusion is read out along `ΦU` the same way.
-/

noncomputable section

namespace BoCa.Fig16.Tree.ChainSix3
open BoCa.Fig16 BoCa.Fig16.Tree

variable {Loc Val : Type}

end BoCa.Fig16.Tree.ChainSix3

namespace BoCa.Fig16.Tree
open BoCa.Fig16 BoCa.Fig16.Tree.ChainSix3

variable {Loc Val : Type}

/-- **`[TR]` Lemma 6.34 at the chain**: the printed statement (`ResU.six34`), from
`ResUT.six34` at `WCactus.chain`. -/
theorem chain_ResU_six34 {l : Loc} {s : LSet} {v : Val} {ρ ρv W : ResU Loc Val}
    {hs : ρv.InStratum s.join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hh : ResU.Hash ρ W) :
    ResU.Hash ρ (ResU.single l (CellU.immOf s v ρv hs)) := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρv, rfl⟩ := exists_map_ΦU ρv
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [chain_single_own] at hW
  rw [chain_single_immOf]
  exact chain_hash_iff.mp (ResUT.six34 (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr hh))

/-- **`[TR]` Lemma 6.37 at the chain**: the printed statement (`ResU.six37`), from
`ResUT.six37` at `WCactus.chain`. -/
theorem chain_ResU_six37 {ρ ρ₁ ρ₂ r : ResU Loc Val} (h₁ : ResU.CompatS ρ ρ₁)
    (h₂ : ResU.CompatS ρ ρ₂) (h₁₂ : ResU.CompR ρ₁ ρ₂ r) : ResU.CompatS ρ r := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨r, rfl⟩ := exists_map_ΦU r
  exact chain_resCompatS_iff.mp (ResUT.six37 (chain_resCompatS_iff.mpr h₁)
    (chain_resCompatS_iff.mpr h₂) (chain_resCompR_iff.mpr h₁₂))

/-- **`[TR]` Lemma 6.38 at the chain**: the printed statement (`ResU.six38`, the proposition
`ResU.SixThirtyEight` written out), from `ResUT.six38` at `WCactus.chain`. -/
theorem chain_ResU_six38 :
    ∀ {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
      {ρ ρv ρ' ρp W ρρi ρ'ρp : ResU BoCa.Loc BoCa.Val}
      {hv : ρv.InStratum (LSet.singleton α).join},
      ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W →
      ResU.Hash ρ W →
      ResU.Hash ρ' ρp →
      ρ.InStratum α →
      ρ'.InStratum α →
      ρp.restrict Kind.own = PMap.empty →
      ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi →
      ResU.CompS ρ' ρp ρ'ρp →
      ResU.UpdV ρρi ρ'ρp →
      ∃ G, ResU.CompS ρ' (ρp.del l) G ∧ ResU.Hash G W := by
  intro α l v ρ ρv ρ' ρp W ρρi ρ'ρp hv hW hh hh' hs hs' hown hi hp hu
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρv, rfl⟩ := exists_map_ΦU ρv
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρp, rfl⟩ := exists_map_ΦU ρp
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  obtain ⟨ρρi, rfl⟩ := exists_map_ΦU ρρi
  obtain ⟨ρ'ρp, rfl⟩ := exists_map_ΦU ρ'ρp
  have hv' : ρv.InStratum (TSet.single α) := by
    rw [← TSet.ofLSet_toLSet (TSet.single α), TSet.toLSet_single]
    exact inStratum_ofLSet_iff.mpr hv
  have himm : CellU.immOf (LSet.singleton α) v (ρv.map ΦU) hv =
      ΦU (CellUT.immOf (TSet.single α) v ρv hv') :=
    (ΦU_immOf_eq (TSet.toLSet_single α) rfl).symm
  rw [chain_single_own] at hW
  rw [himm, ← chain_single] at hi
  rw [← chain_restrict, ← chain_empty] at hown
  obtain ⟨G, hG, hGW⟩ := ResUT.six38 (K := WCactus.chain) (hv := hv')
    (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr hh) (chain_hash_iff.mpr hh')
    (chain_inStratum_iff.mpr hs) (chain_inStratum_iff.mpr hs') (ΦU_map_injective hown)
    (chain_resCompS_iff.mpr hi) (chain_resCompS_iff.mpr hp) (chain_updV_iff.mpr hu)
  refine ⟨G.map ΦU, ?_, chain_hash_iff.mp hGW⟩
  rw [← chain_del]
  exact chain_resCompS_iff.mp hG

/-- **`[TR]` Lemma 6.39 at the chain**: the printed statement (`ResU.six39`), from
`ResUT.six39` at `WCactus.chain`. -/
theorem chain_ResU_six39 {l : Loc} {s : LSet} {v : Val}
    {ρ ρ' ρv ov iw iw' : ResU Loc Val} {hstr : ρv.InStratum s.join}
    (hov : ResU.CompS (ResU.single l (CellU.ownOf v)) ρv ov)
    (h1 : ResU.Hash ρ ov) (h2 : ResU.Hash ρ' ov)
    (hi : ResU.CompS ρ (ResU.single l (CellU.immOf s v ρv hstr)) iw)
    (hi' : ResU.CompS ρ' (ResU.single l (CellU.immOf s v ρv hstr)) iw')
    (h3 : ResU.UpdV iw iw') :
    ∃ w w', ResU.CompS ρ ov w ∧ ResU.CompS ρ' ov w' ∧ ResU.UpdV w w' := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρv, rfl⟩ := exists_map_ΦU ρv
  obtain ⟨ov, rfl⟩ := exists_map_ΦU ov
  obtain ⟨iw, rfl⟩ := exists_map_ΦU iw
  obtain ⟨iw', rfl⟩ := exists_map_ΦU iw'
  rw [chain_single_own] at hov
  rw [chain_single_immOf] at hi hi'
  obtain ⟨w, w', hw, hw', hu⟩ := ResUT.six39 (chain_resCompS_iff.mpr hov)
    (chain_hash_iff.mpr h1) (chain_hash_iff.mpr h2) (chain_resCompS_iff.mpr hi)
    (chain_resCompS_iff.mpr hi') (chain_updV_iff.mpr h3)
  exact ⟨w.map ΦU, w'.map ΦU, chain_resCompS_iff.mp hw, chain_resCompS_iff.mp hw',
    chain_updV_iff.mp hu⟩

/-- **`[TR]` Lemma 6.46 at the chain**: the printed statement (`BoLo.hash_shift`), from
`Tree.BoLo.hash_shift` at `WCactus.chain`. -/
theorem chain_BoLo_hash_shift (ρ₁ ρ₂ ρ₃ : BoCa.Fig16.BoLo.WRes) :
    (∃ x, ResU.CompS ρ₂ ρ₃ x ∧ ResU.Hash ρ₁ x) ↔
    (∃ y, ResU.CompS ρ₁ ρ₂ y ∧ ResU.Hash y ρ₃) := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  have e := BoLo.hash_shift (K := WCactus.chain) ρ₁ ρ₂ ρ₃
  constructor
  · rintro ⟨x, hx, hh⟩
    obtain ⟨x, rfl⟩ := exists_map_ΦU x
    obtain ⟨y, hy, hh'⟩ := e.mp ⟨x, chain_resCompS_iff.mpr hx, chain_hash_iff.mpr hh⟩
    exact ⟨y.map ΦU, chain_resCompS_iff.mp hy, chain_hash_iff.mp hh'⟩
  · rintro ⟨y, hy, hh⟩
    obtain ⟨y, rfl⟩ := exists_map_ΦU y
    obtain ⟨x, hx, hh'⟩ := e.mpr ⟨y, chain_resCompS_iff.mpr hy, chain_hash_iff.mpr hh⟩
    exact ⟨x.map ΦU, chain_resCompS_iff.mp hx, chain_hash_iff.mp hh'⟩

/-- **`[TR]` Lemma 6.47 at the chain**: the printed statement (`ResU.Upd.refl`), from
`ResUT.Upd.refl` at `WCactus.chain`. -/
theorem chain_ResU_Upd_refl (ρ : ResU Loc Val) : ρ.Upd ρ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  exact chain_upd_iff.mp (ResUT.Upd.refl ρ)

/-- **`[TR]` Lemma 6.47 at the chain**: the printed statement (`ResU.UpdV.refl`), from
`ResUT.UpdV.refl` at `WCactus.chain`. -/
theorem chain_ResU_UpdV_refl {ρ : ResU Loc Val} (h : ρ.Valid) : ρ.UpdV ρ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  exact chain_updV_iff.mp (ResUT.UpdV.refl (chain_valid_iff.mpr h))

/-- **`[TR]` Lemma 6.48 at the chain**: the printed statement (`BoLo.updV_frame`), from
`Tree.BoLo.updV_frame` at `WCactus.chain`. -/
theorem chain_BoLo_updV_frame {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : BoCa.Fig16.BoLo.WRes}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₂ : ResU.Hash ρ₁ ρ₂) (hh₃ : ResU.Hash ρ₁ ρ₃)
    (h : ResU.UpdV ρ₂ ρ₃) : ResU.UpdV ρ₁₂ ρ₁₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨ρ₁₃, rfl⟩ := exists_map_ΦU ρ₁₃
  exact chain_updV_iff.mp (BoLo.updV_frame (chain_resCompS_iff.mpr h₁₂)
    (chain_resCompS_iff.mpr h₁₃) (chain_hash_iff.mpr hh₂) (chain_hash_iff.mpr hh₃)
    (chain_updV_iff.mpr h))

/-- **`[TR]` Lemma 6.49 at the chain**: the printed statement (`ResU.UpdV.trans`), from
`ResUT.UpdV.trans` at `WCactus.chain`. -/
theorem chain_ResU_UpdV_trans {ρ₁ ρ₂ ρ₃ : ResU Loc Val} (h₁ : ρ₁.UpdV ρ₂)
    (h₂ : ρ₂.UpdV ρ₃) : ρ₁.UpdV ρ₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  exact chain_updV_iff.mp (ResUT.UpdV.trans (chain_updV_iff.mpr h₁) (chain_updV_iff.mpr h₂))

/-- **`[TR]` Lemma 6.49 at the chain**: the printed statement (`ResU.Upd.trans`), from
`ResUT.Upd.trans` at `WCactus.chain`. -/
theorem chain_ResU_Upd_trans {ρ₁ ρ₂ ρ₃ : ResU Loc Val} (h₁ : ρ₁.Upd ρ₂) (h₂ : ρ₂.Upd ρ₃) :
    ρ₁.Upd ρ₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  exact chain_upd_iff.mp (ResUT.Upd.trans (chain_upd_iff.mpr h₁) (chain_upd_iff.mpr h₂))

/-- **`[TR]` Lemma 6.50 at the chain**: the printed statement (`BoLo.updV_outlives`), from
`Tree.BoLo.updV_outlives` at `WCactus.chain`, at the stratum `{α}`. -/
theorem chain_BoLo_updV_outlives {ρ ρ' : BoCa.Fig16.BoLo.WRes} {α : Life}
    (h : BoCa.Fig16.BoLo.Outlives ρ α)
    (hu : ResU.UpdV ρ ρ') : BoCa.Fig16.BoLo.Outlives ρ' α := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  exact chain_inStratum_iff.mp
    (BoLo.updV_outlives (chain_inStratum_iff.mpr h) (chain_updV_iff.mpr hu))

/-- **`[TR]` Lemma 6.51 at the chain**: the printed statement (`ResU.six51`), from
`ResUT.six51` at `WCactus.chain`. -/
theorem chain_ResU_six51 {ρ ρ' ρ₁₂ σ σ' σ₁₂ : ResU BoCa.Loc BoCa.Val}
    (hc : ResU.CompS ρ ρ' ρ₁₂) (hσ : ResU.Flat ρ σ) (hσ' : ResU.Flat ρ' σ')
    (hσ₁₂ : ResU.Flat ρ₁₂ σ₁₂)
    {l : BoCa.Loc} {a b : LSet} {v : BoCa.Val} {χ : ResU BoCa.Loc BoCa.Val}
    {ha : χ.InStratum a.join} {hb : χ.InStratum b.join}
    (hg : σ.get l = some (CellU.immOf a v χ ha))
    (hg' : σ'.get l = some (CellU.immOf b v χ hb)) :
    ∃ h : χ.InStratum (a ∪ b).join,
      σ₁₂.get l = some (CellU.immOf (a ∪ b) v χ h) := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  obtain ⟨σ', rfl⟩ := exists_map_ΦU σ'
  obtain ⟨σ₁₂, rfl⟩ := exists_map_ΦU σ₁₂
  obtain ⟨χ, rfl⟩ := exists_map_ΦU χ
  rw [← ΦU_immOf_eq (s := TSet.ofLSet a) (h := inStratum_ofLSet_iff.mpr ha)
    (TSet.toLSet_ofLSet a) rfl, map_ΦU_get] at hg
  rw [← ΦU_immOf_eq (s := TSet.ofLSet b) (h := inStratum_ofLSet_iff.mpr hb)
    (TSet.toLSet_ofLSet b) rfl, map_ΦU_get] at hg'
  obtain ⟨h, e⟩ := ResUT.six51 (chain_resCompS_iff.mpr hc) (chain_flat_iff.mpr hσ)
    (chain_flat_iff.mpr hσ') (chain_flat_iff.mpr hσ₁₂) hg hg'
  have hL : (TSet.ofLSet a ∪ TSet.ofLSet b).toLSet = a ∪ b := by
    rw [TSet.toLSet_union, TSet.toLSet_ofLSet, TSet.toLSet_ofLSet]
  have h' : ResU.InStratum (a ∪ b).join (χ.map ΦU) := hL ▸ ΦU_map_inStratum h
  refine ⟨h', ?_⟩
  rw [← ΦU_immOf_eq (h := h) hL rfl, map_ΦU_get]
  exact e

/-- **`[TR]` Lemma 6.52 at the chain**: the printed statement (`ResU.six52`), from
`ResUT.six52` at `WCactus.chain`; the tree's `↓α` hypothesis `hD` is the printed `↓α`
(`WCactus.chain_downOf`). -/
theorem chain_ResU_six52 {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : ResU.UpdV ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∃ ψ, ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) ψ ∧
      ResU.CompS ψ (ρ.restrictDom ρ'i.exclPart) ρp ∧ ψ.InStratum α := by
  obtain ⟨ρ'i, rfl⟩ := exists_map_ΦU ρ'i
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρe, rfl⟩ := exists_map_ΦU ρe
  obtain ⟨ρ'', rfl⟩ := exists_map_ΦU ρ''
  obtain ⟨ρp, rfl⟩ := exists_map_ΦU ρp
  obtain ⟨ρρe, rfl⟩ := exists_map_ΦU ρρe
  obtain ⟨ρ'p, rfl⟩ := exists_map_ΦU ρ'p
  obtain ⟨ψ, hsub, hc, hs⟩ := ResUT.six52 (WCactus.chain_downOf α) (chain_reb_iff.mpr hreb)
    (chain_resCompS_iff.mpr hce) (chain_resCompS_iff.mpr hcp) (chain_updV_iff.mpr hupd)
    (chain_inStratum_iff.mpr hse) (chain_inStratum_iff.mpr hs')
  refine ⟨ψ.map ΦU, ?_, ?_, chain_inStratum_iff.mp hs⟩
  · rw [← chain_exclPart, ← chain_restrictDom]; exact chain_sub_iff.mp hsub
  · rw [← chain_exclPart, ← chain_restrictDom]; exact chain_resCompS_iff.mp hc

/-- **`[TR]` Lemma 6.54 at the chain**: the printed statement (`ResU.six54`), from
`ResUT.six54` at `WCactus.chain`. -/
theorem chain_ResU_six54 {β : Life} {ρ' ρ A : ResU Loc Val} {l₀ : Loc} {s : LSet} {v : Val}
    {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hval : ResU.Valid (ResU.single l₀ (CellU.immOf s v ρ' hs)))
    (hagρ : AgW ρ A) :
    ∃ f, ResU.FlatR ρ' f ∧ ∀ l ψ, A.get l = some ψ → ∃ φ, f.get l = some φ := by
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  rw [chain_single_immOf] at hval
  obtain ⟨f, hf, hA⟩ := ResUT.six54 (chain_reb_iff.mpr hreb) (chain_valid_iff.mpr hval)
    (chain_agW_iff.mpr hagρ)
  refine ⟨f.map ΦU, chain_flatR_iff.mp hf, fun l ψ e => ?_⟩
  obtain ⟨φ, hφ⟩ := hA l _ (map_ΦU_get_some.mp e)
  exact ⟨ΦU φ, map_ΦU_get.mpr hφ⟩

/-- **`[TR]` Lemma 6.57 at the chain**: the printed statement (`ResU.six57`), from
`ResUT.six57` at `WCactus.chain`. -/
theorem chain_ResU_six57 {β : Life} {ρ'i ρ A X σ : ResU Loc Val} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hagρ : AgW ρ A)
    (hX : ResU.CompS (ρ.restrictDom (ρ'i.restrict Kind.imm))
        (ResU.single l₀ (CellU.immOf s v ρ'i hs)) X) :
    ResU.Flat X σ ↔ ResU.Flat (ResU.single l₀ (CellU.immOf s v ρ'i hs)) σ := by
  obtain ⟨ρ'i, rfl⟩ := exists_map_ΦU ρ'i
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  obtain ⟨X, rfl⟩ := exists_map_ΦU X
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  rw [chain_single_immOf] at hX ⊢
  rw [← chain_restrict, ← chain_restrictDom] at hX
  rw [← chain_flat_iff, ← chain_flat_iff]
  exact ResUT.six57 (chain_reb_iff.mpr hreb) (chain_agW_iff.mpr hagρ)
    (chain_resCompS_iff.mpr hX)

end BoCa.Fig16.Tree

end
