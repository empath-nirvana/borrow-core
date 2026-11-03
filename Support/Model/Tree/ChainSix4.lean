import Support.Model.Tree.ChainSix1
import Support.Model.Tree.Chain59

/-!
# `[TR]` Lemmas 6.53, 6.55, 6.56 and 6.58 at the chain

`[spec §62]`. The printed statements of 6.53, 6.55, 6.56 and 6.58 (`Paper/S6_2_NonStandardLemmas/
Lemmas.lean`) as chain instances of the tree's (`Tree/Port/Six53to59.lean`). Each carries the
hypothesis `EscrowAgree` that `[TR]` p. 18 asserts; it reads a cell's tag and witness, which
`ΦU` keeps (`chain_escrowAgree_iff`). The printed `EscrowAgree` is stated here by its body
(`escrowU`), so that this file reads no printed lemma file.
-/

noncomputable section

namespace BoCa.Fig16.Tree.ChainSix4
open BoCa.Fig16 BoCa.Fig16.Tree

variable {Loc Val : Type}

/-- The body of the printed `EscrowAgree`. -/
def escrowU (χ ρ σ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (v : Val) (ψ ψf : CellU Loc Val),
    χ.get l = some (CellU.ownOf v) → ρ.get l = some ψ → σ.get l = some ψf →
      ψ.kind ≠ Kind.own → ψf.kind ≠ Kind.own → ψf.wit = ψ.wit

theorem chain_escrowAgree_iff {χ ρ σ : ResUT Loc Val WCactus.chain} :
    Tree.EscrowAgree χ ρ σ ↔ escrowU (χ.map ΦU) (ρ.map ΦU) (σ.map ΦU) := by
  constructor
  · intro H l v ψ ψf e₁ e₂ e₃ k₁ k₂
    rw [← ΦU_ΨU (CellU.ownOf v)] at e₁
    rw [map_ΦU_get] at e₁
    rw [map_ΦU_get_some] at e₂ e₃
    have := H l v _ _ e₁ e₂ e₃ (by rwa [ΨU_kind]) (by rwa [ΨU_kind])
    rw [ΨU_wit, ΨU_wit] at this
    have h := congrArg (PMap.map ΦU) this
    rwa [map_ΦU_ΨU, map_ΦU_ΨU] at h
  · intro H l v ψ ψf e₁ e₂ e₃ k₁ k₂
    have := H l v _ _ (by rw [← ΦU_ownOf]; exact map_ΦU_get.mpr e₁) (map_ΦU_get.mpr e₂)
      (map_ΦU_get.mpr e₃) (by rwa [ΦU_kind]) (by rwa [ΦU_kind])
    rw [ΦU_wit, ΦU_wit] at this
    exact ΦU_map_injective this

/-- The escrow hypothesis read back along `ΦU`. -/
theorem escrow_back {ρ' ρ ρf : ResUT Loc Val WCactus.chain}
    (h : ∀ a, AgW (ρf.map ΦU) a → escrowU (ρ'.map ΦU) (ρ.map ΦU) a) :
    ∀ a, AgWT ρf a → Tree.EscrowAgree ρ' ρ a :=
  fun a ha => chain_escrowAgree_iff.mpr (h _ (chain_agW_iff.mp ha))

end BoCa.Fig16.Tree.ChainSix4

namespace BoCa.Fig16.Tree
open BoCa.Fig16 ChainSix4

variable {Loc Val : Type}

/-- `[TR]` Lemma 6.53 at the chain: the printed statement (`ResU.six53`), from `ResUT.six53` at
`WCactus.chain`. -/
theorem chain_ResU_six53 {β : Life} {ρ' ρ ρf : ResU Loc Val} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hag : ∀ a, AgW ρf a → escrowU ρ' ρ a)
    (hhash : ResU.Hash ρf (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.CompatS ρf ρ := by
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρf, rfl⟩ := exists_map_ΦU ρf
  rw [chain_single_immOf] at hhash
  exact chain_resCompatS_iff.mp (ResUT.six53 (chain_reb_iff.mpr hreb) (escrow_back hag)
    (chain_hash_iff.mpr hhash))

/-- `[TR]` Lemma 6.55 at the chain: the printed statement (`ResU.six55`), from `ResUT.six55` at
`WCactus.chain`. -/
theorem chain_ResU_six55 {β : Life} {ρ' ρ ρf A : ResU Loc Val} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'.InStratum s.join}
    (hreb : ResU.Reb β ρ' ρ)
    (hesc : ∀ a, AgW ρf a → escrowU ρ' ρ a)
    (hagρ : AgW ρ A)
    (hhash : ResU.Hash ρf (ResU.single l₀ (CellU.immOf s v ρ' hs))) :
    ResU.Hash ρf ρ := by
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρf, rfl⟩ := exists_map_ΦU ρf
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  rw [chain_single_immOf] at hhash
  exact chain_hash_iff.mp (ResUT.six55 (chain_reb_iff.mpr hreb) (escrow_back hesc)
    (chain_agW_iff.mpr hagρ) (chain_hash_iff.mpr hhash))

/-- `[TR]` Lemma 6.56 at the chain: the printed statement (`ResU.six56`), from `ResUT.six56` at
`WCactus.chain`. -/
theorem chain_ResU_six56 {β : Life} {ρ' ρ A X : ResU Loc Val} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρ'.InStratum s.join} {w : Loc → Option Val}
    (hreb : ResU.Reb β ρ' ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ' hs)) a → escrowU ρ' ρ a)
    (hagρ : AgW ρ A)
    (hval : ResU.Valid (ResU.single l₀ (CellU.immOf s v ρ' hs)))
    (hX : ResU.CompS (ρ.restrictDom (ρ'.exclPart))
        (ResU.single l₀ (CellU.immOf s v ρ' hs)) X) :
    ResU.Lower X w ↔
      ResU.Lower (ResU.single l₀ (CellU.immOf s v ρ' hs)) w := by
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  obtain ⟨X, rfl⟩ := exists_map_ΦU X
  rw [chain_single_immOf] at hesc hval hX ⊢
  rw [← chain_exclPart, ← chain_restrictDom] at hX
  rw [← chain_lower_iff, ← chain_lower_iff]
  exact ResUT.six56 (chain_reb_iff.mpr hreb) (escrow_back hesc) (chain_agW_iff.mpr hagρ)
    (chain_valid_iff.mpr hval) (chain_resCompS_iff.mpr hX)

/-- `[TR]` Lemma 6.58, left conclusion, at the chain: the printed statement
(`ResU.six58_left`), from `ResUT.six58_left` at `WCactus.chain`. -/
theorem chain_ResU_six58_left {β : Life} {ρ'i ρ ρb A ρρb X Y : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a →
      escrowU ρ'i ρ a)
    (hagρ : AgW ρ A)
    (hρb : ResU.Hash ρ ρb)
    (hbi : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hrb : ResU.CompS ρ ρb ρρb)
    (hX : ResU.CompS ρρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) X)
    (hY : ResU.CompS ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) :
    ∀ w, ResU.Lower X w ↔ ResU.Lower Y w := by
  obtain ⟨ρ'i, rfl⟩ := exists_map_ΦU ρ'i
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρb, rfl⟩ := exists_map_ΦU ρb
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  obtain ⟨ρρb, rfl⟩ := exists_map_ΦU ρρb
  obtain ⟨X, rfl⟩ := exists_map_ΦU X
  obtain ⟨Y, rfl⟩ := exists_map_ΦU Y
  rw [chain_single_immOf] at hesc hbi hX hY
  intro w
  rw [← chain_lower_iff, ← chain_lower_iff]
  exact ResUT.six58_left (chain_reb_iff.mpr hreb) (escrow_back hesc) (chain_agW_iff.mpr hagρ)
    (chain_hash_iff.mpr hρb) (chain_hash_iff.mpr hbi) (chain_resCompS_iff.mpr hrb)
    (chain_resCompS_iff.mpr hX) (chain_resCompS_iff.mpr hY) w

/-- `[TR]` Lemma 6.58, right conclusion, at the chain: the printed statement
(`ResU.six58_right`), from `ResUT.six58_right` at `WCactus.chain`. -/
theorem chain_ResU_six58_right {β : Life} {ρ'i ρ ρ'' ρp χ A ρ'p ρ'χ P Q : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hesc : ∀ a, AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a →
      escrowU ρ'i ρ a)
    (hagρ : AgW ρ A)
    (hpi : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (_hsub : ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hcχ : ResU.CompS ρ'' χ ρ'χ)
    (hP : ResU.CompS ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) P)
    (hQ : ResU.CompS ρ'χ (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Q) :
    ∀ w, ResU.Lower P w ↔ ResU.Lower Q w := by
  obtain ⟨ρ'i, rfl⟩ := exists_map_ΦU ρ'i
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ'', rfl⟩ := exists_map_ΦU ρ''
  obtain ⟨ρp, rfl⟩ := exists_map_ΦU ρp
  obtain ⟨χ, rfl⟩ := exists_map_ΦU χ
  obtain ⟨A, rfl⟩ := exists_map_ΦU A
  obtain ⟨ρ'p, rfl⟩ := exists_map_ΦU ρ'p
  obtain ⟨ρ'χ, rfl⟩ := exists_map_ΦU ρ'χ
  obtain ⟨P, rfl⟩ := exists_map_ΦU P
  obtain ⟨Q, rfl⟩ := exists_map_ΦU Q
  rw [chain_single_immOf] at hesc hpi hP hQ
  rw [← chain_exclPart, ← chain_restrictDom] at _hsub hsplit
  intro w
  rw [← chain_lower_iff, ← chain_lower_iff]
  exact ResUT.six58_right (chain_reb_iff.mpr hreb) (escrow_back hesc) (chain_agW_iff.mpr hagρ)
    (chain_hash_iff.mpr hpi) (chain_resCompS_iff.mpr hcp) (chain_sub_iff.mpr _hsub)
    (chain_resCompS_iff.mpr hsplit) (chain_resCompS_iff.mpr hcχ) (chain_resCompS_iff.mpr hP)
    (chain_resCompS_iff.mpr hQ) w

end BoCa.Fig16.Tree

end
