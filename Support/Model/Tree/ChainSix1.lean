import Support.Model.Tree.Port.Split
import Support.Model.Tree.ChainRes

/-!
# `[TR]` §6.1 at the chain

`[spec §62]`. The printed statements of Lemmas 6.1–6.15, 6.30, 6.31, 6.35 and 6.36
(`Paper/S6_1_StandardLemmas/Lemmas.lean`) are the chain instances of the tree's
(`Tree/CarrierRes.lean`, `Tree/Port/Base.lean`, `Tree/Port/Split.lean`): every resource is the
image of one at `WCactus.chain` (`exists_map_ΦU`), and every hypothesis and conclusion is read
along `ΦU` (`▸◁`, `◐`, `●`, `○`, `✓`, `#`, `⟦−⟧`, `ρ∣imm`, `ex(ρ)`, `ρ∣imm = ∅`).

The lemmas generic in the cell relations `R`, `C` over `CellU` instantiate the tree lemma at
`R (ΦU −) (ΦU −)` and `C (ΦU −) (ΦU −) (ΦU −)`, and read `◐` and `ex(−)` back with
`chain_comp_iff`, `chain_compat_iff` and `chain_exW_iff` at `Iff.rfl` correspondences.

The memory union `m₁ ∪ m₂` of Lemma 6.7 is a relation on memories `Loc ⇀ Val`, which no
carrier enters; it is the tree's `MemUnion`. `ρ∣imm = ∅` written pointwise over `ResU`
(Lemma 6.36's conclusion) is `ChainSix1.immFreeU`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.ChainSix1
open BoCa.Fig16 BoCa.Fig16.Tree

variable {Loc Val : Type}

/-- `ρ∣imm = ∅` over `ResU`, written pointwise. -/
def immFreeU (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.imm

/-- `ρ∣imm = ∅`, pointwise, read back along `ΦU`. -/
theorem chain_immFree_iff {ρ : ResUT Loc Val WCactus.chain} :
    ρ.ImmFree ↔ immFreeU (ρ.map ΦU) := by
  constructor
  · intro h l c e
    rw [map_ΦU_get_some] at e
    have := h l _ e
    rwa [← ΦU_kind, ΦU_ΨU] at this
  · intro h l ψ e
    have := h l _ (map_ΦU_get.mpr e)
    rwa [ΦU_kind] at this

/-- `⟦ρ⟧ = m` at the chain is the printed `⟦ρ⟧ = m`. -/
theorem chain_lower_iff {ρ : ResUT Loc Val WCactus.chain} {m : Loc → Option Val} :
    ρ.Lower m ↔ ResU.Lower (ρ.map ΦU) m := by
  have herase : ∀ σ : ResUT Loc Val WCactus.chain, ∀ l,
      ((σ.map ΦU).get l).map CellU.erase = (σ.get l).map CellUT.erase := by
    intro σ l
    rw [PMap.map_get, Option.map_map]
    exact congrArg (fun f => Option.map f (σ.get l)) (funext ΦU_erase)
  constructor
  · rintro ⟨σ, hσ, hm⟩
    exact ⟨σ.map ΦU, chain_flat_iff.mp hσ, fun l => by rw [hm l, herase]⟩
  · rintro ⟨σ, hσ, hm⟩
    obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
    exact ⟨σ, chain_flat_iff.mpr hσ, fun l => by rw [hm l, herase]⟩

/-- `ρ∣imm = ∅` at the chain is the printed `ρ∣imm = ∅`. -/
theorem chain_restrict_imm_empty_iff {ρ : ResUT Loc Val WCactus.chain} :
    ρ.restrict Kind.imm = PMap.empty ↔ ResU.restrict (ρ.map ΦU) Kind.imm = PMap.empty := by
  rw [← chain_restrict, map_ΦU_eq_iff]
  exact Eq.congr_right (PMap.ext fun _ => rfl)

end BoCa.Fig16.Tree.ChainSix1

namespace BoCa.Fig16.Tree
open BoCa.Fig16 BoCa.Fig16.Tree.ChainSix1

/-- **`[TR]` Lemma 6.1 at the chain**: the printed statement (`ResU.compat_comm_iff`), from
`ResUT.Compat.comm` at `WCactus.chain`, at `C (ΦU −) (ΦU −)`. -/
theorem chain_ResU_compat_comm_iff {Loc Val : Type}
    (C : CellU Loc Val → CellU Loc Val → Prop)
    (hC : ∀ ψ₁ ψ₂, C ψ₁ ψ₂ → C ψ₂ ψ₁) (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Compat C ρ₁ ρ₂ ↔ ResU.Compat C ρ₂ ρ₁ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  have hc := fun (x y : ResUT Loc Val WCactus.chain) =>
    chain_compat_iff (R := fun a b => C (ΦU a) (ΦU b)) (fun _ _ => Iff.rfl) (ρ₁ := x) (ρ₂ := y)
  have hC' : ∀ a b : CellUT Loc Val WCactus.chain, C (ΦU a) (ΦU b) → C (ΦU b) (ΦU a) :=
    fun _ _ h => hC _ _ h
  exact ⟨fun h => (hc _ _).mp (ResUT.Compat.comm hC' ((hc _ _).mpr h)),
    fun h => (hc _ _).mp (ResUT.Compat.comm hC' ((hc _ _).mpr h))⟩

/-- **`[TR]` Lemma 6.2 at the chain**: the printed statement (`ResU.Comp.comm`), from
`ResUT.Comp.comm` at `WCactus.chain`, at `R (ΦU −) (ΦU −)` and `C (ΦU −) (ΦU −) (ΦU −)`. -/
theorem chain_ResU_Comp_comm {Loc Val : Type} {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁)
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) :
    ResU.Comp R C ρ₂ ρ₁ ρ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  have hc := fun (x y z : ResUT Loc Val WCactus.chain) =>
    chain_comp_iff (R := fun a b => R (ΦU a) (ΦU b)) (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c))
      (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (ρ₁ := x) (ρ₂ := y) (ρ := z)
  exact (hc _ _ _).mp (ResUT.Comp.comm (R := fun a b => R (ΦU a) (ΦU b))
    (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c)) (fun _ _ k => hR _ _ k)
    (fun _ _ _ k => hC _ _ _ k) ((hc _ _ _).mpr h))

/-- **`[TR]` Lemma 6.3 at the chain**: the printed statement (`ResU.Comp.assoc`), from
`ResUT.Comp.assoc` at `WCactus.chain`, at `R (ΦU −) (ΦU −)` and `C (ΦU −) (ΦU −) (ΦU −)`. -/
theorem chain_ResU_Comp_assoc {Loc Val : Type} {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.Comp R C ρ₂ ρ₃ x ∧ ResU.Comp R C ρ₁ x w) ↔
    (∃ y, ResU.Comp R C ρ₁ ρ₂ y ∧ ResU.Comp R C y ρ₃ w) := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨w, rfl⟩ := exists_map_ΦU w
  have hc := fun (x y z : ResUT Loc Val WCactus.chain) =>
    chain_comp_iff (R := fun a b => R (ΦU a) (ΦU b)) (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c))
      (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (ρ₁ := x) (ρ₂ := y) (ρ := z)
  have hC' : ∀ a b c d : CellUT Loc Val WCactus.chain,
      (∃ χ, C (ΦU b) (ΦU c) (ΦU χ) ∧ C (ΦU a) (ΦU χ) (ΦU d)) ↔
        (∃ υ, C (ΦU a) (ΦU b) (ΦU υ) ∧ C (ΦU υ) (ΦU c) (ΦU d)) := by
    intro a b c d
    constructor
    · rintro ⟨χ, h₁, h₂⟩
      obtain ⟨υ, k₁, k₂⟩ := (hC _ _ _ _).mp ⟨_, h₁, h₂⟩
      exact ⟨ΨU υ, by rwa [ΦU_ΨU], by rwa [ΦU_ΨU]⟩
    · rintro ⟨υ, h₁, h₂⟩
      obtain ⟨χ, k₁, k₂⟩ := (hC _ _ _ _).mpr ⟨_, h₁, h₂⟩
      exact ⟨ΨU χ, by rwa [ΦU_ΨU], by rwa [ΦU_ΨU]⟩
  have key := ResUT.Comp.assoc (R := fun a b => R (ΦU a) (ΦU b))
    (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c)) (fun _ _ _ k => hR _ _ _ k) hC' ρ₁ ρ₂ ρ₃ w
  constructor
  · rintro ⟨x, h₁, h₂⟩
    obtain ⟨x, rfl⟩ := exists_map_ΦU x
    obtain ⟨y, k₁, k₂⟩ := key.mp ⟨x, (hc _ _ _).mpr h₁, (hc _ _ _).mpr h₂⟩
    exact ⟨y.map ΦU, (hc _ _ _).mp k₁, (hc _ _ _).mp k₂⟩
  · rintro ⟨y, h₁, h₂⟩
    obtain ⟨y, rfl⟩ := exists_map_ΦU y
    obtain ⟨x, k₁, k₂⟩ := key.mpr ⟨y, (hc _ _ _).mpr h₁, (hc _ _ _).mpr h₂⟩
    exact ⟨x.map ΦU, (hc _ _ _).mp k₁, (hc _ _ _).mp k₂⟩

/-- **`[TR]` Lemma 6.4 at the chain**: the printed statement (`ResU.comp_empty_right`), from
`ResUT.comp_empty_right` at `WCactus.chain`, at `R (ΦU −) (ΦU −)` and
`C (ΦU −) (ΦU −) (ΦU −)`. -/
theorem chain_ResU_comp_empty_right {Loc Val : Type} {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    ResU.Comp R C ρ PMap.empty ρ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  have := (chain_comp_iff (R := fun a b => R (ΦU a) (ΦU b))
    (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c)) (fun _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)).mp
    (ResUT.comp_empty_right (R := fun a b => R (ΦU a) (ΦU b))
      (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c)) ρ)
  rwa [chain_empty] at this

/-- **`[TR]` Lemma 6.5 at the chain**: the printed statement (`ResU.hash_empty_right`), from
`ResUT.hash_empty_right` at `WCactus.chain`. -/
theorem chain_ResU_hash_empty_right {Loc Val : Type} {ρ : ResU Loc Val} (h : ResU.Valid ρ) :
    ResU.Hash ρ PMap.empty := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  have := chain_hash_iff.mp (ResUT.hash_empty_right (chain_valid_iff.mpr h))
  rwa [chain_empty] at this

/-- **`[TR]` Lemma 6.6 at the chain**: the printed statement (`ResU.hash_symm_iff`), from
`ResUT.hash_symm_iff` at `WCactus.chain`. -/
theorem chain_ResU_hash_symm_iff {Loc Val : Type} (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Hash ρ₁ ρ₂ ↔ ResU.Hash ρ₂ ρ₁ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  rw [← chain_hash_iff, ← chain_hash_iff]
  exact ResUT.hash_symm_iff ρ₁ ρ₂

/-- **`[TR]` Lemma 6.7 at the chain**: the printed statement (`ResU.Lower.split`), from
`ResUT.Lower.split` at `WCactus.chain`. -/
theorem chain_ResU_Lower_split {Loc Val : Type} {ρ₁ ρ₂ ρ₁₂ : ResU Loc Val}
    {m : Loc → Option Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh : ResU.Hash ρ₁ ρ₂) :
    ResU.Lower ρ₁₂ m ↔
      ∃ m₁ m₂, ResU.Lower ρ₁ m₁ ∧ ResU.Lower ρ₂ m₂ ∧ MemUnion m₁ m₂ m := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  have key := ResUT.Lower.split (m := m) (chain_resCompS_iff.mpr h) (chain_hash_iff.mpr hh)
  simp only [chain_lower_iff] at key
  exact key

/-- **`[TR]` Lemma 6.8 at the chain**: the printed statement (`ResU.Lower.congr`), from
`ResUT.Lower.congr` at `WCactus.chain`. -/
theorem chain_ResU_Lower_congr {Loc Val : Type} {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : ResU Loc Val}
    {m w : Loc → Option Val}
    (hm₂ : ResU.Lower ρ₂ m) (hm₃ : ResU.Lower ρ₃ m)
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh₂ : ResU.Hash ρ₁ ρ₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₃ : ResU.Hash ρ₁ ρ₃) :
    ResU.Lower ρ₁₂ w ↔ ResU.Lower ρ₁₃ w := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨ρ₁₃, rfl⟩ := exists_map_ΦU ρ₁₃
  rw [← chain_lower_iff, ← chain_lower_iff]
  exact ResUT.Lower.congr (chain_lower_iff.mpr hm₂) (chain_lower_iff.mpr hm₃)
    (chain_resCompS_iff.mpr h₁₂) (chain_hash_iff.mpr hh₂) (chain_resCompS_iff.mpr h₁₃)
    (chain_hash_iff.mpr hh₃)

/-- **`[TR]` Lemma 6.9 at the chain**: the printed statement (`ResU.compS_defined_iff`), from
`ResUT.compS_defined_iff` at `WCactus.chain`. -/
theorem chain_ResU_compS_defined_iff {Loc Val : Type} (ρ₁ ρ₂ : ResU Loc Val) :
    (∃ ρ, ResU.CompS ρ₁ ρ₂ ρ) ↔ ResU.CompatS ρ₁ ρ₂ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  rw [← chain_resCompatS_iff, ← ResUT.compS_defined_iff]
  constructor
  · rintro ⟨ρ, h⟩
    obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
    exact ⟨ρ, chain_resCompS_iff.mpr h⟩
  · rintro ⟨ρ, h⟩
    exact ⟨ρ.map ΦU, chain_resCompS_iff.mp h⟩

/-- **`[TR]` Lemmas 6.10 and 6.35 at the chain**: the printed statement (`ResU.Valid.split`),
from `ResUT.Valid.split` at `WCactus.chain`. -/
theorem chain_ResU_Valid_split {Loc Val : Type} {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid) : ρ₁.Valid ∧ ρ₂.Valid := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨k₁, k₂⟩ := ResUT.Valid.split (chain_resCompS_iff.mpr h) (chain_valid_iff.mpr hv)
  exact ⟨chain_valid_iff.mp k₁, chain_valid_iff.mp k₂⟩

/-- **`[TR]` Lemma 6.11 at the chain**: the printed statement (`ResU.Hash.split`), from
`ResUT.Hash.split` at `WCactus.chain`. -/
theorem chain_ResU_Hash_split {Loc Val : Type} {ρ₁ ρ₂ ρ₁₂ ρ₃ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (hh : ResU.Hash ρ₁₂ ρ₃) : ResU.Hash ρ₁ ρ₃ ∧ ResU.Hash ρ₂ ρ₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨k₁, k₂⟩ := ResUT.Hash.split (chain_resCompS_iff.mpr h) (chain_hash_iff.mpr hh)
  exact ⟨chain_hash_iff.mp k₁, chain_hash_iff.mp k₂⟩

/-- **`[TR]` Lemma 6.12 at the chain**: the printed statement (`ResU.compatS_of_compR`), from
`ResUT.compatS_of_compR` at `WCactus.chain`. -/
theorem chain_ResU_compatS_of_compR {Loc Val : Type} {ρ₁ ρ₂ ρ₃ r : ResU Loc Val}
    (h₁₂ : ResU.CompatS ρ₁ ρ₂) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompR ρ₂ ρ₃ r) : ResU.CompatS ρ₁ r := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨r, rfl⟩ := exists_map_ΦU r
  exact chain_resCompatS_iff.mp (ResUT.compatS_of_compR (chain_resCompatS_iff.mpr h₁₂)
    (chain_resCompatS_iff.mpr h₁₃) (chain_resCompR_iff.mpr h₂₃))

/-- **`[TR]` Lemma 6.13 at the chain**: the printed statement (`ResU.compatS_of_pairwise`), from
`ResUT.compatS_of_pairwise` at `WCactus.chain`. -/
theorem chain_ResU_compatS_of_pairwise {Loc Val : Type} {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompatS ρ₂ ρ₃) : ResU.CompatS σ ρ₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  exact chain_resCompatS_iff.mp (ResUT.compatS_of_pairwise (chain_resCompS_iff.mpr h₁₂)
    (chain_resCompatS_iff.mpr h₁₃) (chain_resCompatS_iff.mpr h₂₃))

/-- **`[TR]` Lemma 6.14 at the chain**: the printed statement (`ResU.compatR_of_pairwise`), from
`ResUT.compatR_of_pairwise` at `WCactus.chain`. -/
theorem chain_ResU_compatR_of_pairwise {Loc Val : Type} {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompR ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatR ρ₁ ρ₃)
    (h₂₃ : ResU.CompatR ρ₂ ρ₃) : ResU.CompatR σ ρ₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  exact chain_resCompatR_iff.mp (ResUT.compatR_of_pairwise (chain_resCompR_iff.mpr h₁₂)
    (chain_resCompatR_iff.mpr h₁₃) (chain_resCompatR_iff.mpr h₂₃))

/-- **`[TR]` Lemma 6.15 at the chain**: the printed statement (`ResU.hash_of_pairwise`), from
`ResUT.hash_of_pairwise` at `WCactus.chain`. -/
theorem chain_ResU_hash_of_pairwise {Loc Val : Type} {ρ₁ ρ₂ ρ₃ ρ₂₃ : ResU Loc Val}
    (h₁₂ : ResU.Hash ρ₁ ρ₂) (h₂₃ : ResU.Hash ρ₂ ρ₃) (h₁₃ : ResU.Hash ρ₁ ρ₃)
    (h : ResU.CompS ρ₂ ρ₃ ρ₂₃) : ResU.Hash ρ₁ ρ₂₃ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₃, rfl⟩ := exists_map_ΦU ρ₃
  obtain ⟨ρ₂₃, rfl⟩ := exists_map_ΦU ρ₂₃
  exact chain_hash_iff.mp (ResUT.hash_of_pairwise (chain_hash_iff.mpr h₁₂)
    (chain_hash_iff.mpr h₂₃) (chain_hash_iff.mpr h₁₃) (chain_resCompS_iff.mpr h))

/-- **`[TR]` Lemma 6.30 at the chain**: the printed statement (`ResU.CompatS.of_compR_left`),
from `ResUT.CompatS.of_compR_left` at `WCactus.chain`. -/
theorem chain_ResU_CompatS_of_compR_left {Loc Val : Type} {ρ ρ₁ ρ₂ r : ResU Loc Val}
    (himm : ρ.restrict Kind.imm = PMap.empty)
    (hr : ResU.CompR ρ₁ ρ₂ r) (h : ResU.CompatS ρ r) :
    ResU.CompatS ρ ρ₁ ∧ ResU.CompatS ρ ρ₂ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨r, rfl⟩ := exists_map_ΦU r
  obtain ⟨k₁, k₂⟩ := ResUT.CompatS.of_compR_left (chain_restrict_imm_empty_iff.mpr himm)
    (chain_resCompR_iff.mpr hr) (chain_resCompatS_iff.mpr h)
  exact ⟨chain_resCompatS_iff.mp k₁, chain_resCompatS_iff.mp k₂⟩

/-- **`[TR]` Lemma 6.31 at the chain**: the printed statement (`ResU.compR_iff_compS`), from
`ResUT.compR_iff_compS` at `WCactus.chain`. -/
theorem chain_ResU_compR_iff_compS {Loc Val : Type} {ρ₁ ρ₂ : ResU Loc Val}
    (h : ResU.CompatS ρ₁ ρ₂)
    (σ : ResU Loc Val) : ResU.CompR ρ₁ ρ₂ σ ↔ ResU.CompS ρ₁ ρ₂ σ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  rw [← chain_resCompR_iff, ← chain_resCompS_iff]
  exact ResUT.compR_iff_compS (chain_resCompatS_iff.mpr h) σ

/-- **`[TR]` Lemma 6.36 at the chain**: the printed statement (`ExW.immFree`), from
`ExWT.immFree` at `WCactus.chain`, at `R (ΦU −) (ΦU −)` and `C (ΦU −) (ΦU −) (ΦU −)`; the
schematic operator's hypothesis is read through `ΦU_kind`. -/
theorem chain_ExW_immFree {Loc Val : Type} {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.kind ≠ Kind.imm → ψ₂.kind ≠ Kind.imm →
        ψ.kind ≠ Kind.imm)
    {ρ σ : ResU Loc Val} (h : ExW R C ρ σ) : immFreeU σ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  have hC' : ∀ a b c : CellUT Loc Val WCactus.chain, C (ΦU a) (ΦU b) (ΦU c) →
      a.kind ≠ Kind.imm → b.kind ≠ Kind.imm → c.kind ≠ Kind.imm := by
    intro a b c k ka kb
    rw [← ΦU_kind] at ka kb ⊢
    exact hC _ _ _ k ka kb
  exact chain_immFree_iff.mp (ExWT.immFree hC'
    ((chain_exW_iff (R := fun a b => R (ΦU a) (ΦU b))
      (C := fun a b c => C (ΦU a) (ΦU b) (ΦU c)) (fun _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl)).mpr h))

end BoCa.Fig16.Tree

end
