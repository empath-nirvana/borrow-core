import Support.Model.Tree.Port.Six16to24
import Support.Model.Tree.Port.Six25to33
import Support.Model.Tree.Port.Six27
import Support.Model.Tree.Port.Six28to29
import Support.Model.Tree.Port.Six43to46
import Support.Model.Tree.Chain59

/-!
# `[TR]` Lemmas 6.16–6.29, 6.32, 6.33 and 6.41–6.44 at the chain

`[spec §62]`. The printed statements of these lemmas (`Paper/S6_1_StandardLemmas/Lemmas.lean`,
`Paper/S6_2_NonStandardLemmas/Lemmas.lean`) are the chain instances of the tree's
(`Tree/Port/Six16to24.lean`, `Six25to33.lean`, `Six27.lean`, `Six28to29.lean`,
`Six43to46.lean`, `Split.lean`): every resource is the image of one at `WCactus.chain`
(`exists_map_ΦU`), every hypothesis is read back along `ΦU`, and the conclusion read out along
it. Besides the kit, the statements read `⦇−⦈_○` (Definition 6.1, `chain_flatR_iff`), `⟦−⟧`
(row 5.25, `chain_lower_iff`) and singleton cells: `ℓ ↦ own(v)` (`chain_single_own`), a printed
`ℓ ↦ mut(β, v, ρ_v, P̂)` as the image of the tree's `ℓ ↦ mut({β}, v, ΨU ρ_v, P̂ ∘ ΨU⁻¹)`
(`chain_single_mutOf`, through `ΨU_mutOf`), and `ℓ ↦ imm(ᾱ, v, ρ_v)` at the finite set of
`ᾱ`'s members (`chain_single_immOf`) or at `{α}` (`chain_single_immOf_single`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.ChainSix2
open BoCa.Fig16 BoCa.Fig16.Tree

variable {Loc Val : Type}

/-- `⦇−⦈_○` (Definition 6.1) at the chain is the printed `⦇−⦈_○`. -/
theorem chain_flatR_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    ResUT.FlatR ρ σ ↔ ResU.FlatR (ρ.map ΦU) (σ.map ΦU) := by
  constructor
  · rintro ⟨a, e, ha, he, hc⟩
    exact ⟨a.map ΦU, e.map ΦU, chain_agW_iff.mp ha, chain_exR_iff.mp he,
      chain_resCompR_iff.mp hc⟩
  · rintro ⟨a, e, ha, he, hc⟩
    obtain ⟨a, rfl⟩ := exists_map_ΦU a
    obtain ⟨e, rfl⟩ := exists_map_ΦU e
    exact ⟨a, e, chain_agW_iff.mpr ha, chain_exR_iff.mpr he, chain_resCompR_iff.mpr hc⟩

theorem erase_map_ΦU (o : Option (CellUT Loc Val WCactus.chain)) :
    (o.map ΦU).map CellU.erase = o.map CellUT.erase := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (ΦU_erase ψ)

/-- `⟦−⟧` (row 5.25) at the chain is the printed `⟦−⟧`. -/
theorem chain_lower_iff {ρ : ResUT Loc Val WCactus.chain} {m : Loc → Option Val} :
    ResUT.Lower ρ m ↔ ResU.Lower (ρ.map ΦU) m := by
  constructor
  · rintro ⟨σ, hf, hm⟩
    refine ⟨σ.map ΦU, chain_flat_iff.mp hf, fun l => ?_⟩
    rw [hm l, PMap.map_get, erase_map_ΦU]
  · rintro ⟨σ, hf, hm⟩
    obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
    refine ⟨σ, chain_flat_iff.mpr hf, fun l => ?_⟩
    rw [hm l, PMap.map_get, erase_map_ΦU]

/-- `ℓ ↦ own(v)` read back along `ΦU`. -/
theorem chain_single_own (l : Loc) (v : Val) :
    ResU.single l (CellU.ownOf v) =
      (ResUT.single l (CellUT.ownOf (K := WCactus.chain) (Loc := Loc) v)).map ΦU := by
  rw [chain_single, ΦU_ownOf]

/-- `ℓ ↦ mut(β, v, ρ_v, P̂)` read back along `ΦU`: the image of
`ℓ ↦ mut({β}, v, ΨU ρ_v, P̂ ∘ ΨU⁻¹)`. -/
theorem chain_single_mutOf (l : Loc) {b : Life} {v : Val} {ρv : ResU Loc Val}
    (h : ρv.InStratum b) (P : Val → SPropS Loc Val b) (hw : P v ⟨ρv, h⟩) :
    ResU.single l (CellU.mutOf b v ρv h P hw) =
      (ResUT.single l (CellUT.mutOf (TSet.single b) v (ρv.map ΨU) (ΨU_map_inStratum h)
        (predΨ P) ⟨ρv, h, rfl, hw⟩)).map ΦU := by
  rw [chain_single, ← ΦU_ΨU (CellU.mutOf b v ρv h P hw), ΨU_mutOf]
  rfl

/-- A tree `mut` cell at `{β}` with invariant `P̂ ∘ ΨU⁻¹` is the image along `ΨU` of the printed
cell its witness names. -/
theorem mutOf_predΨ_eq {b : Life} {v : Val} {χ : ResUT Loc Val WCactus.chain}
    {h : χ.InStratum (TSet.single b)} {P : Val → SPropS Loc Val b} {hw : predΨ P v ⟨χ, h⟩}
    {r₀ : ResU Loc Val} {h₀ : r₀.InStratum b} (e₀ : r₀.map ΨU = χ) (hP : P v ⟨r₀, h₀⟩) :
    CellUT.mutOf (TSet.single b) v χ h (predΨ P) hw = ΨU (CellU.mutOf b v r₀ h₀ P hP) := by
  rw [ΨU_mutOf]
  exact CellUT.mutOf_congr' rfl e₀.symm _ _ _ _ _ _ fun _ _ _ _ => Iff.rfl

/-- `ℓ ↦ imm({α}, v, ρ_v)` read back along `ΦU`, at the tree's `{α}`. -/
theorem chain_single_immOf_single (l : Loc) (α : Life) (v : Val)
    (τ : ResUT Loc Val WCactus.chain) (hs : ResU.InStratum (LSet.singleton α).join (τ.map ΦU))
    (hτ : τ.InStratum (TSet.single α)) :
    ResU.single l (CellU.immOf (LSet.singleton α) v (τ.map ΦU) hs) =
      (ResUT.single l (CellUT.immOf (TSet.single α) v τ hτ)).map ΦU := by
  rw [chain_single, ΦU_immOf_eq (TSet.toLSet_single α) rfl]

theorem inStratum_single_of_lset {α : Life} {τ : ResUT Loc Val WCactus.chain}
    (hs : ResU.InStratum (LSet.singleton α).join (τ.map ΦU)) : τ.InStratum (TSet.single α) :=
  chain_inStratum_jn_iff.mpr (by unfold TSet.jn; rw [TSet.toLSet_single]; exact hs)

end BoCa.Fig16.Tree.ChainSix2

namespace BoCa.Fig16.Tree
open BoCa.Fig16 BoCa.Fig16.Tree.ChainSix2

variable {Loc Val : Type}

/-- `[TR]` Lemma 6.16 at the chain: the printed statement (`ResU.CompatS.of_flat`), from
`ResUT.CompatS.of_flat` at `WCactus.chain`. -/
theorem chain_ResU_CompatS_of_flat {ρ ρ' f : ResU Loc Val} (hf : ResU.Flat ρ' f)
    (h : ResU.CompatS ρ f) : ResU.CompatS ρ ρ' := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨f, rfl⟩ := exists_map_ΦU f
  exact chain_resCompatS_iff.mp
    (ResUT.CompatS.of_flat (chain_flat_iff.mpr hf) (chain_resCompatS_iff.mpr h))

/-- `[TR]` Lemma 6.17 at the chain: the printed statement (`ResU.compatS_of_hash_mut`), from
`ResUT.compatS_of_hash_mut` at `WCactus.chain`. -/
theorem chain_ResU_compatS_of_hash_mut {ρ ρv w : ResU Loc Val} {l : Loc} {α : Life} {v : Val}
    {hs : ρv.InStratum α} {P : Val → SPropS Loc Val α} {hP : P v ⟨ρv, hs⟩}
    (h : ResU.Hash ρ (ResU.single l (CellU.mutOf α v ρv hs P hP)))
    (hw : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) w) : ResU.CompatS ρ w := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨w, rfl⟩ := exists_map_ΦU w
  rw [chain_single_mutOf] at h
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hw
  exact chain_resCompatS_iff.mp
    (ResUT.compatS_of_hash_mut (chain_hash_iff.mpr h) (chain_resCompS_iff.mpr hw))

/-- `[TR]` Lemma 6.18 at the chain: the printed statement (`ExS.split`), from `ExST.split` at
`WCactus.chain`. -/
theorem chain_ExS_split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ExS ρ₁₂ w ↔ ∃ σ₁ σ₂, ExS ρ₁ σ₁ ∧ ExS ρ₂ σ₂ ∧ ResU.CompS σ₁ σ₂ w := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨w, rfl⟩ := exists_map_ΦU w
  rw [← chain_exS_iff, ExST.split (chain_resCompS_iff.mpr h₁₂)]
  constructor
  · rintro ⟨σ₁, σ₂, a, b, c⟩
    exact ⟨_, _, chain_exS_iff.mp a, chain_exS_iff.mp b, chain_resCompS_iff.mp c⟩
  · rintro ⟨σ₁, σ₂, a, b, c⟩
    obtain ⟨σ₁, rfl⟩ := exists_map_ΦU σ₁
    obtain ⟨σ₂, rfl⟩ := exists_map_ΦU σ₂
    exact ⟨σ₁, σ₂, chain_exS_iff.mpr a, chain_exS_iff.mpr b, chain_resCompS_iff.mpr c⟩

/-- `[TR]` Lemma 6.19 at the chain: the printed statement (`ResU.flatR_idem`), from
`ResUT.flatR_idem` at `WCactus.chain`. -/
theorem chain_ResU_flatR_idem {ρ σ : ResU Loc Val} (hf : ResU.FlatR ρ σ) :
    ResU.CompR σ σ σ ∧ ∀ τ, ResU.CompR σ σ τ → τ = σ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  obtain ⟨h₁, h₂⟩ := ResUT.flatR_idem (chain_flatR_iff.mpr hf)
  refine ⟨chain_resCompR_iff.mp h₁, fun τ hτ => ?_⟩
  obtain ⟨τ, rfl⟩ := exists_map_ΦU τ
  rw [h₂ τ (chain_resCompR_iff.mpr hτ)]

/-- `[TR]` Lemma 6.20 at the chain: the printed statement (`AgW.split`), from `AgWT.split` at
`WCactus.chain`. -/
theorem chain_AgW_split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    AgW ρ₁₂ w ↔ ∃ σ₁ σ₂, AgW ρ₁ σ₁ ∧ AgW ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ w := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  obtain ⟨ρ₁₂, rfl⟩ := exists_map_ΦU ρ₁₂
  obtain ⟨w, rfl⟩ := exists_map_ΦU w
  rw [← chain_agW_iff, AgWT.split (chain_resCompS_iff.mpr h₁₂)]
  constructor
  · rintro ⟨σ₁, σ₂, a, b, c⟩
    exact ⟨_, _, chain_agW_iff.mp a, chain_agW_iff.mp b, chain_resCompR_iff.mp c⟩
  · rintro ⟨σ₁, σ₂, a, b, c⟩
    obtain ⟨σ₁, rfl⟩ := exists_map_ΦU σ₁
    obtain ⟨σ₂, rfl⟩ := exists_map_ΦU σ₂
    exact ⟨σ₁, σ₂, chain_agW_iff.mpr a, chain_agW_iff.mpr b, chain_resCompR_iff.mpr c⟩

/-- `[TR]` Lemma 6.21 at the chain: the printed statement (`ResU.six21`), from `ResUT.six21` at
`WCactus.chain`. -/
theorem chain_ResU_six21 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (h : ResU.Hash ρ W) :
    ResU.CompatS ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [chain_single_mutOf]
  exact chain_resCompatS_iff.mp
    (ResUT.six21 (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr h))

/-- `[TR]` Lemma 6.22 at the chain: the printed statement (`ResU.six22`), from `ResUT.six22` at
`WCactus.chain`. -/
theorem chain_ResU_six22 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (h : ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw))) :
    ResU.Hash ρ W := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [chain_single_mutOf] at h
  exact chain_hash_iff.mp (ResUT.six22 (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr h))

/-- `[TR]` Lemma 6.23 at the chain: the printed statement (`ResU.six23`), from `ResUT.six23` at
`WCactus.chain`. -/
theorem chain_ResU_six23 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (h : ResU.Hash ρ W) :
    ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [chain_single_mutOf]
  exact chain_hash_iff.mp (ResUT.six23 (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr h))

/-- `[TR]` Lemma 6.24 at the chain: the printed statement (`ResU.six24`), from `ResUT.six24` at
`WCactus.chain`. -/
theorem chain_ResU_six24 {l : Loc} {b : Life} {v : Val} {ρ ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) :
    ResU.Hash ρ (ResU.single l (CellU.mutOf b v ρv hstr P hw)) ↔ ResU.Hash ρ W := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [chain_single_mutOf]
  exact chain_hash_iff.symm.trans
    ((ResUT.six24 (ρ := ρ) (chain_resCompS_iff.mpr hW)).trans chain_hash_iff)

/-- `[TR]` Lemma 6.25 at the chain: the printed statement (`ResU.six25`), from `ResUT.six25` at
`WCactus.chain`. -/
theorem chain_ResU_six25 {l : Loc} {b : Life} {v : Val} {ρv W : ResU Loc Val}
    {hstr : ResU.InStratum b ρv} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hstr⟩}
    {m : Loc → Option Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hvm : ResU.Valid (ResU.single l (CellU.mutOf b v ρv hstr P hw)))
    (hvW : ResU.Valid W) :
    ResU.Lower (ResU.single l (CellU.mutOf b v ρv hstr P hw)) m ↔ ResU.Lower W m := by
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [chain_single_mutOf] at hvm ⊢
  exact chain_lower_iff.symm.trans
    ((ResUT.six25 (chain_resCompS_iff.mpr hW) (chain_valid_iff.mpr hvm)
      (chain_valid_iff.mpr hvW)).trans chain_lower_iff)

/-- `[TR]` Lemma 6.26 at the chain: the printed statement (`ResU.six26`), from `ResUT.six26` at
`WCactus.chain`, with `ᾱ` the finite set of its members (`TSet.ofLSet`). -/
theorem chain_ResU_six26 {l : Loc} {s : LSet} {v : Val} {ρv W : ResU Loc Val}
    {hs : ρv.InStratum s.join} {m : Loc → Option Val}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hvi : ResU.Valid (ResU.single l (CellU.immOf s v ρv hs)))
    (hvW : ResU.Valid W) :
    ResU.Lower (ResU.single l (CellU.immOf s v ρv hs)) m ↔ ResU.Lower W m := by
  obtain ⟨ρv, rfl⟩ := exists_map_ΦU ρv
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  rw [chain_single_own] at hW
  rw [chain_single_immOf] at hvi ⊢
  exact chain_lower_iff.symm.trans
    ((ResUT.six26 (chain_resCompS_iff.mpr hW) (chain_valid_iff.mpr hvi)
      (chain_valid_iff.mpr hvW)).trans chain_lower_iff)

/-- `[TR]` Lemma 6.27 at the chain: the printed statement (`ResU.six27`), from `ResUT.six27` at
`WCactus.chain`. The tree's `hD : K.DownOf D {α}` is discharged by the printed `↓α`
(`WCactus.chain_downOf α`); the tree's `mut` cell at `{α}` with invariant `P̂ ∘ ΨU⁻¹` is the
image of the printed one (`chain_single_mutOf`, `mutOf_predΨ_eq`). -/
theorem chain_ResU_six27 {l : BoCa.Loc} {α : Life} {v : BoCa.Val}
    {ρ ρv M ρ' : ResU BoCa.Loc BoCa.Val}
    {h : ResU.InStratum α ρv} {P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α}
    {hw : P v ⟨ρv, h⟩}
    (hout : ResU.InStratum α ρ)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M)
    (hu : ResU.UpdV M ρ') :
    ∃ (v' : BoCa.Val) (χ : ResU BoCa.Loc BoCa.Val) (h' : ResU.InStratum α χ)
      (hw' : P v' ⟨χ, h'⟩),
      ResU.CompS (ρ'.del l) (ResU.single l (CellU.mutOf α v' χ h' P hw')) ρ' := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨M, rfl⟩ := exists_map_ΦU M
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  rw [chain_single_mutOf] at hM
  obtain ⟨v', χ, h', hw', hc⟩ := ResUT.six27 (WCactus.chain_downOf α)
    (chain_inStratum_iff.mpr hout) (chain_resCompS_iff.mpr hM) (chain_updV_iff.mpr hu)
  obtain ⟨r₀, h₀, e₀, hP⟩ := id hw'
  refine ⟨v', r₀, h₀, hP, ?_⟩
  rw [mutOf_predΨ_eq e₀ hP] at hc
  have := chain_resCompS_iff.mp hc
  rwa [chain_del, chain_single, ΦU_ΨU] at this

/-- `[TR]` Lemma 6.28 at the chain: the printed statement (`ResU.six28`), from `ResUT.six28` at
`WCactus.chain`. -/
theorem chain_ResU_six28 {l : Loc} {b : Life} {v v' : Val}
    {ρ ρ' ρv ρv' W W' M M' O O' : ResU Loc Val}
    {hs : ResU.InStratum b ρv} {hs' : ResU.InStratum b ρv'}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hs⟩} {hw' : P v' ⟨ρv', hs'⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hW' : ResU.CompS ρv' (ResU.single l (CellU.ownOf v')) W')
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf b v ρv hs P hw)) M)
    (hM' : ResU.CompS ρ' (ResU.single l (CellU.mutOf b v' ρv' hs' P hw')) M')
    (hO : ResU.CompS ρ W O) (hO' : ResU.CompS ρ' W' O')
    (hvM : ResU.Valid M) (hvM' : ResU.Valid M')
    (hvO : ResU.Valid O) (hvO' : ResU.Valid O') :
    ResU.Upd M M' ↔ ResU.Upd O O' := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  obtain ⟨W', rfl⟩ := exists_map_ΦU W'
  obtain ⟨M, rfl⟩ := exists_map_ΦU M
  obtain ⟨M', rfl⟩ := exists_map_ΦU M'
  obtain ⟨O, rfl⟩ := exists_map_ΦU O
  obtain ⟨O', rfl⟩ := exists_map_ΦU O'
  rw [← map_ΦU_ΨU ρv, chain_single_own] at hW
  rw [← map_ΦU_ΨU ρv', chain_single_own] at hW'
  rw [chain_single_mutOf] at hM hM'
  exact chain_upd_iff.symm.trans
    ((ResUT.six28 (chain_resCompS_iff.mpr hW) (chain_resCompS_iff.mpr hW')
      (chain_resCompS_iff.mpr hM) (chain_resCompS_iff.mpr hM') (chain_resCompS_iff.mpr hO)
      (chain_resCompS_iff.mpr hO') (chain_valid_iff.mpr hvM) (chain_valid_iff.mpr hvM')
      (chain_valid_iff.mpr hvO) (chain_valid_iff.mpr hvO')).trans chain_upd_iff)

/-- `[TR]` Lemma 6.29 at the chain: the printed statement (`ResU.six29`), from `ResUT.six29` at
`WCactus.chain`, with `{α}` the tree's one-lifetime set. -/
theorem chain_ResU_six29 {α : Life} {ρ ρv ρ' W ρρi : ResU BoCa.Loc BoCa.Val}
    {l : BoCa.Loc} {v : BoCa.Val} {hv : ρv.InStratum (LSet.singleton α).join}
    (hα : ρ.InStratum α)
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hhash : ResU.Hash ρ W)
    (hρi : ResU.CompS ρ (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρρi)
    (hupd : ResU.UpdV ρρi ρ') :
    ResU.CompS (ρ'.del l)
      (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) ρ' := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨ρv, rfl⟩ := exists_map_ΦU ρv
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  obtain ⟨W, rfl⟩ := exists_map_ΦU W
  obtain ⟨ρρi, rfl⟩ := exists_map_ΦU ρρi
  rw [chain_single_own] at hW
  rw [chain_single_immOf_single l α v ρv hv (inStratum_single_of_lset hv)] at hρi ⊢
  rw [← chain_del]
  exact chain_resCompS_iff.mp (ResUT.six29 (chain_inStratum_iff.mpr hα)
    (chain_resCompS_iff.mpr hW) (chain_hash_iff.mpr hhash) (chain_resCompS_iff.mpr hρi)
    (chain_updV_iff.mpr hupd))

/-- `[TR]` Lemma 6.32 at the chain: the printed statement (`ExS.toExR`), from `ExST.toExR` at
`WCactus.chain`. -/
theorem chain_ExS_toExR {ρ σ : ResU Loc Val} (h : ExS ρ σ) : ExR ρ σ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  exact chain_exR_iff.mp (ExST.toExR (chain_exS_iff.mpr h))

/-- `[TR]` Lemma 6.33 at the chain: the printed statement (`ResU.six33`), from `ResUT.six33` at
`WCactus.chain`. -/
theorem chain_ResU_six33 {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ) : ResU.FlatR ρ σ := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  obtain ⟨σ, rfl⟩ := exists_map_ΦU σ
  exact chain_flatR_iff.mp (ResUT.six33 (chain_flat_iff.mpr h))

/-- `[TR]` Lemma 6.41 at the chain: the printed statement (`ResU.compatS_single_own`), from
`ResUT.compatS_single_own` at `WCactus.chain`. -/
theorem chain_ResU_compatS_single_own {l : Loc} {v : Val} {ρ : ResU Loc Val}
    (h : ResU.CompatS (ResU.single l (CellU.ownOf v)) ρ) : ρ.get l = none := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  rw [chain_single_own] at h
  exact map_ΦU_get_none.mpr (ResUT.compatS_single_own (chain_resCompatS_iff.mpr h))

/-- `[TR]` Lemma 6.42 at the chain: the printed statement (`ResU.compatS_single_mut`), from
`ResUT.compatS_single_mut` at `WCactus.chain`. -/
theorem chain_ResU_compatS_single_mut {l : Loc} {b : Life} {v : Val}
    {σ : ResU Loc Val} {hs : σ.InStratum b} {P : Val → SPropS Loc Val b}
    {hw : P v ⟨σ, hs⟩} {ρ : ResU Loc Val}
    (h : ResU.CompatS (ResU.single l (CellU.mutOf b v σ hs P hw)) ρ) :
    ρ.get l = none := by
  obtain ⟨ρ, rfl⟩ := exists_map_ΦU ρ
  rw [chain_single_mutOf] at h
  exact map_ΦU_get_none.mpr (ResUT.compatS_single_mut (chain_resCompatS_iff.mpr h))

/-- `[TR]` Lemma 6.43 at the chain: the printed statement (`ResU.compS_single_imm`), from
`ResUT.compS_single_imm` at `WCactus.chain`, with `α`, `β` the finite sets of their members
(`TSet.ofLSet`). -/
theorem chain_ResU_compS_single_imm (l : Loc) (s t : LSet) (v : Val) (ρ' : ResU Loc Val)
    (h : ρ'.InStratum s.join) (h' : ρ'.InStratum t.join)
    (h'' : ρ'.InStratum (s ∪ t).join) :
    ResU.CompS (ResU.single l (CellU.immOf s v ρ' h))
      (ResU.single l (CellU.immOf t v ρ' h'))
      (ResU.single l (CellU.immOf (s ∪ t) v ρ' h'')) := by
  obtain ⟨ρ', rfl⟩ := exists_map_ΦU ρ'
  have eU : (TSet.ofLSet s ∪ TSet.ofLSet t).toLSet = s ∪ t := by
    rw [TSet.toLSet_union, TSet.toLSet_ofLSet, TSet.toLSet_ofLSet]
  have hU : ρ'.InStratum (TSet.ofLSet s ∪ TSet.ofLSet t) :=
    chain_inStratum_jn_iff.mpr (by unfold TSet.jn; rw [eU]; exact h'')
  have e₃ : ResU.single l (CellU.immOf (s ∪ t) v (ρ'.map ΦU) h'') =
      (ResUT.single l (CellUT.immOf (TSet.ofLSet s ∪ TSet.ofLSet t) v ρ' hU)).map ΦU := by
    rw [chain_single, ΦU_immOf_eq eU rfl]
  rw [chain_single_immOf, chain_single_immOf, e₃]
  exact chain_resCompS_iff.mp (ResUT.compS_single_imm l _ _ v ρ' _ _ hU)

/-- `[TR]` Lemma 6.44 at the chain: the printed statement (`ResU.compatS_single_imm_inv`), from
`ResUT.compatS_single_imm_inv` at `WCactus.chain`, with `α`, `β` the finite sets of their
members (`TSet.ofLSet`). -/
theorem chain_ResU_compatS_single_imm_inv {l : Loc} {s t : LSet} {v₁ v₂ : Val}
    {ρ₁ ρ₂ : ResU Loc Val} {h₁ : ρ₁.InStratum s.join} {h₂ : ρ₂.InStratum t.join}
    (h : ResU.CompatS (ResU.single l (CellU.immOf s v₁ ρ₁ h₁))
      (ResU.single l (CellU.immOf t v₂ ρ₂ h₂))) : v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  obtain ⟨ρ₁, rfl⟩ := exists_map_ΦU ρ₁
  obtain ⟨ρ₂, rfl⟩ := exists_map_ΦU ρ₂
  rw [chain_single_immOf, chain_single_immOf] at h
  obtain ⟨hv, hρ⟩ := ResUT.compatS_single_imm_inv (chain_resCompatS_iff.mpr h)
  exact ⟨hv, congrArg (PMap.map ΦU) hρ⟩

end BoCa.Fig16.Tree

end
