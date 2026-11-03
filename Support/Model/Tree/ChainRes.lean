import Support.Model.Tree.Port.Base
import Support.Model.Tree.CarrierChainValid

/-!
# The printed resource vocabulary along `chainEquiv`

`[spec §62]`. On resources `chainEquiv` is `ρ ↦ ρ.map ΦU`, a bijection from the resources of the
tree-stratified carrier at `WCactus.chain` onto the printed resources (`map_ΦU_ΨU`,
`map_ΨU_ΦU`). Each piece of the printed vocabulary the printed proofs of `[TR]` §6 use is the
tree's along it: `◐` at any cell relations that correspond (`chain_comp_iff`), `●`, `○`, `▶◀`,
`⋈`, `⨀`, the walks, `ρ∣ι`, the index sets, `ℓ ↦ ψ`, `ρ/ℓ`, `ρ∣ῑ`, `≤`, `⦇ρ⦈(ℓ)` and `Res_α`.

A printed statement over `ResU` is the chain instance of a tree statement over `ResUT K`
when every printed piece it reads is the tree's along `ΦU`; these are the lemmas it is read
through.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type}

/-! ### The bijection on resources -/

theorem map_ΦU_eq_iff {τ : ResUT Loc Val WCactus.chain} {ρ : ResU Loc Val} :
    τ.map ΦU = ρ ↔ τ = ρ.map ΨU := by
  constructor
  · rintro rfl; exact (map_ΨU_ΦU τ).symm
  · rintro rfl; exact map_ΦU_ΨU ρ

/-- Every printed resource is the image of a tree resource at the chain. -/
theorem exists_map_ΦU (ρ : ResU Loc Val) : ∃ τ : ResUT Loc Val WCactus.chain, τ.map ΦU = ρ :=
  ⟨ρ.map ΨU, map_ΦU_ΨU ρ⟩

theorem map_ΦU_get {τ : ResUT Loc Val WCactus.chain} {l : Loc} {ψ : CellUT Loc Val WCactus.chain} :
    (τ.map ΦU).get l = some (ΦU ψ) ↔ τ.get l = some ψ := by
  rw [PMap.map_get]
  constructor
  · intro h
    cases e : τ.get l with
    | none => rw [e] at h; cases h
    | some χ => rw [e] at h; rw [ΦU_injective (Option.some.inj h)]
  · intro h; rw [h]; rfl

theorem map_ΦU_get_none {τ : ResUT Loc Val WCactus.chain} {l : Loc} :
    (τ.map ΦU).get l = none ↔ τ.get l = none := by
  rw [PMap.map_get, Option.map_eq_none_iff]

theorem map_ΦU_get_some {τ : ResUT Loc Val WCactus.chain} {l : Loc} {c : CellU Loc Val} :
    (τ.map ΦU).get l = some c ↔ τ.get l = some (ΨU c) := by
  rw [← map_ΦU_get, ΦU_ΨU]

/-! ### `◐` and its instances -/

section Comp
variable {R : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → Prop}
  {C : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain →
    CellUT Loc Val WCactus.chain → Prop}
  {R' : CellU Loc Val → CellU Loc Val → Prop}
  {C' : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- Cell relations that correspond along `ΦU`, read back along `ΨU`. -/
theorem rel_ΨU (hR : ∀ a b, R a b ↔ R' (ΦU a) (ΦU b)) :
    ∀ a b, R' a b → R (ΨU a) (ΨU b) :=
  fun a b h => (hR _ _).mpr (by rw [ΦU_ΨU, ΦU_ΨU]; exact h)

theorem rel3_ΨU (hC : ∀ a b c, C a b c ↔ C' (ΦU a) (ΦU b) (ΦU c)) :
    ∀ a b c, C' a b c → C (ΨU a) (ΨU b) (ΨU c) :=
  fun a b c h => (hC _ _ _).mpr (by rw [ΦU_ΨU, ΦU_ΨU, ΦU_ΨU]; exact h)

/-- **`◐` at the chain is the printed `◐`**, at cell relations that correspond along `ΦU`. -/
theorem chain_comp_iff (hR : ∀ a b, R a b ↔ R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c ↔ C' (ΦU a) (ΦU b) (ΦU c)) {ρ₁ ρ₂ ρ : ResUT Loc Val WCactus.chain} :
    G.Comp R C ρ₁ ρ₂ ρ ↔ ResU.Comp R' C' (ρ₁.map ΦU) (ρ₂.map ΦU) (ρ.map ΦU) := by
  refine ⟨t_comp (fun a b => (hR a b).mp) (fun a b c => (hC a b c).mp), fun h => ?_⟩
  have := p_comp (rel_ΨU hR) (rel3_ΨU hC) h
  rwa [map_ΨU_ΦU, map_ΨU_ΦU, map_ΨU_ΦU] at this

/-- `▸◁` at the chain is the printed `▸◁`. -/
theorem chain_compat_iff (hR : ∀ a b, R a b ↔ R' (ΦU a) (ΦU b))
    {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    G.Compat R ρ₁ ρ₂ ↔ ResU.Compat R' (ρ₁.map ΦU) (ρ₂.map ΦU) := by
  constructor
  · intro h l a b e₁ e₂
    rw [map_ΦU_get_some] at e₁ e₂
    have := (hR _ _).mp (h l _ _ e₁ e₂)
    rwa [ΦU_ΨU, ΦU_ΨU] at this
  · intro h l a b e₁ e₂
    exact (hR a b).mpr (h l _ _ (map_ΦU_get.mpr e₁) (map_ΦU_get.mpr e₂))

theorem chain_bigComp_iff (hR : ∀ a b, R a b ↔ R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c ↔ C' (ΦU a) (ΦU b) (ΦU c)) {L : List (ResUT Loc Val WCactus.chain)}
    {b : ResUT Loc Val WCactus.chain} :
    G.BigComp R C L b ↔ BigComp R' C' (L.map (PMap.map ΦU)) (b.map ΦU) := by
  refine ⟨t_bigComp (fun a b => (hR a b).mp) (fun a b c => (hC a b c).mp), fun h => ?_⟩
  have := p_bigComp (rel_ΨU hR) (rel3_ΨU hC) h
  rwa [List.map_map, map_ΨU_ΦU,
    show PMap.map ΨU ∘ PMap.map ΦU = (id : ResUT Loc Val WCactus.chain → _) from
      funext map_ΨU_ΦU, List.map_id] at this

theorem chain_exW_iff (hR : ∀ a b, R a b ↔ R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c ↔ C' (ΦU a) (ΦU b) (ΦU c)) {ρ σ : ResUT Loc Val WCactus.chain} :
    G.ExW CellUT.kind CellUT.wit R C ρ σ ↔ ExW R' C' (ρ.map ΦU) (σ.map ΦU) := by
  refine ⟨t_exW (fun a b => (hR a b).mp) (fun a b c => (hC a b c).mp), fun h => ?_⟩
  have := p_exW (rel_ΨU hR) (rel3_ΨU hC) h
  rwa [map_ΨU_ΦU, map_ΨU_ΦU] at this

end Comp

theorem cellCompatS_iff (a b : CellUT Loc Val WCactus.chain) :
    CellUT.CompatS a b ↔ CellU.CompatS (ΦU a) (ΦU b) := chain_compatS_iff.symm

theorem cellCompS_iff (a b c : CellUT Loc Val WCactus.chain) :
    CellUT.CompS a b c ↔ CellU.CompS (ΦU a) (ΦU b) (ΦU c) := chain_compS_iff.symm

theorem cellCompatR_iff (a b : CellUT Loc Val WCactus.chain) :
    CellUT.CompatR a b ↔ CellU.CompatR (ΦU a) (ΦU b) := chain_compatR_iff.symm

theorem cellCompR_iff (a b c : CellUT Loc Val WCactus.chain) :
    CellUT.CompR a b c ↔ CellU.CompR (ΦU a) (ΦU b) (ΦU c) := chain_compR_iff.symm

/-- **`●` at the chain is the printed `●`.** -/
theorem chain_resCompS_iff {ρ₁ ρ₂ ρ : ResUT Loc Val WCactus.chain} :
    ResUT.CompS ρ₁ ρ₂ ρ ↔ ResU.CompS (ρ₁.map ΦU) (ρ₂.map ΦU) (ρ.map ΦU) :=
  chain_comp_iff cellCompatS_iff cellCompS_iff

/-- **`○` at the chain is the printed `○`.** -/
theorem chain_resCompR_iff {ρ₁ ρ₂ ρ : ResUT Loc Val WCactus.chain} :
    ResUT.CompR ρ₁ ρ₂ ρ ↔ ResU.CompR (ρ₁.map ΦU) (ρ₂.map ΦU) (ρ.map ΦU) :=
  chain_comp_iff cellCompatR_iff cellCompR_iff

theorem chain_resCompatS_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.CompatS ρ₁ ρ₂ ↔ ResU.CompatS (ρ₁.map ΦU) (ρ₂.map ΦU) :=
  chain_compat_iff cellCompatS_iff

theorem chain_resCompatR_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.CompatR ρ₁ ρ₂ ↔ ResU.CompatR (ρ₁.map ΦU) (ρ₂.map ΦU) :=
  chain_compat_iff cellCompatR_iff

theorem chain_exS_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    ExST ρ σ ↔ ExS (ρ.map ΦU) (σ.map ΦU) :=
  chain_exW_iff cellCompatS_iff cellCompS_iff

theorem chain_exR_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    ExRT ρ σ ↔ ExR (ρ.map ΦU) (σ.map ΦU) :=
  chain_exW_iff cellCompatR_iff cellCompR_iff

theorem chain_agW_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    AgWT ρ σ ↔ AgW (ρ.map ΦU) (σ.map ΦU) := by
  refine ⟨t_agW, fun h => ?_⟩
  have := p_agW h
  rwa [map_ΨU_ΦU, map_ΨU_ΦU] at this

/-! ### Restrictions, index sets, singletons -/

theorem chain_restrict (ρ : ResUT Loc Val WCactus.chain) (k : Kind) :
    (ρ.restrict k).map ΦU = ResU.restrict (ρ.map ΦU) k := t_restrict ρ k

theorem chain_sites_iff {ρ : ResUT Loc Val WCactus.chain} {k : Kind} {d : List Loc} :
    ρ.Sites k d ↔ ResU.Sites (ρ.map ΦU) k d := by
  refine ⟨t_sites, fun h => ?_⟩
  have := p_sites h
  rwa [map_ΨU_ΦU] at this

theorem chain_dom_iff {ρ : ResUT Loc Val WCactus.chain} {d : List Loc} :
    ρ.Dom d ↔ ResU.Dom (ρ.map ΦU) d := by
  refine and_congr_right fun _ => forall_congr' fun l => iff_congr Iff.rfl ?_
  rw [PMap.map_get]
  constructor
  · rintro ⟨ψ, e⟩; exact ⟨ΦU ψ, by rw [e]; rfl⟩
  · rintro ⟨c, e⟩
    cases f : ρ.get l with
    | none => rw [f] at e; cases e
    | some ψ => exact ⟨ψ, rfl⟩

theorem chain_restrictOn (ρ : ResUT Loc Val WCactus.chain) (p : Kind → Bool) :
    (ρ.restrictOn p).map ΦU = ResU.restrictOn (ρ.map ΦU) p := by
  refine PMap.ext fun l => ?_
  show Option.map ΦU ((ρ.get l).bind _) = (Option.map ΦU (ρ.get l)).bind _
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.bind_some, Option.map_some, ΦU_kind]
      split <;> rfl

theorem chain_single (l : Loc) (ψ : CellUT Loc Val WCactus.chain) :
    (ResUT.single l ψ).map ΦU = ResU.single l (ΦU ψ) := by
  classical
  refine PMap.ext fun l' => ?_
  rw [PMap.map_get]
  show Option.map ΦU (if l' = l then some ψ else none) = if l' = l then some (ΦU ψ) else none
  split <;> rfl

theorem chain_del (ρ : ResUT Loc Val WCactus.chain) (l : Loc) :
    (ρ.del l).map ΦU = ResU.del (ρ.map ΦU) l := by
  classical
  refine PMap.ext fun l' => ?_
  rw [PMap.map_get]
  show Option.map ΦU (if l' = l then none else ρ.get l') =
    if l' = l then none else Option.map ΦU (ρ.get l')
  split <;> rfl

theorem chain_empty : (PMap.empty : ResUT Loc Val WCactus.chain).map ΦU = PMap.empty :=
  PMap.ext fun _ => rfl

theorem chain_le_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    ResUT.Le ρ σ ↔ ResU.Le (ρ.map ΦU) (σ.map ΦU) := by
  constructor
  · rintro ⟨τ, h⟩; exact ⟨τ.map ΦU, chain_resCompS_iff.mp h⟩
  · rintro ⟨τ, h⟩
    refine ⟨τ.map ΨU, chain_resCompS_iff.mpr ?_⟩
    rwa [map_ΦU_ΨU]

/-! ### Flattening at a location, strata -/

theorem chain_flatAt_iff {ρ : ResUT Loc Val WCactus.chain} {l : Loc}
    {ψ : CellUT Loc Val WCactus.chain} :
    ρ.FlatAt l ψ ↔ ResU.FlatAt (ρ.map ΦU) l (ΦU ψ) := by
  constructor
  · rintro ⟨σ, h, e⟩; exact ⟨σ.map ΦU, chain_flat_iff.mp h, map_ΦU_get.mpr e⟩
  · rintro ⟨σ, h, e⟩
    refine ⟨σ.map ΨU, chain_flat_iff.mpr (by rwa [map_ΦU_ΨU]), ?_⟩
    rw [← map_ΦU_get, map_ΦU_ΨU]; exact e

theorem chain_inStratum_iff {ρ : ResUT Loc Val WCactus.chain} {a : Life} :
    ρ.InStratum (TSet.single a) ↔ ResU.InStratum a (ρ.map ΦU) := by
  constructor
  · intro h l c e
    rw [map_ΦU_get_some] at e
    have := ΦU_inStratum_single_iff.mpr (h l _ e)
    rwa [ΦU_ΨU] at this
  · intro h l ψ e
    exact ΦU_inStratum_single_iff.mp (h l _ (map_ΦU_get.mpr e))

/-! ### `⟦−⟧` and `ℓ ↦ own(v)` -/

theorem ΦU_ownOf (v : Val) : ΦU (CellUT.ownOf (K := WCactus.chain) (Loc := Loc) v) = CellU.ownOf v :=
  rfl

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

end BoCa.Fig16.Tree

end
