import Core.TreeCactus
import Support.Model.Entailments

/-!
# Allocation and freeing at the step-indexed relation over the tree world  `[spec §62]`

`twp`'s rules for the two steps that change the memory's domain, over the tree carrier:

* **`alloc v`** (`twp_alloc`): the run continues from `Kc[loc ℓ]` with `ℓ ↦ own(v)` added to its
  resource, at every location `ℓ` the composite misses. The world gains the cell by
  `TWNT.alloc`; the store typing is not read (an `own` cell is covered at every code, `Cov.own`).
* **`free (loc ℓ)`** (`twp_free`): the run gives up `ℓ ↦ own(v)` and continues from `Kc[v]`;
  the world loses the cell by `TWNT.free`.

Both are `Support/TypedWorld/Wp.lean`'s `wpTS_alloc`/`wpTS_free` (rows 6.141, 6.142) read at `twp`:
the cell is beside the rest of the world (`flat_compS_ownT`), `⟦·⟧` gains or loses `ℓ ↦ v`
(`lower_compS_ownT`, `lower_compS_own_invT`), `↭` ignores `own` cells (`updX_compS_own`), and the
records' frame lifetimes read `ag`, which an `own` cell leaves unchanged (`taggedT_of_ag`).
Neither step is deterministic in the memory it leaves (`alloc` picks the location), so neither is
paid by the index: both read the postcondition downward closed (`TPost.Down`).

The tree helpers are `Support/Model/Entailments.lean`'s at the tree carrier, by the same proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont freeE)

variable {K : WCactus}

/-! ### An `own` cell beside a resource -/

/-- `⦇ρ ● ℓ↦own(v)⦈ = ⦇ρ⦈ ● ℓ↦own(v)` (`flat_compS_own` over the tree). -/
theorem flat_compS_ownT {ρ ρ' τ : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ') :
    ResUT.Flat ρ' τ ↔
      ∃ σ, ResUT.Flat ρ σ ∧ ResUT.CompS σ (ResUT.single l (CellUT.ownOf v)) τ := by
  constructor
  · intro hτ
    obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hcτ⟩ :=
      (ResUT.Flat.split hc).mp hτ
    cases ExST.functional he₂ (ExWT.single_own l v)
    cases AgWT.functional ha₂ (AgWT.single_own l v)
    cases ResUT.CompR.functional hac (ResUT.comp_empty_right a₁)
    obtain ⟨x, hx, hxτ⟩ :=
      (ResUT.CompS.assoc e₁ (ResUT.single l (CellUT.ownOf v)) a₁ τ).mpr ⟨e, hec, hcτ⟩
    obtain ⟨σ, hσ, hστ⟩ :=
      (ResUT.CompS.assoc e₁ a₁ (ResUT.single l (CellUT.ownOf v)) τ).mp
        ⟨x, ResUT.CompS.comm hx, hxτ⟩
    exact ⟨σ, ⟨e₁, a₁, he₁, ha₁, hσ⟩, hστ⟩
  · rintro ⟨σ, ⟨e₁, a₁, he₁, ha₁, hσ⟩, hστ⟩
    obtain ⟨x, hx, hxτ⟩ :=
      (ResUT.CompS.assoc e₁ a₁ (ResUT.single l (CellUT.ownOf v)) τ).mpr ⟨σ, hσ, hστ⟩
    obtain ⟨e, hec, hcτ⟩ :=
      (ResUT.CompS.assoc e₁ (ResUT.single l (CellUT.ownOf v)) a₁ τ).mp
        ⟨x, ResUT.CompS.comm hx, hxτ⟩
    exact (ResUT.Flat.split hc).mpr
      ⟨e₁, _, e, a₁, PMap.empty, a₁, he₁, ExWT.single_own l v, hec, ha₁,
        AgWT.single_own l v, ResUT.comp_empty_right a₁, hcτ⟩

/-- A location `⦇ρ⦈` misses is a location `ρ` misses. -/
theorem get_eq_none_of_flatT {ρ τ : TRes K} {l : BoCa.Loc} (hτ : ResUT.Flat ρ τ)
    (hl : τ.get l = none) : ρ.get l = none := by
  cases f : ρ.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨χ, hχ, -⟩ := hτ.get f
      exact absurd (hχ.symm.trans hl) (by simp)

/-- `ρ ▶◀ ℓ↦ψ` at a location `ρ` misses. -/
theorem compatS_single_of_get_noneT {ρ : TRes K} {l : BoCa.Loc} {ψ : TCell K}
    (hl : ρ.get l = none) : ResUT.CompatS ρ (ResUT.single l ψ) := by
  classical
  refine ResUT.Compat.of_disjoint fun k => ?_
  by_cases e : k = l
  · exact Or.inl (e ▸ hl)
  · exact Or.inr (ResUT.single_get_ne _ e)

/-- `⟦ρ ● ℓ↦own(v)⟧ = ⟦ρ⟧ ⊎ ℓ↦v`, at a location the memory misses. -/
theorem lower_compS_ownT {ρ ρ' : TRes K} {μ : Heap} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ') (hμ : ResUT.Lower ρ μ)
    (hl : μ l = none) : ResUT.Lower ρ' (BoCa.BoLo.Heap.upd μ l v) := by
  classical
  obtain ⟨τ, hτ, hval⟩ := hμ
  have hτl : τ.get l = none := by
    have := hval l; rw [hl] at this
    revert this; cases τ.get l <;> simp
  obtain ⟨t, ht⟩ := (ResUT.compS_defined_iff τ (ResUT.single l (CellUT.ownOf v))).mpr
    (compatS_single_of_get_noneT hτl)
  refine ⟨t, (flat_compS_ownT hc).mpr ⟨τ, hτ, ht⟩, fun k => ?_⟩
  by_cases e : k = l
  · subst e
    rw [ResUT.Comp.get_of_left_none ht hτl, ResUT.single_get_self]
    simp [BoCa.BoLo.Heap.upd, CellUT.ownOf, CellUT.erase]
  · rw [ResUT.Comp.get_of_right_none ht (ResUT.single_get_ne _ e),
      BoCa.BoLo.Heap.upd_other e]
    exact hval k

/-- `⟦ρ ● ℓ↦own(v)⟧ = ⟦ρ⟧ ⊎ ℓ↦v`, read the other way. -/
theorem lower_compS_own_invT {ρ ρ' : TRes K} {μ' : Heap} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ') (hμ : ResUT.Lower ρ' μ') :
    μ' l = some v ∧
      ∃ μ, ResUT.Lower ρ μ ∧ μ' = BoCa.BoLo.Heap.upd μ l v ∧ μ l = none := by
  classical
  obtain ⟨t, ht, hval⟩ := hμ
  obtain ⟨τ, hτ, hστ⟩ := (flat_compS_ownT hc).mp ht
  have hτl : τ.get l = none :=
    ResUT.compatS_single_own (ResUT.CompatS.symm hστ.1)
  have hvl : t.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hστ hτl, ResUT.single_get_self]
  refine ⟨by rw [hval l, hvl]; rfl,
    fun k => (τ.get k).map CellUT.erase, ⟨τ, hτ, fun _ => rfl⟩, ?_, by simp [hτl]⟩
  funext k
  by_cases e : k = l
  · subst e
    rw [hval k, hvl, BoCa.BoLo.Heap.upd_same]
    rfl
  · rw [hval k, BoCa.BoLo.Heap.upd_other e,
      ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ e)]

/-- **`↭` ignores `own` cells**: `ρ ↭ ρ ● ℓ↦own(v)` at every mask, across no re-reading. -/
theorem updX_compS_own {Θ : LocTy} {E : BoCa.Loc → Prop} {ρ ρ' : TRes K} {l : BoCa.Loc}
    {v : BoCa.Val} (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ')
    (hv : ResUT.Valid ρ) (hv' : ResUT.Valid ρ') (hcov : CovR Θ K ρ) :
    UpdX Θ E E ρ ρ' := by
  classical
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨t, ht⟩ := hv'
  obtain ⟨τ', hτ', hστ⟩ := (flat_compS_ownT hc).mp ht
  cases ResUT.Flat.functional hτ' hτ
  have hτl : τ.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hστ.1)
  have hget : ∀ k, k ≠ l → t.get k = τ.get k := fun k e =>
    ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ e)
  have hgetl : t.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hστ hτl, ResUT.single_get_self]
  -- `↭` of `ρ` with itself, read at the flattening `τ`
  obtain ⟨τ₁, τ₂, h₁, h₂, hx⟩ := UpdX.of_rr (Θ := Θ) (WCactus.Ext.refl K) E ⟨τ, hτ⟩ (RR.refl hcov)
  obtain rfl := ResUT.Flat.functional hτ h₁
  obtain rfl := ResUT.Flat.functional hτ h₂
  refine ⟨τ, t, hτ, ht, fun k => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · by_cases ek : k = l
    · subst ek; rw [hτl] at e; cases e
    · rw [hget k ek]; exact (hx k).1 ψ e hk hE
  · by_cases ek : k = l
    · subst ek; rw [hgetl] at e; cases e; exact absurd rfl hk
    · rw [hget k ek] at e; exact (hx k).2 ψ' e hk hE

/-- `ρ ● ℓ↦own(v) ↭ ρ`: the free direction of `updX_compS_own`. -/
theorem updX_compS_own_back {Θ : LocTy} {E : BoCa.Loc → Prop} {ρ ρ' : TRes K} {l : BoCa.Loc}
    {v : BoCa.Val} (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ')
    (hv : ResUT.Valid ρ) (hv' : ResUT.Valid ρ') (hcov : CovR Θ K ρ) :
    UpdX Θ E E ρ' ρ := by
  classical
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨t, ht⟩ := hv'
  obtain ⟨τ', hτ', hστ⟩ := (flat_compS_ownT hc).mp ht
  cases ResUT.Flat.functional hτ' hτ
  have hτl : τ.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hστ.1)
  have hget : ∀ k, k ≠ l → t.get k = τ.get k := fun k e =>
    ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ e)
  have hgetl : t.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hστ hτl, ResUT.single_get_self]
  obtain ⟨τ₁, τ₂, h₁, h₂, hx⟩ := UpdX.of_rr (Θ := Θ) (WCactus.Ext.refl K) E ⟨τ, hτ⟩ (RR.refl hcov)
  obtain rfl := ResUT.Flat.functional hτ h₁
  obtain rfl := ResUT.Flat.functional hτ h₂
  refine ⟨t, τ, ht, hτ, fun k => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · by_cases ek : k = l
    · subst ek; rw [hgetl] at e; cases e; exact absurd rfl hk
    · rw [hget k ek] at e; exact (hx k).1 ψ e hk hE
  · by_cases ek : k = l
    · subst ek; rw [hτl] at e; cases e
    · rw [hget k ek]; exact (hx k).2 ψ' e hk hE

/-- An `own` cell split off a resource leaves the resource without its location. -/
theorem eq_del_of_compS_single {ρ ρ₂ : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ₂ ρ) : ρ₂ = ρ.del l := by
  classical
  refine PMap.ext fun x => ?_
  by_cases ex : x = l
  · subst ex
    rw [ResUT.del_get_self]
    exact ResUT.compatS_single_own hc.1
  · rw [ResUT.del_get_ne _ ex, ResUT.Comp.get_of_left_none hc (ResUT.single_get_ne _ ex)]

/-- A resource with an `own` cell at `ℓ` is that cell beside the rest. -/
theorem compS_single_del {ρ : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (e : ρ.get l = some (CellUT.ownOf v)) :
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) (ρ.del l) ρ := by
  classical
  refine ⟨ResUT.Compat.of_disjoint fun x => ?_, fun x => ?_⟩
  · by_cases ex : x = l
    · exact Or.inr (ex ▸ ResUT.del_get_self ρ l)
    · exact Or.inl (ResUT.single_get_ne _ ex)
  · by_cases ex : x = l
    · subst ex
      rw [ResUT.single_get_self, ResUT.del_get_self, e]; rfl
    · rw [ResUT.single_get_ne _ ex, ResUT.del_get_ne _ ex]
      cases ρ.get x <;> rfl

/-- An `own` cell at a location the world misses keeps the world covered. -/
theorem covR_compS_own {Θ : LocTy} {ρ ρ' : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ') (h : CovR Θ K ρ) :
    CovR Θ K ρ' := by
  classical
  intro m ψ e
  by_cases em : m = l
  · subst em
    have hl : ρ.get m = none := ResUT.compatS_single_own (ResUT.CompatS.symm hc.1)
    rw [ResUT.Comp.get_of_left_none hc hl, ResUT.single_get_self] at e
    cases e; exact Cov.own _ _
  · rw [ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ em)] at e
    exact h m ψ e

/-- `ag(W ● ℓ ↦ own(v)) = ag(W)`. -/
theorem alloc_agT {W W' a' : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hW : ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W') (ha' : AgWT W' a') : AgWT W a' := by
  obtain ⟨σw, σo, hw, ho, hc⟩ := (AgWT.split hW).mp ha'
  rw [AgWT.functional ho (AgWT.single_own l v)] at hc
  rw [ResUT.CompR.functional hc (ResUT.comp_empty_right σw)]
  exact hw

/-- The records' frame lifetimes read `ag(W)` only. -/
theorem taggedT_of_ag {W W' : TRes K} {ps : List (FrameRecT K)} {ls : List (SRecT K)}
    (t : ∀ a, AgWT W' a → AgWT W a) (h : TaggedT K W ps ls) : TaggedT K W' ps ls := by
  intro x hx
  obtain ⟨p, hp, hd, hf₁, hf₂⟩ := h x hx
  exact ⟨p, hp, hd, fun a ha => hf₁ a (t a ha), fun a ha => hf₂ a (t a ha)⟩

/-- A memory with finitely many cells misses a location. -/
theorem exists_fresh_heap {μ : Heap} (h : FinDom μ) : ∃ l, μ l = none := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨l, hl⟩ := loc_infinite d
  exact ⟨l, by by_contra hne; exact hl (hd l hne)⟩

/-! ### The rules -/

/-- **Allocation at `twp`** (row 6.141): at every extension the run starts at and every location
the world misses, the run continues from `Kc[loc ℓ]` with `ℓ ↦ own(v)` beside its resource. -/
theorem twp_alloc {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (v : BoCa.Val) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      ∀ (l : BoCa.Loc) (ρ₁ : TRes w₀.K), ResUT.CompS ρ₀ (ResUT.single l (CellUT.ownOf v)) ρ₁ →
        twp (ℍ := ℍ) F Q n w₀ ls₀ O₀ (Kc.plug (.val (.loc l))) ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ _ hc hS hR hI hfd j μ' e' hj hrun hfin
  cases hrun with
  | refl =>
      obtain ⟨l, hμl⟩ := exists_fresh_heap hfd
      exact absurd ((step1_alloc_iff Kc v).2 ⟨l, hμl, rfl, rfl⟩) (hfin _ _)
  | @more j' _ μ₁ _ _ e₁ _ hs t =>
  obtain ⟨l, hμl, rfl, rfl⟩ := (step1_alloc_iff Kc v).1 hs
  obtain ⟨σ, hσ, hval⟩ := hI.2
  have hσl : σ.get l = none := by
    have := hval l; rw [hμl] at this
    revert this; cases σ.get l <;> simp
  have hfl : fρ.get l = none := get_eq_none_of_flatT hσ hσl
  obtain ⟨fρ₁, hfρ₁⟩ := (ResUT.compS_defined_iff fρ (ResUT.single l (CellUT.ownOf v))).mpr
    (compatS_single_of_get_noneT hfl)
  obtain ⟨ρ₁, hρ₁, hfρ₁'⟩ :=
    (ResUT.CompS.assoc ρf ρ₀ (ResUT.single l (CellUT.ownOf v)) fρ₁).mpr ⟨fρ, hc, hfρ₁⟩
  have hlow : ResUT.Lower fρ₁ (BoCa.BoLo.Heap.upd μ l v) := lower_compS_ownT hfρ₁ hI.2 hμl
  have hv₁ : ResUT.Valid fρ₁ := by obtain ⟨τ, hτ, -⟩ := hlow; exact ⟨τ, hτ⟩
  have hI₁ : WInv w₀ fρ₁ (BoCa.BoLo.Heap.upd μ l v) := ⟨covR_compS_own hfρ₁ hI.1, hlow⟩
  have hR₁ : RecInv w₀ fρ₁ ps ls₀ :=
    ⟨TWNT.alloc hR.1 hI.2 hμl hfρ₁ hv₁, taggedT_of_ag (fun a ha => alloc_agT hfρ₁ ha) hR.2⟩
  have hcov₀ : CovR (sem w₀.Θ) w₀.K ρ₀ := cov_of_comp hc hI
  have hcov₁ : CovR (sem w₀.Θ) w₀.K ρ₁ := cov_of_comp hfρ₁' hI₁
  have hu : UpdX (sem w₀.Θ) (recMask O₀) (recMask O₀) ρ₀ ρ₁ :=
    updX_compS_own hρ₁ (cov_valid hc hI) (cov_valid hfρ₁' hI₁) hcov₀
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w₀ ρ₀ ls₀ O₀ hE hr hl hO l ρ₁ hρ₁ w₀ ρ₁ ρf fρ₁ ls₀ O₀ ps psF _ (TWd.Ext.refl _ _)
      (RR.refl hcov₁) (SRecsRR.refl hR₁.cov_ls)
      (RecsRR.refl fun r hr' => hR₁.cov_ps r (hS.left r hr')) hFρ (hash_of_inv hfρ₁' hI₁) hfρ₁'
      hS hR₁ hI₁ (finDom_upd hfd l v) j' μ' e' (by omega) t hfin
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇,
    hQ.le (by omega) _ _ _ _ _ g₈, UpdX.trans g₀.1 hu g₉, g₁₀,
    (InvKept.refl _ _ _).trans hu g₁₁⟩

/-- **Free at `twp`** (row 6.142): the run gives up `ℓ ↦ own(v)` and continues from `Kc[v]`. -/
theorem twp_free {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (l : BoCa.Loc)
    (v : BoCa.Val) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ ρ₂ : TRes w.K} (hcρ : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ₂ ρ)
    (h : twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.val v)) ρ₂) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (freeE (.val (.loc l)))) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ _ hc hS hR hI hfd j μ' e' hj hrun hfin
  have hρl : ρ.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_right_none hcρ (ResUT.compatS_single_own hcρ.1),
      ResUT.single_get_self]
  obtain rfl := eq_del_of_compS_single hcρ
  have hc₀ := compS_single_del (RR.own_fwd hr hρl)
  have h₂₀ : RRw (w := w) (w' := w₀) (ρ.del l) (ρ₀.del l) := RR.del hr l
  set ρ₂₀ := ρ₀.del l
  replace hc₀ : ResUT.CompS ρ₂₀ (ResUT.single l (CellUT.ownOf v)) ρ₀ := ResUT.CompS.comm hc₀
  -- `fρ = (ρf ● ρ₂₀) ● ℓ ↦ own(v)`
  obtain ⟨fρ₂, hfρ₂, hfρ₂'⟩ :=
    (ResUT.CompS.assoc ρf ρ₂₀ (ResUT.single l (CellUT.ownOf v)) fρ).mp
      ⟨ρ₀, hc₀, hc⟩
  obtain ⟨hμl, μ₂, hlow₂, rfl, hμ₂l⟩ := lower_compS_own_invT hfρ₂' hI.2
  have hdel : BoCa.BoLo.Heap.del (BoCa.BoLo.Heap.upd μ₂ l v) l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hμ₂l]
    · rw [BoCa.BoLo.Heap.del_other e, BoCa.BoLo.Heap.upd_other e]
  have hv₂ : ResUT.Valid fρ₂ := by obtain ⟨τ, hτ, -⟩ := hlow₂; exact ⟨τ, hτ⟩
  have hI₂ : WInv w₀ fρ₂ μ₂ := ⟨CovR.of_compS_left hfρ₂' hI.1, hlow₂⟩
  have hR₂ : RecInv w₀ fρ₂ ps ls₀ :=
    ⟨TWNT.free hR.1 (ResUT.CompS.comm hfρ₂') hv₂,
      taggedT_of_ag (fun a ha => (own_cell_ag (ResUT.CompS.comm hfρ₂') a).mpr ha) hR.2⟩
  cases hrun with
  | refl =>
      exact absurd ((step1_free_iff Kc l).2 ⟨v, hμl, rfl, rfl⟩) (hfin _ _)
  | @more j' _ μ₁ _ _ e₁ _ hs t =>
  obtain ⟨u, hu', rfl, rfl⟩ := (step1_free_iff Kc l).1 hs
  rw [hμl] at hu'; cases hu'
  rw [hdel] at t
  have hcov₂ : CovR (sem w₀.Θ) w₀.K ρ₂₀ := cov_of_comp hfρ₂ hI₂
  have hu : UpdX (sem w₀.Θ) (recMask O₀) (recMask O₀) ρ₀ ρ₂₀ :=
    updX_compS_own_back hc₀ (cov_valid hfρ₂ hI₂) (cov_valid hc hI) hcov₂
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w₀ ρ₂₀ ρf fρ₂ ls₀ O₀ ps psF μ₂ (hE.of_compS_right hcρ) h₂₀ hl hO hFρ
      (hash_of_inv hfρ₂ hI₂) hfρ₂ hS hR₂ hI₂ (by rw [← hdel]; exact finDom_del hfd l) j' μ' e'
      (by omega) t hfin
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇,
    hQ.le (by omega) _ _ _ _ _ g₈, UpdX.trans g₀.1 hu g₉, g₁₀,
    (InvKept.refl _ _ _).trans hu g₁₁⟩

/-- An `own` cell holds no `mut` cell. -/
theorem not_holdsMut_own {K : WCactus} {l l' : BoCa.Loc} {v : BoCa.Val} :
    ¬ HoldsMut (ResUT.single l' (CellUT.ownOf (K := K) v)) l := by
  intro h
  cases h with
  | top e => obtain ⟨-, h⟩ := ResUT.single_get_eq_some e; cases h
  | deep e h =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      cases h with
      | top e' => simp [CellUT.ownOf, CellUT.wit] at e'
      | deep e' _ => simp [CellUT.ownOf, CellUT.wit] at e'

/-- A `mut` cell a composite with an `own` cell holds is held by the other part. -/
theorem holdsMut_of_compS_own {K : WCactus} {a y : TRes K} {l' : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS a (ResUT.single l' (CellUT.ownOf v)) y) {l : BoCa.Loc}
    (h : HoldsMut y l) : HoldsMut a l := by
  classical
  have hal : a.get l' = none := ResUT.compatS_single_own (ResUT.CompatS.symm hc.1)
  have hyl : y.get l' = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hc hal, ResUT.single_get_self]
  cases h with
  | @top _ _ m e =>
      by_cases hk : l = l'
      · subst hk; rw [hyl] at e; cases e
      · rw [ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ hk)] at e
        exact .top e
  | @deep _ k _ ψ e h =>
      by_cases hk : k = l'
      · subst hk; rw [hyl] at e; cases e
        cases h with
        | top e' => simp [CellUT.ownOf, CellUT.wit] at e'
        | deep e' _ => simp [CellUT.ownOf, CellUT.wit] at e'
      · rw [ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ hk)] at e
        exact .deep e h


/-! ### Load and store at an `own` cell -/

/-- A load's head steps: the memory's value at the location. -/
theorem head_load_inv {μ μ' : Heap} {ℓ : BoCa.Loc} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .load)) (.val (Val.loc ℓ))) μ' a') :
    ∃ u, μ ℓ = some u ∧ μ' = μ ∧ a' = .val u := by
  generalize hb : Expr.app (.val (.prim .load)) (.val (Val.loc ℓ)) = b at h
  cases h with
  | load k u hk =>
      simp only [Expr.val, Val.prim, Val.loc, Expr.app.injEq, Expr.loc.injEq, true_and] at hb
      subst hb
      exact ⟨u, hk, rfl, rfl⟩
  | _ => simp_all [BoCa.BoLo.hndE, BoCa.BoLo.ubindE, BoCa.BoLo.ccatchE, BoCa.BoLo.cfinE, Expr.val, Val.prim]

theorem step1_load_iff {μ μ₁ : Heap} {e₁ : Expr} (K : Kont) (ℓ : BoCa.Loc) :
    Step1 (ℍ := ℍ) μ (K.plug (.app (.val (.prim .load)) (.val (Val.loc ℓ)))) μ₁ e₁ ↔
      ∃ u, μ ℓ = some u ∧ μ₁ = μ ∧ e₁ = K.plug (.val u) := by
  constructor
  · rintro ⟨K', b, b', he, rfl, hb⟩
    obtain ⟨rfl, rfl⟩ := plug_decomp hb K K'
      (Head.load (ℍ := ℍ) (fun _ => some Val.unit) ℓ Val.unit rfl) he
    obtain ⟨u, hu, rfl, rfl⟩ := head_load_inv hb
    exact ⟨u, hu, rfl, rfl⟩
  · rintro ⟨u, hu, rfl, rfl⟩
    exact ⟨K, _, _, rfl, rfl, Head.load _ ℓ u hu⟩

/-- A store's head steps: the location held, overwritten. -/
theorem head_store_inv {μ μ' : Heap} {ℓ : BoCa.Loc} {v : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.app (.val (.prim .store)) (.val (Val.loc ℓ))) (.val v)) μ' a') :
    (∃ u, μ ℓ = some u) ∧ μ' = μ.upd ℓ v ∧ a' = .val .unit := by
  generalize hb : Expr.app (.app (.val (.prim .store)) (.val (Val.loc ℓ))) (.val v) = b at h
  cases h with
  | store k u w hk =>
      simp only [Expr.val, Val.prim, Val.loc, Expr.app.injEq, Expr.loc.injEq, true_and] at hb
      obtain ⟨rfl, hv⟩ := hb
      obtain rfl : v = u := Subtype.ext hv
      exact ⟨⟨w, hk⟩, rfl, rfl⟩
  | _ => simp_all [BoCa.BoLo.hndE, BoCa.BoLo.ubindE, BoCa.BoLo.ccatchE, BoCa.BoLo.cfinE, Expr.val, Val.prim]

theorem step1_store_iff {μ μ₁ : Heap} {e₁ : Expr} (K : Kont) (ℓ : BoCa.Loc) (v : Val) :
    Step1 (ℍ := ℍ) μ (K.plug (.app (.app (.val (.prim .store)) (.val (Val.loc ℓ))) (.val v)))
      μ₁ e₁ ↔ (∃ u, μ ℓ = some u) ∧ μ₁ = μ.upd ℓ v ∧ e₁ = K.plug (.val .unit) := by
  constructor
  · rintro ⟨K', b, b', he, rfl, hb⟩
    obtain ⟨rfl, rfl⟩ := plug_decomp hb K K'
      (Head.store (ℍ := ℍ) (fun _ => some Val.unit) ℓ v Val.unit rfl) he
    obtain ⟨hu, rfl, rfl⟩ := head_store_inv hb
    exact ⟨hu, rfl, rfl⟩
  · rintro ⟨⟨u, hu⟩, rfl, rfl⟩
    exact ⟨K, _, _, rfl, rfl, Head.store μ ℓ v u hu⟩

/-- An `own` cell excludes every other cell at its location. -/
theorem get_eq_none_of_compatS_ownT {ρ σ : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (h : ResUT.CompatS σ ρ) (e : ρ.get l = some (CellUT.ownOf v)) : σ.get l = none := by
  cases f : σ.get l with
  | none => rfl
  | some χ => exact absurd (CellUT.CompatS.kinds (h l χ _ f e)).2 (by simp [CellUT.ownOf, CellUT.kind])

/-- A location owned in `ρ` reads its value in every memory `ρ` lowers to. -/
theorem lower_get_ownT {ρ : TRes K} {μ : Heap} {l : BoCa.Loc} {v : BoCa.Val}
    (h : ResUT.Lower ρ μ) (e : ρ.get l = some (CellUT.ownOf v)) : μ l = some v := by
  obtain ⟨τ, hτ, hval⟩ := h
  obtain ⟨χ, hχ, -, hv, -⟩ := hτ.get e
  rw [hval l, hχ]
  exact congrArg some hv

/-- **Load at `twp`** (row 6.143): an `own` cell of the run's resource is read; nothing changes. -/
theorem twp_load {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (l : BoCa.Loc)
    (v : BoCa.Val) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ : TRes w.K} (hρ : ρ.get l = some (CellUT.ownOf v))
    (h : twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.val v)) ρ) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (.val (.prim .load)) (.val (.loc l)))) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI hfd j μ' e' hj hrun hfin
  have hρ₀ := RR.own_fwd hr hρ
  have hfl : fρ.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hc (get_eq_none_of_compatS_ownT hc.1 hρ₀), hρ₀]
  have hμl : μ l = some v := lower_get_ownT hI.2 hfl
  cases hrun with
  | refl => exact absurd ((step1_load_iff Kc l).2 ⟨v, hμl, rfl, rfl⟩) (hfin _ _)
  | @more j' _ μ₁ _ _ e₁ _ hs t =>
  obtain ⟨u, hu, rfl, rfl⟩ := (step1_load_iff Kc l).1 hs
  rw [hμl] at hu; cases hu
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF _ hE hr hl hO hFρ hf hc hS hR hI hfd j' μ' e'
      (by omega) t hfin
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇,
    hQ.le (by omega) _ _ _ _ _ g₈, g₉, g₁₀, g₁₁⟩

/-- **Store at `twp`** (row 6.145): an `own` cell of the run's resource is overwritten. -/
theorem twp_store {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (l : BoCa.Loc)
    (v₁ v₂ : BoCa.Val) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ ρ₂ ρ' : TRes w.K} (hcρ : ResUT.CompS (ResUT.single l (CellUT.ownOf v₁)) ρ₂ ρ)
    (hcρ' : ResUT.CompS (ResUT.single l (CellUT.ownOf v₂)) ρ₂ ρ')
    (h : twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.val .unit)) ρ') :
    twp (ℍ := ℍ) F Q n w ls O
      (Kc.plug (.app (.app (.val (.prim .store)) (.val (.loc l))) (.val v₂))) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ _ hc hS hR hI hfd j μ' e' hj hrun hfin
  have hρl : ρ.get l = some (CellUT.ownOf v₁) := by
    rw [ResUT.Comp.get_of_right_none hcρ (ResUT.compatS_single_own hcρ.1),
      ResUT.single_get_self]
  obtain rfl := eq_del_of_compS_single hcρ
  have hρ₀l := RR.own_fwd hr hρl
  have hc₀ := ResUT.CompS.comm (compS_single_del hρ₀l)
  have h₂₀ : RRw (w := w) (w' := w₀) (ρ.del l) (ρ₀.del l) := RR.del hr l
  have hcov₀ : CovR (sem w₀.Θ) w₀.K ρ₀ := cov_of_comp hc hI
  -- `fρ = (ρf ● ρ₂₀) ● ℓ ↦ own(v₁)`
  obtain ⟨Z, hZ, hZf⟩ :=
    (ResUT.CompS.assoc ρf (ρ₀.del l) (ResUT.single l (CellUT.ownOf v₁)) fρ).mp ⟨ρ₀, hc₀, hc⟩
  obtain ⟨hμl, μZ, hlowZ, rfl, hμZl⟩ := lower_compS_own_invT hZf hI.2
  have hZl : Z.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hZf.1)
  obtain ⟨fρ', hfρ'⟩ := (ResUT.compS_defined_iff Z (ResUT.single l (CellUT.ownOf v₂))).mpr
    (compatS_single_of_get_noneT hZl)
  have hlow' : ResUT.Lower fρ' (BoCa.BoLo.Heap.upd μZ l v₂) := lower_compS_ownT hfρ' hlowZ hμZl
  have hupd : BoCa.BoLo.Heap.upd (BoCa.BoLo.Heap.upd μZ l v₁) l v₂ = BoCa.BoLo.Heap.upd μZ l v₂ := by
    funext k; by_cases e : k = l
    · subst e; simp
    · simp [BoCa.BoLo.Heap.upd_other e]
  have hv' : ResUT.Valid fρ' := by obtain ⟨τ, hτ, -⟩ := hlow'; exact ⟨τ, hτ⟩
  have hI' : WInv w₀ fρ' (BoCa.BoLo.Heap.upd μZ l v₂) :=
    ⟨covR_compS_own hfρ' (CovR.of_compS_left hZf hI.1), hlow'⟩
  have hR' : RecInv w₀ fρ' ps ls₀ :=
    ⟨TWNT.store hR.1 (ResUT.CompS.comm hZf) (ResUT.CompS.comm hfρ') hv',
      taggedT_of_ag (fun a ha => (own_cell_ag (ResUT.CompS.comm hZf) a).mpr
        ((own_cell_ag (ResUT.CompS.comm hfρ') a).mp ha)) hR.2⟩
  -- the run's new resource `ρ₀′ = ρ₂₀ ● ℓ ↦ own(v₂)`, beside the frame
  obtain ⟨ρ₀', hρ₀', hfρ₀'⟩ :=
    (ResUT.CompS.assoc ρf (ρ₀.del l) (ResUT.single l (CellUT.ownOf v₂)) fρ').mpr ⟨Z, hZ, hfρ'⟩
  have hrs : RR (sem w₀.Θ) (ResUT.single l (CellUT.ownOf (K := w.K) v₂))
      (ResUT.single l (CellUT.ownOf (K := w₀.K) v₂)) := by
    refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
    · by_cases hm : m = l
      · subst hm; simp
      · simp only [ResUT.single_get_ne _ hm]
    · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
      exact RC.own _ _
  obtain ⟨ρx, hcx, hrx⟩ := RR.compS h₂₀ hrs (ResUT.CompS.comm hcρ')
  obtain rfl := ResUT.CompS.functional hcx hρ₀'
  have hE' : w.Ext w₀ ρ' := ⟨hE.1, fun m hm => (hE.of_compS_right hcρ).2 m
    (holdsMut_of_compS_own (ResUT.CompS.comm hcρ') hm)⟩
  have hcov₂ : CovR (sem w₀.Θ) w₀.K (ρ₀.del l) := CovR.of_compS_left hc₀ hcov₀
  have hu : UpdX (sem w₀.Θ) (recMask O₀) (recMask O₀) ρ₀ ρx :=
    UpdX.trans (WCactus.Ext.refl _)
      (updX_compS_own_back hc₀ (cov_valid hZ ⟨CovR.of_compS_left hZf hI.1, hlowZ⟩)
        (cov_valid hc hI) hcov₂)
      (updX_compS_own hρ₀' (cov_valid hZ ⟨CovR.of_compS_left hZf hI.1, hlowZ⟩)
        (cov_valid hfρ₀' hI') hcov₂)
  cases hrun with
  | refl =>
      exact absurd ((step1_store_iff Kc l v₂).2 ⟨⟨v₁, hμl⟩, rfl, rfl⟩) (hfin _ _)
  | @more j' _ μ₁ _ _ e₁ _ hs t =>
  obtain ⟨-, rfl, rfl⟩ := (step1_store_iff Kc l v₂).1 hs
  rw [hupd] at t
  obtain ⟨w', ρf', ρ'', fρ'', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w₀ ρx ρf fρ' ls₀ O₀ ps psF _ hE' hrx hl hO hFρ (hash_of_inv hfρ₀' hI') hfρ₀' hS hR' hI'
      (by rw [← hupd]; exact finDom_upd hfd l v₂) j' μ' e' (by omega) t hfin
  exact ⟨w', ρf', ρ'', fρ'', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇,
    hQ.le (by omega) _ _ _ _ _ g₈, UpdX.trans g₀.1 hu g₉, g₁₀,
    (InvKept.refl _ _ _).trans hu g₁₁⟩

end BoCa.Fig16.Tree.Wp

end
