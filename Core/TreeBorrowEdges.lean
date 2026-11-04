import Core.TreeSchedPool
import Core.TreeLend

/-!
# Borrow edges point to ancestors: configurations at depth 1 and depth 3  `[spec §62]`

`lender_ancestor` (`Core/TreeSchedPool.lean`) reads `CactusInvT` only. This file builds
`CactusInvT` configurations meeting every premise, from the empty world through `TWNT`'s own
constructors, the second branch added by hand (`cactusT_spawn`). They are not reached by a
scheduler: nothing connects them to `PoolT` or to a stored `κ` (open, #789).

* **a lend opened at the world** (`recWInv_lendStep`): a fresh `ℓ ↦ own(())` allocated
  (`TWNT.alloc`), then lent `imm` at any `α` with the empty escrow (`TWNT.immFrame`, the record
  `lendRec ℓ` tagged `α`). It is `twp_lendOpen`'s update read at the world, with no run around it;
* **depth 1** (`lenderEdge_depth1`): one lend at `α₁`; a second branch at `α₁` holds its view;
* **depth 3** (`lenderEdge_depth3`): three lends nested `α₃ ⊏ α₂ ⊏ α₁` on the chain tree
  `chainP`, each record owned by the running branch; a second branch at `α₃`, two lends inside the
  outermost, holds the outermost lend's view. `lender_ancestor` puts its lender `α₁` above it,
  strictly and two levels up.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap)

/-! ### A lend opened at the world -/

/-- **An allocation keeps the world's invariants**: a fresh `ℓ ↦ own(())` beside the world. -/
theorem recWInv_alloc {w : TWd} {W W' : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {l : BoCa.Loc}
    (hR : RecInv w W ps ls) (hI : WInv w W μ) (hl : μ l = none)
    (hW : ResUT.CompS W (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) W') :
    RecInv w W' ps ls ∧ WInv w W' (BoCa.BoLo.Heap.upd μ l BoCa.Val.unit) := by
  have hlo := lower_compS_ownT hW hI.2 hl
  obtain ⟨τ, hτ, -⟩ := id hlo
  exact ⟨⟨TWNT.alloc hR.1 hI.2 hl hW ⟨τ, hτ⟩, taggedT_of_ag (fun a ha => alloc_agT hW ha) hR.2⟩,
    covR_compS_own hW hI.1, hlo⟩

/-- **A lend opened at the world**: `ℓ ↦ own(())` beside `Y` becomes the lend cell
`ℓ ↦ imm({α}, (), ∅)` beside `Y`; the record `lendRec ℓ` joins the records proper, tagged `α`.
`twp_lendOpen`'s update, read at the world. -/
theorem recWInv_lend {w : TWd} {Y W W₁ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {l : BoCa.Loc} (α : Life)
    (hR : RecInv w W ps ls) (hI : WInv w W μ)
    (hYf : ResUT.CompS Y (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) W)
    (hY₁ : ResUT.CompS Y (viewRes α l) W₁) :
    RecInv w W₁ (lendRec l :: ps) ((lendRec l, α) :: ls) ∧ WInv w W₁ μ := by
  classical
  obtain ⟨τ, hτ⟩ := hI.valid
  obtain ⟨σ, hσ, hστ⟩ := (flat_compS_ownT hYf).mp hτ
  have hσl : σ.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hστ.1)
  obtain ⟨τ₁, hτ₁, hστ₁⟩ := flat_compS_view hY₁ hσ hσl
  have hv₁ : ResUT.Valid W₁ := ⟨τ₁, hτ₁⟩
  have hTW := hR.1
  have hTin : TWNT w.K w.Θ w.tc W₁ (lendRec l :: ps) (lendRec l :: ([] ++ rsOfT ls)) :=
    TWNT.immFrame (ds := []) KTy.unit (emptyT_inStratum _) hTW (ResUT.compS_empty_right _)
      (ResUT.CompS.comm hYf) ⟨rfl, rfl⟩ (ResUT.CompS.comm hY₁) hv₁
      (fun d => ⟨fun h => by simp at h, fun h => (emptyRec_no_desc l _ _ d h).elim⟩)
  have hpsl : ∀ q ∈ ps, q.le ≠ l := by
    intro q hq hql
    obtain ⟨a, ha⟩ := agW_of_valid ⟨τ, hτ⟩
    obtain ⟨ψ, eψ⟩ := leInv_view hTW hq a ha
    obtain ⟨eY, aY, -, haY, hσc⟩ := hσ
    have ea : aY = a := AgWT.functional haY (alloc_agT hYf ha)
    subst ea
    rw [hql, get_none_of_compS_right hσc hσl] at eψ
    cases eψ
  have hFLold : ∀ p ∈ ps, ∀ t, FrameLifeT w.K W p t → FrameLifeT w.K W₁ p t := by
    intro p hp t ⟨h₁, h₂⟩
    refine ⟨fun a₁ ha₁ ζ s eζ hs y hy => ?_, fun a₁ ha₁ m hm ψ s eψ hs y hy => ?_⟩
    · obtain ⟨a, ha, -, -, hm⟩ := ag_compS_view hY₁ hσ hσl ha₁
      exact h₁ a (ag_compS_own hYf ha) ζ s (by rw [← hm _ (hpsl p hp)]; exact eζ) hs y hy
    · obtain ⟨a, ha, -, -, hm'⟩ := ag_compS_view hY₁ hσ hσl ha₁
      by_cases hml : m = l
      · subst hml
        exact (le_not_linLoc hTin (List.mem_cons_of_mem _ hp) List.mem_cons_self hm).elim
      · exact h₂ a (ag_compS_own hYf ha) m hm ψ s (by rw [← hm' m hml]; exact eψ) hs y hy
  have hFLnew : FrameLifeT w.K W₁ (lendRec l) α := by
    refine ⟨fun a₁ ha₁ ζ s eζ hs y hy => ?_, fun a₁ _ m hm => (linLoc_lendRec hm).elim⟩
    obtain ⟨a, -, -, hl₁, -⟩ := ag_compS_view hY₁ hσ hσl ha₁
    have eζ' : a₁.get l = some ζ := eζ
    rw [hl₁] at eζ'
    cases eζ'
    simp only [viewCell, CellUT.lsOfI_immOf, Option.some.injEq] at hs
    subst hs
    simpa using hy
  have htg : TaggedT w.K W₁ (lendRec l :: ps) ((lendRec l, α) :: ls) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨lendRec l, List.mem_cons_self, DescRT.refl _, hFLnew⟩
    · obtain ⟨p, hp, hd, hf⟩ := hR.2 x hx
      exact ⟨p, List.mem_cons_of_mem _ hp, hd, hFLold p hp x.2 hf⟩
  have hcovY : CovR (sem w.Θ) w.K Y := CovR.of_compS_left hYf hI.1
  refine ⟨⟨hTin, htg⟩, fun m ψ e => ?_, ?_⟩
  · by_cases hm : m = l
    · subst hm
      rw [ResUT.Comp.get_of_left_none hY₁ (get_eq_none_of_flatT hσ hσl), viewRes,
        ResUT.single_get_self] at e
      cases e
      exact Cov.immOf_iff.mpr fun x ψ e => by simp at e
    · rw [ResUT.Comp.get_of_right_none hY₁ (ResUT.single_get_ne _ hm)] at e
      exact hcovY m ψ e
  · obtain ⟨τ', hτ', hval⟩ := hI.2
    obtain rfl := ResUT.Flat.functional hτ hτ'
    refine ⟨τ₁, hτ₁, fun x => ?_⟩
    rw [hval x]
    by_cases hx : x = l
    · subst hx
      rw [ResUT.Comp.get_of_left_none hστ hσl, ResUT.Comp.get_of_left_none hστ₁ hσl, viewRes,
        ResUT.single_get_self, ResUT.single_get_self]
      rfl
    · rw [ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ hx),
        ResUT.Comp.get_of_right_none hστ₁ (ResUT.single_get_ne _ hx)]

/-- **Allocate and lend at a location the memory misses**: the world grows by the lend cell at
`ℓ`, the records proper by `lendRec ℓ` tagged `α`, the memory by `ℓ ↦ ()`. -/
theorem recWInv_lendStep {w : TWd} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {l : BoCa.Loc} (α : Life)
    (hR : RecInv w W ps ls) (hI : WInv w W μ) (hl : μ l = none) :
    ∃ W₁ : TRes w.K, ResUT.CompS W (viewRes α l) W₁ ∧
      RecInv w W₁ (lendRec l :: ps) ((lendRec l, α) :: ls) ∧
      WInv w W₁ (BoCa.BoLo.Heap.upd μ l BoCa.Val.unit) := by
  obtain ⟨τ, hτ, hval⟩ := hI.2
  have hτl : τ.get l = none := by
    have := hval l; rw [hl] at this
    revert this; cases τ.get l <;> simp
  have hWl : W.get l = none := get_eq_none_of_flatT hτ hτl
  obtain ⟨W', hW'⟩ := (ResUT.compS_defined_iff W (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT hWl)
  obtain ⟨W₁, hW₁⟩ := (ResUT.compS_defined_iff W (viewRes α l)).mpr
    (compatS_single_of_get_noneT hWl)
  obtain ⟨hR', hI'⟩ := recWInv_alloc hR hI hl hW'
  obtain ⟨hR₁, hI₁⟩ := recWInv_lend α hR' hI' hW' hW₁
  exact ⟨W₁, hW₁, hR₁, hI₁.1, hI₁.2⟩

/-- The lend cell is on the branch of every point inside its lifetime. -/
theorem onBranch_view {K : WCactus} {n β : Life} (h : K.le n β) (m : BoCa.Loc) :
    OnBranchResT K n (viewRes β m) := by
  intro l ψ e s hs x hx
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  change some (TSet.single β) = some s at hs
  cases Option.some.inj hs
  simp only [TSet.single_set, Finset.mem_singleton] at hx
  subst hx; exact h

/-- The lender of `lendRec ℓ` in a world whose tagged list carries only lend records: the tag
`TaggedT` gives `ℓ`'s record is its own, at the tag's lifetime. -/
theorem frameLife_of_tag {w : TWd} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (hR : RecInv w W ps ls) {l : BoCa.Loc} {α : Life}
    (hx : (lendRec l, α) ∈ ls) (hps : ∀ p ∈ ps, ∃ k, p = lendRec k) :
    FrameLifeT w.K W (lendRec l) α := by
  obtain ⟨p, hp, hd, hf⟩ := hR.2 _ hx
  obtain ⟨k, rfl⟩ := hps p hp
  have e : lendRec l = lendRec k := descRT_lendRec hd
  rw [e]
  exact hf

/-! ### The chain tree -/

/-- The chain `⊤ = 0 ⊐ 1 ⊐ 2 ⊐ 3 ⊐ …`: each lifetime's parent is its predecessor. -/
def chainP : ParentFn where
  par n := n - 1
  rank n := n
  par_zero := rfl
  rank_lt n hn := by show n - 1 < n; omega

theorem chainP_inAlloc : chainP.InAlloc := fun n hn => by show n - 1 < n; omega

/-- The world on the chain tree, with the empty store typing. -/
abbrev wE : TWd := ⟨chainP, fun _ => none, tmplT _ (fun _ => none)⟩

/-- The lifetime `k` of the chain. -/
abbrev lfE (k : Nat) : Life := OrderDual.toDual k

theorem chain_le {a b : Nat} (h : b ≤ a) : wE.K.le (lfE a) (lfE b) := by
  change chainP.Anc a b
  induction a with
  | zero => obtain rfl : b = 0 := by omega
            exact .refl 0
  | succ a ih =>
      by_cases e : b = a + 1
      · subst e; exact .refl _
      · exact .up (ih (by omega))

theorem chain_not_le {a b : Nat} (h : a < b) : ¬ wE.K.le (lfE a) (lfE b) := fun h' => by
  have := ParentFn.Anc.le chainP_inAlloc (show chainP.Anc a b from h')
  omega

theorem lfE_ne {a b : Nat} (h : a ≠ b) : lfE a ≠ lfE b := fun e =>
  h (OrderDual.toDual.injective e)

/-! ### Depth 1 -/

/-- **Depth 1**: one lend of `ℓ = 1` at `α₁ = 1`; the running branch owns its record, a second
branch at `α₁` holds the lend's view. Every premise of `lender_ancestor` holds. -/
theorem lenderEdge_depth1 :
    ∃ (W : TRes wE.K) (μ : Heap),
      CactusInvT wE [(PMap.empty, [lendRec 1]), (viewRes (lfE 1) 1, [])] [lfE 1, lfE 1] W
        [lendRec 1] [(lendRec 1, lfE 1)] μ ∧
      FrameLifeT wE.K W (lendRec 1) (lfE 1) ∧ wE.K.le (lfE 1) (lfE 1) := by
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  have hv : ResUT.CompS PMap.empty (viewRes (lfE 1) 1) W₁ := hW₁
  have hI₀ : CactusInvT wE [(W₁, [lendRec 1] ++ [])] [lfE 1] W₁ [lendRec 1]
      [(lendRec 1, lfE 1)] _ :=
    ⟨.cons .nil (ResUT.compS_empty_right _), fun p => by simp, List.pairwise_singleton _ _,
      hR₁, hI₁, .cons (OnBranchResT.compS hv (OnBranchResT.empty _)
        (onBranch_view (wE.K.refl _) 1)) .nil⟩
  have hFL := frameLife_of_tag hR₁ List.mem_cons_self (by simp)
  have hI := cactusT_spawn (O₁ := [lendRec 1]) (O₂ := []) hv (by simp)
    (onBranch_view (wE.K.refl _) 1) hI₀
  refine ⟨W₁, _, hI, hFL, ?_⟩
  exact lender_ancestor hI (b := (viewRes (lfE 1) 1, [])) (by simp)
    (ResUT.compS_empty_right _) List.mem_cons_self hFL (ResUT.single_get_self _ _)

/-! ### Depth 3 -/

/-- **Depth 3**: lends of `ℓ = 1, 2, 3` at `α₁ = 1 ⊐ α₂ = 2 ⊐ α₃ = 3`, each record owned by the
running branch; a second branch at `α₃` holds the outermost lend's view. Every premise of
`lender_ancestor` holds there, so the second branch's lender `α₁` encloses its point, strictly and
two levels up. -/
theorem lenderEdge_depth3 :
    ∃ (W ρ : TRes wE.K) (μ : Heap),
      CactusInvT wE [(ρ, [lendRec 3, lendRec 2, lendRec 1]), (viewRes (lfE 1) 1, [])]
        [lfE 3, lfE 3] W [lendRec 3, lendRec 2, lendRec 1]
        [(lendRec 3, lfE 3), (lendRec 2, lfE 2), (lendRec 1, lfE 1)] μ ∧
      FrameLifeT wE.K W (lendRec 1) (lfE 1) ∧ FrameLifeT wE.K W (lendRec 2) (lfE 2) ∧
      FrameLifeT wE.K W (lendRec 3) (lfE 3) ∧
      wE.K.lt (lfE 3) (lfE 2) ∧ wE.K.lt (lfE 2) (lfE 1) ∧ wE.K.le (lfE 3) (lfE 1) := by
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain ⟨W₂, hW₂, hR₂, hI₂⟩ := recWInv_lendStep (lfE 2) hR₁ hI₁ (l := 2)
    (BoCa.BoLo.Heap.upd_other (by decide))
  obtain ⟨W₃, hW₃, hR₃, hI₃⟩ := recWInv_lendStep (lfE 3) hR₂ hI₂ (l := 3)
    (by rw [BoCa.BoLo.Heap.upd_other (by decide), BoCa.BoLo.Heap.upd_other (by decide)])
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  obtain ⟨ρ, hρ, hρW⟩ := (ResUT.CompS.assoc (viewRes (lfE 1) 1) (viewRes (lfE 2) 2)
    (viewRes (lfE 3) 3) W₃).mpr ⟨W₂, hW₂, hW₃⟩
  have hon : ∀ k, 1 ≤ k → k ≤ 3 → OnBranchResT wE.K (lfE 3) (viewRes (lfE k) k) :=
    fun k _ hk => onBranch_view (chain_le hk) k
  have hρon : OnBranchResT wE.K (lfE 3) ρ :=
    OnBranchResT.compS hρ (hon 2 (by omega) (by omega)) (hon 3 (by omega) (by omega))
  have hI₀ : CactusInvT wE [(W₃, [lendRec 3, lendRec 2, lendRec 1] ++ [])] [lfE 3] W₃
      [lendRec 3, lendRec 2, lendRec 1]
      [(lendRec 3, lfE 3), (lendRec 2, lfE 2), (lendRec 1, lfE 1)] _ :=
    ⟨.cons .nil (ResUT.compS_empty_right _), fun p => by simp, List.pairwise_singleton _ _,
      hR₃, hI₃, .cons (OnBranchResT.compS hρW (hon 1 le_rfl (by omega)) hρon) .nil⟩
  have hps : ∀ p ∈ [lendRec (K := wE.K) 3, lendRec 2, lendRec 1], ∃ k, p = lendRec k := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hFL₁ := frameLife_of_tag hR₃ (l := 1) (α := lfE 1) (by simp) hps
  have hFL₂ := frameLife_of_tag hR₃ (l := 2) (α := lfE 2) (by simp) hps
  have hFL₃ := frameLife_of_tag hR₃ (l := 3) (α := lfE 3) (by simp) hps
  have hI := cactusT_spawn (O₁ := [lendRec 3, lendRec 2, lendRec 1]) (O₂ := [])
    (ResUT.CompS.comm hρW) (by simp) (hon 1 le_rfl (by omega)) hI₀
  refine ⟨W₃, ρ, _, hI, hFL₁, hFL₂, hFL₃, ⟨chain_le (by omega), lfE_ne (by omega)⟩,
    ⟨chain_le (by omega), lfE_ne (by omega)⟩, ?_⟩
  exact lender_ancestor hI (b := (viewRes (lfE 1) 1, [])) (by simp)
    (ResUT.compS_empty_right _) (by simp) hFL₁ (ResUT.single_get_self _ _)

end BoCa.Fig16.Tree.Wp

end
