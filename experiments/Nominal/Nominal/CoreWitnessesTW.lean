import Nominal.TypedWorldEquiv
import Nominal.CoreWitnesses

/-!
# Nominal — the corollary and the `kU` witness at Core's own `wp`

`reopenR_wpTS`: `Package.lean`'s corollary at Core's clauses over `wpTS`. `kUW_convention`: the
probe-3 closure at Core's clauses over `wpTS`, on the nominal carrier — related at `x`, preserved by
the same-parents swap, not related at `x″`. The refutation at `x″` runs `wpTS` at the borrow of a
borrow, which is a typed world (`tw_mm`: built from `∅` by `alloc` and `mutFold`, as Core's
`tw_nested`), so the failure is at a configuration `wpTS` quantifies over.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **The corollary at Core's own `wp`.** -/
theorem reopenR_wpTS {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L] (π : L ≃o L)
    {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P) {δ : LSubN L} (hδ : δ.map π = δ)
    {ls : List (SRecN L)} (hls : actL π ls = ls) (xv : LifeVar) (y : L) (b : Bool) (T : VTy)
    {ρ : ResU L} (h : p.Opens P y ρ) :
    p.Opens P (π y) (relRU π ρ) ∧
      (vR (wpTSN (ℍ := ℍ)) b T ls (δ.extend xv (π y)) p.w (relRU π ρ) ↔
        vR (wpTSN (ℍ := ℍ)) b T ls (δ.extend xv y) p.w ρ) :=
  reopenR π _ (wpTSN_equiv π) hfix hδ hls xv y b T h

section Valid
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]

theorem own_ne_mut (u : Val) : (CellU.own u : CellU L).kind ≠ .mut := by simp [CellU.kind]
theorem own_ne_imm (u : Val) : (CellU.own u : CellU L).kind ≠ .imm := by simp [CellU.kind]

theorem valid_single_own (l : Loc) (u : Val) : (ResU.single l (CellU.own u : CellU L)).Valid := by
  refine ⟨ResU.single l (.own u), ResU.single l (.own u), PMap.empty, ?_, ?_,
    comp_empty_right _ _ _⟩
  · refine .mk (w := []) (nm := ResU.single l (.own u)) (b := PMap.empty)
      (sites_single_ne l _ _ (own_ne_mut u)) .nil .nil ?_ (comp_empty_right _ _ _)
    rw [restrict_single_of l (CellU.own u) .own rfl,
      restrict_single_of_ne l (CellU.own u) .mut (own_ne_mut u)]
    exact comp_empty_right _ _ _
  · refine .mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty) (bi := PMap.empty)
      (sites_single_ne l _ _ (own_ne_mut u)) (sites_single_ne l _ _ (own_ne_imm u)) .nil .nil
      .nil .nil ?_ (comp_empty_left _ _ _)
    rw [restrict_single_of_ne l (CellU.own u) .imm (own_ne_imm u)]
    exact comp_empty_left _ _ _

/-- The two-cell resource with an owned cell at `l` and one `mut` cell at `l′`, by kind. -/
theorem restrict_own_mut (l l' : Loc) (hl : l ≠ l') (u : Val) (ψ' : CellU L)
    (hk : ψ'.kind = .mut) :
    (ResU.pair l (CellU.own u) l' ψ').restrict .own = ResU.single l (.own u) ∧
      (ResU.pair l (CellU.own u) l' ψ').restrict .mut = ResU.single l' ψ' ∧
      (ResU.pair l (CellU.own u) l' ψ').restrict .imm = PMap.empty := by
  have hl' : l' ≠ l := fun e => hl e.symm
  have get_r : ∀ k m, ((ResU.pair l (CellU.own u) l' ψ').restrict k).get m =
      ((ResU.pair l (CellU.own u) l' ψ').get m).bind
        (fun ψ => if ψ.kind = k then some ψ else none) := fun _ _ => rfl
  refine ⟨PMap.ext fun m => ?_, PMap.ext fun m => ?_, PMap.ext fun m => ?_⟩
  · rw [get_r]
    by_cases e : m = l
    · subst e
      rw [ResU.pair_get_left, ResU.single_get_self]
      simp [CellU.kind]
    · rw [ResU.single_get_ne _ e]
      by_cases e' : m = l'
      · subst e'
        rw [ResU.pair_get_right _ _ e]
        simp [hk]
      · rw [ResU.pair_get_ne _ _ e e']; rfl
  · rw [get_r]
    by_cases e : m = l
    · subst e
      rw [ResU.pair_get_left, ResU.single_get_ne _ hl]
      simp [CellU.kind]
    · by_cases e' : m = l'
      · subst e'
        rw [ResU.pair_get_right _ _ e, ResU.single_get_self]
        simp [hk]
      · rw [ResU.pair_get_ne _ _ e e', ResU.single_get_ne _ e']; rfl
  · rw [get_r]
    by_cases e : m = l
    · subst e
      rw [ResU.pair_get_left]
      simp [CellU.kind]
    · by_cases e' : m = l'
      · subst e'
        rw [ResU.pair_get_right _ _ e]
        simp [hk]
      · rw [ResU.pair_get_ne _ _ e e']; rfl

/-- **An owned cell beside a `mut` cell whose witness is `∅` is valid.** -/
theorem valid_own_mut {l l' : Loc} (hl : l ≠ l') (u : Val) {ψ' : CellU L} (hk : ψ'.kind = .mut)
    (hw : ψ'.wit = PMap.empty) : (ResU.pair l (CellU.own u) l' ψ').Valid := by
  obtain ⟨ho, hm, hi⟩ := restrict_own_mut l l' hl u ψ' hk
  have hsm : ResU.Sites (ResU.pair l (CellU.own u) l' ψ') .mut [l'] := by
    refine ⟨List.nodup_singleton _, fun m => ⟨fun h => ?_, fun ⟨ψ, e, k⟩ => ?_⟩⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨ψ', ResU.pair_get_right _ _ (fun e => hl e.symm), hk⟩
    · by_cases e₁ : m = l
      · subst e₁; rw [ResU.pair_get_left] at e; cases Option.some.inj e; cases k
      · by_cases e₂ : m = l'
        · exact List.mem_singleton.mpr e₂
        · rw [ResU.pair_get_ne _ _ e₁ e₂] at e; cases e
  have hsi : ResU.Sites (ResU.pair l (CellU.own u) l' ψ') .imm [] := by
    refine ⟨List.nodup_nil, fun m => ⟨fun h => (by cases h), fun ⟨ψ, e, k⟩ => ?_⟩⟩
    by_cases e₁ : m = l
    · subst e₁; rw [ResU.pair_get_left] at e; cases Option.some.inj e; cases k
    · by_cases e₂ : m = l'
      · subst e₂; rw [ResU.pair_get_right _ _ e₁] at e; cases Option.some.inj e; rw [hk] at k
        cases k
      · rw [ResU.pair_get_ne _ _ e₁ e₂] at e; cases e
  refine ⟨ResU.pair l (CellU.own u) l' ψ', ResU.pair l (CellU.own u) l' ψ', PMap.empty, ?_, ?_,
    comp_empty_right _ _ _⟩
  · refine .mk (w := [(l', PMap.empty)]) (nm := ResU.pair l (CellU.own u) l' ψ')
      (b := PMap.empty) hsm (.cons ψ' (ResU.pair_get_right _ _ (fun e => hl e.symm)) hk
        (by rw [hw]; exact exW_empty _ _) .nil) (.cons .nil (comp_empty_left _ _ _)) ?_
      (comp_empty_right _ _ _)
    rw [ho, hm]
    exact comp_single_single _ _ hl _ _
  · refine .mk (wm := [(l', PMap.empty)]) (wi := []) (a := PMap.empty) (bm := PMap.empty)
      (bi := PMap.empty) hsm hsi
      (.cons ψ' (ResU.pair_get_right _ _ (fun e => hl e.symm)) hk (by rw [hw]; exact agW_empty)
        .nil) .nil (.cons .nil (comp_empty_left _ _ _)) .nil ?_ (comp_empty_left _ _ _)
    rw [hi]
    exact comp_empty_left _ _ _

theorem lower_of_flat {ρ σ : ResU L} (h : ρ.Flat σ) :
    ρ.Lower (fun l => (σ.get l).map CellU.erase) := ⟨σ, h, fun _ => rfl⟩

end Valid

section KUW
open W

/-- The world `1 ↦ own(())`. -/
theorem tw_one : TWN (ResU.single 1 (CellU.own Val.unit : CellU Lft)) [] [] :=
  .alloc (μ := fun _ => none) (l := 1) (v := .unit) .empty ⟨_, flat_empty, fun _ => rfl⟩ rfl
    (comp_empty_left _ _ _) (valid_single_own 1 .unit)

/-- **The borrow of a borrow at `x″` is a typed world**: `alloc` and `mutFold` at `1`, then at `0`
(Core's `tw_nested`). -/
theorem tw_mm (Wp : WpOpN Lft) : TWN (ResU.single 0 (mmCellR Wp)) [] [] := by
  set inner : CellU Lft := unitCellR Wp (δ₂ x'' q) q with hinner
  have hk : inner.kind = .mut := rfl
  have hwi : inner.wit = PMap.empty := CellU.wit_mutOf _ _ _ _ _ _
  -- `1 ↦ inner`
  have h₂ : TWN (ResU.single 1 inner) [] [] :=
    .mutFold (X := ResU.single 1 (.own .unit)) (Z := PMap.empty) (ρ := PMap.empty)
      (l := 1) (v := .unit) tw_one (comp_empty_right _ _ _) (comp_empty_right _ _ _)
      ⟨inner, hk, rfl, hwi, comp_empty_right _ _ _⟩ (valid_single_mut_empty hk hwi)
  -- `0 ↦ own(loc 1), 1 ↦ inner`
  have h₃ : TWN (ResU.pair 0 (CellU.own (Val.loc 1)) 1 inner) [] [] := by
    refine .alloc (μ := fun l => ((ResU.single 1 inner).get l).map CellU.erase) (l := 0)
      (v := .loc 1) h₂ (lower_of_flat (flat_single_mut_empty hk hwi))
      (by simp [ResU.single_get]) ?_ (valid_own_mut (by decide) _ hk hwi)
    rw [ResU.pair_comm (by decide)]
    exact comp_single_single _ _ (by decide) _ _
  -- `0 ↦ mut(r, loc 1, 1 ↦ inner, 𝒱⟦Mut 'b 1⟧)`
  refine .mutFold (X := ResU.pair 0 (CellU.own (Val.loc 1)) 1 inner) (Z := PMap.empty)
    (ρ := ResU.single 1 inner) (l := 0) (v := .loc 1) h₃
    (comp_single_single _ _ (by decide) _ _) (comp_empty_right _ _ _)
    ⟨mmCellR Wp, rfl, rfl, CellU.wit_mutOf _ _ _ _ _ _, comp_empty_right _ _ _⟩
    (mmCellR_valid Wp)

/-- **At Core's own `wp`, the extra-parents re-make breaks the relation at `kU`**: the closure with
no resource is not related at `x″`, the refuting run taken at a typed world. -/
theorem kUW_not_related_x'' (v : Val) :
    ¬ vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x'' q) v PMap.empty := by
  intro h
  have hw := h [] (ExtN.refl _ _) (.loc 0) (ResU.single 0 (mmCellR (wpTSN (ℍ := ℍ))))
    (ResU.single 0 (mmCellR (wpTSN (ℍ := ℍ)))) (vR_boxMM_x'' _) (comp_empty_left _ _ _)
  obtain ⟨_, _, _, _, _, u, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hq⟩ :=
    hw PMap.empty (ResU.single 0 (mmCellR (wpTSN (ℍ := ℍ)))) []
      (hash_empty_of_valid (mmCellR_valid _)) (comp_empty_left _ _ _) (tw_mm _)
      (fun _ h => by cases h) BoCa.BoLo.Alloc.leastFree 0
  exact vR_mm0_empty _ _ _ true u _ hq

theorem kUW_swap (v : Val) (ρ : ResU Lft) :
    vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x' q) v (relRU π ρ) ↔
      vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x q) v ρ := by
  have := vR_map_wpTS (ℍ := ℍ) π true kU [] (δ₂ x q) v ρ
  rwa [actL_nil, δ₂_map, π_x, π_q] at this

/-- **The probe-3 witness at Core's own relation and `wp`, on the nominal carrier**: related at `x`,
at `x′`, and not at `x″`. -/
theorem kUW_convention (v : Val) :
    vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x q) v PMap.empty ∧
      vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x' q) v PMap.empty ∧
      ¬ vR (wpTSN (ℍ := ℍ)) true kU [] (δ₂ x'' q) v PMap.empty := by
  refine ⟨kUR_related_x _ v, ?_, kUW_not_related_x'' v⟩
  have := (kUW_swap (ℍ := ℍ) v PMap.empty).mpr (kUR_related_x _ v)
  rwa [relRU_empty] at this

end KUW

end Nominal

end
