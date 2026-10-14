import Nominal.CoreRelation
import Nominal.Witnesses

/-!
# Nominal — the corollary and the `kU` witness at Core's clauses with records

`reopenR`: `Package.lean`'s corollary at `vR`, for every automorphism fixing the package, the
other variables' reading and the record list, and carrying the `wp`.

`kU` at `vR (wpLift)`: related at `x` with no records (its argument type is empty at every record
list, `vR_boxMM_empty`), preserved by the same-parents swap (`kUR_swap`, from `vR_map`), and not
related at `x″` (`kUR_not_related_x''`): the same outcome as at the record-free relation.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

section General
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem actL_nil (π : L ≃o L) : actL π ([] : List (SRecN L)) = [] := rfl

/-- **The corollary at Core's clauses**: opening at `π y` relates exactly what opening at `y`
related, for every `π` fixing the package, the reading and the record list, and carrying `W`. -/
theorem reopenR (π : L ≃o L) (W : WpOpN L) (hW : WpEquiv π W) {P : Val → WPropN L}
    {p : Pkg L} (hfix : p.FixedBy π P) {δ : LSubN L} (hδ : δ.map π = δ)
    {ls : List (SRecN L)} (hls : actL π ls = ls) (xv : LifeVar) (y : L) (b : Bool) (T : VTy)
    {ρ : ResU L} (h : p.Opens P y ρ) :
    p.Opens P (π y) (relRU π ρ) ∧
      (vR W b T ls (δ.extend xv (π y)) p.w (relRU π ρ) ↔ vR W b T ls (δ.extend xv y) p.w ρ) := by
  refine ⟨Pkg.opens_relRU hfix h, ?_⟩
  have := vR_map π W hW b T ls (δ.extend xv y) p.w ρ
  rwa [LSubN.map_extend, hδ, hls] at this

theorem vR_mut (W : WpOpN L) (b : Bool) (a : Lifetime.Life) (A : VTy) (ls : List (SRecN L))
    (δ : LSubN L) (v : Val) :
    vR W b (.mut a A) ls δ v = atLifeN δ a fun α => exN fun ℓ =>
      sepN (pureN (v = .loc ℓ)) (ptoMutR ℓ α ls (fun ls₀ => vR W true A ls₀ δ)) := by
  cases b <;> rfl

theorem vR_box (W : WpOpN L) (b : Bool) (a : Lifetime.Life) (A : VTy) (ls : List (SRecN L))
    (δ : LSubN L) (v : Val) :
    vR W b (.box a A) ls δ v = atLifeN δ a fun α => boxE α (vR W b A ls δ v) := by
  cases b <;> rfl

theorem vR_unit_iff {W : WpOpN L} {b : Bool} {ls : List (SRecN L)} {δ : LSubN L} {v : Val}
    {σ : ResU L} : vR W b .unit ls δ v σ ↔ σ = PMap.empty ∧ v = .unit := by
  cases b <;> exact Iff.rfl

/-- `ℓ ↦ mut(b, (), ∅, 𝒱⟦1⟧)` at the records' empty list. -/
def unitCellR (W : WpOpN L) (δ : LSubN L) (b : L) : CellU L :=
  CellU.mutOf b .unit PMap.empty (empty_inStratum {b}) (vR W true .unit [] δ)
    (vR_unit_iff.mpr ⟨rfl, rfl⟩)

theorem vR_mut_unit (W : WpOpN L) (δ : LSubN L) {a : Lifetime.Life} {α b : L}
    (ha : interpN δ a = some α) (hab : α ≤ b) (ℓ : Loc) :
    vR W true (.mut a .unit) [] δ (.loc ℓ) (ResU.single ℓ (unitCellR W δ b)) := by
  rw [vR_mut]
  refine ⟨α, ha, ℓ, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  refine ⟨b, .unit, PMap.empty, empty_inStratum {b}, [], vR_unit_iff.mpr ⟨rfl, rfl⟩, hab,
    fun x => by simp, ?_, rfl⟩
  intro ls' u σ h
  obtain ⟨rfl, -⟩ := vR_unit_iff.mp h
  exact empty_inStratum {b}

/-- The payload's stratification forces the lent cell strictly below `@'c` when `Mut 'c 1` is the
payload. -/
theorem lt_of_mutR_unit (W : WpOpN L) {δ : LSubN L} {c : Lifetime.Life} {γ b : L}
    (hγ : interpN δ c = some γ)
    (hstr : ∀ ls' u σ, vR W true (.mut c .unit) ls' δ u σ → σ.InStratum {b}) : b < γ := by
  have := hstr _ _ _ (vR_mut_unit W δ hγ (le_refl γ) 0) 0 _ (ResU.single_get_self _ _)
  exact above_singleton_singleton.mp this

theorem vR_mut_unit_inStratum (W : WpOpN L) {δ : LSubN L} {c : Lifetime.Life} {γ b : L}
    (hγ : interpN δ c = some γ) (hb : b < γ) (ls : List (SRecN L)) (u : Val) (σ : ResU L)
    (h : vR W true (.mut c .unit) ls δ u σ) : σ.InStratum {b} := by
  rw [vR_mut] at h
  obtain ⟨α, hα, ℓ, hs⟩ := h
  obtain ⟨-, b', u', σ', h', ls₀, hw', hαb', -, -, rfl⟩ := sepN_pure_iff.mp hs
  rw [hγ] at hα
  cases Option.some.inj hα
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact above_singleton_singleton.mpr (lt_of_lt_of_le hb hαb')

/-- **`Mut 'a (Mut 'a 1)` has no value, at any record list.** -/
theorem vR_mm0_empty (W : WpOpN L) (ls : List (SRecN L)) (δ : LSubN L) (b : Bool) (v : Val)
    (ρ : ResU L) : ¬ vR W b (.mut (.var 0) (.mut (.var 0) .unit)) ls δ v ρ := by
  intro h
  rw [vR_mut] at h
  obtain ⟨α, hα, ℓ, hs⟩ := h
  obtain ⟨-, b', u, σ, hσ, ls₀, hw, hαb, -, hstr, -⟩ := sepN_pure_iff.mp hs
  have hlt := lt_of_mutR_unit W hα hstr
  exact lt_irrefl α (lt_of_le_of_lt hαb hlt)

end General

section KUR
open W
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- At `'a ↦ α`, `'b ↦ β`, `boxMM` is empty at every record list when no lifetime lies strictly
between them. -/
theorem vR_boxMM_empty (Wp : WpOpN Lft) {α β : Lft} (hno : ∀ b : Lft, α < b → b < β → False)
    (b : Bool) (ls : List (SRecN Lft)) (v : Val) (ρ : ResU Lft) :
    ¬ vR Wp b boxMM ls (δ₂ α β) v ρ := by
  intro h
  rw [vR_box] at h
  obtain ⟨α', hα', hbox, hsurv⟩ := h
  cases Option.some.inj hα'
  rw [vR_mut] at hbox
  obtain ⟨α'', hα'', ℓ, hs⟩ := hbox
  cases Option.some.inj hα''
  obtain ⟨-, b₁, u, σ, h₁, ls₀, hw, hαb, -, hstr, rfl⟩ := sepN_pure_iff.mp hs
  have hβ : b₁ < β := lt_of_mutR_unit Wp (δ₂_interp1 α β) hstr
  have hne : ¬ b₁ ≤ α := hsurv ℓ _ (ResU.single_get_self _ _)
  exact hno b₁ (lt_of_le_of_ne hαb (fun e => hne (e ▸ le_rfl))) hβ

/-- **`kU` is related at `x`** at Core's clauses with no records. -/
theorem kUR_related_x (Wp : WpOpN Lft) (v : Val) : vR Wp true kU [] (δ₂ x q) v PMap.empty := by
  intro ls' _ v' ρ₁ _ h₁ _
  exact absurd h₁ (vR_boxMM_empty Wp no_between_x_q true ls' v' ρ₁)

/-- **The same-parents swap preserves it at every resource** (`vR_map`). -/
theorem kUR_swap (v : Val) (ρ : ResU Lft) :
    vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x' q) v (relRU π ρ) ↔
      vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x q) v ρ := by
  have := vR_map_wpLift (ℍ := ℍ) π true kU [] (δ₂ x q) v ρ
  rwa [actL_nil, δ₂_map, π_x, π_q] at this

/-- The borrow of a borrow at `x″` (outer at `r`, inner at `q`), at Core's clauses. -/
def mmCellR (Wp : WpOpN Lft) : CellU Lft :=
  CellU.mutOf (r : Lft) (.loc 1) (ResU.single 1 (unitCellR Wp (δ₂ x'' q) q))
    (fun l ψ e => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact above_singleton_singleton.mpr r_lt_q)
    (vR Wp true (.mut (.var 1) .unit) [] (δ₂ x'' q))
    (vR_mut_unit Wp (δ₂ x'' q) (δ₂_interp1 _ _) le_rfl 1)

theorem vR_boxMM_x'' (Wp : WpOpN Lft) :
    vR Wp true boxMM [] (δ₂ x'' q) (.loc 0) (ResU.single 0 (mmCellR Wp)) := by
  rw [vR_box]
  refine ⟨x'', rfl, ?_, ?_⟩
  · rw [vR_mut]
    refine ⟨x'', rfl, 0, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
    exact ⟨r, _, _, _, [], vR_mut_unit Wp (δ₂ x'' q) (δ₂_interp1 _ _) le_rfl 1, x''_lt_r.le,
      fun x => by simp, fun ls' u σ h => vR_mut_unit_inStratum Wp (δ₂_interp1 _ _) r_lt_q ls' u σ h,
      rfl⟩
  · intro l ψ e
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    exact not_le_of_gt x''_lt_r

theorem mmCellR_valid (Wp : WpOpN Lft) : (ResU.single 0 (mmCellR Wp)).Valid :=
  valid_mut_mut (by decide) rfl rfl (CellU.wit_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _)

/-- **The extra-parents re-make breaks the relation at `kU`, at Core's clauses** with the printed
`wp`: the same closure with the same empty resource is not related at `x″`. -/
theorem kUR_not_related_x'' (v : Val) :
    ¬ vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x'' q) v PMap.empty := by
  intro h
  have hw := h [] (ExtN.refl _ _) (.loc 0) (ResU.single 0 (mmCellR (wpLift (ℍ := ℍ))))
    (ResU.single 0 (mmCellR (wpLift (ℍ := ℍ)))) (vR_boxMM_x'' _) (comp_empty_left _ _ _)
  obtain ⟨_, _, _, _, _, _, u, _, _, _, _, _, _, _, _, _, _, _, _, _, hq⟩ :=
    hw PMap.empty (hash_empty_of_valid (mmCellR_valid _))
  exact vR_mm0_empty _ [] _ true u _ hq

/-- (a) and (b) at Core's clauses with records. -/
theorem kUR_convention (v : Val) :
    vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x q) v PMap.empty ∧
      vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x' q) v PMap.empty ∧
      ¬ vR (wpLift (ℍ := ℍ)) true kU [] (δ₂ x'' q) v PMap.empty := by
  refine ⟨kUR_related_x _ v, ?_, kUR_not_related_x'' v⟩
  have := (kUR_swap (ℍ := ℍ) v PMap.empty).mpr (kUR_related_x _ v)
  rwa [relRU_empty] at this

end KUR

end Nominal

end
