import PositiveArrays.Index

/-!
# PositiveArrays — splitting the indexed tensor (K3)

A partition of the index set is a split of the family, at every leaf predicate at once:
owned, `imm` or `mut` leaves, at one lifetime. No frame and no lifetime is involved.

- `vP_fam_split`, `vP_fam_join`: an array or slice `(ℓ, n)` is `(ℓ, i)` beside
  `(ℓ + i, n − i)` for `i ≤ n`, and back: `⊗ⁿ ≅ ⊗ⁱ ⊗ ⊗ⁿ⁻ⁱ`, K3's content
  (`docs/strings-slices-design.md` §5.1).
- `sepList_partition`: any family over a finite list of places splits along any predicate on
  the places, into the places that satisfy it and those that do not. A static subset of a
  struct's fields, and a strided sub-family of a range, are instances; each part is again a
  family of the same leaves.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem uint32_sub_toNat {n i : UInt32} (hi : i ≤ n) : (n - i).toNat = n.toNat - i.toNat :=
  UInt32.toNat_sub_of_le n i hi

/-- **K3's content**: a family splits at a run-time index `i ≤ n`, at every leaf. -/
theorem vP_fam_split {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {n i : UInt32}
    {ρ : WRes} (hv : vP (.fam L) ls δ (Val.arr ℓ n) ρ) (hi : i ≤ n) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vP (.fam L) ls δ (Val.arr ℓ i) ρ₁ ∧
      vP (.fam L) ls δ (Val.arr (ℓ + i.toNat) (n - i)) ρ₂ := by
  obtain ⟨ℓ', n', he, hs⟩ := vP_fam_iff.mp hv
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hin : i.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp hi
  rw [show n.toNat = i.toNat + (n.toNat - i.toNat) by omega] at hs
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := sepRange_split hs
  refine ⟨ρ₁, ρ₂, hc, vP_fam_mk h₁, vP_fam_mk ?_⟩
  rwa [uint32_sub_toNat hi]

/-- Two adjacent families at the same leaves are one. -/
theorem vP_fam_join {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {i k : UInt32}
    {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : vP (.fam L) ls δ (Val.arr ℓ i) ρ₁)
    (h₂ : vP (.fam L) ls δ (Val.arr (ℓ + i.toNat) k) ρ₂)
    (hik : i.toNat + k.toNat < 2 ^ 32) :
    vP (.fam L) ls δ (Val.arr ℓ (i + k)) ρ := by
  obtain ⟨ℓ₁, n₁, he₁, hs₁⟩ := vP_fam_iff.mp h₁
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he₁
  obtain ⟨ℓ₂, n₂, he₂, hs₂⟩ := vP_fam_iff.mp h₂
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he₂
  refine vP_fam_mk ?_
  rw [show (i + k).toNat = i.toNat + k.toNat by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt hik]
  exact sepRange_append hc hs₁ hs₂

/-- **Any partition of a finite index set** splits the family. -/
theorem sepList_partition {P : Loc → WProp} (p : Loc → Bool) (I : List Loc) {ρ : WRes}
    (h : sepList P I ρ) : (sepList P (I.filter p) ⋆ sepList P (I.filter (fun m => !p m))) ρ :=
  (sepList_append _ _ ρ).mp (sepList_perm (List.filter_append_perm p I).symm ρ h)

/-- The parts of a partition compose back. -/
theorem sepList_unpartition {P : Loc → WProp} (p : Loc → Bool) (I : List Loc) {ρ : WRes}
    (h : (sepList P (I.filter p) ⋆ sepList P (I.filter (fun m => !p m))) ρ) : sepList P I ρ :=
  sepList_perm (List.filter_append_perm p I) ρ ((sepList_append _ _ ρ).mpr h)

end BoCa.Fig16.LogRel.Core.PositiveArrays

end
