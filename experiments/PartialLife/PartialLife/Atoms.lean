import PartialLife.Cell
import PartialLife.Symmetry

/-!
# PartialLife — lifetimes as finite sets of atoms

Problem B's nominal reading (`research/effects/src/tier2-problems.md`) re-makes a borrow at a
lifetime `x′` with the same parents as the ended `x`, so that the swap `x ↔ x′` is an automorphism
and the resumer's lifetimes stay incomparable to `x′`; a borrow made after resumption takes parents
from both sides. On a chain that carries the model no such swap exists (`carrier_rigid`). `Atoms` is
an order with all of it: a lifetime is a finite set of atoms, beneath another when it has every atom
of the other (reverse inclusion); `⊤ = ∅` and `x ⊓ y = x ∪ y`.

* `atoms_carrier`: it carries the model, in both readings of `ᾱ` (it is a reverse-well-founded
  lattice);
* `permAtoms`: every permutation of the atoms is an order automorphism; `swap_siblings`: the swap
  `i ↔ j` of two atoms not in `a` exchanges `a ∪ {i}` and `a ∪ {j}` and fixes `a`;
* `siblings_incomparable`: `a ∪ {i}` and `a ∪ {j}` are incomparable, both strictly beneath `a`;
* `beneath_both`: `x ∪ r` is beneath both `x` and `r`, the lifetime a borrow made after resumption
  can take, beneath `x′` and the resumer's `r`.

The relation's clauses are invariant under every automorphism of such an order
(`Symmetry.lean`'s `vP_map`, `cP_map`, at `L = Atoms`). `nominal_remake` reads it at the swap: when
no other lifetime of the reading `δ₀` has the atoms `i`, `j`, the relation with `'x` read at
`a ∪ {j}` (and the slots' reading moved by the swap) is the relation with `'x` read at `a ∪ {i}`.
-/

noncomputable section

namespace PartialLife

/-- Lifetimes as finite sets of atoms, reverse inclusion: more atoms, shorter-lived. -/
abbrev Atoms : Type := (Finset ℕ)ᵒᵈ

/-- The lifetime with atoms `s`. -/
def atomsOf (s : Finset ℕ) : Atoms := OrderDual.toDual s

theorem atomsOf_le_atomsOf {s t : Finset ℕ} : atomsOf s ≤ atomsOf t ↔ t ⊆ s := Iff.rfl

theorem atomsOf_lt_atomsOf {s t : Finset ℕ} : atomsOf s < atomsOf t ↔ t ⊂ s := Iff.rfl

theorem atomsOf_top : atomsOf ∅ = ⊤ := rfl

theorem atomsOf_inf (s t : Finset ℕ) : atomsOf s ⊓ atomsOf t = atomsOf (s ∪ t) := rfl

/-- **`Atoms` carries the model**, in both readings of `ᾱ`. -/
theorem atoms_carrier (Loc Val : Type) :
    (∃ Cell : Atoms → Type, IsCarrierP Loc Val Cell) ∧
      (∃ Cell : Atoms → Type, IsCarrierL Loc Val Cell) :=
  ⟨⟨_, carrierP_of_wellFoundedGT Loc Val⟩, ⟨_, carrierL_of_wellFoundedGT Loc Val⟩⟩

/-- A permutation of the atoms, on finite sets. -/
def permFinset (e : Equiv.Perm ℕ) : Finset ℕ ≃o Finset ℕ where
  toEquiv := Equiv.finsetCongr e
  map_rel_iff' := by
    intro s t
    show s.map e.toEmbedding ⊆ t.map e.toEmbedding ↔ s ⊆ t
    exact Finset.map_subset_map

/-- **Every permutation of the atoms is an order automorphism of `Atoms`.** -/
def permAtoms (e : Equiv.Perm ℕ) : Atoms ≃o Atoms := (permFinset e).dual

theorem permAtoms_atomsOf (e : Equiv.Perm ℕ) (s : Finset ℕ) :
    permAtoms e (atomsOf s) = atomsOf (s.map e.toEmbedding) := rfl

/-- **The swap of two atoms exchanges the two siblings and fixes their parent.** -/
theorem swap_siblings (a : Finset ℕ) {i j : ℕ} (hi : i ∉ a) (hj : j ∉ a) :
    permAtoms (Equiv.swap i j) (atomsOf (insert i a)) = atomsOf (insert j a) ∧
      permAtoms (Equiv.swap i j) (atomsOf (insert j a)) = atomsOf (insert i a) ∧
      permAtoms (Equiv.swap i j) (atomsOf a) = atomsOf a := by
  have hfix : ∀ s : Finset ℕ, i ∉ s → j ∉ s → s.map (Equiv.swap i j).toEmbedding = s := by
    intro s hsi hsj
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_swap]
    by_cases hxi : x = i
    · subst hxi; simp [Equiv.swap_apply_left, hsi, hsj]
    · by_cases hxj : x = j
      · subst hxj; simp [Equiv.swap_apply_right, hsi, hsj]
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  refine ⟨?_, ?_, ?_⟩
  · rw [permAtoms_atomsOf, Finset.map_insert, hfix a hi hj]
    simp [Equiv.swap_apply_left]
  · rw [permAtoms_atomsOf, Finset.map_insert, hfix a hi hj]
    simp [Equiv.swap_apply_right]
  · rw [permAtoms_atomsOf, hfix a hi hj]

/-- The swap of two atoms is not the identity. -/
theorem swap_ne_refl {i j : ℕ} (h : i ≠ j) : permAtoms (Equiv.swap i j) ≠ OrderIso.refl Atoms := by
  intro e
  have := congrArg (fun π : Atoms ≃o Atoms => π (atomsOf {i})) e
  simp only [OrderIso.refl_apply, permAtoms_atomsOf, Finset.map_singleton] at this
  have h' : ({(Equiv.swap i j) i} : Finset ℕ) = {i} := congrArg OrderDual.ofDual this
  rw [Equiv.swap_apply_left, Finset.singleton_inj] at h'
  exact h h'.symm

/-- **The two siblings are incomparable, and both strictly beneath their parent.** -/
theorem siblings_incomparable (a : Finset ℕ) {i j : ℕ} (hi : i ∉ a) (hj : j ∉ a) (h : i ≠ j) :
    ¬ atomsOf (insert i a) ≤ atomsOf (insert j a) ∧ ¬ atomsOf (insert j a) ≤ atomsOf (insert i a) ∧
      atomsOf (insert i a) < atomsOf a ∧ atomsOf (insert j a) < atomsOf a := by
  refine ⟨fun hle => ?_, fun hle => ?_, ?_, ?_⟩
  · rw [atomsOf_le_atomsOf] at hle
    have := hle (Finset.mem_insert_self j a)
    rcases Finset.mem_insert.mp this with e | e
    · exact h e.symm
    · exact hj e
  · rw [atomsOf_le_atomsOf] at hle
    have := hle (Finset.mem_insert_self i a)
    rcases Finset.mem_insert.mp this with e | e
    · exact h e
    · exact hi e
  · rw [atomsOf_lt_atomsOf]; exact Finset.ssubset_insert hi
  · rw [atomsOf_lt_atomsOf]; exact Finset.ssubset_insert hj

/-- **A lifetime beneath both**: `x ∪ r` is beneath `x` and beneath `r`. -/
theorem beneath_both (x r : Finset ℕ) :
    atomsOf (x ∪ r) ≤ atomsOf x ∧ atomsOf (x ∪ r) ≤ atomsOf r :=
  ⟨atomsOf_le_atomsOf.mpr Finset.subset_union_left,
    atomsOf_le_atomsOf.mpr Finset.subset_union_right⟩

/-! ### Re-making at a sibling is an automorphism of the relation -/

open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core in
open BoCa.Lifetime (LifeVar) in
open DenseCarrier (LSubD) in
/-- The swap of `i`, `j` on a reading none of whose values has either atom moves only `'x`. -/
theorem map_swap_extend (δ₀ : LSubD Atoms) {i j : ℕ}
    (hδ₀ : ∀ p ∈ δ₀.entries, i ∉ OrderDual.ofDual p.2 ∧ j ∉ OrderDual.ofDual p.2)
    (a : Finset ℕ) (hi : i ∉ a) (hj : j ∉ a) (x : LifeVar) :
    (δ₀.extend x (atomsOf (insert i a))).map (permAtoms (Equiv.swap i j)) =
      δ₀.extend x (atomsOf (insert j a)) := by
  rw [LSubD.map_extend, (swap_siblings a hi hj).1]
  congr 1
  conv_rhs => rw [← LSubD.map_id δ₀]
  refine LSubD.map_congr fun p hp => ?_
  obtain ⟨hpi, hpj⟩ := hδ₀ p hp
  show OrderDual.toDual ((OrderDual.ofDual p.2).map (Equiv.swap i j).toEmbedding) = p.2
  have : (OrderDual.ofDual p.2).map (Equiv.swap i j).toEmbedding = OrderDual.ofDual p.2 := by
    ext y
    simp only [Finset.mem_map_equiv, Equiv.symm_swap]
    by_cases hyi : y = i
    · subst hyi; simp [Equiv.swap_apply_left, hpi, hpj]
    · by_cases hyj : y = j
      · subst hyj; simp [Equiv.swap_apply_right, hpi, hpj]
      · rw [Equiv.swap_apply_of_ne_of_ne hyi hyj]
  rw [this]; rfl

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ] in
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core in
open BoCa.Lifetime (LifeVar) in
open DenseCarrier (LSubD) in
/-- **Re-making `'x` at a sibling is an automorphism of the relation**: with `'x` read at `a ∪ {j}`
and the slots' reading moved by the swap `i ↔ j`, the relation is the one with `'x` read at
`a ∪ {i}`, at every value type, record list, value and resource, when no other value of the reading
has `i` or `j`. -/
theorem nominal_remake (ι : Reading Atoms) (A : VTy) (ls : List SRec) (δ₀ : LSubD Atoms)
    {i j : ℕ} (hδ₀ : ∀ p ∈ δ₀.entries, i ∉ OrderDual.ofDual p.2 ∧ j ∉ OrderDual.ofDual p.2)
    (a : Finset ℕ) (hi : i ∉ a) (hj : j ∉ a) (x : LifeVar) :
    vP (ℍ := ℍ) (ι.map (permAtoms (Equiv.swap i j))) A ls (δ₀.extend x (atomsOf (insert j a))) =
      vP (ℍ := ℍ) ι A ls (δ₀.extend x (atomsOf (insert i a))) := by
  rw [← map_swap_extend δ₀ hδ₀ a hi hj x, vP_map]

end PartialLife

end
