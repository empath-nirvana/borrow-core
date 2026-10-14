import Nominal.Package

/-!
# Nominal — the probe-3 witnesses, re-run

The atoms: `q` beneath `⊤`; `x`, `x′` and `r` beneath `q` (siblings); `x″` beneath `q` and `r`.
`x′` has `x`'s parents (the **same-parents** re-make); `x″` has an extra parent `r` (the
**extra-parents** re-make, probes 3–6's positional choice: `x` placed beneath a lifetime `r` it was
not beneath).

**(a) `kU` (`DenseCarrier`'s `core_not_relend_kU`).** `kU = U([@'a](Mut 'a (Mut 'b 1)) ⊸ F mm0)`
with `mm0 = Mut 'a (Mut 'a 1)`, which has no value (`vN_mm0_empty`). At `'a ↦ x`, `'b ↦ q` the
argument type is empty — no lifetime lies strictly between `x` and `q` (`vN_boxMM_empty_x`) — so
the closure with no resource is related (`kU_related_x`). The same-parents re-make preserves it
(`kU_swap`, an instance of `vN_map`; `kU_related_x'` directly). The extra-parents re-make breaks
it (`kU_not_related_x''`): `r` lies strictly between `x″` and `q`, a valid borrow of a borrow
inhabits the argument type, and `F mm0` has no value.

**The `Imm 'x (Imm 'r U)` closure.** In this relation `Imm 'x (Imm 'r U)` is inhabited at every
reading, `r` an ancestor of `x` or not (`vN_immImm_inhabited`): an `imm` cell's payload carries no
stratification condition, and an inner cell at `⊤` (or at a common ancestor) is in the outer
cell's stratum. So a closure over it is not vacuously related at `x`. The `Mut` analogue is:
`Mut 'x (Mut 'r 1)` is empty when `r` is not a strict ancestor of `x` (`vN_mutMut_empty`), so
`kV = U(Mut 'x (Mut 'r 1) ⊸ F mm0)` is related at `x` (`kV_related_x`), at `x′`
(`kV_related_x'`), and not at `x″`, beneath `r` (`kV_not_related_x''`).

**(b) The convention is what matters**: at `kU` and `kV` the same closure, with the same (empty)
resource, is related after the same-parents re-make and not after the extra-parents one.

**(c) The scheduler.** A closed package whose resources are owned (a task that borrowed only its
own local, `S = ∅`) lies in every stratum, so it can be stored under any `Mut 'q`
(`closed_inStratum`). A package that captured a borrow at `s` can be stored under `Mut 'q` only if
`s ⊐ 'q`: `Mut 'q (Ref 1 ⊗ Mut 's 1)` is inhabited exactly when `q < s`
(`vN_store_captured_iff`), Rust's `T: 'q`.

The self-borrow itself: opening the minimal package (`c` owned, contents the borrow of `c`) at `x`
is related at `Mut 'x 1` (`selfBorrow_related`), and so is re-opening at `x′` (`selfBorrow_reopen`,
from `reopen_swap`).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

/-! ### Unfolding the clauses -/

section Unfold
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem vN_unit (b : Bool) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b .unit δ v = pureN (v = .unit) := by cases b <;> rfl

theorem vN_mut (b : Bool) (a : Lifetime.Life) (A : VTy) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b (.mut a A) δ v = atLifeN δ a fun α =>
      exN fun ℓ => sepN (pureN (v = .loc ℓ)) (ptoMutN ℓ α (vN (ℍ := ℍ) true A δ)) := by
  cases b <;> rfl

theorem vN_imm (b : Bool) (a : Lifetime.Life) (A : VTy) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b (.imm a A) δ v = atLifeN δ a fun α =>
      exN fun ℓ => sepN (pureN (v = .loc ℓ)) (ptoImmN ℓ α (vN (ℍ := ℍ) false A δ)) := by
  cases b <;> rfl

theorem vN_box (b : Bool) (a : Lifetime.Life) (A : VTy) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b (.box a A) δ v = atLifeN δ a fun α => boxE α (vN (ℍ := ℍ) b A δ v) := by
  cases b <;> rfl

theorem vN_ref (b : Bool) (A : VTy) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b (.ref A) δ v = exN fun ℓ => exN fun v' =>
      sepN (pureN (v = .loc ℓ)) (sepN (ptoOwnN ℓ v') (vN (ℍ := ℍ) b A δ v')) := by
  cases b <;> rfl

theorem vN_tensor (b : Bool) (A B : VTy) (δ : LSubN L) (v : Val) :
    vN (ℍ := ℍ) b (.tensor A B) δ v = exN fun v₁ => exN fun v₂ =>
      sepN (pureN (v = .pair v₁ v₂)) (sepN (vN (ℍ := ℍ) b A δ v₁) (vN (ℍ := ℍ) b B δ v₂)) := by
  cases b <;> rfl

theorem vN_thunk_arr (A : VTy) (C : CTy) (δ : LSubN L) (v : Val) (ρ : ResU L) :
    vN (ℍ := ℍ) true (.thunk (.arr A C)) δ v ρ ↔
      ∀ v', wandN (vN (ℍ := ℍ) true A δ v') (cN (ℍ := ℍ) C δ (.app (.val v) (.val v'))) ρ :=
  Iff.rfl

theorem cN_ret (A : VTy) (δ : LSubN L) (e : Expr) :
    cN (ℍ := ℍ) (.ret A) δ e = wpN (ℍ := ℍ) e (vN (ℍ := ℍ) true A δ) := rfl

end Unfold

/-! ### Closures over an argument type -/

section Closures
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- A closure whose argument type has no value is related, with any resource. -/
theorem closure_vacuous {A B : VTy} {δ : LSubN L} (hA : ∀ v σ, ¬ vN (ℍ := ℍ) true A δ v σ)
    (v : Val) (ρ : ResU L) : vN (ℍ := ℍ) true (.thunk (.arr A (.ret B))) δ v ρ :=
  (vN_thunk_arr A _ δ v ρ).mpr fun v' ρ₁ _ h₁ _ => absurd h₁ (hA v' ρ₁)

/-- A closure with no resource whose argument type has a valid value and whose result type has
none is not related. -/
theorem closure_not_related {A B : VTy} {δ : LSubN L} {v' : Val} {σ : ResU L}
    (hA : vN (ℍ := ℍ) true A δ v' σ) (hσ : σ.Valid) (hB : ∀ v ρ, ¬ vN (ℍ := ℍ) true B δ v ρ)
    (v : Val) : ¬ vN (ℍ := ℍ) true (.thunk (.arr A (.ret B))) δ v PMap.empty := by
  intro h
  have hw := ((vN_thunk_arr A _ δ v _).mp h) v' σ σ hA (comp_empty_left _ _ _)
  rw [cN_ret] at hw
  obtain ⟨_, _, _, _, _, _, u, _, _, _, _, _, _, _, _, _, _, _, _, _, hq⟩ :=
    hw PMap.empty (hash_empty_of_valid hσ)
  exact hB u _ hq

end Closures

/-! ### Cells of the `Mut` clause -/

section MutCells
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem vN_unit_empty_iff {b : Bool} {δ : LSubN L} {v : Val} {σ : ResU L} :
    vN (ℍ := ℍ) b .unit δ v σ ↔ σ = PMap.empty ∧ v = .unit := by
  rw [vN_unit]; exact Iff.rfl

theorem empty_inStratum (S : Finset L) : ResU.InStratum S (PMap.empty : ResU L) :=
  fun _ _ e => absurd e (by simp)

/-- The cell `ℓ ↦ mut(b, (), ∅, 𝒱⟦1⟧)`. -/
def unitCell (δ : LSubN L) (b : L) : CellU L :=
  CellU.mutOf b .unit PMap.empty (empty_inStratum {b})
    (vN (ℍ := ℍ) true .unit δ) (vN_unit_empty_iff.mpr ⟨rfl, rfl⟩)

/-- `ℓ ↦ mut(b, (), ∅, 𝒱⟦1⟧)` is related at `Mut 'a 1` when `@'a ≤ b`. -/
theorem vN_mut_unit (δ : LSubN L) {a : Lifetime.Life} {α b : L} (ha : interpN δ a = some α)
    (hab : α ≤ b) (ℓ : Loc) :
    vN (ℍ := ℍ) true (.mut a .unit) δ (.loc ℓ) (ResU.single ℓ (unitCell (ℍ := ℍ) δ b)) := by
  rw [vN_mut]
  refine ⟨α, ha, ℓ, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  refine ⟨b, .unit, PMap.empty, _, vN_unit_empty_iff.mpr ⟨rfl, rfl⟩, hab, ?_, rfl⟩
  intro u σ h
  obtain ⟨rfl, -⟩ := vN_unit_empty_iff.mp h
  exact fun _ _ e => absurd e (by simp)

/-- Every value of `Mut 'a A` is one `mut` cell at a lifetime `⊒ @'a` storing `𝒱⟦A⟧`. -/
theorem vN_mut_cell {δ : LSubN L} {a : Lifetime.Life} {A : VTy} {v : Val} {ρ : ResU L}
    (h : vN (ℍ := ℍ) true (.mut a A) δ v ρ) :
    ∃ α, interpN δ a = some α ∧ ∃ ℓ, v = .loc ℓ ∧ ptoMutN ℓ α (vN (ℍ := ℍ) true A δ) ρ := by
  rw [vN_mut] at h
  obtain ⟨α, hα, ℓ, hs⟩ := h
  obtain ⟨hv, hp⟩ := sepN_pure_iff.mp hs
  exact ⟨α, hα, ℓ, hv, hp⟩

/-- **`Mut 'a (Mut 'a 1)` has no value**: its payload holds at a cell at `@'a`, which is not in
the stratum of a cell at or above `@'a`. -/
theorem vN_mm0_empty (δ : LSubN L) (b : Bool) (v : Val) (ρ : ResU L) :
    ¬ vN (ℍ := ℍ) b (.mut (.var 0) (.mut (.var 0) .unit)) δ v ρ := by
  intro h
  rw [vN_mut] at h
  obtain ⟨α, hα, ℓ, hs⟩ := h
  obtain ⟨-, b', u, σ, hσ, hw, hαb, hstr, -⟩ := sepN_pure_iff.mp hs
  have hin := vN_mut_unit (ℍ := ℍ) δ hα (le_refl α) 0
  have := hstr _ _ hin 0 _ (ResU.single_get_self _ _)
  have hlt : b' < α := (above_singleton_singleton.mp this)
  exact lt_irrefl α (lt_of_le_of_lt hαb hlt)

/-- The payload's stratification forces the lent cell strictly below `@'c` when `Mut 'c 1` is the
payload. -/
theorem lt_of_mut_mut_unit {δ : LSubN L} {c : Lifetime.Life} {γ b : L}
    (hγ : interpN δ c = some γ) (hstr : ∀ u σ, vN (ℍ := ℍ) true (.mut c .unit) δ u σ →
      σ.InStratum {b}) : b < γ := by
  have := hstr _ _ (vN_mut_unit (ℍ := ℍ) δ hγ (le_refl γ) 0) 0 _ (ResU.single_get_self _ _)
  exact above_singleton_singleton.mp this

/-- Every value of `Mut 'c 1` sits in the stratum of any lifetime strictly below `@'c`. -/
theorem vN_mut_unit_inStratum {δ : LSubN L} {c : Lifetime.Life} {γ b : L}
    (hγ : interpN δ c = some γ) (hb : b < γ) (u : Val) (σ : ResU L)
    (h : vN (ℍ := ℍ) true (.mut c .unit) δ u σ) : σ.InStratum {b} := by
  obtain ⟨α, hα, ℓ, -, b', u', σ', h', hw', hαb', -, rfl⟩ := vN_mut_cell h
  rw [hγ] at hα
  cases Option.some.inj hα
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact above_singleton_singleton.mpr (lt_of_lt_of_le hb hαb')

theorem single_unitCell_inStratum (δ : LSubN L) {γ b₁ b₂ : L} (h₁ : b₁ < γ) (h₂ : γ ≤ b₂)
    (ℓ' : Loc) : ResU.InStratum {b₁} (ResU.single ℓ' (unitCell (ℍ := ℍ) δ b₂)) := by
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact above_singleton_singleton.mpr (lt_of_lt_of_le h₁ h₂)

/-- The borrow of a borrow `ℓ ↦ mut(b₁, ℓ′, ℓ′ ↦ mut(b₂, (), ∅, 𝒱⟦1⟧), 𝒱⟦Mut 'c 1⟧)`. -/
def mmCell (δ : LSubN L) (c : Lifetime.Life) {γ : L} (hγ : interpN δ c = some γ) (b₁ b₂ : L)
    (h₁ : b₁ < γ) (h₂ : γ ≤ b₂) (ℓ' : Loc) : CellU L :=
  CellU.mutOf b₁ (.loc ℓ') (ResU.single ℓ' (unitCell (ℍ := ℍ) δ b₂))
    (single_unitCell_inStratum δ h₁ h₂ ℓ')
    (vN (ℍ := ℍ) true (.mut c .unit) δ) (vN_mut_unit (ℍ := ℍ) δ hγ h₂ ℓ')

/-- **The borrow of a borrow is related at `Mut 'a (Mut 'c 1)`** when `@'a ≤ b₁ < @'c ≤ b₂`. -/
theorem vN_mm (δ : LSubN L) {a c : Lifetime.Life} {α γ : L} (ha : interpN δ a = some α)
    (hγ : interpN δ c = some γ) {b₁ b₂ : L} (h₀ : α ≤ b₁) (h₁ : b₁ < γ) (h₂ : γ ≤ b₂)
    (ℓ ℓ' : Loc) :
    vN (ℍ := ℍ) true (.mut a (.mut c .unit)) δ (.loc ℓ)
      (ResU.single ℓ (mmCell (ℍ := ℍ) δ c hγ b₁ b₂ h₁ h₂ ℓ')) := by
  rw [vN_mut]
  refine ⟨α, ha, ℓ, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  exact ⟨b₁, _, _, _, vN_mut_unit (ℍ := ℍ) δ hγ h₂ ℓ', h₀, vN_mut_unit_inStratum hγ h₁, rfl⟩

theorem mmCell_valid (δ : LSubN L) (c : Lifetime.Life) {γ : L} (hγ : interpN δ c = some γ)
    (b₁ b₂ : L) (h₁ : b₁ < γ) (h₂ : γ ≤ b₂) {ℓ ℓ' : Loc} (hl : ℓ ≠ ℓ') :
    (ResU.single ℓ (mmCell (ℍ := ℍ) δ c hγ b₁ b₂ h₁ h₂ ℓ')).Valid :=
  valid_mut_mut hl rfl rfl (CellU.wit_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _)

/-- `Mut 'a (Mut 'c 1)` is empty unless some lifetime `b` has `@'a ≤ b < @'c`. -/
theorem vN_mutMut_empty_of {δ : LSubN L} {a c : Lifetime.Life} {α γ : L}
    (ha : interpN δ a = some α) (hγ : interpN δ c = some γ) (hno : ¬ α < γ) (v : Val)
    (ρ : ResU L) : ¬ vN (ℍ := ℍ) true (.mut a (.mut c .unit)) δ v ρ := by
  intro h
  obtain ⟨α', hα', ℓ, -, b, u, σ, h₁, hw, hαb, hstr, -⟩ := vN_mut_cell h
  rw [ha] at hα'
  cases Option.some.inj hα'
  exact hno (lt_of_le_of_lt hαb (lt_of_mut_mut_unit hγ hstr))

end MutCells

/-! ### The atoms -/

namespace W

/-- `q`, beneath `⊤` only. -/
def q : Atom := .mk [] 0
/-- `x`, beneath `q`. -/
def x : Atom := .mk [q] 1
/-- `x′`, beneath `q`: `x`'s parents. -/
def x' : Atom := .mk [q] 2
/-- `r`, beneath `q`: a sibling of `x`. -/
def r : Atom := .mk [q] 3
/-- `x″`, beneath `q` and `r`: `x`'s parents and one more. -/
def x'' : Atom := .mk [q, r] 4

theorem not_below_q (b : Atom) : ¬ Atom.Below q b := by
  intro h
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.mp h
  exact (List.not_mem_nil (a := c)) hc

/-- The strict ancestors of an atom all of whose parents are beneath `⊤` only are its parents. -/
theorem below_iff_of_roots {a b : Atom} (h : ∀ p ∈ a.ps, p.ps = []) :
    Atom.Below a b ↔ b ∈ a.ps := by
  constructor
  · intro hb
    obtain ⟨c, hc, hcb⟩ := Relation.TransGen.head'_iff.mp hb
    rcases Relation.ReflTransGen.cases_head hcb with rfl | ⟨d, hd, -⟩
    · exact hc
    · have : d ∈ c.ps := hd
      rw [h c hc] at this
      exact absurd this (List.not_mem_nil)
  · exact fun hb => Relation.TransGen.single hb

theorem below_x_iff (b : Atom) : Atom.Below x b ↔ b = q := by
  rw [below_iff_of_roots (by intro p hp; rw [List.mem_singleton.mp hp]; rfl)]
  exact List.mem_singleton

theorem below_x'_iff (b : Atom) : Atom.Below x' b ↔ b = q := by
  rw [below_iff_of_roots (by intro p hp; rw [List.mem_singleton.mp hp]; rfl)]
  exact List.mem_singleton

theorem below_r_iff (b : Atom) : Atom.Below r b ↔ b = q := by
  rw [below_iff_of_roots (by intro p hp; rw [List.mem_singleton.mp hp]; rfl)]
  exact List.mem_singleton

theorem sameParents : Atom.SameParents x x' := fun _ => Iff.rfl

theorem q_ne_x : q ≠ x := by intro h; cases h
theorem r_ne_q : r ≠ q := by intro h; cases h
theorem x_ne_x' : x ≠ x' := by intro h; cases h

theorem x_lt_q : (x : Lft) < q := WithTop.coe_lt_coe.mpr ((below_x_iff q).mpr rfl)
theorem x'_lt_q : (x' : Lft) < q := WithTop.coe_lt_coe.mpr ((below_x'_iff q).mpr rfl)
theorem r_lt_q : (r : Lft) < q := WithTop.coe_lt_coe.mpr ((below_r_iff q).mpr rfl)
theorem x''_lt_r : (x'' : Lft) < r :=
  WithTop.coe_lt_coe.mpr (Atom.lt_of_mem_ps (by simp [x'']))
theorem x''_lt_q : (x'' : Lft) < q := lt_trans x''_lt_r r_lt_q

/-- **No lifetime lies strictly between `x` and `q`.** -/
theorem no_between_x_q (b : Lft) (h₁ : (x : Lft) < b) (h₂ : b < q) : False := by
  induction b using WithTop.recTopCoe with
  | top => exact absurd h₂ (not_lt_of_ge le_top)
  | coe b =>
      have hb : Atom.Below x b := WithTop.coe_lt_coe.mp h₁
      rw [below_x_iff] at hb
      subst hb
      exact lt_irrefl _ h₂

theorem no_between_x'_q (b : Lft) (h₁ : (x' : Lft) < b) (h₂ : b < q) : False := by
  induction b using WithTop.recTopCoe with
  | top => exact absurd h₂ (not_lt_of_ge le_top)
  | coe b =>
      have hb : Atom.Below x' b := WithTop.coe_lt_coe.mp h₁
      rw [below_x'_iff] at hb
      subst hb
      exact lt_irrefl _ h₂

/-- `r` is not an ancestor of `x`: they are siblings. -/
theorem not_x_lt_r : ¬ (x : Lft) < r := by
  intro h
  have hb : Atom.Below x r := WithTop.coe_lt_coe.mp h
  rw [below_x_iff] at hb
  exact r_ne_q hb

theorem not_x'_lt_r : ¬ (x' : Lft) < r := by
  intro h
  have hb : Atom.Below x' r := WithTop.coe_lt_coe.mp h
  rw [below_x'_iff] at hb
  exact r_ne_q hb

/-- `q` and `r` contain neither `x` nor `x′`: the swap fixes them. -/
theorem q_not_le (a : Atom) (ha : a = x ∨ a = x') : ¬ q ≤ a := by
  rintro (h | h)
  · rcases ha with rfl | rfl <;> cases h
  · exact not_below_q a h

theorem r_not_le (a : Atom) (ha : a = x ∨ a = x') : ¬ r ≤ a := by
  rintro (h | h)
  · rcases ha with rfl | rfl <;> cases h
  · have : a = q := (below_r_iff a).mp h
    rcases ha with rfl | rfl <;> cases this

/-- The same-parents swap `x ↔ x′`. -/
abbrev π : Lft ≃o Lft := swapLft sameParents

theorem π_x : π (x : Lft) = x' := swapLft_x sameParents
theorem π_q : π (q : Lft) = q :=
  swapLft_fix sameParents fun a ha => by
    obtain rfl := WithTop.coe_injective ha
    exact ⟨q_not_le x (Or.inl rfl), q_not_le x' (Or.inr rfl)⟩
theorem π_r : π (r : Lft) = r :=
  swapLft_fix sameParents fun a ha => by
    obtain rfl := WithTop.coe_injective ha
    exact ⟨r_not_le x (Or.inl rfl), r_not_le x' (Or.inr rfl)⟩

/-- `'a ↦ α`, `'b ↦ β`. -/
def δ₂ (α β : Lft) : LSubN Lft := ⟨[(0, α), (1, β)]⟩

theorem δ₂_find0 (α β : Lft) : (δ₂ α β).find? 0 = some α := rfl
theorem δ₂_find1 (α β : Lft) : (δ₂ α β).find? 1 = some β := rfl
theorem δ₂_interp0 (α β : Lft) : interpN (δ₂ α β) (.var 0) = some α := rfl
theorem δ₂_interp1 (α β : Lft) : interpN (δ₂ α β) (.var 1) = some β := rfl

theorem δ₂_map (α β : Lft) : (δ₂ α β).map π = δ₂ (π α) (π β) := rfl

end W

/-! ### (a), (b): `kU` -/

section KU
open W
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `Mut 'a (Mut 'b 1)`. -/
abbrev mm : VTy := .mut (.var 0) (.mut (.var 1) .unit)
/-- `[@'a] (Mut 'a (Mut 'b 1))`. -/
abbrev boxMM : VTy := .box (.var 0) mm
/-- `Mut 'a (Mut 'a 1)`. -/
abbrev mm0 : VTy := .mut (.var 0) (.mut (.var 0) .unit)
/-- `U ([@'a] (Mut 'a (Mut 'b 1)) ⊸ F (Mut 'a (Mut 'a 1)))`, `DenseCarrier`'s `kU`. -/
abbrev kU : VTy := .thunk (.arr boxMM (.ret mm0))

/-- At `'a ↦ α`, `'b ↦ β`, `boxMM` is empty when no lifetime lies strictly between them. -/
theorem vN_boxMM_empty {α β : Lft} (hno : ∀ b : Lft, α < b → b < β → False) (b : Bool)
    (v : Val) (ρ : ResU Lft) : ¬ vN (ℍ := ℍ) b boxMM (δ₂ α β) v ρ := by
  intro h
  rw [vN_box] at h
  obtain ⟨α', hα', hbox, hsurv⟩ := h
  cases Option.some.inj hα'
  rw [vN_mut] at hbox
  obtain ⟨α'', hα'', ℓ, hs⟩ := hbox
  cases Option.some.inj hα''
  obtain ⟨-, b₁, u, σ, h₁, hw, hαb, hstr, rfl⟩ := sepN_pure_iff.mp hs
  have hβ : b₁ < β := lt_of_mut_mut_unit (δ₂_interp1 α β) hstr
  have hsv := hsurv ℓ _ (ResU.single_get_self _ _)
  have hne : ¬ b₁ ≤ α := hsv
  exact hno b₁ (lt_of_le_of_ne hαb (fun e => hne (e ▸ le_rfl))) hβ

theorem vN_boxMM_empty_x (b : Bool) (v : Val) (ρ : ResU Lft) :
    ¬ vN (ℍ := ℍ) b boxMM (δ₂ x q) v ρ := vN_boxMM_empty no_between_x_q b v ρ

theorem vN_boxMM_empty_x' (b : Bool) (v : Val) (ρ : ResU Lft) :
    ¬ vN (ℍ := ℍ) b boxMM (δ₂ x' q) v ρ := vN_boxMM_empty no_between_x'_q b v ρ

/-- **`kU` is related at `x`**, vacuously: its argument type is empty. -/
theorem kU_related_x (v : Val) : vN (ℍ := ℍ) true kU (δ₂ x q) v PMap.empty :=
  closure_vacuous (fun v σ => vN_boxMM_empty_x true v σ) v _

/-- **The same-parents re-make preserves the relation at `kU`, at every resource**: an instance of
`vN_map` at the swap `x ↔ x′`. -/
theorem kU_swap (v : Val) (ρ : ResU Lft) :
    vN (ℍ := ℍ) true kU (δ₂ x' q) v (relRU π ρ) ↔ vN (ℍ := ℍ) true kU (δ₂ x q) v ρ := by
  have := vN_map (ℍ := ℍ) π true kU (δ₂ x q) v ρ
  rwa [δ₂_map, π_x, π_q] at this

theorem kU_related_x' (v : Val) : vN (ℍ := ℍ) true kU (δ₂ x' q) v PMap.empty := by
  have := (kU_swap (ℍ := ℍ) v PMap.empty).mpr (kU_related_x v)
  rwa [relRU_empty] at this

/-- At `x″`, beneath `r`, a valid borrow of a borrow inhabits `boxMM`: outer cell at `r`, inner
at `q`. -/
theorem vN_boxMM_x'' :
    ∃ v σ, vN (ℍ := ℍ) true boxMM (δ₂ x'' q) v σ ∧ σ.Valid := by
  refine ⟨.loc 0, ResU.single 0 (mmCell (ℍ := ℍ) (δ₂ x'' q) (.var 1) (δ₂_interp1 _ _) r q
    r_lt_q le_rfl 1), ?_, mmCell_valid _ _ _ _ _ _ _ (by decide)⟩
  rw [vN_box]
  refine ⟨x'', rfl, vN_mm (ℍ := ℍ) (δ₂ x'' q) (δ₂_interp0 _ _) (δ₂_interp1 _ _) x''_lt_r.le r_lt_q
    le_rfl 0 1, ?_⟩
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact not_le_of_gt x''_lt_r

/-- **The extra-parents re-make breaks the relation at `kU`**: the same closure, with the same
(empty) resource, is not related at `x″`. -/
theorem kU_not_related_x'' (v : Val) : ¬ vN (ℍ := ℍ) true kU (δ₂ x'' q) v PMap.empty := by
  obtain ⟨v', σ, hA, hσ⟩ := vN_boxMM_x'' (ℍ := ℍ)
  exact closure_not_related hA hσ (fun u ρ => vN_mm0_empty _ true u ρ) v

/-- (a) and (b) at `kU`, together. -/
theorem kU_convention (v : Val) :
    vN (ℍ := ℍ) true kU (δ₂ x q) v PMap.empty ∧
      vN (ℍ := ℍ) true kU (δ₂ x' q) v PMap.empty ∧
      ¬ vN (ℍ := ℍ) true kU (δ₂ x'' q) v PMap.empty :=
  ⟨kU_related_x v, kU_related_x' v, kU_not_related_x'' v⟩

end KU

/-! ### The `Imm 'x (Imm 'r U)` and `Mut 'x (Mut 'r 1)` closures -/

section KV
open W
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `Imm 'x (Imm 'r A)`. -/
abbrev immImm (A : VTy) : VTy := .imm (.var 0) (.imm (.var 1) A)

/-- **`Imm 'x (Imm 'r (U C))` is inhabited at every reading**: the inner cell at `{⊤}` is in the
stratum of any outer cell, and the payload `U C` is held in the observable view. -/
theorem vN_immImm_inhabited (α ρl : Lft) (hα : α ≠ ⊤) (C : CTy) (b : Bool) :
    ∃ v σ, vN (ℍ := ℍ) b (immImm (.thunk C)) (δ₂ α ρl) v σ := by
  have hin : ResU.InStratum {⊤} (PMap.empty : ResU Lft) := fun _ _ e => absurd e (by simp)
  have hne : ({⊤} : Finset Lft).Nonempty := Finset.singleton_nonempty _
  set inner : CellU Lft := CellU.immOf {⊤} hne .unit PMap.empty hin with hinner
  have hσ : (ResU.single 1 inner).InStratum {α} := by
    intro l ψ e
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    refine ⟨hne, fun t ht s hs => ?_⟩
    rw [Finset.mem_singleton.mp ht, Finset.mem_singleton.mp hs]
    exact lt_of_le_of_ne le_top hα
  refine ⟨.loc 0, ResU.single 0 (CellU.immOf {α} (Finset.singleton_nonempty _) (.loc 1)
    (ResU.single 1 inner) hσ), ?_⟩
  rw [vN_imm]
  refine ⟨α, rfl, 0, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  refine ⟨{α}, _, .loc 1, ResU.single 1 inner, hσ, fun m hm => (Finset.mem_singleton.mp hm) ▸ le_rfl,
    ?_, rfl⟩
  rw [vN_imm]
  refine ⟨ρl, rfl, 1, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  refine ⟨{⊤}, hne, .unit, PMap.empty, hin, fun m hm => (Finset.mem_singleton.mp hm) ▸ le_top,
    trivial, rfl⟩

/-- `Mut 'x (Mut 'r 1)`. -/
abbrev mutMut : VTy := .mut (.var 0) (.mut (.var 1) .unit)

/-- `U (Mut 'x (Mut 'r 1) ⊸ F (Mut 'x (Mut 'x 1)))`. -/
abbrev kV : VTy := .thunk (.arr mutMut (.ret mm0))

/-- **`Mut 'x (Mut 'r 1)` is empty when `r` is not a strict ancestor of `x`.** -/
theorem vN_mutMut_empty {α ρl : Lft} (hno : ¬ α < ρl) (v : Val) (σ : ResU Lft) :
    ¬ vN (ℍ := ℍ) true mutMut (δ₂ α ρl) v σ :=
  vN_mutMut_empty_of (δ₂_interp0 _ _) (δ₂_interp1 _ _) hno v σ

theorem kV_related_x (v : Val) : vN (ℍ := ℍ) true kV (δ₂ x r) v PMap.empty :=
  closure_vacuous (fun v σ => vN_mutMut_empty not_x_lt_r v σ) v _

theorem kV_swap (v : Val) (ρ : ResU Lft) :
    vN (ℍ := ℍ) true kV (δ₂ x' r) v (relRU π ρ) ↔ vN (ℍ := ℍ) true kV (δ₂ x r) v ρ := by
  have := vN_map (ℍ := ℍ) π true kV (δ₂ x r) v ρ
  rwa [δ₂_map, π_x, π_r] at this

theorem kV_related_x' (v : Val) : vN (ℍ := ℍ) true kV (δ₂ x' r) v PMap.empty := by
  have := (kV_swap (ℍ := ℍ) v PMap.empty).mpr (kV_related_x v)
  rwa [relRU_empty] at this

theorem kV_related_x'_direct (v : Val) : vN (ℍ := ℍ) true kV (δ₂ x' r) v PMap.empty :=
  closure_vacuous (fun v σ => vN_mutMut_empty not_x'_lt_r v σ) v _

/-- **Beneath `r`, the closure has to do real work and cannot**: not related at `x″`. -/
theorem kV_not_related_x'' (v : Val) : ¬ vN (ℍ := ℍ) true kV (δ₂ x'' r) v PMap.empty := by
  refine closure_not_related (v' := .loc 0) (σ := ResU.single 0 (mmCell (ℍ := ℍ) (δ₂ x'' r)
    (.var 1) (δ₂_interp1 _ _) x'' r x''_lt_r le_rfl 1)) ?_
    (mmCell_valid _ _ _ _ _ _ _ (by decide)) (fun u ρ => vN_mm0_empty _ true u ρ) v
  exact vN_mm (ℍ := ℍ) (δ₂ x'' r) (δ₂_interp0 _ _) (δ₂_interp1 _ _) le_rfl x''_lt_r le_rfl 0 1

end KV

/-! ### (c) The scheduler -/

section Scheduler
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem ownOnly_single_own (l : Loc) (v : Val) : OwnOnly (ResU.single l (CellU.own v : CellU L)) := by
  intro l' ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  rfl

theorem ownOnly_compS {ρ₁ ρ₂ ρ : ResU L} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : OwnOnly ρ₁)
    (h₂ : OwnOnly ρ₂) : OwnOnly ρ := by
  intro l ψ e
  have hl := hc.2 l
  cases e₁ : ρ₁.get l with
  | none =>
      cases e₂ : ρ₂.get l with
      | none => rw [e₁, e₂, e] at hl; cases hl
      | some ψ₂ =>
          rw [e₁, e₂, e] at hl
          cases (Option.some.inj hl)
          exact h₂ l _ e₂
  | some ψ₁ =>
      cases e₂ : ρ₂.get l with
      | none =>
          rw [e₁, e₂, e] at hl
          cases (Option.some.inj hl)
          exact h₁ l _ e₁
      | some ψ₂ =>
          rw [e₁, e₂, e] at hl
          obtain ⟨ψ', hψ', hC⟩ := hl
          have := hC.1.1
          rw [h₁ l ψ₁ e₁] at this
          cases this

/-- **A closed package of owned cells is in every stratum**: a task that borrowed only its own
local (`S = ∅`) is, closed, an owned value to every `Mut 'q`. -/
theorem closed_inStratum {p : Pkg L} {ρ : ResU L} (hc : p.Closed ρ) (h₁ : OwnOnly p.σu)
    (h₂ : OwnOnly p.ρw) (S : Finset L) : ρ.InStratum S := by
  obtain ⟨ρ₁, hc₁, hc₂⟩ := hc
  exact (ownOnly_compS hc₂ (ownOnly_compS hc₁ (ownOnly_single_own _ _) h₁) h₂).inStratum S

/-- Any family of such packages meets the `Mut` clause's stratification at every lifetime. -/
theorem closed_family_stratified (P : Val → WPropN L)
    (hP : ∀ v ρ, P v ρ → ∃ p : Pkg L, p.Closed ρ ∧ OwnOnly p.σu ∧ OwnOnly p.ρw) (b : L) :
    ∀ v ρ, P v ρ → ρ.InStratum {b} := by
  intro v ρ h
  obtain ⟨p, hc, h₁, h₂⟩ := hP v ρ h
  exact closed_inStratum hc h₁ h₂ {b}

/-- Stratification is closed under `●`. -/
theorem inStratum_compS {ρ₁ ρ₂ ρ : ResU L} (hc : ResU.CompS ρ₁ ρ₂ ρ) {S : Finset L}
    (h₁ : ρ₁.InStratum S) (h₂ : ρ₂.InStratum S) : ρ.InStratum S := by
  intro l ψ e
  have hl := hc.2 l
  cases e₁ : ρ₁.get l with
  | none =>
      cases e₂ : ρ₂.get l with
      | none => rw [e₁, e₂, e] at hl; cases hl
      | some ψ₂ =>
          rw [e₁, e₂, e] at hl
          cases (Option.some.inj hl)
          exact h₂ l _ e₂
  | some ψ₁ =>
      cases e₂ : ρ₂.get l with
      | none =>
          rw [e₁, e₂, e] at hl
          cases (Option.some.inj hl)
          exact h₁ l _ e₁
      | some ψ₂ =>
          rw [e₁, e₂, e] at hl
          obtain ⟨ψ', hψ', ⟨hk₁, hk₂, -, -⟩, hk, -, -, hlts⟩ := hl
          cases Option.some.inj hψ'
          have a₁ := h₁ l ψ₁ e₁
          have a₂ := h₂ l ψ₂ e₂
          cases ψ₁ with
          | own _ => cases hk₁
          | «mut» _ => cases hk₁
          | imm i₁ =>
            cases ψ₂ with
            | own _ => cases hk₂
            | «mut» _ => cases hk₂
            | imm i₂ =>
              cases ψ with
              | own _ => cases hk
              | «mut» _ => cases hk
              | imm i =>
                change i.ls = i₁.ls ∪ i₂.ls at hlts
                refine ⟨i.hne, fun t ht s hs => ?_⟩
                rw [hlts] at ht
                rcases Finset.mem_union.mp ht with ht | ht
                · exact a₁.2 t ht s hs
                · exact a₂.2 t ht s hs

/-- `Ref 1 ⊗ Mut 's 1`: an owned cell and a captured borrow at `'s`. -/
abbrev captured : VTy := .tensor (.ref .unit) (.mut (.var 1) .unit)

/-- `Mut 'q (Ref 1 ⊗ Mut 's 1)`: such a package stored under a lent cell at `'q`. -/
abbrev storeCaptured : VTy := .mut (.var 0) captured

theorem vN_ref_unit (δ : LSubN L) (ℓ : Loc) :
    vN (ℍ := ℍ) true (.ref .unit) δ (.loc ℓ) (ResU.single ℓ (.own .unit)) := by
  rw [vN_ref]
  refine ⟨ℓ, .unit, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  exact ⟨ResU.single ℓ (.own .unit), PMap.empty, comp_empty_right _ _ _, rfl,
    vN_unit_empty_iff.mpr ⟨rfl, rfl⟩⟩

theorem vN_captured (δ : LSubN L) {σl : L} (hs : interpN δ (.var 1) = some σl) {b : L}
    (hb : σl ≤ b) {ℓ ℓ' : Loc} (hl : ℓ ≠ ℓ') :
    vN (ℍ := ℍ) true captured δ (.pair (.loc ℓ) (.loc ℓ'))
      (ResU.pair ℓ (.own .unit) ℓ' (unitCell (ℍ := ℍ) δ b)) := by
  rw [vN_tensor]
  refine ⟨.loc ℓ, .loc ℓ', sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  exact ⟨_, _, comp_single_single _ _ hl _ _, vN_ref_unit δ ℓ, vN_mut_unit δ hs hb ℓ'⟩

/-- Every value of `Ref 1 ⊗ Mut 's 1` lies in `Res_{b}` when `b < @'s`. -/
theorem vN_captured_inStratum (δ : LSubN L) {σl b : L} (hs : interpN δ (.var 1) = some σl)
    (hb : b < σl) (u : Val) (σ : ResU L) (h : vN (ℍ := ℍ) true captured δ u σ) :
    σ.InStratum {b} := by
  rw [vN_tensor] at h
  obtain ⟨v₁, v₂, hsep⟩ := h
  obtain ⟨-, σ₁, σ₂, hc, h₁, h₂⟩ := sepN_pure_iff.mp hsep
  refine inStratum_compS hc ?_ (vN_mut_unit_inStratum hs hb v₂ σ₂ h₂)
  rw [vN_ref] at h₁
  obtain ⟨ℓ, v', hsep₁⟩ := h₁
  obtain ⟨-, τ₁, τ₂, hc₁, hτ₁, hτ₂⟩ := sepN_pure_iff.mp hsep₁
  obtain ⟨rfl, -⟩ := vN_unit_empty_iff.mp hτ₂
  refine inStratum_compS hc₁ ?_ (fun _ _ e => absurd e (by simp))
  rw [hτ₁]
  exact (ownOnly_single_own ℓ v').inStratum {b}

/-- **A package that captured a borrow at `s` can be stored under `Mut 'q` exactly when `s`
strictly outlives `q`**: `Mut 'q (Ref 1 ⊗ Mut 's 1)` is inhabited iff `q < s`. -/
theorem vN_store_captured_iff (q s : L) :
    (∃ v ρ, vN (ℍ := ℍ) true storeCaptured (⟨[(0, q), (1, s)]⟩ : LSubN L) v ρ) ↔ q < s := by
  constructor
  · rintro ⟨v, ρ, h⟩
    obtain ⟨α, hα, ℓ, -, b, u, σ, h₁, hw, hαb, hstr, -⟩ := vN_mut_cell h
    have hαq : q = α := Option.some.inj hα
    subst hαq
    have hin := hstr _ _ (vN_captured (ℍ := ℍ) (⟨[(0, q), (1, s)]⟩ : LSubN L) rfl (le_refl s)
      (ℓ := 0) (ℓ' := 1) (by decide))
    have := hin 1 _ (ResU.pair_get_right _ _ (by decide))
    exact lt_of_le_of_lt hαb (above_singleton_singleton.mp this)
  · intro hqs
    set δ : LSubN L := ⟨[(0, q), (1, s)]⟩
    have hs : interpN δ (.var 1) = some s := rfl
    have hw : vN (ℍ := ℍ) true captured δ (.pair (.loc 0) (.loc 1))
        (ResU.pair 0 (.own .unit) 1 (unitCell (ℍ := ℍ) δ s)) :=
      vN_captured δ hs (le_refl s) (by decide)
    have hσ : (ResU.pair 0 (.own .unit) 1 (unitCell (ℍ := ℍ) δ s)).InStratum {q} :=
      vN_captured_inStratum δ hs hqs _ _ hw
    refine ⟨.loc 2, ResU.single 2 (CellU.mutOf q _ _ hσ (vN (ℍ := ℍ) true captured δ) hw), ?_⟩
    rw [vN_mut]
    refine ⟨q, rfl, 2, sepN_pure_iff.mpr ⟨rfl, q, _, _, hσ, hw, le_rfl,
      vN_captured_inStratum δ hs hqs, rfl⟩⟩

/-- **`S = ∅`: a package of owned cells is storable under every `Mut 'q`**: `Mut 'q (Ref 1)` is
inhabited at every `q`, its payload in every stratum. -/
theorem vN_store_owned (q : L) :
    ∃ v ρ, vN (ℍ := ℍ) true (.mut (.var 0) (.ref .unit)) (⟨[(0, q)]⟩ : LSubN L) v ρ := by
  set δ : LSubN L := ⟨[(0, q)]⟩
  have hw := vN_ref_unit (ℍ := ℍ) δ 1
  have hσ : (ResU.single 1 (.own .unit) : ResU L).InStratum {q} :=
    (ownOnly_single_own 1 .unit).inStratum {q}
  refine ⟨.loc 0, ResU.single 0 (CellU.mutOf q _ _ hσ (vN (ℍ := ℍ) true (.ref .unit) δ) hw), ?_⟩
  rw [vN_mut]
  refine ⟨q, rfl, 0, sepN_pure_iff.mpr ⟨rfl, q, _, _, hσ, hw, le_rfl, ?_, rfl⟩⟩
  intro u σ h
  rw [vN_ref] at h
  obtain ⟨ℓ, v', hsep⟩ := h
  obtain ⟨-, τ₁, τ₂, hc, hτ₁, hτ₂⟩ := sepN_pure_iff.mp hsep
  obtain ⟨rfl, -⟩ := vN_unit_empty_iff.mp hτ₂
  refine inStratum_compS hc ?_ (fun _ _ e => absurd e (by simp))
  rw [hτ₁]
  exact (ownOnly_single_own ℓ v').inStratum {q}

end Scheduler

/-! ### The self-borrow, opened and re-opened -/

section SelfBorrow
open W
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The minimal self-borrowing package: `c` owns `()`, the contents are the borrow of `c`. -/
def selfPkg (c : Loc) : Pkg Lft := ⟨c, .unit, PMap.empty, .loc c, PMap.empty⟩

/-- `'x ↦ y`, the only variable. -/
def δx (y : Lft) : LSubN Lft := ⟨[(0, y)]⟩

/-- **Opened at `x`, the package is related at `Mut 'x 1`.** -/
theorem selfBorrow_related (c : Loc) :
    ∃ ρ, (selfPkg c).Opens (vN (ℍ := ℍ) true .unit ⟨[]⟩) (x : Lft) ρ ∧
      vN (ℍ := ℍ) true (.mut (.var 0) .unit) ((⟨[]⟩ : LSubN Lft).extend 0 (x : Lft))
        (selfPkg c).w ρ := by
  have hin : ResU.InStratum {(x : Lft)} (PMap.empty : ResU Lft) := fun _ _ e => absurd e (by simp)
  have hw : vN (ℍ := ℍ) true .unit (⟨[]⟩ : LSubN Lft) Val.unit PMap.empty :=
    vN_unit_empty_iff.mpr ⟨rfl, rfl⟩
  refine ⟨ResU.single c (CellU.mutOf (x : Lft) .unit PMap.empty hin _ hw),
    ⟨hin, hw, comp_empty_right _ _ _⟩, ?_⟩
  rw [vN_mut]
  refine ⟨x, rfl, c, sepN_pure_iff.mpr ⟨rfl, ?_⟩⟩
  refine ⟨x, .unit, PMap.empty, hin, ?_, le_rfl, ?_, ?_⟩
  · exact vN_unit_empty_iff.mpr ⟨rfl, rfl⟩
  · intro u σ h
    obtain ⟨rfl, -⟩ := vN_unit_empty_iff.mp h
    exact hin
  · congr 1

/-- **Re-opened at `x′`, it is related too**: `reopen_swap`, every hypothesis discharged. -/
theorem selfBorrow_reopen (c : Loc) :
    ∃ ρ, (selfPkg c).Opens (vN (ℍ := ℍ) true .unit ⟨[]⟩) (x' : Lft) ρ ∧
      vN (ℍ := ℍ) true (.mut (.var 0) .unit) ((⟨[]⟩ : LSubN Lft).extend 0 (x' : Lft))
        (selfPkg c).w ρ := by
  have hfix : (selfPkg c).FixedBy π (vN (ℍ := ℍ) true .unit ⟨[]⟩) :=
    fixedBy_of_ownOnly π (fun _ _ e => absurd e (by simp [selfPkg]))
      (fun _ _ e => absurd e (by simp [selfPkg])) rfl .unit
  have hav : ∀ y : Atom, (⟨[]⟩ : LSubN Lft).Avoids y := fun _ p hp => absurd hp (by simp)
  exact (reopen_swap sameParents hfix (hav x) (hav x') 0 true _).mpr (selfBorrow_related c)

end SelfBorrow

/-! ### The move is the re-make -/

section MoveRemake
variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The image of the relation is the relation at the moved reading. -/
theorem img_vN (π : L ≃o L) (b : Bool) (A : VTy) (δ : LSubN L) :
    img π (vN (ℍ := ℍ) b A δ) = vN (ℍ := ℍ) b A (δ.map π) :=
  img_eq_of π fun u σ => vN_map π b A δ u σ

theorem relU_unitCell (π : L ≃o L) (δ : LSubN L) (b : L) :
    relU π (unitCell (ℍ := ℍ) δ b) = unitCell (ℍ := ℍ) (δ.map π) (π b) := by
  unfold unitCell
  refine (relU_mutOf π _ _ _ _ _ _).trans ?_
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · rw [CellU.wit_mutOf, CellU.wit_mutOf, relRU_empty]
  · rfl
  · rw [CellU.pu_mutOf, CellU.pu_mutOf, img_vN]

/-- **Moving a borrow of a borrow by an automorphism is re-making it at the moved lifetimes**:
the moved outer cell stores the image of `𝒱⟦Mut 'c 1⟧δ`, which is `𝒱⟦Mut 'c 1⟧(π·δ)`, what a cell
made afresh stores. On Core's carrier the two differ (`DenseCarrier`'s `remake_not_move`). -/
theorem move_eq_remake (π : L ≃o L) (δ : LSubN L) (c : Lifetime.Life) {γ : L}
    (hγ : interpN δ c = some γ) (b₁ b₂ : L) (h₁ : b₁ < γ) (h₂ : γ ≤ b₂) (ℓ' : Loc) :
    relU π (mmCell (ℍ := ℍ) δ c hγ b₁ b₂ h₁ h₂ ℓ') =
      mmCell (ℍ := ℍ) (δ.map π) c (by rw [interpN_map, hγ]; rfl) (π b₁) (π b₂)
        (π.lt_iff_lt.mpr h₁) (π.le_iff_le.mpr h₂) ℓ' := by
  unfold mmCell
  refine (relU_mutOf π _ _ _ _ _ _).trans ?_
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · rw [CellU.wit_mutOf, CellU.wit_mutOf, relRU_single, relU_unitCell]
  · rfl
  · rw [CellU.pu_mutOf, CellU.pu_mutOf, img_vN]

theorem mmCell_congr {δ δ' : LSubN L} {c : Lifetime.Life} {γ γ' : L}
    {hγ : interpN δ c = some γ} {hγ' : interpN δ' c = some γ'} {b₁ b₁' b₂ b₂' : L}
    {h₁ : b₁ < γ} {h₂ : γ ≤ b₂} {h₁' : b₁' < γ'} {h₂' : γ' ≤ b₂'} (ℓ' : Loc)
    (eδ : δ = δ') (e₁ : b₁ = b₁') (e₂ : b₂ = b₂') :
    mmCell (ℍ := ℍ) δ c hγ b₁ b₂ h₁ h₂ ℓ' = mmCell (ℍ := ℍ) δ' c hγ' b₁' b₂' h₁' h₂' ℓ' := by
  subst eδ; subst e₁; subst e₂
  obtain rfl : γ = γ' := Option.some.inj (hγ.symm.trans hγ')
  rfl

end MoveRemake

section MoveRemakeW
open W
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The borrow of a borrow at `x` (outer) and `q` (inner), related at `Mut 'a (Mut 'b 1)` at
`'a ↦ x`, `'b ↦ q`. -/
def mmAt (y : Atom) (hy : (y : Lft) < q) : ResU Lft :=
  ResU.single 0 (mmCell (ℍ := ℍ) (δ₂ y q) (.var 1) (δ₂_interp1 _ _) y q hy le_rfl 1)

/-- **`not_reslotInvV`'s configuration, moved by the swap, is related, and is the re-make at
`x′`.** -/
theorem mm_swap_related :
    relRU π (mmAt (ℍ := ℍ) x x_lt_q) = mmAt (ℍ := ℍ) x' x'_lt_q ∧
      vN (ℍ := ℍ) true mm (δ₂ x' q) (.loc 0) (relRU π (mmAt (ℍ := ℍ) x x_lt_q)) := by
  have hrel : vN (ℍ := ℍ) true mm (δ₂ x q) (.loc 0) (mmAt (ℍ := ℍ) x x_lt_q) :=
    vN_mm (ℍ := ℍ) (δ₂ x q) (δ₂_interp0 _ _) (δ₂_interp1 _ _) le_rfl x_lt_q le_rfl 0 1
  have hmoved := (vN_map (ℍ := ℍ) π true mm (δ₂ x q) (.loc 0) _).mpr hrel
  rw [δ₂_map, π_x, π_q] at hmoved
  refine ⟨?_, hmoved⟩
  unfold mmAt
  rw [relRU_single, move_eq_remake]
  congr 1
  exact mmCell_congr 1 (by rw [δ₂_map, π_x, π_q]) π_x π_q

/-- **The two readings of `[α]P` differ in a partial order**: a cell at `x′`, incomparable with
`x`, survives the end of `x` and is not in `Res_{x}`. -/
theorem split_is_real :
    (ResU.single 0 (unitCell (ℍ := ℍ) (δ₂ x q) (x' : Lft))).Survives (x : Lft) ∧
      ¬ (ResU.single 0 (unitCell (ℍ := ℍ) (δ₂ x q) (x' : Lft))).InStratum {(x : Lft)} := by
  have hxx' : ¬ (x' : Lft) ≤ x := by
    intro h
    rcases WithTop.coe_le_coe.mp h with e | hb
    · exact x_ne_x' e.symm
    · rw [below_x'_iff] at hb; exact q_ne_x hb.symm
  refine ⟨fun l ψ e => ?_, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    exact hxx'
  · have := h 0 _ (ResU.single_get_self _ _)
    have hlt : (x : Lft) < x' := above_singleton_singleton.mp this
    have hb : Atom.Below x x' := WithTop.coe_lt_coe.mp hlt
    rw [below_x_iff] at hb
    exact absurd hb (by intro e; cases e)

end MoveRemakeW

end Nominal

end
