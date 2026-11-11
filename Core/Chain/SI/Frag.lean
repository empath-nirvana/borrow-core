import Core.DivRuntime
import Core.Steps

/-!
# Step-indexed relation, resources: exact fragments of the memory

A thread's resource is a fragment `σ : Heap` of the memory: the cells it owns, each with its
contents. Fragments compose by disjoint union (`Disj`, `un`). Ownership is exact: a predicate over
fragments says which cells are owned, not which are at least owned, so nothing is discarded
silently. This is LinearActris's `aProp` at our machine, with `Cell(ℓ) ↦ inr v` the only edge
label, the thread the only node that owns, and no step index in the fragment itself.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.BoLo (Heap)

/-- Two fragments own no common cell. -/
def Disj (a b : Heap) : Prop := ∀ ℓ, a ℓ = none ∨ b ℓ = none

/-- The union of two fragments, the left one first where both hold a cell. -/
def un (a b : Heap) : Heap := fun ℓ =>
  match a ℓ with
  | some v => some v
  | none => b ℓ

/-- The empty fragment. -/
def emp : Heap := fun _ => none

/-- The fragment owning one cell. -/
def single (ℓ : Loc) (v : Val) : Heap := fun k => if k = ℓ then some v else none

@[simp] theorem un_apply_some {a b : Heap} {ℓ : Loc} {v : Val} (h : a ℓ = some v) :
    un a b ℓ = some v := by simp [un, h]

@[simp] theorem un_apply_none {a b : Heap} {ℓ : Loc} (h : a ℓ = none) : un a b ℓ = b ℓ := by
  simp [un, h]

@[simp] theorem emp_apply (ℓ : Loc) : emp ℓ = none := rfl

@[simp] theorem single_same (ℓ : Loc) (v : Val) : single ℓ v ℓ = some v := by simp [single]

@[simp] theorem single_other {ℓ k : Loc} (v : Val) (h : k ≠ ℓ) : single ℓ v k = none := by
  simp [single, h]

theorem Disj.symm {a b : Heap} (h : Disj a b) : Disj b a := fun ℓ => (h ℓ).symm

theorem disj_comm {a b : Heap} : Disj a b ↔ Disj b a := ⟨Disj.symm, Disj.symm⟩

@[simp] theorem un_emp_left (a : Heap) : un emp a = a := by funext ℓ; simp [un]

@[simp] theorem un_emp_right (a : Heap) : un a emp = a := by
  funext ℓ; simp only [un]; split <;> simp_all

@[simp] theorem disj_emp_left (a : Heap) : Disj emp a := fun _ => .inl rfl

@[simp] theorem disj_emp_right (a : Heap) : Disj a emp := fun _ => .inr rfl

theorem un_comm {a b : Heap} (h : Disj a b) : un a b = un b a := by
  funext ℓ
  rcases h ℓ with h | h <;> simp only [un] <;> split <;> split <;> simp_all

theorem un_assoc (a b c : Heap) : un (un a b) c = un a (un b c) := by
  funext ℓ
  simp only [un]
  split <;> split <;> simp_all

theorem disj_un_left {a b c : Heap} : Disj (un a b) c ↔ Disj a c ∧ Disj b c := by
  constructor
  · intro h
    refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩
    · rcases h ℓ with h' | h'
      · simp only [un] at h'; split at h' <;> simp_all
      · exact .inr h'
    · rcases h ℓ with h' | h'
      · simp only [un] at h'; split at h' <;> simp_all
      · exact .inr h'
  · rintro ⟨h₁, h₂⟩ ℓ
    rcases h₁ ℓ with h₁ | h₁
    · rcases h₂ ℓ with h₂ | h₂
      · exact .inl (by simp [un, h₁, h₂])
      · exact .inr h₂
    · exact .inr h₁

theorem disj_un_right {a b c : Heap} : Disj a (un b c) ↔ Disj a b ∧ Disj a c := by
  rw [disj_comm, disj_un_left, disj_comm (a := b), disj_comm (a := c)]

/-- Regrouping `a ∪ (b ∪ c)` as `b ∪ (a ∪ c)`. -/
theorem un_left_comm {a b c : Heap} (h : Disj a b) : un a (un b c) = un b (un a c) := by
  rw [← un_assoc, un_comm h, un_assoc]

theorem single_disj {ℓ : Loc} {v : Val} {a : Heap} : Disj (single ℓ v) a ↔ a ℓ = none := by
  constructor
  · intro h
    rcases h ℓ with h | h
    · simp at h
    · exact h
  · intro h k
    by_cases hk : k = ℓ
    · subst hk; exact .inr h
    · exact .inl (single_other v hk)

/-- An allocation at a location free in `a ∪ f`: the cell joins the owned part. -/
theorem upd_un {a f : Heap} {ℓ : Loc} (v : Val) (h : un a f ℓ = none) :
    (un a f).upd ℓ v = un (un (single ℓ v) a) f := by
  funext k
  by_cases hk : k = ℓ
  · subst hk; simp [un]
  · simp [un, single, BoLo.Heap.upd, hk]

/-- A release of an owned cell: it leaves the owned part. -/
theorem del_un {a f : Heap} {ℓ : Loc} {u : Val} (hd : Disj (un (single ℓ u) a) f) (ha : a ℓ = none) :
    (un (un (single ℓ u) a) f).del ℓ = un a f := by
  funext k
  by_cases hk : k = ℓ
  · subst hk
    have hf : f k = none := by
      rcases hd k with h | h
      · simp [un] at h
      · exact h
    simp [BoLo.Heap.del, un, ha, hf]
  · simp [un, single, BoLo.Heap.del, hk]

theorem un_eq_none {a b : Heap} {ℓ : Loc} : un a b ℓ = none ↔ a ℓ = none ∧ b ℓ = none := by
  simp only [un]; split <;> simp_all

/-- A fragment's union with a frame determines it. -/
theorem un_cancel_right {a a' f : Heap} (h : Disj a f) (h' : Disj a' f) (he : un a f = un a' f) :
    a = a' := by
  funext ℓ
  have e := congrFun he ℓ
  cases ha : a ℓ with
  | none =>
      cases ha' : a' ℓ with
      | none => rfl
      | some v' =>
          rcases h' ℓ with h₂ | h₂
          · rw [ha'] at h₂; cases h₂
          · rw [un_apply_none ha, un_apply_some ha', h₂] at e; cases e
  | some v =>
      cases ha' : a' ℓ with
      | none =>
          rcases h ℓ with h₂ | h₂
          · rw [ha] at h₂; cases h₂
          · rw [un_apply_some ha, un_apply_none ha', h₂] at e; cases e
      | some v' => rw [un_apply_some ha, un_apply_some ha'] at e; exact e

/-! ### Finite memories -/

theorem fd_upd {μ : Heap} (h : FinDom μ) (ℓ : Loc) (v : Val) : FinDom (μ.upd ℓ v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨ℓ :: d, fun k hk => ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ]; exact List.mem_cons_self
  · rw [BoCa.BoLo.Heap.upd_other hkℓ] at hk; exact List.mem_cons_of_mem _ (hd k hk)

theorem fd_del {μ : Heap} (h : FinDom μ) (ℓ : Loc) : FinDom (μ.del ℓ) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun k hk => hd k ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ, BoCa.BoLo.Heap.del_same] at hk; exact absurd rfl hk
  · rwa [BoCa.BoLo.Heap.del_other hkℓ] at hk

theorem fd_fill {μ : Heap} (h : FinDom μ) (ℓ : Loc) (n : ℕ) (v : Val) :
    FinDom (μ.fill ℓ n v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨List.range' ℓ n ++ d, fun k hk => ?_⟩
  unfold BoCa.BoLo.Heap.fill at hk
  split at hk
  · rename_i hr
    exact List.mem_append_left _ (List.mem_range'_1.2 ⟨hr.1, hr.2⟩)
  · exact List.mem_append_right _ (hd k hk)

/-- The copy step writes only cells of its destination range.  `[spec §74]` -/
theorem fd_copyHeap {μ : Heap} (h : FinDom μ) (ℓd : Loc) (nd di : UInt32) (ℓs : Loc)
    (ns si len : UInt32) : FinDom (BoCa.BoLo.copyHeap μ ℓd nd di ℓs ns si len) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨List.range' (ℓd + di.toNat) len.toNat ++ d, fun k hk => ?_⟩
  unfold BoCa.BoLo.copyHeap at hk
  split at hk
  · simp only [BoCa.BoLo.Heap.copy] at hk
    split at hk
    · rename_i hr
      exact List.mem_append_left _ (List.mem_range'_1.2 ⟨hr.1, hr.2⟩)
    · exact List.mem_append_right _ (hd k hk)
  · exact List.mem_append_right _ (hd k hk)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem fd_step1 {μ μ' : Heap} {e e' : Expr} (h : BoLo.Step1 (ℍ := ℍ) μ e μ' e')
    (hf : FinDom μ) : FinDom μ' := by
  obtain ⟨_, _, _, -, -, hh⟩ := h
  cases hh <;>
    first
    | exact hf
    | exact fd_upd hf _ _
    | exact fd_del hf _
    | exact fd_fill hf _ _ _
    | exact fd_copyHeap hf _ _ _ _ _ _ _

theorem fd_empty : FinDom emp := ⟨[], fun _ h => absurd rfl h⟩

theorem fd_un_left {a b : Heap} (h : FinDom (un a b)) : FinDom a := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun k hk => hd k ?_⟩
  cases ha : a k with
  | none => exact absurd ha hk
  | some v => rw [un_apply_some ha]; simp

theorem fd_un {a b : Heap} (ha : FinDom a) (hb : FinDom b) : FinDom (un a b) := by
  obtain ⟨d, hd⟩ := ha
  obtain ⟨d', hd'⟩ := hb
  refine ⟨d ++ d', fun k hk => ?_⟩
  cases hak : a k with
  | some v => exact List.mem_append_left _ (hd k (by simp [hak]))
  | none =>
      rw [un_apply_none hak] at hk
      exact List.mem_append_right _ (hd' k hk)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
