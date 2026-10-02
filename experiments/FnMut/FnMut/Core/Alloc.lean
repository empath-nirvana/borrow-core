import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine
import Support.Dynamics.Arrays
import Support.Model.Prelude

/-!
# Core — allocators and allocator runs  `[spec §13]`

`alloc↦` and `tab↦` choose any free location.  An allocator fixes the choice: at the `k`-th
allocation of a run, from memory `μ`, a block of `n` cells at `pick k μ n`, free whenever `μ` has
finite domain.  An allocator run (`ARun`) is a run whose allocations are the allocator's and
whose other steps allocate nothing (`Expr.allocs`).  `wpTS` asks for an allocator run at every
allocator, which covers every run of the machine (`Core/Demonic.lean`).

The constructions `wpTS`'s rules build runs with are here: the empty run, a step that allocates
nothing (`Step1N`), an allocation or a block allocation at the allocator's location, plugging
into an evaluation context, and concatenation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.BoLo
open BoCa

/-- The redexes that choose a location: `alloc v` and `tab v`.  `[spec §13]` -/
def _root_.BoCa.Expr.allocs : Expr → Bool
  | .app (.prim .alloc) _ => true
  | .app (.prim .tab) _ => true
  | _ => false

/-- An allocator: at the `k`-th allocation from memory `μ`, a block of `n` cells at `pick k μ n`,
free in every memory of finite domain.  `[spec §13]` -/
structure Alloc where
  pick : Nat → Heap → Nat → Loc
  fresh : ∀ k (μ : Heap) n, Fig16.FinDom μ → ∀ i, i < n → μ (pick k μ n + i) = none

/-- A memory of finite domain misses every location from one past its largest. -/
theorem finDom_block {μ : Heap} (h : Fig16.FinDom μ) : ∃ ℓ : Loc, ∀ j, μ (ℓ + j) = none := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.foldr max 0 + 1, fun j => ?_⟩
  by_contra hne
  have hmem := hd _ hne
  have hub : ∀ (t : List Nat) (l : Nat), l ∈ t → l ≤ t.foldr max 0 := by
    intro t
    induction t with
    | nil => intro l hl; exact absurd hl (by simp)
    | cons a t ih =>
        intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih l hl) (Nat.le_max_right _ _)
  have := hub d _ hmem
  omega

open Classical in
/-- The least location starting a free block of `n` cells, at every count.  `[spec §13]` -/
def Alloc.leastFree : Alloc where
  pick _ μ n := if h : ∃ ℓ : Loc, ∀ i, i < n → μ (ℓ + i) = none then Nat.find h else 0
  fresh _ μ n hfin := by
    obtain ⟨ℓ, hℓ⟩ := finDom_block hfin
    have h : ∃ ℓ : Loc, ∀ i, i < n → μ (ℓ + i) = none := ⟨ℓ, fun i _ => hℓ i⟩
    simp only [dif_pos h]
    exact Nat.find_spec h

/-- A head step under the allocator `A`, from allocation count `k`: a head step that allocates
nothing, or an allocation at `A`'s location.  `[spec §13]` -/
inductive AHead (A : Alloc) : Nat → Heap → Expr → Nat → Heap → Expr → Prop where
  | det {k : Nat} {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
      (hn : a.allocs = false) : AHead A k μ a k μ' a'
  | alloc (k : Nat) (μ : Heap) (v : Val) (h : μ (A.pick k μ 1) = none) :
      AHead A k μ (.app (.val (.prim .alloc)) (.val v)) (k + 1)
        (μ.upd (A.pick k μ 1) v) (.val (.loc (A.pick k μ 1)))
  | tab (k : Nat) (μ : Heap) (c : UInt32) (f : Val)
      (h : ∀ i, i < (arrLen c).toNat → μ (A.pick k μ (arrLen c).toNat + i) = none) :
      AHead A k μ (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f))) (k + 1)
        (μ.fill (A.pick k μ (arrLen c).toNat) (arrLen c).toNat .unit)
        (tabFill f (A.pick k μ (arrLen c).toNat) (arrLen c) 0 (arrLen c).toNat)

/-- A step under the allocator: an `AHead` in an evaluation context.  `[spec §13]` -/
def AStep1 (A : Alloc) (k : Nat) (μ : Heap) (e : Expr) (k' : Nat) (μ' : Heap) (e' : Expr) :
    Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ AHead (ℍ := ℍ) A k μ a k' μ' a'

/-- A run under the allocator `A`, from allocation count `k` to `k'`.  `[spec §13]` -/
inductive ARun (A : Alloc) : Nat → Heap → Expr → Nat → Heap → Expr → Prop where
  | refl (k : Nat) (μ : Heap) (e : Expr) : ARun A k μ e k μ e
  | more {k k₁ k' : Nat} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : AStep1 (ℍ := ℍ) A k μ e k₁ μ₁ e₁) (t : ARun A k₁ μ₁ e₁ k' μ' e') :
      ARun A k μ e k' μ' e'

/-- A step that allocates nothing: a head step, `alloc` and `tab` excluded, in an evaluation
context.  `[spec §13]` -/
def Step1N (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head (ℍ := ℍ) μ a μ' a' ∧
    a.allocs = false

theorem AHead.toHead {A : Alloc} {k k' : Nat} {μ μ' : Heap} {a a' : Expr}
    (h : AHead (ℍ := ℍ) A k μ a k' μ' a') : Head (ℍ := ℍ) μ a μ' a' := by
  cases h with
  | det h _ => exact h
  | alloc v h => exact .alloc _ v _ h
  | tab c f h => exact .tab _ c f _ h

theorem AStep1.toStep1 {A : Alloc} {k k' : Nat} {μ μ' : Heap} {e e' : Expr}
    (h : AStep1 (ℍ := ℍ) A k μ e k' μ' e') : Step1 (ℍ := ℍ) μ e μ' e' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  exact ⟨K, a, a', rfl, rfl, hh.toHead⟩

theorem AStep1.plug {A : Alloc} {k k' : Nat} {μ μ' : Heap} {e e' : Expr} (K : Kont)
    (h : AStep1 (ℍ := ℍ) A k μ e k' μ' e') :
    AStep1 (ℍ := ℍ) A k μ (K.plug e) k' μ' (K.plug e') := by
  obtain ⟨K', a, a', rfl, rfl, hh⟩ := h
  exact ⟨K.comp K', a, a', (Kont.plug_comp K K' a).symm, (Kont.plug_comp K K' a').symm, hh⟩

theorem Step1N.head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (hn : a.allocs = false) : Step1N (ℍ := ℍ) μ a μ' a' :=
  ⟨.hole, a, a', rfl, rfl, h, hn⟩

theorem Step1N.plug {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Step1N (ℍ := ℍ) μ e μ' e') :
    Step1N (ℍ := ℍ) μ (K.plug e) μ' (K.plug e') := by
  obtain ⟨K', a, a', rfl, rfl, hh, hn⟩ := h
  exact ⟨K.comp K', a, a', (Kont.plug_comp K K' a).symm, (Kont.plug_comp K K' a').symm, hh, hn⟩

theorem Step1N.toStep1 {μ μ' : Heap} {e e' : Expr} (h : Step1N (ℍ := ℍ) μ e μ' e') :
    Step1 (ℍ := ℍ) μ e μ' e' := by
  obtain ⟨K, a, a', rfl, rfl, hh, -⟩ := h
  exact ⟨K, a, a', rfl, rfl, hh⟩

/-- A step that allocates nothing is a step under every allocator, at every count. -/
theorem Step1N.toAStep1 {μ μ' : Heap} {e e' : Expr} (h : Step1N (ℍ := ℍ) μ e μ' e') (A : Alloc)
    (k : Nat) : AStep1 (ℍ := ℍ) A k μ e k μ' e' := by
  obtain ⟨K, a, a', rfl, rfl, hh, hn⟩ := h
  exact ⟨K, a, a', rfl, rfl, .det hh hn⟩

namespace ARun

variable {A : Alloc}

theorem toSteps {k k' : Nat} {μ μ' : Heap} {e e' : Expr} (h : ARun (ℍ := ℍ) A k μ e k' μ' e') :
    Steps (ℍ := ℍ) μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.toStep1 ih

theorem trans {k k₁ k' : Nat} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
    (h₁ : ARun (ℍ := ℍ) A k μ e k₁ μ₁ e₁) (h₂ : ARun (ℍ := ℍ) A k₁ μ₁ e₁ k' μ' e') :
    ARun (ℍ := ℍ) A k μ e k' μ' e' := by
  induction h₁ with
  | refl => exact h₂
  | more h _ ih => exact .more h (ih h₂)

theorem plug (K : Kont) {k k' : Nat} {μ μ' : Heap} {e e' : Expr}
    (h : ARun (ℍ := ℍ) A k μ e k' μ' e') :
    ARun (ℍ := ℍ) A k μ (K.plug e) k' μ' (K.plug e') := by
  induction h with
  | refl => exact .refl _ _ _
  | more h _ ih => exact .more (h.plug K) ih

/-- A step that allocates nothing, then an allocator run. -/
theorem cons {k k' : Nat} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : Step1N (ℍ := ℍ) μ e μ₁ e₁)
    (t : ARun (ℍ := ℍ) A k μ₁ e₁ k' μ' e') : ARun (ℍ := ℍ) A k μ e k' μ' e' :=
  .more (h.toAStep1 A k) t

/-- One step that allocates nothing. -/
theorem one {k : Nat} {μ μ' : Heap} {e e' : Expr} (h : Step1N (ℍ := ℍ) μ e μ' e') :
    ARun (ℍ := ℍ) A k μ e k μ' e' :=
  cons h (.refl _ _ _)

/-- The allocation at the allocator's location. -/
theorem alloc (k : Nat) (μ : Heap) (v : Val) (hfin : Fig16.FinDom μ) :
    ARun (ℍ := ℍ) A k μ (.app (.val (.prim .alloc)) (.val v)) (k + 1)
      (μ.upd (A.pick k μ 1) v) (.val (.loc (A.pick k μ 1))) :=
  .more ⟨.hole, _, _, rfl, rfl, .alloc k μ v (by simpa using A.fresh k μ 1 hfin 0 one_pos)⟩
    (.refl _ _ _)

end ARun

end BoCa.BoLo

end
