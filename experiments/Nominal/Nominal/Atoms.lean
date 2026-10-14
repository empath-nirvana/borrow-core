import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.WellFoundedSet
import Mathlib.Logic.Relation

/-!
# Nominal — atoms with parents, and the hereditary swap

**Atoms.** An atom is a list of parents and a tag (`Atom.mk ps t`): the lifetimes it is directly
beneath, and a name telling it apart from its siblings. Parents are read as a set. This is the
free order: every finite set of atoms is the parent set of infinitely many atoms (`fresh`).

**The order.** `a < b` when `b` is a strict ancestor of `a` (a chain of parent edges from `a` up
to `b`): `b` strictly outlives `a`. It is a partial order (`Atom.instPartialOrder`) with no
infinite ascending chain (`WellFoundedGT Atom`: an ancestor is a strict subterm). Lifetimes are
`Lft ≜ WithTop Atom`: `⊤` is static and outlives every atom. Two atoms are comparable exactly when
one is an ancestor of the other; siblings are incomparable.

**Fresh atoms.** `fresh S avoid` has parents exactly `S` and occurs in no atom of `avoid` (it is
neither one of them nor an ancestor of one: `fresh_not_le`).

**The hereditary swap.** For `x`, `x′` with the same parents, `swap x x′` exchanges them and
re-parents their descendants (`mk ps t ↦ mk (swap ps) t`), and fixes every atom in which neither
occurs (`swap_fix`). It is an involution (`swap_swap`) that preserves parent edges both ways
(`parent_swap_iff`), hence an order automorphism (`swapIso`, on lifetimes `swapLft`). An order
that carries the cell model over a chain has only the identity automorphism
(`DenseCarrier.carrier_rigid`); this one carries it (`Nominal.isCarrier`) and moves `x` to `x′`
(`swapLft_x`).
-/

noncomputable section
open Classical

namespace Nominal

/-- An atom: its parents and a tag. -/
inductive Atom where
  | mk (ps : List Atom) (tag : ℕ)

namespace Atom

/-- The parents. -/
def ps : Atom → List Atom
  | mk ps _ => ps

/-- The tag. -/
def tag : Atom → ℕ
  | mk _ t => t

@[simp] theorem ps_mk (ps : List Atom) (t : ℕ) : (mk ps t).ps = ps := rfl
@[simp] theorem tag_mk (ps : List Atom) (t : ℕ) : (mk ps t).tag = t := rfl

theorem eta (a : Atom) : mk a.ps a.tag = a := by cases a; rfl

/-- `b` is a parent of `a`. -/
def Parent (a b : Atom) : Prop := b ∈ a.ps

/-- `b` is a strict ancestor of `a`: `b` strictly outlives `a`. -/
def Below (a b : Atom) : Prop := Relation.TransGen Parent a b

theorem sizeOf_lt_of_parent {a b : Atom} (h : Parent a b) : sizeOf b < sizeOf a := by
  cases a with
  | mk ps t =>
      have := List.sizeOf_lt_of_mem (show b ∈ ps from h)
      simp only [Atom.mk.sizeOf_spec]
      omega

theorem sizeOf_lt_of_below {a b : Atom} (h : Below a b) : sizeOf b < sizeOf a := by
  induction h with
  | single h => exact sizeOf_lt_of_parent h
  | tail _ h ih => exact lt_trans (sizeOf_lt_of_parent h) ih

theorem below_irrefl (a : Atom) : ¬ Below a a := fun h => lt_irrefl _ (sizeOf_lt_of_below h)

theorem below_trans {a b c : Atom} (h₁ : Below a b) (h₂ : Below b c) : Below a c :=
  Relation.TransGen.trans h₁ h₂

theorem below_asymm {a b : Atom} (h₁ : Below a b) (h₂ : Below b a) : False :=
  below_irrefl a (below_trans h₁ h₂)

instance instPartialOrder : PartialOrder Atom where
  le a b := a = b ∨ Below a b
  lt a b := Below a b
  le_refl a := Or.inl rfl
  le_trans a b c := by
    rintro (rfl | h₁) (rfl | h₂)
    · exact Or.inl rfl
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inr (below_trans h₁ h₂)
  le_antisymm a b := by
    rintro (rfl | h₁) (e | h₂)
    · rfl
    · rfl
    · exact e.symm
    · exact (below_asymm h₁ h₂).elim
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (e | h')
      · subst e; exact below_irrefl _ h
      · exact below_asymm h h'
    · rintro ⟨(e | h), h'⟩
      · subst e; exact absurd (Or.inl rfl) h'
      · exact h

theorem lt_iff_below {a b : Atom} : a < b ↔ Below a b := Iff.rfl
theorem le_iff {a b : Atom} : a ≤ b ↔ a = b ∨ Below a b := Iff.rfl

/-- A parent is strictly above. -/
theorem lt_of_mem_ps {a b : Atom} (h : b ∈ a.ps) : a < b := Relation.TransGen.single h

instance : WellFoundedGT Atom := by
  refine ⟨Subrelation.wf (r := InvImage (· < ·) (sizeOf : Atom → ℕ)) ?_ (InvImage.wf _ wellFounded_lt)⟩
  intro x y h
  exact sizeOf_lt_of_below h

/-! ### Fresh atoms -/

mutual
/-- The largest tag occurring in an atom or its ancestors. -/
def maxTag : Atom → ℕ
  | mk ps t => max t (maxTagL ps)
/-- The largest tag occurring in a list of atoms or their ancestors. -/
def maxTagL : List Atom → ℕ
  | [] => 0
  | a :: as => max (maxTag a) (maxTagL as)
end

theorem tag_le_maxTag (a : Atom) : a.tag ≤ maxTag a := by
  cases a with
  | mk ps t => simp only [tag_mk, maxTag]; exact le_max_left _ _

theorem maxTag_le_maxTagL {a : Atom} : ∀ {as : List Atom}, a ∈ as → maxTag a ≤ maxTagL as
  | b :: bs, h => by
      simp only [maxTagL]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (maxTag_le_maxTagL h) (le_max_right _ _)

theorem maxTag_parent {a b : Atom} (h : Parent a b) : maxTag b ≤ maxTag a := by
  cases a with
  | mk ps t =>
      simp only [maxTag]
      exact le_trans (maxTag_le_maxTagL (show b ∈ ps from h)) (le_max_right _ _)

theorem maxTag_le_of_below {a b : Atom} (h : Below a b) : maxTag b ≤ maxTag a := by
  induction h with
  | single h => exact maxTag_parent h
  | tail _ h ih => exact le_trans (maxTag_parent h) ih

/-- An atom occurring in `a` (an ancestor-or-self of it) has a tag at most `maxTag a`. -/
theorem tag_le_of_le {a y : Atom} (h : a ≤ y) : y.tag ≤ maxTag a := by
  rcases h with rfl | h
  · exact tag_le_maxTag a
  · exact le_trans (tag_le_maxTag y) (maxTag_le_of_below h)

/-- A fresh atom: parents `S`, occurring in no atom of `avoid`. -/
def fresh (S avoid : List Atom) : Atom := mk S (maxTagL avoid + 1)

@[simp] theorem ps_fresh (S avoid : List Atom) : (fresh S avoid).ps = S := rfl

/-- **The fresh atom occurs in no atom of `avoid`**: it is neither one of them nor an ancestor
of one. -/
theorem fresh_not_le {S avoid : List Atom} {a : Atom} (ha : a ∈ avoid) : ¬ a ≤ fresh S avoid := by
  intro h
  have h₁ := tag_le_of_le h
  have h₂ := maxTag_le_maxTagL ha
  simp only [fresh, tag_mk] at h₁
  omega

theorem fresh_ne {S avoid : List Atom} {a : Atom} (ha : a ∈ avoid) : fresh S avoid ≠ a :=
  fun e => fresh_not_le ha (by rw [e])

/-! ### The hereditary swap -/

mutual
/-- **The hereditary swap**: `x ↔ x′`, and every descendant re-parented. -/
def swap (x x' : Atom) : Atom → Atom
  | mk ps t => if mk ps t = x then x' else if mk ps t = x' then x else mk (swapL x x' ps) t
/-- The swap on a list of parents. -/
def swapL (x x' : Atom) : List Atom → List Atom
  | [] => []
  | a :: as => swap x x' a :: swapL x x' as
end

theorem swapL_eq (x x' : Atom) : ∀ ps, swapL x x' ps = ps.map (swap x x')
  | [] => rfl
  | a :: as => by simp [swapL, swapL_eq x x' as]

theorem swap_eq (x x' a : Atom) :
    swap x x' a = if a = x then x' else if a = x' then x else mk (a.ps.map (swap x x')) a.tag := by
  cases a with
  | mk ps t => rw [swap, swapL_eq]; rfl

theorem swap_x (x x' : Atom) : swap x x' x = x' := by rw [swap_eq, if_pos rfl]

theorem swap_x' (x x' : Atom) : swap x x' x' = x := by
  rw [swap_eq]
  by_cases e : x' = x
  · rw [if_pos e, e]
  · rw [if_neg e, if_pos rfl]

theorem swap_generic {x x' a : Atom} (h : a ≠ x) (h' : a ≠ x') :
    swap x x' a = mk (a.ps.map (swap x x')) a.tag := by
  rw [swap_eq, if_neg h, if_neg h']

/-- **The swap fixes every atom in which neither `x` nor `x′` occurs.** -/
theorem swap_fix {x x' : Atom} : ∀ a : Atom, ¬ a ≤ x → ¬ a ≤ x' → swap x x' a = a := by
  intro a
  induction a using WellFoundedGT.induction with
  | _ a ih =>
    intro hx hx'
    have h₁ : a ≠ x := fun e => hx (e ▸ le_rfl)
    have h₂ : a ≠ x' := fun e => hx' (e ▸ le_rfl)
    rw [swap_generic h₁ h₂]
    conv_rhs => rw [← eta a]
    congr 1
    conv_rhs => rw [← List.map_id a.ps]
    refine List.map_congr_left fun p hp => ?_
    have hap : a < p := lt_of_mem_ps hp
    exact ih p hap (fun h => hx (le_trans hap.le h)) (fun h => hx' (le_trans hap.le h))

/-- `x` and `x′` have the same parents. -/
def SameParents (x x' : Atom) : Prop := ∀ p, p ∈ x.ps ↔ p ∈ x'.ps

theorem SameParents.symm {x x' : Atom} (h : SameParents x x') : SameParents x' x :=
  fun p => (h p).symm

/-- An ancestor of `x` contains neither `x` nor (when the parents agree) `x′`. -/
theorem not_le_of_lt {x x' p : Atom} (hs : SameParents x x') (hp : x < p) :
    ¬ p ≤ x ∧ ¬ p ≤ x' := by
  refine ⟨fun h => lt_irrefl x (lt_of_lt_of_le hp h), fun h => ?_⟩
  -- `x < p ≤ x′`: the first edge from `x` is a parent of `x`, so of `x′`
  have hxx' : x < x' := lt_of_lt_of_le hp h
  have : ∃ q, q ∈ x.ps ∧ q ≤ x' := by
    have hb : Below x x' := hxx'
    induction hb using Relation.TransGen.head_induction_on with
    | single h => exact ⟨_, h, le_rfl⟩
    | head h hrest _ => exact ⟨_, h, Or.inr hrest⟩
  obtain ⟨q, hq, hqx'⟩ := this
  have : x' < q := lt_of_mem_ps ((hs q).mp hq)
  exact lt_irrefl x' (lt_of_lt_of_le this hqx')

/-- The swap fixes every ancestor of `x`. -/
theorem swap_fix_of_lt {x x' p : Atom} (hs : SameParents x x') (hp : x < p) : swap x x' p = p :=
  swap_fix p (not_le_of_lt hs hp).1 (not_le_of_lt hs hp).2

/-- **The swap is an involution.** -/
theorem swap_swap {x x' : Atom} (hs : SameParents x x') : ∀ a, swap x x' (swap x x' a) = a := by
  intro a
  induction a using WellFoundedGT.induction with
  | _ a ih =>
    by_cases h₁ : a = x
    · subst h₁; rw [swap_x, swap_x']
    by_cases h₂ : a = x'
    · subst h₂; rw [swap_x', swap_x]
    have hmap : (a.ps.map (swap x x')).map (swap x x') = a.ps := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id a.ps]
      exact List.map_congr_left fun p hp => ih p (lt_of_mem_ps hp)
    -- the image is not `x` or `x′`, whose parents the swap fixes
    have hne : ∀ y, (y = x ∨ y = x') → mk (a.ps.map (swap x x')) a.tag ≠ y := by
      intro y hy e
      have hfix : ∀ p ∈ y.ps, swap x x' p = p := by
        intro p hp
        rcases hy with rfl | rfl
        · exact swap_fix_of_lt hs (lt_of_mem_ps hp)
        · exact swap_fix_of_lt hs (lt_of_mem_ps ((hs p).mpr hp))
      have hps : a.ps.map (swap x x') = y.ps := by rw [← e]; rfl
      have : a.ps = y.ps := by
        rw [← hmap, hps]
        conv_rhs => rw [← List.map_id y.ps]
        exact List.map_congr_left hfix
      have ht : a.tag = y.tag := by rw [← e]; rfl
      rcases hy with rfl | rfl
      · exact h₁ (by rw [← eta a, ← eta y, this, ht])
      · exact h₂ (by rw [← eta a, ← eta y, this, ht])
    rw [swap_generic h₁ h₂, swap_generic (hne x (Or.inl rfl)) (hne x' (Or.inr rfl))]
    simp only [ps_mk, tag_mk]
    rw [hmap, eta]

theorem swap_injective {x x' : Atom} (hs : SameParents x x') : Function.Injective (swap x x') :=
  fun a b h => by rw [← swap_swap hs a, h, swap_swap hs b]

/-- The parents of a swapped atom are the swapped parents. -/
theorem ps_swap_mem {x x' : Atom} (hs : SameParents x x') (a q : Atom) :
    q ∈ (swap x x' a).ps ↔ swap x x' q ∈ a.ps := by
  by_cases h₁ : a = x
  · subst h₁
    rw [swap_x]
    constructor
    · intro hq
      have hq' : q ∈ a.ps := (hs q).mpr hq
      rwa [swap_fix_of_lt hs (lt_of_mem_ps hq')]
    · intro hq
      have := swap_fix_of_lt hs (lt_of_mem_ps hq)
      rw [swap_swap hs] at this
      exact (hs q).mp (this ▸ hq)
  by_cases h₂ : a = x'
  · subst h₂
    rw [swap_x']
    constructor
    · intro hq
      have hq' : q ∈ a.ps := (hs q).mp hq
      rwa [swap_fix_of_lt hs (lt_of_mem_ps hq)]
    · intro hq
      have hp : swap x a q ∈ x.ps := (hs _).mpr hq
      have := swap_fix_of_lt hs (lt_of_mem_ps hp)
      rw [swap_swap hs] at this
      exact this ▸ hp
  · rw [swap_generic h₁ h₂, ps_mk, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rwa [swap_swap hs]
    · intro hq
      exact ⟨_, hq, swap_swap hs q⟩

/-- **The swap preserves parent edges, both ways.** -/
theorem parent_swap_iff {x x' : Atom} (hs : SameParents x x') (a b : Atom) :
    Parent (swap x x' a) (swap x x' b) ↔ Parent a b := by
  show swap x x' b ∈ (swap x x' a).ps ↔ b ∈ a.ps
  rw [ps_swap_mem hs, swap_swap hs]

theorem below_swap_iff {x x' : Atom} (hs : SameParents x x') (a b : Atom) :
    Below (swap x x' a) (swap x x' b) ↔ Below a b := by
  have fwd : ∀ a b, Below a b → Below (swap x x' a) (swap x x' b) := by
    intro a b h
    induction h with
    | single h => exact Relation.TransGen.single ((parent_swap_iff hs _ _).mpr h)
    | tail _ h ih => exact Relation.TransGen.tail ih ((parent_swap_iff hs _ _).mpr h)
  refine ⟨fun h => ?_, fwd a b⟩
  have := fwd _ _ h
  rwa [swap_swap hs, swap_swap hs] at this

/-- **The hereditary swap is an order automorphism.** -/
def swapIso {x x' : Atom} (hs : SameParents x x') : Atom ≃o Atom where
  toFun := swap x x'
  invFun := swap x x'
  left_inv := swap_swap hs
  right_inv := swap_swap hs
  map_rel_iff' := by
    intro a b
    show (swap x x' a = swap x x' b ∨ Below (swap x x' a) (swap x x' b)) ↔ (a = b ∨ Below a b)
    rw [below_swap_iff hs, (swap_injective hs).eq_iff]

@[simp] theorem swapIso_apply {x x' : Atom} (hs : SameParents x x') (a : Atom) :
    swapIso hs a = swap x x' a := rfl

theorem swapIso_symm {x x' : Atom} (hs : SameParents x x') : (swapIso hs).symm = swapIso hs := by
  ext a; rfl

end Atom

/-- Lifetimes: `⊤` (static) or an atom. -/
abbrev Lft : Type := WithTop Atom

/-- The hereditary swap on lifetimes; `⊤` is fixed. -/
def swapLft {x x' : Atom} (hs : Atom.SameParents x x') : Lft ≃o Lft :=
  OrderIso.withTopCongr (Atom.swapIso hs)

@[simp] theorem swapLft_coe {x x' : Atom} (hs : Atom.SameParents x x') (a : Atom) :
    swapLft hs (a : Lft) = (Atom.swap x x' a : Lft) := rfl

@[simp] theorem swapLft_top {x x' : Atom} (hs : Atom.SameParents x x') :
    swapLft hs (⊤ : Lft) = ⊤ := rfl

theorem swapLft_x {x x' : Atom} (hs : Atom.SameParents x x') : swapLft hs (x : Lft) = x' := by
  rw [swapLft_coe, Atom.swap_x]

theorem swapLft_x' {x x' : Atom} (hs : Atom.SameParents x x') : swapLft hs (x' : Lft) = x := by
  rw [swapLft_coe, Atom.swap_x']

theorem swapLft_symm {x x' : Atom} (hs : Atom.SameParents x x') : (swapLft hs).symm = swapLft hs := by
  ext a
  induction a using WithTop.recTopCoe with
  | top => rfl
  | coe a => rfl

/-- The swap fixes every lifetime in which neither `x` nor `x′` occurs. -/
theorem swapLft_fix {x x' : Atom} (hs : Atom.SameParents x x') {α : Lft}
    (h : ∀ a : Atom, α = a → ¬ a ≤ x ∧ ¬ a ≤ x') : swapLft hs α = α := by
  induction α using WithTop.recTopCoe with
  | top => rfl
  | coe a =>
      obtain ⟨h₁, h₂⟩ := h a rfl
      rw [swapLft_coe, Atom.swap_fix a h₁ h₂]

/-- A swap other than the identity: the order has automorphisms. -/
theorem swapLft_ne_refl {x x' : Atom} (hs : Atom.SameParents x x') (hne : x ≠ x') :
    swapLft hs ≠ OrderIso.refl Lft := by
  intro h
  have := congrArg (fun e : Lft ≃o Lft => e (x : Lft)) h
  simp only [swapLft_x, OrderIso.refl_apply] at this
  exact hne (WithTop.coe_injective this).symm

end Nominal

end
