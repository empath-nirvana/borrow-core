import Support.Model.Tree.Order

/-!
# A cactus from a parent function

`[spec §62]`. Every lifetime other than `⊤` has a parent; following parents always reaches `⊤` (`rank`
decreases). The order is "is an ancestor of, or equal" (`ParentFn.Anc`), and it is a tree
(`Cactus.ofParent`).

When every fresh lifetime is a child of the current branch's innermost lifetime, a parent is
opened before its children: `ParentFn.InAlloc`, under which the cactus sits inside the printed
chain (`Cactus.ofParent_inChain`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- A parent for every lifetime other than `⊤`, with a rank that parents decrease. -/
structure ParentFn where
  par : Nat → Nat
  rank : Nat → Nat
  par_zero : par 0 = 0
  rank_lt : ∀ n, n ≠ 0 → rank (par n) < rank n

/-- `b` is `a` or an ancestor of it. -/
inductive ParentFn.Anc (P : ParentFn) : Nat → Nat → Prop
  | refl (n : Nat) : ParentFn.Anc P n n
  | up {a b : Nat} : ParentFn.Anc P (P.par a) b → ParentFn.Anc P a b

namespace ParentFn

/-- Parents were opened before their children. -/
def InAlloc (P : ParentFn) : Prop := ∀ n, n ≠ 0 → P.par n < n

theorem Anc.eq_or_rank_lt {P : ParentFn} {a b : Nat} (h : P.Anc a b) :
    b = a ∨ P.rank b < P.rank a := by
  induction h with
  | refl => exact Or.inl rfl
  | @up a b _ ih =>
      by_cases ha : a = 0
      · subst ha
        rw [P.par_zero] at ih
        rcases ih with rfl | h
        · exact Or.inl rfl
        · exact Or.inr h
      · have hr := P.rank_lt a ha
        rcases ih with rfl | h
        · exact Or.inr hr
        · exact Or.inr (lt_trans h hr)

theorem Anc.trans {P : ParentFn} {a b c : Nat} (h₁ : P.Anc a b) (h₂ : P.Anc b c) :
    P.Anc a c := by
  induction h₁ with
  | refl => exact h₂
  | up _ ih => exact .up (ih h₂)

theorem Anc.antisymm {P : ParentFn} {a b : Nat} (h₁ : P.Anc a b) (h₂ : P.Anc b a) : a = b := by
  rcases h₁.eq_or_rank_lt with rfl | r₁
  · rfl
  · rcases h₂.eq_or_rank_lt with rfl | r₂
    · rfl
    · exact absurd (lt_trans r₁ r₂) (lt_irrefl _)

theorem anc_zero (P : ParentFn) (a : Nat) : P.Anc a 0 := by
  induction h : P.rank a using Nat.strong_induction_on generalizing a with
  | _ k ih =>
    by_cases ha : a = 0
    · subst ha; exact .refl 0
    · exact .up (ih _ (h ▸ P.rank_lt a ha) _ rfl)

theorem Anc.chain {P : ParentFn} {a b c : Nat} (hb : P.Anc a b) (hc : P.Anc a c) :
    P.Anc b c ∨ P.Anc c b := by
  induction hb generalizing c with
  | refl => exact Or.inl hc
  | up h ih =>
      cases hc with
      | refl => exact Or.inr (.up h)
      | up hc' => exact ih hc'

theorem Anc.le {P : ParentFn} (hP : P.InAlloc) {a b : Nat} (h : P.Anc a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl _
  | @up a b _ ih =>
      by_cases ha : a = 0
      · subst ha; rw [P.par_zero] at ih; exact ih
      · exact le_trans ih (hP a ha).le

end ParentFn

/-- **The cactus of a parent function.** -/
def Cactus.ofParent (P : ParentFn) : Cactus where
  le a b := P.Anc (OrderDual.ofDual a) (OrderDual.ofDual b)
  refl _ := .refl _
  trans h₁ h₂ := h₁.trans h₂
  antisymm h₁ h₂ := OrderDual.ofDual.injective (h₁.antisymm h₂)
  top _ := P.anc_zero _
  up_chain h₁ h₂ := h₁.chain h₂

/-- Parents opened before their children: the cactus sits inside the chain. -/
theorem Cactus.ofParent_inChain {P : ParentFn} (hP : P.InAlloc) : (Cactus.ofParent P).InChain :=
  fun h => h.le hP

end BoCa.Fig16.Tree

end
