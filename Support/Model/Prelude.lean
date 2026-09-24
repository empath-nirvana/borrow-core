import Mathlib

/-!
# Support — Model — Prelude

`[about ours]`.  The carrier's prelude: `min`/`max` arithmetic, the finite-domain predicate, casts, bundled bijections, and the index `ι ∈ {own, imm, mut}` of `ρ∣ι`.
-/

noncomputable section

namespace BoCa.Fig16

theorem minLeL (a b : Nat) : min a b ≤ a := by omega

theorem minLeR (a b : Nat) : min a b ≤ b := by omega

theorem leMaxL (a b : Nat) : a ≤ max a b := by omega

theorem leMaxR (a b : Nat) : b ≤ max a b := by omega

/-- `f` has finite domain: some list of locations covers it. -/
def FinDom {Loc A : Type} (f : Loc → Option A) : Prop :=
  ∃ d : List Loc, ∀ l, f l ≠ none → l ∈ d

theorem cast_left {A B : Type} (h : A = B) (x : A) : cast h.symm (cast h x) = x := by
  cases h; rfl

theorem cast_right {A B : Type} (h : A = B) (y : B) : cast h (cast h.symm y) = y := by
  cases h; rfl

/-- A bundled bijection. -/
structure Equiv (A B : Type) where
    toFun : A → B
    invFun : B → A
    leftInv : ∀ a, invFun (toFun a) = a
    rightInv : ∀ b, toFun (invFun b) = b

/-- `ι ∈ {own, mut, imm}` (`[TR]` p. 5, in `ρ|ι`). -/
inductive Kind where
    | own
    | imm
    | mut
  deriving DecidableEq

end BoCa.Fig16

end
