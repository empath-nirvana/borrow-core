import EffModelRel.Tree

/-!
# EffModelRel — where this method stops: negative recursion under `U`

The relation needs no step index because every type denotes a set and every term a finite tree.
The one recursive type, the stream `μX. U(F(A + int × X) & F 1)`, has `X` only in positive
positions, so its denotation is an inductive type (`Strm`).

A recursive type with `X` to the left of an arrow under `U`, such as `μX. U(X → F bool)` (T15's
"X under a `U`-codomain"), has no such denotation: a set `X` with a retraction onto
`X → Tree S Bool` would give a surjection onto `X → Bool`, and Cantor's argument refutes it
(`no_negative_domain`). Interpreting such a type needs a domain-theoretic or step-indexed model
(guarded recursion, or approximation by steps). This theorem is about the method of this
development; it does not say the type is unsound.
-/

namespace EffRel

variable {S : Sig}

/-- A tree that differs from the given one. -/
def flipT : Tree S Bool → Tree S Bool
  | .ret b => .ret (!b)
  | _ => .ret true

theorem flipT_ne : ∀ t : Tree S Bool, flipT t ≠ t
  | .ret b => by cases b <;> simp [flipT]
  | .op .. => by simp [flipT]
  | .ab .. => by simp [flipT]
  | .nu _ => by simp [flipT]
  | .act .. => by simp [flipT]

/-- No set retracts onto its own functions into trees of booleans. -/
theorem no_negative_domain (X : Type) (f : X → (X → Tree S Bool)) (g : (X → Tree S Bool) → X)
    (hfg : ∀ h, f (g h) = h) : False :=
  let d : X → Tree S Bool := fun x => flipT (f x x)
  flipT_ne (f (g d) (g d)) (congrFun (hfg d) (g d)).symm

end EffRel
