import Core.Dtor

/-!
# NestedFold — the design pass's probe (#595)

What the kernel's grammar does at nested recursion, before the class `P`:

- `μX. I32 ⊗ Array X` meets `roll`'s premises, and its body is outside `FShape`, so `HasDtor.mu`
  cannot apply to it.
- A mutual group `A = 1 ⊕ (Ref A ⊗ Ref B)`, `B = 1 ⊕ (Ref B ⊗ Ref A)` encoded by Bekič as nested
  `μ`: the `B` found inside an unrolled `A` is `μY. B-body[A/X]`, which is not syntactically the
  canonical `B` (the kernel's `μ` is iso-recursive).
- The nested-`μ` encoding of member 0 of a fully connected group of `n` members, in nodes:
  `7, 19, 61, 241, 1171, 6847, 46969, 369901` for `n = 1, …, 8`.
-/

namespace Probe595
open BoCa.Fig16.LogRel.Core

abbrev i32 : VTy := .int .w32
/-- Rose tree with children in an array: `μX. I32 ⊗ Array X`. -/
abbrev roseA : VTy := .mu (.tensor i32 (.fam (.ref (.tvar 0))))

/-- Kernel type: positive and closed (roll's premises). -/
example : (VTy.tensor i32 (.fam (.ref (.tvar 0)))).NoMut 0 ∧ roseA.Cl 0 := by
  simp [VTy.NoMut, VTy.Cl]

/-- Outside today's class: `toFShape` reads `Array X` as a leaf, not closed. -/
example : ¬ (toFShape (.tensor i32 (.fam (.ref (.tvar 0))))).WF := by
  simp [toFShape, FShape.WF, VTy.Cl]

/-- Mutual group `A = 1 ⊕ (Ref A ⊗ Ref B)`, `B = 1 ⊕ (Ref B ⊗ Ref A)` by Bekič.
`A` closed: `μX. 1 ⊕ (Ref X ⊗ Ref (μY. 1 ⊕ (Ref Y ⊗ Ref X)))`. -/
abbrev bodyB (outer : VTy) : VTy := .sum .unit (.tensor (.ref (.tvar 0)) (.ref outer))
abbrev tyA : VTy := .mu (.sum .unit (.tensor (.ref (.tvar 0)) (.ref (.mu (bodyB (.tvar 1))))))
abbrev tyB : VTy := .mu (.sum .unit (.tensor (.ref (.tvar 0))
  (.ref (.mu (.sum .unit (.tensor (.ref (.tvar 0)) (.ref (.tvar 1)))))))) 
/-- The `B` found inside an unrolled `A`: `μY. B-body[A/X]`. -/
abbrev tyBinA : VTy := .mu (bodyB tyA)

/-- Iso-recursive: the `B` inside an `A` is not syntactically the canonical `B`, and `TyEq`
(structural) does not relate them. -/
example : tyBinA ≠ tyB := by intro h; simp [tyBinA, tyB, bodyB, tyA] at h

/-- Bekič closed type of member 0 of a fully connected group of `n` members, each body
`1 ⊕ (Ref X₀ ⊗ (Ref X₁ ⊗ …))`.  Size in nodes. -/
def nodes : VTy → Nat
  | .tensor A B => 1 + nodes A + nodes B
  | .sum A B => 1 + nodes A + nodes B
  | .ref A => 1 + nodes A
  | .mu A => 1 + nodes A
  | .fam A => 1 + nodes A
  | _ => 1

/-- Solve a system of `k` remaining members, with `d` outer binders already in scope; returns
the closed (relative to outer) type of the first remaining member. Body: `1 ⊕ ⊗ Ref(var j)`
over all members; outer members are de Bruijn vars, the others are solved recursively. -/
def bekic : Nat → Nat → VTy
  | 0, _ => .unit
  | k + 1, d =>
    -- binder for this member at depth d; remaining k members solved inside
    let rest : List VTy := (List.range k).map (fun _ => bekic k (d + 1))
    let refs : List VTy := (List.range (d + 1)).map (fun i => .ref (.tvar i)) ++ rest.map .ref
    .mu (.sum .unit (refs.foldr .tensor .unit))

#guard (List.range 8).map (fun n => (n + 1, nodes (bekic (n + 1) 0))) =
  [(1, 7), (2, 19), (3, 61), (4, 241), (5, 1171), (6, 6847), (7, 46969), (8, 369901)]

end Probe595
