import Backend.Driver

/-!
# Backend — the checker's cell classes against the layout types' cell widths  `[spec §5]`

    lake exe bcc-counts --cells <file>

The checker carries, for each type a cell of `main` is allocated at, every type such a cell may
hold (`Checked.cells`, `Frontend/Check/Cells.lean`). The closure IR's layout types find a cell's
width by unification instead: a cell class joins the locations that may be one cell, and is as
wide as the widest contents any of them holds (`Backend/Clos/Types.lean`). This compares the two,
as a check on the carried classes while both exist.

* **The checker's side.** A class *grows* when it holds a type wider than the one its cells are
  allocated at. A type's width is its words as the closure IR lays it out (`vWords`): `1` and `0`
  none, an integer or a location one, a family two, a pair its fields, a sum a tag and its wider
  payload, `!` and `[@a]` their contents, a recursive type its body with the variable a pointer. A
  closure's width depends on the codes of its type's union, not on its type, so a class holding a
  `U C` (or a host type) is reported as not measured.
* **The layout types' side.** An allocation (`alloc`, a scoped `alloc`) grows when its cell's
  class is wider than the value it is allocated with.

The program agrees when the set of growths (the allocated width and the cell's) is the same on
both sides. `scripts/check-cells.sh` prints the row of every program where either side grows or a
class is not measured, and pins the table in `corpus/cells.expected`.
-/

namespace Backend.Cells
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check Backend.Clos

/-- A value type's words, as the closure IR lays it out; `none` at a closure or a host type,
whose words its type does not give. -/
def vWords : Nat → VTy → Option Nat
  | 0, _ => none
  | _ + 1, .unit | _ + 1, .zero | _ + 1, .unk => some 0
  | _ + 1, .int _ => some 1
  | n + 1, .tensor A B => do pure ((← vWords n A) + (← vWords n B))
  | n + 1, .sum A B => do pure (1 + max (← vWords n A) (← vWords n B))
  | _ + 1, .ref _ | _ + 1, .imm _ _ | _ + 1, .mut _ _ => some 1
  | _ + 1, .fam _ => some 2
  | n + 1, .box _ A | n + 1, .bang A => vWords n A
  | _ + 1, .thunk _ | _ + 1, .opq _ => none
  | _ + 1, .tvar _ => some 1
  | n + 1, .mu A => vWords n A

/-- The allocations of a term of the closure IR: each one's value's words and its cell's. -/
def allocs (T : Types) (t : Tm) : List (Nat × Nat) :=
  here ++ match t with
    | .letv _ e b => allocs T e ++ allocs T b
    | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .hnd _ _ _ b | .ubind _ _ b | .catch _ b
    | .fin _ _ b | .catchAll b => allocs T b
    | .case _ _ b₁ _ b₂ => allocs T b₁ ++ allocs T b₂
    | .when _ _ _ _ b r => allocs T b ++ allocs T r
    | _ => []
where
  here : List (Nat × Nat) := match t with
    | .prim .alloc [v] | .prim (.scopedAlloc _) [v] =>
      match T.cons[v]? with
      | some l => [(T.words (T.varTy.getD v 0), T.cellWords l)]
      | none => []
    | _ => []

/-- The comparison of one program, or `none` when neither side grows and every class is
measured. -/
def report (k : CheckedProg) : Except String (Option String) := do
  let (p, T) ← k.closTypes
  let some T := T | throw "no layout types"
  let cls := k.main.cells
  let measured (cl : CellClass) : Option (Nat × Nat) := do
    let r ← vWords 64 cl.root
    let ws ← cl.tys.mapM (vWords 64)
    pure (r, ws.foldl max r)
  let unmeasured := cls.filter fun cl => cl.tys.length > 1 && (measured cl).isNone
  let ours := (cls.filterMap measured).filter (fun (r, w) => w > r) |>.eraseDups
  let as := allocs T p.main ++ p.codes.toList.flatMap fun c => allocs T c.body
  let theirs := (as.filter fun (r, w) => w > r).eraseDups
  let sort (xs : List (Nat × Nat)) := xs.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)
  let ours := sort ours
  let theirs := sort theirs
  if ours.isEmpty && theirs.isEmpty && unmeasured.isEmpty then return none
  let pp (xs : List (Nat × Nat)) : String :=
    if xs.isEmpty then "none" else ", ".intercalate (xs.map fun (r, w) => s!"{r}→{w}")
  let classes := cls.filter (·.tys.length > 1) |>.map fun cl =>
    s!"{Frontend.Check.ppVTy cl.root} holds {", ".intercalate (cl.tys.map Frontend.Check.ppVTy)}"
  let verdict := if !unmeasured.isEmpty then "not measured"
    else if ours == theirs then "agree" else "disagree"
  pure (some s!"checker grows {pp ours} ({"; ".intercalate classes}); layout types grow {pp theirs}; {verdict}")

end Backend.Cells
