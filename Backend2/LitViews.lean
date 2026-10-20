import Std.Data.HashMap
import Std.Data.HashSet
import Backend2.Frames

/-!
# Backend2 — literal views  `[spec §17]`

A string literal is `(n, t)`, its table `t` the closure of a code the conversion makes from the
`litFn` node's bytes (`Backend2/Convert.lean`, `litCode`), the bytes placed in the program's data.
Lent as a family (`borrow imm l { v -> … }`), the literal is tabulated into an array, lent shared,
and the array destroyed. When the tabulator is that code (the closure flow, `Backend2/Flow.lean`)
and the array is only read before it is destroyed (its owner lent shared and then given to its
destructor, `Frames.readOnly`), the array may be the literal's bytes in the data itself: `tab`
becomes `tabLit`, which at a length within the literal's points the array at the data and
allocates nothing, and otherwise tabulates as `tab` does.
-/

namespace Backend2.LitViews
open Backend2

/-- Rewrite each `tab` whose array is a literal's view. -/
def rewrite (p : Prog) (lits : Option Nat) (sets : Std.HashMap Var (Std.HashSet Nat))
    : Prog := Id.run do
  let litOf (f : Var) : Option Nat := do
    let cs := sets.getD f {}
    if cs.size != 1 then none
    let c ← cs.toList.head?
    if lits == some c then some c else none
  let rw (body : Tm) : Tm :=
    let uses := Frames.usesOf (1 <<< 22) body none {}
    go uses litOf (1 <<< 22) body none
  { p with fns := p.fns.map (fun fd => { fd with body := rw fd.body }), main := rw p.main }
where
  go (uses : Std.HashMap Var Frames.Use) (litOf : Var → Option Nat) :
      Nat → Tm → Option Var → Tm
    | 0, t, _ => t
    | f + 1, t, dst => match t with
      | .prim (.tab fi) [g, n] =>
        match dst, litOf g with
        | some a, some _ =>
          if Frames.readOnly p uses 4096 a none then .prim (.tabLit fi) [g, n] else t
        | _, _ => t
      | .letv x e b => .letv x (go uses litOf f e (some x)) (go uses litOf f b dst)
      | .letpair x y q b => .letpair x y q (go uses litOf f b dst)
      | .case s x b₁ y b₂ => .case s x (go uses litOf f b₁ dst) y (go uses litOf f b₂ dst)
      | .copy x x' b => .copy x x' (go uses litOf f b dst)
      | .drop x b => .drop x (go uses litOf f b dst)
      | t => t

end Backend2.LitViews
