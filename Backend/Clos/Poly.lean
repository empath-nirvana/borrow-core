import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Clos.Capture

/-!
# Backend — polymorphic lets, lowered per row  `[spec §24]`

`[let-poly]` binds a closed λ once and types each use at its own row, and the let reduces by one
β-step, which allocates nothing, to its body with the λ at each use (`letPoly_compatC`). The
lowering is per code: what a code may raise and suspend with fixes the convention it is called by
(`Backend/Clos/Unwind.lean`, `Backend/Clos/Capture.lean`), and the closure flow
(`Backend/Clos/Flow.lean`) gives a code every value any of its uses passes it. So a let whose uses
are at one row is lowered once, as any let, and a let whose uses are at different rows is lowered
per use: it is converted as its β-reduct (`polyLets`), each use a code of its own at its own row,
as a definition is substituted at each use. This is monomorphisation, as Rust instantiates a
generic function once per closure type it is called with: no use dispatches, allocates, or answers
for another use's effects.

**Which lets.** A use's row is what the lowering's analysis finds of it when it is a code of its
own. The program is converted with every polymorphic let replaced by its β-reduct and each use's λ
marked (`polyUseMark`), so that the conversion records the codes each use makes (`PolyUse`), and
analysed (`Prog.effects`). Of each of those codes the analysis gives the operations it may suspend
with and the keys it may raise, and the same of every closure the code may be given, answer or
capture, at any depth: a row of the function's type, in its argument or its result. The uses of one
instance of a let (inside one use of an enclosing let, or outside every use) are at one row when
these agree, code by code. The program is then converted with exactly the lets whose uses are not at
one row replaced: a program whose lets are each used at one row is converted as it is written.
-/

namespace Backend.Clos

/-- What a code may do: the operations it may suspend with and the keys it may raise (`none` when
a raise's key is not known), each sorted without repeats. -/
abbrev EffSig := List Nat × Option (List OpKey)

/-- `a` before `b`: by name, then by operation. -/
def opKeyLe (a b : OpKey) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- `a` and `b` together. -/
def EffSig.union (a b : EffSig) : EffSig :=
  ((a.1 ++ b.1).eraseDups.mergeSort (· ≤ ·), match a.2, b.2 with
    | some x, some y => some ((x ++ y).eraseDups.mergeSort opKeyLe)
    | _, _ => none)

/-- The codes of the closures a key holds at any depth: in pairs, injections, variants and the
contents of locations. -/
def Solver.closuresWithin (S : Solver) (k : Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert k
  let mut work : List Nat := [k]
  let mut out : List Nat := []
  -- Each key is put on the work list once.
  for _ in [0:S.set.size + 1] do
    match work with
    | [] => break
    | key :: rest =>
      work := rest
      for v in S.set[key]?.getD #[] do
        let inner : List Nat := match S.vals[v]! with
          | .clos _ => []
          | .pair a b => [a, b]
          | .inj _ a | .con _ a | .loc a => [a]
        if let .clos c := S.vals[v]! then
          if !out.contains c then out := out ++ [c]
        for a in inner do
          if !seen.contains a then
            seen := seen.insert a
            work := a :: work
  return out

/-- What code `c` may do, and what the closures it may be given, answer or capture may do. -/
def EffFacts.sig (E : EffFacts) (c : Nat) : EffSig × EffSig :=
  let eff (d : Nat) : EffSig :=
    ((E.skeys[d]?.getD []).eraseDups.mergeSort (· ≤ ·),
     (E.raises[d]?.getD (some [])).map fun ks => ks.eraseDups.mergeSort opKeyLe)
  let vars : List Var := match E.codes[c]? with
    | some code => code.param :: code.env
    | none => []
  let keys := (vars.filter (· < E.S.num.vars)).map (E.S.num.idx <| .var ·) ++
    [E.S.num.idx (.res c false), E.S.num.idx (.res c true)]
  let carried := (keys.flatMap E.S.closuresWithin).eraseDups
  (eff c, carried.foldl (fun s d => s.union (eff d)) ([], some []))

/-- The lets whose uses are not at one row: the uses grouped by their let and the use they are
converted inside, each group's uses compared code by code. -/
def polyRows (uses : Array PolyUse) (E : EffFacts) : List Nat := Id.run do
  let mut first : Std.HashMap (Nat × Option Nat) (List (EffSig × EffSig)) := {}
  let mut out : List Nat := []
  for u in uses do
    let s := u.codes.toList.map E.sig
    match first[(u.letId, u.parent)]? with
    | none => first := first.insert (u.letId, u.parent) s
    | some s₀ => if s != s₀ && !out.contains u.letId then out := out ++ [u.letId]
  return out

/-- The polymorphic lets whose uses are not at one row, by the conversion `conv` of the term with
the lets it is given replaced and, when asked, marked: none when the term has no polymorphic let,
or when its marked conversion or the analysis of it fails. -/
def polySelect (e : BoCa.Expr)
    (conv : (Nat → Bool) → Bool → Except String (Prog × Array PolyUse)) : List Nat :=
  if polyLetCount e == 0 then [] else
  match conv (fun _ => true) true with
  | .error _ => []
  | .ok (p, uses) => match p.effects with
    | .error _ => []
    | .ok E => polyRows uses E

/-- **Closure-convert a closed term** (`convertWith`), each polymorphic let whose uses are at
different rows as its β-reduct. -/
def convert (e : BoCa.Expr) : Except String Prog := do
  let sel := polySelect e fun s m => convertWith s m e
  return (← convertWith (sel.contains ·) false e).1

/-- **Closure-convert `run_io` applied to `arg` over its externs** (`convertMainWith`), each
polymorphic let whose uses are at different rows as its β-reduct.  `[spec §11]` -/
def convertMain (exts : List ExtImpl) (loops : Bool) (e arg : BoCa.Expr) :
    Except String Prog := do
  let sel := polySelect e fun s m => convertMainWith s m exts loops e arg
  return (← convertMainWith (sel.contains ·) false exts loops e arg).1

end Backend.Clos
