import Frontend.Check.TExpr
import Frontend.Check.Elab

/-!
# Frontend — Check — implicit deep copies  `[#108, docs/decisions.md 39, spec §10]`

A persistent value may be used more than once (SPEC §10), and the compiled program keeps every
object owned by exactly one word: a variable used by two sequential parts of a term is copied for
all but the last (`Backend/README.md`, Memory discipline; `Backend/Clos/Convert.lean`). At a type
that holds recursive data the copy is deep: it allocates every node. No C or Rust programmer
writes that copy by accident, so it is not made by accident here either. Such a use is written
`clone(x)`, and a use that would copy without it is an error that points at it.

A copy at a type whose copy is its words (`i32`, `bool`, a pair of them) stays implicit.

**Which uses copy.** This reads the checked typed term (`Frontend/Check/TExpr.lean`): every use is
a node, its variable a slot of the node's context with the slot's type, and a written copy is the
use's `TInfo.clone`. It follows closure conversion's ownership plan on the term, node for node:
the parts of a node run in sequence (a pair's components, an application's argument and then its
function, `M x`'s argument and then `M`, a binding's head and body, a `case`'s scrutinee and then
its arms, a `[then]`'s head and then its body or finaliser), the two arms of a `case` and the two
components of `<M, N>` are one part (only one runs), and a variable used in a part and in a later
part is copied for the earlier one. Every use of it in the earlier part receives a copy on its
path, so each must be written `clone(x)`. The program's externs are not variables of the term.

**Recursive data** is a persistent type with a `μ` in it, also under `⊗`, `⊕`, `[@a]` and `!`
(`deepData`): the backend boxes a `μ`'s recursive fields, and its generated copy allocates each
one. A persistent closure (`!(A ⇒ B)`) is copied by copying what it captures, which its type does
not say; it is not checked here, and `bcc-counts` counts every deep copy a run makes.
-/

namespace Frontend.Check
open BoCa.Fig16.LogRel.Core.Check

/-- A persistent type that holds recursive data, whose copy allocates. -/
def deepData : CVTy → Bool
  | .mu _ => true
  | .tensor A B | .sum A B => deepData A || deepData B
  | .box _ A | .bang A => deepData A
  | _ => false

/-- A use of a variable: its name, span and type, its slot (a level of the context, counted from
the outermost slot, so one variable has one level everywhere in its scope), and whether the
program writes it `clone(x)`. -/
structure Use where
  x : String
  sp : Span
  ty : CVTy
  lvl : Nat
  clone : Bool

/-- The variable a node uses itself, at a context of `d` slots: a variable, or the argument of
`M x` (its child `M` is a part of its own). Only a use at a persistent type that holds recursive
data can be copied deep, so only those are kept. -/
def _root_.BoCa.Fig16.LogRel.Core.Check.TExpr.ownUse (d : Nat) : TExpr → Option Use
  | .var i _ k A => if A.persistent && deepData A then some ⟨i.name, i.sp, A, d - 1 - k, i.clone⟩ else none
  | .app i _ k A _ _ _ =>
    if A.persistent && deepData A then some ⟨i.name, i.sp, A, d - 1 - k, false⟩ else none
  | _ => none

/-- The children of a node in the order of the source it was checked from: `V W`'s function before
its argument. -/
def _root_.BoCa.Fig16.LogRel.Core.Check.TExpr.srcChildren (t : TExpr) : List (TScope × TExpr) :=
  match t with
  | .lolliE .. => t.children.reverse
  | _ => t.children

/-- The parts of a node that run in sequence, as groups of its children's indices
(`TExpr.children`), in the order they run. A node with no group has no sequential parts; `M x`'s
own use runs before its child (`scanT`). -/
def _root_.BoCa.Fig16.LogRel.Core.Check.TExpr.parts : TExpr → List (List Nat)
  | .tensorI .. | .lolliE .. | .bind .. | .effLet .. | .unitE .. | .tensorE .. => [[0], [1]]
  | .sumE .. | .effThen .. => [[0], [1, 2]]
  | _ => []

/-- The uses of `earlier` that are copied because `later` uses the same variable, with a use in
`later` for each; the uses written `clone(x)` excepted, and those of the slots below `b`, the
program's externs. -/
def copiedUses (b : Nat) (earlier later : List Use) : List (Use × Use) :=
  earlier.filterMap fun u =>
    if u.clone || u.lvl < b then none else (later.find? (·.lvl == u.lvl)).map (u, ·)

/-- One pass over a node at a context of `d` slots whose `b` outermost slots are the externs: the
uses free in it (those of the variables a child binds dropped, and none from a child at a context
of its own), and every earlier use that is copied implicitly, with a later use of the same
variable, in the node and its children. -/
def scanT : Nat → Nat → Nat → TExpr →
    List Use × List (Use × Use)
  | 0, _, _, _ => ([], [])
  | n + 1, b, d, t =>
    let ks := t.children.map fun (sc, k) => match sc with
      | .push m => let (us, cs) := scanT n b (d + m) k; (us.filter (·.lvl < d), cs)
      | .fresh m => ([], (scanT n 0 m k).2)
    let group (is : List Nat) : List Use := is.flatMap fun i => (ks.getD i ([], [])).1
    let groups := match t with
      | .app .. => [(t.ownUse d).toList, group [0]]
      | _ => t.parts.map group
    let here := (List.range groups.length).flatMap fun i =>
      copiedUses b (groups.getD i []) (groups.drop (i + 1)).flatten
    let src := match t with
      | .lolliE .. => ks.reverse
      | _ => ks
    ((t.ownUse d).toList ++ src.flatMap (·.1), here ++ src.flatMap (·.2))

/-- The depth bound for reading a typed term. -/
def copiesFuel : Nat := 1 <<< 20

/-- The error for the first implicit deep copy among checked terms, each at a context of `d`
slots, the program's externs. -/
def implicitCopy (ts : List (Nat × TExpr)) : Option Error := do
  let (u, v) ← (ts.flatMap fun (d, t) => (scanT copiesFuel d d t).2).head?
  pure ⟨u.sp, s!"`{u.x}` is used again at {v.sp.start.render}, so this use copies it, and its " ++
    s!"type `{ppVTy u.ty}` holds recursive data: the copy allocates every node. Write " ++
    s!"`clone({u.x})` to copy it here, or do not use `{u.x}` after this"⟩

end Frontend.Check
