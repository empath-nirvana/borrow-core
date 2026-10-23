import Frontend.Check.Program

/-!
# Rewrite — the guard  `[spec §54]`

Run after the kernel's re-check, over the source's checked `main` `c`, the re-checked `c′` and the
rewrite's binder map `π` (the scope's §4). A failure is a hard error. Every check reads the two
checked terms; none reads a backend's state.

* **G-main**: `c′`'s type, context and externs are `c`'s (`exitsOnDivError` is carried from `c`,
  `Rewrite.run`).
* **G-assure**: `c′.pins ⊆ c.pins`: the rewrite adds no use of a relaxed rule.
* **G-qual**: each non-persistent binder of `c` keeps its class at its image under `π`
  (`qualClass`): a linear binder stays linear, a droppable one is not made persistent.
* **G-κ**: each handled operation's count at `c′` is its count at `c`, for every operation no
  rule rewrites.
* **G-bang**: `c′` has no more `!`-introductions, `!` copies or forgets, or forgets of `unk`, than
  `c`.
* **G-fin**: `c′` has as many finalisers (`[then]`'s `D`, an unwinding borrow's `td`) as `c`, but
  for the ones a rule accounts for.
* **Implicit copies**: `implicitCopy` over the re-check's typed terms, the check `checkProgram`
  runs and `checkMain` does not.

`π` (`Pi`) lists each binder a rule maps elsewhere than to itself: the identity rewrite (step 0)
has none, and every binder of `c` is then its own image.
-/

namespace Rewrite
open Frontend.Check (CVTy Checked hasDtorB implicitCopy)
open BoCa.Fig16.LogRel.Core.Check (TExpr)

/-- A binder's image under the rewrite: an output binder (by its position in `c′`'s binder
order), a control operation (`ctl`), or a binder a rule's schema names (`inv`). -/
inductive Image where
  | binder (k : Nat)
  | ctl
  | inv (rule role : String)
  deriving DecidableEq, Repr

/-- The rewrite's binder map: the binders (by position in `c`'s binder order) a rule maps
elsewhere than to the binder at the same position. Empty for the identity. -/
abbrev Pi := List (Nat × Image)

/-- A binder's class: `0` persistent, `1` droppable, `2` linear. -/
def qualClass (A : CVTy) : Nat :=
  if A.persistent then 0 else if hasDtorB A then 1 else 2

/-- What the guard reads of a typed term, in one walk: the types of its term binders in pre-order
(each node's in the order its rule pushes them), its handled operations `(n, i, count)` in
pre-order, and its numbers of `!`-introductions, copies and forgets, and of finalisers. -/
structure Facts where
  binders : Array CVTy := #[]
  ops : Array (UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := #[]
  bangs : Nat := 0
  fins : Nat := 0

def isBangIntro : TExpr → Bool
  | .bangThunkF .. | .bangThunkV .. | .copyBang .. | .forgetBang .. | .forgetUnk .. => true
  | _ => false

def isFinaliser : TExpr → Bool
  | .effThen .. | .withbor1U .. | .withbor2U .. | .withbor3U .. | .sliceBorrowMU ..
  | .sliceBorrowIU .. => true
  | _ => false

/-- The guard's facts of a typed term, added to `acc`. -/
def facts : Nat → TExpr → Facts → Except String Facts
  | 0, _, _ => throw "guard: a term nested too deeply"
  | f + 1, t, acc => do
    let bs : List CVTy := match t with
      | .bind _ _ A _ _ _ _ | .effLet _ _ A _ _ _ _ _ | .effThen _ _ A _ _ _ _ _ _ _ _ => [A]
      | .lam _ _ A _ _ => [A]
      | .tensorE _ _ A B _ _ _ _ => [A, B]
      | .sumE _ _ A B _ _ _ _ _ => [A, B]
      | _ => []
    let os : List (UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := match t with
      | .effHandleV _ _ _ E _ n .. | .effHandleVB _ _ _ E _ n .. | .effHandleT _ _ _ _ E _ n ..
      | .effHandleL _ _ _ _ E _ _ n .. =>
        E.zipIdx.map fun ((q, _), i) => (n, i, q)
      | _ => []
    let acc := { acc with binders := acc.binders ++ bs.toArray, ops := acc.ops ++ os.toArray,
                          bangs := acc.bangs + (if isBangIntro t then 1 else 0),
                          fins := acc.fins + (if isFinaliser t then 1 else 0) }
    t.children.foldlM (init := acc) fun acc (_, c) => facts f c acc

/-- **The guard** over the source `c`, the re-checked `c′`, the binder map `π`, the names of the
operations the rewrite eliminates, and the re-check's typed terms. -/
def guard (fuel : Nat) (c c' : Checked) (π : Pi) (ruled : List UInt32)
    (terms' : List (Nat × TExpr)) : Except String Unit := do
  -- G-main.
  unless c'.C == c.C do throw "guard G-main: the rewritten `main` has another type"
  unless (c'.ctx.map fun s => (s.ty, s.live)) == (c.ctx.map fun s => (s.ty, s.live)) do
    throw "guard G-main: the rewritten `main` has another context of externs"
  -- G-assure.
  unless c'.pins.all c.pins.contains do
    throw "guard G-assure: the rewritten `main` uses a relaxed rule the source does not"
  let fs ← facts fuel c.t {}
  let fs' ← facts fuel c'.t {}
  -- G-qual.
  for (A, k) in fs.binders.toList.zipIdx do
    let img := (π.lookup k).getD (.binder k)
    match img with
    | .binder k' =>
      match fs'.binders[k']? with
      | some A' =>
        if !A.persistent && qualClass A' < qualClass A then
          throw s!"guard G-qual: the binder {k} of class {qualClass A} is made class {qualClass A'}"
      | none => throw s!"guard G-qual: the binder {k} has no image in the rewritten `main`"
    | .ctl | .inv .. => pure ()
  -- G-κ.
  let keep (o : UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := !ruled.contains o.1
  unless fs'.ops.filter keep == fs.ops.filter keep do
    throw "guard G-κ: an operation no rule rewrites is handled at another count"
  -- G-bang.
  unless fs'.bangs ≤ fs.bangs do
    throw "guard G-bang: the rewritten `main` introduces, copies or forgets a `!` the source does not"
  -- G-fin.
  unless ruled.length > 0 || fs'.fins == fs.fins do
    throw "guard G-fin: the rewritten `main` has another number of finalisers"
  -- Implicit copies.
  if let some e := implicitCopy terms' then
    throw s!"guard: implicit copy at {e.span.start.render}: {e.msg}"

end Rewrite
