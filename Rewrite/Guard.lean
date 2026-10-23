import Rewrite.Abort

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
  `c` and the rules' own (R0's forwarding answer clauses, each over the source's persistent
  answer clause).
* **G-fin**: every finaliser of `c` (`[then]`'s `D`, an unwinding borrow's `td`) is reached once on
  each abort path of `c′`. It is a finaliser of `c′` while its row keeps an operation no rule
  rewrites that may end the computation without resuming it (its count is not `1`; for a
  finaliser the program writes, any operation no rule rewrites: the re-check binds a row of
  operations at `1` by `[let]`, with no finaliser). For each name of its row a rule rewrites, an
  abort arm of `c′` (the `inr` arm of the `case` R0 writes at the finaliser's node) runs it first:
  a written `D` itself (`⟦D⟧ to d. …`, at `D`'s span and erasure), drop glue as the `return ()`
  its drops are read back to (the re-check places the drops), or `td`'s destructor on the lent
  source.
* **Implicit copies**: `implicitCopy` over the re-check's typed terms, the check `checkProgram`
  runs and `checkMain` does not.

**`π`** (`piOf`) maps each binder of `c` to its images in `c′` by id. Before the rules, every
source binder gets an id (`numberBinders`), written into its name (`x#s.k`), which the read-back
writes and the re-check keeps; every rule that moves a binder moves its `TInfo`, so its id with
it, and a rule that copies a term (a finaliser on two abort paths) copies its ids. `π` is id
equality, checked total (every source id has an image) and injective (an image carries one id).
The binders a rule writes are named by the rule (`%R0…`, `Cx.binder`) and carry no id; R0 maps no
source binder to `ctl` or `inv`. A program no rule rewrites is not numbered, and `π` is the
identity binder by binder. **G-qual** reads `π`: a binder keeps its class and, declared `linear`,
stays declared so.
-/

namespace Rewrite
open Frontend.Check (CVTy Checked hasDtorB implicitCopy)
open BoCa.Fig16.LogRel.Core.Check (TExpr)

/-- A binder's class: `0` persistent, `1` droppable, `2` linear. -/
def qualClass (A : CVTy) : Nat :=
  if A.persistent then 0 else if hasDtorB A then 1 else 2

/-- A finaliser node of a typed term: its span, the names of its row, and its finaliser's root span
and erasure (`[then]`'s `D`; an unwinding borrow's `td`, a destructor of its type). -/
structure Fin where
  sp : Frontend.Span
  names : List UInt32
  /-- The row's operations: each one's name and whether it may end the computation without
  resuming (its count is not `1`). -/
  ops : List (UInt32 × Bool)
  dsp : Frontend.Span
  dexp : BoCa.Expr
  dty : Option CVTy
  written : Bool

/-- What the guard reads of a typed term, in one walk: the types of its term binders in pre-order
(each node's in the order its rule pushes them) with their node's span and name, its handled
operations `(n, i, count)` in pre-order, its numbers of `!`-introductions, copies and forgets, its
finaliser nodes, and its `case` nodes' `inr` arms as G-fin reads them. -/
structure Facts where
  /-- Each term binder: its id (`Rewrite.idOf?` of its name, at a numbered program), its name,
  its type, and whether it is declared `linear`. -/
  binders : Array (Option String × String × CVTy × Bool) := #[]
  ops : Array (UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := #[]
  bangs : Nat := 0
  fins : Array Fin := #[]
  /-- Each `case`'s span, and the head of its `inr` arm: a binding's span and its head's erasure,
  or a drop's destructor's type. -/
  arms : Array (Frontend.Span × Option (Frontend.Span × BoCa.Expr) × Option CVTy) := #[]

def isBangIntro : TExpr → Bool
  | .bangThunkF .. | .bangThunkV .. | .copyBang .. | .forgetBang .. | .forgetUnk .. => true
  | _ => false

/-- A row's operations, each one's name and whether its count is not `1`. -/
def opsOf (S : BoCa.Fig16.LogRel.Core.Row) : List (UInt32 × Bool) :=
  S.map fun o => (o.n, o.cnt != .one)

/-- The erasure of `return ()`, which a finaliser the checker inserts (drop glue) reads back as:
its drops are the re-check's. -/
def unitE : BoCa.Expr := (TExpr.unitI default (.val .unit)).erase

/-- A finaliser node: `[then]`, or an unwinding borrow with a destructor. -/
def finOf : TExpr → Option Fin
  | .effThen i _ _ _ S _ _ _ _ _ tD =>
    some ⟨i.sp, S.map (·.n), opsOf S, tD.info.sp, tD.erase, none, i.written⟩
  | .withbor1U i _ _ _ S _ td | .withbor2U i _ _ _ S _ td | .withbor3U i _ _ _ _ S _ td
  | .sliceBorrowMU i _ _ _ S _ td | .sliceBorrowIU i _ _ _ S _ td =>
    let dty := match td with
      | .dtor _ _ A => some A
      | _ => none
    some ⟨i.sp, S.map (·.n), opsOf S, td.info.sp, td.erase, dty, false⟩
  | _ => none

/-- An arm with the `[sub]` the checker inserts around it peeled. -/
def peelSub : Nat → TExpr → TExpr
  | 0, t => t
  | f + 1, t => match t with
    | .effSub i _ _ _ _ c => if i.ins then peelSub f c else t
    | t => t

/-- The first drop of a variable by a destructor on an abort arm's spine, past the inserted `[sub]`s
and the bindings of values (`x <- return V`), where the re-check places a drop (§12): the
destructor's type. -/
def spineDrop : Nat → TExpr → Option CVTy
  | 0, _ => none
  | f + 1, t => match peelSub 8 t with
    | .unitE _ _ _ _ (.lolliE _ _ _ _ _ (.var ..) (.dtor _ _ A)) _ => some A
    | .bind _ _ _ _ _ (.ret ..) tN => spineDrop f tN
    | .effLet _ _ _ _ _ _ (.ret ..) tN => spineDrop f tN
    | _ => none

/-- The head of an abort arm: a binding (its span and its head's erasure), and the first drop by
a destructor on its spine (`spineDrop`). -/
def armHead (t : TExpr) : Option (Frontend.Span × BoCa.Expr) × Option CVTy :=
  let d := spineDrop 16 t
  match peelSub 8 t with
  | .bind i _ _ _ _ tM _ => (some (i.sp, tM.erase), d)
  | _ => (none, d)

/-- The guard's facts of a typed term, added to `acc`. -/
def facts : Nat → TExpr → Facts → Except String Facts
  | 0, _, _ => throw "guard: a term nested too deeply"
  | f + 1, t, acc => do
    let i := t.info
    let b (x : String) (A : CVTy) (lin : Bool) := (idOf? x, x, A, lin)
    let nm (k : Nat) : String := (i.binders[k]?).getD ""
    let bs := match t with
      | .bind _ _ A _ _ _ _ | .effLet _ _ A _ _ _ _ _ | .effThen _ _ A _ _ _ _ _ _ _ _ =>
        [b (nm 0) A i.lin]
      | .lam _ _ A _ _ => [b i.name A false]
      | .tensorE _ _ A B _ _ _ _ => [b (nm 0) A false, b (nm 1) B false]
      | .sumE _ _ A B _ _ _ _ _ => [b (nm 0) A false, b (nm 1) B false]
      | _ => []
    let os : List (UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := match t with
      | .effHandleV _ _ _ E _ n .. | .effHandleVB _ _ _ E _ n .. | .effHandleT _ _ _ _ E _ n ..
      | .effHandleL _ _ _ _ E _ _ n .. =>
        E.zipIdx.map fun ((q, _), i) => (n, i, q)
      | _ => []
    let arms := match t with
      | .sumE i _ _ _ _ _ _ _ t₂ =>
        let (b, d) := armHead t₂
        acc.arms.push (i.sp, b, d)
      | _ => acc.arms
    let acc := { acc with binders := acc.binders ++ bs.toArray, ops := acc.ops ++ os.toArray,
                          bangs := acc.bangs + (if isBangIntro t then 1 else 0),
                          fins := match finOf t with
                            | some fn => acc.fins.push fn
                            | none => acc.fins,
                          arms }
    match t with
    -- R1's relaxed lend: its λ is the lend's own (`withbor2r`), which the read-back writes as the
    -- lend's binder (`TInfo` of `lendR`); `π` reads the lend's.
    | .nilDead _ _ _ (.lam _ _ _ _ body) => facts f body acc
    | _ => t.children.foldlM (init := acc) fun acc (_, c) => facts f c acc

/-- A binder's image under the rewrite: an output binder (by its position in `c′`'s binder
order), a control operation (`ctl`), or a binder a rule's schema names (`inv`). -/
inductive Image where
  | binder (k : Nat)
  | ctl
  | inv (rule role : String)
  deriving DecidableEq, Repr

/-- The rewrite's binder map: each binder of `c` (by its position in `c`'s binder order) and its
image. -/
abbrev Pi := List (Nat × Image)

/-- **`π`**: each binder of `c` to the binder of `c′` at its node's span and with its name, the
`k`-th to the `k`-th; the binders a rule writes (`%…`) are no source binder's image. A binder with
no image is a failure. -/
def piOf (bs bs' : Array (Option String × String × CVTy × Bool)) : Except String Pi := do
  -- An unnumbered source (no rule rewrote it): the identity, binder by binder.
  if bs.all (·.1.isNone) then
    unless bs.size == bs'.size do throw "guard: the rewritten `main` has other binders"
    return (List.range bs.size).map fun k => (k, .binder k)
  -- Each id's first binder in `c′` (the binders of one id are the copies of one source binder:
  -- an instance's body at each use, a finaliser on each abort path).
  let mut img : Std.HashMap String Nat := {}
  for ((id?, _, _, _), k') in bs'.toList.zipIdx do
    if let some id := id? then
      unless img.contains id do img := img.insert id k'
  let mut seen : Std.HashSet String := {}
  let mut π : Array (Nat × Image) := #[]
  for ((id?, x, _, _), k) in bs.toList.zipIdx do
    let some id := id? | throw s!"guard: the source binder `{x}` has no id"
    if seen.contains id then continue
    seen := seen.insert id
    match img.get? id with
    | some k' => π := π.push (k, .binder k')
    | none => throw s!"guard: the binder `{x}` has no image in the rewritten `main`"
  pure π.toList

/-- Each id's binders' classes and declarations, joined over its copies: the source's strictest,
the image's loosest. -/
def byId (bs : Array (Option String × String × CVTy × Bool)) (src : Bool) :
    Std.HashMap String (Nat × Bool) := Id.run do
  let mut m : Std.HashMap String (Nat × Bool) := {}
  for (id?, _, A, lin) in bs do
    if let some id := id? then
      let q := if A.persistent then 0 else qualClass A
      m := match m.get? id with
        | none => m.insert id (q, lin)
        | some (q₀, l₀) => m.insert id (if src then (max q₀ q, l₀ || lin) else (min q₀ q, l₀ && lin))
  return m

/-- **The guard** over the source `c`, the re-checked `c′`, the names of the operations the rewrite
eliminates, the `!`-introductions its rules write, and the re-check's typed terms. Returns `π`. -/
def guard (fuel : Nat) (c c' : Checked) (t₀ : TExpr) (ruled : List UInt32) (ruleBangs : Nat)
    (terms' : List (Nat × TExpr)) : Except String Pi := do
  -- G-main.
  unless c'.C == c.C do throw "guard G-main: the rewritten `main` has another type"
  unless (c'.ctx.map fun s => (s.ty, s.live)) == (c.ctx.map fun s => (s.ty, s.live)) do
    throw "guard G-main: the rewritten `main` has another context of externs"
  -- G-assure.
  unless c'.pins.all c.pins.contains do
    throw "guard G-assure: the rewritten `main` uses a relaxed rule the source does not"
  -- The source as the rules read it: numbered (`numberBinders`) where a rule rewrites it.
  let fs ← facts fuel t₀ {}
  let fs' ← facts fuel c'.t {}
  -- G-qual, through π: a binder keeps its class and, declared `linear`, stays declared so.
  let π ← piOf fs.binders fs'.binders
  if fs.binders.all (·.1.isNone) then
    for (k, img) in π do
      let some (_, x, A, lin) := fs.binders[k]? | throw "guard: a binder out of range"
      let .binder k' := img | continue
      let some (_, _, A', lin') := fs'.binders[k']? | throw "guard G-qual: a binder with no image"
      if !A.persistent && qualClass A' < qualClass A then
        throw s!"guard G-qual: the binder `{x}` of class {qualClass A} is made class {qualClass A'}"
      if lin && !lin' then throw s!"guard G-qual: the binder `{x}` is declared `linear` and its image is not"
  else
    let src := byId fs.binders true
    let img := byId fs'.binders false
    for (id, (q, lin)) in src.toList do
      let some (q', lin') := img.get? id | throw s!"guard G-qual: the binder {id} has no image"
      if q' < q then throw s!"guard G-qual: the binder {id} of class {q} is made class {q'}"
      if lin && !lin' then throw s!"guard G-qual: the binder {id} is declared `linear` and its image is not"
  -- G-κ.
  let keep (o : UInt32 × Nat × BoCa.Fig16.LogRel.Core.Count) := !ruled.contains o.1
  unless fs'.ops.filter keep == fs.ops.filter keep do
    throw "guard G-κ: an operation no rule rewrites is handled at another count"
  -- G-bang.
  unless fs'.bangs ≤ fs.bangs + ruleBangs do
    throw "guard G-bang: the rewritten `main` introduces, copies or forgets a `!` the source does not"
  -- G-fin: each finaliser kept while its row keeps an operation no rule rewrites that may end the
  -- computation without resuming it …
  let spKey (sp : Frontend.Span) := (sp.start.line, sp.start.col, sp.stop.line, sp.stop.col)
  let kept := fs.fins.toList.filter fun fn =>
    fn.ops.any fun (n, weak) => !ruled.contains n && (fn.written || weak)
  let count {α} (l : List α) (p : α → Bool) := (l.filter p).length
  for fn in fs.fins.toList do
    let want := count kept (spKey ·.sp == spKey fn.sp)
    let got := count fs'.fins.toList (spKey ·.sp == spKey fn.sp)
    unless got == want do
      throw s!"guard G-fin: the finaliser at {fn.sp.start.render} is a finaliser of the rewritten `main` {got} times, not {want}"
  -- … and run first on the abort arm of each name of its row a rule rewrites.
  for fn in fs.fins.toList do
    let atSp := fs.fins.toList.filter (spKey ·.sp == spKey fn.sp)
    let want := atSp.foldl (fun n g => n + count g.names ruled.contains) 0
    let runs := fs'.arms.toList.filter fun (sp, b, d) =>
      spKey sp == spKey fn.sp &&
        match fn.dty with
        | some A => d == some A
        | none => match b with
          | some (dsp, e) => spKey dsp == spKey fn.dsp &&
              e == (if fn.written then fn.dexp.shift 1 1 else unitE)
          | none => false
    unless runs.length == want do
      throw s!"guard G-fin: the finaliser at {fn.sp.start.render} runs first on {runs.length} abort arms of the rewritten `main`, not {want}"
  -- Implicit copies.
  if let some e := implicitCopy terms' then
    throw s!"guard: implicit copy at {e.span.start.render}: {e.msg}"
  pure π

end Rewrite
