import Backend.Driver
import Backend2.Convert
import Backend2.Print
import Backend2.Interp
import Backend2.Lower
import Backend2.Flow
import Backend2.Lint
import Backend2.LayoutCheck
import Frontend.Check.Handled
import Frontend.Check.TFacts

/-!
# Backend2 — driver

From a checked program (`Backend.CheckedProg`, the one check every stage shares) to the new
backend's stages. This module is the new backend's one contact with the frontend: it reads
`Checked`'s typed term, context, type and the externs' roles, and hands the stages plain data.
It is outside the import fence (`scripts/check-backend2.sh`).
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- The implementation of each extern, in declaration order. -/
def extsOf (m : Frontend.Check.IOMain) : Except String (List Ext) :=
  m.externs.mapM fun x => match x.role with
    | .cap fd => pure (.cap fd)
    | .clockCap => pure .clock
    | .readByte => pure (.io .readByte)
    | .writeByte => pure (.io .writeByte)
    | .writeAll => pure (.io .writeAll)
    | .readInto => pure (.io .readInto)
    | .clockNow => pure (.io .clockNow)
    | .clockSleep => pure (.io .clockSleep)
    | .harness => throw s!"extern `{x.name}` is the model's harness and is not compiled"

/-- A `handle` node of the typed term, as the direct-call facts read it: its name, operations,
outer row, clauses' kinds and its handler pair's erasure. -/
structure HNode where
  n : UInt32
  E : List (Qual × VTy × VTy)
  S : Row
  ks : List ClauseKinds.HKind
  H : Expr
  /-- The node is `effHandleVB`: its clauses receive `κ` boxed (BOXED-κ, SPEC §28). -/
  boxed : Bool := false
  /-- At a `[handle-last]` node (SPEC §51): its works' row `Σ_W`, its exits' arguments and whether
  its cancel rows are the empty ones the checker emits. -/
  last : Option (Row × (Nat → VTy) × Bool) := none
  /-- The names each operation's code performs or raises: the clause's (`handlerNames`), or at a
  rule-written handler its answering function's or work's (`ruleNames`). -/
  names : List (Option (List UInt32)) := []
  /-- The row that code runs at: `Σ`, or `Σ_N` (`effHandleT`), or `Σ_W` (`effHandleL`). -/
  codeRow : Row := []
  /-- The length of the node's context. -/
  depth : Nat := 0
  /-- At a rule-written handler, its answering functions' or works' tuple, as erased. -/
  fns : Option Expr := none
  /-- The frames its handled computation holds (`inside`, pinned by the typed rule:
  `TDerivesAt.inside_eqL`). -/
  inside : ClauseKinds.HIn := {}
  /-- The shapes of the code its handled computation takes in (`codeShapesV` of its free
  variables' types, `freeTys`); `none` when it may take in code of any type. -/
  codeIn : Option (List String) := none

mutual
/-- **The shape of a type**, its rows, lifetimes and qualifiers dropped: what `[sub]`, a row
instantiation and a lifetime's do not change. -/
def shapeV : VTy → String
  | .unit => "1" | .zero => "0" | .unk => "?" | .int w => s!"i{repr w}" | .opq _ => "o"
  | .tvar n => s!"#{n}"
  | .tensor A B => s!"({shapeV A}*{shapeV B})"
  | .sum A B => s!"({shapeV A}+{shapeV B})"
  | .thunk C => s!"U{shapeC C}"
  | .ref A => s!"R{shapeV A}" | .imm _ A => s!"I{shapeV A}" | .mut _ A => s!"M{shapeV A}"
  | .box _ A => s!"B{shapeV A}" | .bang A => s!"!{shapeV A}" | .mu A => s!"mu{shapeV A}"
  | .fam A => s!"[{shapeV A}]"
def shapeC : CTy → String
  | .ret A => s!"F{shapeV A}"
  | .arr A C => s!"({shapeV A}-o{shapeC C})"
  | .amp C D => s!"({shapeC C}&{shapeC D})"
  | .top => "T"
  | .all _ _ C => shapeC C
  | .nu C => s!"nu{shapeC C}"
  | .eff _ _ _ _ _ _ _ C => shapeC C
end

/-- A computation type a continuation may have: `&` or `ν`, under `∀` and rows. -/
def mayKont : CTy → Bool
  | .amp .. | .nu _ => true
  | .all _ _ C | .eff _ _ _ _ _ _ _ C => mayKont C
  | _ => false

/-- **The shapes of the code a value of the type holds**: each `U C` in it, outside the arrows.
Code a function returns or is given is made by code of the program, whose frames that code holds
(`Expr.hin` counts the frames of every λ and handled computation inside it). `none` when the
value may hold code of any type (`Unk`) or a continuation (a `&` or a `ν`: `κ`,
a stored generator), whose frames are another computation's, or code under a `μ` whose type
names the `μ`'s variable (its shape is not the shape of the code value that builds it).
`[spec §65]` -/
def codeShapesV : VTy → Option (List String)
  | .unit | .zero | .int _ | .opq _ => some []
  -- The typed term's types are closed: a type variable is a `μ`'s.
  | .tvar _ => some []
  | .unk => none
  | .tensor A B | .sum A B => do pure ((← codeShapesV A) ++ (← codeShapesV B))
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A => codeShapesV A
  -- A code type under the `μ` that names its variable has the folded type's shape (`#n` for
  -- the `μ`), while the code value that builds it has the unrolled type's (`shapeC` writes the
  -- `μ` out): the shapes do not meet, so the bound is not read there and is any frame. (The
  -- surface refuses a `μ`'s variable under `U`, `Frontend/Check/Elab.lean`, so no program
  -- reaches this today.)
  | .mu A => do
    let shs ← codeShapesV A
    if shs.any (·.contains '#') then none else pure shs
  | .thunk C => if mayKont C then none else some [shapeC C]

/-- The types of the variables free in `t` (indices at or past the binders inside it, `d`), read
off its `var` nodes; a child at a fresh context reads no slot outside. -/
def freeTys : Nat → Nat → TExpr → List VTy
  | 0, _, _ => [.unk]
  | f + 1, d, t =>
    (match t with
      | .var _ _ i A => if i ≥ d then [A] else []
      | _ => []) ++
    t.children.flatMap fun (sc, c) => match sc with
      | .push k => freeTys f (d + k) c
      | .fresh _ => []

/-- The code values of the typed term: each `thunkV` and `bangThunkV` node, its type's shape, the
frames its body holds (`Expr.hin` of its erasure) and the shapes of the code its body takes in. -/
def codeNodes : Nat → TExpr → List (String × ClauseKinds.HIn × Option (List String))
  | 0, _ => []
  | f + 1, t =>
    let here := match t with
      | .thunkV _ _ C b | .bangThunkV _ _ C b =>
        [(shapeC C, b.erase.hin, ((freeTys Frontend.Check.copiesFuel 0 b).mapM codeShapesV).map List.flatten)]
      | _ => []
    here ++ t.children.flatMap fun (_, c) => codeNodes f c

/-- **The frames code a handled computation takes in may hold**  `[spec §65]`: from the shapes of
the code its free variables' types hold, the frames of every code value of the typed term of one
of those shapes, and of the code those take in, to a fixed point; `none` (any frame) when a type
may hold code of any type. A value of a type holds code of a code value at that type's shape
(`[sub]`, a row's or a lifetime's instantiation change only what the shape drops), or a
continuation, whose frames a storing handler's flow record holds (`Checked.flowsKept`). -/
-- UNPROVED: that the code a handled computation takes in through a free variable is a code value
-- of the typed term whose type has one of the shapes that variable's type holds (`codeShapesV`), or
-- code those take in. It should hold because every closure is made by a `thunkV`/`bangThunkV` node
-- of the term, and `[sub]`, a row's or a lifetime's instantiation change only what `shapeC` drops;
-- a continuation or `Unk` falls back to `Checked.flowsKept`. That a run never puts other code there
-- is the run's typing invariant, which is not proved. If it fails, `directOK` misses a frame of
-- `K` that catches a work's operation, and the work's `perform` is called past that handler.
def takenFrames (nodes : List (String × ClauseKinds.HIn × Option (List String)))
    (shapes : List String) : Option ClauseKinds.HIn := Id.run do
  let mut seen : List String := []
  let mut todo := shapes
  let mut acc : ClauseKinds.HIn := {}
  for _ in [0:nodes.length + shapes.length + 1] do
    match todo with
    | [] => return some acc
    | sh :: rest =>
      todo := rest
      if seen.contains sh then continue
      seen := sh :: seen
      for (sh', hin, ins) in nodes do
        if sh' == sh then
          acc := acc ++ hin
          match ins with
          | some more => todo := todo ++ more
          | none => return none
  return if todo.isEmpty then some acc else none

/-- The `handle` nodes of a typed term, within the depth `fuel`. At `effHandleT` and `effHandleL`
the clauses are the rule's (`tailKind`, `lastKind`), written out from the node's tuples as the
handler runs them. -/
def hnodes (fuel : Nat) (t : TExpr) (depth : Nat := 0) : List HNode :=
  match fuel with
  | 0 => []
  | f + 1 =>
    let here : List HNode := match t with
      | .effHandleV _ _ S E _ n _ _ _ ks _ ins tc te =>
          [⟨n, E, S, ks, tc.erase, false, none, Check.handlerNames E tc.erase, S, depth, none, ins,
            (((freeTys Frontend.Check.copiesFuel 0 te).mapM codeShapesV).map List.flatten)⟩]
      | .effHandleVB _ _ S E _ n _ _ _ _ ks _ ins tc te =>
          [⟨n, E, S, ks, tc.erase, true, none, Check.handlerNames E tc.erase, S, depth, none, ins,
            (((freeTys Frontend.Check.copiesFuel 0 te).mapM codeShapesV).map List.flatten)⟩]
      | .effHandleT _ _ S SN E _ n _ _ _ _ _ ins tc te =>
          [⟨n, E, S, E.map ClauseKinds.tailKind,
            .pair (Expr.pairL tc.erase) (tailTuple E 0 (Expr.pairR tc.erase)), false, none,
            Check.ruleNames E (Expr.pairR tc.erase), SN, depth, some (Expr.pairR tc.erase), ins,
            (((freeTys Frontend.Check.copiesFuel 0 te).mapM codeShapesV).map List.flatten)⟩]
      | .effHandleL _ _ S SW E fs Xs n _ _ _ _ ins tc te =>
          [⟨n, E, S, E.map ClauseKinds.lastKind,
            .pair (Expr.pairL tc.erase) (lastTuple E 0 (Expr.pairL (Expr.pairR tc.erase))
              (Expr.pairR (Expr.pairR tc.erase))), false,
            some (SW, Xs, (List.range E.length).all fun j => decide (fs j = .ret .unit)),
            Check.ruleNames E (Expr.pairL (Expr.pairR tc.erase)), SW, depth,
            some (Expr.pairL (Expr.pairR tc.erase)), ins, (((freeTys Frontend.Check.copiesFuel 0 te).mapM codeShapesV).map List.flatten)⟩]
      | _ => []
    here ++ t.children.flatMap fun (sc, c) =>
      hnodes f c (match sc with | .push k => depth + k | .fresh k => k)

/-- `main`'s externs whose values are the platform's operations (`ExternSpec`'s I/O roles, persistent
closures with no state), by `main`'s context slot (`Backend2/Convert.lean`, `convMain`): code that
reads only these of its context is closed but for them, and is made again where it runs
(`mainIO`).  `[spec §64]` -/
def ioSlots (k : Backend.CheckedProg) : Nat × (Nat → Bool) :=
  match k.io with
  | none => (0, fun _ => false)
  | some m =>
    let n := k.main.ctx.length
    let roles := m.externs.toArray
    (n, fun i => match roles[n - 1 - i]? with
      | some x => match x.role with
        | .readByte | .writeByte | .writeAll | .readInto | .clockNow | .clockSleep => true
        | _ => false
      | none => false)

/-- The code `e` at a node whose context has `depth` slots reads none of them but `main`'s I/O
externs (`ioSlots`, the last `n`). -/
def openOK (io : Nat × (Nat → Bool)) (depth : Nat) (e : Expr) : Bool :=
  let (n, ext) := io
  (freeVars e).all fun v => v < depth && depth ≥ n && v ≥ depth - n && ext (v - (depth - n))

/-- **The context slots each rule-written handler's code reads** (`effHandleT`'s answering
functions, `effHandleL`'s works), by operation: the free variables of its `λ` in the node's
erasure, which `openOK` admits only at `main`'s I/O externs (`Backend2/Convert.lean`, `ioCtx`).
`[spec §64]` -/
def ruleFVs (c : Frontend.Check.Checked) : Std.HashMap (UInt32 × Nat) (List Nat) := Id.run do
  let mut out : Std.HashMap (UInt32 × Nat) (List Nat) := {}
  for h in hnodes Frontend.Check.copiesFuel c.t c.ctx.length do
    let some fs := h.fns | continue
    for j in List.range h.E.length do
      if let some e := Check.clauseExpr fs j then
        out := out.insert (h.n, j) ((out.getD (h.n, j) []) ++ freeVars e).eraseDups
  return out

/-- **The direct calls the checked facts license**  `[spec §47]`: for each static name, for each of
its operations, whether every `handle` node of the name
- classifies the operation's clause `tail` (`ks`, `classifyHandler_sound`),
- holds names of the clause's own code (`handlerNames`; its row's names where it has none) that
  `main`'s flow record cannot catch (`cond2B` at `Checked.flows`, which gives
  `Checked.unhandledNames`: no frame between a `perform` and its handler catches them), and
- holds one clause for it, closed (`closedAt 0`), at one outer row and one signature,
so that the clause a `perform` reaches is known and needs nothing from its handler's frame. -/
def directFacts (c : Frontend.Check.Checked) (io : Nat × (Nat → Bool) := (0, fun _ => false)) :
    Std.HashMap UInt32 (List Bool) := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t c.ctx.length
  let flows := c.flows
  let mut out : Std.HashMap UInt32 (List Bool) := {}
  for h in nodes do
    if out.contains h.n then continue
    let same := nodes.filter (·.n == h.n)
    let hs := match h.H with | .pair _ hs => some hs | _ => none
    let ok := h.E.zipIdx.map fun (_, j) =>
      same.all fun g =>
        let gs := match g.H with | .pair _ hs => some hs | _ => none
        let names := g.names
        let row := (g.codeRow.map (·.n)).eraseDups
        let cl := gs.bind fun hs => Check.clauseExpr hs j
        (g.ks[j]?.map (·.kind)) == some .tail &&
          Frontend.Check.cond2B flows (Frontend.Check.cond2Names row ((names[j]?).getD none)) &&
          (match cl with | some e => openOK io g.depth e | none => false) &&
          cl == hs.bind (fun hs => Check.clauseExpr hs j) &&
          decide (CTy.effOf g.S .unit = CTy.effOf h.S .unit) && decide (g.E = h.E)
    out := out.insert h.n ok
  return out

/-- The `div_fuel` nodes of a typed term, within the depth `fuel`. -/
def divFuels : Nat → TExpr → Nat
  | 0, _ => 0
  | f + 1, t =>
    (match t with | .divFuel .. => 1 | _ => 0) +
      (t.children.map fun (_, c) => divFuels f c).foldl (· + ·) 0

/-- The handlers of `Div` in a typed term, within the depth `fuel`: its `reify` and `div_fuel`
nodes (SPEC §14). -/
def divHandlers : Nat → TExpr → Nat
  | 0, _ => 0
  | f + 1, t =>
    let here := match t with
      | .reify .. | .divFuel .. => 1
      | _ => 0
    here + (t.children.map fun (_, c) => divHandlers f c).foldl (· + ·) 0

/-- The handlers of `Div` in the typed term are `main`'s `reify` alone, or none: no frame of any
context between a `perform` and its handler is a handler of `Div` (`main`'s `reify` is outside
every node).  `[spec §62, §65]` -/
def divAtMainOnly (c : Frontend.Check.Checked) : Bool :=
  divHandlers Frontend.Check.copiesFuel c.t == (if (mainReify? c.t).isSome then 1 else 0)

/-- What `directOK` reads of the whole program, computed once: the code values of the typed term
(`codeNodes`), the frames each name's nodes hold (`inside`), `Checked.flowsKept` and
`divAtMainOnly`. -/
structure DirectCx where
  code : List (String × ClauseKinds.HIn × Option (List String))
  inside : Std.HashMap UInt32 ClauseKinds.HIn
  kept : Thunk ClauseKinds.HIn
  divMain : Bool

def DirectCx.of (c : Frontend.Check.Checked) (nodes : List HNode) : DirectCx :=
  { code := codeNodes Frontend.Check.copiesFuel c.t,
    inside := nodes.foldl (fun m h => m.insert h.n ((m.getD h.n {}) ++ h.inside)) {},
    kept := Thunk.mk fun _ => c.flowsKept,
    divMain := divAtMainOnly c }

/-- **`DirectOK`, the checked fact at a `[handle-last]` operation** (#564's T-B2 spike, `DirectOK`
and `ActiveOK`; the user's decision of 2026-10-22)  `[spec §65]`: the work of operation `j` of
the node `h` runs in place of its `perform`, inside the context `K` between the `perform` and the
node, when
- **F-names**: no handler in `K` serves a name the work performs or raises. The work's own names
  (`ruleNames`, its row `Σ_W`'s where it has none), other than `Div`'s, are held by no frame of
  the bound: the frames the node's handled computation holds (`inside`, pinned by the typed rule),
  the cancel delimiter, and the frames of the code it takes in (`takenFrames` at the shapes its
  free variables' types hold; `Checked.flowsKept` where a type may hold a continuation or any
  code). `Div`'s `tick` is caught by no frame of `K` when the typed term's only handler of `Div`
  is `main`'s `reify` (`divAtMainOnly`). A finaliser in `K` catches a raise, and F-fin covers it;
- **F-fin**: the cancel rows are the empty ones the checker emits, so every finaliser in `K` is
  at the empty row (`[then]`'s `hfin` at the empty cancel row): it performs and raises nothing;
- **the exit indices are in bounds**: `2·|E| < 2³²`.
Where it fails, the node is the fallback (a drive, SPEC §49, §65): correct, not an error. -/
-- UNPROVED: that calling the work in place of its `perform` runs as `[handle-last]`'s clause does.
-- T-B1/T-B1′ (`last_resume_direct`, `last_cancel_direct`, `Core/DivHandleLastRuns.lean`) prove it
-- for a work that performs nothing; for a work that performs an operation of a site outside or
-- ticks (T-B2) it is not proved. `DirectOK` guards the two known differences: an operation of the
-- work caught by a frame of `K` (F-names, bounded by the checked `inside`, the cancel delimiter
-- and `takenFrames`, itself UNPROVED above) and a finaliser of `K` that performs or raises (F-fin,
-- read off the checked cancel rows). If it fails, a work's operation reaches a handler inside `K`
-- instead of the one outside the node, or a finaliser's effect is reordered.
def directOK (D : DirectCx) (h : HNode) (j : Nat) (emptyFins : Bool) : Bool :=
  let names := Frontend.Check.cond2Names (h.codeRow.map (·.n)).eraseDups ((h.names[j]?).getD none)
  let taken := match h.codeIn with
    | some [] => some ({} : ClauseKinds.HIn)
    | some shs => takenFrames D.code shs
    | none => none
  let bound := D.inside.getD h.n {} ++ ClauseKinds.HIn.one 0 ++ taken.getD D.kept.get
  emptyFins && decide (2 * h.E.length < 2 ^ 32) &&
    (names.filter (· != divName)).all (fun m => !(bound.names.contains m || bound.any)) &&
    (!names.contains divName || D.divMain)

/-- **The `[handle-last]` works the checked facts license to call where their operation is
performed**  `[spec §64, §65]`: for each static name, for each of its operations, whether every
`handle` node of the name is a `[handle-last]` node (`effHandleL`, its clauses `lastKind`'s) that
- holds one handler for it, closed but for `main`'s I/O externs (`openOK`), at one outer row and
  one signature, so that the work a `perform` calls is the one its node runs (`last_resume_direct`,
  `last_cancel_direct`);
- meets `DirectOK` (`directOK`): the work's operations reach the handlers outside the node, and
  `K`'s finalisers perform nothing, so its cancel unwinds to the node running them
  (`cancel_prefix`, `cancelOf_steps`).
Each licensed operation's cancel summand (`cancelSummand`): its exit's argument, beside the work's
raises. -/
def lastFacts (c : Frontend.Check.Checked) (io : Nat × (Nat → Bool) := (0, fun _ => false)) :
    Std.HashMap (UInt32 × UInt32) (VTy × Row) := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t c.ctx.length
  let D := DirectCx.of c nodes
  let mut out : Std.HashMap (UInt32 × UInt32) (VTy × Row) := {}
  for h in nodes do
    let some (SW, Xs, _) := h.last | continue
    let same := nodes.filter (·.n == h.n)
    for (k, j) in h.ks.zipIdx do
      if k.kind != .last then continue
      let ok := openOK io h.depth h.H &&
        same.all fun g => g.H == h.H && (match g.last with
            | some (_, _, ef) => directOK D g j ef
            | none => false) &&
          decide (CTy.effOf g.S .unit = CTy.effOf h.S .unit) && decide (g.E = h.E)
      if ok then out := out.insert (h.n, j.toUInt32) (Xs j, SW)
  return out

/-- **The program's machine operations**  `[spec §49]`: each control operation `(n, j)` whose
clause at some `handle` node of `n` is neither abortive nor called where it is performed
(`directFacts`, `lastFacts`): its `perform` suspends the computation, and the node's drive runs the
clause on the argument and `κ`. Read off the nodes' kinds (`ks`, `classifyHandler_sound`) and the
direct calls' facts. With them, the licensed `[handle-last]` operations' cancel summands
(`MachSet.last`). -/
def machineOps (c : Frontend.Check.Checked) (io : Nat × (Nat → Bool) := (0, fun _ => false)) :
    MachSet := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t c.ctx.length
  let direct := directFacts c io
  let mut last := lastFacts c io
  let mainR := if (mainReify? c.t).isSome then 1 else 0
  let mut out : MachSet := {}
  -- A work whose row `Σ_W` holds a machine operation would suspend inside the code that performs
  -- its operation, which its type does not say: that operation is a machine operation too, to a
  -- fixed point (`last` only shrinks).  [spec §65]
  for _ in [0:last.size + 1] do
    out := {}
    for h in nodes do
      for (k, j) in h.ks.zipIdx do
        unless k.kind == .abortive || (k.kind == .tail && (direct.getD h.n [])[j]? == some true) ||
            (k.kind == .last && last.contains (h.n, j.toUInt32)) do
          out := out.insert (h.n, j.toUInt32)
    -- A stored loop's `reify` (any but `main`'s): its observations suspend at each tick, so `tick`
    -- is a machine operation (SPEC §64).
    if divHandlers Frontend.Check.copiesFuel c.t > mainR then out := out.insert (divName, 0)
    let last' := last.filter fun _ (_, SW) => SW.all fun o => !out.contains (o.n, o.i)
    if last'.size == last.size then break
    last := last'
  -- The cancel summands, a work's holding those of the operations its row holds: to a fixed
  -- point.
  let mut ms : MachSet := out
  for _ in [0:last.size + 1] do
    let mut more := false
    for (key, (X, SW)) in last.toList do
      if ms.last.contains key then continue
      if let .ok (some t) := cancelSummand ms (fun k => last.contains k && !ms.last.contains k) X SW then
        ms := { ms with last := ms.last.insert key t }
        more := true
    if !more then break
  return ms

/-- **The operations whose every `handle` node keeps `κ` boxed** (SPEC §52): each machine operation
`(n, j)` whose clause at every node of `n` is `stored`, every node of `n` is `effHandleVB` (BOXED-κ,
SPEC §28) and no operation of any node of `n` is `unr` (a site with a stack has no `κ` that may be
copied). A stack machine's frames have one owner there:
the stored site whose `κ` holds them, which keeps a stack. -/
def stackOps (c : Frontend.Check.Checked) (io : Nat × (Nat → Bool) := (0, fun _ => false)) :
    MachSet := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t c.ctx.length
  let ms := machineOps c io
  let mut out : MachSet := {}
  for (n, j) in ms.ops.toList do
    let same := nodes.filter (·.n == n)
    if !same.isEmpty && same.all (fun g => g.boxed && g.E.all (·.1 != .unr) &&
        (g.ks[j.toNat]?.map (·.kind)) == some .stored &&
        (g.E[j.toNat]?.map (·.1)).any (· != .unr)) then
      out := out.insert (n, j)
  return out

/-- **The width classes** (SPEC §57): for each type `main` allocates a cell at, its class
(`Checked.classAt`, `Checked.classAt_alloc`), and for the contents of each capability's cell (an
extern, which no `alloc` node allocates) the class the checker's construction gives it
(`cellClasses`), checked closed under the term's `swap`s (`cellsOkB`, `cellsOkB_sound`): each
type's LIR types. -/
def classesOf (k : Backend.CheckedProg) : Except String (List (VTy × List LTy)) := do
  let c := k.main
  let ms := machineOps c (ioSlots k)
  let lir (tys : List VTy) : List LTy := tys.filterMap fun t => (ofV ms t).toOption
  let mut out : List (VTy × List LTy) := c.cells.map fun cl => (cl.root, lir cl.tys)
  let es := c.t.cells.2
  for s in c.ctx do
    if let .ref B := s.ty then
      let B := B.eraseLife
      if out.any (·.1 == B) then continue
      let cls := cellClasses [B] es
      unless cellsOkB [B] es cls do throw s!"internal error: a capability's cell class is not closed"
      out := out ++ cls.map fun cl => (cl.root, lir cl.tys)
  return out

/-- Each variable's uses in a term: whether each is the operand of a `free`. -/
def freeUses : Nat → Tm → List (Var × Bool)
  | 0, _ => []
  | f + 1, t => match t with
    | .var x => [(x, false)]
    | .unit | .lit _ => []
    | .pair a b => [(a, false), (b, false)]
    | .inj _ a => [(a, false)]
    | .clos _ env => env.map (·, false)
    | .app g a => [(g, false), (a, false)]
    | .app0 g | .sel g _ => [(g, false)]
    | .call _ as => as.map (·, false)
    | .prim op as => as.map (·, op == .free)
    | .letv _ e b => freeUses f e ++ freeUses f b
    | .letpair _ _ p b => (p, false) :: freeUses f b
    | .case s _ b₁ _ b₂ => (s, false) :: (freeUses f b₁ ++ freeUses f b₂)
    | .absurd s => [(s, false)]
    | .copy x _ b | .drop x b => (x, false) :: freeUses f b

/-- The lend scopes a term allocates cells for, and the variables its `letpair`s bind first. -/
def scopesIn : Nat → Tm → List Nat × List Var
  | 0, _ => ([], [])
  | f + 1, t => match t with
    | .letv _ (.prim (.allocLent s _) _) b =>
      let (ss, xs) := scopesIn f b
      (s :: ss, xs)
    | .letv _ e b =>
      let (s₁, x₁) := scopesIn f e
      let (s₂, x₂) := scopesIn f b
      (s₁ ++ s₂, x₁ ++ x₂)
    | .letpair x _ _ b => let (ss, xs) := scopesIn f b; (ss, x :: xs)
    | .case _ _ b₁ _ b₂ =>
      let (s₁, x₁) := scopesIn f b₁
      let (s₂, x₂) := scopesIn f b₂
      (s₁ ++ s₂, x₁ ++ x₂)
    | .copy _ _ b | .drop _ b => scopesIn f b
    | _ => ([], [])

-- UNPROVED: that a variable its function uses only as the operand of `free` is freed on every
-- path of that function before it returns. It should hold because the LIR consumes each variable
-- exactly once on every path, which `Lint.lint` checks of each program it compiles (`flatOf`),
-- and a lent cell's borrow does not outlive its lend (`withbor`'s fresh `'x`). If it fails, a
-- frame slot is read or freed after its frame is given back.
/-- **The frame slots** (SPEC §57): the lend scopes whose cell is a frame slot, by their owners. A
scope's `rel` (`TExpr.lendScope`) says the owner is released by `free` on every path of the typed
term; the conversion may place parts of that code in functions of their own (a closure, a join or
a resumption point of a machine, SPEC §49), and the owner's variable then reaches them as a
parameter. So a scope's cell is a slot where its function, the one that allocates it, binds its
owner and uses it only as the operand of `free`: every path of that function frees it there
(the LIR consumes each variable once on every path, which `Lint.lint` checks of the program). -/
def slotsOf (p : Prog) (owners : Std.HashMap Var Nat) : Std.HashMap Var Nat := Id.run do
  let mut out : Std.HashMap Var Nat := {}
  for b in p.main :: p.fns.toList.map (·.body) do
    let (ss, xs) := scopesIn (1 <<< 22) b
    let us := freeUses (1 <<< 22) b
    for x in xs do
      let some s := owners[x]? | continue
      unless ss.contains s do continue
      let mine := us.filter (·.1 == x)
      if !mine.isEmpty && mine.all (·.2) then out := out.insert x s
  return out

/-- **The check of a program's layouts** (`Backend2/LayoutCheck.lean`), as the compiler's error. -/
def checkLayouts (p : Prog) (L : Lay.Layouts) : Except String Unit :=
  match LayCheck.check p L with
  | .ok () => pure ()
  | .error e => throw s!"internal: closure classes not a fixed point: {e}"

/-- **The layouts of a program's LIR, checked**: `Layouts`'s analysis (`Lay.places`,
`Lay.resolve`), then the check that its result is a solution of the program's constraints
(`checkLayouts`). Every layout the compiler reads is one of these. A failure is the compiler's
error, not the program's. -/
def checkedLayouts (p : Prog) : Except String Lay.Layouts := do
  let (g, m) ← Lay.places p
  let L := Lay.resolve p g m
  checkLayouts p L
  pure L

/-- **The check of a program's closure flow** (`LayCheck.checkFlow`): the direct calls `fs`
licenses (`Flow.known`), its sets checked a solution of the flow's constraints. -/
def checkFlow (p : Prog) (L : Lay.Layouts) (fs : Flow.St) : Except String (Std.HashMap Var Nat) := do
  let kn := Flow.known p L fs
  match LayCheck.checkFlow p L fs.sets kn with
  | .ok () => pure kn
  | .error e => throw s!"internal: closure classes not a fixed point: closure flow: {e}"

/-- **The closure flow of a program's LIR, checked**: `Flow.solution`, then `checkFlow`. -/
def checkedFlow (p : Prog) (L : Lay.Layouts) : Except String (Flow.St × Std.HashMap Var Nat) := do
  let fs := Flow.solution p L
  pure (fs, ← checkFlow p L fs)

/-- **The runtime answers every tick**  `[spec §62]`: the typed term's handlers of `Div` are
`main`'s `reify` alone, when `main` is a loop the runtime drives (SPEC §11) and its value is
`reify` of its body (`mainReify?`), or there are none. Every tick of the program is then performed
inside `main`'s body, and the runtime's drive answers it *next* (`drive_reify_tick`). -/
def divRuntime (c : Frontend.Check.Checked) (loops : Bool) : Bool :=
  let main := if loops && (mainReify? c.t).isSome then 1 else 0
  divHandlers Frontend.Check.copiesFuel c.t == main

/-- The codes of the suspended computations an outcome `o` (of `M`) may hold, by the layouts: the
closure classes of each suspension's `k`.  `[spec §49]` -/
def suspCodes (L : Lay.Layouts) (o : Var) (M : OutInfo) : List Nat := Id.run do
  let n := L.node o
  let .sum _ x := L.sh n | return []
  let s := if (payTy M.pay).isSome then (match L.sh x with | .sum _ s => s | _ => x) else x
  let mut leaves : List Nat := []
  let mut cur := s
  for i in [0:M.ms.length] do
    if i + 1 == M.ms.length then leaves := leaves ++ [cur]
    else match L.sh cur with
      | .sum a b => leaves := leaves ++ [a]; cur := b
      | _ => leaves := leaves ++ [cur]
  return leaves.flatMap fun l => match L.sh l with
    | .pair _ kn => (L.unionOf kn).toList
    | _ => []

/-- **The functions a stored loop's `reify` may run**  `[spec §65]`: from the code it is given and
the suspended computations its drives resume (`CState.reifyRuns`), every function a call may
reach: a direct call, a closure's call at the codes the closure flow gives its variable
(`Flow.solution`, whose sets over-approximate every flow), a loop's function. -/
def reifyReach (p : Prog) (fs : Flow.St) (roots : Array Var) : Std.HashSet Nat := Id.run do
  let codesFns (x : Var) : List Nat :=
    ((fs.sets.getD x {}).toList.filterMap fun c => p.codes[c]?).flatMap (·.fns)
  let rec calls : Nat → Tm → List Nat
    | 0, _ => []
    | f + 1, t => match t with
      | .call fn _ => [fn]
      | .app g _ | .app0 g | .sel g _ => codesFns g
      | .prim (.tab fi) _ | .prim (.tabLit fi ..) _ => [fi]
      | .letv _ e b => calls f e ++ calls f b
      | .letpair _ _ _ b | .copy _ _ b | .drop _ b => calls f b
      | .case _ _ b₁ _ b₂ => calls f b₁ ++ calls f b₂
      | _ => []
  let mut seen : Std.HashSet Nat := {}
  let mut todo : List Nat := roots.toList.flatMap codesFns
  for _ in [0:p.fns.size + 1] do
    match todo with
    | [] => break
    | fn :: rest =>
      todo := rest
      if seen.contains fn then continue
      seen := seen.insert fn
      if let some fd := p.fns[fn]? then
        todo := calls (1 <<< 22) fd.body ++ todo
  -- The bound above counts functions, and each is entered once: the search ends within it.
  return seen

/-- The LIR of a checked program, and what the conversion read. With state machines (SPEC §49), the
layouts of the converted program decide the calls in tail position that close a loop
(`tailPass`) and the machines whose state is a cell (`cellPass`). A machine whose state is a cell
and whose body takes its continuation is converted again with the level's cell passed on to its
next point (`threadedOf`, SPEC §50): the conversion's second run, at those machines. -/
def lirOf₀ (k : Backend.CheckedProg) (census : Bool := false) : Except String (Prog × CState) := do
  let c := k.main
  let classes ← classesOf k
  -- A `main` the runtime's clause drives (SPEC §63) is run as one that does not loop.
  let (exts, ncaps, loops, rt) ← match k.io with
    | none => pure ([], 0, false, (Frontend.Check.rtMainOf c.C).isSome)
    | some m => pure (← extsOf m, m.caps.length, m.loopB.isSome && !m.rt, m.rt)
  let ctx := c.ctx.map fun s => (s.ty, s.live)
  let run (threaded stacked : Std.HashMap Nat LTy) (atRt : Std.HashSet Nat) :
      Except String (Prog × CState × Std.HashMap Nat LTy × Std.HashMap Nat LTy) := do
    let (p, st) ← convertProg exts ctx c.t c.C ncaps loops census (directFacts c (ioSlots k))
      (machineOps c (ioSlots k)) (divRuntime c loops) threaded stacked classes rt (ruleFVs c) atRt
    let p := { p with exits := c.exitsOnDivError }
    if st.done.isEmpty then return (p, st, {}, {})
    -- A call in tail position whose callee's suspended computations may be the machine's own
    -- closes a loop of tail calls, and passes its outcome on (SPEC §49, `tailPass`).
    let L₁ ← checkedLayouts p
    let loop (site : Nat × Var × OutInfo × Nat) : Bool :=
      let (_, o, M, i) := site
      let own := (st.done[i]?.map fun (_, kcs) => kcs.map (·.2)).getD []
      (suspCodes L₁ o M).any own.contains
    let (p, st) ← if st.tailSites.any loop then do
        let (p₁, st₁) ← tailPass st loop
        pure ({ p with fns := p₁.fns, codes := p₁.codes, ty := p₁.ty }, st₁)
      else pure (p, st)
    -- The machines whose suspended computation's class holds itself keep their state in a cell
    -- (SPEC §49, `cellPass`), read off the layouts' recursive classes.
    let L ← checkedLayouts p
    let recursive (kc : Nat) : Bool := match L.codeClass[kc]? with
      | some cls => L.isRec cls
      | none => false
    let (p₂, st₂) ← cellPass st recursive
    -- The stack machines (SPEC §52), read off these layouts: each call point's callee's suspended
    -- computations' classes.
    let sk := stackedOf st recursive (stackOps c (ioSlots k)) (suspCodes L)
    let th := (threadedOf st recursive).filter fun i _ => !sk.contains i
    return ({ p with fns := p₂.fns, codes := p₂.codes, ty := p₂.ty, statics := p₂.statics }, st₂, th, sk)
  let (p, st, th, sk) ← run {} {} {}
  -- The ticks whose code no stored loop's `reify` runs are answered where they are performed
  -- (SPEC §65): read off the first conversion's closure flow, when `main` is driven by the
  -- runtime and no `div_fuel` node counts ticks.
  -- UNPROVED: that a tick point `reifyReach` does not reach is performed under `main`'s `reify`
  -- alone, so the runtime answers it *next* in place. It should hold because `reifyReach`
  -- over-approximates the functions a stored loop's `reify` runs (every code the checked flow
  -- lets its closures and their callees reach), and the second conversion numbers the tick points
  -- as the first does (one conversion of the same typed term). If it fails, a tick inside a
  -- stored loop is answered *next* in place and the loop's observation never suspends: the
  -- loop runs ahead of its consumer.
  let atRt : Std.HashSet Nat ← do
    if st.tickPoints.isEmpty || !loops || (mainReify? c.t).isNone ||
        divFuels Frontend.Check.copiesFuel c.t > 0 then
      pure {}
    else
      let L ← checkedLayouts p
      let (fs, _) ← checkedFlow p L
      let reach := reifyReach p fs st.reifyRuns
      pure (st.tickPoints.fold (fun acc t mk => if reach.contains mk then acc else acc.insert t) {})
  if th.isEmpty && sk.isEmpty && atRt.isEmpty then return (p, st)
  let (p, st, _, _) ← run th sk atRt
  return (p, st)

/-- The LIR of a checked program (`lirOf₀`), with its frame slots (`slotsOf`). -/
def lirOf (k : Backend.CheckedProg) (census : Bool := false) : Except String (Prog × CState) := do
  let (p, st) ← lirOf₀ k census
  pure ({ p with slots := slotsOf p st.owners }, st)

/-- **The effect erasure's postcondition**, for a program (`bcc lir --erasure`, SPEC §47, §49): the
LIR has no `handle` and no `perform`, so a program the new backend compiles has none left. The
line counts, at a compiled program, the `handle`, `perform` and `raise` nodes the conversion
erased, and with state machines the `handle` nodes compiled as drives and the `perform`s as
suspensions (each `use` body once per key); a compiled program leaves no node. At a program
outside the fragment it counts the `handle` nodes with a clause of kind `once` or `stored` (the
stored-continuation sites) and the others no rule takes. -/
def erasureLine (k : Backend.CheckedProg) : String := Id.run do
  let c := k.main
  let nodes := hnodes Frontend.Check.copiesFuel c.t c.ctx.length
  let direct := directFacts c (ioSlots k)
  let last := lastFacts c (ioSlots k)
  let erasable (g : HNode) : Bool := g.ks.zipIdx.all fun (h, j) =>
    h.kind == .abortive || (h.kind == .tail && (direct.getD g.n [])[j]? == some true) ||
      (h.kind == .last && last.contains (g.n, j.toUInt32))
  let storedB (g : HNode) : Bool := g.ks.any fun h => match h.kind with
    | .stored | .resumeOnce _ => true
    | _ => false
  let stored := (nodes.filter storedB).length
  let other := (nodes.filter fun g => !erasable g && !storedB g).length
  match lirOf k with
  | .ok (_, st) =>
    let r (key : String) := st.erased.getD key 0
    -- A compiled program leaves no node: each is erased (SPEC §47) or a machine's drive (§49).
    let m := if r "machine" > 0 then s!" machines {r "machine"} suspends {r "suspend"}" else ""
    s!"erased handles {r "handle"} performs {r "perform"} raises {r "raise"}{m} left 0 0"
  | .error _ => s!"outside left {stored} {other}"

/-- Convert and lint a program (`bcc lir --lint`): an error outside the pure fragment, or the
lint's. -/
def lintOf (k : Backend.CheckedProg) : Except String Unit := do
  let (p, _) ← lirOf k
  Lint.lint p

/-- **The frame slots** (`bcc lir --frames`, SPEC §50, §57): of the cells allocated for one lend
(`Op.allocLent`), how many are placed in a frame slot (`slotsOf`) and how many on the heap. -/
def framesLine (k : Backend.CheckedProg) : Except String String := do
  let (p, _) ← lirOf k
  let all := (p.main :: p.fns.toList.map (·.body)).flatMap fun b => (scopesIn (1 <<< 22) b).1
  let slots := p.slots.fold (fun s _ sc => s.insert sc) ({} : Std.HashSet Nat)
  let n := (all.filter slots.contains).length
  pure s!"framed {n} allocated {all.length - n}"

/-- The layouts of a program's LIR, checked (`checkedLayouts`). -/
def layoutsOf (_k : Backend.CheckedProg) (p : Prog) : Except String Lay.Layouts :=
  checkedLayouts p

/-- The closure classes of a program's layouts, one a line: its codes, its width, whether its
environment is on the heap (`bcc lir --layout`). -/
def layoutReport (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _) ← lirOf k
  let L ← layoutsOf k p
  let cls := (L.union.toList.filter (!·.2.isEmpty)).map fun (r, cs) =>
    s!"class {r}: codes {cs.toList} width {L.w r}{if L.isRec r then " heap" else ""} : " ++
      (p.codes[cs[0]!]?.map (fun c => (c.ty.pp.take 100).toString)).getD ""
  let boxes := L.boxed.toList.map fun (v, i) => s!"boxed {v}.{i}"
  pure (cls ++ boxes)

/-- **The checks refuse wrong layouts** (`bcc lir --layout-reject`, the reject tests): the
program's layouts and closure flow as computed, accepted; then each perturbation of them
(`LayCheck.perturbLayouts`, `LayCheck.perturbFlow`), refused, with the refusal. A line
`ACCEPTED` is a perturbation the checks let through. -/
def rejectReport (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _) ← lirOf k
  Lint.lint p
  let (g, m) ← Lay.places p
  let L := Lay.resolve p g m
  let fs := Flow.solution p L
  let kn := Flow.known p L fs
  let base := match LayCheck.check p L, LayCheck.checkFlow p L fs.sets kn with
    | .ok (), .ok () => "accepted: the layouts and the closure flow as computed"
    | .error e, _ | _, .error e => s!"REFUSED as computed: {e}"
  let line (name : String) (r : Option (Except String Unit)) : String := match r with
    | none => s!"n/a: {name}"
    | some (.ok ()) => s!"ACCEPTED: {name}"
    | some (.error e) => s!"refused: {name}: {e.take 160}"
  let ls := (LayCheck.perturbLayouts p L).map fun (name, L') =>
    line name (L'.map fun L' => LayCheck.check p L')
  let fl := (LayCheck.perturbFlow p fs.sets kn).map fun (name, x) =>
    line name (x.map fun (s, kn') => LayCheck.checkFlow p L s kn')
  pure (base :: ls ++ fl)

/-- The word IR of a checked program by the new backend; with `counts`, the counting build. -/
def flatOf (k : Backend.CheckedProg) (counts : Bool := false) : Except String Backend.Flat.Prog := do
  let (p, _) ← lirOf k
  -- The LIR is linted on the way: each variable consumed once on every path, which `slotsOf`
  -- reads.
  Lint.lint p
  let L ← layoutsOf k p
  let (fs, kn) ← checkedFlow p L
  Low.lowerProg p L kn fs.sets counts

/-- The program as WAT by the new backend. -/
def watOf (k : Backend.CheckedProg) (counts : Bool := false) : Except String String := do
  pure (Backend.Wasm.printModule (Backend.Wasm.lowerProg (← flatOf k counts) counts))

/-- The program as LLVM IR by the new backend: typed pointers, and with `facts` the parameters'
facts as attributes (SPEC §50); without, for the differential run, which must print the same. -/
def llOf (k : Backend.CheckedProg) (counts : Bool := false) (facts : Bool := true) :
    Except String String := do
  Backend.Native.printProg (← flatOf k counts) Backend.nativeTriple counts (typed := true)
    (attrs := facts)

/-- **The new backend's compile, timed** (`bcc compile --backend new --timings`): `file`'s WAT, each
stage's time and output size written to standard error as `Backend.compileWatTimed` writes the
old backend's, then their total. The stages are the frontend's (parse, check, `main`'s I/O) and the
new backend's (the LIR, its layouts and their check, the 0-CFA and its check, the word IR, Wasm,
the printed module).
A measurement of the new backend's compile time, outside the gate (SPEC §48). -/
def watTimed (file src : String) : IO (Except String String) := do
  let tot ← IO.mkRef 0
  let stage {α} := @Backend.timed α (some tot)
  let go : ExceptT String IO String := do
    let p₀ ← ExceptT.mk <| stage "parse" (fun (p : Frontend.Program) => s!"{p.decls.length} declarations")
      fun _ => match Frontend.parseProgram src (lib := Frontend.Sugar.libSrc) with
        | .ok p => pure p
        | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
    let r ← ExceptT.mk <| stage "check" (fun _ => "") fun _ =>
      match Frontend.Check.checkProgram p₀ with
        | .ok r => pure r
        | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
    let some c := r.main | throw s!"{file}: no `main`"
    let k ← ExceptT.mk <| stage "io main" (fun _ => "") fun _ =>
      match Frontend.Check.ioMainOf r.el.prog c with
        | .ok io => pure (⟨r.el.prog, c, io⟩ : Backend.CheckedProg)
        | .error e => throw s!"{file}: {e}"
    let (p, _) ← ExceptT.mk <| stage "lir" (fun (q : Prog × CState) =>
        s!"{q.1.fns.size} functions, {q.1.codes.size} codes") fun _ => lirOf k
    let L ← ExceptT.mk <| stage "layout" (fun _ => "") fun _ => do
      let (g, m) ← Lay.places p
      pure (Lay.resolve p g m)
    ExceptT.mk <| stage "layout check" (fun _ => "") fun _ => checkLayouts p L
    let fs ← ExceptT.mk <| stage "flow" (fun _ => "") fun _ => pure (Flow.solution p L)
    let kn ← ExceptT.mk <| stage "flow check" (fun _ => "") fun _ => checkFlow p L fs
    let flat ← ExceptT.mk <| stage "lower" (fun (q : Backend.Flat.Prog) => s!"{q.fns.size} functions")
      fun _ => do
        Lint.lint p
        Low.lowerProg p L kn fs.sets false
    let wasm ← ExceptT.mk <| stage "wasm" (fun (m : Backend.Wasm.Module) => s!"{m.funcs.length} functions")
      fun _ => pure (Backend.Wasm.lowerProg flat)
    let wat ← ExceptT.mk <| stage "print" (fun (s : String) => s!"{s.utf8ByteSize} bytes")
      fun _ => pure (Backend.Wasm.printModule wasm)
    pure wat
  let r ← go.run
  IO.eprintln s!"total: {(← tot.get) / 1000000} ms"
  pure r

/-- A stage of the new backend on a checked program: `lir` is the LIR interpreter, `lflat` the
word IR's interpreter at the new backend's lowering. -/
def interpStage (stage : String) (k : Except String Backend.CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String Backend.Output := do
  match stage with
  | "lir" => runLIR (← lirOf (← k)).1 Backend.runFuel input args
  | "lflat" => Backend.Flat.interp Backend.runFuel (← flatOf (← k)) input args
  | "lflat-counts" => Backend.Flat.interp Backend.runFuel (← flatOf (← k) true) input args
  | _ => throw s!"unknown stage `{stage}`"

end Backend2
