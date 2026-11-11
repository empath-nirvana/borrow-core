import Pipeline.Driver
import Target.Flat.Interp
import Target.Wasm.Lower
import Target.Wasm.Print
import Target.Native.Lower
import Backend2.Convert
import Backend2.Print
import Backend2.Interp
import Backend2.Lower
import Backend2.Flow
import Backend2.Lint
import Backend2.LayoutCheck
import Frontend.Check.Handled

/-!
# Backend2 — driver

From a checked program (`Backend.CheckedProg`, `Pipeline/Driver.lean`, the one check every stage
shares) to the new backend's stages. This module is the new backend's one contact with the
frontend: it reads `Checked`'s typed term, context, type and the externs' roles, and hands the
stages plain data. The import fence (`scripts/check-backend2.sh`) lets it reach the elaboration,
through the parse and check, and keeps it, as every module of `Backend2/`, off the old backend.
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- The implementation of each extern of `run_io`, in declaration order: an operation, or the
harness's make or take of a stream's capability cell. A capability is not an extern of `run_io`:
the harness makes it. -/
def extsOf (xs : List Frontend.Check.ExternSpec) : Except String (List Ext) :=
  xs.mapM fun x => match x.role with
    | .readByte => pure (.io .readByte)
    | .writeByte => pure (.io .writeByte)
    | .writeAll => pure (.io .writeAll)
    | .readInto => pure (.io .readInto)
    | .clockNow => pure (.io .clockNow)
    | .clockSleep => pure (.io .clockSleep)
    | .mk s => pure (.mk (capStream s))
    | .take s => pure (.take (capStream s))
    | .cap _ | .clockCap =>
      throw s!"extern `{x.name}` is a capability, which run_io's harness makes"
where
  capStream : Frontend.Check.IOStream → CapStream
    | .input => .input
    | .output => .output
    | .clock => .clock
    | .args => .args

/-- A `handle` node of the typed term, as the direct-call facts read it: its name, operations,
outer row, clauses' kinds, its handler pair's erasure and its typed term. -/
structure HNode where
  n : UInt32
  E : List (Qual × VTy × VTy)
  S : Row
  ks : List ClauseKinds.HKind
  H : Expr
  /-- The node is `effHandleVB`: its clauses receive `κ` boxed (BOXED-κ, SPEC §28). -/
  boxed : Bool := false
  /-- Each operation's cancel row, as its clause's `κ` reads it (`cancelTy`). -/
  fs : Nat → CTy := fun _ => .ret .unit
  /-- The handler pair's typed term. -/
  tc : Option TExpr := none

/-- The `handle` nodes of a typed term, within the depth `fuel`. -/
def hnodes : Nat → TExpr → List HNode
  | 0, _ => []
  | f + 1, t =>
    let here : List HNode := match t with
      | .effHandleV _ _ S E fs _ n _ _ _ ks _ _ tc _ => [⟨n, E, S, ks, tc.erase, false, fs, some tc⟩]
      | .effHandleVB _ _ S E fs _ n _ _ _ _ ks _ _ tc _ => [⟨n, E, S, ks, tc.erase, true, fs, some tc⟩]
      | _ => []
    here ++ t.children.flatMap fun (_, c) => hnodes f c

/-- **How a `perform` of an operation reaches its clause** (SPEC §47): called directly, with no
evidence (`closed`), with the values the clause captures passed as its name's evidence (`env`,
SPEC §71), or not called directly (`no`): a machine operation, or abortive. -/
inductive DirectKind where
  | closed | env | no
  deriving BEq, Inhabited, Repr

/-- The free variables of an erased term, at or above `k`, as indices into the context outside
it (`closedAt`'s complement). -/
def freeAt : Nat → Expr → List Nat
  | k, .var i => if i < k then [] else [i - k]
  | _, .unit | _, .loc _ | _, .prim _ => []
  | k, .pair e₁ e₂ | k, .seq e₁ e₂ | k, .app e₁ e₂ => freeAt k e₁ ++ freeAt k e₂
  | k, .inj₁ e | k, .inj₂ e => freeAt k e
  | k, .lam b => freeAt (k + 1) b
  | k, .letpair e₁ e₂ => freeAt k e₁ ++ freeAt (k + 2) e₂
  | k, .case e e₁ e₂ => freeAt k e ++ freeAt (k + 1) e₁ ++ freeAt (k + 1) e₂

/-- The types the typed term gives the slots of the context outside `t` that it reads, at `d`
binders below that context: each variable, forced variable and argument slot's type, as its node
records it. A child at a fresh context reads none of them. -/
def slotTypes : Nat → Nat → TExpr → List (Nat × VTy)
  | 0, _, _ => []
  | f + 1, d, t =>
    let here : List (Nat × VTy) := match t with
      | .var _ _ i A | .force _ _ i A _ | .app _ _ i A _ _ _ => if i < d then [] else [(i - d, A)]
      | _ => []
    here ++ t.children.flatMap fun (sc, c) => match sc with
      | .push k => slotTypes f (d + k) c
      | .fresh _ => []

mutual
/-- The names of the rows a value type holds. -/
def vNames : VTy → List UInt32
  | .tensor A B | .sum A B => vNames A ++ vNames B
  | .mu A | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A => vNames A
  | .thunk C => cNames C
  | .code _ E C => vNames E ++ cNames C
  | _ => []
/-- The names of the rows a computation type holds. -/
def cNames : CTy → List UInt32
  | .ret A => vNames A
  | .arr A C => vNames A ++ cNames C
  | .amp C D => cNames C ++ cNames D
  | .all _ _ C | .nu C => cNames C
  | .eff n _ _ A B fin _ C => n :: (vNames A ++ vNames B ++ cNames fin ++ cNames C)
  | .top => []
end

/-- **The direct calls the checked facts license**  `[spec §47]`: for each static name, the kind
of each of its operations' direct call, and at a name with an `env` operation its captured slots
with their types. An operation is called directly when every `handle` node of the name
- classifies the operation's clause `tail` (`ks`, `classifyHandler_sound`),
- holds names of the clause's own code (`handlerNames`; its row's names where it has none) that
  `main`'s flow record cannot catch (`cond2B` at `Checked.flows`, which gives
  `Checked.unhandledNames`: no frame between a `perform` and its handler catches them), and
- holds one clause for it (its erasure, de Bruijn), at one outer row and one signature, both up to
  `[α]` (`tyEqC`, `tyEqEnts`, SPEC §3): copies of one site from generic instances at different
  lifetime contexts spell their binders differently,
so that the clause a `perform` reaches is known. It is `closed` when the clause is closed
(`closedAt 0`): it needs nothing from its handler's frame. It is `env` [spec §71]
when the clause's free variables are slots of the node's context whose types, as the clause's
typed term records them, are persistent (`[handle]`'s `hd : Ctx.DeadP Γ₁`), agree at every node
up to `[α]` (`tyEqV`), and hold no row naming a name with an `env` operation: the clause's code
is the one static clause, and its captures are passed to it by value as its name's evidence. One
erasure at every node captures the same slots relative to the node. -/
def directFacts (c : Frontend.Check.Checked) :
    Std.HashMap UInt32 (List DirectKind) × Std.HashMap UInt32 (List (Nat × VTy)) := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let flows := c.flows
  let mut out : Std.HashMap UInt32 (List DirectKind) := {}
  let mut envs : Std.HashMap UInt32 (List (Nat × VTy)) := {}
  for h in nodes do
    if out.contains h.n then continue
    let same := nodes.filter (·.n == h.n)
    let hs := match h.H with | .pair _ hs => some hs | _ => none
    -- The clauses' typed terms at a node, written in place (`clausesOf`'s shape).
    let clauseT (g : HNode) (j : Nat) : Option TExpr := match g.tc with
      | some (.tensorI _ _ _ _ _ _ tCs) => (clauses g.E.length tCs)[j]?
      | _ => none
    let base (j : Nat) : Bool := same.all fun g =>
      let gs := match g.H with | .pair _ hs => some hs | _ => none
      let names := Check.handlerNames g.E g.H
      let row := (g.S.map (·.n)).eraseDups
      let cl := gs.bind fun hs => Check.clauseExpr hs j
      (g.ks[j]?.map (·.kind)) == some .tail &&
        Frontend.Check.cond2B flows (Frontend.Check.cond2Names row ((names[j]?).getD none)) &&
        cl.isSome && cl == hs.bind (fun hs => Check.clauseExpr hs j) &&
        Frontend.Check.tyEqC (CTy.effOf g.S .unit) (CTy.effOf h.S .unit) &&
        Frontend.Check.tyEqEnts g.E h.E
    -- Each captured slot's type at each node: one type, persistent.
    let slotsAt (j : Nat) : Option (List (Nat × VTy)) := do
      let cl ← hs.bind fun hs => Check.clauseExpr hs j
      let fv := (freeAt 0 cl).eraseDups.mergeSort (· ≤ ·)
      let mut first : List (Nat × VTy) := []
      for g in same do
        let tys := slotTypes 4096 0 (← clauseT g j)
        let mut here : List (Nat × VTy) := []
        for i in fv do
          let ts := (tys.filter (·.1 == i)).map (·.2)
          let A ← ts.head?
          unless ts.all (Frontend.Check.tyEqV A ·) && A.persistent do none
          here := here ++ [(i, A)]
        if first.isEmpty then first := here
        else unless (first.zip here).all fun ((_, A), (_, B)) => Frontend.Check.tyEqV A B do none
      pure first
    let mut ks : List DirectKind := []
    let mut slots : List (Nat × VTy) := []
    for (_, j) in h.E.zipIdx do
      if !base j then ks := ks ++ [.no]; continue
      let cl := hs.bind fun hs => Check.clauseExpr hs j
      if (cl.map (closedAt 0)) == some true then ks := ks ++ [.closed]; continue
      match slotsAt j with
      | some sl =>
        -- The name's evidence: the captured slots of all its `env` clauses, one type a slot.
        let clash := sl.any fun (i, A) => slots.any fun (i', B) => i == i' && !Frontend.Check.tyEqV A B
        if clash then ks := ks ++ [.no]
        else
          slots := (slots ++ sl.filter fun (i, _) => !slots.any (·.1 == i)).mergeSort (·.1 ≤ ·.1)
          ks := ks ++ [.env]
      | none => ks := ks ++ [.no]
    out := out.insert h.n ks
    if ks.contains .env then envs := envs.insert h.n slots
  -- A capture whose type holds a row naming a name with evidence is not passed (its LIR type would
  -- take evidence itself): those names' `env` operations are not called directly.
  let mut drop : List UInt32 := []
  for _ in [0:envs.size + 1] do
    let live := envs.toList.filter fun (n, _) => !drop.contains n
    let bad := live.filter fun (_, sl) => sl.any fun (_, A) =>
      (vNames A).any fun m => envs.contains m && !drop.contains m
    if bad.isEmpty then break
    drop := drop ++ bad.map (·.1)
  for n in drop do
    out := out.insert n ((out.getD n []).map fun k => if k == .env then .no else k)
    envs := envs.erase n
  return (out, envs)
where
  clauses : Nat → TExpr → List TExpr
    | 0, _ => []
    | n + 1, .tensorI _ _ _ _ _ c rest => c :: clauses n rest
    | _, _ => []

/-- The direct calls a conversion makes (`CState.direct`): `closed` operations, and `env` ones of
the names not dropped (`dropped`: the `env` names `evNames` excludes). -/
def directOf (kinds : Std.HashMap UInt32 (List DirectKind)) (dropped : List UInt32) :
    Std.HashMap UInt32 (List Bool) :=
  kinds.fold (fun m n ks => m.insert n (ks.map fun k =>
    k == .closed || (k == .env && !dropped.contains n))) {}

/-- **The program's machine operations**  `[spec §49]`: each control operation `(n, j)` whose
clause at some `handle` node of `n` is neither abortive nor called where it is performed
(`directFacts`): its `perform` suspends the computation, and the node's drive runs the clause on
the argument and `κ`. Read off the nodes' kinds (`ks`, `classifyHandler_sound`) and the direct
calls' facts. -/
def machineOps (c : Frontend.Check.Checked)
    (direct : Std.HashMap UInt32 (List Bool) := directOf (directFacts c).1 []) : MachSet := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let mut out : MachSet := {}
  for h in nodes do
    for (k, j) in h.ks.zipIdx do
      unless k.kind == .abortive || (k.kind == .tail && (direct.getD h.n [])[j]? == some true) do
        out := out.insert (h.n, j.toUInt32)
  return out

/-- **The operations whose every `handle` node keeps `κ` boxed** (SPEC §52): each machine operation
`(n, j)` whose clause at every node of `n` is `stored`, every node of `n` is `effHandleVB` (BOXED-κ,
SPEC §28) and no operation of any node of `n` is `unr` (a site with a stack has no `κ` that may be
copied), and whose cancel row at every node holds no machine operation (a stack machine's cancel
is a plain loop: a cancel that may suspend is not lowered on the task stack). A stack machine's
frames have one owner there: the stored site whose `κ` holds them, which keeps a stack. -/
def stackOps (c : Frontend.Check.Checked) (ms : MachSet := machineOps c) : MachSet := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let mut out : MachSet := {}
  for (n, j) in ms.toList do
    let same := nodes.filter (·.n == n)
    if !same.isEmpty && same.all (fun g => g.boxed && g.E.all (·.1 != .unr) &&
        (g.ks[j.toNat]?.map (·.kind)) == some .stored &&
        (g.E[j.toNat]?.map (·.1)).any (· != .unr) &&
        (g.E[j.toNat]?).all fun (q, _, B) => match ofFinAt ms {} q B (g.fs j.toNat) with
          | .ok cp => cp.all (·.ms.isEmpty)
          | .error _ => false) then
      out := out.insert (n, j)
  return out

mutual
/-- The computation types a value type holds, at every depth. -/
def subCV : VTy → List CTy
  | .tensor A B | .sum A B => subCV A ++ subCV B
  | .mu A | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A => subCV A
  | .thunk C => subCC C
  | .code _ E C => subCV E ++ subCC C
  | _ => []
/-- A computation type and the computation types it holds, at every depth. -/
def subCC : CTy → List CTy
  | .ret A => .ret A :: subCV A
  | .arr A D => .arr A D :: (subCV A ++ subCC D)
  | .amp D E => .amp D E :: (subCC D ++ subCC E)
  | .all x b D => .all x b D :: subCC D
  | .nu D => .nu D :: subCC D
  | .eff n i q A B fin rc D => .eff n i q A B fin rc D :: (subCV A ++ subCV B ++ subCC fin ++ subCC D)
  | .top => [.top]
end

/-- The operations of a row (`CTy.effOf`'s layers): key, qualifier and answer type. -/
def rowOps : CTy → List ((UInt32 × UInt32) × Qual × VTy)
  | .eff n i q _ B _ _ C => ((n, i), q, B) :: rowOps C
  | _ => []

/-- A computation type through its `∀`s. -/
def stripAllC : CTy → CTy
  | .all _ _ C => stripAllC C
  | C => C

/-- A row holds a machine operation of `ms` (`Types.ofC`, `Convert.rowMs`). -/
def machRow (ms : MachSet) (C : CTy) : Bool :=
  (rowOps C).any fun (k, q, B) => !abortB q B && ms.contains k

/-- The names of `cur` whose evidence a node's judgment `j` would take where the first cut builds
none  `[spec §71]`: a row holding the name at a machine operation (`Types.ofC`,
`Convert.outInfo?`), a `&` or `ν` component at a row holding it (`Types.ofC`), or, at a constant
whose expansion calls its closure argument from a generated helper (`helper`: `genTab`,
`genArrFree`, `genCount`, `genCountTry`, the folds, `unfold`), any row of its type holding it. -/
def evExcludedAt (cur : List UInt32) (ms : MachSet) (j : Jdg) (helper : Bool) : List UInt32 :=
  let tys := match j with | .val A => subCV A | .comp C => subCC C
  tys.flatMap fun C =>
    let here := if helper || machRow ms C then C.effNames.filter cur.contains else []
    let comp := match C with
      | .amp D E => ((stripAllC D).effNames ++ (stripAllC E).effNames).filter cur.contains
      | .nu D => (stripAllC D).effNames.filter cur.contains
      | _ => []
    here ++ comp

/-- The names a `handle` node of `n` at the outer row `S` excludes  `[spec §71]`: `n`, when its
clause's work, which runs at `S`, would be a machine or need evidence of `S` (the first cut builds
neither); and, when any of the node's clauses is called directly (`direct`, `closed` or `env`),
the evidence names `S` holds, since every direct work runs at `S` with no evidence in scope. -/
def evExcludedNode (cur : List UInt32) (ms : MachSet) (n : UInt32) (S : Row) (direct : Bool) :
    List UInt32 :=
  let outer := CTy.effOf S .unit
  let own := if cur.contains n && (machRow ms outer || outer.effNames.any cur.contains)
    then [n] else []
  -- Any direct work runs at `S` with no evidence in scope: `S`'s evidence names are excluded.
  let outerNames := if direct then outer.effNames.filter cur.contains else []
  own ++ outerNames

/-- The judgments of the nodes of a typed term, within the depth `fuel`, each with whether the node
is a constant whose expansion is a generated helper calling a closure argument (`evExcludedAt`). -/
def jdgsOf : Nat → TExpr → List (Jdg × Bool)
  | 0, _ => []
  | f + 1, t =>
    let helper := match t with
      | .arrNew .. | .arrFree .. | .countFold .. | .countTry .. | .foldImm .. | .foldOwn ..
      | .foldReuse .. | .foldOwnG .. | .unfoldN .. => true
      | _ => false
    (t.jdg, helper) :: t.children.flatMap fun (_, c) => jdgsOf f c

/-- **The program's evidence names**  `[spec §71]`: the names with an `env` operation
(`directFacts`) whose evidence the first cut builds, chosen before conversion so that it runs
once. A name is excluded, from the checked types, rows and nodes, when its evidence would reach
- a machine: a computation type of the term at a row holding the name and a machine operation
  (`evExcludedAt`), or a `handle` node of the name whose outer row holds one (`evExcludedNode`:
  its clause's work would be a machine);
- a `&` or `ν` component at a row holding the name (`evExcludedAt`);
- a generated helper other than `bounded_fix`'s loop (`evExcludedAt`);
- a work, of any name, whose outer row holds an evidence name (`evExcludedNode`): the outer
  row's evidence names are excluded;
- a captured value whose type has no LIR type.
Excluding a name makes its `env` operations machine operations, which may exclude another: the
exclusions are taken to a fixed point, from all `env` names down. A call site with no evidence in
scope is not a separate exclusion: a code at a row holding a name runs, by the row's typing,
only where that row is in effect, and the places the conversion has none in scope (a machine, a
drive, a `&`'s component, a helper, a work) are the exclusions above; the conversion meeting one
is an internal error (`evInternal`). -/
def evNames (c : Frontend.Check.Checked) (kinds : Std.HashMap UInt32 (List DirectKind))
    (envs : Std.HashMap UInt32 (List (Nat × VTy))) : List UInt32 := Id.run do
  let all := envs.toList.map (·.1)
  if all.isEmpty then return []
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let jdgs := jdgsOf Frontend.Check.copiesFuel c.t
  let mut cur := all
  for _ in [0:all.length + 1] do
    let dir := directOf kinds (all.filter (!cur.contains ·))
    let ms := machineOps c dir
    let mut bad : List UInt32 := jdgs.flatMap fun (j, h) => evExcludedAt cur ms j h
    for g in nodes do
      let direct := (dir.getD g.n []).any id
      bad := evExcludedNode cur ms g.n g.S direct ++ bad
    for (n, sl) in envs.toList do
      let tys : Except String (List LTy) := sl.mapM fun (p : Nat × VTy) => ofV ms {} p.2
      if cur.contains n && tys.toOption.isNone then bad := n :: bad
    let next := cur.filter (!bad.contains ·)
    if next.length == cur.length then break
    cur := next
  return cur

/-- **The width classes** (SPEC §57): for each type the compiled term `c` allocates a cell at, its
class (`Checked.classAt`, `Checked.classAt_alloc`), and for the contents of each capability's cell
(a harness make's result, which no `alloc` node of the term allocates) the class the checker's
construction gives it (`cellClasses`), checked closed under the term's `swap`s (`cellsOkB`,
`cellsOkB_sound`): each type's LIR types. -/
def classesOf (c : Frontend.Check.Checked) (ms : MachSet := machineOps c) (fd : EvSet := {}) :
    Except String (List (VTy × List LTy)) := do
  let lir (tys : List VTy) : List LTy := tys.filterMap fun t => (ofV ms fd t).toOption
  let mut out : List (VTy × List LTy) := c.cells.map fun cl => (cl.root, lir cl.tys)
  let es := c.t.cells.2
  for s in c.ctx do
    if let .bang (.thunk (.arr _ (.ret (.ref B)))) := s.ty then
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
    | .appE g a _ ev => (g, false) :: (a.toList ++ ev).map (·, false)
    | .call _ as => as.map (·, false)
    | .prim op as => as.map (·, op == .free)
    | .letv _ e b => freeUses f e ++ freeUses f b
    | .letpair _ _ p b => (p, false) :: freeUses f b
    | .case s _ b₁ _ b₂ => (s, false) :: (freeUses f b₁ ++ freeUses f b₂)
    | .absurd s => [(s, false)]
    | .copy _ x _ b | .consume _ x b | .abandon _ x b => (x, false) :: freeUses f b

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
    | .copy _ _ _ b | .consume _ _ b | .abandon _ _ b => scopesIn f b
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

/-- The LIR of a checked program, what the conversion read, and the program's layouts
(`checkedLayouts`) when the conversion computed them. With state machines (SPEC §49), the
layouts of the converted program decide the calls in tail position that close a loop
(`tailPass`) and the machines whose state is a cell (`cellPass`). A machine whose state is a cell
and whose body takes its continuation is converted again with the level's cell passed on to its
next point (`threadedOf`, SPEC §50): the conversion's second run, at those machines.

The layouts are computed once per distinct program: `L₁`'s program is the one `cellPass` reads
when `tailPass` changes nothing, and with no `cellSites` the program answered is the one the
layouts are of. -/
def lirOf₀ (k : Backend.CheckedProg) (census : Bool := false) :
    Except String (Prog × CState × Option Lay.Layouts) := do
  -- A program with capabilities is compiled as `run_io` (SPEC §11), the term `IORun.every_run`
  -- is about.
  let (c, exts, arg, loops) ← match ← k.runIO with
    | none => pure (k.main, [], none, false)
    | some (r, xs) => pure (r.c, ← extsOf xs, some [], r.loops)
  let (kinds, envs) := directFacts c
  -- The program's evidence [spec §71]: the names `evNames` keeps, each with its captured
  -- slots and their LIR types. A captured type holds no row naming such a name (`directFacts`),
  -- so it is read without evidence.
  let keep := evNames c kinds envs
  let direct := directOf kinds ((envs.toList.map (·.1)).filter (!keep.contains ·))
  let ms := machineOps c direct
  let envL := envs.toList.filter fun (n, _) => keep.contains n
  let mut fd : EvSet := {}
  for (n, sl) in envL do
    match sl.mapM (fun (_, A) => ofV ms {} A) with
    | .ok ts => fd := fd.insert n ts
    | .error e => throw (evInternal n s!"a captured value's type: {e}")
  let fdSlots : Std.HashMap UInt32 (List Nat) :=
    envL.foldl (fun m (n, sl) => m.insert n (sl.map (·.1))) {}
  let classes ← classesOf c ms fd
  let ctx := c.ctx.map fun s => (s.ty, s.live)
  let run (threaded stacked : Std.HashMap Nat LTy) :
      Except String (Prog × CState × Std.HashMap Nat LTy × Std.HashMap Nat LTy ×
        Option Lay.Layouts) := do
    let (p, st) ← convertProg exts ctx c.t c.C arg loops census direct ms
      threaded stacked classes fd fdSlots
    let p := { p with exits := c.exitsOnDivError }
    if st.done.isEmpty then return (p, st, {}, {}, none)
    -- A call in tail position whose callee's suspended computations may be the machine's own
    -- closes a loop of tail calls, and passes its outcome on (SPEC §49, `tailPass`).
    let L₁ ← checkedLayouts p
    let loop (site : Nat × Var × OutInfo × Nat) : Bool :=
      let (_, o, M, i) := site
      let own := (st.done[i]?.map fun (_, kcs) => kcs.map (·.2)).getD []
      (suspCodes L₁ o M).any own.contains
    -- The machines whose suspended computation's class holds itself keep their state in a cell
    -- (SPEC §49, `cellPass`), read off the layouts' recursive classes: `L₁` when no call closes a
    -- loop, the program then unchanged.
    let (p, st, L) ← if st.tailSites.any loop then do
        let (p₁, st₁) ← tailPass st loop
        let p := { p with fns := p₁.fns, codes := p₁.codes, ty := p₁.ty }
        pure (p, st₁, ← checkedLayouts p)
      else pure (p, st, L₁)
    let recursive (kc : Nat) : Bool := match L.codeClass[kc]? with
      | some cls => L.isRec cls
      | none => false
    -- The stack machines (SPEC §52), read off these layouts: each call point's callee's suspended
    -- computations' classes.
    let sk := stackedOf st recursive (stackOps c ms) (suspCodes L)
    let th := (threadedOf st recursive).filter fun i _ => !sk.contains i
    -- With no machine to make again, `cellPass` leaves the state as it is, and `p`'s functions,
    -- codes, types and statics are the state's (`convertProg` answers them, `tailPass` sets the
    -- first three and makes no static): the program is `p`, whose layouts are `L`.
    if (cellSites st recursive).isEmpty then return (p, st, th, sk, some L)
    let (p₂, st₂) ← cellPass st recursive
    return ({ p with fns := p₂.fns, codes := p₂.codes, ty := p₂.ty, statics := p₂.statics }, st₂,
      th, sk, none)
  let (p, st, th, sk, L) ← run {} {}
  if th.isEmpty && sk.isEmpty then return (p, st, L)
  let (p, st, _, _, L) ← run th sk
  return (p, st, L)

/-- The LIR of a checked program (`lirOf₀`), with its frame slots (`slotsOf`), and its layouts
when the conversion computed them. The layouts do not read the frame slots. -/
def lirLayOf (k : Backend.CheckedProg) (census : Bool := false) :
    Except String (Prog × CState × Option Lay.Layouts) := do
  let (p, st, L) ← lirOf₀ k census
  pure ({ p with slots := slotsOf p st.owners }, st, L)

/-- The LIR of a checked program (`lirLayOf`). -/
def lirOf (k : Backend.CheckedProg) (census : Bool := false) : Except String (Prog × CState) := do
  let (p, st, _) ← lirLayOf k census
  pure (p, st)

/-- The layouts of a program's LIR, checked: `L` when the conversion computed them
(`lirLayOf`), else `checkedLayouts`. -/
def layoutsAt (p : Prog) : Option Lay.Layouts → Except String Lay.Layouts
  | some L => pure L
  | none => checkedLayouts p

/-- **The effect erasure's postcondition**, for a program (`bcc lir --erasure`, SPEC §47, §49): the
LIR has no `handle` and no `perform`, so a program the new backend compiles has none left. The
line counts, at a compiled program, the `handle`, `perform` and `raise` nodes the conversion
erased, and with state machines the `handle` nodes compiled as drives and the `perform`s as
suspensions (each `use` body once per key); a compiled program leaves no node. At a program
outside the fragment it counts the `handle` nodes with a clause of kind `once` or `stored` (the
stored-continuation sites) and the others no rule takes. -/
def erasureLine (k : Backend.CheckedProg) : String := Id.run do
  let c := k.main
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let direct := directOf (directFacts c).1 []
  let erasable (g : HNode) : Bool := g.ks.zipIdx.all fun (h, j) =>
    h.kind == .abortive || (h.kind == .tail && (direct.getD g.n [])[j]? == some true)
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

/-- The closure classes of a program's layouts, one a line: its codes, its width, whether its
environment is on the heap; then the boxed fields; then each sum with a merged arm or packed
(SPEC §43), its tags, its width and the width a tag word and its payload would take (`bcc lir --layout`). A node is numbered by its
place in the canonical order (`Layouts.order`), and the lines are sorted by those numbers: the
report depends on the program and its types, not on how the analysis numbered its nodes. -/
def layoutReport (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _, L) ← lirLayOf k
  let L ← layoutsAt p L
  let idx : Std.HashMap Nat Nat := L.order.toList.zipIdx.foldl (fun m (v, i) => m.insert v i) {}
  let num (v : Nat) : Nat := idx.getD (L.r v) 0
  let cls := ((L.union.toList.filter (!·.2.isEmpty)).mergeSort fun a b => num a.1 ≤ num b.1).map
    fun (r, cs) =>
      s!"class {num r}: codes {cs.toList} width {L.w r}{if L.isRec r then " heap" else ""} : " ++
        (p.codes[cs[0]!]?.map (fun c => (c.ty.pp.take 100).toString)).getD ""
  let boxes := (L.boxed.toList.map fun (v, i) => (num v, i)).mergeSort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)
  -- The sums a merged arm or packing lays out otherwise than a tag word and a payload (SPEC §43),
  -- each with the words it would take as that (`was`).
  let rec plainW (fuel v : Nat) : Nat := match fuel with
    | 0 => L.w v
    | f + 1 =>
      let fw (j c : Nat) : Nat := if L.isBoxed v j then 1 else plainW f c
      match L.sh v with
      | .pair a b => fw 0 a + fw 1 b
      | .sum a b => 1 + max (fw 0 a) (fw 1 b)
      | _ => L.w v
  let sums := (L.order.toList.filter fun v => (L.merged v).isSome || L.isPacked v).map fun v =>
    s!"sum {num v}: merges {(L.merged v).map toString |>.getD "-"} tags {L.tagsOf v}" ++
      s!"{if L.isPacked v then " packed" else ""} width {L.w v} was {plainW 64 v}"
  pure (cls ++ boxes.map (fun (v, i) => s!"boxed {v}.{i}") ++ sums)

/-- **The checks refuse wrong layouts** (`bcc lir --layout-reject`, the reject tests): the
program's layouts and closure flow as computed, accepted; then each perturbation of them
(`LayCheck.perturbLayouts`, `LayCheck.perturbFlow`), refused, with the refusal. A line
`ACCEPTED` is a perturbation the checks let through. -/
def rejectReport (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _, L) ← lirLayOf k
  Lint.lint p
  let L ← match L with
    | some L => pure L
    | none => do let (g, m) ← Lay.places p; pure (Lay.resolve p g m)
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
  let (p, _, L) ← lirLayOf k
  -- The LIR is linted on the way: each variable consumed once on every path, which `slotsOf`
  -- reads.
  Lint.lint p
  let L ← layoutsAt p L
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
        | .ok io => pure (⟨r.el.prog, c, io, r.el.keys⟩ : Backend.CheckedProg)
        | .error e => throw s!"{file}: {e}"
    let (p, _, L₀) ← ExceptT.mk <| stage "lir" (fun (q : Prog × CState × Option Lay.Layouts) =>
        s!"{q.1.fns.size} functions, {q.1.codes.size} codes") fun _ => lirLayOf k
    -- The layouts the conversion computed and checked are reused: their stages then take no time.
    let L ← ExceptT.mk <| stage "layout" (fun _ => "") fun _ => match L₀ with
      | some L => pure L
      | none => do
        let (g, m) ← Lay.places p
        pure (Lay.resolve p g m)
    ExceptT.mk <| stage "layout check" (fun _ => "") fun _ =>
      if L₀.isSome then pure () else checkLayouts p L
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

/-- `UNPROVED:` (#746 item 5, F3) **the stack machine's hand-over**: at every configuration of
the LIR interpreter that a run of a converted program reaches at a `stackK` consume of `x`, whose
body binds `clos kc [base]` first, `x` is `clos kc [a]` and `base` is at or below `a` on the
current task stack, the frames from the top down to `a` written (`HandOver`). Proved beside it,
and only this: the frames of `k₂`'s range contain the consumed `k`'s (`TakesOver.suffix`), and a
`stackK` consume's step, as every consume's, touches no heap (`enter_stackK_keeps`). That `k₂`, resumed
or cancelled as its type requires, then releases those frames, so that the consume leaks nothing, is
part of what is assumed, not derived.

This is an assumption. It rests on the stack machine's construction (`genStackMach`): each
level's `mk` answers `clos kc [a]` at its own frame, and its call points call levels of the
machine itself, whose frames are above it (`stackedOf`). The kernel does not see the task stack,
so no kernel rule licenses the consume; #755 (task stacks in the kernel) is the route to proving
it. It is about the code `Convert` generates: an LIR program can carry a `stackK` node that `Lint`
accepts whose run fails the hand-over (`Backend2/LintTests.lean`), which the interpreter refuses
(`handOverB`, checked at every `stackK` consume of every run). It covers every checked program,
those with capabilities (`run_io`) among them: the machine's code is the same there. -/
def StackKHandOver : Prop :=
  ∀ (k : Backend.CheckedProg) (p : Prog) (c : CState), lirOf k = .ok (p, c) →
    ∀ (input args : List UInt8) (s : St) (x : Var) (b : Tm),
      Visits p (St.init p input args) p.main s (.consume .stackK x b) → HandOver s x b

/-- Whether a node of `t` is a stack machine's hand-over, a consume at the rule `stackK`. -/
def Tm.hasHandOver : Tm → Bool
  | .consume r _ b => r == .stackK || b.hasHandOver
  | .copy _ _ _ b | .abandon _ _ b => b.hasHandOver
  | .letv _ e b => e.hasHandOver || b.hasHandOver
  | .letpair _ _ _ b => b.hasHandOver
  | .case _ _ b₁ _ b₂ => b₁.hasHandOver || b₂.hasHandOver
  | _ => false

/-- **The lend encloses the function** (SPEC §50): the step from the kernel's "the lend is live" to
"the lend is live for the whole of this LIR function", which the borrow facts (`noalias`,
`readonly`, `nonnull`, `dereferenceable`: `Low.paramFacts`) need, since LLVM's attributes speak of
the whole of a function's execution. At every call a run of a converted program makes, of a
function `d` on arguments `as`:

- no borrow a parameter whose lend bit is set (`Fn.lendEncl`) holds is beside its cell's owner
  among the parameters, the same one included, or beside another borrow of the cell unless both
  are `imm` (`EnclosesAt`);
- each cell such a parameter borrows, a pair's fields among them, is live at every configuration
  the call's body reaches (`enclCells`).

This is an assumption. The bit is set only at a source function, the code of a source `λ`,
thunk or `&` (`Convert.sourceEncl`); every function the conversion makes clears it. A source
function is entered where the source term forces or applies its closure, inside every lend whose
borrow it receives, and the lend's owner is not in the source term's context there: the kernel's
lexical lends. That the conversion keeps this is not proved: the LIR's types carry no lifetimes.
The assumption also covers what the Prop does not state: that the function reaches no owner of
the cell other than as a parameter's word (in a closure's environment, in a cell), which
`noalias` asks too. That part is checked only through its effect, the cell's liveness at the
call's return (`enclCells`), not at entry: `ownersIn` does not look into a closure's
environment. The interpreter checks it at every call of every run (`enclosesB`, sound for
`EnclosesAt`, and the cells at the call's return); `Backend2/LintTests.lean` gives a program
`Lint` accepts whose run fails it, so it is a fact about the code `Convert` generates. -/
def LendEnclosesFn : Prop :=
  ∀ (k : Backend.CheckedProg) (p : Prog) (c : CState), lirOf k = .ok (p, c) →
    ∀ (input args : List UInt8) (s s₁ s' : St) (t u : Tm) (fn : Nat) (as : List LV) (d : Fn),
      Visits p (St.init p input args) p.main s t →
      (callEntry p t).run s = .ok (some (.inr (fn, as)), s₁) → p.fns[fn]? = some d →
      EnclosesAt p d as ∧
        (Visits p { s₁ with frame := entryFrame d as } d.body s' u →
          ∀ a ∈ enclCells p d as, s'.mem.contains a)

/-- **The functions with borrow facts** (SPEC §50), read off the word IR's `Fn.facts`, not the
emitted attributes: each LIR function (by index and name) whose word IR function has a fact. The
word IR's functions are `printDec`, then the LIR's, so the LIR's `f i` is the word IR's `i + 1`. -/
def factsFns (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _) ← lirOf k
  let fp ← flatOf k
  pure <| (p.fns.toList.zipIdx.filter fun (_, i) =>
      ((fp.fns[i + 1]?).map (!·.facts.isEmpty)).getD false).map
    fun (d, i) => s!"f{i} ({d.name})"

/-- **The functions with `willreturn`** (SPEC §50), read off the word IR's `Fn.willreturn`, not
the emitted attributes: each LIR function (by index and name) of the class. -/
def willreturnFns (k : Backend.CheckedProg) : Except String (List String) := do
  let (p, _) ← lirOf k
  let fp ← flatOf k
  pure <| (p.fns.toList.zipIdx.filter fun (_, i) =>
      ((fp.fns[i + 1]?).map (·.willreturn.isSome)).getD false).map
    fun (d, i) => s!"f{i} ({d.name})"

/-- **The native target's named assumptions** (SPEC §50), each listed by `bcc trusted`:

- `NoUnwind`: no native function unwinds, so each is `nounwind`. The emitter writes no `invoke`,
  `landingpad` or `resume`; errors and cancels are branches (SPEC §47); every extern is a C
  function of `Target/Native/Runtime.lean`, C does not unwind, and the runtime cancels no thread
  (no `pthread_cancel`, so no forced unwinding at a cancellation point). `abort` and `llvm.trap`
  are traps, which LangRef's `nounwind` permits.
- `WidthClass`: a cell holds, over its life, only types of the width class its allocation carries,
  so the class's widest bytes (`Layouts.clsBytes`) hold every value it is given; a borrow's
  `dereferenceable(b)` rests on it (`Low` `.alloc`, UNPROVED there).
- `CallRelated`: a call of a `willreturn` function that a run reaches is at arguments in the
  relation, at a tagged typed world whose completion lowers to the memory: the premises of
  `total_open` (`total_open_pin` under `PinLaw`). Proved for a closed `CDerives` program at a
  plain context (`total_subrun`); assumed under a handler or catch frame, under `PinLaw`, with
  externs (`externs_every_run`, `io_every_run`) and for a `main` that loops. It is not the
  lowering's faithfulness, which says the native call is the LIR's.
- `HostStack`: the machine stack does not overflow in a call of a `willreturn` function. The
  kernel's machine has no stack bound; `total_open` says the call returns, and an overflow would
  not return to the caller.

`CallRelated` and `HostStack` are listed at each `willreturn` function (`willreturnFns`), the
others at every program the new backend compiles.
- The native runtime (`Target/Native/Runtime.lean`) meets its contracts, and `clang` compiles the
  emitted IR by LangRef. -/
def nativeAssumptions : List String :=
  ["backend (native): NoUnwind (Backend2/Driver.lean, nativeAssumptions), every function nounwind: " ++
     "no invoke, landingpad or resume is emitted; the runtime is C and cancels no thread",
   "backend (native): WidthClass (Backend2/Lower.lean, .alloc), a cell holds only its width " ++
     "class's types, so its class's widest bytes hold them (dereferenceable)",
   "backend (native): the runtime (Backend/Native/Runtime.lean) and clang"]

/-- **What the new backend's code rests on beyond the kernel** (`bcc trusted`, SPEC §29, §50,
§52): the hand-over `StackKHandOver` at each function of the program's LIR with a `stackK` consume,
as `typingReport` lists `PinLaw` at each relaxed rule; `LendEnclosesFn` at each function whose
parameters have borrow facts (`factsFns`); `CallRelated` and `HostStack` at each `willreturn`
function (`willreturnFns`); and the native target's other assumptions (`nativeAssumptions`) at
every program the new backend compiles. A site's line is left out when it has no site; one line
when the new backend does not compile the program. Sites are named by function index and name. -/
def trustedReport (k : Backend.CheckedProg) : List String :=
  match lirOf k with
  | .error _ => ["backend: the new backend does not compile the program"]
  | .ok (p, _) =>
    let fs := (p.fns.toList.zipIdx.filter fun (d, _) => d.body.hasHandOver).map
      fun (d, i) => s!"f{i} ({d.name})"
    let fs := if p.main.hasHandOver then "main" :: fs else fs
    let hand := if fs.isEmpty then [] else
      [s!"backend: StackKHandOver (Backend2/Driver.lean), the stack machines' hand-over of a " ++
        s!"level's k: {fs.length} site{if fs.length == 1 then "" else "s"}"] ++
      fs.map ("  " ++ ·)
    let encl := match factsFns k with
      | .error e => [s!"backend: the word IR of the program failed, its borrow facts unread: {e}"]
      | .ok ffs => if ffs.isEmpty then [] else
      [s!"backend: LendEnclosesFn (Backend2/Driver.lean), the native borrow facts' lends enclose " ++
        s!"their functions: {ffs.length} function{if ffs.length == 1 then "" else "s"}"] ++
        ffs.map ("  " ++ ·)
    let wr := match willreturnFns k with
      | .error e => [s!"backend: the word IR of the program failed, its willreturn class unread: {e}"]
      | .ok ws => if ws.isEmpty then [] else
      [s!"backend (native): CallRelated and HostStack (Backend2/Driver.lean, nativeAssumptions' " ++
        s!"list), a willreturn function returns (total_open; total_open_pin under PinLaw) at a " ++
        s!"reached call at related arguments (total_subrun at a closed program's plain context) " ++
        s!"with no stack overflow: {ws.length} function{if ws.length == 1 then "" else "s"}"] ++
        ws.map ("  " ++ ·)
    hand ++ encl ++ wr ++ nativeAssumptions

namespace EvNamesTests

/-! ### `evNames`'s tests  `[spec §71]`

The names whose evidence the first cut builds, decided before conversion: a program whose `tail`
clause captures a persistent value keeps its name; each exclusion, on the types and rows it reads. -/

/-- `F_Σ 1` at the operations `ops` (name, index, machine), each `1 ↠ 1`. -/
def rowT (ops : List (UInt32 × UInt32)) : CTy :=
  CTy.effOf (ops.map fun (n, i) => { n, i, q := .lin, A := .unit, B := .unit }) .unit

/-- The machine set holding `(2, 0)`. -/
def ms2 : MachSet := ({} : MachSet).insert (2, 0)

-- The name 5 at a row with no machine operation: kept.
#guard evExcludedAt [5] ms2 (.comp (rowT [(5, 0)])) false == []
#guard evExcludedAt [5] ms2 (.val (.thunk (.arr .unit (rowT [(5, 0), (3, 0)])))) false == []
-- A machine: the row holds `(2, 0)`, a machine operation, beside 5.
#guard evExcludedAt [5] ms2 (.comp (rowT [(5, 0), (2, 0)])) false == [5]
#guard evExcludedAt [5] ms2 (.val (.thunk (.arr .unit (rowT [(2, 0), (5, 0)])))) false == [5]
-- A `&` component at a row holding 5; a `&` of functions holds none at its top.
#guard evExcludedAt [5] {} (.val (.thunk (.amp (rowT [(5, 0)]) (.ret .unit)))) false == [5]
#guard evExcludedAt [5] {} (.val (.thunk (.amp (.arr .unit (rowT [(5, 0)])) .top))) false == []
-- A `ν`'s observation at a row holding 5.
#guard evExcludedAt [5] {} (.val (.thunk (.nu (rowT [(5, 0)])))) false == [5]
-- A constant whose generated helper calls a closure at a row holding 5.
#guard evExcludedAt [5] {} (.val (.thunk (.arr (.thunk (.arr .unit (rowT [(5, 0)]))) (.ret .unit)))) true == [5]
#guard evExcludedAt [5] {} (.val (.thunk (.arr (.thunk (.arr .unit (rowT [(5, 0)]))) (.ret .unit)))) false == []
-- A work whose outer row holds an evidence name, or a machine operation; and one that holds neither.
#guard (evExcludedNode [5, 6] {} 5 [{ n := 6, i := 0, q := .lin, A := .unit, B := .unit }] true).contains 5
#guard evExcludedNode [5] ms2 5 [{ n := 2, i := 0, q := .lin, A := .unit, B := .unit }] false == [5]
#guard evExcludedNode [5] ms2 5 [{ n := 3, i := 0, q := .lin, A := .unit, B := .unit }] true == []
-- A direct work of another name, 7, at an outer row holding the evidence name 5: 5 is excluded;
-- with no direct clause at the node, it is not.
#guard evExcludedNode [5] {} 7 [{ n := 5, i := 0, q := .lin, A := .unit, B := .unit }] true == [5]
#guard evExcludedNode [5] {} 7 [{ n := 5, i := 0, q := .lin, A := .unit, B := .unit }] false == []

/-- The evidence names of a program (`evNames` on its checked `main`), and its `env` names. -/
def evNamesOf (src : String) : Option (List UInt32 × List UInt32) := do
  let p ← (Frontend.parseProgram src (lib := Frontend.Sugar.libSrc)).toOption
  let r ← (Frontend.Check.checkProgram p).toOption
  let c ← r.main
  let (kinds, envs) := directFacts c
  pure (evNames c kinds envs, envs.toList.map (·.1))

/-- `yld`'s clause reads `c`, a `!` parameter of its handler: an `env` name, kept. -/
def directSrc : String := "effect Y { ctl yld() }
handler pass[A](c: !(1 => i32)): Y, A -> A = { return(a) = a; yld(k) = { let _ = c(()); k(()) } }
main -> 1 =
  let c: !(1 => i32) = !{ u -> 7 };
  with pass[1](c) { yld() }
"

#guard match evNamesOf directSrc with
  | some (keep, envs) => keep.length == 1 && keep == envs
  | none => false


end EvNamesTests

end Backend2
