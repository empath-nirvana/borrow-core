import Backend.Driver
import Backend2.Convert
import Backend2.Print
import Backend2.Interp
import Backend2.Lower
import Backend2.Flow
import Backend2.Frames
import Backend2.LitViews
import Backend2.Lint
import Frontend.Check.Handled

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

/-- The `handle` nodes of a typed term, within the depth `fuel`. -/
def hnodes : Nat → TExpr → List HNode
  | 0, _ => []
  | f + 1, t =>
    let here : List HNode := match t with
      | .effHandleV _ _ S E _ n _ _ _ ks _ _ tc _ => [⟨n, E, S, ks, tc.erase⟩]
      | .effHandleVB _ _ S E _ n _ _ _ _ ks _ _ tc _ => [⟨n, E, S, ks, tc.erase⟩]
      | _ => []
    here ++ t.children.flatMap fun (_, c) => hnodes f c

/-- **The direct calls the checked facts license**  `[spec §47]`: for each static name, for each of
its operations, whether every `handle` node of the name
- classifies the operation's clause `tail` (`ks`, `classifyHandler_sound`),
- holds names of the clause's own code (`handlerNames`; its row's names where it has none) that
  `main`'s flow record cannot catch (`cond2B` at `Checked.flows`, which gives
  `Checked.unhandledNames`: no frame between a `perform` and its handler catches them), and
- holds one clause for it, closed (`closedAt 0`), at one outer row and one signature,
so that the clause a `perform` reaches is known and needs nothing from its handler's frame. -/
def directFacts (c : Frontend.Check.Checked) : Std.HashMap UInt32 (List Bool) := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let flows := c.flows
  let mut out : Std.HashMap UInt32 (List Bool) := {}
  for h in nodes do
    if out.contains h.n then continue
    let same := nodes.filter (·.n == h.n)
    let hs := match h.H with | .pair _ hs => some hs | _ => none
    let ok := h.E.zipIdx.map fun (_, j) =>
      same.all fun g =>
        let gs := match g.H with | .pair _ hs => some hs | _ => none
        let names := Check.handlerNames g.E g.H
        let row := (g.S.map (·.n)).eraseDups
        let cl := gs.bind fun hs => Check.clauseExpr hs j
        (g.ks[j]?.map (·.kind)) == some .tail &&
          Frontend.Check.cond2B flows (Frontend.Check.cond2Names row ((names[j]?).getD none)) &&
          (match cl with | some e => closedAt 0 e | none => false) &&
          cl == hs.bind (fun hs => Check.clauseExpr hs j) &&
          decide (CTy.effOf g.S .unit = CTy.effOf h.S .unit) && decide (g.E = h.E)
    out := out.insert h.n ok
  return out

/-- **The program's machine operations**  `[spec §49]`: each control operation `(n, j)` whose
clause at some `handle` node of `n` is neither abortive nor called where it is performed
(`directFacts`): its `perform` suspends the computation, and the node's drive runs the clause on
the argument and `κ`. Read off the nodes' kinds (`ks`, `classifyHandler_sound`) and the direct
calls' facts. -/
def machineOps (c : Frontend.Check.Checked) : MachSet := Id.run do
  let nodes := hnodes Frontend.Check.copiesFuel c.t
  let direct := directFacts c
  let mut out : MachSet := {}
  for h in nodes do
    for (k, j) in h.ks.zipIdx do
      unless k.kind == .abortive || (k.kind == .tail && (direct.getD h.n [])[j]? == some true) do
        out := out.insert (h.n, j.toUInt32)
  return out

/-- The checker's cell classes (`Checked.cells`) at LIR types. -/
def cellsOf (k : Backend.CheckedProg) : List (List LTy) :=
  k.main.cells.map fun c => c.tys.filterMap fun t => (ofV (machineOps k.main) t).toOption

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

/-- The LIR of a checked program, and what the conversion read. With state machines (SPEC §49), the
layouts of the converted program decide the calls in tail position that close a loop
(`tailPass`) and the machines whose state is a cell (`cellPass`). -/
def lirOf (k : Backend.CheckedProg) (census : Bool := false) : Except String (Prog × CState) := do
  let c := k.main
  let (exts, ncaps, loops) ← match k.io with
    | none => pure ([], 0, false)
    | some m => pure (← extsOf m, m.caps.length, m.loopB.isSome)
  let ctx := c.ctx.map fun s => (s.ty, s.live)
  let (p, st) ← convertProg exts ctx c.t c.C ncaps loops census (directFacts c) (machineOps c)
  let p := { p with exits := c.exitsOnDivError }
  if st.done.isEmpty then return (p, st)
  -- A call in tail position whose callee's suspended computations may be the machine's own
  -- closes a loop of tail calls, and passes its outcome on (SPEC §49, `tailPass`).
  let (g, m) ← Lay.places p
  let L₁ := Lay.resolve p g m (cellsOf k)
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
  let (g, m) ← Lay.places p
  let L := Lay.resolve p g m (cellsOf k)
  let recursive (kc : Nat) : Bool := match L.codeClass[kc]? with
    | some cls => L.isRec cls
    | none => false
  let (p₂, st₂) ← cellPass st recursive
  return ({ p with fns := p₂.fns, codes := p₂.codes, ty := p₂.ty }, st₂)

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
  let direct := directFacts c
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

/-- The layouts of a program's LIR. -/
def layoutsOf (k : Backend.CheckedProg) (p : Prog) : Except String Lay.Layouts := do
  let (g, m) ← Lay.places p
  pure (Lay.resolve p g m (cellsOf k))

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

/-- The word IR of a checked program by the new backend; with `counts`, the counting build. -/
def flatOf (k : Backend.CheckedProg) (counts : Bool := false) : Except String Backend.Flat.Prog := do
  let (p, cs) ← lirOf k
  let L ← layoutsOf k p
  let fs := Flow.solution p L
  let p := LitViews.rewrite p cs.lits fs.sets
  Low.lowerProg p L (Flow.known p L fs) (Frames.framed p) counts

/-- The program as WAT by the new backend. -/
def watOf (k : Backend.CheckedProg) (counts : Bool := false) : Except String String := do
  pure (Backend.Wasm.printModule (Backend.Wasm.lowerProg (← flatOf k counts) counts))

/-- The program as LLVM IR by the new backend. -/
def llOf (k : Backend.CheckedProg) (counts : Bool := false) : Except String String := do
  Backend.Native.printProg (← flatOf k counts) Backend.nativeTriple counts

/-- **The new backend's compile, timed** (`bcc compile --backend new --timings`): `file`'s WAT, each
stage's time and output size written to standard error as `Backend.compileWatTimed` writes the
old backend's, then their total. The stages are the frontend's (parse, check, `main`'s I/O) and the
new backend's (the LIR, its layouts, the 0-CFA, the word IR, Wasm, the printed module).
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
    let (p, cs) ← ExceptT.mk <| stage "lir" (fun (q : Prog × CState) =>
        s!"{q.1.fns.size} functions, {q.1.codes.size} codes") fun _ => lirOf k
    let L ← ExceptT.mk <| stage "layout" (fun _ => "") fun _ => layoutsOf k p
    let fs ← ExceptT.mk <| stage "flow" (fun _ => "") fun _ => pure (Flow.solution p L)
    let flat ← ExceptT.mk <| stage "lower" (fun (q : Backend.Flat.Prog) => s!"{q.fns.size} functions")
      fun _ => do
        let p := LitViews.rewrite p cs.lits fs.sets
        Low.lowerProg p L (Flow.known p L fs) (Frames.framed p) false
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
