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

/-- **The direct calls the checked facts license**  `[spec §48]`: for each static name, for each of
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

/-- The LIR of a checked program, and what the conversion read. -/
def lirOf (k : Backend.CheckedProg) (census : Bool := false) : Except String (Prog × CState) := do
  let c := k.main
  let (exts, ncaps, loops) ← match k.io with
    | none => pure ([], 0, false)
    | some m => pure (← extsOf m, m.caps.length, m.loopB.isSome)
  let ctx := c.ctx.map fun s => (s.ty, s.live)
  let (p, st) ← convertProg exts ctx c.t c.C ncaps loops census (directFacts c)
  return ({ p with exits := c.exitsOnDivError }, st)

/-- **The effect erasure's postcondition**, for a program (`bcc lir --erasure`, SPEC §48): the LIR
has no `handle` and no `perform`, so a program the new backend compiles has none left. The line
counts, at a compiled program, the `handle`, `perform` and `raise` nodes the conversion erased
(each `use` body once per key); at any program, the `handle` nodes left for the state machines
(a clause of kind `once` or `stored`: the stored-continuation sites, N3) and those left by a rule
not built (`tail+state`, `resume-or-cancel`, or a tail-resumptive clause whose direct call the
facts do not license). -/
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
    s!"erased handles {r "handle"} performs {r "perform"} raises {r "raise"} left {stored} {other}"
  | .error _ => s!"outside left {stored} {other}"

/-- Convert and lint a program (`bcc lir --lint`): an error outside the pure fragment, or the
lint's. -/
def lintOf (k : Backend.CheckedProg) : Except String Unit := do
  let (p, _) ← lirOf k
  Lint.lint p

/-- The checker's cell classes (`Checked.cells`) at LIR types. -/
def cellsOf (k : Backend.CheckedProg) : List (List LTy) :=
  k.main.cells.map fun c => c.tys.filterMap fun t => (ofV t).toOption

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
