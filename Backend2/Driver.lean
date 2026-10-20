import Backend.Driver
import Backend2.Convert
import Backend2.Print
import Backend2.Interp
import Backend2.Lower
import Backend2.Flow

/-!
# Backend2 — driver

From a checked program (`Backend.CheckedProg`, the one check every stage shares) to the new
backend's stages. This module is the new backend's one contact with the frontend: it reads
`Checked`'s typed term, context, type and the externs' roles, and hands the stages plain data.
It is outside the import fence (`scripts/check-backend2.sh`).
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core

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

/-- The LIR of a checked program, and what the conversion read. -/
def lirOf (k : Backend.CheckedProg) : Except String (Prog × CState) := do
  let c := k.main
  let (exts, ncaps, loops) ← match k.io with
    | none => pure ([], 0, false)
    | some m => pure (← extsOf m, m.caps.length, m.loopB.isSome)
  let ctx := c.ctx.map fun s => (s.ty, s.live)
  convertProg exts ctx c.t c.C ncaps loops

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
  let (p, _) ← lirOf k
  let L ← layoutsOf k p
  Low.lowerProg p L (Flow.known p L) counts

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
