import Backend.Driver
import Backend2.Convert
import Backend2.Print
import Backend2.Interp

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

/-- A stage of the new backend on a checked program: `lir` is the LIR interpreter. -/
def interpStage (stage : String) (k : Except String Backend.CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String Backend.Output := do
  match stage with
  | "lir" => runLIR (← lirOf (← k)).1 Backend.runFuel input args
  | _ => throw s!"unknown stage `{stage}`"

end Backend2
