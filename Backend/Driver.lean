import Frontend.Parser
import Frontend.Check.Program
import Backend.Source
import Backend.Clos.Convert
import Backend.Clos.Interp
import Backend.Flat.Lower
import Backend.Flat.Interp
import Backend.Wasm.Lower
import Backend.Wasm.Print

/-!
# Backend — driver

From source text to each stage: the checked erasure of `main`, its closure-IR form, and the
report of each stage's interpreter.
-/

namespace Backend

/-- The fuel of every interpreter. -/
def runFuel : Nat := 100000000

/-- The erasure of a closed `main`, from checked source. -/
def checkedMain (file src : String) : Except String BoCa.Expr := do
  let p ← match Frontend.parseProgram src with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.render}"
  let r ← match Frontend.Check.checkProgram p with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.render}"
  let some c := r.main | throw s!"{file}: no `main`"
  if !c.ctx.isEmpty then throw s!"{file}: `main` has externs; only closed programs are compiled"
  pure c.e

def closOf (file src : String) : Except String Clos.Prog := do
  Clos.convert (← checkedMain file src)

def flatOf (file src : String) : Except String Flat.Prog := do
  Flat.lower (← closOf file src)

/-- The program as WAT. -/
def compileWat (file src : String) : Except String String := do
  pure (Wasm.printModule (Wasm.lowerProg (← flatOf file src)))

/-- A stage's report on a source file. -/
def interpStage (stage file src : String) : Except String String := do
  match stage with
  | "source" => interpSource runFuel (← checkedMain file src)
  | "clos" => Clos.interp runFuel (← closOf file src)
  | "flat" => Flat.interp runFuel (← flatOf file src)
  | _ => throw s!"unknown stage `{stage}`"

end Backend
