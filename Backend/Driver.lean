import Frontend.Parser
import Frontend.Check.Program
import Frontend.Check.Externs
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
output of each stage's interpreter. A program with capabilities (SPEC §11) is compiled with
each extern bound to its host implementation, and run at the source stage as `run_io` with the
model of each extern.
-/

namespace Backend

/-- The fuel of every interpreter. -/
def runFuel : Nat := 100000000

/-- A checked program: the source, `main`, and its capabilities if it has any. -/
structure CheckedProg where
  prog : Frontend.Program
  main : Frontend.Check.Checked
  io : Option Frontend.Check.IOMain

/-- Parse and check `src`; a `main` with externs must be a standard I/O program (SPEC §11). -/
def checkedOf (file src : String) : Except String CheckedProg := do
  let p ← match Frontend.parseProgram src with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.render}"
  let p ← match Frontend.Sugar.elaborate p with
    | .ok (p, _) => pure p
    | .error e => throw s!"{file}:{e.render}"
  let r ← match Frontend.Check.checkProgram p with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.render}"
  let some c := r.main | throw s!"{file}: no `main`"
  match Frontend.Check.ioMainOf p c with
  | .ok io => pure ⟨p, c, io⟩
  | .error e => throw s!"{file}: {e}"

/-- The host implementation of each extern, in declaration order. -/
def extImpls (m : Frontend.Check.IOMain) : Except String (List Clos.ExtImpl) :=
  m.externs.mapM fun x => match x.role with
    | .cap fd => pure (.cap fd)
    | .readByte => pure (.io .readByte)
    | .writeByte => pure (.io .writeByte)
    | .harness => throw s!"extern `{x.name}` is the model's harness and is not compiled"

/-- The program reads standard input. -/
def readsInput (file src : String) : Bool :=
  match checkedOf file src with
  | .ok k => match k.io with
    | some m => m.caps.any (·.name == "stdin")
    | none => false
  | .error _ => false

def closOf (file src : String) : Except String Clos.Prog := do
  let k ← checkedOf file src
  match k.io with
  | none => Clos.convert k.main.e
  | some m => Clos.convertMain (← extImpls m) m.loopB.isSome k.main.e

/-- The flat IR; with `counts`, the entry writes the run's counts after the report. -/
def flatOf (file src : String) (counts : Bool := false) : Except String Flat.Prog := do
  Flat.lower (← closOf file src) counts

/-- The program as WAT; with `counts`, it counts dispatched calls and writes the run's counts after
the report. -/
def compileWat (file src : String) (counts : Bool := false) : Except String String := do
  pure (Wasm.printModule (Wasm.lowerProg (← flatOf file src counts) counts))

/-- The model run of a program with capabilities: `run_io` checked, with every extern's model
(`Frontend.Check.IORun`). -/
def ioRunOf (file : String) (k : CheckedProg) (m : Frontend.Check.IOMain) :
    Except String Frontend.Check.IORun := do
  let w ← match Frontend.Check.ioWrapper k.prog m with
    | .ok w => pure w
    | .error e => throw s!"{file}: {e}"
  match Frontend.Check.ioRunOf w with
  | .ok r => pure r
  | .error e => throw s!"{file}: {e}"

/-- A stage's output on a source file, with `input` as standard input. -/
def interpStage (stage file src : String) (input : List UInt8) : Except String Output := do
  match stage with
  | "source" =>
    let k ← checkedOf file src
    match k.io with
    | none => interpSource runFuel k.main.e
    | some m =>
      let r ← ioRunOf file k m
      if r.loops then interpIOLoop runFuel (r.expr input) else interpIO runFuel (r.expr input)
  | "clos" => Clos.interp runFuel (← closOf file src) input
  | "flat" => Flat.interp runFuel (← flatOf file src) input
  | "flat-counts" => Flat.interp runFuel (← flatOf file src true) input
  | _ => throw s!"unknown stage `{stage}`"

/-- The program's trusted boundaries (`bcc trusted`).  `[spec §11]` -/
def trusted (file src : String) : Except String String := do
  let p ← match Frontend.parseProgram src with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.render}"
  let p ← match Frontend.Sugar.elaborate p with
    | .ok (p, _) => pure p
    | .error e => throw s!"{file}:{e.render}"
  let xs ← match Frontend.Check.externs p.decls.toArray with
    | .ok xs => pure xs
    | .error e => throw s!"{file}:{e.render}"
  let lines := Frontend.Check.trustedReport xs
  let unproved := xs.filter fun (n, _) => match Frontend.Check.findExtern n with
    | some x => x.host.isSome
    | none => true
  pure ("\n".intercalate lines ++ "\n" ++
    s!"unproved boundaries: {unproved.length}" ++
    (if unproved.isEmpty then "" else s!" ({", ".intercalate (unproved.map (·.1))})") ++
    "\nalways trusted: the allocator and runtime (Backend/Wasm/Runtime.lean), the WAT printer, " ++
    "wasmtime\n")

end Backend
