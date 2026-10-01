import Frontend.Parser
import Frontend.Check.Program
import Frontend.Check.Externs
import Backend.Source
import Backend.Clos.Convert
import Backend.Clos.Collapse
import Backend.Clos.Unwind
import Backend.Kernel
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
  let p₀ ← match Frontend.parseProgram src with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.render}"
  -- The checker elaborates the program as parsed: its explicit copies (`clone(x)`) are known
  -- only there.
  let r ← match Frontend.Check.checkProgram p₀ with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.render}"
  let p ← match Frontend.Sugar.elaborate p₀ with
    | .ok (p, _) => pure p
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
    | .writeAll => pure (.io .writeAll)
    | .readInto => pure (.io .readInto)
    | .harness => throw s!"extern `{x.name}` is the model's harness and is not compiled"

/-- The program reads standard input. -/
def readsInput (file src : String) : Bool :=
  match checkedOf file src with
  | .ok k => match k.io with
    | some m => m.caps.any (·.name == "stdin")
    | none => false
  | .error _ => false

/-- The closure IR, and its layout types when collapsing found them. -/
def closTypesOf (file src : String) : Except String (Clos.Prog × Option Clos.Types) := do
  let k ← checkedOf file src
  let p ← match k.io with
    | none => Clos.convert k.main.e
    | some m => Clos.convertMain (← extImpls m) m.loopB.isSome k.main.e
  pure (← p.unwind).collapseT

def closOf (file src : String) : Except String Clos.Prog := return (← closTypesOf file src).1

/-- The flat IR; with `counts`, the entry writes the run's counts after the report. -/
def flatOf (file src : String) (counts : Bool := false) : Except String Flat.Prog := do
  let (p, T) ← closTypesOf file src
  Flat.lower p counts T

/-- The program as WAT; with `counts`, it counts dispatched calls and writes the run's counts after
the report. -/
def compileWat (file src : String) (counts : Bool := false) : Except String String := do
  pure (Wasm.printModule (Wasm.lowerProg (← flatOf file src counts) counts))

/-! ### Timings

`bcc compile --timings` runs the same pipeline as `compileWat`, stage by stage, and writes each
stage's time and the size of what it produced to standard error. It also times the two
whole-program analyses the later stages run (`Clos.Prog.flow`, `Clos.Prog.types`) on their own,
on the program each stage receives. -/

/-- The nodes of a closure-IR term. -/
def Clos.Tm.size : Clos.Tm → Nat
  | .letv _ e b => 1 + e.size + b.size
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => 1 + b.size
  | .case _ _ b₁ _ b₂ => 1 + b₁.size + b₂.size
  | _ => 1

def Clos.Prog.size (p : Clos.Prog) : Nat := p.codes.foldl (fun k c => k + c.body.size) p.main.size

mutual
def Flat.Stmt.size : Flat.Stmt → Nat
  | .ite _ t e => 1 + Flat.Stmt.sizes t + Flat.Stmt.sizes e
  | .switch _ cs d => 1 + Flat.Stmt.sizess cs + Flat.Stmt.sizes d
  | _ => 1
def Flat.Stmt.sizes : List Flat.Stmt → Nat
  | [] => 0
  | s :: ss => s.size + Flat.Stmt.sizes ss
def Flat.Stmt.sizess : List (List Flat.Stmt) → Nat
  | [] => 0
  | c :: cs => Flat.Stmt.sizes c + Flat.Stmt.sizess cs
end

/-- `f ()`, computed when the action runs. -/
@[noinline] def runPure (f : Unit → α) : IO α := pure (f ())

/-- Run `f` and write its time and the size of its result to standard error; add the time to
`total` unless the stage is an analysis timed on its own (`total = none`). -/
@[noinline] def timed (total : Option (IO.Ref Nat)) (name : String) (size : α → String)
    (f : Unit → Except String α) : IO (Except String α) := do
  let t₀ ← IO.monoNanosNow
  let r ← runPure f
  let t₁ ← IO.monoNanosNow
  if let some tot := total then tot.modify (· + (t₁ - t₀))
  if let .ok a := r then
    let s := size a
    IO.eprintln s!"{name}: {(t₁ - t₀) / 1000000} ms{if s.isEmpty then "" else ", " ++ s}"
  pure r

/-- The size of a flow solution: its keys, edges and the values the keys hold. -/
def flowSize : Option Clos.Solver → String
  | some S => s!"{S.set.size} keys, {S.succ.foldl (· + ·.size) 0} edges, {S.set.foldl (· + ·.size) 0} values held"
  | none => "no solution"

/-- `compileWat`, timing each stage (`bcc compile --timings`). The total is the stages' times,
without the analyses timed on their own. -/
def compileWatTimed (file src : String) : IO (Except String String) := do
  let tot ← IO.mkRef 0
  let stage {α} := @timed α (some tot)
  let analysis {α} := @timed α none
  let go : ExceptT String IO String := do
    let p₀ ← ExceptT.mk <| stage "parse" (fun (p : Frontend.Program) => s!"{p.decls.length} declarations")
      fun _ => match Frontend.parseProgram src with
        | .ok p => pure p
        | .error e => throw s!"{file}:{e.render}"
    let r ← ExceptT.mk <| stage "check" (fun _ => "") fun _ =>
      match Frontend.Check.checkProgram p₀ with
        | .ok r => pure r
        | .error e => throw s!"{file}:{e.render}"
    let p ← ExceptT.mk <| stage "elaborate" (fun (p : Frontend.Program) => s!"{p.decls.length} declarations")
      fun _ => match Frontend.Sugar.elaborate p₀ with
        | .ok (p, _) => pure p
        | .error e => throw s!"{file}:{e.render}"
    let some c := r.main | throw s!"{file}: no `main`"
    let io ← ExceptT.mk <| stage "io main" (fun _ => "") fun _ =>
      match Frontend.Check.ioMainOf p c with
        | .ok io => pure io
        | .error e => throw s!"{file}: {e}"
    let clos ← ExceptT.mk <| stage "convert" (fun (q : Clos.Prog) =>
        s!"{q.codes.size} codes, {q.size} nodes") fun _ => match io with
      | none => Clos.convert c.e
      | some m => do Clos.convertMain (← extImpls m) m.loopB.isSome c.e
    let _ ← ExceptT.mk <| analysis "  flow (converted)" flowSize fun _ =>
      pure (Clos.solve clos.codes clos.constraints (1 <<< 40))
    let _ ← ExceptT.mk <| analysis "  types (converted)" (fun (T : Clos.Types) =>
      s!"{T.rep.size} type nodes") fun _ => clos.types
    let (col, colT) ← ExceptT.mk <| stage "collapse" (fun (q : Clos.Prog × Option Clos.Types) =>
        s!"{q.1.codes.size} codes, {q.1.liveCodes.size} live, {q.1.size} nodes") fun _ =>
      pure clos.collapseT
    let _ ← ExceptT.mk <| analysis "  flow (collapsed)" flowSize fun _ =>
      pure (Clos.solve col.codes col.constraints (1 <<< 40))
    let _ ← ExceptT.mk <| analysis "  types (collapsed)" (fun (T : Clos.Types) =>
      s!"{T.rep.size} type nodes") fun _ => col.types
    let flat ← ExceptT.mk <| stage "flat" (fun (q : Flat.Prog) =>
        s!"{q.fns.size} functions, {q.fns.foldl (fun k f => k + Flat.Stmt.sizes f.body) 0} statements")
      fun _ => Flat.lower col false colT
    let wasm ← ExceptT.mk <| stage "wasm" (fun (m : Wasm.Module) => s!"{m.funcs.length} functions")
      fun _ => pure (Wasm.lowerProg flat)
    let wat ← ExceptT.mk <| stage "print" (fun (s : String) => s!"{s.utf8ByteSize} bytes")
      fun _ => pure (Wasm.printModule wasm)
    pure wat
  let r ← go.run
  IO.eprintln s!"total: {(← tot.get) / 1000000} ms"
  pure r

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

/-! ### Kernel programs

The programs of `Core/` that have no surface form (`Backend/Kernel.lean`): closed terms, compiled
as `main`'s erasure is. -/

/-- A kernel program's closure IR and layout types. -/
def closTypesOfExpr (e : BoCa.Expr) : Except String (Clos.Prog × Option Clos.Types) := do
  pure (← (← Clos.convert e).unwind).collapseT

/-- A kernel program's WAT. -/
def compileWatExpr (e : BoCa.Expr) (counts : Bool := false) : Except String String := do
  let (p, T) ← closTypesOfExpr e
  pure (Wasm.printModule (Wasm.lowerProg (← Flat.lower p counts T) counts))

/-- A kernel program at stage `stage`'s interpreter. -/
def interpStageExpr (stage : String) (e : BoCa.Expr) : Except String Output := do
  match stage with
  | "source" => interpSource runFuel e
  | "clos" => Clos.interp runFuel (← closTypesOfExpr e).1 []
  | "flat" => do
    let (p, T) ← closTypesOfExpr e
    Flat.interp runFuel (← Flat.lower p false T) []
  | "flat-counts" => do
    let (p, T) ← closTypesOfExpr e
    Flat.interp runFuel (← Flat.lower p true T) []
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
