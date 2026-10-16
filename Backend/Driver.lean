import Frontend.Parser
import Frontend.Check.Program
import Frontend.Check.Externs
import Backend.Source
import Backend.Falsify
import Backend.Clos.Convert
import Backend.Clos.Collapse
import Backend.Clos.Unwind
import Backend.Clos.Capture
import Backend.Clos.Poly
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

/-- The wasm stack `wasmtime` is run with, in bytes: 64 MiB. A recursion under `bounded`
(SPEC §20) has a budget of depth (`lib/rec.bc`, `rec_budget`) calibrated against it: at the
budget, a recursion's frames must fit with room left for the finalisers an unwind runs.
Provisional: the calibration is by measurement (`docs/rec-effect/bounded-deep.md`). -/
def wasmStackBytes : Nat := 67108864

/-- The arguments `wasmtime run` is given before the module: tail calls, and the stack. -/
def wasmtimeArgs : Array String :=
  #["run", "-W", "tail-call=y", "-W", s!"max-wasm-stack={wasmStackBytes}"]

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
    | .clockCap => pure .clockCell
    | .readByte => pure (.io .readByte)
    | .writeByte => pure (.io .writeByte)
    | .writeAll => pure (.io .writeAll)
    | .readInto => pure (.io .readInto)
    | .clockNow => pure (.io .clockNow)
    | .clockSleep => pure (.io .clockSleep)
    | .harness => throw s!"extern `{x.name}` is the model's harness and is not compiled"

/-- The program reads standard input. -/
def readsInput (file src : String) : Bool :=
  match checkedOf file src with
  | .ok k => match k.io with
    | some m => m.caps.any (·.name == "stdin")
    | none => false
  | .error _ => false

/-- A converted program with its effects lowered and its codata collapsed, and its layout types
when they were found. A program whose layout types fail is lowered again with the control
operations' answers carried as variants (`Clos.Ops.wrapsAnswers`): a code that suspends at
operations of different answer types is resumed at one type then.  `[spec §34]` -/
def lowerEffects (p : Clos.Prog) : Except String (Clos.Prog × Option Clos.Types) := do
  let r := (← (← p.capture).unwind).collapseT
  if r.2.isSome then return r
  let r' := (← (← p.capture (wrapAnswers := true)).unwind).collapseT
  pure (if r'.2.isSome then r' else r)

/-- The closure IR, and its layout types when collapsing found them. -/
def closTypesOf (file src : String) : Except String (Clos.Prog × Option Clos.Types) := do
  let k ← checkedOf file src
  let p ← match k.io with
    | none => Clos.convert k.main.e
    | some m => Clos.convertMain (← extImpls m) m.loopB.isSome k.main.e
  lowerEffects p

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
    let clos ← ExceptT.mk <| stage "effects" (fun (q : Clos.Prog) =>
        s!"{q.codes.size} codes, {q.size} nodes") fun _ => do (← clos.capture).unwind
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
def ioRunOf (file : String) (k : CheckedProg) (m : Frontend.Check.IOMain)
    (args : List UInt8 := []) : Except String Frontend.Check.IORun := do
  let w ← match Frontend.Check.ioWrapper k.prog m args with
    | .ok w => pure w
    | .error e => throw s!"{file}: {e}"
  match Frontend.Check.ioRunOf w with
  | .ok r => pure r
  | .error e => throw s!"{file}: {e}"

/-- A stage's output on a source file, with `input` as standard input and `args` as the
arguments' stream (each argument followed by `0`, SPEC §34). -/
def interpStage (stage file src : String) (input : List UInt8) (args : List UInt8 := []) :
    Except String Output := do
  match stage with
  | "source" =>
    let k ← checkedOf file src
    match k.io with
    | none => interpSource runFuel k.main.e
    | some m =>
      let r ← ioRunOf file k m args
      if r.loops then interpIOLoop runFuel (r.expr input) else interpIO runFuel (r.expr input)
  | "clos" => Clos.interp runFuel (← closOf file src) input args
  | "flat" => Flat.interp runFuel (← flatOf file src) input args
  | "flat-counts" => Flat.interp runFuel (← flatOf file src true) input args
  | _ => throw s!"unknown stage `{stage}`"

/-! ### The falsifier

`bcc interp --check fresh|tags` and `--alloc least` (`Backend/Falsify.lean`,
docs/async-capabilities.md §6.1): the source stage on the falsifier's machine. The run's output,
and its statistics. -/

/-- The falsifier's options, by name: `least`, `fresh` or `tags`. -/
def falsifyOpts : String → Except String Falsify.Opts
  | "least" => pure ⟨.least, false⟩
  | "fresh" => pure ⟨.fresh, false⟩
  | "tags" => pure ⟨.fresh, true⟩
  | m => throw s!"unknown check `{m}` (expected `fresh` or `tags`, or `--alloc least`)"

/-- The source stage of a source file, on the falsifier's machine under `o`. -/
def interpChecked (o : Falsify.Opts) (file src : String) (input : List UInt8)
    (args : List UInt8 := []) : Except String (Output × String) := do
  let k ← checkedOf file src
  match k.io with
  | none => Falsify.interpSource o runFuel k.main.e
  | some m =>
    let r ← ioRunOf file k m args
    if r.loops then Falsify.interpIOLoop o runFuel (r.expr input)
    else Falsify.interpIO o runFuel (r.expr input)

/-- A closed term on the falsifier's machine under `o`. -/
def interpCheckedExpr (o : Falsify.Opts) (e : BoCa.Expr) : Except String (Output × String) :=
  Falsify.interpSource o runFuel e

/-! ### Kernel programs

The programs of `Core/` that have no surface form (`Backend/Kernel.lean`): closed terms, compiled
as `main`'s erasure is. -/

/-- A kernel program's closure IR and layout types. -/
def closTypesOfExpr (e : BoCa.Expr) : Except String (Clos.Prog × Option Clos.Types) := do
  lowerEffects (← Clos.convert e)

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

/-- What the typing of `main` rests on (SPEC §29): nothing beyond Core's theorems, or `PinLaw` at
each relaxed rule the derivation uses. -/
def typingReport (c : Frontend.Check.Checked) : String :=
  match c.pins with
  | [] => "typing: unconditional: a CDerives derivation (fundamentalC, adequacyD)"
  | ps =>
    let ps := ps.eraseDups
    let field (r : String) : String := if r == "R2" then "PinLaw.loop" else "PinLaw.stop"
    "typing: PinLaw (Core/PinLaw.lean), the hypothesis of fundamentalC_pin and adequacyD_pin: " ++
      s!"{ps.length} site{if ps.length == 1 then "" else "s"}" ++
      String.join (ps.map fun q => s!"\n  {q.rule} at {q.line}:{q.col}: {field q.rule}")

/-- The program's trusted boundaries (`bcc trusted`).  `[spec §11, §29]` -/
def trusted (file src : String) : Except String String := do
  let p ← match Frontend.parseProgram src with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.render}"
  let r ← match Frontend.Check.checkProgram p with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.render}"
  let typing := (r.main.map typingReport).toList
  let p ← match Frontend.Sugar.elaborate p with
    | .ok (p, _) => pure p
    | .error e => throw s!"{file}:{e.render}"
  let xs ← match Frontend.Check.externs p.decls.toArray with
    | .ok xs => pure xs
    | .error e => throw s!"{file}:{e.render}"
  -- The externs `main`'s erasure uses: a library's extern that the program never reaches is not
  -- in its trusted base (SPEC §34). The last declared is at index 0 of `main`'s context.
  let xs := match r.main with
    | some c => xs.zipIdx.filterMap fun (x, i) =>
        if BoCa.Fig16.LogRel.Core.occ (xs.length - 1 - i) c.e then some x else none
    | none => xs
  let lines := Frontend.Check.trustedReport xs
  let unproved := xs.filter fun (n, _) => match Frontend.Check.findExtern n with
    | some x => x.host.isSome
    | none => true
  pure ("\n".intercalate (lines ++ typing) ++ "\n" ++
    s!"unproved boundaries: {unproved.length}" ++
    (if unproved.isEmpty then "" else s!" ({", ".intercalate (unproved.map (·.1))})") ++
    "\nalways trusted: the allocator and runtime (Backend/Wasm/Runtime.lean), the WAT printer, " ++
    "wasmtime\n")

end Backend
