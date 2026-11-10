import Frontend.Parser
import Frontend.Check.Program
import Frontend.Check.Externs
import Reference.Source
import Pipeline.Driver
import Reference.Falsify
import Backend.Clos.Convert
import Backend.Clos.Collapse
import Backend.Clos.Unwind
import Backend.Clos.Capture
import Backend.Clos.Poly
import Backend.Kernel
import Backend.Clos.Interp
import Backend.Flat.Lower
import Target.Flat.Interp
import Target.Wasm.Lower
import Target.Wasm.Print
import Target.Native.Lower
import Target.Native.Runtime

/-!
# Backend — driver

From source text to each stage: the checked erasure of `main`, its closure-IR form, and the
output of each stage's interpreter. A program with capabilities (SPEC §11) is compiled with
each extern bound to its host implementation, and run at the source stage as `run_io` with the
model of each extern. The checked program and the plumbing every backend shares are
`Pipeline/Driver.lean`'s.
-/

namespace Backend

/-- The host implementation of each extern of `run_io`, in declaration order: an operation, or
the harness's make or take of a stream's capability cell. A capability is not an extern of
`run_io`: the harness makes it. -/
def extImpls (xs : List Frontend.Check.ExternSpec) : Except String (List Clos.ExtImpl) :=
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
  capStream : Frontend.Check.IOStream → Clos.CapStream
    | .input => .input
    | .output => .output
    | .clock => .clock
    | .args => .args

/-- A converted program with its effects lowered and its codata collapsed, and its layout types
when they were found. A program whose layout types fail is lowered again with the control
operations' answers carried as variants (`Clos.Ops.wrapsAnswers`): a code that suspends at
operations of different answer types is resumed at one type then.  `[spec §34]` -/
def lowerEffects (p : Clos.Prog) : Except String (Clos.Prog × Option Clos.Types) := do
  let r := (← (← p.capture).unwind).collapseT
  if r.2.isSome then return r
  let r' := (← (← p.capture (wrapAnswers := true)).unwind).collapseT
  pure (if r'.2.isSome then r' else r)

/-- The closure IR of a checked program, and its layout types when collapsing found them. -/
def CheckedProg.closTypes (k : CheckedProg) : Except String (Clos.Prog × Option Clos.Types) := do
  let (p, c) ← match ← k.runIO with
    | none => pure (← Clos.convert k.main.e, k.main)
    | some (r, xs) => pure (← Clos.convertMain (← extImpls xs) r.loops r.c.e (Frontend.Check.IORun.arg []).1, r.c)
  let (p, T) ← lowerEffects p
  pure ({ p with exits := c.exitsOnDivError }, T)

/-- The closure IR of a checked program. -/
def CheckedProg.clos (k : CheckedProg) : Except String Clos.Prog := return (← k.closTypes).1

/-- The flat IR; with `counts`, the entry writes the run's counts after the report. -/
def CheckedProg.flat (k : CheckedProg) (counts : Bool := false) : Except String Flat.Prog := do
  let (p, T) ← k.closTypes
  Flat.lower p counts T

/-- The program as WAT; with `counts`, it counts dispatched calls and writes the run's counts after
the report. -/
def CheckedProg.wat (k : CheckedProg) (counts : Bool := false) : Except String String := do
  pure (Wasm.printModule (Wasm.lowerProg (← k.flat counts) counts))

/-- The closure IR of a source file, and its layout types. -/
def closTypesOf (file src : String) : Except String (Clos.Prog × Option Clos.Types) := do
  (← checkedOf file src).closTypes

def closOf (file src : String) : Except String Clos.Prog := return (← closTypesOf file src).1

/-- The flat IR of a source file. -/
def flatOf (file src : String) (counts : Bool := false) : Except String Flat.Prog := do
  (← checkedOf file src).flat counts

/-- A source file as WAT. -/
def compileWat (file src : String) (counts : Bool := false) : Except String String := do
  (← checkedOf file src).wat counts

/-! ### The native target  `[spec §40]`

`bcc compile --target native` prints the program's LLVM IR (`Target/Native/Lower.lean`), for
the host's target; `bcc run --native` builds it with `clang`, beside the runtime
(`Target/Native/Runtime.lean`), and runs it. -/

/-- The program as LLVM IR; with `counts`, it counts dispatched calls and copies and writes the
run's counts after the report. -/
def CheckedProg.ll (k : CheckedProg) (counts : Bool := false) : Except String String := do
  Native.printProg (← k.flat counts) nativeTriple counts

/-- A source file as LLVM IR. -/
def compileLL (file src : String) (counts : Bool := false) : Except String String := do
  (← checkedOf file src).ll counts

/-! ### Timings

`bcc compile --timings` runs the same pipeline as `compileWat`, stage by stage, and writes each
stage's time and the size of what it produced to standard error. It also times the two
whole-program analyses the later stages run (`Clos.Prog.flow`, `Clos.Prog.types`) on their own,
on the program each stage receives. -/

/-- The nodes of a closure-IR term. -/
def Clos.Tm.size : Clos.Tm → Nat
  | .letv _ e b => 1 + e.size + b.size
  | .letpair _ _ _ b | .copy _ _ _ b | .consume _ _ b => 1 + b.size
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
      fun _ => match Frontend.parseProgram src (lib := Frontend.Sugar.libSrc) with
        | .ok p => pure p
        | .error e => throw (e.renderAt file src Frontend.Sugar.libSrc)
    let r ← ExceptT.mk <| stage "check" (fun _ => "") fun _ =>
      match Frontend.Check.checkProgram p₀ with
        | .ok r => pure r
        | .error e => throw (e.renderAt file src Frontend.Sugar.libSrc)
    let some c := r.main | throw s!"{file}: no `main`"
    let io ← ExceptT.mk <| stage "io main" (fun _ => "") fun _ =>
      match Frontend.Check.ioMainOf r.el.prog c with
        | .ok io => pure io
        | .error e => throw s!"{file}: {e}"
    let clos ← ExceptT.mk <| stage "convert" (fun (q : Clos.Prog) =>
        s!"{q.codes.size} codes, {q.size} nodes") fun _ => match io with
      | none => Clos.convert c.e
      | some _ => do
        match ← CheckedProg.runIO ⟨r.el.prog, c, io, r.el.keys⟩ with
        | some (w, xs) => Clos.convertMain (← extImpls xs) w.loops w.c.e (Frontend.Check.IORun.arg []).1
        | none => Clos.convert c.e
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

/-- A stage's output on a source file, checked (`checkedOf file src`), with `input` as standard
input and `args` as the arguments' stream (each argument followed by `0`, SPEC §34). -/
def interpStage (stage file : String) (k : Except String CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String Output := do
  match stage with
  | "source" =>
    let k ← k
    match k.io with
    | none => interpSource runFuel k.main.e
    | some m =>
      let r ← ioRunOf file k m args
      if r.loops then interpIOLoop runFuel (r.expr input) r.c.exitsOnDivError
      else interpIO runFuel (r.expr input) r.c.exitsOnDivError
  | "clos" => Clos.interp runFuel (← (← k).clos) input args
  | "flat" => Flat.interp runFuel (← (← k).flat) input args
  | "flat-counts" => Flat.interp runFuel (← (← k).flat true) input args
  | _ => throw s!"unknown stage `{stage}`"

/-- The counting build at the flat IR of a checked program, with `input` and `args` as
`interpStage`'s: its output and its memory operations (`Flat.interpMem`). -/
def flatMemCounts (k : CheckedProg) (input : List UInt8) (args : List UInt8 := []) :
    Except String (Output × Flat.MemCounts) := do
  Flat.interpMem runFuel (← k.flat true) input args

/-! ### The falsifier

`bcc interp --check fresh|tags` and `--alloc least` (`Reference/Falsify.lean`,
docs/async-capabilities.md §6.1): the source stage on the falsifier's machine. The run's output,
and its statistics. -/

/-- The falsifier's options, by name: `least`, `fresh` or `tags`. -/
def falsifyOpts : String → Except String Falsify.Opts
  | "least" => pure ⟨.least, false⟩
  | "fresh" => pure ⟨.fresh, false⟩
  | "tags" => pure ⟨.fresh, true⟩
  | m => throw s!"unknown check `{m}` (expected `fresh` or `tags`, or `--alloc least`)"

/-- The source stage of a checked program, on the falsifier's machine under `o`. -/
def interpChecked (o : Falsify.Opts) (file : String) (k : CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String (Output × String) := do
  match k.io with
  | none => Falsify.interpSource o runFuel k.main.e
  | some m =>
    let r ← ioRunOf file k m args
    if r.loops then Falsify.interpIOLoop o runFuel (r.expr input) r.c.exitsOnDivError
    else Falsify.interpIO o runFuel (r.expr input) r.c.exitsOnDivError

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

/-- A kernel program's LLVM IR. -/
def compileLLExpr (e : BoCa.Expr) (counts : Bool := false) : Except String String := do
  let (p, T) ← closTypesOfExpr e
  Native.printProg (← Flat.lower p counts T) nativeTriple counts

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

/-! ### The old backend's licences, as statements  (#746 §5.4)

The closure IR's `copy` and `consume` carry a `Clos.Licence`. The conversion reads the erased term,
so no licence is read from the typed term's rule: each is a statement about the conversion of a
checked term, stated here and not proved. -/

/-- Whether a node of `t` is at the licence `l`. -/
def Clos.Tm.atLicence (l : Clos.Licence) : Clos.Tm → Bool
  | .copy l' _ _ b | .consume l' _ b => l' == l || b.atLicence l
  | .letv _ e b => e.atLicence l || b.atLicence l
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.atLicence l || b₂.atLicence l
  | .letpair _ _ _ b | .hnd _ _ _ b | .ubind _ _ b | .catch _ b | .fin _ _ b | .catchAll b =>
    b.atLicence l
  | _ => false

/-- Whether the program has a node at the licence `l`. -/
def Clos.Prog.atLicence (p : Clos.Prog) (l : Clos.Licence) : Bool :=
  p.main.atLicence l || p.codes.any (·.body.atLicence l)

/-- **A licence's statement**: every checked program with no externs whose `main` is a closed
`CDerives` computation of `F 1`, and whose closure IR (`CheckedProg.clos`) has a node at `l`, runs
in the closure IR to `()` with no object left, as the source does (`adequacyD`): the copies and
consumes at `l` alias and leak nothing. -/
def Clos.LicenceSound (l : Clos.Licence) : Prop :=
  ∀ (k : CheckedProg) (p : Clos.Prog) (fuel : Nat) (o : Output), k.io = none →
    BoCa.Fig16.LogRel.Core.CDerives BoCa.Lifetime.LifeCtx.empty [] k.main.e
      (.comp (.ret .unit)) →
    k.clos = .ok p → p.atLicence l = true → Clos.interp fuel p [] = .ok o →
    o = Output.mk' ByteArray.empty ByteArray.empty (report .unit 0)

/-- `UNPROVED:` the licence `word`: what the conversion consumes or copies as its own word is of an
unrestricted type (`Ctx.DeadP.weaken`, `Ctx.SplitP.dup`). -/
def Clos.WordSound : Prop := Clos.LicenceSound .word
/-- `UNPROVED:` the licence `clauses`: a clause tuple or answer clause is `!`
(`clausesTy_persistent`). -/
def Clos.ClausesSound : Prop := Clos.LicenceSound .clauses
/-- `UNPROVED:` the licence `const`: an erased constant's body consumes what the constant's
type does. -/
def Clos.ConstSound : Prop := Clos.LicenceSound .const
/-- `UNPROVED:` the licence `payload`: a superseded payload holds no owned cell (`effRaise`'s
`hd`). -/
def Clos.PayloadSound : Prop := Clos.LicenceSound .payload
/-- `UNPROVED:` the licence `split`: a variable free in two sequential parts is unrestricted, or
copied by a `copy` constant (`Ctx.SplitP.dup`, `CDerives.copy`). -/
def Clos.SplitSound : Prop := Clos.LicenceSound .split
/-- `UNPROVED:` the licence `unused`: a variable that does not occur is weakened or absorbed
(`Check.UnmentionedAbsorbed`). -/
def Clos.UnusedSound : Prop := Clos.LicenceSound .unused
/-- `UNPROVED:` the licence `abort`: a level's variables at a raise or a cancel are abandoned by
`effLet`'s `hW` or weakened. -/
def Clos.AbortSound : Prop := Clos.LicenceSound .abort
/-- `UNPROVED:` the licence `kappa`: a continuation consumed at its tail resume is unrestricted or
has its consume (`kTy_unr`, `kTy_cancel_consumable_iff`). -/
def Clos.KappaSound : Prop := Clos.LicenceSound .kappa
/-- `UNPROVED:` the licence `step`: a step closure copied for the next step is `!`. -/
def Clos.StepSound : Prop := Clos.LicenceSound .step

end Backend
