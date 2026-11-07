import Frontend.Parser
import Frontend.Check.Program
import Frontend.Check.Externs
import Target.Native.Runtime

/-!
# Pipeline — the checked program

What every backend shares between the checker and its stages: the checked program
(`CheckedProg`, one check per command), the program a backend compiles for a program with
capabilities (`CheckedProg.runIO`), the fuel of every interpreter, the `wasmtime` and `clang`
invocations, the stage timer of `bcc compile --timings`, the model run of `run_io`, and the
program's trusted boundaries (`bcc trusted`).
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

/-- A checked program: the elaborated program the checker checked, `main` (its typed term, and
whether it is served `Fail[DivError]` by `main_div_error`, SPEC §39), and its capabilities if it
has any. Every stage below takes it, so a command checks its program once. -/
structure CheckedProg where
  prog : Frontend.Program
  main : Frontend.Check.Checked
  io : Option Frontend.Check.IOMain
  /-- The keys of the `def`s the elaboration copied (`Elaborated.keys`), which `run_io`'s check
  carries (`Frontend.Check.ioRunOf`). -/
  keys : List Frontend.DefKey

/-- Parse and check `src`; a `main` with externs must be a standard I/O program (SPEC §11). -/
def checkedOf (file src : String) : Except String CheckedProg := do
  let p₀ ← match Frontend.parseProgram src (lib := Frontend.Sugar.libSrc) with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
  let r ← match Frontend.Check.checkProgram p₀ with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
  let some c := r.main | throw s!"{file}: no `main`"
  match Frontend.Check.ioMainOf r.el.prog c with
  | .ok io => pure ⟨r.el.prog, c, io, r.el.keys⟩
  | .error e => throw s!"{file}: {e}"

/-- **The program a backend compiles, for a program with capabilities** (SPEC §11): `run_io`
checked in its compiled form (`Frontend.Check.IORun`, the term `IORun.every_run` and
`externs_every_run` are about), which returns `main`'s result and weakens the outputs, built with
no arguments in the term (the arguments are the stream `mk_args`'s host gives `args`), and its
externs in declaration order. A backend compiles `IORun.expr r []`: this term applied to its
argument `IORun.arg []`, each extern its host. `none` for a program without capabilities,
compiled as `main`. -/
def CheckedProg.runIO (k : CheckedProg) :
    Except String (Option (Frontend.Check.IORun × List Frontend.Check.ExternSpec)) := do
  let some m := k.io | return none
  let w ← Frontend.Check.ioWrapper k.prog m [] (outs := false)
  let r ← Frontend.Check.ioRunOf w k.keys
  return some (r, ← Frontend.Check.wrapperExterns w)

/-- The program reads standard input. -/
def CheckedProg.readsInput (k : CheckedProg) : Bool :=
  match k.io with
  | some m => m.caps.any (·.name == "stdin")
  | none => false

/-- The checked program, if it checks, reads standard input. -/
def readsInput (k : Except String CheckedProg) : Bool :=
  match k with
  | .ok k => k.readsInput
  | .error _ => false

/-- The target the native code is built for: the host's. -/
def nativeTriple : String := System.Platform.target

/-! ### The native build  `[spec §40]`

The host's target, and `clang` building LLVM IR beside the native runtime
(`Target/Native/Runtime.lean`). -/

/-- The flags `clang` builds a native program with. -/
def clangArgs : Array String := #["-O2", "-w", "-pthread"]

/-- A `clang` on `PATH` outside a Lean toolchain: `lake exe` and `lake env` put the toolchain's
`bin` first, and its bundled `clang` has no C library headers. -/
def clangOnPath : IO (Option String) := do
  let path := (← IO.getEnv "PATH").getD ""
  for d in path.splitOn ":" do
    if d.isEmpty || (d.splitOn "/.elan/").length > 1 then continue
    let c : System.FilePath := d / "clang"
    if ← c.pathExists then return some c.toString
  return none

/-- The C compiler the native target builds with, as a command and the arguments that come
first (`[spec §40]`): `$BC_CC` when set; else on macOS `xcrun clang`, the Xcode toolchain's
`clang` with the SDK `xcrun` finds (that `clang` run by its path has no SDK, so no C headers);
else the first `clang` on `PATH` outside a Lean toolchain (`clangOnPath`). `none` when there is
none. -/
def nativeCC : IO (Option (String × Array String)) := do
  if let some cc := ← IO.getEnv "BC_CC" then
    if !cc.isEmpty then return some (cc, #[])
  if System.Platform.isOSX then
    let r ← try IO.Process.output { cmd := "xcrun", args := #["-f", "clang"] }
      catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if r.exitCode == 0 then return some ("xcrun", #["clang"])
  return (← clangOnPath).map (·, #[])

/-- Build the LLVM IR `ll` and the runtime in `dir` with `nativeCC`: the executable's path, or
the compiler's error. -/
def buildNative (ll : String) (dir : System.FilePath) : IO (Except String System.FilePath) := do
  let some (cc, pre) ← nativeCC
    | return .error "no C compiler for the native target: set BC_CC, or install clang"
  IO.FS.writeFile (dir / "main.ll") ll
  IO.FS.writeFile (dir / "runtime.c") Native.runtimeC
  let exe := dir / "main"
  let r ← IO.Process.output
    { cmd := cc, args := pre ++ clangArgs ++
        #[(dir / "main.ll").toString, (dir / "runtime.c").toString, "-o", exe.toString] }
  if r.exitCode != 0 then return .error s!"{cc} failed ({r.exitCode}):\n{r.stderr}"
  pure (.ok exe)

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

/-! ### Timings

The stage timer of `bcc compile --timings`. -/

/-- The model run of a program with capabilities: `run_io` checked, with every extern's model
(`Frontend.Check.IORun`). -/
def ioRunOf (file : String) (k : CheckedProg) (m : Frontend.Check.IOMain)
    (args : List UInt8 := []) : Except String Frontend.Check.IORun := do
  let w ← match Frontend.Check.ioWrapper k.prog m args with
    | .ok w => pure w
    | .error e => throw s!"{file}: {e}"
  match Frontend.Check.ioRunOf w k.keys with
  | .ok r => pure r
  | .error e => throw s!"{file}: {e}"

/-- What the typing of `main` rests on (SPEC §29): nothing beyond Core's theorems, or `PinLaw` at
each relaxed rule the derivation uses. -/
def typingReport (c : Frontend.Check.Checked) : String :=
  match c.pins with
  | [] => "typing: unconditional: a CDerives derivation (fundamentalC, adequacyD)"
  | ps =>
    let ps := ps.eraseDups
    let field (r : String) : String :=
      if r == "R2" then "LoopFrame (PinLaw.loopFrame)" else "LendFrame at ref (PinLaw.lendFrame)"
    "typing: PinLaw (Core/PinLaw.lean), the hypothesis of fundamentalC_pin and adequacyD_pin: " ++
      s!"{ps.length} site{if ps.length == 1 then "" else "s"}" ++
      String.join (ps.map fun q => s!"\n  {q.rule} at {q.line}:{q.col}: {field q.rule}")

/-- The program's trusted boundaries (`bcc trusted`).  `[spec §11, §29]` -/
def trusted (file src : String) : Except String String := do
  let p ← match Frontend.parseProgram src (lib := Frontend.Sugar.libSrc) with
    | .ok p => pure p
    | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
  let r ← match Frontend.Check.checkProgram p with
    | .ok r => pure r
    | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
  let typing := (r.main.map typingReport).toList
  let xs ← match Frontend.Check.externs r.el.prog.decls.toArray with
    | .ok xs => pure xs
    | .error e => throw s!"{file}:{e.renderIn src Frontend.Sugar.libSrc}"
  -- The externs `main`'s erasure uses: a library's extern that the program never reaches is not
  -- in its trusted base (SPEC §34). The last declared is at index 0 of `main`'s context.
  let xs := match r.main with
    | some c => xs.zipIdx.filterMap fun (x, i) =>
        if BoCa.Fig16.LogRel.Core.occ (xs.length - 1 - i) c.e then some x else none
    | none => xs
  -- A program with capabilities is compiled as `run_io` (SPEC §11): the harness's makes and takes
  -- it calls are in its trusted base too.
  let harness ← match r.main with
    | some c => match Frontend.Check.ioMainOf r.el.prog c with
      | .ok (some m) => do
        let w ← Frontend.Check.ioWrapper r.el.prog m []
        let ws ← Frontend.Check.wrapperExterns w
        pure (ws.filterMap fun x => match x.role with
          | .mk _ | .take _ => some (x.name, x.ty)
          | _ => none)
      | _ => pure []
    | none => pure []
  let xs := xs ++ harness
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
