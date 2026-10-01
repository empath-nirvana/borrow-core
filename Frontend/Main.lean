import Frontend.Parser
import Frontend.Print
import Frontend.Check.Program
import Backend.Driver
/-!
# Frontend — `bcc`

    lake exe bcc parse <file>   parse, and check that printing and re-parsing gives the same AST
    lake exe bcc print <file>   parse and print in the canonical ASCII spelling
    lake exe bcc check <file>   parse and type-check: print each declaration's type, or the error
    lake exe bcc compile [--timings] <file> -o <out.wat>
                                compile a closed `main` to WebAssembly text (`Backend/`); with
                                `--timings`, write each stage's time and output size to
                                standard error
    lake exe bcc run <file>     compile, and run under `wasmtime`: `main`'s value, then the number
                                of live objects after it is dropped
    lake exe bcc interp [--stage S] <file>
                                run `main` in the interpreter of stage `S` (`Backend/`):
                                `source` (the default), `clos`, `flat`; a program that
                                declares `stdin` reads all of standard input first
    lake exe bcc desugar <file> print the program with its I/O sugar elaborated (SPEC §11)
    lake exe bcc tir <file>     print the typed IR of the elaborated program: each
                                declaration's binders with their types and classes
                                (docs/typed-elaboration.md)
    lake exe bcc erase <file>   print the erasure of the checked `main`
    lake exe bcc trusted <file> list the program's externs with their contracts, host
                                implementations and assurance levels (SPEC §11)
    lake exe bcc kernel (list | interp [--stage S] <name> | compile <name> -o <out.wat> | run <name>)
                                the kernel programs of `Backend/Kernel.lean`, which the surface
                                cannot spell (SPEC §19), at a stage, compiled, or run

Exit code 0 on success, 1 on a syntax error, a round-trip mismatch or a type error, 2 on bad
usage. A successful `check` has built a `CDerives` derivation of `main`'s erasure
(`Frontend.Check.checkProgram_sound`).
-/

open Frontend

/-- All of standard input, read in at most `fuel` chunks of 64 KiB. -/
def readAll (h : IO.FS.Stream) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw (IO.userError "standard input is too long")
  | n + 1, acc => do
    let b ← h.read 65536
    if b.isEmpty then return acc else readAll h n (acc ++ b)

/-- Write a stage's output on `file` (`Backend.interpStage`): the program's standard output and
the report, and its standard error. -/
def interp (stage file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  let input ← if Backend.readsInput file src then readAll (← IO.getStdin) (1 <<< 16) .empty
    else pure .empty
  match Backend.interpStage stage file src input.toList with
  | .ok o =>
    let out ← IO.getStdout
    out.write o.out
    out.flush
    let err ← IO.getStderr
    err.write o.err
    err.flush
    return 0
  | .error e => IO.eprintln e; return 1

/-- Print `file` with its I/O sugar elaborated. -/
def desugar (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match parseProgram src with
  | .error e => IO.eprintln s!"{file}:{e.render}"; return 1
  | .ok p => match Frontend.Elab.elaborate p with
    | .error e => IO.eprintln s!"{file}:{e.render}"; return 1
    | .ok el => IO.print el.prog.pp; return 0

/-- Print `file`'s typed IR: for each declaration with a body, its node count, the nodes whose
type is not known, and its binders with their types and classes. Exit code 1 when a node is not
typed or lowering does not give back the elaborated program. -/
def tir (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match parseProgram src with
  | .error e => IO.eprintln s!"{file}:{e.render}"; return 1
  | .ok p => match Frontend.Elab.tirReport p with
    | .error e => IO.eprintln s!"{file}:{e.render}"; return 1
    | .ok (lines, ok) =>
      for l in lines do IO.println l
      if ok then return 0
      IO.eprintln s!"{file}: the typed IR has untyped nodes, or does not lower to the program"
      return 1

/-- Print the erasure of `file`'s checked `main`. -/
def erase (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match Backend.checkedOf file src with
  | .error e => IO.eprintln e; return 1
  | .ok k => IO.println (reprStr k.main.e); return 0

/-- Print `file`'s trusted boundaries. -/
def trusted (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match Backend.trusted file src with
  | .ok s => IO.print s; return 0
  | .error e => IO.eprintln e; return 1

/-- Write `file`'s WAT to `out`. -/
def compile (file out : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match Backend.compileWat file src with
  | .ok wat => IO.FS.writeFile out wat; return 0
  | .error e => IO.eprintln e; return 1

/-- Write `file`'s WAT to `out`, writing each stage's time to standard error. -/
def compileTimed (file out : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match ← Backend.compileWatTimed file src with
  | .ok wat => IO.FS.writeFile out wat; return 0
  | .error e => IO.eprintln e; return 1

/-- Compile `file` and run it under `wasmtime` (with tail calls), with this process's standard
input, output and error. -/
def run (file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match Backend.compileWat file src with
  | .error e => IO.eprintln e; return 1
  | .ok wat =>
    let dir ← IO.FS.createTempDir
    let out := dir / "main.wat"
    IO.FS.writeFile out wat
    let child ← IO.Process.spawn
      { cmd := "wasmtime", args := #["run", "-W", "tail-call=y", out.toString],
        stdin := .inherit, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    IO.FS.removeDirAll dir
    return (if code == 0 then 0 else 1)

/-! ### Kernel programs -/

/-- A kernel program by name (`Backend.kernelPrograms`). -/
def kernelProg (name : String) : Option BoCa.Expr :=
  ((Backend.kernelPrograms ++ Backend.kernelProgramsControl).lookup name)

/-- Write a kernel program's stage output, or its error. -/
def kernelReport (r : Except String Backend.Output) : IO UInt32 := do
  match r with
  | .ok o =>
    let out ← IO.getStdout
    out.write o.out
    out.flush
    return 0
  | .error e => IO.eprintln e; return 1

/-- Write a kernel program's WAT to `out`. -/
def kernelCompile (e : BoCa.Expr) (out : String) : IO UInt32 := do
  match Backend.compileWatExpr e with
  | .ok wat => IO.FS.writeFile out wat; return 0
  | .error err => IO.eprintln err; return 1

/-- Compile a kernel program and run it under `wasmtime`. -/
def kernelRun (e : BoCa.Expr) : IO UInt32 := do
  match Backend.compileWatExpr e with
  | .error err => IO.eprintln err; return 1
  | .ok wat =>
    let dir ← IO.FS.createTempDir
    let out := dir / "main.wat"
    IO.FS.writeFile out wat
    let child ← IO.Process.spawn
      { cmd := "wasmtime", args := #["run", "-W", "tail-call=y", out.toString],
        stdin := .inherit, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    IO.FS.removeDirAll dir
    return (if code == 0 then 0 else 1)

/-- `bcc kernel …`: list, interpret at a stage, compile, or run a kernel program. -/
def kernel (args : List String) : IO UInt32 := do
  let withProg (name : String) (k : BoCa.Expr → IO UInt32) : IO UInt32 :=
    match kernelProg name with
    | some e => k e
    | none => do IO.eprintln s!"no kernel program `{name}`"; return 1
  match args with
  | ["list"] =>
    for (n, _) in Backend.kernelPrograms do IO.println n
    return 0
  | ["interp", name] => withProg name (kernelReport ∘ Backend.interpStageExpr "source")
  | ["interp", "--stage", stage, name] =>
    withProg name (kernelReport ∘ Backend.interpStageExpr stage)
  | ["compile", name, "-o", out] => withProg name (kernelCompile · out)
  | ["run", name] => withProg name kernelRun
  | _ =>
    IO.eprintln "usage: bcc kernel (list | interp [--stage S] <name> | compile <name> -o <out.wat> | run <name>)"
    return 2

/-- Parse `src`, print it, parse the output, and compare the two ASTs up to spans. -/
def roundTrip (p : Program) : Except String Unit := do
  let out := p.pp
  match parseProgram out with
  | .error e => throw s!"the printed program does not parse: {e.render}\n{out}"
  | .ok q =>
    if q.strip == p.strip then pure ()
    else throw s!"printing and re-parsing changed the program:\n{out}"

def main (argv : List String) : IO UInt32 := do
  match argv with
  | "kernel" :: args => kernel args
  | ["compile", file, "-o", out] => compile file out
  | ["compile", "--timings", file, "-o", out] => compileTimed file out
  | ["run", file] => run file
  | ["interp", file] => interp "source" file
  | ["interp", "--stage", stage, file] => interp stage file
  | ["trusted", file] => trusted file
  | ["desugar", file] => desugar file
  | ["tir", file] => tir file
  | ["erase", file] => erase file
  | [cmd, file] =>
    if cmd != "parse" && cmd != "print" && cmd != "check" then
      IO.eprintln s!"unknown command `{cmd}`"; return 2
    let src ← IO.FS.readFile file
    match parseProgram src with
    | .error e =>
      IO.eprintln s!"{file}:{e.render}"
      return 1
    | .ok p =>
      if cmd == "print" then
        IO.print p.pp
        return 0
      if cmd == "check" then
        match Check.checkProgram p with
        | .error e =>
          IO.eprintln s!"{file}:{e.render}"
          return 1
        | .ok r =>
          for l in r.lines do IO.println l
          return 0
      match roundTrip p with
      | .error msg =>
        IO.eprintln s!"{file}: {msg}"
        return 1
      | .ok () =>
        IO.println s!"{file}: ok, {p.decls.length} declarations"
        return 0
  | _ =>
    IO.eprintln "usage: bcc (parse | print | check | run | trusted | desugar | tir | erase | interp [--stage S]) <file>\n       bcc compile <file> -o <out.wat>"
    return 2
