import Frontend.Parser
import Frontend.Print
import Frontend.Check.Program
import Backend.Driver
/-!
# Frontend — `bcc`

    lake exe bcc parse <file>   parse, and check that printing and re-parsing gives the same AST
    lake exe bcc print <file>   parse and print in the canonical ASCII spelling
    lake exe bcc check <file>   parse and type-check: print each declaration's type, or the error
    lake exe bcc interp [--stage S] <file>
                                run a closed `main` in the interpreter of stage `S` (`Backend/`):
                                `source` (the default), `clos`

Exit code 0 on success, 1 on a syntax error, a round-trip mismatch or a type error, 2 on bad
usage. A successful `check` has built a `CDerives` derivation of `main`'s erasure
(`Frontend.Check.checkProgram_sound`).
-/

open Frontend

/-- Print a stage's report on `file` (`Backend.interpStage`). -/
def interp (stage file : String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  match Backend.interpStage stage file src with
  | .ok out => IO.print out; return 0
  | .error e => IO.eprintln e; return 1

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
  | ["interp", file] => interp "source" file
  | ["interp", "--stage", stage, file] => interp stage file
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
    IO.eprintln "usage: bcc (parse | print | check | interp [--stage S]) <file>"
    return 2
