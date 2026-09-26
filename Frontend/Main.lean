import Frontend.Parser
import Frontend.Print
/-!
# Frontend — `bcc`

    lake exe bcc parse <file>   parse, and check that printing and re-parsing gives the same AST
    lake exe bcc print <file>   parse and print in the canonical ASCII spelling

Exit code 0 on success, 1 on a syntax error or a round-trip mismatch, 2 on bad usage.
-/

open Frontend

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
  | [cmd, file] =>
    if cmd != "parse" && cmd != "print" then
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
      match roundTrip p with
      | .error msg =>
        IO.eprintln s!"{file}: {msg}"
        return 1
      | .ok () =>
        IO.println s!"{file}: ok, {p.decls.length} declarations"
        return 0
  | _ =>
    IO.eprintln "usage: bcc (parse | print) <file>"
    return 2
