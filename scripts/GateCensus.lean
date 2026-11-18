import GateCensus.View
import GateCensus.Result
import CheckAxioms
import AxiomCheck
import TypeEq
import PinSites

/-!
# `gate-census`: the gate's checks that read the Lean environment, in one compiled program

    lake env .lake/build/bin/gate-census CENSUS[+FILE]
    lake env .lake/build/bin/gate-census --out DIR CENSUS[+FILE]...

The library is not imported when this program is built: it loads the built `.olean`s when it runs,
once, the union of the imports of every census named, and runs each census in a task of its own on
that one environment, through the census's view of it (`GateCensus.View`: the modules its own
import list reaches).

| census | what it checks | read by |
|---|---|---|
| `axioms` | every declaration's axioms (`scripts/CheckAxioms.lean`) | `scripts/check-hygiene.sh` |
| `axiom-report` | the axioms of the theorems `scripts/axioms/*.names` names (`scripts/AxiomCheck.lean`) | the gate's `axiom report` |
| `research-axiom-report` | the same for `research/tree/axioms/*.names` | `scripts/check-research.sh` |
| `type-eq` | the compiler's type comparisons (`scripts/TypeEq.lean`) | `scripts/check-type-eq.sh` |
| `pins` | the insertion pins (`scripts/PinSites.lean`) | `scripts/check-pins.sh` |

`CENSUS+FILE` runs the census on the environment with `FILE`'s declarations elaborated into it
(a Lean file without `import` lines): the scripts' negative tests. Its declarations belong to no
module, as a declaration of the file `lean` runs did.

With one census and no `--out`, the census's output is printed and its status is the program's.
With `--out DIR`, each census writes `DIR/LABEL.out` and `DIR/LABEL.status` (its exit status),
`LABEL` the census's name, or the name and `-neg` for `CENSUS+FILE`; the program fails only when
a census could not run. Run from the repository's root. With `GATE_CENSUS_TIMES` set, the time of
the import and of each census is printed on stderr.
-/

open Lean

namespace GateCensus

/-- A census: its name, the modules it reads, and how it runs on an environment. -/
structure Census where
  name : String
  imports : Array Name
  run : Environment → View → IO Result

def censuses : List Census := [
  ⟨"axioms", Axioms.imports, fun env v => pure (Axioms.run env v)⟩,
  ⟨"axiom-report", AxiomReport.imports, fun env v => AxiomReport.run env v "scripts/axioms"⟩,
  ⟨"research-axiom-report", AxiomReport.researchImports,
    fun env v => AxiomReport.run env v "research/tree/axioms"⟩,
  ⟨"type-eq", TypeEq.imports, TypeEq.run⟩,
  ⟨"pins", PinSites.imports, PinSites.run⟩]

/-- One requested run: a census, and the file of declarations added to the environment, if any. -/
structure Job where
  census : Census
  file? : Option System.FilePath

def Job.label (j : Job) : String :=
  if j.file?.isSome then j.census.name ++ "-neg" else j.census.name

def parseJob (arg : String) : Except String Job := do
  let (name, file?) := match arg.splitOn "+" with
    | [n] => (n, none)
    | n :: rest => (n, some (System.FilePath.mk ("+".intercalate rest)))
    | [] => (arg, none)
  let some c := censuses.find? (·.name == name)
    | throw s!"unknown census {name} (one of {", ".intercalate (censuses.map (·.name))})"
  return ⟨c, file?⟩

/-- The declarations of no module (a negative test's) whose type or value names a constant outside
`view`, each with those constants. The negative test's file is elaborated on the environment of
every census of the run, not on its census's imports alone as when it was a file of its own; a
term that names only constants of the census's view is what elaboration on those imports gives
(an instance, notation or default from another module would appear in the term), so a test
whose term names any other constant stops the census instead. -/
def outsideView (env : Environment) (view : View) : Array String :=
  env.constants.foldStage2 (fun (acc : Array String) n ci =>
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let out := used.filter (!view.has env ·)
    if out.isEmpty then acc else acc.push s!"{n}: {out.toList}") #[]

/-- The environment with the declarations of `file` (a Lean file with no `import` lines)
elaborated into it, or the messages that stopped it. -/
def addDecls (env : Environment) (file : System.FilePath) : IO (Except String Environment) := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  let opts := Options.empty.setBool `Elab.async false
  let s ← Elab.IO.processCommands inputCtx {} (Elab.Command.mkState env {} opts)
  let msgs := s.commandState.messages
  if msgs.hasErrors then
    let texts ← msgs.toList.mapM (·.toString)
    return .error (String.join texts)
  return .ok s.commandState.env

def usage : String :=
  "usage: gate-census CENSUS[+FILE]  |  gate-census --out DIR CENSUS[+FILE]...\n" ++
  s!"censuses: {", ".intercalate (censuses.map (·.name))}"

end GateCensus

open GateCensus in
unsafe def main (args : List String) : IO UInt32 := do
  let (out?, args) := match args with
    | "--out" :: dir :: rest => (some (System.FilePath.mk dir), rest)
    | _ => (none, args)
  if args.isEmpty || (out?.isNone && args.length != 1) then
    IO.eprintln usage; return 2
  let jobs ← match args.mapM parseJob with
    | .ok js => pure js.toArray
    | .error e => IO.eprintln s!"gate-census: {e}\n{usage}"; return 2
  let labels := jobs.map (·.label)
  if labels.toList.eraseDups.length != labels.size then
    IO.eprintln "gate-census: a census is named twice"; return 2
  -- One environment: the union of the imports.
  let roots := jobs.foldl (init := #[]) fun acc j =>
    j.census.imports.foldl (init := acc) fun acc m => if acc.contains m then acc else acc.push m
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules (roots.map ({ module := · })) {} 0 (loadExts := true)
  let times := (← IO.getEnv "GATE_CENSUS_TIMES").isSome
  if times then IO.eprintln s!"gate-census: import {(← IO.monoMsNow) - t0} ms"
  -- The negative tests' environments, elaborated in turn; then every census, each in a task.
  let mut tasks : Array (Job × Task (Except IO.Error Result)) := #[]
  for j in jobs do
    let env' ← match j.file? with
      | none => pure (.ok env)
      | some f => do
        let t ← IO.monoMsNow
        let r ← addDecls env f
        if times then IO.eprintln s!"gate-census: elaborating {f} {(← IO.monoMsNow) - t} ms"
        pure r
    match env' with
    | .error msg =>
      tasks := tasks.push (j, .pure (.ok { lines := #[s!"gate-census: {j.file?.get!} failed to elaborate:", msg], code := 2 }))
    | .ok env' =>
      let view := View.ofRoots env' j.census.imports
      let out := outsideView env' view
      unless out.isEmpty do
        tasks := tasks.push (j, .pure (.ok { code := 2, lines :=
          #[s!"gate-census: {j.file?.get!} names constants outside the census's imports:"] ++ out }))
        continue
      tasks := tasks.push (j, ← IO.asTask do
        let t ← IO.monoMsNow
        let r ← j.census.run env' view
        if times then IO.eprintln s!"gate-census: {j.label} {(← IO.monoMsNow) - t} ms"
        return r)
  let mut failed := false
  for (j, t) in tasks do
    let r ← match ← IO.wait t with
      | .ok r => pure r
      | .error e => pure { lines := #[s!"gate-census {j.label}: {e}"], code := 2 }
    match out? with
    | none =>
      IO.print r.text
      return r.code
    | some dir =>
      IO.FS.writeFile (dir / s!"{j.label}.out") r.text
      IO.FS.writeFile (dir / s!"{j.label}.status") s!"{r.code}\n"
      if r.code == 2 then failed := true
  return if failed then 2 else 0
