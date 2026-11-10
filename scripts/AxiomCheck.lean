import Paper
import Support
import Examples
import Core
import Frontend.Check.Externs
import Frontend.Check.Program
import Frontend.Check.Handled
import Frontend.Check.TFacts
import Frontend.Check.Derived
import Backend2.Lint
import Backend2.Interp
import Lean
/-!
The theorems `SPEC.md` names, with their axioms.

The names are data: every `scripts/axioms/*.names`, read in file-name order. A line is a fully
qualified declaration name, a `--` comment, or blank. For each name this prints what
`#print axioms` prints, and it fails on a name that does not resolve and on any axiom outside
`propext`, `Classical.choice` and `Quot.sound`. A new list is a new file
(`scripts/axioms/README.md`); this file does not change.
-/

open Lean Elab Command in
run_cmd do
  let dir := ((← getFileName : System.FilePath).parent.getD ".") / "axioms"
  let files := ((← dir.readDir).filter (·.fileName.endsWith ".names")).map (·.fileName) |>.qsort (· < ·)
  if files.isEmpty then logError m!"AxiomCheck: no `*.names` file in {dir}"
  let allowed : NameSet := NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  for file in files do
    let lines := (← IO.FS.readFile (dir / file)).splitOn "\n"
    for h : i in [0:lines.length] do
      let line := lines[i].trimAscii.toString
      if line.isEmpty || line.startsWith "--" then continue
      let at_ := s!"{file}:{i + 1}"
      match Parser.runParserCategory (← getEnv) `term line with
      | .ok id@(.ident ..) =>
        try
          for c in ← liftCoreM <| realizeGlobalConstWithInfos id do
            let axioms ← collectAxioms c
            if axioms.isEmpty then
              logInfo m!"'{c}' does not depend on any axioms"
            else
              logInfo m!"'{c}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
            for a in axioms do
              unless allowed.contains a do logError m!"{at_}: '{c}' depends on the axiom '{a}'"
        catch e => logError m!"{at_}: {e.toMessageData}"
      | _ => logError m!"{at_}: not a declaration name: {line}"
