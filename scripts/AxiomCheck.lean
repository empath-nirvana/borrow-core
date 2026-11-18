import GateCensus.View
import GateCensus.Result

/-!
# The theorems `SPEC.md` names, with their axioms  (`gate-census axiom-report`)

The names are data: every `*.names` file of a directory (`scripts/axioms/` for the library,
`research/tree/axioms/` for the research archive), read in file-name order. A line is a fully
qualified declaration name, a `--` comment, or blank. For each name this prints what
`#print axioms` prints, and it fails on a name that does not resolve and on any axiom outside
`propext`, `Classical.choice` and `Quot.sound`. A new list is a new file
(`scripts/axioms/README.md`); this file does not change.
-/

open Lean Elab Command

namespace GateCensus.AxiomReport

/-- The modules the library's report reads. -/
def imports : Array Name :=
  #[`Paper, `Support, `Examples, `Core, `Frontend.Check.Externs, `Frontend.Check.Program,
    `Frontend.Check.Handled, `Frontend.Check.TFacts, `Frontend.Check.Derived, `Backend2.Lint,
    `Backend2.Interp, `Lean]

/-- The modules the research archive's report reads. -/
def researchImports : Array Name := #[`ResearchTree, `Lean]

/-- The report, as messages logged in `CoreM`. -/
def report (view : View) (dir : System.FilePath) : CoreM Unit := do
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
          for c in ← realizeGlobalConstWithInfos id do
            unless view.has (← getEnv) c do
              logError m!"{at_}: unknown constant '{c}': its module is not among the report's imports"
              continue
            let axioms ← collectAxioms c
            if axioms.isEmpty then
              logInfo m!"'{c}' does not depend on any axioms"
            else
              logInfo m!"'{c}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
            for a in axioms do
              unless allowed.contains a do logError m!"{at_}: '{c}' depends on the axiom '{a}'"
        catch e => logError m!"{at_}: {e.toMessageData}"
      | _ => logError m!"{at_}: not a declaration name: {line}"

/-- An information message prints as its text, an error as `error: ` and its text. -/
def render (msgs : List Message) : IO (Array String × Bool) := do
  let mut out := #[]
  let mut bad := false
  for m in msgs do
    let s ← m.data.toString
    match m.severity with
    | .error => out := out.push s!"error: {s}"; bad := true
    | .warning => out := out.push s!"warning: {s}"
    | .information => out := out.push s
  return (out, bad)

def run (env : Environment) (view : View) (dir : System.FilePath) : IO Result := do
  let ctx : Core.Context := {
    fileName := "<gate-census axiom-report>", fileMap := default,
    openDecls := [.simple `Lean [], .simple `Lean.Elab [], .simple `Lean.Elab.Command []] }
  let (_, st) ← (report view dir).toIO ctx { env }
  let (lines, bad) ← render st.messages.toList
  return { lines, code := if bad then 1 else 0 }

end GateCensus.AxiomReport
