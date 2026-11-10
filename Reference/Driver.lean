import Pipeline.Driver
import Reference.Source
import Reference.Falsify

/-!
# Reference — the source stage

The source stage of `bcc interp` (`Support`'s interpreter, the reference semantics that writes
and checks the goldens) on a checked program, and the falsifier's run of it. A program with
capabilities (SPEC §11) runs as `run_io` with the model of each extern (`Pipeline/Driver.lean`,
`ioRunOf`).
-/

namespace Backend

/-- The run the source stage makes of a checked program: the closed term the interpreter runs,
and how its value is read. -/
inductive SourceRun where
  /-- `main`'s erasure, run to a value. -/
  | plain (e : BoCa.Expr)
  /-- `run_io[γ] inp` (SPEC §11): a loop driven to its end when `loops`; a division's error ends
  the run with status `1` when `exits` (SPEC §39). -/
  | io (e : BoCa.Expr) (loops exits : Bool)

/-- The source stage's run of `k` with `input` as standard input and `args` as the arguments'
stream (each argument followed by `0`, SPEC §34). -/
def sourceRunOf (file : String) (k : CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String SourceRun := do
  match k.io with
  | none => pure (.plain k.main.e)
  | some m =>
    let r ← ioRunOf file k m args
    pure (.io (r.expr input) r.loops r.c.exitsOnDivError)

/-- The source stage's output on a source file, checked (`checkedOf file src`): its run
(`sourceRunOf`) in `Support`'s interpreter. -/
def interpSourceStage (file : String) (k : Except String CheckedProg) (input : List UInt8)
    (args : List UInt8 := []) : Except String Output := do
  match ← sourceRunOf file (← k) input args with
  | .plain e => interpSource runFuel e
  | .io e loops exits =>
    if loops then interpIOLoop runFuel e exits else interpIO runFuel e exits

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

end Backend
