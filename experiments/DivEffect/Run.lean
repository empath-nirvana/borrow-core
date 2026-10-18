import DivEffect.Plain
import Core.DelayPrograms
import Backend

/-!
# DivEffect — running the programs  (§4.1, unknowns 2 and 3)

`lake build DivEffect && lake env lean --run experiments/DivEffect/Run.lean` runs:

* `Residual.lean`'s `prog` (`div_fuel 3`) at the source, closure and flat stages and as
  WebAssembly under `wasmtime`.  Each prints the count `3`, `inr (inr (inr (inl ())))`, and
  `live 0`.
* The same loop as today's machine, `unfold` of the same step driven by `driveE n`
  (`Core/DelayPrograms.lean`), against `div_fuel n` of `tick; iterate`, at `n = 0, …, 6`, at the
  source stage: the same answer at each `n`.
* `div_fuel 0 Ω` (`Plain.lean`), which runs out of the interpreter's fuel.
-/

open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.DivEffect

/-- The name of `Div` in the programs. -/
def divName : UInt32 := 7

/-- Today's machine for the loop: `c ← alloc 0; L ← unfold step c; r ← driveE n L; fin r`. -/
def progOld (n : ℕ) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val (natV 0)))
    (bindE (.app (.app (.val (unfoldV (CTy.loopBody .zero (.ref .unit)))) (.val cellStep)) (.var 0))
      (bindE (driveE n) (.app (.val finV) (.var 0))))

def out (stage : String) (e : Expr) : String :=
  match Backend.interpStageExpr stage e with
  | .ok o => (String.fromUTF8! o.out).replace "\n" " "
  | .error err => s!"error: {err}"

def main : IO UInt32 := do
  let e := prog divName 3
  for stage in ["source", "clos", "flat"] do
    IO.println s!"div_fuel 3, {stage}: {out stage e}"
  match Backend.compileWatExpr e with
  | .error err => IO.println s!"wasm: error {err}"; return 1
  | .ok wat =>
    let dir ← IO.FS.createTempDir
    let path := dir / "main.wat"
    IO.FS.writeFile path wat
    let r ← IO.Process.output { cmd := "wasmtime", args := Backend.wasmtimeArgs.push path.toString }
    IO.FS.removeDirAll dir
    IO.println s!"div_fuel 3, wasm: {r.stdout.replace "\n" " "}(exit {r.exitCode})"
  for n in [0, 1, 2, 3, 4, 5, 6] do
    IO.println s!"n = {n}: today {out "source" (progOld n)} | Div {out "source" (prog divName n)}"
  match Backend.interpSource 100000 (fuelE divName 0 (omE divName)) with
  | .ok o => IO.println s!"div_fuel 0 Ω: {(String.fromUTF8! o.out).replace "\n" " "}"
  | .error err => IO.println s!"div_fuel 0 Ω, 100000 steps: {err}"
  return 0
