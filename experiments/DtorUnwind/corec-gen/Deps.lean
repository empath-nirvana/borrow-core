import Core.Fundamental
/-!
The declarations of the library that read the world relation, for `gen.py`.

Seeds: the definitions whose type or body mentions `Core.TW` (`wpTS`, `wpTSAngelic`, `wpG`,
`RebChooseTW`, …), and the inductive types with a constructor whose type mentions it (`Cfg`). A declaration
is *dependent* when its type or value (proofs included), or for an inductive type its
constructors' types, reach a seed. Writes, under `.lake/corec-gen/`:

* `deps.txt`: every dependent declaration, `module startLine endLine name`;
* `all.txt`: every library declaration with a source range;
* `iface.txt`: the declarations that are not dependent but mention `TW` (the world's interface).

The library's leaf modules cannot all be imported together, so `deps.py` runs this file once per
leaf (with this import replaced) and merges the outputs; the environment variable `COREC_TAG`
names the run's output files.
-/
open Lean Meta

def twName : Name := `BoCa.Fig16.LogRel.Core.TW

def coreMod? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if (`Core).isPrefixOf m then some m else none

/-- The constants a declaration reads: its type and value, and an inductive type's constructors'
types. -/
def usedOf (env : Environment) (ci : ConstantInfo) : Array Name :=
  let ctors := match ci with
    | .inductInfo i => i.ctors.toArray.flatMap fun c =>
        (env.find? c).map (·.type.getUsedConstants) |>.getD #[]
    | _ => #[]
  ci.type.getUsedConstants ++ ctors ++
    ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])

#eval show CoreM Unit from do
  let env ← getEnv
  let dir : System.FilePath := ".lake/corec-gen"
  let tag := (← IO.getEnv "COREC_TAG").getD "Fundamental"
  IO.FS.createDirAll dir
  let mut consts : Array (Name × ConstantInfo × Name) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let some m := coreMod? env n then consts := consts.push (n, ci, m)
  let mut dep : Std.HashSet Name := {}
  for (n, ci, _) in consts do
    if twName.isPrefixOf n then continue
    match ci with
    | .defnInfo d =>
      if d.value.getUsedConstants.contains twName || d.type.getUsedConstants.contains twName then
        dep := dep.insert n
    | .inductInfo _ =>
      if (usedOf env ci).contains twName then dep := dep.insert n
    | _ => pure ()
  let mut changed := true
  while changed do
    changed := false
    for (n, ci, _) in consts do
      if dep.contains n then continue
      if (usedOf env ci).any dep.contains then
        dep := dep.insert n; changed := true
  let mut depOut : Array String := #[]
  let mut allOut : Array String := #[]
  let mut ifOut : Array String := #[]
  for (n, ci, m) in consts do
    let r? ← findDeclarationRanges? n
    let rng := match r? with
      | some r => s!"{r.range.pos.line} {r.range.endPos.line}"
      | none => "-1 -1"
    if r?.isSome then allOut := allOut.push s!"{m} {rng} {n}"
    if dep.contains n then depOut := depOut.push s!"{m} {rng} {n}"
    else if (usedOf env ci).any (fun c => twName.isPrefixOf c) then ifOut := ifOut.push s!"{m} {n}"
  IO.FS.writeFile (dir / s!"deps-{tag}.txt") (String.intercalate "\n" depOut.toList)
  IO.FS.writeFile (dir / s!"all-{tag}.txt") (String.intercalate "\n" allOut.toList)
  IO.FS.writeFile (dir / s!"iface-{tag}.txt") (String.intercalate "\n" ifOut.toList)
