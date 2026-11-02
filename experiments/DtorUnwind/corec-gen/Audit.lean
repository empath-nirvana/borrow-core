import DtorUnwind.CoreC.Fundamental
/-!
The copy reads nothing of the library's world relation: from every declaration in `Core.C`, every
constant it reaches (type and value, transitively) is checked against `.lake/corec-gen/deps.txt`
(the library's dependent declarations) and `Core.TW`. Prints the number of hits and the first
ones; a hit is a copied declaration that still resolves to the library's `TW`-based relation.

Run with `lake env lean experiments/DtorUnwind/corec-gen/Audit.lean` from the repository root,
once per copied leaf module (the import replaced).
-/
open Lean Meta

#eval show CoreM Unit from do
  let env ← getEnv
  let C : Name := `BoCa.Fig16.LogRel.Core.C
  let lines ← IO.FS.lines ".lake/corec-gen/deps.txt"
  let mut bad : Std.HashSet Name := {}
  for l in lines do
    match l.splitOn " " with
    | [_, _, _, n] => bad := bad.insert n.toName
    | _ => pure ()
  bad := bad.insert `BoCa.Fig16.LogRel.Core.TW
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  let mut roots := 0
  for (n, _) in env.constants.toList do
    if C.isPrefixOf n then
      stack := stack.push n; roots := roots + 1
  let mut hits : Array (Name × Name) := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    for u in used do
      if bad.contains u then hits := hits.push (n, u)
      else if !seen.contains u then stack := stack.push u
  IO.println s!"copy declarations {roots}, reachable {seen.size}, hits {hits.size}"
  for (a, b) in hits.toList.take 40 do IO.println s!"{a} -> {b}"
