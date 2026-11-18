import GateCensus.View
import GateCensus.Result

/-!
# Every declaration's axioms  (`gate-census axioms`, hygiene)

`#print axioms` for every declaration of the libraries `imports` lists, at once, and of the
declarations of no module (those the negative test of `scripts/check-hygiene.sh` elaborates into
the environment): for each, the axioms its type and value reach, transitively. Fails unless every
one is among `propext`, `Classical.choice` and `Quot.sound`.

One traversal serves every declaration. A forward walk from all of them, sharing one visited set,
records each reached constant's users (the reverse edges) and the axioms it meets. A declaration
reaches an axiom exactly when the axiom reaches it backwards along those edges, so a backward
walk from each axiom outside the three finds every declaration that depends on it: the same
answer as a separate `#print axioms` per declaration, in time linear in the graph.
-/

open Lean

namespace GateCensus.Axioms

/-- The libraries whose declarations are checked: the census imports each, and walks every
module under each. -/
def imports : Array Name :=
  #[`Paper, `Support, `Examples, `Core, `Frontend, `Target, `Pipeline, `Reference, `Backend, `Backend2]

/-- The constants a declaration's type and value mention. -/
def uses (ci : ConstantInfo) : Array Name :=
  let v := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | .thmInfo t => t.value.getUsedConstants
    | .opaqueInfo o => o.value.getUsedConstants
    | _ => #[]
  ci.type.getUsedConstants ++ v

def run (env : Environment) (view : View) : Result := Id.run do
  let ok : NameSet := NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  -- The project's declarations, module by module (a module may list a name twice).
  let mut decls : Array Name := #[]
  let mut listed : NameSet := {}
  for h : i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    unless view.hasModule i do continue
    unless imports.any (·.isPrefixOf mod) do continue
    for n in env.header.moduleData[i]!.constNames do
      unless listed.contains n do
        listed := listed.insert n
        decls := decls.push n
  -- The declarations of no module (the negative test's, elaborated into the environment), by name.
  let extra := env.constants.foldStage2 (fun acc n _ => acc.push n) (#[] : Array Name)
  for n in extra.qsort Name.lt do
    unless listed.contains n do
      listed := listed.insert n
      decls := decls.push n
  -- Forward: everything the declarations reach, with each constant's users and the axioms met.
  let mut seen : NameSet := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut axs : Array Name := #[]
  let mut stack : Array Name := decls
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then
      unless ok.contains n do axs := axs.push n
    for c in uses ci do
      users := users.alter c fun us => some ((us.getD #[]).push n)
      unless seen.contains c do stack := stack.push c
  -- Backward: from each axiom outside the three, every constant that reaches it.
  let mut reachers : Std.HashMap Name (Array Name) := {}
  for a in axs do
    let mut back : NameSet := {}
    let mut work : Array Name := #[a]
    while h : work.size > 0 do
      let n := work[work.size - 1]
      work := work.pop
      if back.contains n then continue
      back := back.insert n
      reachers := reachers.alter n fun as => some ((as.getD #[]).push a)
      for u in users.getD n #[] do
        unless back.contains u do work := work.push u
  let mut out : Array String := #[]
  let mut bad := 0
  for n in decls do
    for a in reachers.getD n #[] do
      out := out.push s!"{n} depends on axiom {a}"
      bad := bad + 1
  out := out.push s!"{decls.size} declarations checked; {bad} depend on an axiom outside [propext, Classical.choice, Quot.sound]."
  return { lines := out, code := if bad == 0 then 0 else 1 }

end GateCensus.Axioms
