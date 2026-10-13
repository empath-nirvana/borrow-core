import Paper
import Support
import Core

/-!
# The declarations that rest on a discreteness fact or on the stratified construction

Run with `lake env lean experiments/DenseCarrier/scripts/Deps.lean`.

For each declaration of `Paper.*`, `Support.*` and `Core.*`, whether its type or value uses,
directly or through other declarations, one of the **discreteness facts** `Life.le_of_down_lt`
and `Life.not_lt_of_down_lt` (no lifetime strictly between `↓a` and `a`), and whether it uses the
**stratified construction** `BoCa.Fig16.Cell` (the well-founded recursion on `ℕ`). Prints the
counts, and the declarations of the first kind by module.
-/

open Lean Meta

namespace DenseDeps

/-- The constants a declaration uses, in its type and its value. -/
def usedBy (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)

/-- The declarations that use one of `targets`, directly or through other declarations: marked
pass by pass over the environment until a pass marks nothing new. -/
def closure (env : Environment) (targets : List Name) : Std.HashSet Name := Id.run do
  let decls := env.constants.map₁.toList
  let mut marked : Std.HashSet Name := targets.foldl (·.insert ·) {}
  for _ in [0:decls.length] do
    let mut changed := false
    for (n, ci) in decls do
      if marked.contains n then continue
      if (usedBy ci).any marked.contains then
        marked := marked.insert n
        changed := true
    if !changed then break
  return marked

def inLib (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if [`Paper, `Support, `Core].any (·.isPrefixOf m) then some m else none

end DenseDeps

set_option maxHeartbeats 0 in
open DenseDeps in
#eval show MetaM Unit from do
  let env ← getEnv
  let disc := closure env [`BoCa.Fig16.Life.le_of_down_lt, `BoCa.Fig16.Life.not_lt_of_down_lt]
  let strat := closure env [`BoCa.Fig16.Cell]
  let mut total := 0
  let mut nDisc := 0
  let mut nStrat := 0
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternal then continue
    let some m := inLib env n | continue
    total := total + 1
    if disc.contains n then
      nDisc := nDisc + 1
      out := out.push s!"{m} | {n}"
    if strat.contains n then nStrat := nStrat + 1
  IO.println s!"declarations: {total}"
  IO.println s!"resting on a discreteness fact: {nDisc}"
  IO.println s!"resting on the stratified construction: {nStrat}"
  for l in out.qsort (· < ·) do
    IO.println l
