import Paper
import Support
import Core

/-!
# What rests on the declarations that compare two lifetimes

Run with `lake env lean experiments/PartialLife/scripts/Deps.lean`.

For each declaration of the census's class (iii) (`classify.py`), the number of declarations of
`Paper.*`, `Support.*` and `Core.*` that use it, directly or through other declarations, and whether
`fundamentalC` and `adequacyC` (`Core/Fundamental.lean`) are among them; then the same for the
whole class, and for the statics' entailments.
-/

open Lean Meta

namespace PartialDeps

/-- The constants a declaration uses, in its type and its value. -/
def usedBy (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)

def inLib (env : Environment) (n : Name) : Bool := Id.run do
  let some idx := env.getModuleIdxFor? n | return false
  let m := env.header.moduleNames[idx.toNat]!
  return [`Paper, `Support, `Core].any (·.isPrefixOf m)

/-- The census's class (iii). -/
def classIII : List Name :=
  [`BoCa.Fig16.CellU.InStratum.sup, `BoCa.Fig16.ResU.InStratum.sup,
   `BoCa.Fig16.CellU.compS_assoc, `BoCa.Fig16.CellU.compR_assoc_forward,
   `BoCa.Fig16.BoLo.ptoImm_agree, `BoCa.Fig16.LSet.union,
   `BoCa.Fig16.CellU.CompS.inStratum, `BoCa.Fig16.BoLo.cellCompS_inStratum,
   `BoCa.Fig16.BoLo.cellCompR_inStratum, `BoCa.Fig16.ResU.atLife_comp_sqsupset,
   `BoCa.Fig16.LogRel.Core.frameLife_reb_like, `BoCa.Fig16.SPropS.conj_assoc]

/-- The class (iii) places whose statement is a chain fact (the others compare two lifetimes only
in their proofs, `PartialLife/Reproved.lean`). -/
def classIIIStatement : List Name :=
  [`BoCa.Fig16.CellU.InStratum.sup, `BoCa.Fig16.ResU.InStratum.sup, `BoCa.Fig16.LSet.union,
   `BoCa.Fig16.CellU.CompS.inStratum, `BoCa.Fig16.BoLo.cellCompS_inStratum,
   `BoCa.Fig16.BoLo.cellCompR_inStratum, `BoCa.Fig16.ResU.atLife_comp_sqsupset,
   `BoCa.Fig16.LogRel.Core.frameLife_reb_like]

/-- The census's class (iv), `DenseCarrier`'s class (c). -/
def classIV : List Name :=
  [`BoCa.Fig16.Life.le_of_down_lt, `BoCa.Fig16.Life.not_lt_of_down_lt]

/-- The statics' entailments, read over `ℕ`-valued lifetime substitutions (a chain). -/
def statics : List Name :=
  [`BoCa.Lifetime.LifeCtx.EntailsLt, `BoCa.Lifetime.LifeCtx.EntailsLe]

def roots : List Name :=
  [`BoCa.Fig16.LogRel.Core.fundamentalC, `BoCa.Fig16.LogRel.Core.adequacyC]

/-- Reverse edges: for each constant, the library declarations that use it. -/
def users (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    if !inLib env n then continue
    for c in usedBy ci do
      m := m.insert c ((m.getD c #[]).push n)
  return m

/-- Everything that rests on one of `ts`. -/
def reach (us : Std.HashMap Name (Array Name)) (ts : List Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := ts.foldl (·.insert ·) {}
  let mut todo : Array Name := ts.toArray
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    for u in us.getD n #[] do
      if !seen.contains u then
        seen := seen.insert u
        todo := todo.push u
  return seen

end PartialDeps

set_option maxHeartbeats 0 in
open PartialDeps in
#eval show MetaM Unit from do
  let env ← getEnv
  let us := users env
  let decls := env.constants.map₁.toList.filter fun (n, _) => !n.isInternal && inLib env n
  IO.println s!"declarations: {decls.length}"
  let report (label : String) (ts : List Name) : MetaM Unit := do
    let c := reach us ts
    let n := (decls.filter fun (n, _) => c.contains n && !ts.contains n).length
    let rs := roots.map fun r => s!"{r.getString!} {c.contains r}"
    IO.println s!"{label} | {n} | {String.intercalate ", " rs}"
  for t in classIII do
    report t.toString [t]
  report "class (iii), all" classIII
  report "class (iii), statement-level" classIIIStatement
  report "class (iv), the two discreteness facts" classIV
  for t in statics do
    report t.toString [t]
