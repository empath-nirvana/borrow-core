import Core.Chain.LendExit835N
import Core.Chain.ConfigsKW835N

/-!
# RQ1 chain tests: which definitions of the chain's typed layer compute a lifetime

Scans every definition declared in a module `Core.Chain.*` imported here for constants that
compute a lifetime rather than compare two: `Life.down`, `OrderDual.toDual/ofDual`, an algebraic
instance at `ᵒᵈ`, `Classical.choose`/`Exists.choose`, and the lattice operations `min`/`max`/`⊓`/`⊔`.
It prints the hits; it pins nothing.
-/

open Lean Meta Elab Command

namespace RQ1Chain.Audit

def inScope (m : Name) : Bool := (`Core.Chain).isPrefixOf m

def isComp (n : Name) : Bool :=
  n == ``BoCa.Fig16.Life.down || n == ``OrderDual.toDual || n == ``OrderDual.ofDual ||
  n == ``Classical.choose || n == ``Exists.choose ||
  n == ``Min.min || n == ``Max.max ||
  n == ``Lattice.inf || n == ``SemilatticeInf.inf || n == ``SemilatticeSup.sup ||
  (n.getRoot == `OrderDual &&
    ["Add", "Sub", "Mul", "One", "Zero", "OfNat", "NatCast", "Succ", "Pred"].any fun k =>
        (n.toString.splitOn k).length > 1)

def auditDefsM : MetaM (Array (Name × Name × Array Name)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless inScope m do continue
    let hits := match ci with
      | .defnInfo d => (d.value.getUsedConstants ++ d.type.getUsedConstants).filter isComp
      | .inductInfo d => d.type.getUsedConstants.filter isComp
      | _ => #[]
    unless hits.isEmpty do out := out.push (m, n, hits.toList.eraseDups.toArray)
  return out.qsort (·.2.1.toString < ·.2.1.toString)

end RQ1Chain.Audit

open RQ1Chain.Audit in
run_meta do
  let ds ← auditDefsM
  logInfo m!"{ds.size} definitions in Core.Chain.* computing a lifetime:\n{ds.toList}"
