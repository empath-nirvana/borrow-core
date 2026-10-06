import Targets.Defs.World

/-!
# Targets — the step-index audit, and the pin of Core's relation (DESIGN §4.4, §6 P14)

**The audit (§4.4).**  W's relation is to be defined by recursion on types and stratification by
lifetime, with least and greatest fixed points written in `Prop`, and no natural-number step index
(decision 7).  That is a property of a definition, so the audit reads definitions: `closure` walks
the constants a world's fields use, transitively (`Expr.getUsedConstants`), within `Paper`,
`Support`, `Core` and `Targets`, and `stepAudit` reports every definition in that closure whose
value uses a shape a step index takes: `Nat.rec`/`Nat.brecOn` (structural recursion on a natural
number), `Nat.iterate`, `Nat.repeat`, `Nat.fold`, `Fin.induction`, `WellFounded.fix`.  The report
is pinned: the build fails if it changes.  Modelled on Restrat's audit of lifetime arithmetic
(`experiments/Restrat/Restrat/Audit.lean`).

It runs on `coreW` now, which checks the audit on a relation known to be step-free.  Every entry
of `coreW`'s report is recursion on data or on a lifetime, none on a count of machine steps:

* `BoCa.Fig16.Cell`: `WellFounded.fix` on the lifetime index (`invImage OrderDual.ofDual`), the
  stratification by lifetime that decision 7 keeps ([CONF] 415:20).
* `BoCa.Fig16.BoLo.sepRange` and its auxiliary `sepRange._f`: `⋆_{i<n} P(ℓ+i)`, recursion on an
  array's length, the separating conjunction over its cells.
* `BoCa.tabFill`, `BoCa.dropFill` and their auxiliaries: the machine's array steps `tab` and
  `drop`, recursion on the array's length.

When `W` is built, `audit_W` is the same `run_meta` at `W`, with its report pinned and justified
entry by entry.

**The pin (§6 P14).**  `ConservativeWB` and `Conservative` read `vCE none`, Core's relation as this
branch imports it.  `pinHash` hashes a definition together with every constant of ours it uses
(statements, and values of definitions); the `run_meta` below compares the hashes of `vCE`, `cC`,
`wpTS`, `wpG`, `ewpTS`, `opTable` and `contShare` with the recorded ones and fails the build if any
changes.  A redefinition of Core's relation then keeps today's under a new name (`vC₀`), and both
conservativity forms are restated against it.
-/

open Lean Meta Elab Command

namespace Targets.Audit

/-- The modules the audit reads: ours. -/
def ourModule (m : Name) : Bool :=
  match m.components.head? with
  | some r => r == `Paper || r == `Support || r == `Core || r == `Targets
  | none => false

def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => ourModule env.header.moduleNames[idx.toNat]!
  | none => false

/-- The constants a constant uses: its statement's, a definition's value's, and an inductive
type's constructors.  A theorem's proof is not read. -/
def usedOf (ci : ConstantInfo) : Array Name :=
  let v := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | _ => #[]
  let c := match ci with
    | .inductInfo d => d.ctors.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ v ++ c

/-- The constants of ours that `roots` use, transitively, sorted by name. -/
def closure (roots : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := roots.toList
  let mut out : Array Name := #[]
  for _ in [0:100000000] do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      unless isOurs env n do continue
      let some ci := env.find? n | continue
      out := out.push n
      todo := (usedOf ci).toList ++ todo
  return out.qsort (·.toString < ·.toString)

/-- The shapes a step index takes. -/
def stepShapes : List Name :=
  [``Nat.rec, ``Nat.recOn, ``Nat.brecOn, ``Nat.below, ``Nat.iterate, ``WellFounded.fix,
   ``WellFounded.fixF, ``Nat.strongRecOn, ``Nat.repeat, ``Nat.fold, ``Fin.induction]

/-- Every definition in the closure of `roots` whose value uses a step-index shape, with the
shapes found. -/
def stepAudit (roots : Array Name) : MetaM (Array (Name × Array Name)) := do
  let env ← getEnv
  let mut out := #[]
  for n in ← closure roots do
    if let some (.defnInfo d) := env.find? n then
      let hits := d.value.getUsedConstants.filter (stepShapes.contains ·)
      unless hits.isEmpty do out := out.push (n, hits)
  return out

/-- A hash of one constant: its name and statement, and its value when it is a definition. -/
def constHash (ci : ConstantInfo) : UInt64 :=
  let h := mixHash (hash ci.name) ci.type.hash
  match ci with
  | .defnInfo d => mixHash h d.value.hash
  | .inductInfo d => mixHash h (hash d.ctors)
  | _ => h

/-- A hash of a definition and everything of ours it uses. -/
def pinHash (root : Name) : MetaM UInt64 := do
  let env ← getEnv
  let mut h : UInt64 := 7
  for n in ← closure #[root] do
    if let some ci := env.find? n then h := mixHash h (constHash ci)
  return h

/-- `coreW`'s report, each entry justified in the module docstring. -/
def expectedCore : List String :=
  ["BoCa.Fig16.BoLo.sepRange", "BoCa.Fig16.BoLo.sepRange._f", "BoCa.Fig16.Cell",
   "BoCa.dropFill", "BoCa.dropFill._f", "BoCa.tabFill", "BoCa.tabFill._f"]

/-- Core's relation as this branch imports it. -/
def pinned : List (Name × UInt64) :=
  [(``BoCa.Fig16.LogRel.Core.vCE, 6239293437465802492),
   (``BoCa.Fig16.LogRel.Core.cC, 16948310798130247264),
   (``BoCa.Fig16.LogRel.Core.wpTS, 1143937682946941997),
   (``BoCa.Fig16.LogRel.Core.wpG, 1502089995547854245),
   (``BoCa.Fig16.LogRel.Core.ewpTS, 17047834202755263910),
   (``BoCa.Fig16.LogRel.Core.opTable, 9303654006174601968),
   (``BoCa.Fig16.LogRel.Core.contShare, 8902597917553824952)]

end Targets.Audit

open Targets.Audit in
run_meta do
  let r := (← stepAudit #[``Targets.coreW]).map (·.1.toString)
  unless r.qsort (· < ·) == expectedCore.toArray.qsort (· < ·) do
    throwError m!"the step-index audit of coreW changed: {r}"

open Targets.Audit in
run_meta do
  for (n, h) in pinned do
    let h' ← pinHash n
    unless h' == h do
      throwError m!"Core's relation changed at {n}: {h'}, pinned {h}"
