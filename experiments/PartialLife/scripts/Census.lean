import Paper
import Support
import Core

/-!
# The census of what the library uses of the lifetime order

Run with `lake env lean experiments/PartialLife/scripts/Census.lean > census.txt`, then
`python3 experiments/PartialLife/scripts/classify.py census.txt`.

`Life` is `ℕᵒᵈ`, a chain. A declaration uses more of it than a partial order gives exactly where
its elaborated term applies a constant that asks for more than a partial order at `Life` (an
instance argument of class `LinearOrder`, `SemilatticeInf`, `Max`, …, at `Life`), where it passes a
`Life` to an `ℕ` slot or an `ℕ` to a `Life` slot (a fact about `ℕ` used at `Life`; the two types are
definitionally equal), or where it names the carrier's construction. This script walks the value
and the type of every declaration of the modules `Paper.*`, `Support.*` and `Core.*` and records,
at every application node:

* `inst`: an instance argument whose class is applied to `Life` (after reducible unfolding); the
  finding records the applied constant and the class it asks for;
* `split`: a `Decidable` instance for `a ≤ b` or `a < b` at `Life` (a case split on the order);
* `iff.mp` / `iff.mpr` / `rw`: an iff lemma about a chain (`not_le`, `sup_lt_iff`, …) used in one
  direction, or rewritten with (`propext`); the inner application is then not recorded again;
* `L→N`, `N→L`: a `Life` in an `ℕ` slot or an `ℕ` in a `Life` slot, with the applied constant;
* `const`: `Life.down`, `OrderDual.ofDual`/`toDual` at `ℕ`, `WellFounded.fix`, `Nat.lt_wfRel`;
* `nat`: in a declaration that mentions the `ℕ`-valued lifetime layer of the statics (`SLife`,
  `Life.interp`, `LifeCtx.Models`, `EntailsLt`, `EntailsLe`), an `ℕ`-instance of a class beyond a
  partial order (`LinearOrder`, `Max`, `Min`, …) or a `Nat` comparability lemma;
* `omega`: a proof term built by `omega`.

Each finding is printed as one line

    <module> | <declaration> | <line> | <kind> | <head> | <class> | <part>

with `<part>` `T` (the declaration's type) or `V` (its value). Declarations whose walk exceeds the
heartbeat budget are printed with kind `timeout`.
-/

open Lean Meta

namespace PartialCensus

/-- `ℕᵒᵈ` after reducible unfolding. -/
def isLifeTy (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isAppOfArity ``OrderDual 1 && (e.appArg!.isConstOf ``Nat)

/-- `ℕ` after reducible unfolding. -/
def isNatTy (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isConstOf ``Nat

/-- The constants whose use names the carrier's construction. -/
def carrierConsts : List Name :=
  [``WellFounded.fix, ``WellFounded.fix_eq, ``Nat.lt_wfRel, `BoCa.Fig16.Life.down]

/-- Iff lemmas that hold in a chain and not in every partial order, in at least one direction. -/
def chainIffs : List Name :=
  [`not_le, `not_lt, `sup_lt_iff, `lt_inf_iff, `max_lt_iff, `lt_min_iff, `le_max_iff, `min_le_iff,
   `lt_max_iff, `min_lt_iff, `inf_lt_iff, `lt_sup_iff, `le_sup_iff, `inf_le_iff, `lt_iff_not_ge,
   `Nat.not_le, `Nat.not_lt, `Nat.max_lt, `Nat.lt_min, `Nat.le_max_iff, `Nat.lt_max_iff,
   `Nat.min_le_iff, `Nat.min_lt_iff, `Nat.lt_iff_le_not_le, `Nat.lt_iff_not_ge]

/-- The constants marking the statics' `ℕ`-valued lifetimes. -/
def natLifeMarkers : List Name :=
  [`BoCa.Lifetime.SLife.top, `BoCa.Lifetime.SLife.join, `BoCa.Lifetime.SLife.meet,
   `BoCa.Lifetime.SLife.Lt, `BoCa.Lifetime.SLife.Le, `BoCa.Lifetime.Life.interp,
   `BoCa.Lifetime.LifeCtx.Models, `BoCa.Lifetime.LifeCtx.EntailsLt,
   `BoCa.Lifetime.LifeCtx.EntailsLe, `BoCa.Lifetime.LifeCtx.Defines]

/-- Classes at `ℕ` that ask for more than a partial order. -/
def natClasses : List Name :=
  [``LinearOrder, ``Max, ``Min, ``Lattice, ``SemilatticeInf, ``SemilatticeSup, ``DistribLattice,
   `LinearOrderedAddCommMonoid, `LinearOrderedSemiring, `LinearOrderedCommSemiring,
   `LinearOrderedRing, `LinearOrderedAddCommGroup]

/-- `Nat` lemmas that compare in a chain. -/
def natChainLemmas : List Name :=
  [``Nat.le_total, ``Nat.lt_or_ge, ``Nat.lt_trichotomy, ``Nat.le_of_not_lt, ``Nat.lt_of_not_le,
   ``Nat.lt_or_gt_of_ne, ``Nat.eq_or_lt_of_le, `Nat.le_of_not_gt, `Nat.lt_of_not_ge,
   `Nat.le_of_not_le, `Nat.lt_or_le, `Nat.le_or_lt, `Nat.max_def, `Nat.min_def, `Nat.lt_max_iff,
   `Nat.le_max_iff, `Nat.max_lt, `Nat.lt_min, `Nat.not_le, `Nat.not_lt, ``Nat.decLe, ``Nat.decLt,
   ``Nat.decEq]

structure Finding where
  kind : String
  head : Name
  cls : Name
  part : String
  deriving BEq, Hashable

structure St where
  found : Std.HashSet Finding := {}
  skip : Std.HashSet UInt64 := {}
  part : String := "T"
  natLayer : Bool := false

abbrev M := StateRefT St MetaM

def headName (f : Expr) : Name :=
  match f.getAppFn with
  | .const n _ => n
  | .fvar _ => `«fvar»
  | .lam .. => `«lambda»
  | _ => `«other»

def record (kind : String) (head cls : Name) : M Unit :=
  modify fun s => { s with found := s.found.insert ⟨kind, head, cls, s.part⟩ }

/-- The class an instance binder asks for, and whether it is applied to `Life` (resp. `ℕ`). -/
def classOf (d : Expr) : MetaM (Option (Name × Bool × Bool)) := do
  let d ← whnfR (← instantiateMVars d)
  let .const C _ := d.getAppFn | return none
  let mut atLife := false
  let mut atNat := false
  for a in d.getAppArgs do
    if (← isLifeTy a) then atLife := true
    else if (← isNatTy a) then atNat := true
  return some (C, atLife, atNat)

/-- A `Decidable p` binder whose `p` is `a ≤ b` or `a < b` at `Life`. -/
def splitOf (d : Expr) : MetaM (Option Name) := do
  let d ← whnfR (← instantiateMVars d)
  unless d.isAppOfArity ``Decidable 1 do return none
  let p ← whnfR d.appArg!
  let fn := p.getAppFn
  if let .const n _ := fn then
    if (n == ``LE.le || n == ``LT.lt) && p.getAppNumArgs == 4 then
      if (← isLifeTy (p.getArg! 0)) then return some n
  return none

/-- The type argument of an application of `c` (its first explicit or implicit type argument),
when it is `Life`. -/
def appAtLife (e : Expr) : MetaM Bool := do
  for a in e.getAppArgs do
    let ty ← try inferType a catch _ => continue
    if (← isLifeTy ty) then return true
    if (← isLifeTy a) then return true
  return false

/-- Check one application node. -/
def checkApp (e : Expr) : M Unit := do
  if (← get).skip.contains e.hash then return
  let f := e.getAppFn
  let args := e.getAppArgs
  let hd := headName f
  if let .const n _ := f then
    if carrierConsts.contains n then record "const" n .anonymous
    if n == ``OrderDual.ofDual || n == ``OrderDual.toDual then
      if h : 0 < args.size then
        if args[0].isConstOf ``Nat then record "const" n .anonymous
    if n.getPrefix == `Lean.Omega || (n.toString.startsWith "Lean.Omega") then
      record "omega" `Lean.Omega .anonymous
    -- iff lemmas used in one direction, or rewritten with
    if (n == ``Iff.mp || n == ``Iff.mpr) && args.size ≥ 3 then
      let h := args[2]!
      if let .const k _ := h.getAppFn then
        if chainIffs.contains k then
          if (← appAtLife h) || (k.getPrefix == `Nat && (← get).natLayer) then
            record (if n == ``Iff.mp then "iff.mp" else "iff.mpr") k .anonymous
            modify fun s => { s with skip := s.skip.insert h.hash }
    if n == ``propext && args.size ≥ 3 then
      let h := args[2]!
      if let .const k _ := h.getAppFn then
        if chainIffs.contains k then
          if (← appAtLife h) || (k.getPrefix == `Nat && (← get).natLayer) then
            record "rw" k .anonymous
            modify fun s => { s with skip := s.skip.insert h.hash }
    if (← get).natLayer && natChainLemmas.contains n then
      record "nat" n .anonymous
  let mut fType ← try inferType f catch _ => return
  for a in args do
    fType ← whnf fType
    match fType with
    | .forallE _ d b bi =>
        if bi.isInstImplicit then
          if let some (C, atLife, atNat) ← classOf d then
            if atLife then record "inst" hd C
            else if atNat && (← get).natLayer && natClasses.contains C then
              record "nat" hd C
          if let some r ← splitOf d then record "split" hd r
        else
          let aType ← try inferType a catch _ => pure d
          if (← isNatTy d) && (← isLifeTy aType) then
            record "L→N" hd .anonymous
          else if (← isLifeTy d) && (← isNatTy aType) then
            record "N→L" hd .anonymous
        fType := b.instantiate1 a
    | _ => return

def visit (e : Expr) : M Unit := do
  let _ ← Meta.transform e (pre := fun e => do
    if e.isApp then checkApp e
    return .continue)

/-- The user-facing declaration an auxiliary one (`_proof_n`, `match_n`, …) belongs to. -/
def rootName : Name → Name
  | .anonymous => .anonymous
  | n@(.str p _) => if n.isInternal then rootName p else n
  | n@(.num p _) => if n.isInternal then rootName p else n

def interesting (mods : Array Name) (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  if mods.any (fun p => p.isPrefixOf m) then some m else none

def mentionsNatLayer (ci : ConstantInfo) : Bool :=
  let used := ci.type.getUsedConstants ++
    (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)
  used.any natLifeMarkers.contains

end PartialCensus

set_option maxHeartbeats 0 in
open PartialCensus in
#eval show MetaM Unit from do
  let env ← getEnv
  let prefixes : Array Name := #[`Paper, `Support, `Core]
  let mut out : Array String := #[]
  let mut count := 0
  for (n₀, ci) in env.constants.map₁.toList do
    let some m := interesting prefixes env n₀ | continue
    let n := rootName n₀
    if n.isAnonymous then continue
    count := count + 1
    let line ← do
      match ← findDeclarationRanges? n with
      | some r => pure r.range.pos.line
      | none => pure 0
    let nl := mentionsNatLayer ci
    let run : M Unit := do
      modify fun s => { s with part := "T", natLayer := nl }
      visit ci.type
      if let some v := ci.value? (allowOpaque := true) then
        modify fun s => { s with part := "V" }
        visit v
    let res ← tryCatchRuntimeEx
        (do
          let (_, s) ← withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := 400000000 })
              (run.run {})
          pure (some s))
        (fun _ => pure none)
    match res with
    | none => out := out.push s!"{m} | {n} | {line} | timeout | - | - | -"
    | some s =>
        for f in s.found.toList do
          out := out.push s!"{m} | {n} | {line} | {f.kind} | {f.head} | {f.cls} | {f.part}"
  IO.println s!"declarations scanned: {count}"
  for l in out.qsort (· < ·) do
    IO.println l
