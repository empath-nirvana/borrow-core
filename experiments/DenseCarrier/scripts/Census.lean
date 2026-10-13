import Paper
import Support
import Core

/-!
# The census of `ℕ`-specific uses of `Life = ℕᵒᵈ`

Run with `lake env lean experiments/DenseCarrier/scripts/Census.lean`.

`Life` is `ℕᵒᵈ`, which is `ℕ` up to unfolding `OrderDual`. A declaration uses a fact about `ℕ`
at `Life` exactly where its elaborated term passes a `Life` where an `ℕ` is expected, or an `ℕ`
where a `Life` is expected: the two types are definitionally equal and syntactically different.
This script walks the value and the type of every declaration of the modules `Paper.*`,
`Support.*` and `Core.*`, and at every application compares each argument's type with the binder
type it fills, after reducible unfolding (`Life` to `OrderDual ℕ`). It also records the constants
that name the carrier's construction: `OrderDual.ofDual`/`OrderDual.toDual` at `ℕ`, `Life.down`,
`WellFounded.fix`/`fix_eq` and `Nat.lt_wfRel`.

Each finding is printed as one line

    <module> | <declaration> | <line> | <kind> | <head>

where `<kind>` is `L→N` (a `Life` in an `ℕ` slot), `N→L` (an `ℕ` in a `Life` slot) or `const`,
and `<head>` is the applied constant. Declarations whose walk exceeds the heartbeat budget are
printed with kind `timeout`.
-/

open Lean Meta

namespace DenseCensus

/-- `ℕᵒᵈ` after reducible unfolding. -/
def isLifeTy (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isAppOfArity ``OrderDual 1 && (e.appArg!.isConstOf ``Nat)

/-- `ℕ` after reducible unfolding. -/
def isNatTy (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isConstOf ``Nat

/-- The constants whose mere use names the carrier's construction. -/
def carrierConsts : List Name :=
  [``WellFounded.fix, ``WellFounded.fix_eq, ``Nat.lt_wfRel, `BoCa.Fig16.Life.down]

structure Finding where
  kind : String
  head : Name
  deriving BEq, Hashable

abbrev M := StateRefT (Std.HashSet Finding) MetaM

def headName (f : Expr) : Name :=
  match f.getAppFn with
  | .const n _ => n
  | .fvar _ => `«fvar»
  | .lam .. => `«lambda»
  | _ => `«other»

/-- Check one application node. -/
def checkApp (e : Expr) : M Unit := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let hd := headName f
  if let .const n _ := f then
    if carrierConsts.contains n then
      modify (·.insert ⟨"const", n⟩)
    if n == ``OrderDual.ofDual || n == ``OrderDual.toDual then
      if h : 0 < args.size then
        if args[0].isConstOf ``Nat then
          modify (·.insert ⟨"const", n⟩)
  let mut fType ← try inferType f catch _ => return
  for a in args do
    fType ← whnf fType
    match fType with
    | .forallE _ d b _ =>
        let aType ← try inferType a catch _ => pure d
        if (← isNatTy d) && (← isLifeTy aType) then
          modify (·.insert ⟨"L→N", hd⟩)
        else if (← isLifeTy d) && (← isNatTy aType) then
          modify (·.insert ⟨"N→L", hd⟩)
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

end DenseCensus

set_option maxHeartbeats 0 in
open DenseCensus in
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
    let run : M Unit := do
      visit ci.type
      if let some v := ci.value? (allowOpaque := true) then visit v
    let res ← tryCatchRuntimeEx
        (do
          let (_, s) ← withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := 400000000 })
              (run.run {})
          pure (some s))
        (fun _ => pure none)
    match res with
    | none => out := out.push s!"{m} | {n} | {line} | timeout | -"
    | some s =>
        for f in s.toList do
          out := out.push s!"{m} | {n} | {line} | {f.kind} | {f.head}"
  IO.println s!"declarations scanned: {count}"
  for l in out.qsort (· < ·) do
    IO.println l
