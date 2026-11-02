import Lean
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_3_FrameAndAntiFrame.Lemmas
import Paper.S6_5_NonStandardEntailments.Lemmas
import Paper.S6_7_WeakestPreconditionRules.Lemmas
import DtorUnwind.SI.FdTypes
import DtorUnwind.SI.CanonDeep
import DtorUnwind.SI.LinDisj

/-!
# Where the elaborated proofs read `Life` as a single chain

`Life` is `ℕᵒᵈ` (row 5.9): every two lifetimes are comparable. A proof term reads that fact
only through a few doors, and `#chainScan` lists them over the transitive closure of a
declaration (through every `BoCa` declaration its type or value mentions):

* **lin** — a non-instance constant whose signature asks for `LinearOrder`, a lattice
  (`SemilatticeInf`/`SemilatticeSup`/`Lattice`/`DistribLattice`) or `Min`/`Max`, applied at
  `Life`: `le_total`, `not_lt`, `sup_lt_iff`, `⊓`, `⊔`, `inf_le_left`, …
* **nat** — a `Nat.*` or `omega` constant applied to a term that produces a `Life` (a
  projection returning `Life`, `OrderDual.ofDual`, `OrderDual.toDual`): reasoning on the
  representation `ℕ`.
* **down** — `↓α ≜ α + 1` (row 5.12), the next-shorter lifetime.
* **meetMem** — `⊓ᾱ ∈ ᾱ`: a least member of a lifetime set, used as a member.

The scan reads the elaborated terms, so it sees what tactics produced, not the source text.
Projections from a linear order to a weaker structure (`LinearOrder.toPartialOrder`, …) and
instances themselves are not reported: they carry no comparability.
-/

open Lean Meta Elab Command

namespace TreeScan

/-- A project declaration. -/
def isProject (n : Name) : Bool := (`BoCa).isPrefixOf n || (`TR).isPrefixOf n

/-- `Life`, as written or unfolded to `ℕᵒᵈ`. -/
def isLifeTy (e : Expr) : Bool :=
  e.isConstOf ``BoCa.Fig16.Life ||
    (e.isAppOfArity ``OrderDual 1 && e.appArg!.isConstOf ``Nat)

/-- Classes that carry comparability or a binary meet/join. -/
def linClasses : List Name :=
  [``LinearOrder, ``Lattice, ``SemilatticeInf, ``SemilatticeSup, ``DistribLattice, ``Min, ``Max]

/-- The signature of `c` asks for one of `linClasses`, and `c` is neither an instance nor a
projection to a weaker structure. -/
def isLinConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | none => false
  | some ci =>
    let ty := ci.type
    let res := ty.getForallBody
    let resHead := res.getAppFn
    -- instances and structure projections into classes are not reasoning
    let isInstLike := resHead.isConst && (isClass? env resHead.constName!).isSome
    if isInstLike then false
    else (ty.find? fun x => x.isConst && linClasses.contains x.constName!).isSome
where
  isClass? (env : Environment) (n : Name) : Option Name :=
    if Lean.isClass env n then some n else none

/-- A term that produces a `Life`: a constant (applied) whose result type is `Life`, or the
`OrderDual` coercions. -/
def producesLife (env : Environment) (e : Expr) : Bool :=
  let f := e.getAppFn
  if f.isConst then
    let n := f.constName!
    n == ``OrderDual.ofDual || n == ``OrderDual.toDual ||
      (match env.find? n with
       | some ci => isLifeTy ci.type.getForallBody
       | none => false)
  else false

/-- What one declaration's own term reads (not its dependencies). -/
structure Flags where
  lin : NameSet := {}
  nat : NameSet := {}
  down : Bool := false
  meetMem : Bool := false

def Flags.isEmpty (f : Flags) : Bool := f.lin.isEmpty && f.nat.isEmpty && !f.down && !f.meetMem

def flagsOf (env : Environment) (e : Expr) : Flags := Id.run do
  let mut fl : Flags := {}
  let apps := (e.foldConsts #[] fun c acc => acc.push c)
  if apps.contains ``BoCa.Fig16.Life.down then fl := { fl with down := true }
  if apps.contains ``BoCa.Fig16.LSet.meet_mem then fl := { fl with meetMem := true }
  -- application spines with a constant head
  let mut seen : Std.HashSet Expr := {}
  let mut stack : List Expr := [e]
  while !stack.isEmpty do
    let x := stack.head!
    stack := stack.tail!
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app .. =>
        let f := x.getAppFn
        let args := x.getAppArgs
        if f.isConst then
          let c := f.constName!
          if !isProject c then
            if args.any isLifeTy && isLinConst env c then
              fl := { fl with lin := fl.lin.insert c }
            if ((`Nat).isPrefixOf c || (`Lean.Omega).isPrefixOf c) &&
                args.any (producesLife env) then
              fl := { fl with nat := fl.nat.insert c }
        stack := f :: args.toList ++ stack
    | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ b => stack := b :: stack
    | .proj _ _ b => stack := b :: stack
    | _ => pure ()
  return fl

/-- Auxiliary declarations generated from an inductive; its constructors are scanned instead. -/
def isAux (n : Name) : Bool :=
  match n with
  | .str _ s => s ∈ ["rec", "recOn", "casesOn", "below", "brecOn", "noConfusion",
      "noConfusionType", "ibelow", "binductionOn", "inj", "injEq", "sizeOf_spec", "ctorIdx"]
  | _ => false

/-- The project declarations reachable from `roots`, each with its own flags. -/
def closure (env : Environment) (roots : List Name) : Array (Name × Flags) := Id.run do
  let mut out : Array (Name × Flags) := #[]
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let body : Lean.Expr := match ci.value? (allowOpaque := true) with
        | some v => mkAnd ci.type v
        | none => ci.type
      let fl := flagsOf env body
      if !fl.isEmpty && !isAux n then out := out.push (n, fl)
      let deps := body.foldConsts #[] fun c acc => acc.push c
      let deps := match ci with
        | .inductInfo ii => deps ++ ii.ctors.toArray
        | _ => deps
      for d in deps do
        if isProject d && !seen.contains d then todo := d :: todo
  return out

def render (n : Name) (fl : Flags) : String :=
  let parts : List String :=
    (if fl.lin.isEmpty then [] else ["lin " ++ toString fl.lin.toList]) ++
    (if fl.nat.isEmpty then [] else ["nat " ++ toString fl.nat.toList]) ++
    (if fl.down then ["down"] else []) ++
    (if fl.meetMem then ["meetMem"] else [])
  s!"{n}: {", ".intercalate parts}"

/-- `#chainScan r₁ r₂ …`: every declaration in the closure of the roots that reads `Life` as a
single chain, with what it reads. -/
elab "#chainScan " ids:ident* : command => do
  let env ← getEnv
  let roots ← ids.toList.mapM fun i => liftCoreM (realizeGlobalConstNoOverloadWithInfo i)
  let res := closure env roots
  let lines := res.toList.map fun (n, fl) => render n fl
  let sorted := lines.toArray.qsort (· < ·)
  logInfo m!"{sorted.size} declarations read Life as a chain:\n{"\n".intercalate sorted.toList}"

end TreeScan
