import Targets.I.World

/-!
# Targets — the step-index audit, extended, and the pin of Core's relation (RESTRUCTURE §5.2)

**Decision 7 (no step-indexing) is a property of `W`'s definition, not of its laws** (finding #6).
A step-indexed relation can meet every conjunct of done, with its index hidden in `Stk` and
decremented by `Upd` or at the `U` and `ν` clauses, so no Prop over `W` excludes it; and the
lifetime stratification the model already uses (`Life = ℕᵒᵈ`, `Cell`'s `WellFounded.fix`), which
decision 7 keeps, is itself recursion on a natural number, so a structural requirement
("well-founded recursion on lifetimes only") cannot be told apart from a counter.  So the
enforcement is a **definitional audit with negative tests, plus review of `W`'s definition**.

`closure` walks the constants a world's definition uses, transitively, within `Paper`, `Support`,
`Core` and `Targets`.  **Count-like** types are `ℕ`, `Fin n`, `UInt8`–`UInt64`, `Life` and `ℕᵒᵈ`,
read after unfolding reducible definitions and instantiating `Stk` (so `Idx Stk` at `Stk := ℕ` is
count-like), and through `×`, `Σ`, `List` and `Option`; a type that reaches `ℕ` only through `Loc`
(locations, heaps, resources) is reported in a bucket of its own.  Five reports:

1. **recursor and case shapes** in the values of definitions (`Nat.rec`, `Nat.casesOn`,
   `WellFounded.fix`, …; a `match` on a count compiles to a matcher that uses `Nat.casesOn`);
2. **indexed predicate families**: inductive `Prop`s with a count-like index (and, apart, those
   indexed through `Loc` only);
3. **impredicative indexed fixed points**: definitions binding `∀ P : … → Prop` with a count-like
   argument;
4. **bounded iteration**: `List.range`, `List.replicate`, `Nat.fold`, `Nat.iterate`, …;
5. **arithmetic on an index**: (a) a constructor of a reported family whose result index uses
   `Nat.succ` or `+`; (b) in the world's own modules, `Nat.sub`, `Nat.pred`, `Nat.succ`, `-` or `+`
   at a count-like type.

Each report is pinned (`expectedCore`), and the build fails when it changes.  Every entry of
`coreW`'s report is recursion on data, on a lifetime, or on an allocation count, never on a count of
machine steps; the justification of each is in `Targets/Status.lean`'s audit table.

**Negative tests**: nine toy step-indexed worlds the audit must reject (`stepW₁`–`stepW₉`): `val`
by `Nat.rec` on an index; a family `SafeN : ℕ → Prop` with `Stk := ℕ`; the relation as a
`List.range` fold; an impredicative `ℕ`-indexed fixed point, with its predicate the first binder of
its `∀` telescope (`stepW₄`) and the second (`stepW₉`); `Stk := Life` counted down by `Upd`;
`Stk := ℕ` counted down by `Upd` with `Nat.sub`; `Upd` decrementing by a `match`, true at `0`; a
family indexed by `Idx Stk` at `Stk := ℕ` with an `n + 1` constructor.  When `W` is built,
`audit_W` is the same `run_meta` at `W`, its report pinned and justified entry by entry.

**The residual, stated.**  The audit is syntactic: it reports the forms step-indexing takes in
Lean, and a counter in a type it does not list would pass it.  `W` is ours and built in good faith,
so the audit is a check against accidental step-indexing, and decision 7's enforcement also includes
a review of `W`'s definition before done is claimed.

**The pin.**  `ConservativeWB`, `Conservative` and `EmbedsNil` read `vCE none`, Core's relation as
this branch imports it.  `pinHash` hashes a definition with every constant of ours it uses; the
`run_meta` compares the hashes of `vCE`, `cC`, `wpTS`, `wpG`, `ewpTS`, `opTable` and `contShare`
with the recorded ones.
-/

open Lean Meta Elab Command

namespace Targets.Audit

/-- The modules the audit reads: ours. -/
def ourModule (m : Name) : Bool :=
  match m.components.head? with
  | some r => r == `Paper || r == `Support || r == `Core || r == `Targets
  | none => false

/-- The module a constant is declared in (the module being compiled, for its own constants). -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => some env.header.moduleNames[idx.toNat]!
  | none => if env.contains n then some env.mainModule else none

def isOurs (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => ourModule m
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

/-! ### Report 1: recursor and case shapes -/

/-- The shapes a step index takes in a definition's value. -/
def stepShapes : List Name :=
  [``Nat.rec, ``Nat.recOn, ``Nat.brecOn, ``Nat.below, ``Nat.casesOn, ``Nat.casesAuxOn,
   ``Nat.iterate, ``WellFounded.fix, ``WellFounded.fixF, ``Nat.strongRecOn, ``Nat.repeat,
   ``Nat.fold, ``Fin.induction, ``Fin.cases, ``Fin.casesOn, ``UInt8.casesOn, ``UInt16.casesOn,
   ``UInt32.casesOn, ``UInt64.casesOn]

/-- Every definition in the closure of `roots` whose value uses a step-index shape. -/
def stepAudit (roots : Array Name) : MetaM (Array (Name × Array Name)) := do
  let env ← getEnv
  let mut out := #[]
  for n in ← closure roots do
    if let some (.defnInfo d) := env.find? n then
      let hits := d.value.getUsedConstants.filter (stepShapes.contains ·)
      unless hits.isEmpty do out := out.push (n, hits)
  return out

/-! ### Count-like types -/

/-- The heads of count-like types. -/
def countHeads : List Name := [``Nat, ``Fin, ``UInt8, ``UInt16, ``UInt32, ``UInt64]

/-- The type formers a count-like component is looked for in. -/
def throughHeads : List Name := [``Prod, ``PProd, ``Sigma, ``PSigma, ``Subtype, ``List, ``Option]

/-- `t` is count-like (`ℕ`, `Fin n`, `UIntN`, `Life`, `ℕᵒᵈ`, or one of these inside `×`, `Σ`,
`List`, `Option`), after unfolding reducible definitions; `Loc` is not (its own bucket).  `fuel`
bounds the unfolding. -/
def countLike : Nat → Expr → MetaM Bool
  | 0, _ => pure false
  | n + 1, t => do
    let t ← instantiateMVars t
    match t.getAppFn with
    | .const c _ =>
      if c == ``BoCa.Loc then return false
      if countHeads.contains c || c == ``BoCa.Fig16.Life then return true
      if c == ``OrderDual then return true
      if throughHeads.contains c then
        for a in t.getAppArgs do
          if ← countLike n a then return true
        return false
      let t' ← withReducible (whnfR t)
      if t' == t then return false
      countLike n t'
    | _ => return false

/-- `t` reaches `Loc`: it mentions `Loc`, or does after unfolding reducible definitions. -/
def reachesLoc : Nat → Expr → MetaM Bool
  | 0, _ => pure false
  | n + 1, t => do
    let t ← instantiateMVars t
    if (t.find? fun e => e.isConstOf ``BoCa.Loc).isSome then return true
    let t' ← withReducible (whnfR t)
    if t' == t then
      for a in t.getAppArgs do
        if ← reachesLoc n a then return true
      return false
    reachesLoc n t'

/-! ### Report 2: indexed predicate families -/

/-- The index types of an inductive family. -/
def indexTypes (d : InductiveVal) : MetaM (Array Expr) :=
  forallTelescopeReducing d.type fun xs _ => do
    let mut out := #[]
    for x in xs[d.numParams:] do out := out.push (← inferType x)
    return out

/-- The inductive `Prop`s of the closure with a count-like index, and apart those indexed through
`Loc` only. -/
def familyAudit (roots : Array Name) : MetaM (Array Name × Array Name) := do
  let env ← getEnv
  let mut count := #[]
  let mut viaLoc := #[]
  for n in ← closure roots do
    if let some (.inductInfo d) := env.find? n then
      let (isProp, c, l) ← forallTelescopeReducing d.type fun xs s => do
        let mut c := false
        let mut l := false
        for x in xs[d.numParams:] do
          let t ← inferType x
          if ← countLike 30 t then c := true
          else if ← reachesLoc 30 t then l := true
        return (s.isProp, c, l)
      unless isProp do continue
      if c then count := count.push n
      else if l then viaLoc := viaLoc.push n
  return (count, viaLoc)

/-! ### Report 3: impredicative indexed fixed points -/

/-- `b` is a predicate type `∀ … → Prop` with an argument of a count-like type. -/
def isCountPred (b : Expr) : MetaM Bool := do
  if !b.isForall then return false
  (forallTelescopeReducing b fun xs s => do
      if !s.isProp then return false
      for x in xs do
        if ← countLike 30 (← inferType x) then return true
      return false) <|> pure false

/-- `e` binds `∀ P : … → Prop` whose binder type has a count-like argument: every binder of every
`∀` telescope of `e`, at every depth, read in the telescope's local context.  (`forEachExpr`
visits a telescope at its head and then each binder's type, so the head alone shows only the first
binder; the telescope is opened here to see them all.)  A `λ`-bound predicate is a parameter, not
an impredicative quantifier, and is not reported. -/
def bindsCountPred (e : Expr) : MetaM Bool := do
  let hit ← IO.mkRef false
  forEachExpr e fun s => do
    unless ← hit.get do
      let tele : MetaM Unit := match s with
        | .forallE .. => forallTelescope s fun xs _ => xs.forM fun x => do
            if ← isCountPred (← inferType x) then hit.set true
        | _ => pure ()
      tele <|> pure ()
  hit.get

/-- The definitions of the closure whose value binds a count-indexed predicate. -/
def fixAudit (roots : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for n in ← closure roots do
    if let some (.defnInfo d) := env.find? n then
      if ← bindsCountPred d.value then out := out.push n
  return out

/-! ### Report 4: bounded iteration -/

/-- The bounded iterators. -/
def iterShapes : List Name :=
  [``List.range, ``List.range', ``List.replicate, ``Nat.fold, ``Nat.iterate, ``Nat.repeat,
   ``Fin.foldl]

def iterAudit (roots : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for n in ← closure roots do
    if let some (.defnInfo d) := env.find? n then
      unless (d.value.getUsedConstants.filter (iterShapes.contains ·)).isEmpty do out := out.push n
  return out

/-! ### Report 5: arithmetic on an index -/

/-- (a) The constructors of the reported families whose result index uses `Nat.succ` or `+`. -/
def succCtorAudit (fams : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for f in fams do
    if let some (.inductInfo d) := env.find? f then
      for c in d.ctors do
        if let some ci := env.find? c then
          let hit ← forallTelescopeReducing ci.type fun _ concl => do
            let idx := concl.getAppArgs[d.numParams:]
            return idx.any fun e => (e.find? fun s => s.isConstOf ``Nat.succ ||
              s.isConstOf ``HAdd.hAdd || s.isConstOf ``Nat.add).isSome
          if hit then out := out.push c
  return out

/-- The arithmetic operations that decrement or increment a count. -/
def arithHeads : List Name := [``Nat.sub, ``Nat.pred, ``Nat.succ, ``HSub.hSub, ``HAdd.hAdd]

/-- The applications of `e` headed by an arithmetic operation, at every depth. -/
def arithApps (e : Expr) : MetaM (Array Expr) := do
  let acc ← IO.mkRef (#[] : Array Expr)
  forEachExpr e fun s => match s.getAppFn with
    | .const c _ => if arithHeads.contains c then acc.modify (·.push s) else pure ()
    | _ => pure ()
  acc.get

/-- `e` uses an arithmetic operation at a count-like type. -/
def usesCountArith (e : Expr) : MetaM Bool := do
  for a in ← arithApps e do
    let fn := a.getAppFn
    if fn.isConstOf ``Nat.sub || fn.isConstOf ``Nat.pred || fn.isConstOf ``Nat.succ then return true
    match a.getAppArgs[0]? with
    | some ty => if !ty.hasLooseBVars then if ← countLike 30 ty then return true
    | none => pure ()
  return false

/-- (b) The definitions in the roots' own modules that do arithmetic at a count-like type. -/
def arithAudit (roots : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mods := roots.filterMap (moduleOf env)
  let mut out := #[]
  for n in ← closure roots do
    unless (moduleOf env n).any (mods.contains ·) do continue
    if let some (.defnInfo d) := env.find? n then
      if ← usesCountArith d.value then out := out.push n
  return out

/-- **The whole audit**: the five reports. -/
structure Report where
  shapes : Array Name
  families : Array Name
  viaLoc : Array Name
  fixes : Array Name
  iters : Array Name
  succCtors : Array Name
  arith : Array Name

def sortNames (a : Array Name) : Array String := (a.map (·.toString)).qsort (· < ·)

def audit (roots : Array Name) : MetaM Report := do
  let (fams, viaLoc) ← familyAudit roots
  return ⟨(← stepAudit roots).map (·.1), fams, viaLoc, ← fixAudit roots, ← iterAudit roots,
    ← succCtorAudit fams, ← arithAudit roots⟩

/-- The audit rejects a world: some report other than the `Loc` bucket is non-empty. -/
def Report.rejects (r : Report) : Bool :=
  !(r.shapes.isEmpty && r.families.isEmpty && r.fixes.isEmpty && r.iters.isEmpty &&
    r.succCtors.isEmpty && r.arith.isEmpty)

/-- **`coreW`'s report, pinned**: each entry is justified in `Targets/Status.lean`'s audit table. -/
def expectedCore : List (String × List String) :=
  [("shapes", ["BoCa.BoLo.capTag._sparseCasesOn_5", "BoCa.BoLo.capTag.match_1", "BoCa.BoLo.clauseAt.match_1", "BoCa.Fig16.BoLo.sepRange", "BoCa.Fig16.BoLo.sepRange._f", "BoCa.Fig16.BoLo.sepRange.match_1", "BoCa.Fig16.Cell", "BoCa.Fig16.LogRel.Core.VTy.upR.match_1", "BoCa.dropFill", "BoCa.dropFill._f", "BoCa.tabFill", "BoCa.tabFill._f", "BoCa.tabFill.match_1"]),
   ("families", ["BoCa.BoLo.AHead", "BoCa.BoLo.ARun"]),
   ("viaLoc", ["BoCa.BoLo.Head", "BoCa.Fig16.LogRel.Core.Chain", "BoCa.Fig16.LogRel.Core.GPos", "BoCa.Fig16.LogRel.Core.LinPath", "BoCa.Fig16.LogRel.Core.MutPos", "BoCa.Fig16.LogRel.Core.RefPos", "BoCa.Fig16.LogRel.Core.TW"]),
   ("fixes", ["BoCa.Fig16.LogRel.Core.Table", "BoCa.Fig16.LogRel.Core.ewpTS", "BoCa.Fig16.LogRel.Core.vCE._f"]),
   ("iters", []),
   ("succCtors", ["BoCa.BoLo.AHead.alloc", "BoCa.BoLo.AHead.tab"]),
   ("arith", [])]

/-- The report, as the pinned list. -/
def Report.toList (r : Report) : List (String × List String) :=
  [("shapes", (sortNames r.shapes).toList), ("families", (sortNames r.families).toList),
   ("viaLoc", (sortNames r.viaLoc).toList), ("fixes", (sortNames r.fixes).toList),
   ("iters", (sortNames r.iters).toList), ("succCtors", (sortNames r.succCtors).toList),
   ("arith", (sortNames r.arith).toList)]

/-! ### The pin of Core's relation -/

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

/-- Core's relation as this branch imports it. -/
def pinned : List (Name × UInt64) :=
  [(``BoCa.Fig16.LogRel.Core.vCE, 2634188461942789339),
   (``BoCa.Fig16.LogRel.Core.cC, 1577135250918925567),
   (``BoCa.Fig16.LogRel.Core.wpTS, 9102727463225695086),
   (``BoCa.Fig16.LogRel.Core.wpG, 15068369448990440630),
   (``BoCa.Fig16.LogRel.Core.ewpTS, 9716194076298458845),
   (``BoCa.Fig16.LogRel.Core.opTable, 17297278857222068005),
   (``BoCa.Fig16.LogRel.Core.contShare, 7895051437212535705)]

end Targets.Audit

/-! ### The negative tests: nine step-indexed toy worlds -/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Audit.Toy
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub)

/-- A toy world at the stack type `Stk`, from its configurations, run-end relation and relation;
the other fields trivial. -/
def toyW (Stk : Type) (nil : Stk) (Fam : WRes → List FrameRec → Idx Stk → Prop)
    (Upd : Idx Stk → Idx Stk → WRes → WRes → WRes → Prop)
    (val : Bool → VTy → Idx Stk → LSub → BoCa.Val → WProp)
    (comp : CTy → Idx Stk → LSub → BoCa.Expr → WProp) :
    SemWorld where
  Stk := Stk
  nil := nil
  Fam := Fam
  Upd := Upd
  Ext _ _ _ := True
  payStk _ s := s
  val := val
  comp := comp
  held _ := ([], [])
  Stop _ _ _ := True
  share _ _ _ _ _ _ _ := False

/-- `stepW₁`: the value relation by `Nat.rec` on the index. -/
def stepW₁ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun _ _ _ _ _ => True)
    (fun _ _ i _ _ _ => Nat.rec (motive := fun _ => Prop) False (fun _ ih => ih) i.2)
    (fun _ _ _ _ _ => True)

/-- A step-indexed safety family. -/
inductive SafeN : ℕ → Prop
  | zero : SafeN 0
  | succ {n : ℕ} : SafeN n → SafeN (n + 1)

/-- `stepW₂`: configurations through `SafeN` at `Stk := ℕ`. -/
def stepW₂ : SemWorld :=
  toyW ℕ 0 (fun _ _ i => SafeN i.2) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True)

/-- `stepW₃`: the relation as a `List.range` fold. -/
def stepW₃ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun _ _ _ _ _ => True)
    (fun _ _ i _ _ _ => (List.range i.2).foldl (fun acc _ => acc) True) (fun _ _ _ _ _ => True)

/-- `stepW₄`: an impredicative `ℕ`-indexed least fixed point. -/
def stepW₄ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    (fun _ i _ _ _ => ∀ P : ℕ → Prop, (∀ n, P n → P (n + 1)) → P i.2)

/-- `stepW₉`: the same fixed point with the predicate the second binder of its `∀` telescope. -/
def stepW₉ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    (fun _ i _ _ _ => ∀ (k : ℕ) (P : ℕ → Prop), P k → (∀ n, P n → P (n + 1)) → P i.2)

/-- `stepW₅`: `Stk := Life`, `Upd` counting it down. -/
def stepW₅ : SemWorld :=
  toyW Life (OrderDual.toDual 0) (fun _ _ _ => True)
    (fun i i' _ _ _ => OrderDual.ofDual i'.2 + 1 = OrderDual.ofDual i.2)
    (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ => True)

/-- `stepW₆`: `Stk := ℕ`, `Upd` counting it down with `Nat.sub`. -/
def stepW₆ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun i i' _ _ _ => i'.2 = Nat.sub i.2 1)
    (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ => True)

/-- `stepW₇`'s run-end relation: decrement by a match, true at `0`. -/
def updDec (i i' : Idx ℕ) : Prop :=
  match i.2 with
  | 0 => True
  | n + 1 => i'.2 = n

/-- `stepW₇`: `Upd` decrementing by a match. -/
def stepW₇ : SemWorld :=
  toyW ℕ 0 (fun _ _ _ => True) (fun i i' _ _ _ => updDec i i') (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True)

/-- A family indexed by `Idx ℕ`, with an `n + 1` constructor. -/
inductive StepFam : Idx ℕ → Prop
  | base (ls : List SRec) : StepFam (ls, 0)
  | step {ls : List SRec} {n : ℕ} : StepFam (ls, n) → StepFam (ls, n + 1)

/-- `stepW₈`: configurations through `StepFam` at `Stk := ℕ`. -/
def stepW₈ : SemWorld :=
  toyW ℕ 0 (fun _ _ i => StepFam i) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => True)

end Targets.Audit.Toy

end

/-! ### The audits, pinned -/

-- `coreW`'s report, checked against the pinned one
open Targets.Audit in
run_meta do
  let r ← audit #[``Targets.coreW]
  unless r.toList == expectedCore do
    throwError m!"the step-index audit of coreW changed: {r.toList}"

-- the negative tests: each step-indexed toy world shows up in the report kind its step index
-- takes, by a constant of its own (the shared closure, `Cell` and the rest, is the justified
-- baseline every world has)
open Targets.Audit in
run_meta do
  let toy (s : String) : Name := (`Targets.Audit.Toy).append (Name.mkSimple s)
  let checks : List (Name × String × Name) :=
    [(toy "stepW₁", "shapes", toy "stepW₁"), (toy "stepW₂", "families", toy "SafeN"),
     (toy "stepW₂", "succCtors", (toy "SafeN").append `succ), (toy "stepW₃", "iters", toy "stepW₃"),
     (toy "stepW₄", "fixes", toy "stepW₄"), (toy "stepW₉", "fixes", toy "stepW₉"),
     (toy "stepW₅", "arith", toy "stepW₅"),
     (toy "stepW₆", "arith", toy "stepW₆"), (toy "stepW₇", "shapes", (toy "updDec").append `match_1),
     (toy "stepW₈", "families", toy "StepFam"),
     (toy "stepW₈", "succCtors", (toy "StepFam").append `step)]
  for (w, kind, c) in checks do
    let r ← audit #[w]
    let xs := match kind with
      | "shapes" => r.shapes | "families" => r.families | "fixes" => r.fixes
      | "iters" => r.iters | "succCtors" => r.succCtors | _ => r.arith
    unless xs.contains c do
      throwError m!"the audit does not report {c} under {kind} for {w}: {sortNames xs}"

open Targets.Audit in
run_meta do
  for (n, h) in pinned do
    let h' ← pinHash n
    unless h' == h do
      throwError m!"Core's relation changed at {n}: {h'}, pinned {h}"
