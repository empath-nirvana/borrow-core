import Backend.Driver
import Backend2.Driver

/-!
# Kernel census  (`docs/kernel-usage.md`)

    lake build kernel-census && .lake/build/bin/kernel-census <file.bc>…

Check each program as `bcc check` does (`Frontend.Check.checkProgram`) and count, over `main`'s
typed term (`Checked.t`), the nodes of each `TExpr` constructor, the type formers of the nodes'
judgments, and the qualifiers of the operations at `[handle]` nodes. Nothing here changes what
the compiler does: it reads the typed term the checker returns.

A `use` node holds the body of the `def` it uses, checked once per key (SPEC §3). Each count is
given twice:

* `static`: every node of `main`'s own term, and of each distinct body a `use` reaches once per
  program (the derivations the checker builds);
* `expanded`: through every `use` as often as it occurs (the nodes `t.erase` has, the term the
  backend compiles).

`lib` is the part of `static` inside bodies of declarations the library declares (index below the
elaborated program's `lib`). `progs` is the number of programs whose term has the node.

It also converts each program by the new backend (`Backend2/`, docs/n1-plan.md) and counts what the
conversion reads of the typed term, by rule and fact (`Backend2.readFact`): the facts a lowering
reads beside a node's term (a split's masks, a constant's types, a derived node's data, a type
former a layout is read from). A program outside the new backend's fragment reads nothing.

Output: tab-separated lines `node <ctor> progs static lib expanded <first programs>`,
`read <rule> <fact> progs count`,
`former <ctor> progs nodes`, `qual <q> progs ops`, and `fail <file> <message>` for a program that
does not check.
-/

open Lean Elab Term Meta in
/-- The constructors' names of an inductive type, in `ctorIdx` order. -/
elab "ctorNames% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let some (.inductInfo i) := (← getEnv).find? n | throwError "{n} is not an inductive type"
  let names := i.ctors.map fun c => match c with
    | .str _ s => s
    | c => c.toString
  return toExpr names.toArray

namespace KernelCensus
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

def texprNames : Array String := ctorNames% TExpr
def vtyNames : Array String := ctorNames% VTy
def ctyNames : Array String := ctorNames% CTy

/-- Counts by name. -/
abbrev Counts := Std.HashMap String Nat

def Counts.add (m : Counts) (k : String) (n : Nat := 1) : Counts :=
  m.insert k (m.getD k 0 + n)

def Counts.sum (a b : Counts) : Counts := b.fold (fun m k n => m.add k n) a

def Counts.scale (a : Counts) (n : Nat) : Counts := a.fold (fun m k v => m.insert k (v * n)) {}

def vName (t : VTy) : String := "V." ++ vtyNames[t.ctorIdx]!
def cName (t : CTy) : String := "C." ++ ctyNames[t.ctorIdx]!

mutual
/-- The formers of a value type, each once. -/
def formersV (acc : Std.HashSet String) : VTy → Std.HashSet String
  | t@(.tensor A B) | t@(.sum A B) => formersV (formersV (acc.insert (vName t)) A) B
  | t@(.thunk C) => formersC (acc.insert (vName t)) C
  | t@(.ref A) | t@(.imm _ A) | t@(.mut _ A) | t@(.box _ A) | t@(.bang A) | t@(.mu A)
  | t@(.fam A) => formersV (acc.insert (vName t)) A
  | t => acc.insert (vName t)
/-- The formers of a computation type, each once. -/
def formersC (acc : Std.HashSet String) : CTy → Std.HashSet String
  | t@(.ret A) => formersV (acc.insert (cName t)) A
  | t@(.arr A C) => formersC (formersV (acc.insert (cName t)) A) C
  | t@(.amp C D) => formersC (formersC (acc.insert (cName t)) C) D
  | t@(.all _ _ C) | t@(.nu C) => formersC (acc.insert (cName t)) C
  | t@(.eff _ _ _ A B fin cg C) =>
    -- A call-graded operation (SPEC §48) is counted as the former `C.eff.call` besides.
    let acc := if cg then acc.insert "C.eff.call" else acc
    formersC (formersC (formersV (formersV (acc.insert (cName t)) A) B) fin) C
  | t@.top => acc.insert (cName t)
end

def formersJ : Jdg → Std.HashSet String
  | .val A => formersV {} A
  | .comp C => formersC {} C

/-- A `use`'s identity: the declaration and its type arguments. -/
structure UseKey where
  decl : Nat
  name : String
  targs : List VTy
  deriving BEq

/-- What one term holds outside the bodies of its `use` nodes: its nodes, its nodes' formers, its
handler operations' qualifiers, and the `use` nodes directly under it. -/
structure Own where
  nodes : Counts := {}
  formers : Counts := {}
  quals : Counts := {}
  uses : List (UseKey × TExpr) := []

def qualName : Qual → String
  | .lin => "lin" | .aff => "aff" | .unr => "unr"

/-- The depth bound of the walk: the checker's (`Frontend.Check.checkFuel`). -/
def ownFuel : Nat := 1 <<< 20

def own : Nat → Own → TExpr → Own
  | 0, acc, _ => acc
  | fuel + 1, acc, t =>
  let acc := { acc with
    nodes := acc.nodes.add texprNames[t.ctorIdx]!,
    formers := (formersJ t.jdg).fold (fun m f => m.add f) acc.formers }
  let acc := match t with
    | .effHandleV _ _ _ E .. | .effHandleVB _ _ _ E .. | .effHandleT _ _ _ _ E ..
    | .effHandleL _ _ _ _ E .. =>
      { acc with quals := E.foldl (fun m (q, _, _) => m.add (qualName q)) acc.quals }
    | _ => acc
  match t with
  | .use _ _ name decl targs _ body => { acc with uses := acc.uses ++ [(⟨decl, name, targs⟩, body)] }
  | _ => t.children.foldl (fun a (_, c) => own fuel a c) acc

/-- One program's counts. -/
structure Prog where
  static : Counts := {}
  lib : Counts := {}
  expanded : Counts := {}
  formers : Counts := {}
  quals : Counts := {}

/-- Walk `main`: each distinct body once for `static`, every occurrence for `expanded`
(memoised by key). -/
def census (lib : Nat) (main : TExpr) : Prog := Id.run do
  let mut seen : List (UseKey × Own) := []
  let mut todo : List (UseKey × TExpr) := []
  let o := own ownFuel {} main
  let mut p : Prog := { static := o.nodes, expanded := {}, formers := o.formers, quals := o.quals }
  todo := o.uses
  -- static: each distinct body once
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | (k, b) :: rest =>
      todo := rest
      if seen.any (·.1 == k) then continue
      let ob := own ownFuel {} b
      seen := seen ++ [(k, ob)]
      p := { p with
        static := p.static.sum ob.nodes,
        lib := if k.decl < lib then p.lib.sum ob.nodes else p.lib,
        formers := p.formers.sum ob.formers,
        quals := p.quals.sum ob.quals }
      todo := todo ++ ob.uses
  -- expanded: memoised on keys, bodies' expansions computed bottom-up by repeated passes
  let mut memo : List (UseKey × Counts) := []
  let mut changed := true
  while changed do
    changed := false
    for (k, ob) in seen do
      if memo.any (·.1 == k) then continue
      let subs := ob.uses.map fun (k', _) => memo.find? (·.1 == k')
      if subs.all Option.isSome then
        let e := subs.foldl (fun m s => match s with | some (_, c) => m.sum c | none => m) ob.nodes
        memo := memo ++ [(k, e)]
        changed := true
  let top := o.uses.foldl (fun m (k, _) => match memo.find? (·.1 == k) with
    | some (_, c) => m.sum c | none => m) o.nodes
  pure { p with expanded := top }

/-- What the new backend's conversion reads of a program's typed term, when the program is in its
fragment. -/
def backend2Reads (file : String) : IO (List (String × Nat)) := do
  let src ← IO.FS.readFile file
  match Backend.checkedOf file src >>= fun k => Backend2.lirOf k (census := true) with
  | .ok (_, s) => return s.reads.toList
  | .error _ => return []

def checkFile (file : String) : IO (Except String (Nat × TExpr)) := do
  let src ← IO.FS.readFile file
  match Frontend.parseProgram src with
  | .error e => return .error (e.renderIn src)
  | .ok p =>
    match Frontend.Check.checkProgram p with
    | .error e => return .error (e.renderIn src)
    | .ok r => match r.main with
      | some c => return .ok (r.el.lib, c.t)
      | none => return .error "no main"

end KernelCensus

open KernelCensus in
def main (files : List String) : IO UInt32 := do
  let mut progs : Counts := {}
  let mut static : Counts := {}
  let mut lib : Counts := {}
  let mut expanded : Counts := {}
  let mut fprogs : Counts := {}
  let mut fnodes : Counts := {}
  let mut qprogs : Counts := {}
  let mut qops : Counts := {}
  let mut firsts : Std.HashMap String (List String) := {}
  let mut rprogs : Counts := {}
  let mut rcount : Counts := {}
  let mut inFrag : Nat := 0
  let mut fails : Nat := 0
  for f in files do
    match ← checkFile f with
    | .error e =>
      IO.println s!"fail\t{f}\t{(e.splitOn "\n").headD ""}"
      fails := fails + 1
    | .ok (l, t) =>
      let rs ← backend2Reads f
      if !rs.isEmpty then inFrag := inFrag + 1
      for (k, n) in rs do
        rprogs := rprogs.add k
        rcount := rcount.add k n
      let p := census l t
      for (k, n) in p.static.toList do
        progs := progs.add k
        static := static.add k n
        if (firsts.getD k []).length < 3 then firsts := firsts.insert k (firsts.getD k [] ++ [f])
      for (k, n) in p.lib.toList do lib := lib.add k n
      for (k, n) in p.expanded.toList do expanded := expanded.add k n
      for (k, n) in p.formers.toList do
        fprogs := fprogs.add k
        fnodes := fnodes.add k n
      for (k, n) in p.quals.toList do
        qprogs := qprogs.add k
        qops := qops.add k n
  for k in texprNames do
    IO.println s!"node\t{k}\t{progs.getD k 0}\t{static.getD k 0}\t{lib.getD k 0}\t{expanded.getD k 0}\t{" ".intercalate (firsts.getD k [])}"
  for k in vtyNames.map ("V." ++ ·) ++ ctyNames.map ("C." ++ ·) ++ #["C.eff.call"] do
    IO.println s!"former\t{k}\t{fprogs.getD k 0}\t{fnodes.getD k 0}"
  for k in ["lin", "aff", "unr"] do
    IO.println s!"qual\t{k}\t{qprogs.getD k 0}\t{qops.getD k 0}"
  for (k, n) in (rcount.toList.mergeSort (fun a b => a.1 ≤ b.1)) do
    let parts := k.splitOn ":"
    IO.println s!"read\t{parts.headD k}\t{(parts.drop 1).headD ""}\t{rprogs.getD k 0}\t{n}"
  IO.println s!"programs\t{files.length - fails}\tfailed\t{fails}\tbackend2\t{inFrag}"
  return 0
