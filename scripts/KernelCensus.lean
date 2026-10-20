import Backend.Driver

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

Output: tab-separated lines `node <ctor> progs static lib expanded <first programs>`,
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

mutual
/-- The formers of a value type, each once. -/
partial def formersV (acc : Std.HashSet String) : VTy → Std.HashSet String
  | t =>
    let acc := acc.insert ("V." ++ vtyNames[t.ctorIdx]!)
    match t with
    | .tensor A B | .sum A B => formersV (formersV acc A) B
    | .thunk C => formersC acc C
    | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => formersV acc A
    | _ => acc
/-- The formers of a computation type, each once. -/
partial def formersC (acc : Std.HashSet String) : CTy → Std.HashSet String
  | t =>
    let acc := acc.insert ("C." ++ ctyNames[t.ctorIdx]!)
    match t with
    | .ret A => formersV acc A
    | .arr A C => formersC (formersV acc A) C
    | .amp C D => formersC (formersC acc C) D
    | .all _ _ C | .nu C => formersC acc C
    | .eff _ _ _ A B fin C => formersC (formersC (formersV (formersV acc A) B) fin) C
    | .top => acc
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

partial def own (acc : Own) (t : TExpr) : Own :=
  let acc := { acc with
    nodes := acc.nodes.add texprNames[t.ctorIdx]!,
    formers := (formersJ t.jdg).fold (fun m f => m.add f) acc.formers }
  let acc := match t with
    | .effHandleV _ _ _ E .. | .effHandleVB _ _ _ E .. | .effHandleT _ _ _ _ E .. =>
      { acc with quals := E.foldl (fun m (q, _, _) => m.add (qualName q)) acc.quals }
    | _ => acc
  match t with
  | .use _ _ name decl targs _ body => { acc with uses := acc.uses ++ [(⟨decl, name, targs⟩, body)] }
  | _ => t.children.foldl (fun a (_, c) => own a c) acc

/-- One program's counts. -/
structure Prog where
  static : Counts := {}
  lib : Counts := {}
  expanded : Counts := {}
  formers : Counts := {}
  quals : Counts := {}

/-- Walk `main`: each distinct body once for `static`, every occurrence for `expanded`
(memoised by key). -/
partial def census (lib : Nat) (main : TExpr) : Prog := Id.run do
  let mut seen : List (UseKey × Own) := []
  let mut todo : List (UseKey × TExpr) := []
  let o := own {} main
  let mut p : Prog := { static := o.nodes, expanded := {}, formers := o.formers, quals := o.quals }
  todo := o.uses
  -- static: each distinct body once
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | (k, b) :: rest =>
      todo := rest
      if seen.any (·.1 == k) then continue
      let ob := own {} b
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
  let mut fails : Nat := 0
  for f in files do
    match ← checkFile f with
    | .error e =>
      IO.println s!"fail\t{f}\t{(e.splitOn "\n").headD ""}"
      fails := fails + 1
    | .ok (l, t) =>
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
  for k in vtyNames.map ("V." ++ ·) ++ ctyNames.map ("C." ++ ·) do
    IO.println s!"former\t{k}\t{fprogs.getD k 0}\t{fnodes.getD k 0}"
  for k in ["lin", "aff", "unr"] do
    IO.println s!"qual\t{k}\t{qprogs.getD k 0}\t{qops.getD k 0}"
  IO.println s!"programs\t{files.length - fails}\tfailed\t{fails}"
  return 0
