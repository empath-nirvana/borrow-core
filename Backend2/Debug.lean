import Backend2.Types

/-!
# Backend2 — the typed term, printed

`bcc lir --typed <file>` prints `main`'s typed term (`Checked.t`) one node a line: its rule, its
judgment at LIR types, and the fields the new backend reads (masks, binders' types, derived
nodes' data). A reading aid, not a stage.
-/

open Lean Elab Term Meta in
/-- The constructors' names of an inductive type, in `ctorIdx` order. -/
elab "ctorNames2% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let some (.inductInfo i) := (← getEnv).find? n | throwError "{n} is not an inductive type"
  let names := i.ctors.map fun c => match c with
    | .str _ s => s
    | c => c.toString
  return toExpr names.toArray

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- The rule of each `TExpr` constructor, by `ctorIdx`. -/
def texprNames : Array String := ctorNames2% TExpr

def ruleName (t : TExpr) : String := texprNames[t.ctorIdx]!

def ppJ (j : Jdg) : String :=
  match ofJ j with
  | .ok (.inl a) => a.pp
  | .ok (.inr k) => "{" ++ k.pp ++ "}"
  | .error e => s!"<{e}>"

def ppVT (A : VTy) : String := match ofV A with
  | .ok a => a.pp
  | .error e => s!"<{e}>"

def ppMasks (m : Masks) : String :=
  String.ofList (m.ms.map fun (a, b) => match a, b with
    | true, true => 'B' | true, false => 'L' | false, true => 'R' | false, false => '.')

/-- The fields of a node worth printing beside its rule. -/
def nodeFields : TExpr → String
  | .var i _ n _ => s!"#{n} {i.name}"
  | .lit _ _ c => reprStr c
  | .hostOp _ _ o => reprStr o
  | .use _ _ name decl targs ab _ =>
    s!"{name} decl {decl} [{", ".intercalate (targs.map ppVT)}] ab {ab.isSome}"
  | .force _ _ i _ => s!"#{i}"
  | .app _ _ i _ _ _ _ => s!"#{i}"
  | .selfCall _ _ j n _ => s!"member {j} of {n}"
  | .litFn _ _ bs _ => s!"{bs.length} bytes"
  | .divLit _ _ op c _ => s!"{reprStr op} {reprStr c}"
  | .walk _ _ m r _ => s!"mut {m} read {r}"
  | .walkGet _ _ m _ => s!"mut {m}"
  | .lendCell _ _ m _ => s!"mut {m}"
  | .nuEta _ _ f s _ => "f #" ++ toString f ++ (match s with | some k => " s #" ++ toString k | none => "")
  | .dtor _ _ A => ppVT A
  | t => match t.masks? with
    | some m => ppMasks m
    | none => ""

/-- The typed term, a node a line, indented by depth; `fuel` bounds the depth. -/
def dumpT : Nat → Nat → TExpr → List String
  | 0, _, _ => ["…"]
  | f + 1, d, t =>
    let line := String.ofList (List.replicate (2 * d) ' ') ++ ruleName t ++ " : " ++ ppJ t.jdg ++
      (let fs := nodeFields t; if fs.isEmpty then "" else "  [" ++ fs ++ "]")
    line :: t.children.flatMap fun (sc, c) =>
      let tag := match sc with
        | .push 0 => [] | .push n => [String.ofList (List.replicate (2 * d + 2) ' ') ++ s!"(+{n})"]
        | .fresh n => [String.ofList (List.replicate (2 * d + 2) ' ') ++ s!"(fresh {n})"]
      tag ++ dumpT f (d + 1) c

end Backend2
