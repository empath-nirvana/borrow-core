import Backend.Driver
import Backend2.Debug
import Core.CapNorm

/-!
# `CapOK` over the corpus  (#855 K0, SPEC §68)

    lake build cap-ok && .lake/build/bin/cap-ok <file.bc>…

Walks each program's typed term with its context: slot types and live flags, the live flags of
each split's parts read from the node's masks (the first child gets the first part, every other
child the second, as every split rule of `CDerives` has it), the pushed slots from the rule
(`lam`, `bind`, `tensorE`, `sumE`, `effLet`, `effThen` live at their types; `thunkF`,
`bangThunkF`, `lamDead`, `withI`, `allI`, `letPoly` dead). A `fresh` context's slots are of
unknown type. At each closure node (`thunkF`, `thunkV`, `bangThunkF`, `bangThunkV`) it reports
the live slots the erased term does not mention whose type is not persistent (or not known), and
captured slots that are dead. Each `use` body once per key.

Output: `clo <file> ok`, `clo <file> fail <slots>`, `deadcap <file>`, `fail <file> <message>`.
-/

namespace CapOKExp
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

structure Slot where
  ty : Option VTy
  live : Bool
  deriving Inhabited

structure UseKey where
  decl : Nat
  name : String
  targs : List VTy
  deriving BEq

structure Acc where
  out : Array String := #[]
  seen : List UseKey := []

def retTy? : Jdg → Option VTy
  | .comp (.ret A) => some A
  | _ => none

def isClo : TExpr → Bool
  | .thunkF .. | .thunkV .. | .bangThunkF .. | .bangThunkV .. => true
  | _ => false

def showSlot (s : Slot) : String := match s.ty with
  | some A => Backend2.ppVT A
  | none => "?"

/-- The node's subtree holds a `topI` or `zeroE`, the two rules that absorb live slots. -/
def absorbs : Nat → TExpr → Bool
  | 0, _ => false
  | f + 1, t => match t with
    | .topI .. | .zeroE .. => true
    | _ => t.children.any fun (_, c) => absorbs f c

def check (file : String) (ctx : List Slot) (t : TExpr) : String :=
  let e := t.erase
  let caps := Expr.capVars e
  let bad := (List.range ctx.length).filterMap fun i =>
    let s := ctx[i]!
    if s.live && !caps.contains i then
      match s.ty with
      | some A => if A.persistent then none else some s!"#{i}:{showSlot s}"
      | none => some s!"#{i}:?"
    else none
  let deadCap := caps.any fun i => match ctx[i]? with | some s => !s.live | none => true
  let live := (List.range ctx.length).filter fun i => ctx[i]!.live
  let unusedP := live.filter fun i => !caps.contains i
  let base := if bad.isEmpty then s!"clo {file} ok live={live.length} caps={caps.length} unusedPersistent={unusedP.length}" else s!"clo {file} fail {" ".intercalate bad}"
  let base := if absorbs 100000 t then base ++ " absorbs" else base
  if deadCap then base ++ " deadcap" else base

/-- The pushed slots of child `k` of a node, innermost first. -/
def pushed (t : TExpr) (k : Nat) (n : Nat) : List Slot :=
  let dead (m : Nat) : List Slot := List.replicate m ⟨some .unit, false⟩
  match t, k with
  | .lam _ _ A _ _, _ => [⟨some A, true⟩]
  | .bind _ _ A _ _ _ _, 1 => [⟨some A, true⟩]
  | .tensorE _ _ A B _ _ _ _, 1 => [⟨some B, true⟩, ⟨some A, true⟩]
  | .sumE _ _ A _ _ _ _ _ _, 1 => [⟨some A, true⟩]
  | .sumE _ _ _ B _ _ _ _ _, 2 => [⟨some B, true⟩]
  | .effLet _ _ A _ _ _ _ _, 1 => [⟨some A, true⟩]
  | .effThen _ _ A _ _ _ _ _ _ _ _, 1 => [⟨some A, true⟩]
  | .effThenDiv _ _ A _ _ _ _ _ _ _ _, 1 => [⟨some A, true⟩]
  | .effThen .., 2 | .effThenDiv .., 2 => dead 1
  | .thunkF .., _ | .bangThunkF .., _ | .lamDead .., _ | .withI .., _ | .allI .., _
  | .letPoly .., _ => dead n
  | _, _ => List.replicate n ⟨none, true⟩

def walk (file : String) : Nat → List Slot → Acc → TExpr → Acc
  | 0, _, acc, _ => acc
  | fuel + 1, ctx, acc, t =>
    let acc := if isClo t then { acc with out := acc.out.push (check file ctx t) } else acc
    match t with
    | .use _ _ name decl targs _ body =>
      let k : UseKey := ⟨decl, name, targs⟩
      if acc.seen.any (· == k) then acc
      else walk file fuel ctx { acc with seen := k :: acc.seen } body
    | _ =>
      let parts : Nat → List Slot := fun k => match t.masks? with
        | some m => (List.range ctx.length).map fun i =>
            let s := ctx[i]!
            let (a, b) := m.at i
            { s with live := s.live && (if k == 0 then a else b) }
        | none => ctx
      (t.children.zipIdx).foldl (fun a ((sc, c), k) =>
        let ctx' := match sc with
          | .push n => pushed t k n ++ parts k
          | .fresh n => List.replicate n ⟨none, true⟩
        walk file fuel ctx' a c) acc

def run (file : String) : IO Unit := do
  let src ← IO.FS.readFile file
  match Frontend.parseProgram src with
  | .error e => IO.println s!"fail {file} {e.renderIn src}"
  | .ok p => match Frontend.Check.checkProgram p with
    | .error e => IO.println s!"fail {file} {(e.renderIn src).replace "\n" " "}"
    | .ok r => match r.main with
      | some c =>
        let ctx := c.ctx.map fun s => (⟨some s.ty, s.live⟩ : Slot)
        for l in (walk file (1 <<< 20) ctx {} c.t).out do IO.println l
      | none => IO.println s!"fail {file} no main"

end CapOKExp

def main (files : List String) : IO UInt32 := do
  for f in files do CapOKExp.run f
  return 0
