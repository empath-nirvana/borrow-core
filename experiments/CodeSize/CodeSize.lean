import Backend.Driver
import Core.CodeNu

/-!
# Code sizes  (#855 K0, SPEC §68's memory measurement)

    lake build code-size && .lake/build/bin/code-size <file.bc>…

Checks each program as `bcc check` does and walks `main`'s typed term (`Checked.t`), each `use`
body once per key. At every closure node (`thunkF`, `thunkV`, `bangThunkF`, `bangThunkV`) it
prints the size, in `Expr` nodes, of the code `capNorm (t.erase)`, and the size of the type
`Code⟨N; E⟩ C` with codes nested inside `E`: the code's size plus, for each capture, the nested
size of the closure the slot is bound to (by `bind` or `letPoly` of a closure node), or `1`.
At each `unfoldN` node it prints the size of `unfold`'s codata code `etaCode C`.
At each `var` node of a slot bound to a closure, it prints that slot's nested size (`mention`):
the copies a typed term holding the type at every use would store.

Output: `clo <file> <codeSize> <typeSize> <captures>`, `eta <file> <size>`,
`mention <file> <typeSize>`, `fail <file> <message>`. Nothing here changes a check.
-/

namespace CodeSize
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

def esize : Expr → Nat
  | .var _ | .unit | .loc _ | .prim _ => 1
  | .pair a b | .seq a b | .letpair a b | .app a b => esize a + esize b + 1
  | .inj₁ a | .inj₂ a | .lam a => esize a + 1
  | .case a b c => esize a + esize b + esize c + 1

structure UseKey where
  decl : Nat
  name : String
  targs : List VTy
  deriving BEq

structure Acc where
  out : Array String := #[]
  seen : List UseKey := []

/-- The nested type size of a closure node, at the context `ctx` (each slot the nested size of
the closure it is bound to, if any). -/
def cloSize (ctx : List (Option Nat)) (t : TExpr) : Option (Nat × Nat × Nat) :=
  match t with
  | .thunkF .. | .thunkV .. | .bangThunkF .. | .bangThunkV .. =>
    let e := t.erase
    let n := esize (Expr.capNorm e)
    let caps := Expr.capVars e
    let ty := caps.foldl (fun s i => s + ((ctx[i]?).bind id).getD 1) n
    some (n, ty, caps.length)
  | _ => none

/-- A bound value's nested type size, through `ret`. -/
def boundSize (ctx : List (Option Nat)) : TExpr → Option Nat
  | .ret _ _ _ t => boundSize ctx t
  | t => (cloSize ctx t).map (·.2.1)

def walk (file : String) : Nat → List (Option Nat) → Acc → TExpr → Acc
  | 0, _, acc, _ => acc
  | fuel + 1, ctx, acc, t =>
    let acc := match cloSize ctx t with
      | some (n, ty, k) => { acc with out := acc.out.push s!"clo {file} {n} {ty} {k}" }
      | none => acc
    let acc := match t with
      | .unfoldN _ _ C _ => { acc with out := acc.out.push s!"eta {file} {esize (etaCode C)}" }
      | .var _ _ i _ => match (ctx[i]?).bind id with
        | some s => { acc with out := acc.out.push s!"mention {file} {s}" }
        | none => acc
      | _ => acc
    match t with
    | .use _ _ name decl targs _ body =>
      let k : UseKey := ⟨decl, name, targs⟩
      if acc.seen.any (· == k) then acc
      else walk file fuel ctx { acc with seen := k :: acc.seen } body
    | .bind _ _ _ _ _ tM tN =>
      let acc := walk file fuel ctx acc tM
      walk file fuel (boundSize ctx tM :: ctx) acc tN
    | .letPoly _ _ _ _ tV tN =>
      let acc := walk file fuel [] acc tV
      walk file fuel (boundSize [] tV :: ctx) acc tN
    | _ => t.children.foldl (fun a (sc, c) =>
        let ctx' := match sc with
          | .push n => List.replicate n none ++ ctx
          | .fresh n => List.replicate n none
        walk file fuel ctx' a c) acc

def run (file : String) : IO Unit := do
  let src ← IO.FS.readFile file
  match Frontend.parseProgram src with
  | .error e => IO.println s!"fail {file} {e.renderIn src}"
  | .ok p => match Frontend.Check.checkProgram p with
    | .error e => IO.println s!"fail {file} {(e.renderIn src).replace "\n" " "}"
    | .ok r => match r.main with
      | some c => for l in (walk file (1 <<< 20) [] {} c.t).out do IO.println l
      | none => IO.println s!"fail {file} no main"

end CodeSize

def main (files : List String) : IO UInt32 := do
  for f in files do CodeSize.run f
  return 0
