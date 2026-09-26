import Backend.Clos.Syntax
import Backend.Flat.Runtime
import Backend.Flat.Host

/-!
# Backend — closure IR to flat IR

Each closure code becomes a function of two parameters, the closure and the argument. On entry
it loads the captured values into locals and frees the closure: calling a closure consumes it.
Each closure-IR variable is a local. A term is lowered for a destination, a local or `return`;
a call in `return` position is a tail call (`tailCallInd`). `case` is `ite` on the
injection's header; `letpair` and `case` free the object they take apart. `copy`/`drop` call
the runtime's deep copy and drop; `load` copies the cell's contents and `store` drops them.

Function indices: the runtime functions (`runtimeFns`), one host function per host operation the
program applies, the closure codes in table order, `main`, and the entry.
-/

namespace Backend.Flat
open BoCa Backend.Clos

inductive Dest where
  | ret
  | to (i : Nat)

structure LState where
  vars : List (Var × Nat)
  next : Nat

abbrev LM := StateT LState (Except String)

def localOf (x : Var) : LM Nat := do
  let s ← get
  match s.vars.lookup x with
  | some i => pure i
  | none =>
    set { s with vars := (x, s.next) :: s.vars, next := s.next + 1 }
    pure s.next

def temp : LM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def emit (d : Dest) (e : Exp) : List Stmt :=
  match d with
  | .ret => [.ret e]
  | .to i => [.set i e]

def lv (x : Var) : LM Exp := return .loc (← localOf x)

def lowerTm (hostIdx : HostOp → Nat) : Tm → Dest → LM (List Stmt)
  | .var x, d => return emit d (← lv x)
  | .unit, d => return emit d (.c64 unitW)
  | .lit (.i32 n), d => return emit d (.c64 (i32W n))
  | .lit (.i64 n), d => do
      let t ← temp
      return mkObj t hI64 [.c64 n] ++ emit d (.loc t)
  | .pair a b, d => do
      let t ← temp
      return mkObj t hPair [← lv a, ← lv b] ++ emit d (.loc t)
  | .inj r a, d => do
      let t ← temp
      return mkObj t (if r then hInj₂ else hInj₁) [← lv a] ++ emit d (.loc t)
  | .clos c xs, d => do
      let t ← temp
      let fields ← xs.mapM lv
      let h := hClos ||| (xs.length.toUInt64 <<< 8)
      return mkObj t h (.c64 c.toUInt64 :: fields) ++ emit d (.loc t)
  | .prim .alloc [v], d => do
      let t ← temp
      return mkObj t hCell [← lv v] ++ emit d (.loc t)
  | .prim .free [l], d => do
      let t ← temp
      let l ← lv l
      return [.set t (.load l 1), .free l] ++ emit d (.loc t)
  | .prim .load [l], d => do
      return emit d (.call fCopy [.load (← lv l) 1])
  | .prim .store [l, v], d => do
      let l ← lv l
      return [.eval (.call fDrop [.load l 1]), .store l 1 (← lv v)] ++ emit d (.c64 unitW)
  | .prim (.host op) [v], d => do
      return emit d (.call (hostIdx op) [← lv v])
  | .prim _ _, _ => throw "flat IR: primitive arity"
  | .app f a, d => do
      let f ← lv f
      let a ← lv a
      match d with
      | .ret => return [.tailCallInd (.load f 1) [f, a]]
      | .to i => return [.set i (.callInd (.load f 1) [f, a])]
  | .letv x e b, d => do
      let i ← localOf x
      let se ← lowerTm hostIdx e (.to i)
      let sb ← lowerTm hostIdx b d
      return se ++ sb
  | .letpair x y p b, d => do
      let p ← lv p
      let x ← localOf x
      let y ← localOf y
      let sb ← lowerTm hostIdx b d
      return [.set x (.load p 1), .set y (.load p 2), .free p] ++ sb
  | .case s x b₁ y b₂, d => do
      let s ← lv s
      let x ← localOf x
      let y ← localOf y
      let s₁ ← lowerTm hostIdx b₁ d
      let s₂ ← lowerTm hostIdx b₂ d
      return [.ite (eq64 (.load s 0) (.c64 hInj₁))
        ([.set x (.load s 1), .free s] ++ s₁) ([.set y (.load s 1), .free s] ++ s₂)]
  | .copy x x' b, d => do
      let x ← lv x
      let x' ← localOf x'
      let sb ← lowerTm hostIdx b d
      return [.set x' (.call fCopy [x])] ++ sb
  | .drop x b, d => do
      let x ← lv x
      let sb ← lowerTm hostIdx b d
      return [.eval (.call fDrop [x])] ++ sb

/-- A closure code: parameter `0` the closure, `1` the argument. -/
def lowerCode (hostIdx : HostOp → Nat) (k : Nat) (c : Code) : Except String Fn := do
  let act : LM (List Stmt) := do
    let unpack ← c.env.zipIdx.mapM fun (x, i) => do
      return Stmt.set (← localOf x) (.load (.loc 0) (i + 2))
    let body ← lowerTm hostIdx c.body .ret
    return unpack ++ [.free (.loc 0)] ++ body ++ [.trap]
  let (body, s) ← act.run ⟨[(c.param, 1)], 2⟩
  pure { name := s!"code{k}", params := 2, locals := s.next - 2, body }

def lowerMain (hostIdx : HostOp → Nat) (t : Tm) : Except String Fn := do
  let (body, s) ← (lowerTm hostIdx t .ret).run ⟨[], 0⟩
  pure { name := "main", params := 0, locals := s.next, body := body ++ [.trap] }

/-- Run `main`, print the value, drop it, print the live count. -/
def entryFn (fMain : Nat) : Fn where
  name := "entry"
  params := 0
  locals := 1
  body :=
    [.set 0 (.call fMain []), .eval (.call fPrint [.loc 0])] ++ outStr "\n" ++
      [.eval (.call fDrop [.loc 0])] ++ outStr "live " ++
      [.eval (.call fPrintDec [.live])] ++ outStr "\n" ++ [.ret (.c64 0)]

def lower (p : Clos.Prog) : Except String Prog := do
  let ops := p.hostOps
  let hostBase := runtimeFns.length
  let hostIdx (o : HostOp) : Nat := hostBase + (ops.idxOf? o).getD 0
  let codeBase := hostBase + ops.length
  let codes ← p.codes.toList.zipIdx.mapM fun (c, k) => lowerCode hostIdx k c
  let fMain := codeBase + codes.length
  let main ← lowerMain hostIdx p.main
  let fns := runtimeFns ++ ops.map hostFn ++ codes ++ [main, entryFn fMain]
  pure { fns := fns.toArray, table := (List.range codes.length).toArray.map (codeBase + ·),
         entry := fMain + 1 }

end Backend.Flat
