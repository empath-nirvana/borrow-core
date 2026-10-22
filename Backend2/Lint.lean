import Std.Data.HashSet
import Backend2.Syntax
import Backend2.Layout

/-!
# Backend2 — the LIR lint  `[docs/compiler.md §5.2]`

A check of closure conversion's output, run in the gate on every program it compiles. It
verifies and never fills in:

- every variable has a type;
- every variable is bound once in the program, and consumed exactly once on every path of its
  function: a use consumes it, `copy` keeps it, the two arms of a `case` consume the same
  variables, and a function ends with all of them consumed (a path that ends at `absurd` is
  unreachable);
- every call has its callee's number of arguments, and every closure its code's environment;
- every `copy` is of a variable whose type is duplicable (`LTy.dupable`).

Every compile of the new backend runs it on the conversion's output (`Backend2/Driver.lean`,
`lintedLirOf`): the lowering reads the LIR's ownership and does not track it (`Lower.vals`), so
the lint is what makes "every variable consumed exactly once" a checked fact of every compiled
program.
-/

namespace Backend2.Lint
open Backend2

/-- **A type whose values the copy helper may duplicate** (`Backend2/Lower.lean`,
`genHelper (.copy _)`): it copies a pair or sum field by field, a closure with its environment,
and any other value's words as they are. Those words are a sound copy only where the value owns
nothing: a unit, an integer, a shared borrow (`imm`), a value of no content (`Unk`). An owned
cell (`ref`), a unique borrow (`mut`), an opaque capability, and a family (`(base, n)`) of any
leaves but shared borrows (an array owns its slots, a `mut` view borrows them uniquely) are not
duplicable; a family of shared borrows, a shared view, is. A `μ`'s variable stands for the `μ`
itself, so it is duplicable when its body is. A closure's type does not say: `!` is erased, so a
persistent closure and a linear one share a type. The closure classes are checked once the
layouts are known (`copiesDup`). -/
def _root_.Backend2.LTy.dupable : LTy → Bool
  | .unit | .zero | .int _ | .unk | .imm _ | .tvar _ | .thunk _ => true
  | .pair a b | .sum a b => a.dupable && b.dupable
  | .mu a => a.dupable
  | .fam (.imm _) => true
  | .ref _ | .mut _ | .fam _ | .opq _ => false

/-- What a path leaves unconsumed; `none` on a path that ends at `absurd`. -/
abbrev Left := Option (Std.HashSet Var)

structure St where
  bound : Std.HashSet Var := {}

abbrev LM := StateT St (Except String)

def bad (where_ : String) (msg : String) : LM α := throw s!"LIR lint: {where_}: {msg}"

def bindNew (w : String) (p : Prog) (env : Std.HashSet Var) (x : Var) : LM (Std.HashSet Var) := do
  if !(p.ty.contains x) then bad w s!"x{x} has no type"
  if (← get).bound.contains x then bad w s!"x{x} is bound twice"
  modify fun s => { s with bound := s.bound.insert x }
  return env.insert x

def use (w : String) (env : Std.HashSet Var) (x : Var) : LM (Std.HashSet Var) := do
  if !env.contains x then bad w s!"x{x} used when it is not owned (consumed, or out of scope)"
  return env.erase x

def useAll (w : String) (env : Std.HashSet Var) (xs : List Var) : LM (Std.HashSet Var) :=
  xs.foldlM (use w) env

def sameSet (a b : Std.HashSet Var) : Bool := a.size == b.size && a.toList.all b.contains

/-- The variables left after `t`, its value consumed by its context. -/
def lintTm (w : String) (p : Prog) : Nat → Std.HashSet Var → Tm → LM Left
  | 0, _, _ => bad w "a term too deep"
  | f + 1, env, t => match t with
    | .var x => return some (← use w env x)
    | .unit | .lit _ => return some env
    | .pair a b => return some (← useAll w env [a, b])
    | .inj _ a => return some (← use w env a)
    | .clos c xs => do
      let some code := p.codes[c]? | bad w s!"no code c{c}"
      for fn in code.fns do
        let some d := p.fns[fn]? | bad w s!"no function f{fn}"
        let k := if code.kind == .lam then d.params.length - 1 else d.params.length
        if k != xs.length then bad w s!"c{c}'s closure of {xs.length} values for {k}"
      return some (← useAll w env xs)
    | .app g a => return some (← useAll w env [g, a])
    | .app0 g | .sel g _ => return some (← use w env g)
    | .call fn as => do
      let some d := p.fns[fn]? | bad w s!"no function f{fn}"
      if d.params.length != as.length then
        bad w s!"f{fn} ({d.name}) called on {as.length} arguments for {d.params.length}"
      return some (← useAll w env as)
    | .prim _ as => return some (← useAll w env as)
    | .letv x e b => do
      match ← lintTm w p f env e with
      | none => return none
      | some env' => lintTm w p f (← bindNew w p env' x) b
    | .letpair x y q b => do
      let env ← use w env q
      let env ← bindNew w p env x
      lintTm w p f (← bindNew w p env y) b
    | .case sv x b₁ y b₂ => do
      let env ← use w env sv
      let l₁ ← lintTm w p f (← bindNew w p env x) b₁
      let l₂ ← lintTm w p f (← bindNew w p env y) b₂
      match l₁, l₂ with
      | none, l | l, none => return l
      | some a, some b =>
        if !sameSet a b then
          bad w s!"the arms of a case on x{sv} consume different variables: {a.toList.filter (!b.contains ·)} / {b.toList.filter (!a.contains ·)}"
        return some a
    | .absurd sv => do let _ ← use w env sv; return none
    | .copy x x' b => do
      if !env.contains x then bad w s!"x{x} copied when it is not owned"
      match p.ty[x]? with
      | none => bad w s!"x{x} has no type"
      | some t =>
        if !t.dupable then
          bad w s!"x{x} copied at a type that is not duplicable: {t}"
      lintTm w p f (← bindNew w p env x') b
    | .drop x b => do lintTm w p f (← use w env x) b

/-- Lint a program. -/
def lint (p : Prog) : Except String Unit := do
  let act : LM Unit := do
    for (d, i) in p.fns.toList.zipIdx do
      let w := s!"f{i} ({d.name})"
      let mut env : Std.HashSet Var := {}
      for x in d.params do env ← bindNew w p env x
      match ← lintTm w p (1 <<< 22) env d.body with
      | some rest => if !rest.isEmpty then bad w s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
      | none => pure ()
    match ← lintTm "main" p (1 <<< 22) {} p.main with
    | some rest => if !rest.isEmpty then bad "main" s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
    | none => pure ()
  let _ ← act.run {}

/-! ### The copies at the layouts -/

/-- A code's environment: its function's parameters before its argument. -/
def envVars (p : Prog) (c : Nat) : List Var := Id.run do
  let some code := p.codes[c]? | return []
  let some fn := code.fns.head? | return []
  let some d := p.fns[fn]? | return []
  let k := if code.kind == .lam then d.params.length - 1 else d.params.length
  return d.params.take k

/-- **The layout nodes whose copy duplicates what is not duplicable** (`genHelper (.copy _)`,
node for node): a closure class one of whose codes has an environment value of a type that is not
duplicable (`LTy.dupable`), and every node from which the helper reaches one: a pair or sum
through a field, a closure class through an environment value of one of its codes. The least set
closed under those steps, by a search back along the reverse edges: linear in the layouts. A
pointer's node (`ref`, `imm`, `mut`, a family) is not read here: the helper copies its words, and
the layouts join an owner's node with its borrows' (a lend's address is the owner's), so the
pointer's kind is the variable's type's, which `LTy.dupable` reads. -/
def badNodes (p : Prog) (L : Lay.Layouts) : Std.HashSet Nat := Id.run do
  let n := L.shape.size
  let mut parents : Array (List Nat) := Array.replicate n []
  let mut todo : Array Nat := #[]
  let mut bad : Std.HashSet Nat := {}
  for i in [0:n] do
    if L.r i != i then continue
    let kids : List Nat := match L.sh i with
      | .pair a b | .sum a b => [a, b]
      | .clos .. => (L.unionOf i).toList.flatMap fun c => L.codeEnv.getD c []
      | _ => []
    for k in kids do
      let k := L.r k
      if k < n then parents := parents.modify k (i :: ·)
    let base := match L.sh i with
      | .clos .. => (L.unionOf i).any fun c =>
        (envVars p c).any fun x => !((p.ty[x]?.map LTy.dupable).getD false)
      | _ => false
    if base then
      bad := bad.insert i
      todo := todo.push i
  while h : todo.size > 0 do
    let i := todo[todo.size - 1]
    todo := todo.pop
    for q in parents[i]?.getD [] do
      if !bad.contains q then
        bad := bad.insert q
        todo := todo.push q
  return bad

/-- The variables a term copies. -/
def copiedIn : Nat → Tm → List Var
  | 0, _ => []
  | f + 1, t => match t with
    | .letv _ e b => copiedIn f e ++ copiedIn f b
    | .letpair _ _ _ b | .drop _ b => copiedIn f b
    | .case _ _ b₁ _ b₂ => copiedIn f b₁ ++ copiedIn f b₂
    | .copy x _ b => x :: copiedIn f b
    | _ => []

/-- **Every copy is of a value the copy helper duplicates soundly**, read at the layouts (the
helper's own dispatch): a copy of a closure copies its class's environments, so each code of the
class has an environment of duplicable values (`badNodes`). The lint's type check
(`LTy.dupable`) cannot see a closure's environment. -/
def copiesDup (p : Prog) (L : Lay.Layouts) : Except String Unit := do
  let bad := badNodes p L
  let bodies := (p.fns.toList.zipIdx.map fun (d, i) => (s!"f{i} ({d.name})", d.body)) ++ [("main", p.main)]
  for (w, b) in bodies do
    for x in copiedIn (1 <<< 22) b do
      if bad.contains (L.node x) then
        throw s!"LIR lint: {w}: x{x} copied at a layout the copy helper cannot duplicate: a closure class holds a value that is not duplicable"

end Backend2.Lint
