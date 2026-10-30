import Std.Data.HashSet
import Backend2.Syntax

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
- every `lend` answers a borrow of its kind: `mut` or `imm` (`Op.lend`, SPEC §57);
- every `copy` is of a variable its type lets the program duplicate (`copyable`): a persistent
  one, `!` read off the LIR type (`Types.ofV` keeps it), or an `imm` borrow;
- every `drop` is of a variable its type lets the program discard (`droppable`), but for the
  callees' suspended computations a stack machine drops (`Prog.stackKs`); a type owning an opaque
  value is never `droppable`;
- every `abandon` meets the premise of the rule the node carries (`abandonable`): at a `[let]`'s
  abort, `effLet`'s `hW` (the variable's type holds no owned cell, `VTy.Drop`); at `⊤`, `topI`'s,
  which has none. It is the only node at which an opaque value is discarded, and `Convert` emits
  it only at those rules' sites.
-/

namespace Backend2.Lint
open Backend2 BoCa.Fig16.LogRel.Core

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

/-- The kind of a borrow's type: `mut`, `imm`, or neither (`!` read through: `LTy.unbang`). -/
def borrowMode (t : LTy) : Option Bool :=
  match t.unbang with
  | .mut _ | .fam (.mut _) => some true
  | .imm _ | .fam (.imm _) => some false
  | _ => none

/-- A type whose values `copy` may duplicate: a persistent one (`LTy.persistent`: a slot a split
duplicates, `Ctx.SplitP.dup`, and what `clone` copies), or an `imm` borrow or a family of them
(the `copy` and `array_copy` constants, `axCopyTy`, `arrCopyTy`). -/
def copyable (t : LTy) : Bool :=
  t.persistent || match t with
    | .imm _ | .fam (.imm _) => true
    | _ => false

/-- A type whose values `drop` may discard anywhere: a persistent one (`Ctx.DeadP.drop`,
`Ctx.SoloP.skip`), one that holds no owned cell and no opaque value (`LTy.drops` without
`LTy.ownsOpq`: the `forget` constants at `Imm`, `Mut`, `Unk`, `!A`), or a family of borrows
(`array_forget`, and the destructor at `[Mut A]`, `dtorAt`: `forget_fam_compatX`). -/
def droppable (t : LTy) : Bool :=
  t.persistent || (t.drops && !t.ownsOpq) || match t with
    | .fam (.imm _) | .fam (.mut _) => true
    | _ => false

/-- A type whose values an `abandon` node at the rule `r` may discard: the premise of `r`, read
on the LIR type. At a `[let]`'s abort, `CDerives.effLet`'s `hW : S.Weak → Γ₂.Drops`: each slot
of `N`'s context is at a `VTy.Drop` type, which `LTy.drops` reads (`ofV_drops`), an opaque value
among them. At `⊤`, `CDerives.topI`, which has no premise: `⊤` absorbs its whole context at every
type. No other rule discards an opaque value: no constant forgets it and it has no destructor. -/
def abandonable : Abandon → LTy → Bool
  | .letAbort, t => t.drops
  | .top, _ => true

/-- A slot a split duplicates (`Ctx.SplitP.dup`: of persistent type) is `copyable` at its LIR
type. -/
theorem copyable_ofV {ms : MachSet} {A : VTy} {t : LTy} (hA : A.persistent = true)
    (h : ofV ms A = .ok t) : copyable t = true := by
  simp [copyable, ofV_persistent hA h]

/-- A slot a leaf drops (`Ctx.DeadP.drop`: of persistent type) is `droppable` at its LIR type. -/
theorem droppable_ofV_persistent {ms : MachSet} {A : VTy} {t : LTy} (hA : A.persistent = true)
    (h : ofV ms A = .ok t) : droppable t = true := by
  simp [droppable, ofV_persistent hA h]

/-- A slot an abort abandons (`Ctx.Drops`: of a `VTy.OwnFree` type) is `abandonable` at its LIR
type. -/
theorem abandonable_ofV_drop {ms : MachSet} {A : VTy} {t : LTy} (hA : A.OwnFree)
    (h : ofV ms A = .ok t) : abandonable .letAbort t = true := by
  simp [abandonable, ofV_drops hA h]

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
    -- A path that reaches `unreachable` is never run, as one that ends at `absurd`.
    | .prim .unreachable as => do let _ ← useAll w env as; return none
    | .prim _ as => return some (← useAll w env as)
    | .letv x e b => do
      if let .prim (.lend m) _ := e then
        match p.ty[x]? with
        | some (.pair _ bT) =>
          if borrowMode bT != some m then bad w s!"x{x}: a lend of kind {m} answers a borrow at {bT}"
        | t => bad w s!"x{x}: a lend answers {t.map (·.pp)}"
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
      | some t => if !copyable t then bad w s!"x{x} copied at {t}, which is not persistent"
      | none => bad w s!"x{x} has no type"
      lintTm w p f (← bindNew w p env x') b
    | .drop x b => do
      match p.ty[x]? with
      | some t =>
        if !droppable t && !p.stackKs.contains x then
          bad w s!"x{x} dropped at {t}, which may own a cell or an opq value"
      | none => bad w s!"x{x} has no type"
      lintTm w p f (← use w env x) b
    | .abandon r x b => do
      match p.ty[x]? with
      | some t =>
        if !abandonable r t then
          bad w s!"x{x} abandoned at {t} ({r.name}), where the rule's premise does not hold"
      | none => bad w s!"x{x} has no type"
      lintTm w p f (← use w env x) b

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

end Backend2.Lint
