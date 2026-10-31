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
- every `copy` meets the premise of the rule the node carries (`copiesAt`): `Ctx.SplitP.dup` at a
  persistent type, `!` read off the LIR type (`Types.ofV` keeps it); the `copy` constants and
  `copy_derives` at an `imm` borrow;
- every `drop` meets the premise of the rule the node carries (`dropsAt`), a `dtor` one only in a
  destructor function (`Prog.dtorFns`), a `stackK` one only as a stack machine's hand-over, its
  premise read from the node (`handsOver`); no rule drops a type owning an opaque value;
- no `&` is observed at a `⊤` component (`⊤` has no elimination);
- every `abandon` meets the premise of the rule the node carries (`abandonable`): at a `[let]`'s
  abort, `effLet`'s `hW` (the variable's type holds no owned cell, `VTy.Drop`); at a superseded
  raise payload, `effRaise`'s `hd`, the same; at `⊤`, `topI`'s, which has none. It is the only
  node at which an opaque value is discarded, and `Convert` emits it only at those rules' sites.
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

/-- **A copy at the rule `r`**, its premise read on the LIR type:
- `dup` (`Ctx.SplitP.dup`): an unrestricted type (`LTy.persistent`, kept by `ofV_persistent`);
- `const` and `derived` (`CDerives.copy`/`arrCopy`, `copy_derives`): `DerivedCopy`, an `imm`
  borrow or a family of them. -/
def copiesAt : CopyRule → LTy → Bool
  | .dup, t => t.persistent
  | .const, t | .derived, t => match t.unbang with
    | .imm _ | .fam (.imm _) => true
    | _ => false

/-- **A drop at the rule `r`**, its premise read on the LIR type:
- `dead` (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`): an unrestricted type;
- `forget` (the `forget` constants, `arrForget`): `Imm`, `Mut`, `Unk`, `[Imm A]`;
- `dtor` (`drop_derives`): only in a destructor function (`Prog.dtorFns`, checked by `lintTm`), a
  leaf the destructor forgets: an unrestricted type, a borrow, `Unk`, or a family of borrows
  (`HasDtor.arrayMut` at `[Mut A]`: `dtorAt` is `idx` then `forget`);
- `unused`: an unrestricted type, the premise of the weakening the part that receives the slot
  applies at its leaves (`Ctx.DeadP.drop`); a persistent value holds no resource
  (`vP_empty_of_persistent`), so dropping it at the split is the same. A slot the part absorbs
  instead (`⊤`, `absurd`) is refused here, not dropped: that no checked program has one of a type
  that is not persistent is `UNPROVED:` (`Check.SplitMasks.NeitherAbsorbed` states the cases);
- `stackK` (`UNPROVED:`, F3, `StackKHandOver`): a closure of a `&` code, the rest of its
  premise read from the node (`handsOver`, checked by `lintTm`).
No rule drops a value that owns an opaque value: an abort abandons it (`abandon`). -/
def dropsAt : DropRule → LTy → Bool
  | .dead, t => t.persistent
  | .forget, t => match t.unbang with
    | .imm _ | .mut _ | .unk | .fam (.imm _) => true
    | _ => false
  | .dtor, t => t.persistent || match t.unbang with
    | .imm _ | .mut _ | .unk | .fam (.imm _) | .fam (.mut _) => true
    | _ => false
  | .unused, t => t.persistent
  | .stackK, t => match t with
    | .thunk (.amp _ _) => true
    | _ => false

/-- **A `stackK` drop's premise, read from the node**: the stack machine's hand-over of `x`, a
level's suspended computation, to the `k` the drop's body binds first, `let k₂ = clos kc [base]`.
`kc` is a `&` code each of whose functions takes one address (the machine's resume and cancel
entries over its base), `x` and `k₂` are both of `kc`'s closure type, and `base` is an address.
What the node cannot show, that `x` is `clos kc [a]` with `base` at or below `a` on the task stack
and the frames from the top down to `a` written, is `UNPROVED:` (`Backend2.StackKHandOver`); the
LIR interpreter checks it on every run (`Backend2.handOverB`). `none` when the premise holds, else
what fails. -/
def handsOver (p : Prog) (x : Var) : Tm → Option String
  | .letv k₂ (.clos kc [base]) _ => Id.run do
    let some code := p.codes[kc]? | return some s!"no code c{kc}"
    if code.kind != .amp then return some s!"c{kc}, the code of the k it hands over to, is not a `&` code"
    for fn in code.fns do
      let some d := p.fns[fn]? | return some s!"no function f{fn}"
      unless d.params.length == 1 && d.params.all (p.ty[·]? == some (.int .w64)) do
        return some s!"f{fn} ({d.name}), an entry of c{kc}, does not take one address"
    let kT := LTy.thunk code.ty
    if p.ty[x]? != some kT then return some s!"x{x} is not of c{kc}'s closure type"
    if p.ty[k₂]? != some kT then return some s!"x{k₂}, the k it hands over to, is not of c{kc}'s closure type"
    if p.ty[base]? != some (.int .w64) then return some s!"x{base}, the base, is not an address"
    return none
  | _ => some "its body does not first bind the k it hands over to, `clos kc [base]`"

/-- A type whose values an `abandon` node at the rule `r` may discard: the premise of `r`, read
on the LIR type. At a `[let]`'s abort, `CDerives.effLet`'s `hW : S.Weak → Γ₂.Drops`: each slot
of `N`'s context is at a `VTy.Drop` type, which `LTy.drops` reads (`ofV_drops`), an opaque value
among them. At `⊤`, `CDerives.topI`, which has no premise: `⊤` absorbs its whole context at every
type. A raise's payload superseded by a finaliser's: `CDerives.effRaise`'s `hd : o.A.Drop`,
`LTy.drops` again. No other rule discards an opaque value: no constant forgets it and it has no
destructor. -/
def abandonable : Abandon → LTy → Bool
  | .letAbort, t | .superseded, t => t.drops
  | .top, _ => true

/-- A slot a split duplicates (`Ctx.SplitP.dup`: of persistent type) is `copyable` at its LIR
type. -/
theorem copyable_ofV {ms : MachSet} {A : VTy} {t : LTy} (hA : A.persistent = true)
    (h : ofV ms A = .ok t) : copiesAt .dup t = true := by
  simp [copiesAt, ofV_persistent hA h]

/-- A slot a leaf drops (`Ctx.DeadP.drop`: of persistent type) is `droppable` at its LIR type. -/
theorem droppable_ofV_persistent {ms : MachSet} {A : VTy} {t : LTy}
    (hA : A.persistent = true) (h : ofV ms A = .ok t) : dropsAt .dead t = true := by
  simp [dropsAt, ofV_persistent hA h]

/-- A slot an abort abandons (`Ctx.Drops`: of a `VTy.OwnFree` type) is `abandonable` at its LIR
type. -/
theorem abandonable_ofV_drop {ms : MachSet} {A : VTy} {t : LTy} (hA : A.OwnFree)
    (h : ofV ms A = .ok t) : abandonable .letAbort t = true := by
  simp [abandonable, ofV_drops hA h]

/-- The variables left after `t`, its value consumed by its context. -/
def lintTm (w : String) (p : Prog) (inDtor : Bool) : Nat → Std.HashSet Var → Tm → LM Left
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
    | .app0 g => return some (← use w env g)
    -- `⊤` has no elimination: a `&` whose second component is `⊤` (a must-resume `κ`'s cancel,
    -- `kTy`) is never observed at it.
    | .sel g j => do
      if j == 1 then
        if let some t := p.ty[g]? then
          if let .thunk (.amp _ .top) := t.peel then
            bad w s!"x{g} observed at `⊤` (its type {t}), which has no elimination"
      return some (← use w env g)
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
      match ← lintTm w p inDtor f env e with
      | none => return none
      | some env' => lintTm w p inDtor f (← bindNew w p env' x) b
    | .letpair x y q b => do
      let env ← use w env q
      let env ← bindNew w p env x
      lintTm w p inDtor f (← bindNew w p env y) b
    | .case sv x b₁ y b₂ => do
      let env ← use w env sv
      let l₁ ← lintTm w p inDtor f (← bindNew w p env x) b₁
      let l₂ ← lintTm w p inDtor f (← bindNew w p env y) b₂
      match l₁, l₂ with
      | none, l | l, none => return l
      | some a, some b =>
        if !sameSet a b then
          bad w s!"the arms of a case on x{sv} consume different variables: {a.toList.filter (!b.contains ·)} / {b.toList.filter (!a.contains ·)}"
        return some a
    | .absurd sv => do let _ ← use w env sv; return none
    | .copy r x x' b => do
      if !env.contains x then bad w s!"x{x} copied when it is not owned"
      match p.ty[x]? with
      | some t =>
        if !copiesAt r t then bad w s!"x{x} copied at {t} ({r.name}), where the rule's premise does not hold"
      | none => bad w s!"x{x} has no type"
      lintTm w p inDtor f (← bindNew w p env x') b
    | .drop r x b => do
      match p.ty[x]? with
      | some t =>
        if !dropsAt r t then
          bad w s!"x{x} dropped at {t} ({r.name}), where the rule's premise does not hold"
        if r == .stackK then
          if let some e := handsOver p x b then bad w s!"x{x} dropped at the rule stack k: {e}"
        if r == .dtor && !inDtor then
          bad w s!"x{x} dropped at the rule dtor outside a destructor function"
      | none => bad w s!"x{x} has no type"
      lintTm w p inDtor f (← use w env x) b
    | .abandon r x b => do
      match p.ty[x]? with
      | some t =>
        if !abandonable r t then
          bad w s!"x{x} abandoned at {t} ({r.name}), where the rule's premise does not hold"
      | none => bad w s!"x{x} has no type"
      lintTm w p inDtor f (← use w env x) b

/-- Lint a program. -/
def lint (p : Prog) : Except String Unit := do
  let act : LM Unit := do
    for (d, i) in p.fns.toList.zipIdx do
      let w := s!"f{i} ({d.name})"
      let mut env : Std.HashSet Var := {}
      for x in d.params do env ← bindNew w p env x
      match ← lintTm w p (p.dtorFns.contains i) (1 <<< 22) env d.body with
      | some rest => if !rest.isEmpty then bad w s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
      | none => pure ()
    match ← lintTm "main" p false (1 <<< 22) {} p.main with
    | some rest => if !rest.isEmpty then bad "main" s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
    | none => pure ()
  let _ ← act.run {}

end Backend2.Lint
