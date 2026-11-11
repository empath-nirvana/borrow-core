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
- the typed checks of "The shapes of the values" below, on the LIR types (`Prog.ty`, `Fn.ret`,
  `Prog.mainTy`, a code's type, the frame and region declarations): each eliminator's operand, each
  builder's and literal's type, each call's arguments and answer, each closure against its code,
  each primitive's operands and answer (`primBad`), and each copy's binder; what they leave
  unchecked is listed there;
- every `lend` answers a borrow of its kind: `mut` or `imm` (`Op.lend`, SPEC §57);
- every `slotPop` is of an owned array and answers that family and its slot's contents
  (`slotPopBad`, SPEC §77);
- every `copy` meets the premise of the rule the node carries (`copiesAt`): `Ctx.SplitP.dup` at a
  persistent type, `!` read off the LIR type (`Types.ofV` keeps it); the `copy` constants and
  `copy_derives` at an `imm` borrow;
- every `consume` meets the premise of the rule the node carries (`consumesAt`), a `consume` one only in a
  consume function (`Prog.consumeFns`), a `stackK` one only as a stack machine's hand-over, its
  premise read from the node (`handsOver`); no rule consumes a type owning an opaque value;
- no `&` is observed at a `⊤` component (`⊤` has no elimination);
- a function's lend bits (`Fn.lendEncl`, SPEC §50) are none, or one per parameter;
- every `abandon` meets the premise of the rule the node carries (`abandonable`): at a `[let]`'s
  abort, `effLet`'s `hW` (the variable's type holds no owned cell, `VTy.Consume`); at a superseded
  raise payload, `effRaise`'s `hd`, the same; at `⊤`, `topI`'s, which has none. It is the only
  node at which an opaque value is discarded, and `Convert` emits it only at those rules' sites.
-/

namespace Backend2.Lint
open Backend2 BoCa.Fig16.LogRel.Core

/-- What a path leaves unconsumed; `none` on a path that ends at `absurd` (or `unreachable`), which
never returns: a variable still owned there needs no consume. It is how `absurd` (`zeroE`) absorbs
the slots its value does not read (`Convert.splitCtx`, SPEC §66). -/
abbrev Left := Option (Std.HashSet Var)

structure St where
  bound : Std.HashSet Var := {}
  /-- The function being linted is a harness extern's (`Prog.hostFns`). -/
  host : Bool := false

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

/-- **A consume at the rule `r`**, its premise read on the LIR type:
- `dead` (`Ctx.DeadP.weaken`, `Ctx.SoloP.skip`): an unrestricted type;
- `release` (the `release` constants, `arrRelease`): `Imm`, `Mut`, `Unk`, `[Imm A]`;
- `consume` (`consumeSlot_derives`): only in a consume function (`Prog.consumeFns`, checked by `lintTm`), a
  leaf the consume releases: an unrestricted type, a borrow, `Unk`, or a family of borrows
  (`Consumable.arrayMut` at `[Mut A]`: `consumeAt` is `idx` then `forget`);
- `unused`: an unrestricted type, the premise of the weakening the part that receives the slot
  applies at its leaves (`Ctx.DeadP.weaken`); a persistent value holds no resource
  (`vP_empty_of_persistent`), so consuming it at the split is the same. The absorbing nodes do not
  reach this rule: at `absurd` (`zeroE`) a slot neither mask holds is left unconsumed on a path
  that ends at `Tm.absurd`, which `lintTm` admits (`Left` is `none` there), and `⊤` (`topI`)
  abandons its context (`Abandon.top`). That no other rule leaves a slot of a type that is not
  persistent in neither part is `UNPROVED:` (`Check.SplitMasks.NeitherAbsorbed` states the cases);
  such a consume is refused here.  [spec §66]
- `stackK` (`UNPROVED:`, F3, `StackKHandOver`): a closure of a `&` code, the rest of its
  premise read from the node (`handsOver`, checked by `lintTm`).
No rule consumes a value that owns an opaque value: an abort abandons it (`abandon`). -/
def consumesAt : ConsumeRule → LTy → Bool
  | .dead, t => t.persistent
  | .release, t => match t.unbang with
    | .imm _ | .mut _ | .unk | .fam (.imm _) => true
    | _ => false
  | .consume, t => t.persistent || match t.unbang with
    | .imm _ | .mut _ | .unk | .fam (.imm _) | .fam (.mut _) => true
    | _ => false
  | .unused, t => t.persistent
  | .stackK, t => match t with
    | .thunk (.amp _ _) => true
    | _ => false

/-- **A `stackK` consume's premise, read from the node**: the stack machine's hand-over of `x`, a
level's suspended computation, to the `k` the consume's body binds first, `let k₂ = clos kc [base]`:
`x` and `k₂` are both of `kc`'s closure type, and `base` is a frame's address (`LTy.addr`). The
check that `kc` is a `&` code each of whose functions takes one address is not part of the rule's
premise: it confines the rule to codes of a stack machine's shape (a resume and a cancel entry
over a base), so that the assertion is not taken at any other closure. What the node cannot show,
that `x` is `clos kc [a]` with `base` at or below `a` on the task stack and the frames from the
top down to `a` written, is `UNPROVED:` (`Backend2.StackKHandOver`); the LIR interpreter checks it
on every run (`Backend2.handOverB`). `none` when the premise holds, else what fails. -/
def handsOver (p : Prog) (x : Var) : Tm → Option String
  | .letv k₂ (.clos kc [base]) _ => Id.run do
    let some code := p.codes[kc]? | return some s!"no code c{kc}"
    if code.kind != .amp then return some s!"c{kc}, the code of the k it hands over to, is not a `&` code"
    for fn in code.fns do
      let some d := p.fns[fn]? | return some s!"no function f{fn}"
      unless d.params.length == 1 && d.params.all (p.ty[·]? == some LTy.addr) do
        return some s!"f{fn} ({d.name}), an entry of c{kc}, does not take one address"
    let kT := LTy.thunk code.ty
    if p.ty[x]? != some kT then return some s!"x{x} is not of c{kc}'s closure type"
    if p.ty[k₂]? != some kT then return some s!"x{k₂}, the k it hands over to, is not of c{kc}'s closure type"
    if p.ty[base]? != some LTy.addr then return some s!"x{base}, the base, is not an address"
    return none
  | _ => some "its body does not first bind the k it hands over to, `clos kc [base]`"

/-- A type whose values an `abandon` node at the rule `r` may discard: the premise of `r`, read
on the LIR type. At a `[let]`'s abort, `CDerives.effLet`'s `hW : S.Weak → Γ₂.Consumes`: each slot
of `N`'s context is at a `VTy.Consume` type, which `LTy.consumes` reads (`ofV_consumes`), an opaque value
among them. At `⊤`, `CDerives.topI`, which has no premise: `⊤` absorbs its whole context at every
type. A raise's payload superseded by a finaliser's: `CDerives.effRaise`'s `hd : o.A.Consume`,
`LTy.consumes` again. No other rule discards an opaque value: no constant discards it and it has no
consume. -/
def abandonable : Abandon → LTy → Bool
  | .letAbort, t | .superseded, t => t.consumes
  | .top, _ => true

/-- A slot a split duplicates (`Ctx.SplitP.dup`: of persistent type) is `copyable` at its LIR
type. -/
theorem copyable_ofV {ms : MachSet} {A : VTy} {t : LTy} (hA : A.persistent = true)
    (h : ofV ms A = .ok t) : copiesAt .dup t = true := by
  simp [copiesAt, ofV_persistent hA h]

/-- A slot a leaf consumes (`Ctx.DeadP.weaken`: of persistent type) is `weakenable` at its LIR type. -/
theorem weakenable_ofV_persistent {ms : MachSet} {A : VTy} {t : LTy}
    (hA : A.persistent = true) (h : ofV ms A = .ok t) : consumesAt .dead t = true := by
  simp [consumesAt, ofV_persistent hA h]

/-- A slot an abort abandons (`Ctx.Consumes`: of a `VTy.OwnFree` type) is `abandonable` at its LIR
type. -/
theorem abandonable_ofV_consume {ms : MachSet} {A : VTy} {t : LTy} (hA : A.OwnFree)
    (h : ofV ms A = .ok t) : abandonable .letAbort t = true := by
  simp [abandonable, ofV_consumes hA h]

/-- **A `slotPop`'s premise, read on the LIR types** (`none` when it holds): one operand, an owned
array `[Ref c]` (not a family of borrows, whose slots are not the family's to move), and the result
`[Ref c] ⊗ c`, the same family and its slot's contents. The popped contents are then a variable
like any other, consumed once on every path (`lintTm`); the slot leaves the family, so the
family's later `freeArr` cannot meet it written. That the operand's length is at least one is the
code's test before the op (`genConsumeW`), checked on every run by the LIR interpreter.  `[spec §77]` -/
def slotPopTyBad (a r : LTy) : Option String :=
  match a.peel, r.peel with
  | .fam (.ref c), .pair f c' =>
    if !f.sameRep (.fam (.ref c)) then some s!"answers the family {f}, not its operand's"
    else if !c'.sameRep c then some s!"answers contents {c'} for slots of {c}"
    else none
  | .fam (.ref c), t => some s!"answers {t}, not a pair of the family and its slot's contents {c}"
  | t, _ => some s!"of {t}, which is not an owned array"

/-- `slotPopTyBad` at a `letv`'s variable `x`. -/
def slotPopBad (p : Prog) (x : Var) : List Var → Option String
  | [a] =>
    match p.ty[a]?, p.ty[x]? with
    | some t, some r => slotPopTyBad t r
    | some t, none => slotPopTyBad t .unit
    | none, _ => some s!"of x{a}, which has no type"
  | as => some s!"on {as.length} operands"

/-! ### The shapes of the values, read on the LIR types

 A variable's type is `Prog.ty`, the
type `Types.ofV` gave it from the checked term; a term's expected type is the type of the variable
a `letv` binds it to, a function's `Fn.ret`, or `Prog.mainTy`, passed down through the tails of
`letv`, `letpair`, `case` and the other binding nodes. A type's shape is read through its
top-level `!`s (`LTy.peel`: `!A` is represented as an `A`). The checks, each `none` when it holds:
- a `letpair` takes apart a pair, binding its two components at their types;
- a `case` takes apart a sum, binding each arm's variable at its summand's type; an `absurd`, a `0`;
- a `pair` is built at a pair type from its components, an `inj` at a sum type from the summand
  it injects, a `()` at `1`;
- a variable answered at a tail, and a direct `call`, have the type the term is expected at.
Types are compared as representations (`sameTy`: up to `!`, and a `ν` read as its unrolling).
A variable with no type is refused where it is bound (`bindNew`); the expected type of a `letv`'s
value is then `none` only on a program that is refused there.

The calls, the closures, the literals, the primitives and the copies are checked on the types
too (below: `callBad`, `codeBad`, `litTy`, `primBad`, `primAt`; a copy's binder at its source's
type in `lintTm`).

**Not checked.** The LIR erases lifetimes, so no borrow's lifetime or outlives relation is read
(only its mode, `imm` or `mut`). An `alloc`'s width class (`Op.alloc`'s `cls`, a layout fact, not a
type). A `divLit`'s operation against its operands' width (a byte's division is at `w32`). A `tab`
loop's index and bound parameters (only the closure it takes, the array it fills and its answer).
Which mode a `relend` answers (either). Which stack a `κ` access or a frame is of, and the static
register a stack operation names: a handle is checked an address, no more; a stack machine's
hand-over is `UNPROVED:` (`handsOver`). The I/O operations are checked at the externs' types of
`lib/wasi.bc`, written here, not read from the program. A family's leaf at `emptyFam`. An
`unreachable`'s operands and answer, and a value's range (an index in bounds, a length below
`2³¹`): the code's tests, checked on every run by the LIR interpreter. -/

/-- `x` and its type, for a message. -/
def tyStr (p : Prog) (x : Var) : String :=
  match p.ty[x]? with
  | some t => s!"x{x} : {t}"
  | none => s!"x{x} (no type)"

mutual
/-- **Two types of one representation, a `ν` read as its unrolling**: `sameRep` (equal up to
`!`), or of one former whose parts are, a closure type compared after its `ν`s are unrolled
(`LCTy.whnf`). No node rolls or unrolls a `ν` (an observation reads the unrolling, as `Convert`
does), so a closure of `νX. C` is one of `C[U(νX. C)/X]`; a `μ` is rolled by `Op.roll`, and is
compared as written. `false` when the fuel runs out. -/
def sameTy : Nat → LTy → LTy → Bool
  | 0, a, b => a.sameRep b
  | f + 1, a, b => a.sameRep b || match a.peel, b.peel with
    | .pair a b, .pair c d | .sum a b, .sum c d => sameTy f a c && sameTy f b d
    | .ref a, .ref b | .imm a, .imm b | .mut a, .mut b | .fam a, .fam b => sameTy f a b
    | .thunk k, .thunk k' => sameCTy f (k.whnf 8) (k'.whnf 8)
    | _, _ => false
/-- `sameTy` at closure types. -/
def sameCTy : Nat → LCTy → LCTy → Bool
  | 0, k, k' => k.sameRep k'
  | f + 1, k, k' => k.sameRep k' || match k.whnf 8, k'.whnf 8 with
    | .ret a, .ret b => sameTy f a b
    | .arr a k, .arr b k' => sameTy f a b && sameCTy f k k'
    | .amp k₁ k₂, .amp k₁' k₂' => sameCTy f k₁ k₁' && sameCTy f k₂ k₂'
    | .top, .top => true
    | _, _ => false
end

/-- `x` has a type of the representation of `t` (`sameTy`). -/
def hasRep (p : Prog) (x : Var) (t : LTy) : Bool :=
  match p.ty[x]? with
  | some u => sameTy 64 u t
  | none => false

/-- The type of a literal. -/
def litTy : BoCa.IntLit → LTy
  | .i32 _ => .int .w32
  | .i64 _ => .int .w64
  | .u8 _ => .int .w8
  | .f32 _ => .int .f32
  | .f64 _ => .int .f64
  | .u32 _ => .int .u32
  | .u64 _ => .int .u64

/-- An eliminator's premise: what it takes apart is of the shape it eliminates, and the
variables it binds are at the component types. -/
def elimBad (p : Prog) : Tm → Option String
  | .letpair x y q _ =>
    match p.ty[q]?.map LTy.peel with
    | some (.pair a b) =>
      if !hasRep p x a then some s!"a letpair binds {tyStr p x} for the component {a} of x{q}"
      else if !hasRep p y b then some s!"a letpair binds {tyStr p y} for the component {b} of x{q}"
      else none
    | _ => some s!"a letpair takes apart {tyStr p q}, which is not a pair"
  | .case sv x _ y _ =>
    match p.ty[sv]?.map LTy.peel with
    | some (.sum a b) =>
      if !hasRep p x a then some s!"a case binds {tyStr p x} for the summand {a} of x{sv}"
      else if !hasRep p y b then some s!"a case binds {tyStr p y} for the summand {b} of x{sv}"
      else none
    | _ => some s!"a case takes apart {tyStr p sv}, which is not a sum"
  | .absurd sv =>
    match p.ty[sv]?.map LTy.peel with
    | some .zero => none
    | _ => some s!"an absurd of {tyStr p sv}, which is not 0"
  | _ => none

/-- A value's premise at the type `t` it is expected at: a `pair` at a pair type of its
components', an `inj` at a sum type of its summand's, `()` at `1`, a variable or a direct call's
answer at `t` itself. -/
def introBad (p : Prog) (t : LTy) : Tm → Option String
  | .pair a b =>
    match t.peel with
    | .pair ta tb =>
      if !hasRep p a ta then some s!"a pair at {t} of {tyStr p a}"
      else if !hasRep p b tb then some s!"a pair at {t} of {tyStr p b}"
      else none
    | _ => some s!"a pair of x{a} and x{b} at {t}, which is not a pair type"
  | .inj r a =>
    match t.peel with
    | .sum ta tb =>
      if !hasRep p a (if r then tb else ta) then
        some s!"an {if r then "inr" else "inl"} at {t} of {tyStr p a}"
      else none
    | _ => some s!"an {if r then "inr" else "inl"} of x{a} at {t}, which is not a sum type"
  | .unit => if t.peel == .unit then none else some s!"a () at {t}"
  | .var x => if hasRep p x t then none else some s!"{tyStr p x} answered at {t}"
  | .lit c => if sameTy 64 (litTy c) t then none else some s!"a literal of {litTy c} at {t}"
  | .call fn _ =>
    match p.fns[fn]? with
    | some d => if sameTy 64 d.ret t then none else some s!"f{fn} ({d.name}), answering {d.ret}, called at {t}"
    | none => none
  | _ => none

/-! ### The calls, the closures and the primitives, read on the LIR types -/

/-- What running a computation of type `c` answers (`Convert.answerOf`): `B` at `F B`, `1` at `⊤`,
else a closure of the rest. -/
def answerTy (c : LCTy) : LTy :=
  match c.whnf 8 with
  | .ret a => a
  | .top => .unit
  | k => .thunk k

/-- A closure's computation type, `ν`s unrolled: `none` when `t` is not a closure type. -/
def closTy? (t : LTy) : Option LCTy :=
  match t.peel with
  | .thunk k => some (k.whnf 8)
  | _ => none

/-- The arguments `as` at the parameters `ps`, each of its parameter's type. -/
def argsBad (p : Prog) (what : String) (as ps : List Var) : Option String :=
  (as.zip ps).findSome? fun (a, x) =>
    match p.ty[x]? with
    | some t => if hasRep p a t then none else some s!"{what}: {tyStr p a} for the parameter x{x} : {t}"
    | none => some s!"{what}: the parameter x{x} has no type"

/-- **A call's or a closure's premise** (`none` when it holds), the term's answer at `r`:
- `call fn as`: each argument at its parameter's type (the answer is `introBad`'s);
- `app g a`: `g` a closure of `A ⊸ C`, `a` an `A`, the answer `C`'s (`answerTy`);
- `app0 g`: `g` a closure of `F B`, the answer `B`;
- `sel g j`: `g` a closure of `C₀ & C₁`, the answer `Cⱼ`'s;
- `clos c xs`: at `U K` for `K` the code's type, each captured value at its function's
  environment parameter's type. -/
def callBad (p : Prog) (r : Option LTy) : Tm → Option String
  | .call fn as =>
    match p.fns[fn]? with
    | some d => argsBad p s!"f{fn} ({d.name}) called" as d.params
    | none => none
  | .app g a =>
    match closTy? (p.ty[g]?.getD .unit) with
    | some (.arr aT c) =>
      if !hasRep p a aT then some s!"x{g} applied to {tyStr p a}, for an argument of {aT}"
      else ansBad s!"x{g} applied" (answerTy c)
    | _ => some s!"{tyStr p g} applied to x{a}: not a closure of a function type"
  | .app0 g =>
    match closTy? (p.ty[g]?.getD .unit) with
    | some (.ret b) => ansBad s!"x{g} run" b
    | _ => some s!"{tyStr p g} run: not a closure of a returner type"
  | .sel g j =>
    match closTy? (p.ty[g]?.getD .unit) with
    | some (.amp k₀ k₁) =>
      if j ≥ 2 then some s!"x{g} observed at {j}: a `&` has two components"
      else ansBad s!"x{g} observed at {j}" (answerTy (if j == 0 then k₀ else k₁))
    | _ => some s!"{tyStr p g} observed at {j}: not a closure of a `&` type"
  | .clos c xs =>
    match p.codes[c]? with
    | some code =>
      let envBad := code.fns.findSome? fun fn =>
        match p.fns[fn]? with
        | some d => argsBad p s!"c{c}'s closure captures" xs (d.params.take xs.length)
        | none => none
      match envBad with
      | some e => some e
      | none =>
        match r with
        | some t =>
          if sameTy 64 t (.thunk code.ty) then none
          else some s!"a closure of c{c}, of {LTy.thunk code.ty}, at {t}"
        | none => none
    | none => none
  | _ => none
where
  ansBad (what : String) (b : LTy) : Option String :=
    match r with
    | some t => if sameTy 64 b t then none else some s!"{what} answers {b}, at {t}"
    | none => none

/-- **A code's functions at its closure type** (`none` when they are): a `lam` code of `A ⊸ C`,
its function's last parameter an `A` and its answer `C`'s (`answerTy`); a `unit` code of `F B`,
answering `B`; a `&` code of `C₀ & C₁`, its two functions answering `C₀`'s and `C₁`'s. A `clos`
of the code is then a closure of the code's type (`callBad`). -/
def codeBad (p : Prog) (c : Nat) (code : Code) : Option String :=
  let fnAt (fn : Nat) : Option Fn := p.fns[fn]?
  let ans (fn : Nat) (b : LTy) : Option String :=
    match fnAt fn with
    | some d => if sameTy 64 d.ret b then none else some s!"c{c}: f{fn} ({d.name}) answers {d.ret}, for {b}"
    | none => some s!"c{c}: no function f{fn}"
  match code.kind, code.ty.whnf 8, code.fns with
  | .lam, .arr a k, [fn] =>
    match fnAt fn with
    | some d =>
      match d.params.getLast? >>= (p.ty[·]?) with
      | some t => if sameTy 64 t a then ans fn (answerTy k) else some s!"c{c}: f{fn} ({d.name}) takes {t}, for {a}"
      | none => some s!"c{c}: f{fn} ({d.name}) takes no typed argument"
    | none => some s!"c{c}: no function f{fn}"
  | .unit, .ret b, [fn] => ans fn b
  | .amp, .amp k₀ k₁, [f₀, f₁] => (ans f₀ (answerTy k₀)).orElse fun _ => ans f₁ (answerTy k₁)
  | _, k, fns => some s!"c{c}: a {reprStr code.kind} code of {fns.length} functions at {LTy.thunk k}"

/-- **`d` is the contents `c` read through `Imm̲`** (`load`), clause by clause Core's `immG`
(`Core/Types.lean`), on the LIR types (`ofV`: no `box`, `Tok` a cell of `1`):
- `1` and `0` read as themselves; `⊗` and `⊕` componentwise;
- a closure (`thunk`, `code`) reads as `Unk`, and as nothing else;
- `Ref A`, `Imm A` and `Mut A` read as `Imm A`; `Tok`'s cell, `Ref 1` here, also as `Unk`
  (`Imm̲ 'b Tok = Unk`);
- `!A` reads as itself (up to `sameTy`): a persistent value is copied out whole;
- a family componentwise; `Unk` as `Unk`; a word as itself; a type variable as itself;
- an opaque value reads as `Unk`, and as nothing else;
- `μX. A` as a `μ` of `A` read, or through its unrolling, where `immG`'s payload substitution makes
  a recursive pointer a shared borrow of the `μ` itself. -/
def readAs : Nat → LTy → LTy → Bool
  | 0, c, d => sameTy 64 c d
  | f + 1, c, d => match c with
    | .bang _ => sameTy 64 c d
    | _ => match c, d.peel with
      | .unit, .unit | .zero, .zero => true
      | .pair a b, .pair a' b' | .sum a b, .sum a' b' => readAs f a a' && readAs f b b'
      | .thunk _, .unk => true
      | .ref a, .imm a' | .imm a, .imm a' | .mut a, .imm a' => sameTy 64 a a'
      | .ref a, .unk => a.peel == .unit
      | .fam a, .fam a' => readAs f a a'
      | .unk, .unk => true
      | .int w, .int w' => w == w'
      | .opq _, .unk => true
      | .tvar n, .tvar n' => n == n'
      | .mu a, .mu a' => readAs f a a' || readAs f a.unrollMu a'.unrollMu
      | _, _ => false

/-- A cell of contents `c` holds a value of type `v`: `c` itself, or, at an opaque type and in a
harness extern's function (`host`: `Prog.hostFns`, `Convert.mkClosOf`, `takeClosOf`), the
host's word for it: a stream's descriptor (`i32`), a clock's time (`i64`). -/
def holds (host : Bool) (c v : LTy) : Bool :=
  sameTy 64 c v || host && match c.peel, v.peel with
    | .opq .input, .int .w32 | .opq .output, .int .w32 | .opq .args, .int .w32 => true
    | .opq .clock, .int .w64 => true
    | _, _ => false

/-- `t` is an integer type, not a float. -/
def isWord (t : LTy) : Bool := match t.peel with
  | .int .f32 | .int .f64 => false
  | .int _ => true
  | _ => false

/-- A family's leaf: its mode (`ref`, `imm` or `mut`) and contents. -/
def famLeaf (t : LTy) : Option (String × LTy) :=
  match t.peel with
  | .fam l => match l.peel with
    | .ref c => some ("ref", c)
    | .imm c => some ("imm", c)
    | .mut c => some ("mut", c)
    | _ => none
  | _ => none

/-- A cell type's contents: `ref C`, `imm C` or `mut C`. -/
def cellC? (t : LTy) : Option LTy :=
  match t.peel with
  | .ref c | .imm c | .mut c => some c
  | _ => none

/-- A family's slot contents: `[ref C]`, `[imm C]` or `[mut C]`. -/
def famC? (t : LTy) : Option LTy :=
  match t.peel with
  | .fam l => cellC? l
  | _ => none

/-- **A primitive's premise, read on the LIR types**: its operands' types `ts` (in order) and its
answer's `r`, as the LIR interpreter (`Interp.evalOp`) and the layout (`Layout.walk`) read them.
`none` when it holds. A frame's and a `κ` region's contents are checked against the program's
declarations (`Prog.frameTys`, `Prog.regionTys`) by `primAt`. -/
def primBad (p : Prog) (host : Bool) (op : Op) (ts : List LTy) (r : LTy) : Option String :=
  let eq := sameTy 64
  let i32 (t : LTy) : Bool := eq t (.int .w32)
  let wrong (what : String) : Option String :=
    some s!"{reprStr op |>.replace "\n" " "} on {ts} answering {r}: {what}"
  let need (b : Bool) (what : String) : Option String := if b then none else wrong what
  -- The leaf of a family: `ref`, `imm` or `mut` (`famLeaf`), each row admitting the modes its
  -- Core constants take.
  let famIs (modes : List String) (t : LTy) : Bool :=
    match famLeaf t with | some (m, _) => modes.contains m | none => false
  match op, ts with
  | .host o, [a] =>
    match ofV {} (hostArg o), ofV {} (hostRes o) with
    | .ok aT, .ok rT => need (eq a aT && eq r rT) s!"the host operation is {aT} -o {rT}"
    | _, _ => wrong "a host operation of no LIR type"
  | .divLit _, [a, d] => need (isWord a && eq a d && eq r a) "a division of two integers of one type"
  | .alloc _, [v] | .allocLent _ _, [v] =>
    need (match r.peel with | .ref c => holds host c v | _ => false) "a cell of the argument"
  | .free, [x] => need (match x.peel with | .ref c => holds host c r | _ => false) "an owned cell's contents"
  | .release, [x] => need ((match x.peel with | .ref _ => true | _ => false) && r.peel == .unit)
      "an owned cell released, answering ()"
  | .swap, [x, v] =>
    need (match x.peel, r.peel with
      | .ref c, .pair (.ref v') c' => eq v v' && eq c c' | _, _ => false)
      "an owned cell and its new contents, answering the cell, now of the new contents' type, and the old contents"
  | .lend m, [x] =>
    let b (c : LTy) : LTy := if m then .mut c else .imm c
    need (match x.peel, r.peel with
      | .ref c, .pair x' bT => eq x x' && eq bT (b c)
      | .fam (.ref c), .pair x' bT => eq x x' && eq bT (.fam (b c))
      | _, _ => false) "an owned cell or array, answering it and its borrow"
  | .relend, [x] =>
    need (match x.peel, r.peel with
      | .mut c, .pair x' bT => eq x x' && (eq bT (.mut c) || eq bT (.imm c))
      | .fam (.mut c), .pair x' bT => eq x x' && (eq bT (.fam (.mut c)) || eq bT (.fam (.imm c)))
      | _, _ => false) "a `mut` borrow, answering it and a borrow of its contents"
  | .load, [b] => need (match cellC? b with | some c => readAs 64 c r | none => false)
      "a borrow's contents read through Imm"
  | .take, [b] =>
    need (match b.peel, r.peel with
      | .mut c, .pair b' c' | .ref c, .pair b' c' => eq b b' && eq c c' | _, _ => false)
      "a `mut` borrow or an owned cell, answering it and its contents"
  | .put, [b, v] =>
    need (match b.peel with | .mut c | .ref c => eq c v && eq r b | _ => false)
      "a `mut` borrow or an owned cell and its contents, answering it"
  | .newArr, [n] => need (i32 n && famIs ["ref"] r) "an i32 length, answering an owned array"
  | .tab fi, [f, n] | .tabLit fi, [f, n] =>
    match p.fns[fi]? with
    | some d =>
      match d.params.map (p.ty[·]?) with
      | [some pf, some pa, _, _] =>
        need (i32 n && famIs ["ref"] r && eq f pf && eq r pa && eq d.ret r)
          s!"an owned array filled by its loop f{fi} ({d.name}), which takes {pf} and fills {pa}"
      | _ => wrong s!"its loop f{fi} does not take four typed parameters"
    | none => wrong s!"no function f{fi}"
  -- `slotPut`, `slotTake`: the slot loops of an array's tabulation and drain (`genTab`,
  -- `genArrFree`, a consume's), at an owned array or a family of `mut` borrows.
  | .slotPut, [a, i, v] =>
    need (i32 i && famIs ["ref", "mut"] a && eq r a && (match famLeaf a with
      | some (_, c) => eq c v | none => false))
      "an owned or `mut` family, an i32 index and a slot's contents, answering the family"
  | .slotTake, [a, i] =>
    need (i32 i && famIs ["ref", "mut"] a && (match famLeaf a, r.peel with
      | some (_, c), .pair a' c' => eq a a' && eq c c' | _, _ => false))
      "an owned or `mut` family and an i32 index, answering it and the slot's contents"
  | .slotPop, [a] => (slotPopTyBad a r).bind wrong
  | .freeArr, [a] => need (famIs ["ref"] a && r.peel == .unit) "an owned array, answering ()"
  -- `size`: `arr_size` (`[Ref A]`), `slice_len_mut` (`[Mut A]`).
  | .size, [v] =>
    need (famIs ["ref", "mut"] v && (match r.peel with
      | .pair v' n => eq v v' && i32 n | _ => false))
      "an owned or `mut` family, answering it and its i32 length"
  -- `len`: `arr_len` (`[Imm A]`).
  | .len, [v] => need (famIs ["imm"] v && i32 r) "an `imm` family, answering its i32 length"
  -- `idx`: `arr_get` (`[Imm A]`), `slice_get_mut` (`[Mut A]`): a borrow of the slot or `()`.
  | .idx _, [v, i] =>
    need (i32 i && famIs ["imm", "mut"] v && (match v.peel, r.peel with
      | .fam l, .sum l' u => eq l l' && u.peel == .unit | _, _ => false))
      "an `imm` or `mut` family and an i32 index, answering a leaf or ()"
  -- `split`: `slice_split_imm`, `slice_split_mut`: never an owned array into owned halves.
  | .split _, [v, i] =>
    need (i32 i && famIs ["imm", "mut"] v && (match r.peel with
      | .sum (.pair a b) c => eq v a && eq v b && eq v c | _ => false))
      "an `imm` or `mut` family and an i32 index, answering its two parts or itself"
  | .emptyFam, [] => need (famLeaf r).isSome "answering a family"
  -- `replace`: `arr_replace` (`[Ref A]`), `slice_replace_mut` (`[Mut A]`).
  | .replace, [v, i, x] =>
    need (i32 i && famIs ["ref", "mut"] v && (match famLeaf v, r.peel with
      | some (_, c), .pair v' (.sum o x') => eq c x && eq v v' && eq o c && eq x' c | _, _ => false))
      "an owned or `mut` family, an i32 index and a slot's contents, answering the family and the old contents or the new"
  -- `swapSlots`: `slice_swap_mut` (`[Mut A]`).
  | .swapSlots, [v, i, j] =>
    need (i32 i && i32 j && eq r v && famIs ["mut"] v)
      "a `mut` family and two i32 indices, answering the family"
  | .roll, [v] => need (match r.peel with | .mu a => eq v a.unrollMu | _ => false)
      "a value of the unrolling, answering the μ"
  | .unroll, [v] => need (match v.peel with | .mu a => eq r a.unrollMu | _ => false)
      "a μ, answering its unrolling"
  | .litByte, [o, n, i] => need (i32 o && i32 n && i32 i && eq r (.int .w8))
      "an i32 offset, length and index, answering a byte"
  | .clampLen, [c] => need (i32 c && i32 r) "an i32 length, answering an i32"
  | .cntLt, [i, n] => need (i32 i && i32 n && eq r (.sum .unit .unit))
      "an i32 index and its bound, answering a test"
  | .cntSucc, [i] | .cntPred, [i] => need (i32 i && i32 r) "an i32 count, answering an i32"
  | .stackSwap _, [h] => need (eq h LTy.addr && eq r LTy.addr) "a stack, answering a stack"
  | .stackFree, [h] => need (eq h LTy.addr && r.peel == .unit) "a stack, answering ()"
  | .stackNew _, [] => need (eq r LTy.addr) "answering a stack"
  | .kappaPut _, [h, _] => need (eq h LTy.addr && r.peel == .unit) "a stack and a value, answering ()"
  | .kappaTake _, [h] => need (eq h LTy.addr && (match r.peel with
      | .pair h' _ => eq h h' | _ => false)) "a stack, answering it and its region's contents"
  | .framePush _ _, [] | .frameTop _ _, [] =>
    need (match r.peel with | .pair (.ref _) a => eq a LTy.addr | _ => false)
      "answering a frame's cell and its address"
  | .framePut, [f, v] => need ((match f.peel with | .ref c => eq c v | _ => false) && r.peel == .unit)
      "a frame's cell and its contents, answering ()"
  | .framePop _, [f] => need ((match f.peel with | .ref _ => true | _ => false) && r.peel == .unit)
      "a frame's cell, answering ()"
  | .io k, [a] => (ioBad k a r).bind wrong
  | .unreachable, _ => none
  | .litView _, _ => wrong "a literal's view, which no conversion makes"
  | _, _ => wrong s!"{ts.length} operands"
where
  /-- An I/O operation's argument and answer, at its extern's type (`lib/wasi.bc`): a `mut` borrow
  of the stream's or the clock's cell, a byte `u8`, the bytes `[Imm u8]` written or `[Mut u8]`
  read into, the count read `i32`, a time `i64`. -/
  ioBad (k : IOKind) (a r : LTy) : Option String :=
    let eq := sameTy 64
    let cap (ks : List Opaque) (m : LTy) : Bool :=
      match m.peel with
      | .mut c => match c.peel with | .opq o => ks.contains o | _ => false
      | _ => false
    let bytes (mode : String) (v : LTy) : Bool :=
      match famLeaf v with
      | some (m, c) => m == mode && eq c (.int .w8)
      | none => false
    let ok : Bool := match k, a.peel, r.peel with
      | .readByte, m, .pair m' (.sum b u) =>
        cap [.input, .args] m && eq m m' && eq b (.int .w8) && u.peel == .unit
      | .writeByte, .pair m b, m' => cap [.output] m && eq m m' && eq b (.int .w8)
      | .writeAll, .pair m v, m' => cap [.output] m && eq m m' && bytes "imm" v
      | .readInto, .pair m v, .pair m' (.pair v' n) =>
        cap [.input] m && eq m m' && bytes "mut" v && eq v v' && eq n (.int .w32)
      | .clockNow, m, .pair m' t => cap [.clock] m && eq m m' && eq t (.int .w64)
      | .clockSleep, .pair m n, m' => cap [.clock] m && eq m m' && eq n (.int .w64)
      | _, _, _ => false
    if ok then none else some s!"not the extern's type"

/-- A primitive's premise (`primBad`), and its frame's or `κ` region's contents at the type its
machine or its site declares (`Prog.frameTys`, `Prog.regionTys`). -/
def primAt (w : String) (p : Prog) (op : Op) (as : List Var) (r : LTy) : LM Unit := do
  let mut ts : List LTy := []
  for a in as do
    let some t := p.ty[a]? | bad w s!"x{a}, an operand, has no type"
    ts := ts ++ [t]
  if let some e := primBad p (← get).host op ts r then bad w e
  let declared (what : String) (d : Option LTy) (c : LTy) : LM Unit := do
    match d with
    | some d => if !sameTy 64 d c then bad w s!"{what} of {c}, declared {d}"
    | none => bad w s!"{what} of {c}, which has no declared type"
  match op, ts, r.peel with
  | .framePush m _, _, .pair (.ref c) _ | .frameTop m _, _, .pair (.ref c) _ =>
    declared s!"a frame of machine {m}" p.frameTys[m]? c
  | .kappaPut s, [_, c], _ | .kappaTake s, _, .pair _ c =>
    declared s!"the κ region of site {s}" p.regionTys[s]? c
  | _, _, _ => pure ()

/-- The variables left after `t`, its value consumed by its context. -/
def lintTm (w : String) (p : Prog) (inConsumeFn : Bool) :
    Nat → Option LTy → Std.HashSet Var → Tm → LM Left
  | 0, _, _, _ => bad w "a term too deep"
  | f + 1, ans, env, t => do
    if let some e := elimBad p t then bad w e
    if let some aT := ans then
      if let some e := introBad p aT t then bad w e
    if let some e := callBad p ans t then bad w e
    if let .prim op as := t then
      if let some r := ans then primAt w p op as r
    match t with
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
          if let some (.amp _ k₁) := closTy? t then
            if k₁.whnf 8 == .top then
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
      if let .prim .slotPop as := e then
        if let some e := slotPopBad p x as then bad w s!"x{x}: a slotPop {e}"
      if let .prim (.lend m) _ := e then
        match p.ty[x]? with
        | some (.pair _ bT) =>
          if borrowMode bT != some m then bad w s!"x{x}: a lend of kind {m} answers a borrow at {bT}"
        | t => bad w s!"x{x}: a lend answers {t.map (·.pp)}"
      match ← lintTm w p inConsumeFn f p.ty[x]? env e with
      | none => return none
      | some env' => lintTm w p inConsumeFn f ans (← bindNew w p env' x) b
    | .letpair x y q b => do
      let env ← use w env q
      let env ← bindNew w p env x
      lintTm w p inConsumeFn f ans (← bindNew w p env y) b
    | .case sv x b₁ y b₂ => do
      let env ← use w env sv
      let l₁ ← lintTm w p inConsumeFn f ans (← bindNew w p env x) b₁
      let l₂ ← lintTm w p inConsumeFn f ans (← bindNew w p env y) b₂
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
      if let (some t, some t') := (p.ty[x]?, p.ty[x']?) then
        if !sameTy 64 t t' then bad w s!"{tyStr p x'} a copy of {tyStr p x}"
      lintTm w p inConsumeFn f ans (← bindNew w p env x') b
    | .consume r x b => do
      match p.ty[x]? with
      | some t =>
        if !consumesAt r t then
          bad w s!"x{x} consumed at {t} ({r.name}), where the rule's premise does not hold"
        if r == .stackK then
          if let some e := handsOver p x b then bad w s!"x{x} consumed at the rule stack k: {e}"
        if r == .consume && !inConsumeFn then
          bad w s!"x{x} consumed at the rule consume outside a consume function"
      | none => bad w s!"x{x} has no type"
      lintTm w p inConsumeFn f ans (← use w env x) b
    | .abandon r x b => do
      match p.ty[x]? with
      | some t =>
        if !abandonable r t then
          bad w s!"x{x} abandoned at {t} ({r.name}), where the rule's premise does not hold"
      | none => bad w s!"x{x} has no type"
      lintTm w p inConsumeFn f ans (← use w env x) b

/-- Lint a program. -/
def lint (p : Prog) : Except String Unit := do
  let act : LM Unit := do
    for (d, i) in p.fns.toList.zipIdx do
      let w := s!"f{i} ({d.name})"
      if !d.lendEncl.isEmpty && d.lendEncl.length != d.params.length then
        bad w s!"{d.lendEncl.length} lend bits for {d.params.length} parameters"
      modify fun s => { s with host := p.hostFns.contains i }
      let mut env : Std.HashSet Var := {}
      for x in d.params do env ← bindNew w p env x
      match ← lintTm w p (p.consumeFns.contains i) (1 <<< 22) (some d.ret) env d.body with
      | some rest => if !rest.isEmpty then bad w s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
      | none => pure ()
    modify fun s => { s with host := false }
    match ← lintTm "main" p false (1 <<< 22) (some p.mainTy) {} p.main with
    | some rest => if !rest.isEmpty then bad "main" s!"ends with {rest.toList.map (s!"x{·}")} unconsumed"
    | none => pure ()
    for (code, c) in p.codes.toList.zipIdx do
      if let some e := codeBad p c code then bad "codes" e
  let _ ← act.run {}

end Backend2.Lint
