import Std.Data.HashMap
import Frontend.Elab.Match
import Frontend.Elab.Subst

/-!
# Frontend — Elab — the instances of effects  `[spec §18, §38]`

An **instance** of an effect is the effect with its type arguments: `Fail[i32]` and
`Fail[ParseError]` are two. The effects pass (`Frontend/Elab/Effects.lean`) resolves each
operation to a handler of its instance and keys every row by instance, so it needs the type
arguments where the types are: an operation's are read off its argument's type, a generic call's
off its arguments' types. This module gives the pass those types. It types every declaration's
body with the typed elaboration's own inference (`TCx.tyV`, `Elab.inferV`) and its matching
(`Frontend/Elab/Match.lean`), before the pass runs, and records at each call:

* an operation of an effect with type parameters: the effect's type arguments, matched from the
  operation's parameter types against the argument's type;
* a call of a template (`fn f[A, …]`): its type arguments, as written or matched from its
  parameter's type against the argument's type.

**At the declaration's own types.** A declaration's type parameters are placeholders while its
body is typed, so the arguments recorded are in its terms (`E`, not what `E` is at a use). The
pass resolves at these types, and the instances of a template are made from the resolved body
(decision 45): instantiation substitutes types into code whose handlers are already chosen, so it
cannot reroute an operation (SPEC §38, *Abstraction safety*).

**Divisions** (SPEC §39). An integer division `a / b` or `a % b` with no answer raises
`Fail[DivError]`: whether it can fail is decided here, at its operands' width as the walk types
them (an operator's result is its operands' width, as the typed elaboration gives it). One that can
fail is recorded at its own span with the instance it raises, `[DivError]` (`divCanFail`); the
effects pass writes it as the checked division and a `raise` at that span (`Elab.Divisions`).

**What is not known.** A type inference cannot synthesize (a literal, whose width its context
decides; an injection; a `with`'s answer) is not recorded: the pass then resolves the operation
to the innermost handler of its effect when every handler of it in scope is one instance, and
otherwise asks for an ascription or a name.
-/

namespace Frontend.Elab.Instances
open Frontend.Check
open BoCa BoCa.Lifetime
open Frontend.Sugar (phBase matchV patOf MatchSt)

/-- A declaration's typing frame: the context `base` with its type parameters `tps` bound to the
placeholders, the `i`-th to `phBase + i`. -/
def frame (base : TCx) (tps : List String) : TCx :=
  { base with E := { base.E with tps := tps.zipIdx.map fun (x, i) => (x, .tvar (phBase + i)) } }

/-- The key of a call in the table: the declaration whose body it is in, and its span. -/
abbrev Key := String × Nat × Nat × Nat × Nat

/-- A declaration's name in the table: its name and where it is declared, since a library's
declarations and the program's are parsed from different files. -/
def ownerKey (name : String) (sp : Span) : String := s!"{name}@{sp.start.line}:{sp.start.col}"

def key (owner : String) (sp : Span) : Key := (owner, sp.start.line, sp.start.col, sp.stop.line, sp.stop.col)

/-- The table: the type arguments recorded at each call, as surface types in the terms of the
declaration the call is in. -/
abbrev Table := Std.HashMap Key (List VTy)

mutual
/-- The type mentions a placeholder. -/
def hasPhV : CVTy → Bool
  | .tvar i => i ≥ phBase
  | .tensor A B | .sum A B => hasPhV A || hasPhV B
  | .thunk C => hasPhC C
  | .ref A | .bang A | .mu A | .fam A | .imm _ A | .mut _ A | .box _ A => hasPhV A
  | _ => false

def hasPhC : CCTy → Bool
  | .ret A => hasPhV A
  | .arr A C => hasPhV A || hasPhC C
  | .amp C D => hasPhC C || hasPhC D
  | .nu C | .all _ _ C => hasPhC C
  | .top => false
  | .eff _ _ _ A B fin C => hasPhV A || hasPhV B || hasPhC fin || hasPhC C
end

/-- A type of the frame of a declaration with type parameters `names`, as surface syntax: each
placeholder is its parameter's name, and a part with none is printed and read back
(`toSurface`). -/
def toSurf (names : List String) : Nat → CVTy → Option VTy
  | 0, _ => none
  | k + 1, A => match A with
    | .tvar i => if i ≥ phBase then (names[i - phBase]?).map (.name .none) else none
    | .unit => some (.unit .none)
    | .zero => some (.zero .none)
    | .tensor A B => do pure (.tensor .none (← toSurf names k A) (← toSurf names k B))
    | .sum A B => do pure (.sum .none (← toSurf names k A) (← toSurf names k B))
    | .bang A => do pure (.bang .none (← toSurf names k A))
    | .ref A => do pure (.ref .none (← toSurf names k A))
    | A => if hasPhV A then none else (toSurface .none A).toOption

/-- The fuel of `toSurf` and of the walk. -/
def fuel : Nat := 1 <<< 16

/-- What the walk knows of the program: each operation of an effect with type parameters, with
the effect's parameters and the operation's parameter types; each template, with its type
parameters and written type. -/
structure Decls where
  ops : List (String × List String × VTy)
  gens : List (String × List String × VTy)

/-- The parameter type of a written function type, under its `!` and lifetimes. -/
def paramTyOf : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramTyOf A
  | .lolli _ P _ | .thunk _ (.arr _ P _) => some P
  | _ => none

/-- The callee of a call as written, with its written type arguments. -/
def callee : Val → Option (String × Option (List VTy))
  | .var _ f | .clone _ f => some (f, none)
  | .defApp _ f As => some (f, some As)
  | .sugar _ (.named _ op) => some (op, none)
  | .inst _ V _ | .unbang _ V => callee V
  | _ => none

/-- The variables a value names outside its computations. -/
def varsV : Nat → Val → List String
  | 0, _ => []
  | k + 1, V => match V with
    | .var _ x | .clone _ x => [x]
    | .lend _ x _ => [x.name]
    | .pair _ V W | .app _ V W => varsV k V ++ varsV k W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => varsV k V
    | _ => []

/-- The error type of an integer division, `lib/arith.bc`'s `DivError`: `inl ()` a zero divisor,
`inr ()` an overflow (SPEC §39). -/
def divErrorTy : VTy := .name .none "DivError"

/-- `checked_div(a, b)` or `checked_rem(a, b)` (`VSugar.checked`): a call of that name when the
program declares no function of it and no local so named is in scope (SPEC §39). -/
def checkedOp? (c : TCx) : Val → Option SurfOp
  | .var _ x | .clone _ x =>
    if (c.locals.lookup x).isSome || (c.E.scope.findDef x).isSome then none
    else if x == "checked_div" then some .div else if x == "checked_rem" then some .rem else none
  | _ => none

/-- A comparison operator: its answer is `1 + 1`. -/
def isCmp : SurfOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- The type of an argument, when inference knows it: every local it names has a known type (an
unknown one is a slot of type `1` to inference), and it is not a computation's (a loop a call runs
in direct style answers its element, not the loop). An operator's is its operands' width, a
literal taking the other operand's (a comparison's is `1 + 1`), as the typed elaboration gives it;
a checked division's is that width and `DivError` (SPEC §39). -/
def argTy (c : TCx) : Val → Option CVTy
  | .ascribe _ _ A => c.elabV A
  | .pair _ V W => do pure (.tensor (← argTy c V) (← argTy c W))
  | .app _ (.sugar _ (.op o)) (.pair _ a b) =>
    if isCmp o then some (.sum .unit .unit) else (argTy c a).orElse fun _ => argTy c b
  | W@(.app _ f (.pair _ a b)) =>
    if (checkedOp? c f).isSome then
      ((argTy c a).orElse fun _ => argTy c b).map (.sum · (.sum .unit .unit))
    else argTyOf c W
  -- `*p` of a borrow: what it is a borrow of.
  | .app _ (.sugar _ .deref) V => match argTy c V with
    | some (.imm _ A) | some (.mut _ A) => some A
    | _ => none
  | W => argTyOf c W
where
  argTyOf (c : TCx) (W : Val) : Option CVTy :=
    if (varsV fuel W).any (fun x => match c.locals.lookup x with
        | some none => true
        | _ => false) then none
    else match c.tyV W with
      | some (.thunk _) => none
      | t => t

/-- The divisor `b` is a literal at which the division `o` at the width `w` has an answer:
nonzero there, and not `-1` for a signed `/`. With the width not known, a written literal `k`
with `0 < k < 256`, which is that at every integer width (SPEC §39). -/
def safeDivisor (w : Option BoCa.Width) (o : SurfOp) : Val → Bool
  | .sugar _ (.lit k) => match w with
    | some .w32 => k % 2^32 != 0 && (o != .div || k % 2^32 != 2^32 - 1)
    | some .w64 => k % 2^64 != 0 && (o != .div || k % 2^64 != 2^64 - 1)
    | some .w8 => k % 2^8 != 0
    | _ => 0 < k && k < 256
  | .const _ (.lit (.i32 n)) => w == some .w32 && n != 0 && (o != .div || n != 0xFFFFFFFF)
  | .const _ (.lit (.i64 n)) => w == some .w64 && n != 0 && (o != .div || n != 0xFFFFFFFFFFFFFFFF)
  | .const _ (.lit (.u8 n)) => w == some .w8 && n != 0
  | _ => false

/-- What the walk knows of the division `a o b` (`o` is `/` or `%`): `some true` when it can fail
(an integer width, and a divisor that is not `safeDivisor`), `some false` when it cannot (a float
width, or a safe divisor), `none` when the operands' width is not known here: not typed, a type
parameter (whose instances may be integers), or a type of the program's own that has a case of
the operator's family (SPEC §36), which the walk does not tell apart. A float literal operand is a
float division. -/
def divCanFail (c : TCx) (o : SurfOp) (a b : Val) : Option Bool :=
  let isLit : Val → Bool := fun | .sugar _ (.lit _) => true | _ => false
  let isFlit : Val → Bool := fun | .sugar _ (.flit ..) => true | _ => false
  if isFlit a || isFlit b then some false else
  match (argTy c a).orElse fun _ => argTy c b with
  | some (.int w) => if w.float?.isSome then some false else some !(safeDivisor (some w) o b)
  | _ =>
    if safeDivisor none o b then some false
    else if isLit a && isLit b then some true
    else none

/-- The type arguments a call of the template's parameter type `P` (its parameters `tps`) is at,
by matching `P` against the argument's type `A`; each as surface syntax in the frame `names`. -/
def matchArgs (c : TCx) (names tps : List String) (P : VTy) (A : CVTy) : Option (List VTy) := do
  let Pc ← patOf c tps P
  let m ← matchV { ty := Array.replicate tps.length none } 0 Pc A
  let ts ← m.ty.toList.mapM id
  ts.mapM (toSurf names fuel)

/-- The type `x <- M` gives `x`: its annotation, a value's type, or a computation's answer. A
binding whose head lends a place answers the place first (SPEC §11): not taken. -/
def bindTy (c : TCx) (A : Option VTy) (M : Comp) : Option CVTy :=
  match A with
  | some A => c.elabV A
  | none =>
    if !M.takeLends.2.isEmpty then none else
    match M with
    | .ret _ V => argTy c V
    | M => match (c.tyC M).bind effRow? with
      | some (_, A) => some A
      | none => none

/-- An operation's parameter tuple type (`1` with no parameters). -/
def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- The walk's state: the table, and the declaration being walked with its type parameters. -/
structure WSt where
  table : Table := {}
  /-- The divisions that can fail (SPEC §39), by their key. -/
  divs : List Key := []
  /-- The divisions whose operands' width the walk does not know: their declaration's name and
  their span. -/
  unknown : List (String × Span) := []

abbrev WM := StateM WSt

def record (owner : String) (sp : Span) (As : List VTy) : WM Unit :=
  modify fun s => { s with table := s.table.insert (key owner sp) As }

/-- At a call `f(W)`: an operation's instance, or a template's type arguments. -/
def atCall (d : Decls) (owner : String) (names : List String) (c : TCx) (sp : Span) (f W : Val) :
    WM Unit := do
  let some (x, written) := callee f | return
  if let some (etps, P) := d.ops.lookup x then
    if let some A := argTy c W then
      if let some As := matchArgs c names etps P A then record owner sp As
  else if let some (tps, G) := d.gens.lookup x then
    match written with
    | some As => if As.length == tps.length then record owner sp As
    | none =>
      if let (some P, some A) := (paramTyOf G, argTy c W) then
        if let some As := matchArgs c names tps P A then record owner sp As

/-- At a division `a o b` at `sp`: one that can fail raises `Fail[DivError]` there (SPEC §39). -/
def atDiv (owner : String) (c : TCx) (sp : Span) (o : SurfOp) (a b : Val) : WM Unit := do
  unless o == .div || o == .rem do return
  match divCanFail c o a b with
  | some true =>
    record owner sp [divErrorTy]
    modify fun s => { s with divs := key owner sp :: s.divs }
  | some false => pure ()
  | none =>
    -- Its width is not known here: it is taken to be able to fail, so that an integer division
    -- raises; at a float width the error's arm is never taken.
    record owner sp [divErrorTy]
    modify fun s => { s with divs := key owner sp :: s.divs, unknown := (owner, sp) :: s.unknown }

mutual
def walkV (d : Decls) (owner : String) (names : List String) : Nat → TCx → Val → WM Unit
  | 0, _, _ => pure ()
  | n + 1, c, V => match V with
    | .app sp (.sugar _ (.op o)) (.pair _ a b) => do
      atDiv owner c sp o a b
      walkV d owner names n c a
      walkV d owner names n c b
    | .app sp f W => do
      atCall d owner names c sp f W
      walkV d owner names n c f
      walkV d owner names n c W
    | .pair _ V W => do walkV d owner names n c V; walkV d owner names n c W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => walkV d owner names n c V
    | .thunk _ M | .bangThunk _ M => walkC d owner names n c.pushDead M
    | .thunkv _ M | .bangThunkv _ M | .run _ M => walkC d owner names n c M
    | _ => pure ()

def walkC (d : Decls) (owner : String) (names : List String) : Nat → TCx → Comp → WM Unit
  | 0, _, _ => pure ()
  | n + 1, c, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => walkV d owner names n c V
    | .bind _ x A M N _ => do
      walkC d owner names n c M
      walkC d owner names n (c.push x.name (bindTy c A M)) N
    | .lam _ x A M => walkC d owner names n (c.push x.name (c.elabV A)) M
    | .lamL _ x b M =>
      match c.elabL b with
      | some b => walkC d owner names n (c.pushLife x.name b) M
      | none => walkC d owner names n c.pushDead M
    | .app _ M _ | .proj _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M | .ascribe _ M _
    | .handle _ _ _ _ M => walkC d owner names n c M
    | .with_ _ M N => do
      walkC d owner names n c.pushDead.pushDead M
      walkC d owner names n c.pushDead.pushDead N
    | .letUnit _ V M => do walkV d owner names n c V; walkC d owner names n c M
    | .letPair _ x y V M => do
      walkV d owner names n c V
      let (A, B) := match argTy c V with
        | some (.tensor A B) => (some A, some B)
        | _ => (none, none)
      walkC d owner names n ((c.push x.name A).push y.name B) M
    | .case _ V x M y N => do
      walkV d owner names n c V
      let (A, B) := match argTy c V with
        | some (.sum A B) => (some A, some B)
        | _ => (none, none)
      walkC d owner names n (c.push x.name A) M
      walkC d owner names n (c.push y.name B) N
    | .loop _ _ .while_ V M N | .loop _ _ .forever V M N => do
      walkV d owner names n c V
      walkC d owner names n c M
      walkC d owner names n c N
    | .loop _ _ (.each x) V M N => do
      walkV d owner names n c V
      -- An iterator's or a generator's element; over a borrowed array, a borrow of an element
      -- (`*x` is what the walk needs of it); over a count `a..b`, an `i32` (SPEC §16).
      let el := match V with
        | .app _ (.sugar _ .count) _ => some (.int .w32)
        | V => (c.tyV V).bind fun T => (elemOf T).orElse fun _ => match T with
          | .fam (.imm a A) => some (.imm a A)
          | .fam (.mut a A) => some (.mut a A)
          | _ => none
      walkC d owner names n (c.push x.name el) M
      walkC d owner names n c N
    | .unwind _ x A M D N => do
      walkC d owner names n c M
      walkC d owner names n c.pushDead D
      walkC d owner names n (c.push x.name (bindTy c A M)) N
    | .withbor2r _ _ _ _ _ _ _ m M => walkC d owner names n (c.push m.name none) M
    | _ => pure ()
end

/-- What the walk of a program finds: the table, the divisions that can fail (SPEC §39), and the
integer divisions whose width it does not know. -/
structure Found where
  table : Table
  divs : List Key
  unknown : List (String × Span)

/-- The table of a program's declarations `ds`: each body typed in its declaration's frame. A
control handler's clauses are typed with its parameters, the operation's parameters (at the
handled effect's type arguments as the handler writes them) and the continuation bound; an
answering handler's with its state and the operation's parameters. -/
def found (ds : List Decl) : Found := Id.run do
  let base := TCx.ofScope ds true
  let effs : List (String × List String × List OpDecl) := ds.filterMap fun
    | .effect _ e tps ops => some (e.name, tps.map (·.name), ops)
    | _ => none
  let ops := effs.flatMap fun (_, tps, os) =>
    if tps.isEmpty then [] else os.map fun o => (o.name.name, tps, tupleTy o.name.span (o.params.map (·.2)))
  let gens := ds.filterMap fun
    | .def_ _ n ps A _ _ => if ps.isEmpty then none else some (n.name, ps.map (·.name), A)
    | _ => none
  let d : Decls := ⟨ops, gens⟩
  let go : WM Unit := do
    for decl in ds do
      match decl with
      | .def_ _ n ps _ V _ =>
        let names := ps.map (·.name)
        walkV d (ownerKey n.name n.span) names fuel (frame base names) V
      | .main sp _ M => walkC d (ownerKey "main" sp) [] fuel base M
      | .chandler _ ch =>
        let names := ch.tps.map (·.name)
        let c₀ := ch.params.foldl (fun c (x, A) => c.push x.name (c.elabV A)) (frame base names)
        let owner := ownerKey ch.name.name ch.name.span
        let (rx, rA, rM) := ch.ret
        walkC d owner names fuel (c₀.push rx.name (c₀.elabV rA)) rM
        let effOps := ((effs.find? (·.1 == ch.eff.name)).map (·.2)).getD ([], [])
        let σ : TySubst := effOps.1.zip ch.effArgs
        for cl in ch.clauses do
          let ps := ((effOps.2.find? (·.name.name == cl.name.name)).map (·.params)).getD []
          let c := cl.params.zipIdx.foldl (fun c (x, j) =>
            c.push x.name ((ps[j]?).bind fun (_, A) => c.elabV (A.subst σ))) c₀
          walkC d owner names fuel c cl.body
      | .handler _ h st S e cs _ =>
        let owner := ownerKey h.name h.span
        let effOps := ((effs.find? (·.1 == e.name)).map (·.2.2)).getD []
        let c₀ := base.push st.name (base.elabV S)
        for cl in cs do
          let ps := ((effOps.find? (·.name.name == cl.name.name)).map (·.params)).getD []
          let c := cl.params.zipIdx.foldl (fun c (x, j) =>
            c.push x.name ((ps[j]?).bind fun (_, A) => c.elabV A)) c₀
          walkC d owner [] fuel c cl.body
      | _ => pure ()
  let s := (go.run {}).2
  pure ⟨s.table, s.divs, s.unknown⟩

/-- The table of a program's declarations `ds` (`found`). -/
def table (ds : List Decl) : Table := (found ds).table

end Frontend.Elab.Instances
