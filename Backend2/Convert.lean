import Std.Data.HashMap
import Backend2.Syntax
import Backend2.Debug
import Frontend.Check.Kinds

/-!
# Backend2 — closure conversion of the typed term  `[spec §3, §10]`

`Checked.t`, the typed term the checker returns, to the LIR (`Backend2/Syntax.lean`). The
conversion follows the derivation node by node:

- **Contexts.** The conversion carries the node's context: at each slot, the LIR variable that
  holds it when it is live, `none` when it is dead. A binder pushes a live slot (its type is the
  node's binder type) or a dead one, as the node's rule does (`TExpr.children`'s scopes).
- **Ownership from the masks.** At a split (`TExpr.masks?`) the masks say which slots each part
  uses: a slot both use is copied (`Ctx.SplitP`'s `dup`, a persistent slot), a slot one uses
  moves to it, a live slot neither uses is dropped there (`Ctx.DeadP`'s `drop`, persistent).
  At a leaf every live slot but the one it reads is dropped (`Ctx.SoloP`, `Ctx.DeadP`). No copy
  and no drop is inferred from occurrences.
- **Closures.** A node that makes a λ-value (`lam`, `thunkF`, `allI`, `withI`, …) is a closure of a
  code of its own, capturing the live slots of its context. A thunk of a λ-value, `ret`,
  dereliction, the lifetime box and the lifetime coercions are the value they are over.
- **Constants** are read from their nodes: applied to their arguments (a spine of `lolliE`
  nodes) each is its operation (`expand`); used as a value it is a closure of a code that applies
  it.
- **Specialisation.** A `use` node's body is converted once per key (`useKey`): its value's
  term is kept as a template over the slots it reads, and each later use instantiates it, so the
  codes it makes are made once.
- **Derived nodes** are read: `divLit` is its division with no error arm, `litFn` a literal's
  table in the program's data, `walk` a counted walk whose reads are in range, `dtor` the drop of
  its type.
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- A slot of the context: its variable when live. -/
abbrev Ctx := List (Option Var)

/-- A `use` body converted once: the term of its value, over the variables of the slots it
reads (by slot), and its type. -/
structure Template where
  slots : List (Nat × Var)
  tm : Tm
  deriving Inhabited

/-- How an extern of `main` is implemented (SPEC §11, §34), in declaration order. -/
inductive Ext where
  /-- A capability's cell, holding the stream's descriptor: a word of the program's data. -/
  | cap (fd : Nat)
  /-- The clock's cell (SPEC §34). -/
  | clock
  /-- An operation. -/
  | io (k : IOKind)
  deriving Inhabited, BEq

structure CState where
  next : Nat := 0
  ty : Std.HashMap Var LTy := {}
  fns : Array Fn := #[]
  codes : Array Code := #[]
  uses : Std.HashMap String Template := {}
  data : Array UInt8 := #[]
  /-- The literal tables' codes, with their bytes' offset and length in the data. -/
  lits : Option Nat := none
  /-- What the conversion read of the typed term, by rule and fact (`bcc lir --census`). -/
  reads : Std.HashMap String Nat := {}
  /-- The static words for the capabilities' cells, in the data after the literals. -/
  statics : Array Nat := #[]
  /-- Record the type formers the layouts are read from (`readFormers`). -/
  census : Bool := false
  /-- The destructors of `μ` types, generated once per type (`genDtor`). -/
  dtors : Std.HashMap String Nat := {}
  /-- The variables bound to `unfold step` (a `bind` whose value is the `unfoldN` constant applied
  to its step), and their copies and captures: the `f` a `nuEta` node may call (SPEC §45). -/
  unfolds : Std.HashSet Var := {}
  /-- Inside a walk whose step reads its view at its index (`TExpr.walk`'s `read`, SPEC §46). -/
  walkRead : Bool := false
  /-- Converting a walk's read (`TExpr.walkGet`) inside such a walk: its index is in range. -/
  inRange : Bool := false
  /-- **The direct calls the checked facts license**  `[spec §48]`: at each static name, for each
  of its operations, whether every `handle` node of the name classifies its clause `tail`, its
  names meet condition 2 at the program's flow record (`cond2B`, `Checked.flows`), and the nodes
  hold one closed clause for it (`Backend2/Driver.lean`, `directFacts`). -/
  direct : Std.HashMap UInt32 (List Bool) := {}
  /-- The function of each directly called clause, by its operation, with the payload of its
  handler's outer row: the clause's work, its resumes removed (`TailResumesAt`). -/
  works : Std.HashMap (UInt32 × Nat) (Nat × List ((UInt32 × UInt32) × LTy)) := {}
  /-- The `handle`, `perform` and `raise` nodes erased (`bcc lir --erasure`). -/
  erased : Std.HashMap String Nat := {}
  /-- **The runtime answers every tick**  `[spec §49]`: `main` is a loop the runtime drives (SPEC
  §11), its value `reify` of its body, and that `reify` is the typed term's one handler of `Div`
  (no other `reify` and no `div_fuel` node: `Backend2/Driver.lean`, `divRuntime`). A tick is then
  answered *next*, where it is performed. -/
  divRt : Bool := false

abbrev CM := StateT CState (Except String)

def fresh (t : LTy) : CM Var := modifyGet fun s =>
  (s.next, { s with next := s.next + 1, ty := s.ty.insert s.next t })

def tyOf (x : Var) : CM LTy := do
  match (← get).ty[x]? with
  | some t => pure t
  | none => throw s!"LIR: variable {x} has no type"

def freshLike (x : Var) : CM Var := do fresh (← tyOf x)

/-- Record that the conversion read a fact of the typed term. -/
def readFact (k : String) : CM Unit :=
  modify fun s => { s with reads := s.reads.insert k (s.reads.getD k 0 + 1) }

def lift (r : Except String α) : CM α := match r with
  | .ok a => pure a
  | .error e => throw e

mutual
/-- The formers of a value type, each once. -/
def formersV (acc : List String) : VTy → List String
  | .tensor A B => formersV (formersV ("V.tensor" :: acc) A) B
  | .sum A B => formersV (formersV ("V.sum" :: acc) A) B
  | .thunk C => formersC ("V.thunk" :: acc) C
  | .ref A => formersV ("V.ref" :: acc) A
  | .imm _ A => formersV ("V.imm" :: acc) A
  | .mut _ A => formersV ("V.mut" :: acc) A
  | .box _ A => formersV ("V.box" :: acc) A
  | .bang A => formersV ("V.bang" :: acc) A
  | .mu A => formersV ("V.mu" :: acc) A
  | .fam A => formersV ("V.fam" :: acc) A
  | .unit => "V.unit" :: acc
  | .zero => "V.zero" :: acc
  | .unk => "V.unk" :: acc
  | .tvar _ => "V.tvar" :: acc
  | .int _ => "V.int" :: acc
  | .opq _ => "V.opq" :: acc
/-- The formers of a computation type, each once. -/
def formersC (acc : List String) : CTy → List String
  | .ret A => formersV ("C.ret" :: acc) A
  | .arr A C => formersC (formersV ("C.arr" :: acc) A) C
  | .amp C D => formersC (formersC ("C.amp" :: acc) C) D
  | .all _ _ C => formersC ("C.all" :: acc) C
  | .nu C => formersC ("C.nu" :: acc) C
  | .eff _ _ _ A B fin C => formersC (formersC (formersV (formersV ("C.eff" :: acc) A) B) fin) C
  | .top => "C.top" :: acc
end

/-- Record the formers a layout is read from (in the census's run). -/
def readFormers (fs : List String) : CM Unit := do
  if (← get).census then
    for f in fs.eraseDups do readFact s!"{f}:layout"

def vty (A : VTy) : CM LTy := do readFormers (formersV [] A); lift (ofV A)
def cty (C : CTy) : CM LCTy := do readFormers (formersC [] C); lift (ofC C)

/-- The type of a node's value: a value type's, `F A`'s `A`, and otherwise the closure the
computation's λ-value is. -/
def repJ (j : Jdg) : CM LTy := do
  match j with
  | .val A => vty A
  | .comp (.ret A) => vty A
  | .comp C@(.eff ..) => do
    -- `F_Σ R`'s value: `R`, or `R ⊕ P` (SPEC §48).
    match ← cty C with
    | .ret a => pure a
    | k => throw s!"LIR: a row's computation type at {k}"
  | .comp .top => pure .unit
  | .comp C => return .thunk (← cty C)

/-- `ls` is the value of a term: bind it to a fresh variable of type `t` unless it is a
variable already. -/
def bindTm (e : Tm) (t : LTy) (k : Var → CM Tm) : CM Tm := do
  match e with
  | .var x => k x
  | _ =>
    let x ← fresh t
    return .letv x e (← k x)

def drops (xs : List Var) (b : Tm) : Tm := xs.foldr (fun x b => .drop x b) b

def live (ctx : Ctx) : List Var := ctx.filterMap id

/-- At a leaf that reads the slot `keep` (or none): every other live slot dropped. -/
def leaf (ctx : Ctx) (keep : Option Nat) (b : Tm) : Tm :=
  let others := (ctx.zipIdx.filter fun (_, i) => some i != keep).filterMap (·.1)
  drops others b

/-- The context at a split, by its masks: the parts' contexts and the copies and drops made at the
split. -/
def splitCtx (ctx : Ctx) (m : Masks) (rule : String := "?") : CM ((Tm → Tm) × Ctx × Ctx) := do
  if m.ms.length != ctx.length then
    throw s!"LIR: masks of {m.ms.length} slots at a context of {ctx.length}"
  let mut pre : List (Tm → Tm) := []
  let mut c₁ : Array (Option Var) := #[]
  let mut c₂ : Array (Option Var) := #[]
  for (s, (a, b)) in ctx.zip m.ms do
    match s, a, b with
    | none, false, false => c₁ := c₁.push none; c₂ := c₂.push none
    | none, _, _ => throw "LIR: a mask uses a dead slot"
    | some x, true, true =>
      let x' ← freshLike x
      if (← get).unfolds.contains x then modify fun st => { st with unfolds := st.unfolds.insert x' }
      pre := (fun t => .copy x x' t) :: pre
      c₁ := c₁.push (some x); c₂ := c₂.push (some x')
    | some x, true, false => c₁ := c₁.push (some x); c₂ := c₂.push none
    | some x, false, true => c₁ := c₁.push none; c₂ := c₂.push (some x)
    | some x, false, false =>
      pre := (fun t => .drop x t) :: pre
      c₁ := c₁.push none; c₂ := c₂.push none
  readFact s!"{rule}:masks"
  return (fun t => pre.foldl (fun t f => f t) t, c₁.toList, c₂.toList)

/-- Register a function. -/
def addFn (f : Fn) : CM Nat := modifyGet fun s => (s.fns.size, { s with fns := s.fns.push f })

/-- Reserve a function's index, to be set by `setFn` (a recursive helper calls itself). -/
def reserveFn (name : String) : CM Nat := addFn { name, params := [], body := .unit, ret := .unit }

def setFn (i : Nat) (f : Fn) : CM Unit := modify fun s => { s with fns := s.fns.set! i f }

def addCode (c : Code) : CM Nat := modifyGet fun s => (s.codes.size, { s with codes := s.codes.push c })

/-- The environment of a closure made in `ctx`: its live slots, and the context its code sees,
each live slot renamed to the code's parameter. -/
def envOf (ctx : Ctx) : CM (List Var × List Var × Ctx) := do
  let mut outer : Array Var := #[]
  let mut inner : Array Var := #[]
  let mut ctx' : Array (Option Var) := #[]
  for s in ctx do
    match s with
    | some x =>
      let x' ← freshLike x
      if (← get).unfolds.contains x then modify fun st => { st with unfolds := st.unfolds.insert x' }
      outer := outer.push x; inner := inner.push x'; ctx' := ctx'.push (some x')
    | none => ctx' := ctx'.push none
  return (outer.toList, inner.toList, ctx'.toList)

/-- A closure of the closure type `k`, made in `ctx`, of a code of one function: `lam` when
`param` gives its argument's type, `unit` otherwise; `body` converts its body at the code's
context (its argument's slot pushed when it has one). -/
def mkClos (name : String) (ctx : Ctx) (k : LCTy) (param : Option LTy) (ret : LTy)
    (body : Ctx → CM Tm) : CM Tm := do
  let (outer, inner, ctx') ← envOf ctx
  let fi ← reserveFn name
  match param with
  | some pt =>
    let p ← fresh pt
    let b ← body (some p :: ctx')
    setFn fi { name, params := inner ++ [p], body := b, ret }
    let c ← addCode { kind := .lam, fns := [fi], ty := k }
    return .clos c outer
  | none =>
    let b ← body ctx'
    setFn fi { name, params := inner, body := b, ret }
    let c ← addCode { kind := .unit, fns := [fi], ty := k }
    return .clos c outer

/-- A closure of a `&`: one function per component over one environment. -/
def mkAmp (name : String) (ctx : Ctx) (k : LCTy) (rets : List LTy)
    (bodies : List (Ctx → CM Tm)) : CM Tm := do
  let (outer, _, _) ← envOf ctx
  let mut fis : Array Nat := #[]
  for (b, r) in bodies.zip rets do
    let (_, inner, ctx') ← envOf ctx
    let fi ← reserveFn name
    let t ← b ctx'
    setFn fi { name, params := inner, body := t, ret := r }
    fis := fis.push fi
  let c ← addCode { kind := .amp, fns := fis.toList, ty := k }
  return .clos c outer

/-- The argument and answer of a closure type `A ⊸ F B`. -/
def arrowOf : LTy → CM (LTy × LTy)
  | .thunk (.arr a (.ret b)) => pure (a, b)
  | t => throw s!"LIR: not a function type: {t}"

/-- The answer of running a closure of type `t`: its argument's type and its answer's, for a
`lam` code; its answer's for a `unit` one. -/
def answerOf : LTy → CM (Option LTy × LTy)
  | .thunk k => do
    match k.whnf 8 with
    | .arr a c => return (some a, ← repC c)
    | .ret a => return (none, a)
    | k => throw s!"LIR: a closure of {k} is not called"
  | t => throw s!"LIR: a call of a non-closure: {t}"
where
  repC : LCTy → CM LTy
    | .ret a => pure a
    | .top => pure .unit
    | k => pure (.thunk k)

/-- Apply the closure `f` to `args` in turn, each call a closure call of the type it has. -/
def applyAll (f : Var) : List Var → CM Tm
  | [] => pure (.var f)
  | [a] => return .app f a
  | a :: as => do
    let (_, r) ← answerOf (← tyOf f)
    bindTm (.app f a) r fun g => applyAll g as

/-! ### Small terms -/

def i32T : LTy := .int .w32
def boolT : LTy := .sum .unit .unit

def lit32 (n : UInt32) (k : Var → CM Tm) : CM Tm := do
  let x ← fresh i32T
  return .letv x (.lit (.i32 n)) (← k x)

/-- `x` copied: `k x x'`. -/
def dup (x : Var) (k : Var → Var → CM Tm) : CM Tm := do
  let x' ← freshLike x
  return .copy x x' (← k x x')

/-- The host operation `op` on the pair `(a, b)`, its answer of type `t`. -/
def bin (op : HostOp) (a b : Var) (t : LTy) (k : Var → CM Tm) : CM Tm := do
  let p ← fresh (.pair (← tyOf a) (← tyOf b))
  let r ← fresh t
  return .letv p (.pair a b) (.letv r (.prim (.host op) [p]) (← k r))

/-- `yes` when `a < b` (unsigned), else `no`; `a` and `b` consumed. -/
def ifLt (a b : Var) (yes no : CM Tm) : CM Tm := do
  let c ← fresh boolT
  let u₁ ← fresh .unit
  let u₂ ← fresh .unit
  return .letv c (.prim .cntLt [a, b]) (.case c u₁ (.drop u₁ (← no)) u₂ (.drop u₂ (← yes)))

def add1 (i : Var) (k : Var → CM Tm) : CM Tm := do
  let j ← fresh i32T
  return .letv j (.prim .cntSucc [i]) (← k j)

def letpairM (p : Var) (k : Var → Var → CM Tm) : CM Tm := do
  match ← tyOf p with
  | .pair a b =>
    let x ← fresh a
    let y ← fresh b
    return .letpair x y p (← k x y)
  | t => throw s!"LIR: letpair of a non-pair: {t}"

def unitThen (b : Tm) : CM Tm := do
  let u ← fresh .unit
  return .letv u b (.drop u .unit)

/-! ### Rows and their payloads  `[spec §48]`

A computation at the row `Σ` answers `R ⊕ P` when `Σ` has abortive operations, `P` the payload of
their arguments (`Backend2/Types.lean`, `payOf`), and `R` otherwise. The payload is read off the
row a node carries; each operation is a summand, at its index among the row's abortive
operations. -/

/-- The payload of a row: its abortive operations, each key once with its argument's type, in the
row's order (`Types.payOf`'s list).  `[spec §48]` -/
abbrev Pay := List ((UInt32 × UInt32) × LTy)

def rowPay (S : Row) : CM Pay := do
  let mut acc : Pay := []
  for o in S do
    if o.abort && !(acc.any (·.1 == (o.n, o.i))) then
      acc := acc ++ [((o.n, o.i), ← vty o.A)]
  return acc

/-- The payload's type: `none` at no operation. -/
def payTy (p : Pay) : Option LTy := payOf p

/-- The value type of a computation answering `a` at the payload `p`. -/
def resTy (a : LTy) (p : Pay) : LTy :=
  match payTy p with
  | none => a
  | some t => .sum a t

/-- The payload `p` holding `v` at the summand `j`. -/
def injectPay (p : Pay) (j : Nat) (v : Var) (k : Var → CM Tm) : CM Tm := do
  match p, j with
  | [_], _ => k v
  | _ :: rest, 0 => do
    let w ← fresh (← lift (Option.elim (payTy p) (.error "LIR: an empty payload") .ok))
    return .letv w (.inj false v) (← k w)
  | _ :: rest, j + 1 =>
    injectPay rest j v fun r => do
      let w ← fresh (← lift (Option.elim (payTy p) (.error "LIR: an empty payload") .ok))
      return .letv w (.inj true r) (← k w)
  | [], _ => throw "LIR: an operation outside its row's payload"

/-- Take the payload `x` of `p` apart: `k j v` at the summand `j`, its argument `v`. -/
def casePay (p : Pay) (x : Var) (k : Nat → Var → CM Tm) : CM Tm := do
  match p with
  | [] => throw "LIR: an empty payload"
  | [_] => k 0 x
  | (_, t) :: rest => do
    let a ← fresh t
    let b ← fresh (← lift (Option.elim (payTy rest) (.error "LIR: an empty payload") .ok))
    return .case x a (← k 0 a) b (← casePay rest b fun j v => k (j + 1) v)

/-- The index of an operation's key among a payload's summands. -/
def payIdx (p : Pay) (key : UInt32 × UInt32) : Option Nat := p.findIdx? (·.1 == key)

/-- A payload `x` of `p` as one of `q`: each operation at its own summand of `q`, which holds it
(the row `Σ ⊆ Σ'`, `RowLe`).  `[spec §48]` -/
def coercePay (p q : Pay) (x : Var) (k : Var → CM Tm) : CM Tm := do
  if p.map (·.1) == q.map (·.1) then return ← k x
  casePay p x fun j v => do
    let some key := (p[j]?).map (·.1) | throw "LIR: a payload's summand"
    let some j' := payIdx q key | throw s!"LIR: a raise of {key} where its row does not hold it"
    injectPay q j' v k

/-- The answer `r` of a computation answering `a` at the payload `p`, as one at `q`: a value
handed on as `inl`, an abort's payload re-injected.  `[spec §48]` -/
def coerceRes (a : LTy) (p q : Pay) (r : Var) : CM Tm := do
  if p.map (·.1) == q.map (·.1) then return .var r
  match payTy p, payTy q with
  | none, none => return .var r
  | none, some _ => return .inj false r
  | some pT, some _ => do
    let x ← fresh a; let e ← fresh pT
    return .case r x (.inj false x) e (← coercePay p q e fun e' => pure (.inj true e'))
  | some _, none => throw "LIR: an abort where the row holds no abortive operation"

/-! ### Loops generated per site -/

/-- `tab (c, f)` (`array_new`, SPEC §9): an array of `len(c)` slots, slot `i` holding `f i`. -/
def genTab (aT fT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "tab"
  let f ← fresh fT; let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let (_, eT) ← answerOf fT
        bindTm (.app f' i') eT fun v => dup i fun i i'' => do
          let a' ← fresh aT
          return .letv a' (.prim .slotPut [a, i'', v]) (← add1 i fun i₂ => pure (.call fi [f, a', i₂, n])))
      (pure (.drop f (.drop i (.drop n (.var a)))))
  setFn fi { name := "tab", params := [f, a, i, n], body, ret := aT }
  letpairM p fun c f => do
    let n ← fresh i32T
    return .letv n (.prim .clampLen [c]) (.prim (.tab fi) [f, n])

/-- `drop (f, a)` (`array_free`): each slot's contents to `f`, in order, then the array freed. -/
def genArrFree (fT aT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "array_free"
  let f ← fresh fT; let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
  let (some eT, _) ← answerOf fT | throw "LIR: array_free's consumer takes no argument"
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup i fun i i' => do
        let pr ← fresh (.pair aT eT)
        let a' ← fresh aT; let v ← fresh eT
        return .letv pr (.prim .slotTake [a, i']) (.letpair a' v pr (← dup f fun f f' => do
          let u ← fresh .unit
          return .letv u (.app f' v) (.drop u (← add1 i fun i₂ => pure (.call fi [f, a', i₂, n]))))))
      (do return .drop f (.drop i (.drop n (← unitThen (.prim .freeArr [a])))))
  setFn fi { name := "array_free", params := [f, a, i, n], body, ret := .unit }
  letpairM p fun f a => do
    let pr ← fresh (.pair aT i32T)
    let a' ← fresh aT; let n ← fresh i32T
    return .letv pr (.prim .size [a]) (.letpair a' n pr (← lit32 0 fun z => pure (.call fi [f, a', z, n])))

/-- `count_fold (f, (n, (i, s)))` (SPEC §16): `f` at `i, …, len(n) − 1`, threading `s`. -/
def genCount (fT sT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "count_fold"
  let f ← fresh fT; let n ← fresh i32T; let i ← fresh i32T; let st ← fresh sT
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let q ← fresh (.pair i32T sT)
        let st' ← fresh sT
        return .letv q (.pair i' st) (.letv st' (.app f' q)
          (← add1 i fun i₂ => pure (.call fi [f, n, i₂, st']))))
      (pure (.drop f (.drop n (.drop i (.var st)))))
  setFn fi { name := "count_fold", params := [f, n, i, st], body, ret := sT }
  letpairM p fun f r => letpairM r fun c r₂ => letpairM r₂ fun i st => do
    let n ← fresh i32T
    return .letv n (.prim .clampLen [c]) (.call fi [f, n, i, st])

/-- `count_try (f, (n, (i, s)))` (SPEC §16): `f` at `i, …, len(n) − 1` while it answers `inl` of
the next state; its first `inr` is the answer, else `inl` of the last state. -/
def genCountTry (fT sT eT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "count_try"
  let f ← fresh fT; let n ← fresh i32T; let i ← fresh i32T; let st ← fresh sT
  let rT : LTy := .sum sT eT
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let q ← fresh (.pair i32T sT)
        let r ← fresh rT
        let s' ← fresh sT; let e ← fresh eT
        return .letv q (.pair i' st) (.letv r (.app f' q)
          (.case r s' (← add1 i fun i₂ => pure (.call fi [f, n, i₂, s']))
            e (.drop f (.drop n (.drop i (.inj true e)))))))
      (pure (.drop f (.drop n (.drop i (.inj false st)))))
  setFn fi { name := "count_try", params := [f, n, i, st], body, ret := rT }
  letpairM p fun f r => letpairM r fun c r₂ => letpairM r₂ fun i st => do
    let n ← fresh i32T
    return .letv n (.prim .clampLen [c]) (.call fi [f, n, i, st])

/-- A borrow `withbor`'s way (SPEC §1): `(x, f [] x)`, the owner `src` lent as the borrow the
callback `cb` (a `∀` closure, its instantiation erased: SPEC §44) is given, by `op` (`lend`,
`relend`). -/
def genLend (op : Op) (src : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some bT, rT) ← answerOf cbT | throw "LIR: a borrow's callback takes no borrow"
  let pr ← fresh (.pair (← tyOf src) bT)
  let o ← freshLike src; let b ← fresh bT
  let r ← fresh rT
  readFact "lend"
  return .letv pr (.prim op [src]) (.letpair o b pr (.letv r (← call b) (.pair o r)))

/-- The call of a borrow's callback `cb` on `b`: `cb [] b`, its instantiation erased (SPEC §44). -/
def callCb (cb : Var) (b : Var) : CM Tm := pure (.app cb b)

/-- `withload x f` (SPEC §1): `f () (load x)`, the contents read at the callback's argument type. -/
def genWithload (x : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some vT, _) ← answerOf cbT | throw "LIR: withload's callback takes no argument"
  let v ← fresh vT
  return .letv v (.prim .load [x]) (← call v)

/-- `withswap x f` (SPEC §1): `let (y, z) = f (load x); store x y; (x, z)`, the load's copy and the
store's drop of the old contents cancelled: the contents moved out, and `y` moved in. -/
def genWithswap (m : Var) (fT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some aT, rT) ← answerOf fT | throw "LIR: withswap's function takes no argument"
  let .pair yT zT := rT | throw "LIR: withswap's function answers no pair"
  let mT ← tyOf m
  let pr ← fresh (.pair mT aT)
  let m' ← fresh mT; let old ← fresh aT
  let r ← fresh rT
  let y ← fresh yT; let z ← fresh zT
  let m'' ← fresh mT
  return .letv pr (.prim .take [m]) (.letpair m' old pr (.letv r (← call old)
    (.letpair y z r (.letv m'' (.prim .put [m', y]) (.pair m'' z)))))

/-! ### Folds (SPEC §6)

`fold_own`, `fold_reuse` and `fold_imm` read their node's shape `F` and result `R`: the fold is a
function generated for the node, recursive on its own, which traverses the unrolled value at the
shape (`travO`, `travR`, `travK` of `Core/`) and applies the algebra. -/

inductive FoldKind where
  | own | reuse | imm
  deriving BEq

/-- The traversal of `w` (of the unrolling at the shape `F`), the recursive positions by `recur`:
its term and its type. `g` is the algebra, copied for each recursive call. -/
def travF (k : FoldKind) (recV recL : Nat) (g : Var) : FShape → Var → CM (Tm × LTy)
  | .leaf _, w => return (.var w, ← tyOf w)
  | .refX, w => do
    let (_, rT) ← answerOf' (← tyOf g)
    let g' ← freshLike g
    match k with
    | .own => do
      let .ref cT := (← tyOf w) | throw "LIR: fold_own at a `Ref X` that is not a cell"
      let c ← fresh cT
      return (.copy g g' (.letv c (.prim .free [w]) (.call recV [g', c])), rT)
    | .reuse => do
      let .ref cT := (← tyOf w) | throw "LIR: fold_reuse at a `Ref X` that is not a cell"
      let u ← fresh .unit
      let pr ← fresh (.pair (.ref .unit) cT)
      let c ← fresh (.ref .unit); let v ← fresh cT
      let r ← fresh rT
      return (.copy g g' (.letv u .unit (.letv pr (.prim .swap [w, u]) (.letpair c v pr
        (.letv r (.call recV [g', v]) (.pair c r))))), .pair (.ref .unit) rT)
    | .imm => return (.copy g g' (.call recL [g', w]), rT)
  | .varX, w => do
    let (_, rT) ← answerOf' (← tyOf g)
    let g' ← freshLike g
    return (.copy g g' (.call recV [g', w]), rT)
  | .tensor F G, w => do
    let .pair aT bT := (← tyOf w) | throw "LIR: a fold's shape `⊗` at a non-pair"
    let a ← fresh aT; let b ← fresh bT
    let (ta, ra) ← travF k recV recL g F a
    let (tb, rb) ← travF k recV recL g G b
    let x ← fresh ra; let y ← fresh rb
    return (.letpair a b w (.letv x ta (.letv y tb (.pair x y))), .pair ra rb)
  | .sum F G, w => do
    let .sum aT bT := (← tyOf w) | throw "LIR: a fold's shape `⊕` at a non-sum"
    let a ← fresh aT; let b ← fresh bT
    let (ta, ra) ← travF k recV recL g F a
    let (tb, rb) ← travF k recV recL g G b
    let x ← fresh ra; let y ← fresh rb
    return (.case w a (.letv x ta (.inj false x)) b (.letv y tb (.inj true y)), .sum ra rb)
where
  /-- The algebra's answer (its `∀` at `fold_imm` erased: SPEC §44). -/
  answerOf' (gT : LTy) : CM (Option LTy × LTy) := answerOf gT

/-- The recursive functions of a fold at the node's shape `F`: on a value of `μX. T` (`recV`), and
at `fold_imm` on a borrow of one (`recL`, whose cell's contents it reads as `Imm̲`). `muT` is the
type of the values `recV` folds, `gT` the algebra's. -/
def genFoldFns (k : FoldKind) (F : FShape) (muT cellT gT : LTy) : CM (Nat × Nat) := do
  let recV ← reserveFn "fold"
  let recL ← if k == .imm then reserveFn "fold_imm" else pure recV
  let .mu body := muT | throw s!"LIR: a fold over a non-μ type: {muT}"
  let g ← fresh gT
  let u ← fresh muT
  let w ← fresh body.unrollMu
  let (tt, rT) ← travF k recV recL g F w
  let r ← fresh rT
  let ans := Tm.app g r
  let (_, R) ← answerOf gT
  setFn recV { name := "fold", params := [g, u], ret := R,
               body := .letv w (.prim .unroll [u]) (.letv r tt ans) }
  if k == .imm then
    let g₂ ← fresh gT
    let l ← fresh (.imm cellT)
    -- `fold_imm`'s values are `Imm̲` of the structure: the borrow's contents read as `muT`.
    let v ← fresh muT
    setFn recL { name := "fold_imm", params := [g₂, l], ret := R,
                 body := .letv v (.prim .load [l]) (.call recV [g₂, v]) }
  return (recV, recL)

/-! ### Codata (SPEC §7)

`unfold`'s node gives its body `C` and state `S`. `unfold g s` is a closure over `(g, s)` of a code
for `νX. C`; an observation runs `g s` along its path (`nodeV`'s `childV`, the step run at the
observation's leaf) and maps each state at an `X` of the answer to `unfold g` of it (`mapV`). -/

/-- The type of component `j` of a `&` closure. -/
def selTy (t : LTy) (j : Nat) : CM LTy := do
  match t with
  | .thunk k =>
    match k.whnf 8, j with
    | .amp k₁ _, 0 => repK k₁
    | .amp _ k₂, _ => repK k₂
    | k, _ => throw s!"LIR: an observation of a closure of {k}"
  | t => throw s!"LIR: an observation of a non-closure: {t}"
where
  repK : LCTy → CM LTy
    | .ret a => pure a
    | .top => pure .unit
    | k => pure (.thunk k)

/-- The type variable `n` occurs at a `⊗`/`⊕` position of `a`. -/
def occursAt (n : Nat) : LTy → Bool
  | .tvar m => m == n
  | .pair a b | .sum a b => occursAt n a || occursAt n b
  | _ => false

def occ0 (a : LTy) : Bool := occursAt 0 a

/-- `t` (the step's type at `a`) with each state at an `X` of `a` replaced by the codata type. -/
def substState : LTy → LTy → LTy → LTy
  | .tvar 0, _, c => c
  | .pair a b, .pair x y, c => .pair (substState a x c) (substState b y c)
  | .sum a b, .sum x y, c => .sum (substState a x c) (substState b y c)
  | _, t, _ => t

/-- A step of an observation's path: a component, or an argument. -/
inductive PathStep where
  | sel (j : Nat)
  | arg (x : Var)

mutual
/-- The answer of the observation tree `C` at the path `steps`, over the step `g` and the state
`s` (consumed): at an `F A` leaf the step run and its states mapped; else a closure of the rest of
the tree. `obs` is the code of `unfold g s` itself. -/
def nodeAt (fuel : Nat) (obs : Nat) (C : LCTy) (steps : List PathStep) (g s : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: an observation tree too deep"
  | fuel + 1 =>
  match C with
  | .ret A => do
    let (_, stT) ← answerOf (← tyOf g)
    let g' ← freshLike g
    let st ← fresh stT
    let t ← runPath fuel st steps fun r => mapStates fuel obs A g r
    return .copy g g' (.letv st (.app g' s) t)
  | .amp C₁ C₂ => do
    let nu ← nuTyOf obs
    let k : LCTy := LCTy.subst 0 nu (.amp C₁ C₂)
    let ctx : Ctx := [some g, some s] ++ (steps.filterMap fun | .arg x => some (some x) | _ => none)
    let r₁ ← resOf (LCTy.subst 0 nu C₁)
    let r₂ ← resOf (LCTy.subst 0 nu C₂)
    mkAmp "observe" ctx k [r₁, r₂] [
      fun ctx' => bodyAt fuel obs C₁ (steps ++ [.sel 0]) ctx',
      fun ctx' => bodyAt fuel obs C₂ (steps ++ [.sel 1]) ctx']
  | .arr A D => do
    let ctx : Ctx := [some g, some s] ++ (steps.filterMap fun | .arg x => some (some x) | _ => none)
    let nu ← nuTyOf obs
    mkClos "observe" ctx (LCTy.subst 0 nu (.arr A D)) (some (LTy.subst 0 nu A))
      (← resOf (LCTy.subst 0 nu D)) fun ctx' => do
      match ctx' with
      | some x :: rest => bodyAt fuel obs D (steps ++ [.arg x]) (rest ++ [some x])
      | _ => throw "LIR: an observation's argument"
  | C => throw s!"LIR: an observation tree at {C}"
/-- `nodeAt` in a code whose context holds `g`, `s` and the path's arguments, in that order. -/
def bodyAt (fuel : Nat) (obs : Nat) (C : LCTy) (steps : List PathStep) (ctx : Ctx) : CM Tm := do
  match fuel, ctx with
  | 0, _ => throw "LIR: an observation tree too deep"
  | fuel + 1, some g :: some s :: args =>
    -- The path's arguments, renamed to the code's parameters.
    let mut as := args.filterMap id
    let mut steps' : Array PathStep := #[]
    for st in steps do
      match st, as with
      | .arg _, a :: rest => steps' := steps'.push (.arg a); as := rest
      | .sel j, _ => steps' := steps'.push (.sel j)
      | .arg _, [] => throw "LIR: an observation's arguments"
    nodeAt fuel obs C steps'.toList g s
  | _, _ => throw "LIR: an observation's environment"
/-- Run the path on the step's answer `st`. -/
def runPath (fuel : Nat) (st : Var) : List PathStep → (Var → CM Tm) → CM Tm
  | [], k => k st
  | .sel j :: rest, k => do
    let t ← selTy (← tyOf st) j
    bindTm (.sel st j) t fun r => runPath fuel r rest k
  | .arg x :: rest, k => do
    let (_, t) ← answerOf (← tyOf st)
    bindTm (.app st x) t fun r => runPath fuel r rest k
/-- `map_A (unfold g) w`: each state at an `X` (`#0`) of `A` the codata `unfold g` of it; `g`
consumed. -/
def mapStates (fuel : Nat) (obs : Nat) (A : LTy) (g w : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a codata answer too deep"
  | fuel + 1 =>
  match A with
  | .tvar 0 => return .clos obs [g, w]
  | .pair a b => do
    if !(occ0 a || occ0 b) then return .drop g (.var w)
    letpairM w fun x y => dup g fun g g' => do
      let x' ← fresh (← mappedTy obs x a)
      let y' ← fresh (← mappedTy obs y b)
      return .letv x' (← mapStates fuel obs a g x) (.letv y' (← mapStates fuel obs b g' y) (.pair x' y'))
  | .sum a b => do
    if !(occ0 a || occ0 b) then return .drop g (.var w)
    let .sum xT yT := (← tyOf w) | throw "LIR: a codata answer's sum"
    let x ← fresh xT; let y ← fresh yT
    let x' ← fresh (← mappedTy obs x a)
    let y' ← fresh (← mappedTy obs y b)
    let g₁ ← freshLike g
    let g₂ ← freshLike g
    return .copy g g₁ (.copy g g₂ (.drop g (.case w
      x (.letv x' (← mapStates fuel obs a g₁ x) (.drop g₂ (.inj false x')))
      y (.letv y' (← mapStates fuel obs b g₂ y) (.drop g₁ (.inj true y'))))))
  | _ => return .drop g (.var w)
/-- The closure type of the codata of the code `obs`. -/
def nuTyOf (obs : Nat) : CM LTy := do
  match (← get).codes[obs]? with
  | some c => pure (.thunk c.ty)
  | none => throw "LIR: no codata code"
/-- The result type of an observation subtree. -/
def resOf : LCTy → CM LTy
  | .ret A => pure A
  | k => pure (.thunk k)
/-- The type of `w`'s value once mapped at `a`. -/
def mappedTy (obs : Nat) (w : Var) (a : LTy) : CM LTy := do
  let t ← tyOf w
  if occ0 a then return substState a t (← nuTyOf obs)
  return t
end

/-- The code of `unfold g s` at the body `C` (a `&` of observation trees, `CTy.NuOk`), its step
of type `gT` and state of type `sT`. -/
def genUnfold (C : LCTy) (gT sT : LTy) : CM Nat := do
  let .amp C₁ C₂ := C | throw s!"LIR: unfold at a body that is not a `&`: {C}"
  let obs ← addCode { kind := .amp, fns := [], ty := .nu C }
  let nu : LTy := .thunk (.nu C)
  let mut fis : Array Nat := #[]
  for (Cj, j) in [(C₁, 0), (C₂, 1)] do
    let g ← fresh gT
    let st ← fresh sT
    let fi ← reserveFn "observe"
    let b ← nodeAt 64 obs Cj [.sel j] g st
    setFn fi { name := "observe", params := [g, st], body := b, ret := ← resOf (LCTy.subst 0 nu Cj) }
    fis := fis.push fi
  modify fun s => { s with codes := s.codes.set! obs { kind := .amp, fns := fis.toList, ty := .nu C } }
  readFact "unfoldN:body"
  return obs

/-! ### Loops of `Div` and of `bounded_fix`  `[spec §49]` -/

/-- **`iterate (f, s)` under the runtime** (SPEC §14, §49): the loop `iterate`'s machine step
unrolls (`Head.iterate`, `iter_step`), its back edge a tail call. A turn `(f s).1` answers
`inl b`, finished, or `inr s′`, after which `iterate` ticks; the runtime answers the tick *next*
(`tail_resumes` at its clause `λ((), κ). κ next`), so the turn's `case` on the answer goes on with
`iterate (f, s′)`: the close `(f s′).2` is never observed. An abort of the row's payload `pay` is
handed on. `ansT` is the node's answer `B ⊕ R` at `pay`.  `[spec §49]` -/
def genIter (fT ansT : LTy) (pay : Pay) (p : Var) : CM Tm := do
  let fi ← reserveFn "iterate"
  let f ← fresh fT
  let (some sT, gT) ← answerOf fT | throw "LIR: iterate's step takes no state"
  let s ← fresh sT
  let xT ← selTy gT 0
  let valT ← match payTy pay, ansT with
    | none, t => pure t
    | some _, .sum t _ => pure t
    | some _, t => throw s!"LIR: iterate's answer at a row with aborts: {t}"
  let .sum _ _ := valT | throw s!"LIR: iterate's answer is not `B ⊕ R`: {valT}"
  let body ← dup f fun f f' => do
    let g ← fresh gT
    let x ← fresh xT
    let turn (o : Var) : CM Tm := do
      let .sum oB oS := (← tyOf o) | throw "LIR: iterate's turn does not answer `B ⊕ S`"
      let b ← fresh oB; let s' ← fresh oS
      let w ← fresh valT
      let done : Tm := match payTy pay with
        | none => .drop f (.letv w (.inj false b) (.var w))
        | some _ => .drop f (.letv w (.inj false b) (.inj false w))
      return .case o b done s' (.call fi [f, s'])
    let rest ← match payTy pay with
      | none => turn x
      | some pT => do
        let .sum oT _ := (← tyOf x) | throw "LIR: iterate's turn at a row with aborts"
        let o ← fresh oT; let e ← fresh pT
        return .case x o (← turn o) e (.drop f (.inj true e))
    return .letv g (.app f' s) (.letv x (.sel g 0) rest)
  setFn fi { name := "iterate", params := [f, s], body, ret := ansT }
  letpairM p fun f s => pure (.call fi [f, s])

/-- **`bounded_fix (s, (k, a))`** (SPEC §20): its machine step (`Head.boundedFix`), `s` run on
`(self_k, a)`, `self_0 = inl ()` and `self_{j+1} = inr (λx. bounded_fix (s, (j, x)))`, the budget
read unsigned and counted down. The self-reference is a closure of a code of its own over `s` and
`j`, whose call is `bounded_fix (s, (j, x))` again: a step that calls it in tail position is a loop
of tail calls with its budget (§47's counted loops at the row), and one that calls it elsewhere a
native recursion bounded by it (§20, §21).  `[spec §49]` -/
def genFix (sT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "bounded_fix"
  let (some qT, rT) ← answerOf sT | throw "LIR: bounded_fix's step takes no argument"
  let .pair selfOT aT := qT | throw "LIR: bounded_fix's step does not take `(self, a)`"
  let .sum _ selfT := selfOT | throw "LIR: bounded_fix's self-reference is not `1 ⊕ U(A ⊸ C)`"
  let .thunk selfK := selfT | throw "LIR: bounded_fix's self-reference is not a closure"
  let si ← reserveFn "bounded_fix self"
  let s₁ ← fresh sT; let k₁ ← fresh i32T; let x ← fresh aT
  setFn si { name := "bounded_fix self", params := [s₁, k₁, x], body := .call fi [s₁, k₁, x],
             ret := rT }
  let c ← addCode { kind := .lam, fns := [si], ty := selfK }
  let s ← fresh sT; let k ← fresh i32T; let a ← fresh aT
  let body ← dup s fun s s' => dup k fun k k' => lit32 0 fun z => do
    let self ← fresh selfOT
    let k₂ ← fresh i32T; let cl ← fresh selfT
    let yes : Tm := .letv k₂ (.prim .cntPred [k]) (.letv cl (.clos c [s', k₂]) (.inj true cl))
    let u ← fresh .unit
    let no : Tm := .drop s' (.drop k (.letv u .unit (.inj false u)))
    let test ← ifLt z k' (pure yes) (pure no)
    let q ← fresh qT
    return .letv self test (.letv q (.pair self a) (.app s q))
  setFn fi { name := "bounded_fix", params := [s, k, a], body, ret := rT }
  letpairM p fun s r => letpairM r fun k a => pure (.call fi [s, k, a])

/-! ### Destructors (SPEC §12)

`dtor A` (the checker's `dtorE A`, at an owned value that goes unused) is the destructor its type
gives (`Core/Dtor.lean`, `dtorAt`): nothing at a forgettable type, componentwise, a cell freed
and its contents destroyed, a `μ` by an owned fold, `close` at codata, `array_free` at an array. -/

mutual
/-- The destructor of `A` on `x`: a term of type `1`. -/
def genDtor (fuel : Nat) (A : VTy) (x : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a destructor's type too deep"
  | f + 1 =>
  match A with
  | .tensor A B => letpairM x fun a b => do
      let u ← fresh .unit
      return .letv u (← genDtor f A a) (.drop u (← genDtor f B b))
  | .sum A B => do
    let .sum aT bT := (← tyOf x) | throw "LIR: a destructor's sum"
    let a ← fresh aT; let b ← fresh bT
    return .case x a (← genDtor f A a) b (← genDtor f B b)
  | .ref A => do
    let c ← fresh (← vty A)
    return .letv c (.prim .free [x]) (← genDtor f A c)
  | .box _ A => genDtor f A x
  | .mu T => do
    let key := ppVT (.mu T)
    let fi ← match (← get).dtors[key]? with
      | some fi => pure fi
      | none => do
        let fi ← reserveFn "dtor"
        modify fun s => { s with dtors := s.dtors.insert key fi }
        let u ← fresh (← vty (.mu T))
        let w ← fresh (← vty (VTy.inst (.mu T) T))
        let body ← dtorShape f fi (toFShape T) T w
        setFn fi { name := "dtor", params := [u], ret := .unit,
                   body := .letv w (.prim .unroll [u]) body }
        pure fi
    return .call fi [x]
  | .thunk (.nu (.amp _ (.ret R))) => do
    let rT ← selTy (← tyOf x) 1
    let r ← fresh rT
    return .letv r (.sel x 1) (← genDtor f R r)
  | .thunk _ => return .sel x 1
  | .fam (.ref A) => do
    let aT ← tyOf x
    let .fam (.ref eT) := aT | throw "LIR: an array's destructor"
    let fi ← reserveFn "array_dtor"
    let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
    let body ← dup i fun i i₁ => dup n fun n n₁ =>
      ifLt i₁ n₁
        (dup i fun i i' => do
          let pr ← fresh (.pair aT eT)
          let a' ← fresh aT; let v' ← fresh eT
          let u ← fresh .unit
          return .letv pr (.prim .slotTake [a, i']) (.letpair a' v' pr
            (.letv u (← genDtor f A v') (.drop u (← add1 i fun i₂ => pure (.call fi [a', i₂, n]))))))
        (do return .drop i (.drop n (.prim .freeArr [a])))
    setFn fi { name := "array_dtor", params := [a, i, n], body, ret := .unit }
    let pr ← fresh (.pair aT i32T)
    let a' ← fresh aT; let n' ← fresh i32T
    return .letv pr (.prim .size [x]) (.letpair a' n' pr (← lit32 0 fun z => pure (.call fi [a', z, n'])))
  | _ => return .drop x .unit

/-- The destructor at a `μ` body's shape, recursive positions by the type's own destructor `fi`. -/
def dtorShape (fuel : Nat) (fi : Nat) (F : FShape) (T : VTy) (w : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a destructor's shape too deep"
  | f + 1 =>
  match F with
  | .leaf A => genDtor f (VTy.inst (.mu T) A) w
  | .refX => do
    let c ← fresh (← vty (.mu T))
    return .letv c (.prim .free [w]) (.call fi [c])
  | .varX => return .call fi [w]
  | .tensor F G => letpairM w fun a b => do
      let u ← fresh .unit
      return .letv u (← dtorShape f fi F T a) (.drop u (← dtorShape f fi G T b))
  | .sum F G => do
    let .sum aT bT := (← tyOf w) | throw "LIR: a destructor's sum"
    let a ← fresh aT; let b ← fresh bT
    return .case w a (← dtorShape f fi F T a) b (← dtorShape f fi G T b)
end

/-! ### Blocks (SPEC §5, §42) -/

/-- A block's allocation at its shape: each leaf a cell. -/
def allocTree (v : Var) (rT : LTy) : CM Tm := do
  match rT with
  | .pair a b => letpairM v fun x y => do
      let x' ← fresh a; let y' ← fresh b
      return .letv x' (← allocTree x a) (.letv y' (← allocTree y b) (.pair x' y'))
  | .ref _ => return .prim .alloc [v]
  | t => throw s!"LIR: a block's handle at {t}"

/-- A block's release at its shape. -/
def freeTree (v : Var) (vT : LTy) : CM Tm := do
  match ← tyOf v, vT with
  | .pair _ _, .pair a b => letpairM v fun x y => do
      let x' ← fresh a; let y' ← fresh b
      return .letv x' (← freeTree x a) (.letv y' (← freeTree y b) (.pair x' y'))
  | .ref _, _ => return .prim .free [v]
  | t, _ => throw s!"LIR: a block's handle at {t}"

/-- Lend each leaf of the handle `v` at the borrow tree `bT`: the term binds `k`'s owners and
borrows. -/
def lendTree (v : Var) (bT : LTy) (k : Var → Var → CM Tm) : CM Tm := do
  match ← tyOf v, bT with
  | .pair _ _, .pair ba bb =>
    letpairM v (fun x y => lendTree x ba (fun ox bx => lendTree y bb (fun oy byy => do
      let o ← fresh (.pair (← tyOf ox) (← tyOf oy))
      let b ← fresh (.pair ba bb)
      return .letv o (.pair ox oy) (.letv b (.pair bx byy) (← k o b)))))
  | vT, _ =>
    let pr ← fresh (.pair vT bT)
    let o ← fresh vT; let b ← fresh bT
    return .letv pr (.prim .lend [v]) (.letpair o b pr (← k o b))

/-- A block borrow (`withborS`, `withborF2`): every leaf lent, the borrows handed to the callback at
one lifetime; `(handle, answer)`. -/
def genLendTree (src : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some bT, rT) ← answerOf cbT | throw "LIR: a block borrow's callback takes no borrow"
  readFact "lend"
  lendTree src bT fun o b => do
    let r ← fresh rT
    return .letv r (← call b) (.pair o r)

/-! ### Externs -/

/-- An I/O operation's closure at its extern's type: `λm. op m`, its `Λ`s erased (SPEC §44). -/
def ioClos (fuel : Nat) (k : IOKind) (t : LTy) : CM Tm := do
  match fuel, t with
  | 0, _ => throw "LIR: an extern's type too deep"
  | _, .thunk (.arr a (.ret b)) =>
    mkClos "extern" [] (.arr a (.ret b)) (some a) b fun ctx => do
      match ctx with
      | some p :: _ => return .prim (.io k) [p]
      | _ => throw "LIR: an extern's argument"
  | _, t => throw s!"LIR: an I/O extern at {t}"

/-! ### The conversion -/

/-- The value a closure of `k` answers when it is run. -/
def repK : LCTy → CM LTy
  | .ret a => pure a
  | .arr _ k => repK k
  | .top => pure .unit
  | k => pure (.thunk k)

/-- The type of a constant's answer after `n` of its arguments. -/
def satTy (t : LTy) : Nat → CM LTy
  | 0 => pure t
  | n + 1 => do
    let (_, r) ← answerOf t
    satTy r n

/-- The literal tables' code (`TExpr.litFn`), made once: `λi. byte i` over the environment
`(off, n)`, the `n` bytes at `off` in the program's data, `0` past the end.  `[spec §45]` -/
def litCode : CM Nat := do
  if let some c := (← get).lits then return c
  let fi ← reserveFn "literal"
  let o ← fresh i32T; let n ← fresh i32T; let i ← fresh i32T
  setFn fi { name := "literal", params := [o, n, i], body := .prim .litByte [o, n, i], ret := .int .w8 }
  let c ← addCode { kind := .lam, fns := [fi], ty := .arr i32T (.ret (.int .w8)) }
  modify fun s => { s with lits := some c }
  return c

/-- The number of arguments a constant takes before its operation runs; `none` at a node that is
not a constant. -/
def constArity : TExpr → Option Nat
  | .alloc .. | .free .. | .copy .. | .forgetImm .. | .forgetMut .. | .forgetUnk .. | .hostOp ..
  | .arrNew .. | .arrFree .. | .arrSize .. | .arrReplace .. | .arrLen .. | .arrGet .. | .arrCopy ..
  | .arrForget .. | .countFold .. | .countTry .. | .sliceGetM .. | .sliceLenM .. | .sliceSplitI ..
  | .sliceSplitM .. | .sliceReplaceM .. | .sliceSwapM .. | .dtor .. | .foldImm .. | .foldOwn ..
  | .foldReuse .. | .unfoldN .. | .allocS .. | .freeS .. | .iterate .. | .boundedFix .. => some 1
  | .swap .. | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap ..
  | .sliceBorrowM .. | .sliceBorrowI .. | .withborSM .. | .withborSI .. | .withborF2M ..
  | .withborF2I .. | .withbor1U .. | .withbor2U .. | .withbor3U .. | .withloadU ..
  | .sliceBorrowMU .. | .sliceBorrowIU .. => some 2
  | .sliceEmptyI .. | .sliceEmptyM .. => some 0
  | _ => none

/-- The nodes whose value is their child's: `ret`, a thunk of a λ-value, dereliction, the lifetime
box and the lifetime coercions, `ν`'s two coercions. -/
def transparent? : TExpr → Option TExpr
  | .bangE _ _ _ t | .boxI _ _ _ _ t | .boxE _ _ _ _ t | .immSub _ _ _ _ _ t | .mutSub _ _ _ _ _ t
  | .ofRet _ _ _ t | .ret _ _ _ t | .thunkV _ _ _ t | .bangThunkV _ _ _ t | .nuIn _ _ _ t
  | .nuOut _ _ _ t => some t
  | _ => none

/-- A function position's head through transparent nodes, and through a `use` whose body is a
constant (nothing is shared there). -/
def headOf : Nat → TExpr → TExpr
  | 0, t => t
  | f + 1, t => match transparent? t with
    | some c => headOf f c
    | none => match t with
      | .use _ _ _ _ _ _ b =>
        let h := headOf f b
        if (constArity h).isSome then h else t
      | _ => t

/-- The nodes of a typed term, to a bound. -/
def tsize : Nat → TExpr → Nat
  | 0, _ => 0
  | f + 1, t => 1 + (t.children.map (fun (_, c) => tsize f c)).foldl (· + ·) 0

/-- A `use` body small enough to be converted at its use when it is applied there: the old
backend's substitution of a small definition, with no copy of a large one (#509). -/
def inlineBound : Nat := 200

/-- A function position that is a λ once its lifetime abstractions are instantiated: `allEV`/`allE`
of `allI`, through transparent nodes and a small `use`; the λ, and the dead slots the `allI`s push.
Applying it is the λ's body at the arguments, with no closure made. -/
def lamOf : Nat → TExpr → Option (Nat × TExpr)
  | 0, _ => none
  | f + 1, t => match transparent? t with
    | some c => lamOf f c
    | none => match t with
      | .lam .. => some (0, t)
      | .use _ _ _ _ _ _ b => if tsize (inlineBound + 1) b ≤ inlineBound then lamOf f b else none
      | .allEV _ _ _ _ _ _ c | .allE _ _ _ _ _ _ c => match allIOf f c with
        | some body => (lamOf f body).map fun (k, l) => (k + 1, l)
        | none => none
      | _ => none
where
  allIOf : Nat → TExpr → Option TExpr
    | 0, _ => none
    | f + 1, t => match transparent? t with
      | some c => allIOf f c
      | none => match t with
        | .allI _ _ _ _ _ _ body => some body
        | .use _ _ _ _ _ _ b => if tsize (inlineBound + 1) b ≤ inlineBound then allIOf f b else none
        | _ => none

/-- The node is `unfold step`: through transparent nodes, the `unfoldN` constant applied to one
argument.  `[spec §45]` -/
def isUnfoldApp (t : TExpr) : Bool :=
  match headOf 64 t with
  | .lolliE _ _ _ _ _ _ tf => (headOf 64 tf matches .unfoldN ..)
  | _ => false

/-- The arguments of a spine of call-by-value applications, outermost first, with each split's
masks; and the function. -/
def spineOf : Nat → TExpr → List (Masks × TExpr) × TExpr
  | f + 1, .lolliE _ _ _ _ u ta tf =>
    let (as, h) := spineOf f tf
    ((u, ta) :: as, h)
  | _, t => ([], t)

mutual
/-- The type holds a closure. -/
def holdsClos : Nat → LTy → Bool
  | 0, _ => true
  | f + 1, t => match t with
    | .thunk _ => true
    | .pair a b | .sum a b => holdsClos f a || holdsClos f b
    | .mu a | .ref a | .imm a | .mut a | .fam a => holdsClos f a
    | _ => false
/-- A value of the type takes a closure as an argument: a higher-order function, or a value holding
one. -/
def takesClos : Nat → LTy → Bool
  | 0, _ => true
  | f + 1, t => match t with
    | .thunk k => takesClosK f k
    | .pair a b | .sum a b => takesClos f a || takesClos f b
    | _ => false
def takesClosK : Nat → LCTy → Bool
  | 0, _ => true
  | f + 1, k => match k with
    | .arr a k => holdsClos f a || takesClosK f k
    | .nu k => takesClosK f k
    | .amp k₁ k₂ => takesClosK f k₁ || takesClosK f k₂
    | .ret a => takesClos f a
    | .top => false
end

/-- The key of a `use`: the declaration, its type arguments and the elaborator's key. -/
def useKey (decl : Nat) (targs : List VTy) (info : TInfo) (j : Jdg) : String :=
  s!"{decl}|{", ".intercalate (targs.map ppVT)}|{reprStr info.key}|{ppJ j}"

/-- Rename every variable a term binds to a fresh one, and its free ones by `m`. -/
def renameTm (m : Std.HashMap Var Var) : Tm → CM Tm
  | .var x => return .var (m.getD x x)
  | .unit => pure .unit
  | .lit c => pure (.lit c)
  | .pair a b => return .pair (m.getD a a) (m.getD b b)
  | .inj r a => return .inj r (m.getD a a)
  | .clos c env => return .clos c (env.map fun x => m.getD x x)
  | .app f a => return .app (m.getD f f) (m.getD a a)
  | .app0 f => return .app0 (m.getD f f)
  | .sel f j => return .sel (m.getD f f) j
  | .call fn as => return .call fn (as.map fun x => m.getD x x)
  | .prim op as => return .prim op (as.map fun x => m.getD x x)
  | .letv x e b => do
    let x' ← freshLike x
    return .letv x' (← renameTm m e) (← renameTm (m.insert x x') b)
  | .letpair x y p b => do
    let x' ← freshLike x; let y' ← freshLike y
    return .letpair x' y' (m.getD p p) (← renameTm ((m.insert x x').insert y y') b)
  | .case s x b₁ y b₂ => do
    let x' ← freshLike x; let y' ← freshLike y
    return .case (m.getD s s) x' (← renameTm (m.insert x x') b₁) y' (← renameTm (m.insert y y') b₂)
  | .absurd s => return .absurd (m.getD s s)
  | .copy x x' b => do
    let x'' ← freshLike x'
    return .copy (m.getD x x) x'' (← renameTm (m.insert x' x'') b)
  | .drop x b => return .drop (m.getD x x) (← renameTm m b)

/-- The outside of the pure fragment. -/
def outside (t : TExpr) : CM α :=
  throw s!"LIR: `{ruleName t}` is outside the pure fragment (N2 and later)"

set_option maxHeartbeats 4000000 in
mutual
/-- **The conversion of a node** at its context: the term of its value. -/
def conv (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  readFact s!"{ruleName t}:node"
  match t with
  | .var _ _ i _ =>
    match ctx[i]? with
    | some (some x) => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: variable {i} is not live"
  | .unitI .. | .topI .. => return leaf ctx none .unit
  | .lit _ _ c => return leaf ctx none (.lit c)
  | .tensorI _ j _ _ u t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorI"
    let rT ← repJ j
    let .pair aT bT := rT | throw "LIR: a pair at a non-pair type"
    return pre (← bindTm (← conv fuel c₁ t₁) aT fun a => do
      bindTm (← conv fuel c₂ t₂) bT fun b => pure (.pair a b))
  | .sumI₁ _ j _ _ c => do
    let .sum aT _ ← repJ j | throw "LIR: an injection at a non-sum"
    bindTm (← conv fuel ctx c) aT fun a => pure (.inj false a)
  | .sumI₂ _ j _ _ c => do
    let .sum _ bT ← repJ j | throw "LIR: an injection at a non-sum"
    bindTm (← conv fuel ctx c) bT fun a => pure (.inj true a)
  | .thunkF _ j _ c | .bangThunkF _ j _ c => do
    let .thunk k ← repJ j | throw "LIR: a thunk at a non-closure type"
    mkClos "thunk" ctx k none (← repK k) fun ctx' => conv fuel (none :: ctx') c
  | .lam _ j A _ c => do
    let .thunk k ← repJ j | throw "LIR: a λ at a non-closure type"
    let (_, r) ← answerOf (.thunk k)
    mkClos "lam" ctx k (some (← vty A)) r fun ctx' => conv fuel ctx' c
  | .lamDead _ j _ _ c => do
    let .thunk k ← repJ j | throw "LIR: a λ at a non-closure type"
    let (_, r) ← answerOf (.thunk k)
    mkClos "lam" ctx k (some .unit) r fun ctx' => do
      match ctx' with
      | some p :: rest => return .drop p (← conv fuel (none :: rest) c)
      | _ => throw "LIR: a dead λ's parameter"
  | .allI _ _ _ _ _ _ c => do
    -- `Λ. M` is `M` (`allI_inst`)  [spec §44]: its body erases to a λ-value, so the binder's slot
    -- is dead and no instantiation runs code.
    unless c.isLam do throw "outside the pure fragment: a Λ whose body is not a λ-value (SPEC §44)"
    readFact "allI:body a λ-value"
    conv fuel (none :: ctx) c
  | .withI _ j _ _ tM tN => do
    let .thunk k ← repJ j | throw "LIR: a `&` at a non-closure type"
    let r₁ ← selTy (.thunk k) 0
    let r₂ ← selTy (.thunk k) 1
    readFact "withI:code kind"
    mkAmp "with" ctx k [r₁, r₂] [fun ctx' => conv fuel (none :: none :: ctx') tM,
      fun ctx' => conv fuel (none :: none :: ctx') tN]
  | .effLet _ _ A B S u tM tN => do
    match payTy (← rowPay S) with
    | none => convBind fuel ctx A u tM tN
    | some pT => do
      -- `M to x. N` at a row with abortive operations: `N` on a value, the abort handed on, `N`'s
      -- context dropped (`effLet`'s `hW`), the branch per call of SPEC §19 (`abort_to`).
      readFact "effLet:row"
      let (pre, c₁, c₂) ← splitCtx ctx u "effLet"
      let aT ← vty A
      let m ← fresh (.sum aT pT); let x ← fresh aT; let e ← fresh pT
      return pre (.letv m (← conv fuel c₁ tM)
        (.case m x (← conv fuel (some x :: c₂) tN) e (drops (live c₂) (.inj true e))))
  | .effSub _ _ S S' A c => do
    -- `[sub]`: the payload of `Σ` as one of `Σ'`.  [spec §48]
    readFact "effSub:rows"
    let p ← rowPay S; let q ← rowPay S'
    let a ← vty A
    bindTm (← conv fuel ctx c) (resTy a p) fun r => coerceRes a p q r
  | .effRaise _ _ S o _ c => do
    -- `raise`: the abort at its operation's summand, handed to the handler's join (`catch_abort`,
    -- `abort_absorbs`).  [spec §48]
    readFact "effRaise:op"
    modify fun st => { st with erased := st.erased.insert "raise" (st.erased.getD "raise" 0 + 1) }
    let p ← rowPay S
    let some j := payIdx p (o.n, o.i) | throw s!"LIR: a raise of ({o.n}, {o.i}) outside its row"
    bindTm (← conv fuel ctx c) (← vty o.A) fun v => injectPay p j v fun w => pure (.inj true w)
  | .effPerform _ _ S o c => do
    if o.n == divName then
      -- **`tick` under the runtime**: its clause `λ((), κ). κ next` resumes in tail position with
      -- the literal *next* (`tail_resumes`); `drive_reify_tick` (`Core/DivDrive.lean`) is the
      -- runtime's drive of `main`'s loop answering it so.  [spec §49]
      unless (← get).divRt do
        throw "LIR: a tick whose handler is not the runtime (a stored loop's `reify`, N3) is outside the pure fragment"
      readFact "effPerform:tick at the runtime"
      modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
      let p ← rowPay S
      return ← bindTm (← conv fuel ctx c) .unit fun v => do
        let u ← fresh .unit
        let nx ← fresh boolT
        match payTy p with
        | none => return .drop v (.letv u .unit (.inj false u))
        | some _ => return .drop v (.letv u .unit (.letv nx (.inj false u) (.inj false nx)))
    -- `perform` of a tail-resumptive clause: a direct call of the clause's work (`tail_resumes`,
    -- `TailResumesAt.subst_kappa`, `tail_clause_names`, `Checked.unhandledNames`).  [spec §48]
    let some (fi, ph) := (← get).works[(o.n, o.i.toNat)]?
      | throw s!"LIR: `effPerform` of ({o.n}, {o.i}) with no direct call is outside the pure fragment (N3)"
    readFact "effPerform:direct call"
    modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
    let p ← rowPay S
    unless ph.all fun k => (payIdx p k.1).isSome do
      throw s!"LIR: `effPerform` of ({o.n}, {o.i}) at a row that does not hold its clause's aborts is outside the pure fragment"
    let bT ← vty o.B
    bindTm (← conv fuel ctx c) (← vty o.A) fun v => do
      let r ← fresh (resTy bT ph)
      return .letv r (.call fi [v]) (← coerceRes bT ph p r)
  | .effThen _ _ A _ S SM SD u tM tN tD => do
    -- `M then x. N unwind D`: `N` on a value; on an abort the finaliser `D`, then the abort, or
    -- the finaliser's own, handed on (`then_ret`, `then_fin`, `unwind_prefix`).  [spec §48]
    readFact "effThen:rows"
    let (pre, c₁, c₂) ← splitCtx ctx u "effThen"
    let pm ← rowPay SM; let ps ← rowPay S; let pd ← rowPay SD
    let aT ← vty A
    match payTy pm with
    | none => return pre (← bindTm (← conv fuel c₁ tM) aT fun x => conv fuel (some x :: c₂) tN)
    | some pmT =>
      let m ← fresh (.sum aT pmT); let x ← fresh aT; let e ← fresh pmT
      let d ← fresh (resTy .unit pd)
      let dTm ← conv fuel (none :: c₂) tD
      let pass ← coercePay pm ps e fun e' => pure (.inj true e')
      let fin ← match payTy pd with
        | none => pure (Tm.letv d dTm (.drop d pass))
        | some pdT => do
          let w ← fresh .unit; let e₂ ← fresh pdT
          pure (Tm.letv d dTm (.case d w (.drop w pass) e₂
            (.drop e (← coercePay pd ps e₂ fun e' => pure (.inj true e')))))
      return pre (.letv m (← conv fuel c₁ tM) (.case m x (← conv fuel (some x :: c₂) tN) e fin))
  | .effHandleV _ _ S E fs n A R u ks _ _ tc te =>
    convHandle fuel ctx S E fs n A R u ks tc te
  | .effHandleVB _ _ S E fs n A R _ u ks _ _ tc te =>
    convHandle fuel ctx S E fs n A R u ks tc te
  | .bind _ _ A _ u tM tN => convBind fuel ctx A u tM tN
  | .force _ j i C => do
    match ctx[i]? with
    | some (some x) =>
      match C with
      | .ret _ | .eff .. => return leaf ctx (some i) (.app0 x)
      | _ => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: forced variable {i} is not live"
  | .app _ j i _ _ u tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "app"
    let some (some x) := c₂[i]? | throw s!"LIR: the argument {i} is not live"
    let rest := leaf c₂ (some i)
    match headOf 64 tM with
    | .lam _ _ _ _ body => return pre (rest (← conv fuel (some x :: c₁) body))
    | _ => do
      let f ← fresh (← repJ tM.jdg)
      return pre (rest (.letv f (← conv fuel c₁ tM) (.app f x)))
  | .proj₁ _ _ _ _ c | .proj₂ _ _ _ _ c => do
    let j := match t with | .proj₂ .. => 1 | _ => 0
    let fT ← repJ c.jdg
    bindTm (← conv fuel ctx c) fT fun f => pure (.sel f j)
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← conv fuel c₂ tM))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun p => do
      let x ← fresh aT; let y ← fresh bT
      return .letpair x y p (← conv fuel (some y :: some x :: c₂) tM))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← conv fuel (some x :: c₂) t₁) y (← conv fuel (some y :: c₂) t₂))
  | .zeroE _ _ _ u tV => do
    let (pre, c₁, _) ← splitCtx ctx u "zeroE"
    return pre (← bindTm (← conv fuel c₁ tV) .zero fun v => pure (.absurd v))
  | .allE _ _ _ _ _ _ c | .allEV _ _ _ _ _ _ c => do
    -- An instantiation is its operand.  [spec §44]
    readFact s!"{ruleName t}:erased"
    conv fuel ctx c
  | .roll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .roll [x])
  | .unroll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .unroll [x])
  | .lolliE .. => convSpine fuel ctx t
  | .use info j _ decl targs _ body => convUse fuel ctx info j decl targs body
  | .litFn _ _ bs _ => do
    let off := (← get).data.size
    modify fun s => { s with data := s.data ++ (bs.map (·.toUInt8)).toArray }
    let c ← litCode
    readFact "litFn:bytes"
    return leaf ctx none (← lit32 off.toUInt32 fun o => lit32 bs.length.toUInt32 fun n =>
      pure (.clos c [o, n]))
  | .divLit _ j op c inner => convDivLit fuel ctx j op c inner
  | .lendCell _ _ _ c => convLendCell fuel ctx t c
  | .walk _ _ _ read c => do
    -- A walk whose step reads its view at its index (`walkReadB`): its read has no test.  [spec §46]
    let old := (← get).walkRead
    if read then readFact "walk:read"
    modify fun s => { s with walkRead := read }
    let r ← conv fuel ctx c
    modify fun s => { s with walkRead := old }
    return r
  | .walkGet _ _ _ c => do
    -- The read of a walk's view at its index: below the bound (`walk_index_lt`), the bound the
    -- view's length, so the read answers its leaf (`walk_get_leaf`, `walk_get_split`).  [spec §46]
    let ok := (← get).walkRead
    let old := (← get).inRange
    modify fun s => { s with inRange := ok }
    let r ← conv fuel ctx c
    modify fun s => { s with inRange := old }
    return r
  | .selfCall _ _ _ _ c => conv fuel ctx c
  | .nuEta _ _ f s c => do
    -- The η-thunk of codata is the codata it observes (`nuEta_var`, `nuEta_unfold`)  [spec §45]:
    -- with no state, the variable itself; at `f = unfold step`, the call `f s`, made here.
    match ctx[f]?, s with
    | some (some fv), none =>
      readFact "nuEta:eta"
      return leaf ctx (some f) (.var fv)
    | some (some fv), some si =>
      match ctx[si]? with
      | some (some sv) =>
        if (← get).unfolds.contains fv then
          readFact "nuEta:unfold call"
          let others := (ctx.zipIdx.filter fun (_, k) => k != f && k != si).filterMap (·.1)
          return drops others (.app fv sv)
        else conv fuel ctx c
      | _ => conv fuel ctx c
    | _, _ => conv fuel ctx c
  | .effHandleT .. | .lendR .. | .lendLoopR .. | .nilDead .. | .divFuel ..
  | .reify .. | .letPoly .. => outside t
  | t =>
    match transparent? t with
    | some c => conv fuel ctx c
    | none =>
      match constArity t with
      | some _ => return leaf ctx none (← constClos fuel t)
      | none => throw s!"LIR: no conversion for `{ruleName t}`"

/-- `x <- M; N`: `M`'s value bound, then `N`. -/
def convBind (fuel : Nat) (ctx : Ctx) (A : VTy) (u : Masks) (tM tN : TExpr) : CM Tm := do
  let (pre, c₁, c₂) ← splitCtx ctx u "bind"
  let unf := isUnfoldApp tM
  return pre (← bindTm (← conv fuel c₁ tM) (← vty A) fun x => do
    if unf then
      readFact "bind:unfold step"
      modify fun st => { st with unfolds := st.unfolds.insert x }
    conv fuel (some x :: c₂) tN)

/-- The function `tF` applied to `a`: a λ's body at `a` (through transparent nodes and lifetime
abstractions, `lamOf`), or a closure call. -/
def applyTo (fuel : Nat) (ctx : Ctx) (tF : TExpr) (a : Var) : CM Tm := do
  match lamOf 64 tF with
  | some (k, .lam _ _ _ _ body) => conv fuel (some a :: (List.replicate k none ++ ctx)) body
  | _ => do
    let f ← fresh (← repJ tF.jdg)
    return .letv f (← conv fuel ctx tF) (.app f a)

/-- **`handle_n e with (h_ret, hs)`, erased**  `[spec §48]`. Read from the node: its name `n`, its
operations `E`, its clauses' kinds `ks`, its outer row `Σ` and the masks. Every clause must be
`abortive`, or `tail` with its direct call licensed (`CState.direct`); any other kind is a
stored-continuation site, left to the state machines (N3). The handled computation runs in place;
its value goes to `h_ret`, an abort of one of `n`'s operations to that operation's clause (the
handler's join: `catch_abort`), an abort of `Σ`'s handed on (`fwd_abort`). A tail-resumptive
clause is called where it is performed (`effPerform`). -/
def convHandle (fuel : Nat) (ctx : Ctx) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
    (n : UInt32) (A R : VTy) (u : Masks) (ks : List ClauseKinds.HKind) (tc te : TExpr) : CM Tm := do
  let direct := (← get).direct.getD n []
  readFact "effHandleV:kinds"
  for (k, j) in ks.zipIdx do
    match k.kind with
    | .abortive => pure ()
    | .tail =>
      unless direct[j]? == some true do
        throw s!"LIR: `effHandleV`: the clause {n}.{j} is tail-resumptive, but its direct call is not licensed (condition 2, or one closed clause at its nodes): outside the pure fragment"
    | .resumeOnce _ | .stored =>
      throw s!"LIR: `effHandleV`: the clause {n}.{j} is `{k.kind.tag}`, a stored-continuation site (N3): outside the pure fragment"
    | kd => throw s!"LIR: `effHandleV`: the clause {n}.{j} is `{kd.tag}`, whose rule is not built: outside the pure fragment"
  let (pre, c₁, c₂) ← splitCtx ctx u "effHandleV"
  -- The handler's pair, written in place: `h_ret` and each clause with its part of the context.
  let .tensorI _ _ _ _ uH tR tCs := tc
    | throw "LIR: `effHandleV`: a handler pair not written in place is outside the pure fragment"
  let (preH, cR, cCs) ← splitCtx c₁ uH "effHandleV"
  let mut parts : Array (Ctx × TExpr) := #[]
  let mut cur := cCs
  let mut tcur := tCs
  let mut preCs : Array (Tm → Tm) := #[]
  for _ in E do
    match tcur with
    | .tensorI _ _ _ _ uc c rest => do
      let (pc, cc, cr) ← splitCtx cur uc "effHandleV"
      preCs := preCs.push pc
      parts := parts.push (cc, c)
      cur := cr; tcur := rest
    | _ => throw "LIR: `effHandleV`: a clause tuple not written in place is outside the pure fragment"
  let tailCtx := cur
  -- The direct calls' functions, made at the first node of the name.
  for (k, j) in ks.zipIdx do
    if k.kind == .tail then
      let some (cc, c) := parts[j]? | throw "LIR: a clause"
      let some o := E[j]? | throw "LIR: an operation"
      ensureWork fuel n j cc.length S o c
  let ctxs : List Ctx := cR :: parts.toList.map (·.1) ++ [tailCtx]
  let dropAll (keep : Option Nat) (b : Tm) : Tm :=
    drops ((ctxs.zipIdx.filter fun (_, i) => some i != keep).flatMap fun (c, _) => live c) b
  let pt ← rowPay (Row.ofEff n E 0 fs ++ S)
  let ps ← rowPay S
  let aT ← vty A
  modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
  let retArm (a : Var) : CM Tm := do return dropAll (some 0) (← applyTo fuel cR tR a)
  let wrap (b : Tm) : Tm := pre (preH (preCs.foldr (fun f t => f t) b))
  match payTy pt with
  | none => return wrap (← bindTm (← conv fuel c₂ te) aT retArm)
  | some ptT =>
    readFact "effHandleV:join"
    let b ← fresh (.sum aT ptT); let a ← fresh aT; let e ← fresh ptT
    let arms ← casePay pt e fun j v => do
      let some (key, _) := pt[j]? | throw "LIR: a payload's summand"
      if key.1 == n then
        let idx := key.2.toNat
        let some (cc, c) := parts[idx]? | throw "LIR: an abortive clause"
        return dropAll (some (idx + 1)) (← applyTo fuel cc c v)
      else
        let some j' := payIdx ps key | throw s!"LIR: an abort of {key} outside the handler's row"
        return dropAll none (← injectPay ps j' v fun w => pure (.inj true w))
    return wrap (.letv b (← conv fuel c₂ te) (.case b a (← retArm a) e arms))

/-- **A tail-resumptive clause's work**, the function a `perform` of its operation calls
(`[spec §48]`, `tail_resumes`): the clause `λp. let (x, κ) = p; M` with each resume of `κ`
replaced by its answer (`TailResumesAt 0 M M'`, which the clause's kind gives,
`classifyHandler_sound`). It takes the argument `x` and answers the operation's answer, at the
payload of the handler's outer row `Σ`. Made once per operation. -/
def ensureWork (fuel : Nat) (n : UInt32) (j : Nat) (depth : Nat) (S : Row)
    (o : Qual × VTy × VTy) (c : TExpr) : CM Unit := do
  if (← get).works.contains (n, j) then return
  match c.unUse with
  | .bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM)) => do
    readFact "effHandleV:tail work"
    let x ← fresh (← vty o.2.1)
    let kv ← fresh .unit
    let ph ← rowPay S
    let bT ← vty o.2.2
    let fi ← reserveFn s!"clause {n}.{j}"
    modify fun st => { st with works := st.works.insert (n, j) (fi, ph) }
    let body ← convWork fuel 0 ph (some kv :: some x :: none :: List.replicate depth none) tM
    -- `κ`'s slot holds a unit: every resume of it is its answer, and it is dropped there.
    setFn fi { name := s!"clause {n}.{j}", params := [x], body := .letv kv .unit body,
               ret := resTy bT ph }
  | _ => throw s!"LIR: the clause {n}.{j} is not `λp. let (x, κ) = p; M`"

/-- The variable a term answers through the nodes that keep their premise's value (`ret`,
`unbox`, `[sub]`, …): the alias `return κ`. -/
def aliasOf : Nat → TExpr → Option Nat
  | 0, _ => none
  | f + 1, t => match t with
    | .var _ _ i _ => some i
    | .effSub _ _ _ _ _ c => aliasOf f c
    | t => match transparent? t with
      | some c => aliasOf f c
      | none => none

/-- **The clause's body with its resumes removed** (`TailResumesAt`), `κ` in the slot `k`: on
each path, through `[⊕E]`, `[⊗E]`, `[1E]`, `[let]` and `[sub]`, to the resume `κ.1 y`
(`resumeB`), whose value is `y`; the right unit `x <- κ.1 y; return x` (`tailLeafB`,
`returns0B`) is the resume; an alias `κ' <- return κ` moves `κ` to its binder. An abort of the
path's `[let]`s is handed on at the handler's row's payload `ph`. -/
def convWork (fuel : Nat) (k : Nat) (ph : Pay) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let answer (y : Var) : CM Tm := do
    match payTy ph with
    | none => return .var y
    | some _ => return .inj false y
  if resumeB k t then
    match t.unSub with
    | .app _ _ y _ _ u _ => do
      let (pre, c₁, c₂) ← splitCtx ctx u "app"
      let some (some yv) := c₂[y]? | throw "LIR: a resume's answer is not live"
      return pre (drops (live c₁) (leaf c₂ (some y) (← answer yv)))
    | _ => throw "LIR: a resume"
  match t with
  | .bind _ _ A _ u tM tN | .effLet _ _ A _ _ u tM tN =>
    let row := match t with | .effLet _ _ _ _ S .. => some S | _ => none
    if tailLeafB k tM && returns0B tN then
      -- The right unit: the resume's answer is the clause's.
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      return pre (drops (live c₂) (← convWork fuel k ph c₁ tM))
    else if aliasOf 64 tM == some k then
      -- `κ' <- return κ`: the alias's slot holds `κ`.
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let some (some kv) := c₁[k]? | throw "LIR: an alias of a continuation that is not live"
      return pre (leaf c₁ (some k) (← convWork fuel 0 ph (some kv :: c₂) tN))
    else
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let aT ← vty A
      let p ← match row with | some S => rowPay S | none => pure []
      match payTy p with
      | none =>
        return pre (← bindTm (← conv fuel c₁ tM) aT fun x => convWork fuel (k + 1) ph (some x :: c₂) tN)
      | some pT =>
        let m ← fresh (.sum aT pT); let x ← fresh aT; let e ← fresh pT
        let pass ← coercePay p ph e fun e' => pure (.inj true e')
        return pre (.letv m (← conv fuel c₁ tM)
          (.case m x (← convWork fuel (k + 1) ph (some x :: c₂) tN) e (drops (live c₂) pass)))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← convWork fuel (k + 1) ph (some x :: c₂) t₁)
        y (← convWork fuel (k + 1) ph (some y :: c₂) t₂))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun pv => do
      let x ← fresh aT; let y ← fresh bT
      return .letpair x y pv (← convWork fuel (k + 2) ph (some y :: some x :: c₂) tM))
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← convWork fuel k ph c₂ tM))
  | .effSub _ _ _ _ _ c => convWork fuel k ph ctx c
  | _ => throw s!"LIR: a tail-resumptive clause's path at `{ruleName t}` ends in no resume"

/-- A spine of `lolliE` nodes: its arguments evaluated outermost first, then its function: a
constant's operation (`expand`), a λ's body (β), or a closure call. -/
def convSpine (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let (as, h) := spineOf 4096 t
  let resT ← repJ t.jdg
  -- A borrow whose callback is a λ written there: the callback's body at the borrow, with no
  -- closure made (the λ-value's construction does nothing).
  match as, cbConst (headOf 64 h) with
  | [(u₁, cb), (u₂, x)], true =>
    match lamOf 64 cb with
    | some (k, .lam _ _ _ _ body) => do
      readFact "lolliE:callback beta"
      let (pre₁, cA, cF) ← splitCtx ctx u₁ "lolliE"
      let (pre₂, cX, cH) ← splitCtx cF u₂ "lolliE"
      let xT ← repJ x.jdg
      let cbT ← repJ cb.jdg
      return pre₁ (pre₂ (← bindTm (← conv fuel cX x) xT fun xv => do
        let body ← expandCb fuel (headOf 64 h) xv cbT
          (fun b => conv fuel (some b :: (List.replicate k none ++ cA)) body) resT
        return leaf cH none body))
    | _ => go fuel ctx as [] h resT
  | _, _ => go fuel ctx as [] h resT
where
  cbConst : TExpr → Bool
    | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap .. | .sliceBorrowM ..
    | .sliceBorrowI .. | .withborSM .. | .withborSI .. | .withborF2M .. | .withborF2I ..
    | .withbor1U .. | .withbor2U .. | .withbor3U .. | .withloadU .. | .sliceBorrowMU ..
    | .sliceBorrowIU .. => true
    | _ => false
  go (fuel : Nat) (ctx : Ctx) : List (Masks × TExpr) → List Var → TExpr → LTy → CM Tm
    | (u, ta) :: rest, vs, h, resT => do
      let (pre, cA, cF) ← splitCtx ctx u "lolliE"
      let aT ← repJ ta.jdg
      return pre (← bindTm (← conv fuel cA ta) aT fun a => go fuel cF rest (a :: vs) h resT)
    | [], vs, h, resT => do
      -- `vs` holds the arguments innermost first: the order they apply in.
      let hd := headOf 64 h
      match constArity hd with
      | some n =>
        if vs.length < n then
          let f ← fresh (← repJ h.jdg)
          return leaf ctx none (.letv f (← constClos fuel hd) (← applyAll f vs))
        let first := vs.take n
        let more := vs.drop n
        if more.isEmpty then return leaf ctx none (← expand fuel hd first resT)
        let r ← fresh (← satTy (← repJ hd.jdg) n)
        return leaf ctx none (.letv r (← expand fuel hd first (← tyOf r)) (← applyAll r more))
      | none =>
        match lamOf 64 h, vs with
        | some (k, .lam _ lj _ _ body), a :: more => do
          readFact "lolliE:beta"
          let (_, r) ← answerOf (← repJ lj)
          let ctx' := some a :: (List.replicate k none ++ ctx)
          if more.isEmpty then conv fuel ctx' body
          else bindTm (← conv fuel ctx' body) r fun g => applyAll g more
        | _, _ => do
          let f ← fresh (← repJ h.jdg)
          return .letv f (← conv fuel ctx h) (← applyAll f vs)

/-- The lend of a cell allocated for it (`TExpr.lendCell`, `withbor (alloc v) cb`, `lendCellB`):
as a spine, its cell's allocation `allocLent`, which the frame pass may place in the frame. -/
def convLendCell (fuel : Nat) (ctx : Ctx) (t inner : TExpr) : CM Tm := do
  let (as, h) := spineOf 8 inner
  match as with
  | [(u₁, cb), (u₂, aApp)] =>
    let (bs, ah) := spineOf 8 aApp
    match bs, headOf 64 ah with
    | [(u₃, v)], .alloc .. => do
      readFact "lendCell:cell"
      let (pre₁, c₁, cF) ← splitCtx ctx u₁ "lolliE"
      let cbv ← fresh (← repJ cb.jdg)
      let cbTm ← conv fuel c₁ cb
      let (pre₂, c₂, cH) ← splitCtx cF u₂ "lolliE"
      let (pre₃, c₃, cA) ← splitCtx c₂ u₃ "lolliE"
      let vv ← fresh (← repJ v.jdg)
      let vTm ← conv fuel c₃ v
      let cell ← fresh (← repJ aApp.jdg)
      let body ← expand fuel (headOf 64 h) [cell, cbv] (← repJ t.jdg)
      return pre₁ (.letv cbv cbTm (pre₂ (pre₃ (.letv vv vTm (leaf cA none
        (.letv cell (.prim .allocLent [vv]) (leaf cH none body)))))))
    | _, _ => conv fuel ctx inner
  | _ => conv fuel ctx inner

/-- A `use` of a `def`: its body's term made once per key, instantiated at each later use. -/
def convUse (fuel : Nat) (ctx : Ctx) (info : TInfo) (j : Jdg) (decl : Nat) (targs : List VTy)
    (body : TExpr) : CM Tm := do
  let key := useKey decl targs info j
  let slots : List (Nat × Var) := ctx.zipIdx.filterMap fun (s, i) => s.map (i, ·)
  -- A body that takes a closure is specialised to each use, as it is to each set of argument codes
  -- (docs/compiler.md §3.1): its codes would join the closures of every use otherwise.
  if takesClos 64 (← repJ j) then
    readFact "use:per-use body"
    return ← conv fuel ctx body
  match (← get).uses[key]? with
  | some tp =>
    -- The slots the template reads must be live here; any other live slot is dropped.
    let mut m : Std.HashMap Var Var := {}
    let mut ok := true
    for (i, x) in tp.slots do
      match ctx[i]? with
      | some (some y) => m := m.insert x y
      | _ => ok := false
    if ok then
      readFact "use:key, shared"
      let kept := tp.slots.map (·.1)
      let extra := slots.filter fun (i, _) => !kept.contains i
      return drops (extra.map (·.2)) (← renameTm m tp.tm)
    conv fuel ctx body
  | none =>
    let tm ← conv fuel ctx body
    modify fun s => { s with uses := s.uses.insert key ⟨slots, tm⟩ }
    readFact "use:key"
    return tm

/-- A division by a literal at which it cannot fail (`TExpr.divLit`): the dividend, then the
operation with no error arm. The node is over `(λa. B) e` (`divLitB`): `e` is the typed term's
bound computation. -/
def convDivLit (fuel : Nat) (ctx : Ctx) (j : Jdg) (op : HostOp) (c : IntLit) (inner : TExpr) :
    CM Tm := do
  let rT ← repJ j
  match peelRet inner with
  | .bind _ _ A _ u tM _ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "bind"
    let aT ← vty A
    readFact "divLit:divisor"
    return pre (leaf c₂ none (← bindTm (← conv fuel c₁ tM) aT fun a => do
      let d ← fresh (match c with | .u8 _ => .int .w8 | .i64 _ => .int .w64 | _ => i32T)
      return .letv d (.lit c) (.prim (.divLit op) [a, d])))
  | _ => conv fuel ctx inner
where
  peelRet : TExpr → TExpr
    | .ofRet _ _ _ t | .ret _ _ _ t => peelRet t
    | t => t

/-- A constant as a value: a closure of a code that applies it, one argument at a time. -/
def constClos (fuel : Nat) (c : TExpr) : CM Tm := do
  let some n := constArity c | throw "LIR: not a constant"
  let cT ← repJ c.jdg
  if n == 0 then return ← expand fuel c [] cT
  curry fuel c cT [] n
where
  curry (fuel : Nat) (c : TExpr) (t : LTy) (got : List Var) : Nat → CM Tm
    | 0 => throw "LIR: a constant of no arguments"
    | k + 1 => do
      let .thunk ck := t | throw s!"LIR: a constant at a non-function type {t}"
      let (some aT, rT) ← answerOf t | throw "LIR: a constant takes no argument"
      let ctx : Ctx := got.reverse.map some
      mkClos "const" ctx ck (some aT) rT fun ctx' => do
        let got' := (ctx'.filterMap id).reverse
        if k == 0 then expand fuel c got'.reverse.reverse rT
        else curry fuel c rT got' k

/-- **An unwinding borrow** (`withborUE d`, SPEC §19): `(f [] r) then b. (r, b) unwind d r`. The
owner lent as `genLend` does; the callback's value `b` gives `(r, b)`; its abort ends the lend, runs
the finaliser `d` on the owner, and is handed on (`then_fin`).  `[spec §48]` -/
def genLendU (fuel : Nat) (op : Op) (src : Var) (cbT : LTy) (call : Var → CM Tm) (td : TExpr) :
    CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let (some bT, rT) ← answerOf cbT | throw "LIR: a borrow's callback takes no borrow"
  match rT with
  | .sum vT eT => do
    readFact "withborU:finaliser"
    let pr ← fresh (.pair (← tyOf src) bT)
    let o ← freshLike src; let b ← fresh bT
    let r ← fresh rT
    let v ← fresh vT; let e ← fresh eT
    let q ← fresh (.pair (← tyOf src) vT)
    let u ← fresh .unit
    let fin ← match constArity (headOf 64 td) with
      | some 1 => expand fuel (headOf 64 td) [o] .unit
      | _ => throw "LIR: an unwinding borrow's finaliser that is not a constant is outside the pure fragment"
    return .letv pr (.prim op [src]) (.letpair o b pr (.letv r (← call b)
      (.case r v (.letv q (.pair o v) (.inj false q)) e (.letv u fin (.drop u (.inj true e))))))
  | _ => genLend op src cbT call

/-- A borrowing constant applied to its first argument `x`, its callback's call given by `call`. -/
def expandCb (_fuel : Nat) (c : TExpr) (x : Var) (cbT : LTy) (call : Var → CM Tm) (resT : LTy) :
    CM Tm := do
  readFact s!"{ruleName c}:expand"
  match c with
  | .withbor1 .. | .withbor2 .. | .sliceBorrowM .. | .sliceBorrowI .. => genLend .lend x cbT call
  | .withbor3 .. => genLend .relend x cbT call
  | .withload .. => genWithload x cbT call
  | .withswap .. => genWithswap x cbT call
  | .withborSM .. | .withborSI .. | .withborF2M .. | .withborF2I .. => genLendTree x cbT call
  | .withbor1U _ _ _ _ _ _ td | .withbor2U _ _ _ _ _ _ td | .sliceBorrowMU _ _ _ _ _ _ td
  | .sliceBorrowIU _ _ _ _ _ _ td => genLendU _fuel .lend x cbT call td
  | .withbor3U _ _ _ _ _ _ _ td => genLendU _fuel .relend x cbT call td
  | .withloadU .. => genWithload x cbT call
  | c => throw s!"LIR: `{ruleName c}` is not a borrow (answer {resT})"

/-- **A constant applied to its arguments**, `args` in the order they apply, its answer of type
`resT`. -/
def expand (fuel : Nat) (c : TExpr) (args : List Var) (resT : LTy) : CM Tm := do
  readFact s!"{ruleName c}:expand"
  match c, args with
  | .alloc .., [v] => return .prim .alloc [v]
  | .free .., [x] => return .prim .free [x]
  | .swap .., [x, v] => return .prim .swap [x, v]
  | .copy .., [x] | .arrCopy .., [x] => dup x fun x x' => pure (.pair x x')
  | .forgetImm .., [x] | .forgetMut .., [x] | .forgetUnk .., [x] | .arrForget .., [x] =>
    return .drop x .unit
  | .dtor _ _ A, [x] => do readFact "dtor:type"; genDtor 64 A x
  | .hostOp _ _ op, [x] => return .prim (.host op) [x]
  | .arrNew _ j _, [p] => do
    let (pT, aT) ← arrowOf (← repJ j)
    let .pair _ fT := pT | throw "LIR: array_new's argument"
    genTab aT fT p
  | .arrFree _ j _, [p] => do
    let (pT, _) ← arrowOf (← repJ j)
    let .pair fT aT := pT | throw "LIR: array_free's argument"
    genArrFree fT aT p
  | .arrSize .., [a] | .sliceLenM .., [a] => return .prim .size [a]
  | .arrLen .., [v] => return .prim .len [v]
  | .arrReplace .., [p] | .sliceReplaceM .., [p] =>
    letpairM p fun a r => letpairM r fun i x => do
      readFact s!"{ruleName c}:slot swap"
      return .prim .replace [a, i, x]
  | .arrGet .., [p] | .sliceGetM .., [p] => do
    let inRange := (← get).inRange
    if inRange then readFact s!"{ruleName c}:in range"
    letpairM p fun v i => pure (.prim (.idx (!inRange)) [v, i])
  | .sliceSplitI .., [p] | .sliceSplitM .., [p] =>
    letpairM p fun v i => pure (.prim (.split true) [v, i])
  | .sliceEmptyI .., [] | .sliceEmptyM .., [] => return .prim .emptyFam []
  | .sliceSwapM .., [p] =>
    letpairM p fun v r => letpairM r fun i k => pure (.prim .swapSlots [v, i, k])
  | .countFold _ j _, [p] => do
    let (pT, sT) ← arrowOf (← repJ j)
    let .pair fT _ := pT | throw "LIR: count_fold's argument"
    genCount fT sT p
  | .countTry _ j _ _, [p] => do
    let (pT, rT) ← arrowOf (← repJ j)
    let .pair fT _ := pT | throw "LIR: count_try's argument"
    let .sum sT eT := rT | throw "LIR: count_try's answer"
    genCountTry fT sT eT p
  | .iterate _ j S _ _ _, [p] => do
    unless (← get).divRt do
      throw "LIR: `iterate` whose ticks the runtime does not answer (a stored loop's `reify`, N3) is outside the pure fragment"
    let (pT, rT) ← arrowOf (← repJ j)
    let .pair fT _ := pT | throw "LIR: iterate's argument"
    readFact "iterate:row"
    genIter fT rT (← rowPay S) p
  | .boundedFix _ j _ _, [p] => do
    let (some pT, _) ← answerOf (← repJ j) | throw "LIR: bounded_fix takes no argument"
    let .pair sT _ := pT | throw "LIR: bounded_fix's argument"
    readFact "boundedFix:budget"
    genFix sT p
  | .withbor1 .., [x, cb] | .withbor2 .., [x, cb] | .sliceBorrowM .., [x, cb]
  | .sliceBorrowI .., [x, cb] => genLend .lend x (← tyOf cb) (callCb cb)
  | .withbor3 .., [m, cb] => genLend .relend m (← tyOf cb) (callCb cb)
  | .withload .., [x, cb] => genWithload x (← tyOf cb) (callCb cb)
  | .withswap .., [m, f] => genWithswap m (← tyOf f) fun old => pure (.app f old)
  | .allocS .., [v] => allocTree v resT
  | .freeS _ j _, [v] => do
    let (_, vT) ← arrowOf (← repJ j)
    freeTree v vT
  | .withborSM .., [x, cb] | .withborSI .., [x, cb] | .withborF2M .., [x, cb]
  | .withborF2I .., [x, cb] => genLendTree x (← tyOf cb) (callCb cb)
  | .withbor1U _ _ _ _ _ _ td, [x, cb] | .withbor2U _ _ _ _ _ _ td, [x, cb]
  | .sliceBorrowMU _ _ _ _ _ _ td, [x, cb] | .sliceBorrowIU _ _ _ _ _ _ td, [x, cb] =>
    genLendU fuel .lend x (← tyOf cb) (callCb cb) td
  | .withbor3U _ _ _ _ _ _ _ td, [m, cb] => genLendU fuel .relend m (← tyOf cb) (callCb cb) td
  | .withloadU .., [x, cb] => genWithload x (← tyOf cb) (callCb cb)
  | .foldOwn _ _ F _, [g] | .foldReuse _ _ F _, [g] => do
    let k : FoldKind := match c with | .foldReuse .. => .reuse | _ => .own
    let .thunk fk := resT | throw "LIR: a fold's answer is not a closure"
    let (some muT, R) ← answerOf resT | throw "LIR: a fold takes no structure"
    readFact s!"{ruleName c}:shape"
    let (recV, _) ← genFoldFns k F muT muT (← tyOf g)
    mkClos "fold" [some g] fk (some muT) R fun ctx' => do
      match ctx' with
      | some x :: some g' :: _ => return .call recV [g', x]
      | _ => throw "LIR: a fold's environment"
  | .foldImm _ _ F y _ _, [g] => do
    -- The answer's `∀'y` is erased (SPEC §44): a closure on the borrow.
    let .thunk fk := resT | throw "LIR: a fold's answer is not a closure"
    let (some lT, R) ← answerOf resT | throw "LIR: fold_imm takes no borrow"
    let .imm cellT := lT | throw "LIR: fold_imm's argument is not a borrow"
    let muT ← vty (VTy.immReborrow (.var y) (.mu F.ty))
    readFact s!"{ruleName c}:shape"
    let (_, recL) ← genFoldFns .imm F muT cellT (← tyOf g)
    mkClos "fold_imm" [some g] fk (some lT) R fun ctx' => do
      match ctx' with
      | some l :: some g' :: _ => return .call recL [g', l]
      | _ => throw "LIR: fold_imm's environment"
  | .unfoldN _ _ C _, [g] => do
    let .thunk uk := resT | throw "LIR: unfold's answer is not a closure"
    let (some sT, _) ← answerOf resT | throw "LIR: unfold takes no state"
    let obs ← genUnfold (← cty C) (← tyOf g) sT
    mkClos "unfold" [some g] uk (some sT) (.thunk (.nu (← cty C))) fun ctx' => do
      match ctx' with
      | some st :: some g' :: _ => return .clos obs [g', st]
      | _ => throw "LIR: unfold's environment"
  | c, _ => throw s!"LIR: `{ruleName c}` applied to {args.length} arguments"
end


/-- The clauses of a handler pair written in place, `(h_ret, (c₀, (c₁, … ())))`: `n` of them. -/
def clausesOf : Nat → TExpr → List TExpr
  | 0, _ => []
  | n + 1, .tensorI _ _ _ _ _ c rest => c :: clausesOf n rest
  | _, _ => []

/-- **The directly called clauses' functions, made first** (`ensureWork`): a `perform` may be
converted before its handler's node (a function made before the `handle` and called inside it).
Each tail-resumptive clause whose direct call is licensed, at the first `handle` node of its
name, with the depth of the node's context.  `[spec §48]` -/
def prepWorks (fuel : Nat) (depth : Nat) (t : TExpr) : CM Unit := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let here : Option (Row × List (Qual × VTy × VTy) × UInt32 × List ClauseKinds.HKind × TExpr) :=
    match t with
    | .effHandleV _ _ S E _ n _ _ _ ks _ _ tc _ => some (S, E, n, ks, tc)
    | .effHandleVB _ _ S E _ n _ _ _ _ ks _ _ tc _ => some (S, E, n, ks, tc)
    | _ => none
  if let some (S, E, n, ks, .tensorI _ _ _ _ _ _ tCs) := here then
    let direct := (← get).direct.getD n []
    let cs := clausesOf E.length tCs
    for (k, j) in ks.zipIdx do
      if k.kind == .tail && direct[j]? == some true then
        if let (some c, some o) := (cs[j]?, E[j]?) then
          ensureWork (1 <<< 22) n j depth S o c
  for (sc, c) in t.children do
    let d := match sc with | .push k => depth + k | .fresh k => k
    prepWorks fuel d c

/-! ### `main` -/

/-- Take the capabilities back from `main`'s value `(caps, a)` (`ncaps` of them, right-nested):
each cell freed with its contents, and `a` the program's value. -/
def epilogue (r : Var) (ncaps : Nat) : CM Tm := do
  if ncaps == 0 then return .var r
  letpairM r fun caps a => do
    let rec split : Nat → Var → CM (List Var × (Tm → Tm))
      | 0, _ => pure ([], id)
      | 1, v => pure ([v], id)
      | k + 1, v => do
        let .pair xT rT := (← tyOf v) | throw "LIR: main's capabilities"
        let x ← fresh xT; let rest ← fresh rT
        let (xs, wrap) ← split k rest
        pure (x :: xs, fun t => .letpair x rest v (wrap t))
    let (xs, wrap) ← split ncaps caps
    let mut body : Tm := .var a
    for x in xs.reverse do
      let .ref cT := (← tyOf x) | throw "LIR: a capability that is not a cell"
      let c ← fresh cT
      body := .letv c (.prim .free [x]) (.drop c body)
    return wrap body

/-- Drive a loop (SPEC §11, §14): observe `next` until it finishes, its value the program's. -/
def genDrive (lT : LTy) : CM Nat := do
  let fi ← reserveFn "drive"
  let l ← fresh lT
  let rT ← selTy lT 0
  let .sum vT nT := rT | throw "LIR: main's loop does not answer a sum"
  let r ← fresh rT
  let v ← fresh vT; let l' ← fresh nT
  setFn fi { name := "drive", params := [l], ret := vT,
             body := .letv r (.sel l 0) (.case r v (.var v) l' (.call fi [l'])) }
  return fi

/-- `main`'s value as `reify` of its body (SPEC §47: a `main` that loops is the loop value of its
body): through the nodes that keep their child's value, the `reify` constant applied to the
body's thunk. Its split's masks, the thunk, and the `reify` node's row `Σ`, result `B` and
residual `R`.  `[spec §49]` -/
def mainReify? (t : TExpr) : Option (Masks × TExpr × Row × VTy × VTy) :=
  match peel 64 t with
  | .lolliE _ _ _ _ u ta tf => match headOf 64 tf with
    | .reify _ _ S B R _ => some (u, ta, S, B, R)
    | _ => none
  | _ => none
where
  peel : Nat → TExpr → TExpr
    | 0, t => t
    | f + 1, t => match transparent? t with
      | some c => peel f c
      | none => t

/-- **The LIR of `main`**: its externs bound to their implementations (`exts`, in declaration
order; the context's slot `i` is extern `n − 1 − i`), its typed term converted, and its
capabilities taken back. With `loops`, `main`'s value is a loop, driven until it finishes. -/
def convMain (exts : List Ext) (ctx : List (VTy × Bool)) (t : TExpr) (C : CTy) (ncaps : Nat)
    (loops : Bool) : CM (Tm × LTy) := do
  let n := ctx.length
  let mut binds : List (Tm → Tm) := []
  let mut cx : Array (Option Var) := #[]
  for ((A, liveS), i) in ctx.zipIdx do
    if !liveS then cx := cx.push none; continue
    let aT ← vty A
    let x ← fresh aT
    let some e := exts[n - 1 - i]? | throw "LIR: main's context has a slot no extern gives"
    match e with
    | .cap fd => do
      let l ← fresh i32T
      let k := (← get).statics.size
      modify fun s => { s with statics := s.statics.push k }
      binds := (fun b => .letv l (.lit (.i32 fd.toUInt32)) (.letv x (.prim (.staticCell k) [l]) b)) :: binds
    | .clock => do
      let l ← fresh (.int .w64)
      let k := (← get).statics.size
      modify fun s => { s with statics := s.statics.push k }
      binds := (fun b => .letv l (.lit (.i64 0)) (.letv x (.prim (.staticCell k) [l]) b)) :: binds
    | .io op => do
      let c ← ioClos 8 op aT
      binds := (fun b => .letv x c b) :: binds
    cx := cx.push (some x)
  prepWorks (1 <<< 22) cx.size t
  if loops then
    if let some (u, ta, S, B, R) := mainReify? t then
      return ← runtimeMain cx.toList u ta S B R binds
  let body ← conv (1 <<< 22) cx.toList t
  let mT ← repJ (.comp C)
  let r ← fresh mT
  let (tm, resT) ← if loops then do
      let d ← genDrive mT
      let fT ← tyOf (← fresh (← selTy mT 0)) -- the loop's `next` answer
      let .sum vT _ := fT | throw "LIR: main's loop"
      let v ← fresh vT
      let ep ← epilogue v ncaps
      pure (Tm.letv r body (.letv v (.call d [r]) ep), ← resultTy vT)
    else pure (Tm.letv r body (← epilogue r ncaps), ← resultTy mT)
  return (binds.foldl (fun t f => f t) tm, resT)
where
  resultTy (t : LTy) : CM LTy := do
    if ncaps == 0 then return t
    match t with
    | .pair _ a => pure a
    | t => throw s!"LIR: main's value with capabilities is not a pair: {t}"
  /-- **`main`'s loop under the runtime**  `[spec §49]`: `main`'s value is `reify` of its body
  `t ()`, which the runtime drives with *next* until it finishes (SPEC §11). The drive answers
  *next* to every tick of the body (`drive_reify_tick`, `Core/DivDrive.lean`), so the program is
  the body run with each tick answered *next* where it is performed (`effPerform`'s tick):
  `inl b` finishes with `b` (`drive_reify_done`); `inr r` is a loop closed with its residual,
  which the drive observes without end (`drive_reify_closed`), a run that does not finish. -/
  runtimeMain (cx : Ctx) (u : Masks) (ta : TExpr) (S : Row) (B R : VTy)
      (binds : List (Tm → Tm)) : CM (Tm × LTy) := do
    readFact "reify:main, at the runtime"
    modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
    let p ← rowPay S
    if (payTy p).isSome then
      throw "LIR: `main`'s loop at a row with aborts (the platform's handler) is outside the pure fragment"
    let (pre, cA, cF) ← splitCtx cx u "lolliE"
    let unitV ← fresh .unit
    let body ← applyTo (1 <<< 22) cA ta unitV
    let bT ← vty B; let rT ← vty R
    let r ← fresh (.sum bT rT)
    let b ← fresh bT; let x ← fresh rT
    let resT ← resultTy bT
    let ep ← epilogue b ncaps
    -- The loop `closed r`, which every observation skips: it holds the residual, and does not
    -- finish.
    let spin ← reserveFn "closed"
    let x₁ ← fresh rT
    setFn spin { name := "closed", params := [x₁], body := .call spin [x₁], ret := resT }
    let tm := pre (leaf cF none (.letv unitV .unit (.letv r body
      (.case r b ep x (.call spin [x])))))
    return (binds.foldl (fun t f => f t) tm, resT)

/-- Convert a checked `main` to a program. -/
def convertProg (exts : List Ext) (ctx : List (VTy × Bool)) (t : TExpr) (C : CTy) (ncaps : Nat)
    (loops : Bool) (census : Bool := false) (direct : Std.HashMap UInt32 (List Bool) := {})
    (divRt : Bool := false) : Except String (Prog × CState) := do
  let ((m, mT), s) ← (convMain exts ctx t C ncaps loops).run { census, direct, divRt }
  return ({ fns := s.fns, codes := s.codes, main := m, mainTy := mT, ty := s.ty, data := s.data,
            statics := s.statics.size }, s)

end Backend2
