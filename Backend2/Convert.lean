import Std.Data.HashMap
import Backend2.Syntax
import Backend2.Debug

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
  lits : Array (Nat × Nat × Nat) := #[]
  /-- What the conversion read of the typed term, by rule and fact (`bcc lir --census`). -/
  reads : Std.HashMap String Nat := {}
  /-- The static words for the capabilities' cells, in the data after the literals. -/
  statics : Array Nat := #[]
  /-- The destructors of `μ` types, generated once per type (`genDtor`). -/
  dtors : Std.HashMap String Nat := {}

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

def vty (A : VTy) : CM LTy := lift (ofV A)
def cty (C : CTy) : CM LCTy := lift (ofC C)

/-- The type of a node's value: a value type's, `F A`'s `A`, and otherwise the closure the
computation's λ-value is. -/
def repJ (j : Jdg) : CM LTy := do
  match j with
  | .val A => vty A
  | .comp (.ret A) => vty A
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
def splitCtx (ctx : Ctx) (m : Masks) : CM ((Tm → Tm) × Ctx × Ctx) := do
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
      pre := (fun t => .copy x x' t) :: pre
      c₁ := c₁.push (some x); c₂ := c₂.push (some x')
    | some x, true, false => c₁ := c₁.push (some x); c₂ := c₂.push none
    | some x, false, true => c₁ := c₁.push none; c₂ := c₂.push (some x)
    | some x, false, false =>
      pre := (fun t => .drop x t) :: pre
      c₁ := c₁.push none; c₂ := c₂.push none
  readFact "masks"
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
    | .all c => return (none, ← repC c)
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
def ifLt (a b : Var) (yes no : CM Tm) : CM Tm :=
  bin (.rel .w32 .lt_u) a b boolT fun c => do
    let u₁ ← fresh .unit
    let u₂ ← fresh .unit
    return .case c u₁ (.drop u₁ (← no)) u₂ (.drop u₂ (← yes))

def add1 (i : Var) (k : Var → CM Tm) : CM Tm :=
  lit32 1 fun one => bin (.bin .w32 .add) i one i32T k

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
    let a ← fresh aT
    return .letv n (.prim .clampLen [c]) (← dup n fun n n' => do
      return .letv a (.prim .newArr [n']) (← lit32 0 fun z => pure (.call fi [f, a, z, n])))

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

/-- A borrow `withbor`'s way (SPEC §1): `(x, f () x)`, the owner `src` lent as the borrow the
callback `cb` (a `∀` closure) is given, by `op` (`lend`, `relend`). -/
def genLend (op : Op) (src cb : Var) : CM Tm := do
  let (_, gT) ← answerOf (← tyOf cb)
  let (some bT, rT) ← answerOf gT | throw "LIR: a borrow's callback takes no borrow"
  let pr ← fresh (.pair (← tyOf src) bT)
  let o ← freshLike src; let b ← fresh bT
  let g ← fresh gT; let r ← fresh rT
  readFact "lend"
  return .letv pr (.prim op [src]) (.letpair o b pr
    (.letv g (.app0 cb) (.letv r (.app g b) (.pair o r))))

/-- `withload x f` (SPEC §1): `f () (load x)`, the contents read at the callback's argument type. -/
def genWithload (x cb : Var) : CM Tm := do
  let (_, gT) ← answerOf (← tyOf cb)
  let (some vT, _) ← answerOf gT | throw "LIR: withload's callback takes no argument"
  let v ← fresh vT
  let g ← fresh gT
  return .letv v (.prim .load [x]) (.letv g (.app0 cb) (.app g v))

/-- `withswap x f` (SPEC §1): `let (y, z) = f (load x); store x y; (x, z)`, the load's copy and the
store's drop of the old contents cancelled: the contents moved out, and `y` moved in. -/
def genWithswap (m f : Var) : CM Tm := do
  let (some aT, rT) ← answerOf (← tyOf f) | throw "LIR: withswap's function takes no argument"
  let .pair yT zT := rT | throw "LIR: withswap's function answers no pair"
  let mT ← tyOf m
  let pr ← fresh (.pair mT aT)
  let m' ← fresh mT; let old ← fresh aT
  let r ← fresh rT
  let y ← fresh yT; let z ← fresh zT
  let m'' ← fresh mT
  return .letv pr (.prim .take [m]) (.letpair m' old pr (.letv r (.app f old)
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
  /-- The algebra's answer: through its `∀` at `fold_imm`. -/
  answerOf' (gT : LTy) : CM (Option LTy × LTy) := do
    match gT with
    | .thunk (.all (.ret h)) => answerOf h
    | t => answerOf t

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
  let ans ← match k with
    | .imm => do
      let .thunk (.all (.ret hT)) := gT | throw "LIR: fold_imm's algebra is not a `∀`"
      let h' ← fresh hT
      pure (Tm.letv h' (.app0 g) (.app h' r))
    | _ => pure (Tm.app g r)
  let hT ← match k, gT with
    | .imm, .thunk (.all (.ret h)) => pure h
    | .imm, _ => throw "LIR: fold_imm's algebra is not a `∀`"
    | _, _ => pure gT
  let (_, R) ← answerOf hT
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
  readFact "unfold"
  return obs

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
def genLendTree (src cb : Var) : CM Tm := do
  let (_, gT) ← answerOf (← tyOf cb)
  let (some bT, rT) ← answerOf gT | throw "LIR: a block borrow's callback takes no borrow"
  readFact "lend"
  lendTree src bT fun o b => do
    let g ← fresh gT; let r ← fresh rT
    return .letv g (.app0 cb) (.letv r (.app g b) (.pair o r))

/-! ### Externs -/

/-- An I/O operation's closure at its extern's type: `Λ. … λm. op m`. -/
def ioClos (fuel : Nat) (k : IOKind) (t : LTy) : CM Tm := do
  match fuel, t with
  | 0, _ => throw "LIR: an extern's type too deep"
  | f + 1, .thunk (.all c) =>
    let inner ← repOfK c
    mkClos "extern" [] (.all c) none inner fun _ => ioClos f k inner
  | _, .thunk (.arr a (.ret b)) =>
    mkClos "extern" [] (.arr a (.ret b)) (some a) b fun ctx => do
      match ctx with
      | some p :: _ => return .prim (.io k) [p]
      | _ => throw "LIR: an extern's argument"
  | _, t => throw s!"LIR: an I/O extern at {t}"
where
  repOfK : LCTy → CM LTy
    | .ret a => pure a
    | k => pure (.thunk k)

/-! ### The conversion -/

/-- The value a closure of `k` answers when it is run. -/
def repK : LCTy → CM LTy
  | .ret a => pure a
  | .all k | .arr _ k => repK k
  | .top => pure .unit
  | k => pure (.thunk k)

/-- The type of a constant's answer after `n` of its arguments. -/
def satTy (t : LTy) : Nat → CM LTy
  | 0 => pure t
  | n + 1 => do
    let (_, r) ← answerOf t
    satTy r n

/-- A literal's table (`TExpr.litFn`): the code `λi. byte i` of the `n` bytes at `off` in the
program's data, `0` past the end. -/
def litCode (off n : Nat) : CM Nat := do
  let fi ← reserveFn "literal"
  let i ← fresh i32T
  setFn fi { name := "literal", params := [i], body := .prim (.litByte off n) [i], ret := .int .w8 }
  addCode { kind := .lam, fns := [fi], ty := .arr i32T (.ret (.int .w8)) }

/-- The number of arguments a constant takes before its operation runs; `none` at a node that is
not a constant. -/
def constArity : TExpr → Option Nat
  | .alloc .. | .free .. | .copy .. | .forgetImm .. | .forgetMut .. | .forgetUnk .. | .hostOp ..
  | .arrNew .. | .arrFree .. | .arrSize .. | .arrReplace .. | .arrLen .. | .arrGet .. | .arrCopy ..
  | .arrForget .. | .countFold .. | .countTry .. | .sliceGetM .. | .sliceLenM .. | .sliceSplitI ..
  | .sliceSplitM .. | .sliceReplaceM .. | .sliceSwapM .. | .dtor .. | .foldImm .. | .foldOwn ..
  | .foldReuse .. | .unfoldN .. | .allocS .. | .freeS .. => some 1
  | .swap .. | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap ..
  | .sliceBorrowM .. | .sliceBorrowI .. | .withborSM .. | .withborSI .. | .withborF2M ..
  | .withborF2I .. => some 2
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
    | .all k | .nu k => takesClosK f k
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
  readFact (ruleName t)
  match t with
  | .var _ _ i _ =>
    match ctx[i]? with
    | some (some x) => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: variable {i} is not live"
  | .unitI .. | .topI .. => return leaf ctx none .unit
  | .lit _ _ c => return leaf ctx none (.lit c)
  | .tensorI _ j _ _ u t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u
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
  | .allI _ j _ _ _ _ c => do
    let .thunk k ← repJ j | throw "LIR: a Λ at a non-closure type"
    let (_, r) ← answerOf (.thunk k)
    mkClos "all" ctx k none r fun ctx' => conv fuel (none :: ctx') c
  | .withI _ j _ _ tM tN => do
    let .thunk k ← repJ j | throw "LIR: a `&` at a non-closure type"
    let r₁ ← selTy (.thunk k) 0
    let r₂ ← selTy (.thunk k) 1
    mkAmp "with" ctx k [r₁, r₂] [fun ctx' => conv fuel (none :: none :: ctx') tM,
      fun ctx' => conv fuel (none :: none :: ctx') tN]
  | .bind _ _ A _ u tM tN | .effLet _ _ A _ [] u tM tN => do
    let (pre, c₁, c₂) ← splitCtx ctx u
    return pre (← bindTm (← conv fuel c₁ tM) (← vty A) fun x => conv fuel (some x :: c₂) tN)
  | .force _ j i C => do
    match ctx[i]? with
    | some (some x) =>
      match C with
      | .ret _ => return leaf ctx (some i) (.app0 x)
      | _ => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: forced variable {i} is not live"
  | .app _ j i _ _ u tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u
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
    let (pre, c₁, c₂) ← splitCtx ctx u
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← conv fuel c₂ tM))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun p => do
      let x ← fresh aT; let y ← fresh bT
      return .letpair x y p (← conv fuel (some y :: some x :: c₂) tM))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← conv fuel (some x :: c₂) t₁) y (← conv fuel (some y :: c₂) t₂))
  | .zeroE _ _ _ u tV => do
    let (pre, c₁, _) ← splitCtx ctx u
    return pre (← bindTm (← conv fuel c₁ tV) .zero fun v => pure (.absurd v))
  | .allE _ _ _ _ _ _ c | .allEV _ _ _ _ _ _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun f => pure (.app0 f)
  | .roll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .roll [x])
  | .unroll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .unroll [x])
  | .lolliE .. => convSpine fuel ctx t
  | .use info j _ decl targs _ body => convUse fuel ctx info j decl targs body
  | .litFn _ _ bs _ => do
    let off := (← get).data.size
    modify fun s => { s with data := s.data ++ (bs.map (·.toUInt8)).toArray }
    let c ← litCode off bs.length
    readFact "litFn.bytes"
    modify fun s => { s with lits := s.lits.push (c, off, bs.length) }
    return leaf ctx none (.clos c [])
  | .divLit _ j op c inner => convDivLit fuel ctx j op c inner
  | .lendCell _ _ _ c => convLendCell fuel ctx t c
  | .walk _ _ _ c | .selfCall _ _ _ _ c => conv fuel ctx c
  | .effPerform .. | .effRaise .. | .effHandleV .. | .effHandleVB .. | .effHandleT .. | .effThen ..
  | .effLet .. | .effSub .. | .lendR .. | .lendLoopR .. | .nilDead .. | .withbor1U .. | .withbor2U ..
  | .withbor3U .. | .withloadU .. | .sliceBorrowMU .. | .sliceBorrowIU .. | .iterate .. | .divFuel ..
  | .reify .. | .boundedFix .. | .letPoly .. => outside t
  | t =>
    match transparent? t with
    | some c => conv fuel ctx c
    | none =>
      match constArity t with
      | some _ => return leaf ctx none (← constClos fuel t)
      | none => throw s!"LIR: no conversion for `{ruleName t}`"

/-- A spine of `lolliE` nodes: its arguments evaluated outermost first, then its function: a
constant's operation (`expand`), a λ's body (β), or a closure call. -/
def convSpine (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let (as, h) := spineOf 4096 t
  let resT ← repJ t.jdg
  go fuel ctx as [] h resT
where
  go (fuel : Nat) (ctx : Ctx) : List (Masks × TExpr) → List Var → TExpr → LTy → CM Tm
    | (u, ta) :: rest, vs, h, resT => do
      let (pre, cA, cF) ← splitCtx ctx u
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
        match hd, vs with
        | .lam _ _ _ _ body, a :: more => do
          let lamT ← repJ hd.jdg
          let (_, r) ← answerOf lamT
          if more.isEmpty then conv fuel (some a :: ctx) body
          else bindTm (← conv fuel (some a :: ctx) body) r fun g => applyAll g more
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
      readFact "lendCell.cell"
      let (pre₁, c₁, cF) ← splitCtx ctx u₁
      let cbv ← fresh (← repJ cb.jdg)
      let cbTm ← conv fuel c₁ cb
      let (pre₂, c₂, cH) ← splitCtx cF u₂
      let (pre₃, c₃, cA) ← splitCtx c₂ u₃
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
    readFact "use.perUse"
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
      readFact "use.shared"
      let kept := tp.slots.map (·.1)
      let extra := slots.filter fun (i, _) => !kept.contains i
      return drops (extra.map (·.2)) (← renameTm m tp.tm)
    conv fuel ctx body
  | none =>
    let tm ← conv fuel ctx body
    modify fun s => { s with uses := s.uses.insert key ⟨slots, tm⟩ }
    readFact "use.key"
    return tm

/-- A division by a literal at which it cannot fail (`TExpr.divLit`): the dividend, then the
operation with no error arm. The node is over `(λa. B) e` (`divLitB`): `e` is the typed term's
bound computation. -/
def convDivLit (fuel : Nat) (ctx : Ctx) (j : Jdg) (op : HostOp) (c : IntLit) (inner : TExpr) :
    CM Tm := do
  let rT ← repJ j
  match peelRet inner with
  | .bind _ _ A _ u tM _ => do
    let (pre, c₁, c₂) ← splitCtx ctx u
    let aT ← vty A
    readFact "divLit.divisor"
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

/-- **A constant applied to its arguments**, `args` in the order they apply, its answer of type
`resT`. -/
def expand (fuel : Nat) (c : TExpr) (args : List Var) (resT : LTy) : CM Tm := do
  readFact (ruleName c)
  match c, args with
  | .alloc .., [v] => return .prim .alloc [v]
  | .free .., [x] => return .prim .free [x]
  | .swap .., [x, v] => return .prim .swap [x, v]
  | .copy .., [x] | .arrCopy .., [x] => dup x fun x x' => pure (.pair x x')
  | .forgetImm .., [x] | .forgetMut .., [x] | .forgetUnk .., [x] | .arrForget .., [x] =>
    return .drop x .unit
  | .dtor _ _ A, [x] => genDtor 64 A x
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
      readFact "replace.swap"
      return .prim .replace [a, i, x]
  | .arrGet .., [p] | .sliceGetM .., [p] =>
    letpairM p fun v i => pure (.prim (.idx true) [v, i])
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
  | .withbor1 .., [x, cb] | .withbor2 .., [x, cb] | .sliceBorrowM .., [x, cb]
  | .sliceBorrowI .., [x, cb] => genLend .lend x cb
  | .withbor3 .., [m, cb] => genLend .relend m cb
  | .withload .., [x, cb] => genWithload x cb
  | .withswap .., [m, f] => genWithswap m f
  | .allocS .., [v] => allocTree v resT
  | .freeS _ j _, [v] => do
    let (_, vT) ← arrowOf (← repJ j)
    freeTree v vT
  | .withborSM .., [x, cb] | .withborSI .., [x, cb] | .withborF2M .., [x, cb]
  | .withborF2I .., [x, cb] => genLendTree x cb
  | .foldOwn _ _ F _, [g] | .foldReuse _ _ F _, [g] => do
    let k : FoldKind := match c with | .foldReuse .. => .reuse | _ => .own
    let .thunk fk := resT | throw "LIR: a fold's answer is not a closure"
    let (some muT, R) ← answerOf resT | throw "LIR: a fold takes no structure"
    readFact "fold.shape"
    let (recV, _) ← genFoldFns k F muT muT (← tyOf g)
    mkClos "fold" [some g] fk (some muT) R fun ctx' => do
      match ctx' with
      | some x :: some g' :: _ => return .call recV [g', x]
      | _ => throw "LIR: a fold's environment"
  | .foldImm _ _ F y _ _, [g] => do
    let .thunk fk := resT | throw "LIR: a fold's answer is not a closure"
    let (_, hT) ← answerOf resT
    let .thunk hk := hT | throw "LIR: fold_imm's inner closure"
    let (some lT, R) ← answerOf hT | throw "LIR: fold_imm takes no borrow"
    let .imm cellT := lT | throw "LIR: fold_imm's argument is not a borrow"
    let muT ← vty (VTy.immReborrow (.var y) (.mu F.ty))
    readFact "fold.shape"
    let (_, recL) ← genFoldFns .imm F muT cellT (← tyOf g)
    mkClos "fold_imm" [some g] fk none hT fun ctx' =>
      mkClos "fold_imm" ctx' hk (some lT) R fun ctx'' => do
        match ctx'' with
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

/-- Convert a checked `main` to a program. -/
def convertProg (exts : List Ext) (ctx : List (VTy × Bool)) (t : TExpr) (C : CTy) (ncaps : Nat)
    (loops : Bool) : Except String (Prog × CState) := do
  let ((m, mT), s) ← (convMain exts ctx t C ncaps loops).run {}
  return ({ fns := s.fns, codes := s.codes, main := m, mainTy := mT, ty := s.ty, data := s.data,
            statics := s.statics.size }, s)

end Backend2
