import Frontend.Parser
import Frontend.Print

/-!
# Frontend — Elab — effects and handlers  `[spec §18]`

An effect is a set of operations, and a handler gives each a clause over the handler's state. A
handler's meaning is its elaboration into core terms the checker already derives (decision 48):
nothing here reaches the kernel, the checker or the proofs.

* **A handler's clauses** are functions over a `mut` borrow of its state:
  `handler h(s: S) for E { op(x) -> M }` gives

      fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let r = modify c { s -> M; (s, r) }; (c, r)

  the `FnMut` row of SPEC §2: the clause is `!` code run by `withswap` on the lent state, and
  the borrow is handed back for the next operation.
* **`with h(e) { S }`** is a borrow block of the state's cell, `borrow mut (alloc(e)) { 'l, c -> S }`
  (or `borrow mut x { … }` for `with h(&mut x)`), whose callback's parameter `c` is the
  capability: the handled body is the callback of a `withbor`.
* **An operation call** `op(v)` in `S` is a call of the innermost handler's clause on the
  capability, which hands it back: `let (c, r) = h__op(c, v)`. The capability is threaded
  through the body as a `let mut` variable is: bound again after each call, handed out of a
  `match`, a borrow block and a `for`'s body.
* **A function that performs an operation**, directly or by calling one that does, has the
  effect in its **row**, which is inferred in declaration order and never written. It is
  elaborated once per handler it runs under, as a generic function is once per instance
  (decision 45): the copy `f__h` takes the capability first and hands it back first, and a call
  of `f` under `h` is a call of `f__h`. A function with a row that is never called under a
  handler is not elaborated.

**`Fail`**, the error effect, is a control effect: it has no capability and no state, and it
changes the type of what performs it (decision 48; `docs/effects-scoping.md` §7.5). `raise(e)`
aborts: a function whose row has `Fail[E]` answers `A + E` (beside its capabilities), each
normal answer `inl v` and each abort `inr e`, and a call of it is followed by a branch that goes
on with `v` or aborts in turn; inside a loop's body an abort is `break` with `inr e`, the loop's
own exit (`count_try`'s, SPEC §16), followed by the same branch after the loop. `try { S }` is the
handler that answers the sum; `catch { S } { e -> S₂ }` answers `S₂` on an error, and
`map_err { S } { e -> S₂ }` raises `S₂`'s value. Destructors run on each abort path, which is an
ordinary path of the elaborated program (SPEC §12), and a value that has none cannot be live
where a `raise` abandons it.

Resolution is lexical: an operation goes to the innermost `with` of its effect around it, or to
the capability the enclosing function was given; a `raise` goes to the innermost `try` around it,
or to the enclosing function's caller.

What is not provided, with the message that says so: an operation inside a closure or block
that is not run in place (a callback stored or passed, #161), a function with a row passed as a
value, a lend `&mut x` in the arguments of an effectful call, an operation inside a handler's
clause, and a function with a row whose result is a computation (a loop or a generator).
-/

namespace Frontend.Elab.Effects

/-- The operation `decl` of the effect `eff`. -/
structure OpSig where
  eff : String
  decl : OpDecl

/-- A handler: its name, its effect, its state and its clauses. -/
structure HSig where
  name : String
  eff : String
  st : Ident
  S : VTy
  clauses : List Clause
  sp : Span

/-- A function with a non-empty row: its declaration, the effects it performs, and the error type
of its `Fail`. -/
structure FSig where
  name : String
  row : List String
  err : Option VTy := none
  decl : Decl

/-- The error effect (SPEC §18). -/
def failEff : String := "Fail"

/-- The operation of `Fail`. -/
def raiseOp : String := "raise"

/-- What the elaboration knows: the operations, the handlers and the functions with a row, each
declared before the point being elaborated. -/
structure Env where
  /-- The functions of the libraries included, whose elaboration is not reported. -/
  lib : List String := []
  ops : List OpSig := []
  handlers : List HSig := []
  fns : List FSig := []

/-- A capability in scope: the effect it serves, the variable holding its `mut 'l S` borrow, the
lifetime `'l`, and the handler. -/
structure Cap where
  eff : String
  var : String
  life : String
  h : HSig

/-- The state of the elaboration: a counter for fresh names, the reports for `bcc check`, and the
copies made at each handler (finished ones in `made`, in the order they were finished). -/
structure St where
  fresh : Nat := 0
  reports : Array (Span × String) := #[]
  made : Array (String × Decl) := #[]
  started : List String := []
  /-- The abort points made so far: the span of each `raise` or raising call, and the binders in
  scope there, for the message when one of them has no destructor. -/
  aborts : Array (Span × List Span) := #[]
  /-- Elaborating a library declaration: nothing is reported. -/
  quiet : Bool := false

abbrev EM := StateT St (Except Error)

def fresh (pre : String) : EM String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

/-- A report for `bcc check` (SPEC §18, #126): its kind (`effect`, `row`, `lowering`, `call`) and
its text, at `sp`. -/
def report (sp : Span) (kind : String) (msg : String) : EM Unit :=
  modify fun s => if s.quiet then s else { s with reports := s.reports.push (sp, kind ++ " " ++ msg) }

/-- The depth bound for the traversals below. -/
def fuel : Nat := 1 <<< 16

/-- The name of a handler's clause for `op`. -/
def clauseName (h op : String) : String := h ++ "__" ++ op

/-- The name of the copy of `f` under the handlers `hs`. -/
def copyName (f : String) (hs : List String) : String := f ++ "__" ++ "_".intercalate hs

/-! ### Rows -/

def Env.op? (env : Env) (x : String) : Option OpSig := env.ops.find? (·.decl.name.name == x)

def Env.fn? (env : Env) (x : String) : Option FSig := env.fns.find? (·.name == x)

def Env.handler? (env : Env) (x : String) : Option HSig := env.handlers.find? (·.name == x)

/-- The name a call applies: `f(…)`, `f[A](…)`, `f ['x](…)`. -/
def headName : Val → Option String
  | .var _ f | .defApp _ f _ => some f
  | .inst _ V _ | .unbang _ V => headName V
  | _ => none

def union (a b : List String) : List String := (a ++ b).eraseDups

mutual
/-- The effects a value performs, outside the `with`s that handle them. -/
def rowV (env : Env) : Nat → Val → List String
  | 0, _ => []
  | n + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle h _)) P) (.thunkv _ (.lam _ _ _ M)) =>
      let inner := rowC env n M
      let inner := match env.handler? h with
        | some hs => inner.filter (· != hs.eff)
        | none => inner
      union (rowV env n P) inner
    | .app _ (.sugar _ .try_) (.thunk _ M) => (rowC env n M).filter (· != failEff)
    | .app _ (.app _ (.sugar _ .catch_) (.thunk _ M)) (.thunkv _ (.lam _ _ _ N)) =>
      union ((rowC env n M).filter (· != failEff)) (rowC env n N)
    | .app _ (.app _ (.sugar _ .mapErr) (.thunk _ M)) (.thunkv _ (.lam _ _ _ N)) =>
      union ((rowC env n M).filter (· != failEff)) (union (rowC env n N) [failEff])
    | .app _ f W =>
      let head := match headName f with
        | some x => if x == raiseOp then [failEff] else match env.op? x, env.fn? x with
          | some o, _ => [o.eff]
          | none, some g => g.row
          | none, none => rowV env n f
        | none => rowV env n f
      union head (rowV env n W)
    | .var _ x => match env.fn? x with
      | some g => g.row
      | none => []
    | .pair _ V W => union (rowV env n V) (rowV env n W)
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => rowV env n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => rowC env n M
    | _ => []

/-- The effects a computation performs, outside the `with`s that handle them. -/
def rowC (env : Env) : Nat → Comp → List String
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => rowV env n V
    | .bind _ _ _ M N _ | .with_ _ M N => union (rowC env n M) (rowC env n N)
    | .letUnit _ V M | .letPair _ _ _ V M => union (rowV env n V) (rowC env n M)
    | .case _ V _ M _ N | .for_ _ _ V M N =>
      union (rowV env n V) (union (rowC env n M) (rowC env n N))
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => rowC env n M
    | _ => []
end

mutual
/-- The error type of the first function with `Fail` a value calls, outside the `try`s that
handle it. -/
def errV (env : Env) : Nat → Val → Option VTy
  | 0, _ => none
  | n + 1, V => match V with
    | .app _ (.sugar _ .try_) _ => none
    | .app _ (.app _ (.sugar _ .catch_) _) (.thunkv _ (.lam _ _ _ N)) => errC env n N
    | .app _ (.app _ (.sugar _ .mapErr) _) (.thunkv _ (.lam _ _ _ N)) => errC env n N
    | .app _ f W =>
      let head := match headName f with
        | some x => (env.fn? x).bind (·.err)
        | none => errV env n f
      head.orElse fun _ => errV env n W
    | .pair _ V W => (errV env n V).orElse fun _ => errV env n W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => errV env n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => errC env n M
    | _ => none

/-- `errV` of a computation. -/
def errC (env : Env) : Nat → Comp → Option VTy
  | 0, _ => none
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => errV env n V
    | .bind _ _ _ M N _ | .with_ _ M N => (errC env n M).orElse fun _ => errC env n N
    | .letUnit _ V M | .letPair _ _ _ V M => (errV env n V).orElse fun _ => errC env n M
    | .case _ V _ M _ N | .for_ _ _ V M N =>
      ((errV env n V).orElse fun _ => errC env n M).orElse fun _ => errC env n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => errC env n M
    | _ => none
end

/-! ### Building terms -/

def _root_.Frontend.Life.vars : Life → List String
  | .var _ x => [x]
  | .meet _ a b | .join _ a b => a.vars ++ b.vars
  | _ => []

mutual
/-- The lifetime variables a type mentions. -/
def _root_.Frontend.VTy.lifeVars : VTy → List String
  | .tensor _ A B | .sum _ A B | .lolli _ A B => A.lifeVars ++ B.lifeVars
  | .thunk _ C => C.lifeVars
  | .ref _ A | .bang _ A | .mu _ _ A | .array _ A => A.lifeVars
  | .imm _ a A | .mut _ a A | .box _ a A | .view _ a A | .arrayImm _ a A | .arrayMut _ a A =>
    a.vars ++ A.lifeVars
  | .all _ _ b A => b.vars ++ A.lifeVars
  | .sized _ D S A => D.lifeVars ++ S.lifeVars ++ A.lifeVars
  | .fam _ _ a _ => a.vars
  | _ => []

def _root_.Frontend.CTy.lifeVars : CTy → List String
  | .ret _ A | .delay _ A | .stream _ A => A.lifeVars
  | .arr _ A C => A.lifeVars ++ C.lifeVars
  | .amp _ C D => C.lifeVars ++ D.lifeVars
  | .all _ _ b C => b.vars ++ C.lifeVars
  | .nu _ _ C => C.lifeVars
  | .iter _ A R R' | .gen _ A R R' => A.lifeVars ++ R.lifeVars ++ R'.lifeVars
  | .loop _ A B => A.lifeVars ++ B.lifeVars
  | _ => []
end


/-- `(c₁, (…, (cₙ, V)))`. -/
def capsTuple (sp : Span) (cs : List Cap) (V : Val) : Val :=
  cs.foldr (fun c W => .pair sp (.var sp c.var) W) V

/-- `mut 'l₁ S₁ * (… * A)`. -/
def capsTy (sp : Span) (cs : List Cap) (A : VTy) : VTy :=
  cs.foldr (fun c B => .tensor sp (.mut sp (.var sp c.life) c.h.S) B) A

/-- `let (c₁, r₁) = t; …; let (cₙ, x) = rₙ₋₁; N`: the capabilities bound again from `t`, and
`x` to the rest. -/
def unpack (sp : Span) : List Cap → String → String → Comp → EM Comp
  | [], x, t, N => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.var sp t)) N false)
  | [c], x, t, N => pure (.letPair sp ⟨c.var, sp⟩ ⟨x, sp⟩ (.var sp t) N)
  | c :: cs, x, t, N => do
    let r ← fresh "fx_r"
    pure (.letPair sp ⟨c.var, sp⟩ ⟨r, sp⟩ (.var sp t) (← unpack sp cs x r N))

/-- `case` on the sum in `t` after the capabilities `cs` are bound again from it:
`let (c₁, (…, s)) = t; case s { inl x -> N | inr e -> A(e) }`. -/
def splitSum (sp : Span) (cs : List Cap) (t x : String) (N : Comp) (onErr : Val → Comp) :
    EM Comp := do
  let e ← fresh "fx_e"
  let arms (s : String) : Comp := .case sp (.var sp s) ⟨x, sp⟩ N ⟨e, sp⟩ (onErr (.var sp e))
  if cs.isEmpty then return arms t
  let s ← fresh "fx_s"
  unpack sp cs s t (arms s)

/-- `t <- M; K`, with the bindings `M` begins with moved before it (they bind fresh names, or
capabilities that `K` binds again), so that the head of the binding is one statement. -/
def bindFlat (sp : Span) (t : String) (A : Option VTy) : Comp → Comp → Comp
  | .bind sp' a B M N lin, K => .bind sp' a B M (bindFlat sp t A N K) lin
  | .letPair sp' x y V M, K => .letPair sp' x y V (bindFlat sp t A M K)
  | .letUnit sp' V M, K => .letUnit sp' V (bindFlat sp t A M K)
  | M, K => .bind sp ⟨t, sp⟩ A M K false

/-- A terminal that leaves a loop: `break`, `break e`, `continue`, or `return e` from a loop's
body. -/
def isExit : Val → Bool
  | .sugar _ .brk | .app _ (.sugar _ .brk) _ | .app _ (.sugar _ .retE) _ | .sugar _ .cont => true
  | _ => false

/-- A binding put before a value: the computation that follows it is its argument. -/
abbrev Bind := Comp → EM Comp

def chain : List Bind → Comp → EM Comp
  | [], M => pure M
  | b :: bs, M => do b (← chain bs M)

/-- The plain calls of a value, bound first in the order its evaluation runs them in (innermost
and leftmost first), so that an effectful call lifted out of it keeps its place among them. A
sugar form (an operator, `*e`, a borrow block) is not a call and stays where it is. -/
def liftCalls : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | n + 1, V => match V with
    | .app sp f W => do
      match f with
      | .sugar .. | .app _ (.sugar ..) _ =>
        pure (.app sp f (← liftCalls n W))
      | _ =>
        let f' ← liftCalls n f
        let W' ← liftCalls n W
        let x ← (fresh "fx_n" : EM String)
        modify (· ++ [fun N => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.app sp f' W')) N false)])
        pure (.var sp x)
    | .pair sp V W => do pure (.pair sp (← liftCalls n V) (← liftCalls n W))
    | .inl sp V => do pure (.inl sp (← liftCalls n V))
    | .inr sp V => do pure (.inr sp (← liftCalls n V))
    | .ascribe sp V A => do pure (.ascribe sp (← liftCalls n V) A)
    | .roll sp V => do pure (.roll sp (← liftCalls n V))
    | .unroll sp V => do pure (.unroll sp (← liftCalls n V))
    | .boxed sp l V => do pure (.boxed sp l (← liftCalls n V))
    | .unbox sp V => do pure (.unbox sp (← liftCalls n V))
    | V => pure V

/-! ### Elaborating a body -/

/-- The context of an elaboration: what is declared, the capabilities in scope, and, in a
function's copy, the capabilities its `return e` from inside a loop hands back. -/
structure Cx where
  env : Env
  caps : List Cap
  fnCaps : List Cap := []
  /-- A `raise` here is handled (by a `try`, or by the caller of a function with `Fail`); `loop`:
  inside the body of a loop, where an abort leaves the loop with `break (inr e)`. -/
  fail : Option Bool := none
  /-- In a function whose result is a sum: `return e` from a loop's body answers `inl e`. -/
  fnFail : Bool := false
  /-- The type of the error the innermost handler of `Fail` receives, when it is known here. -/
  err : Option VTy := none
  /-- The binders in scope, for the message when a `raise` abandons one with no destructor. -/
  scope : List Span := []

/-- The capabilities of `cx` for the effects `row`, in the order of `cx.caps`. -/
def Cx.need (cx : Cx) (row : List String) : List Cap := cx.caps.filter (row.contains ·.eff)

def Cx.needV (cx : Cx) (V : Val) : List Cap := cx.need (rowV cx.env fuel V)
def Cx.needC (cx : Cx) (M : Comp) : List Cap := cx.need (rowC cx.env fuel M)

/-- The computation raises, and a handler of `Fail` is in scope. -/
def Cx.raisesC (cx : Cx) (M : Comp) : Bool := cx.fail.isSome && (rowC cx.env fuel M).contains failEff

/-- The value raises, and a handler of `Fail` is in scope. -/
def Cx.raisesV (cx : Cx) (V : Val) : Bool := cx.fail.isSome && (rowV cx.env fuel V).contains failEff

/-- `cx` for a computation that answers its own value: an abort in it is its answer `inr e`. -/
def Cx.sub (cx : Cx) : Cx := { cx with fail := cx.fail.map fun _ => false }

/-- An abort with the error `e`, from a computation handing back the capabilities `cs`: `break`
with `inr e` in a loop's body, and `(c₁, (…, inr e))` elsewhere. -/
def Cx.abort (cx : Cx) (cs : List Cap) (sp : Span) (e : Val) : Comp :=
  match cx.fail with
  | some true => .ret sp (.app sp (.sugar sp .brk) (.inr sp e))
  | _ => .ret sp (capsTuple sp cs (.inr sp e))

/-- The capability of the effect `e` in scope. -/
def Cx.capOf (cx : Cx) (e : String) : Option Cap := cx.caps.find? (·.eff == e)

def notInClosure (sp : Span) (e : String) : Error :=
  ⟨sp, s!"an operation of `{e}` is performed inside a closure or block that is not run in place: " ++
    "it cannot capture the capability (effectful callbacks, #161)"⟩

/-- A function's type and value taken apart: its lifetime parameters (outermost first), its
parameter's type, its result type, its parameter's name and its body. `!` or not. -/
structure FnParts where
  bang : Bool
  lives : List (Ident × Life)
  P : VTy
  T : VTy
  p : Ident
  body : Comp

def fnParts (sp : Span) (name : String) (A : VTy) (V : Val) : Except Error FnParts := do
  let (bang, A, V) : Bool × VTy × Comp ← match A, V with
    | .bang _ A, .bangThunkv _ M => pure (true, A, M)
    | A, .thunkv _ M => pure (false, A, M)
    | _, _ => throw ⟨sp, s!"`{name}` performs an operation, and is not a function"⟩
  let rec go : Nat → VTy → Comp → Except Error (List (Ident × Life) × VTy × VTy × Ident × Comp)
    | 0, _, _ => throw ⟨sp, "internal error: a function nested too deeply"⟩
    | n + 1, .all _ _ b A, .lamL _ a _ (.ret _ (.thunkv _ M)) => do
      let (ls, r) ← go n A M
      pure ((a, b) :: ls, r)
    | _ + 1, .lolli _ P T, .lam _ p _ body => pure ([], P, T, p, body)
    | _ + 1, .thunk .., _ =>
      throw ⟨sp, s!"`{name}` performs an operation, and its result is a computation (a loop or a " ++
        "generator): not provided"⟩
    | _ + 1, _, _ => throw ⟨sp, s!"`{name}` performs an operation, and its form is not a function's"⟩
  let (lives, P, T, p, body) ← go fuel A V
  pure ⟨bang, lives, P, T, p, body⟩

/-- A function's result type, when it mentions none of its own lifetime parameters: the type of
a call's result, whatever the call's lifetimes. -/
def closedResult (g : Decl) : Option VTy :=
  match g with
  -- A template's result may mention its type parameters: its instance's is not known here.
  | .def_ _ _ (_ :: _) _ _ _ => none
  | .def_ sp n _ A V _ => match fnParts sp n.name A V with
    | .ok f => if f.T.lifeVars.any (f.lives.map (·.1.name)).contains then none else some f.T
    | .error _ => none
  | _ => none

/-- A function type and value put together from its parts. -/
def FnParts.build (sp : Span) (f : FnParts) : VTy × Val :=
  let rec inner : List (Ident × Life) → VTy × Comp
    | [] => (.lolli sp f.P f.T, .lam sp f.p f.P f.body)
    | (a, b) :: ls =>
      let (T, M) := inner ls
      (.all sp a b T, .lamL sp a b (.ret sp (.thunkv sp M)))
  let (T, M) := inner f.lives
  if f.bang then (.bang sp T, .bangThunkv sp M) else (T, .thunkv sp M)

/-- The capabilities of a copy made for the handlers `hs`, one per effect of `row`. -/
def copyCaps (row : List String) (hs : List HSig) : List Cap :=
  (row.zip hs).map fun (e, h) => ⟨e, "fx_c_" ++ e.toLower, "fx_l_" ++ e.toLower, h⟩

/-- A body taking the capabilities `cs` first: `fx_pp : mut 'l₁ S₁ * (… * P)`, taken apart into
the capabilities and the original parameter `p`. -/
def takeCaps (sp : Span) (cs : List Cap) (f : FnParts) (body : Comp) : EM FnParts := do
  let pp ← fresh "fx_pp"
  let body ← unpack sp cs f.p.name pp body
  let lives := cs.map fun c => ((⟨c.life, sp⟩ : Ident), Life.top sp)
  pure { f with lives := lives ++ f.lives, P := capsTy sp cs f.P, T := capsTy sp cs f.T,
                p := ⟨pp, sp⟩, body }

/-- A `with` in a value, outside nothing: the elaboration must reach it. -/
def withInV : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle ..)) _) _ => true
    | .app _ f W | .pair _ f W => withInV k f || withInV k W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V
    | .unbox _ V | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V => withInV k V
    | .run _ M | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M => withInC k M
    | _ => false
where
  withInC : Nat → Comp → Bool
    | 0, _ => false
    | k + 1, M => match M with
      | .ret _ V | .absurd _ V => withInV k V
      | .bind _ _ _ M N _ | .with_ _ M N => withInC k M || withInC k N
      | .letUnit _ V M | .letPair _ _ _ V M => withInV k V || withInC k M
      | .case _ V _ M _ N | .for_ _ _ V M N => withInV k V || withInC k M || withInC k N
      | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
      | .nuOut _ M | .ascribe _ M _ => withInC k M
      | _ => false

/-- The plain calls of `V` that perform no effect of `cx`, lifted (`liftCalls`), in the order its
evaluation runs them in; an effectful call stays, its arguments' plain calls lifted. -/
def liftPlain (cx : Cx) : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | k + 1, V => match V with
    | .app sp f W =>
      match f with
      | .sugar .. | .app _ (.sugar ..) _ => do pure (.app sp f (← liftPlain cx k W))
      | _ =>
        if !(cx.needV V).isEmpty || cx.raisesV V then do pure (.app sp f (← liftPlain cx k W))
        else liftCalls k V
    | .pair sp V W => do pure (.pair sp (← liftPlain cx k V) (← liftPlain cx k W))
    | .inl sp V => do pure (.inl sp (← liftPlain cx k V))
    | .inr sp V => do pure (.inr sp (← liftPlain cx k V))
    | .ascribe sp V A => do pure (.ascribe sp (← liftPlain cx k V) A)
    | .roll sp V => do pure (.roll sp (← liftPlain cx k V))
    | .unroll sp V => do pure (.unroll sp (← liftPlain cx k V))
    | .boxed sp l V => do pure (.boxed sp l (← liftPlain cx k V))
    | .unbox sp V => do pure (.unbox sp (← liftPlain cx k V))
    | V => pure V

/-- A place lent, or a standard capability used, in the body of a handler of `Fail` and declared
outside it is not provided: the body is a computation of its own, which does not hand it back. -/
def noLentIn (sp : Span) (M : Comp) : EM Unit := do
  let bound := M.boundNames
  let lent := (M.lentNames.filter (!bound.contains ·)) ++
    (["stdin", "stdout", "stderr"].filter fun c => (M.lentNames true).contains c && !bound.contains c)
  if let some x := lent.head? then
    throw ⟨sp, s!"`{x}` is lent or used in this block and declared outside it: a handler of " ++
      "`Fail` does not hand back the places its body lends; lend it outside the block"⟩

/-- A lend in the arguments of a call that threads a capability is not provided. -/
def noLend (sp : Span) (what : String) (W : Val) : EM Unit := do
  if W.lends then
    throw ⟨sp, s!"a place is lent (`&mut x`) in the arguments of {what}, which also threads a " ++
      "capability: lend it in a call of its own"⟩

/-- A `raise` or a `try` in a value, outside closures: the elaboration must reach it. -/
def failIn : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => match V with
    | .app _ (.sugar _ .try_) _ | .app _ (.app _ (.sugar _ .catch_) _) _
    | .app _ (.app _ (.sugar _ .mapErr) _) _ => true
    | .app _ (.var _ x) _ => x == raiseOp
    | .app _ f W | .pair _ f W => failIn k f || failIn k W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V
    | .unbox _ V | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V => failIn k V
    | .run _ M | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M => failInC k M
    | _ => false
where
  failInC : Nat → Comp → Bool
    | 0, _ => false
    | k + 1, M => match M with
      | .ret _ V | .absurd _ V => failIn k V
      | .bind _ _ _ M N _ | .with_ _ M N => failInC k M || failInC k N
      | .letUnit _ V M | .letPair _ _ _ V M => failIn k V || failInC k M
      | .case _ V _ M _ N | .for_ _ _ V M N => failIn k V || failInC k M || failInC k N
      | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
      | .nuOut _ M | .ascribe _ M _ => failInC k M
      | _ => false

/-- The type of a `try` whose body is one call of a function that only raises: its result type
and its error type, when the result mentions none of its lifetimes. The call's answer is the
`try`'s, so the binding of it is annotated. -/
def tailSumTy (cx : Cx) (cs : List Cap) : Comp → Option VTy
  | .ret sp (.app _ f _) => do
    let g ← cx.env.fn? (← headName f)
    unless g.row.contains failEff do none
    unless (cx.need (g.row.filter (· != failEff))).map (·.var) == cs.map (·.var) do none
    pure (capsTy sp cs (.sum sp (← closedResult g.decl) (← g.err)))
  | _ => none

/-- The `break`s of a loop's body, outside its inner loops, with their values made `inl v` (a bare
`break`, `inl ()`): the loop's value is a sum when its body raises. -/
def inlBreaks : Nat → Comp → Comp
  | 0, M => M
  | n + 1, M => match M with
    | .ret sp (.sugar ksp .brk) => .ret sp (.app sp (.sugar ksp .brk) (.inl sp (.unit sp)))
    | .ret sp (.app asp (.sugar ksp .brk) v) => .ret sp (.app asp (.sugar ksp .brk) (.inl sp v))
    | .bind sp x A M N lin => .bind sp x A M (inlBreaks n N) lin
    | .letUnit sp V M => .letUnit sp V (inlBreaks n M)
    | .letPair sp x y V M => .letPair sp x y V (inlBreaks n M)
    | .case sp V x M y N => .case sp V x (inlBreaks n M) y (inlBreaks n N)
    | .for_ sp x V M N => .for_ sp x V M (inlBreaks n N)
    | M => M

/-- The terminals of a computation reached through tail positions, `ret V` made `ret (inl V)`. -/
def inlTerms : Nat → Comp → Comp
  | 0, M => M
  | n + 1, M => match M with
    | .ret sp V => .ret sp (.inl sp V)
    | .bind sp x A M N lin => .bind sp x A M (inlTerms n N) lin
    | .letUnit sp V M => .letUnit sp V (inlTerms n M)
    | .letPair sp x y V M => .letPair sp x y V (inlTerms n M)
    | .case sp V x M y N => .case sp V x (inlTerms n M) y (inlTerms n N)
    | .for_ sp x V M N => .for_ sp x V M (inlTerms n N)
    | T => .bind T.span ⟨"fx_ti", T.span⟩ none T (.ret T.span (.inl T.span (.var T.span "fx_ti"))) false

/-- A computation that raises before anything else: `raise(e)`, or a binding whose head does. -/
def abortsAtHead : Comp → Bool
  | .ret _ (.app _ (.var _ x) _) => x == raiseOp
  | .bind _ _ _ M _ _ => abortsAtHead M
  | _ => false

/-- The binder spans a pattern of the computation binds at its head, for `Cx.scope`. -/
def headBinders : Comp → List Span
  | .bind _ x _ _ _ _ => [x.span]
  | .letPair _ x y _ _ => [x.span, y.span]
  | _ => []

mutual
/-- `M` with its operations made calls on the capabilities `cs`, handing them back beside its
result: each terminal answering `v` answers `(c₁, (…, (cₙ, v)))`, and `(c₁, (…, (cₙ, inl v)))`
when `r` (the computation raises: an abort answers `inr e` there). With `wrap := false` (the body
of a loop, which threads the capabilities by name), the terminals are kept, and the capabilities
are only bound again. A `with` inside is elaborated either way. -/
def trC : Nat → Cx → List Cap → Bool → Bool → Comp → EM Comp
  | 0, _, _, _, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, r, M => do
    let cxN (bs : List Span) : Cx := { cx with scope := bs ++ cx.scope }
    match M with
    | .ret sp V@(.app _ f W) =>
      -- A call of a function that raises, in tail position, whose capabilities are the ones
      -- this computation hands back: its answer is already this one's, and is answered as it is.
      match headName f, wrap && r with
      | some x, true =>
        match cx.env.fn? x with
        | some g =>
          let own := g.row.filter (· != failEff)
          let used := cx.need own
          if g.row.contains failEff && !W.lends && used.map (·.var) == cs.map (·.var) &&
              used.length == own.length then
            let (bs, W') ← trV n cx cs W
            let name ← if used.isEmpty then pure x else copyOf n cx.env sp g (used.map (·.h))
            let f' : Val := match f with
              | .defApp fsp _ As => .defApp fsp name As
              | _ => .var f.span name
            report sp "call" (s!"{x} ({", ".intercalate g.row}) → `{name}`, in tail position: its " ++
              "answer is this one's")
            return ← chain bs (.ret sp (.app sp f' (capsTuple sp used W')))
          else trRet n cx cs wrap r sp V
        | none => trRet n cx cs wrap r sp V
      | _, _ => trRet n cx cs wrap r sp V
    | .ret sp V => trRet n cx cs wrap r sp V
    | .bind sp x A M N lin =>
      let csM := cx.needC M
      let rM := cx.raisesC M
      -- `if c { raise(e) } else { M₂ }; N`: the arm that aborts leaves, and the other goes on
      -- with `N`, so no sum is made.
      if let .case csp V y M₁ z M₂ := M then
        if rM && abortsAtHead M₁ && !cx.raisesC M₂ then
          let (bs, V') ← trV n cx cs V
          return ← chain bs (.case csp V' y (← trC n (cxN [y.span]) cs wrap r M₁) z
            (← trC n (cxN [z.span]) cs wrap r (.bind sp x A M₂ N lin)))
        if rM && abortsAtHead M₂ && !cx.raisesC M₁ then
          let (bs, V') ← trV n cx cs V
          return ← chain bs (.case csp V' y (← trC n (cxN [y.span]) cs wrap r (.bind sp x A M₁ N lin))
            z (← trC n (cxN [z.span]) cs wrap r M₂))
      let N' ← trC n (cxN [x.span]) cs wrap r N
      if csM.isEmpty && !rM then
        pure (.bind sp x A (← trC n cx [] false false M) N' lin)
      else if let .ret rsp V := M then
        -- A value: its effectful calls bound before the binding, which keeps its form.
        let (bs, V') ← trV n cx cs V
        chain bs (.bind sp x A (.ret rsp V') N' lin)
      else
        -- `M` hands back the capabilities it uses, which are bound again for `N`; when it
        -- raises, its answer is a sum, and an error aborts here in turn.
        let t ← fresh "fx_b"
        let M' ← trC n cx.sub csM true rM M
        let v ← fresh "fx_v"
        let N'' := if lin || rM then .bind sp x none (.ret sp (.var sp v)) N' lin else N'
        let body ← if rM then splitSum sp csM t v N'' (cx.abort cs sp)
          else if lin then unpack sp csM v t N''
          else unpack sp csM x.name t N'
        let ann := if rM then none else A.map (capsTy sp csM)
        pure (bindFlat sp t ann M' body)
    | .letUnit sp V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letUnit sp V' (← trC n cx cs wrap r M))
    | .letPair sp x y V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letPair sp x y V' (← trC n (cxN [x.span, y.span]) cs wrap r M))
    | .case sp V x M y N =>
      let (bs, V') ← trV n cx cs V
      chain bs (.case sp V' x (← trC n (cxN [x.span]) cs wrap r M) y (← trC n (cxN [y.span]) cs wrap r N))
    | .for_ sp x V M N =>
      let (bs, V') ← trV n cx cs V
      if !cx.raisesC M then
        -- The body rebinds the capabilities it uses by name, and the loop threads them.
        return ← chain bs (.for_ sp x V' (← trC n (cxN [x.span]) [] false false M)
          (← trC n cx cs wrap r N))
      -- The body raises: an abort leaves the loop with `break (inr e)`, its `break`s answer
      -- `inl`, and after the loop an error aborts here in turn.
      let M' ← trC n { cxN [x.span] with fail := some true } [] false false (inlBreaks fuel M)
      let lr ← fresh "fx_lr"
      let e ← fresh "fx_e"
      let abort := cx.abort cs sp (.var sp e)
      let after ← match N with
        | .bind bsp rv A (.ret rsp (.app asp (.sugar fsp .forRes) (.thunk tsp d))) N₂ lin => do
          let N₂' ← trC n (cxN [rv.span]) cs wrap r N₂
          let v ← fresh "fx_v"
          let ann := match A, cx.err with
            | some A, some E => some (VTy.sum bsp A E)
            | _, _ => none
          pure (.bind bsp ⟨lr, bsp⟩ ann
            (.ret rsp (.app asp (.sugar fsp .forRes) (.thunk tsp (inlTerms fuel d))))
            (.case bsp (.var bsp lr) ⟨v, bsp⟩ (.bind bsp rv A (.ret bsp (.var bsp v)) N₂' lin)
              ⟨e, bsp⟩ abort) false)
        | .bind bsp _ _ (.ret _ (.sugar _ .forRes)) _ _ =>
          throw ⟨bsp, "a `raise` in the body of a loop whose value is what its source finishes " ++
            "with is not provided: give the loop an `else`"⟩
        | N => do
          let N' ← trC n cx cs wrap r N
          let u ← fresh "fx_u"
          pure (.bind sp ⟨lr, sp⟩ (cx.err.map (VTy.sum sp (.unit sp)))
            (.ret sp (.app sp (.sugar sp .forRes) (.thunk sp (.ret sp (.inl sp (.unit sp))))))
            (.case sp (.var sp lr) ⟨u, sp⟩ N' ⟨e, sp⟩ abort) false)
      report sp "lowering" "for (Fail): an abort in its body is the loop's exit (`break`), then a branch"
      chain bs (.for_ sp x V' M' after)
    | .absurd sp V =>
      let (bs, V') ← trV n cx cs V
      chain bs (.absurd sp V')
    -- A function's code: a `with` or a handler of `Fail` inside it is elaborated.
    | .lam sp x A M => pure (.lam sp x A (← trC n (cxN [x.span]) cs wrap r M))
    | .lamL sp x b M => pure (.lamL sp x b (← trC n cx cs wrap r M))
    | T =>
      if let some c := (cx.needC T).head? then
        throw ⟨T.span, s!"an operation of `{c.eff}` is performed here, in a form that does not " ++
          "thread its capability"⟩
      if cx.raisesC T then
        throw ⟨T.span, "a `raise` here is in a form that cannot abort (a closure, a `<M, N>` or " ++
          "a computation type): not provided"⟩
      if !wrap || (cs.isEmpty && !r) then return T
      let rv ← fresh "fx_t"
      pure (.bind T.span ⟨rv, T.span⟩ none T (.ret T.span (capsTuple T.span cs
        (if r then .inl T.span (.var T.span rv) else .var T.span rv))) false)

/-- A terminal `return V` of `trC`. -/
def trRet : Nat → Cx → List Cap → Bool → Bool → Span → Val → EM Comp
  | 0, _, _, _, _, sp, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, r, sp, V => do
    let (bs, V') ← trV n cx cs V
    let T := if isExit V' || !wrap then Comp.ret sp V'
      else .ret sp (capsTuple sp cs (if r then .inl sp V' else V'))
    chain bs T

/-- A value with its effectful calls lifted out before it, as bindings that thread the
capabilities `cs` (and branch on an error, when a call raises); the value refers to their
results. Every plain call evaluated before an effectful one is lifted too, so the calls keep
their order. -/
def trV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | n + 1, cx, cs, V => do
    let row := rowV cx.env fuel V
    let needs := !(cx.need row).isEmpty || (cx.fail.isSome && row.contains failEff)
    -- An effect with no handler in scope is reported where it is performed (`goV`).
    let unhandled := row.any fun e => if e == failEff then cx.fail.isNone else (cx.capOf e).isNone
    if !needs && !unhandled && !withInV fuel V && !failIn fuel V then return ([], V)
    let (V, pre) ← if needs then (liftPlain cx fuel V).run [] else pure (V, [])
    let (bs, V') ← goV n cx cs V
    pure (pre ++ bs, V')

/-- `trV` below the lifting of plain calls. -/
def goV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, V => match V with
    | .app sp (.app sp₂ (.sugar ksp (.handle h l)) P) (.thunkv tsp (.lam lsp b A M)) =>
      withBlk k cx cs sp sp₂ ksp h l P tsp lsp b A M
    | .app sp (.app sp₂ (.sugar ksp k'@(.borrow ..)) P) (.thunkv tsp (.lam lsp b A M)) => do
      let (bsP, P') ← goV k cx cs P
      let csM := cx.needC M
      let rM := cx.raisesC M
      if csM.isEmpty && !rM then
        let M' ← trC k cx [] false false M
        return (bsP, .app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M')))
      let M' ← trC k { cx.sub with scope := b.span :: cx.scope } csM true rM M
      let blk := Val.app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M'))
      blockResult k cx cs sp blk csM rM
    | .app sp (.sugar ksp .try_) (.thunk tsp M) => do
      -- `try { M }`: `M` answers `inl` its value or `inr` the error it raised.
      noLentIn ksp M
      let csM := cx.needC M
      let M' ← trC k { cx with fail := some false } csM true true M
      report ksp "lowering" ("try (Fail): branch — an abort never resumes (final ctl): a sum exit, " ++
        "its answer `inl v` or `inr e`")
      let t ← fresh "fx_b"
      let r ← if csM.isEmpty then pure t else fresh "fx_v"
      let ann := tailSumTy cx csM M
      let bind : Bind := fun N => do
        pure (bindFlat sp t ann M' (← if csM.isEmpty then pure N else unpack sp csM r t N))
      pure ([bind], .var sp r)
    | .app sp (.app _ (.sugar ksp h@(.catch_)) (.thunk _ M)) (.thunkv lsp (.lam _ e _ N))
    | .app sp (.app _ (.sugar ksp h@(.mapErr)) (.thunk _ M)) (.thunkv lsp (.lam _ e _ N)) => do
      -- `catch { M } { e -> N }`: a branch on `try { M }`, `N` on its error. `map_err`: `N` is
      -- raised in turn.
      if !(cx.needC N).isEmpty || cx.raisesC N then
        throw ⟨lsp, "the handler's body performs an effect or raises: not provided (bind the error, " ++
          "and handle it after the block)"⟩
      if h == .mapErr && cx.fail.isNone then
        throw ⟨ksp, "this `map_err` raises, and nothing handles it here: put it inside `try`, `catch`, " ++
          "or a function that can raise"⟩
      noLentIn ksp M
      let csM := cx.needC M
      let M' ← trC k { cx with fail := some false } csM true true M
      let N' ← trC k { cx with caps := [], fnCaps := [] } [] false false N
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      let v ← fresh "fx_v"
      let r := if csM.isEmpty then t else r
      let ann := tailSumTy cx csM M
      let tryBind : Bind := fun K => do
        pure (bindFlat sp t ann M' (← if csM.isEmpty then pure K else unpack sp csM r t K))
      if h == .catch_ then
        report ksp "lowering" "catch (Fail): branch — on `inr e` its handler runs in place"
        let x ← fresh "fx_x"
        let bind : Bind := fun K => do
          pure (.bind sp ⟨x, sp⟩ none (.case sp (.var sp r) ⟨v, sp⟩ (.ret sp (.var sp v)) e N') K false)
        return ([tryBind, bind], .var sp x)
      report ksp "lowering" "map_err (Fail): branch — on `inr e` its handler's value is raised"
      modify fun s => { s with aborts := s.aborts.push (ksp, cx.scope) }
      let w ← fresh "fx_w"
      let bind : Bind := fun K => do
        pure (.case sp (.var sp r) ⟨v, sp⟩ K e
          (.bind lsp ⟨w, lsp⟩ cx.err N' (cx.abort cs sp (.var lsp w)) false))
      pure ([tryBind, bind], .var sp v)
    | .app sp f W => do
      match headName f with
      | some x =>
        if x == raiseOp then raiseCall k cx cs sp W else
        match cx.env.op? x, cx.env.fn? x with
        | some o, _ => opCall k cx cs sp x o W
        | none, some g => fnCall k cx cs sp f x g W
        | none, none => plainApp k cx cs sp f W
      | none => plainApp k cx cs sp f W
    | .var sp x => do
      match cx.env.fn? x with
      | some g =>
        if g.row.contains failEff then
          throw ⟨sp, s!"`{x}` raises (`Fail`) and is passed as a value: a fold whose algebra " ++
            "raises needs an early exit from a kernel fold (K4), which is open; an effectful " ++
            "callback is S4's (#161)"⟩
        throw ⟨sp, s!"`{x}` performs `{", ".intercalate g.row}` and is passed as a value: it can " ++
          "only be called (effectful callbacks, #161)"⟩
      | none => pure ([], V)
    | .pair sp V W => do
      let (b₁, V') ← goV k cx cs V
      let (b₂, W') ← goV k cx cs W
      pure (b₁ ++ b₂, .pair sp V' W')
    | .inl sp V => do let (b, V') ← goV k cx cs V; pure (b, .inl sp V')
    | .inr sp V => do let (b, V') ← goV k cx cs V; pure (b, .inr sp V')
    | .ascribe sp V A => do let (b, V') ← goV k cx cs V; pure (b, .ascribe sp V' A)
    | .roll sp V => do let (b, V') ← goV k cx cs V; pure (b, .roll sp V')
    | .unroll sp V => do let (b, V') ← goV k cx cs V; pure (b, .unroll sp V')
    | .boxed sp l V => do let (b, V') ← goV k cx cs V; pure (b, .boxed sp l V')
    | .unbox sp V => do let (b, V') ← goV k cx cs V; pure (b, .unbox sp V')
    | .unbang sp V => do let (b, V') ← goV k cx cs V; pure (b, .unbang sp V')
    | .inst sp V l => do let (b, V') ← goV k cx cs V; pure (b, .inst sp V' l)
    | .sub sp V l => do let (b, V') ← goV k cx cs V; pure (b, .sub sp V' l)
    | .shorten sp m σ l V => do let (b, V') ← goV k cx cs V; pure (b, .shorten sp m σ l V')
    | .run sp M => do
      let csM := cx.needC M
      let rM := cx.raisesC M
      if csM.isEmpty && !rM then return ([], .run sp (← trC k cx [] false false M))
      let M' ← trC k cx.sub csM true rM M
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      let bind : Bind := fun N => do
        if rM then pure (bindFlat sp t none M' (← splitSum sp csM t r N (cx.abort cs sp)))
        else pure (bindFlat sp t none M' (← unpack sp csM r t N))
      pure ([bind], .var sp r)
    | .thunk sp M | .thunkv sp M | .bangThunk sp M | .bangThunkv sp M => do
      match (cx.needC M).head? with
      | some c => throw (notInClosure sp c.eff)
      | none =>
        if cx.raisesC M then
          throw ⟨sp, "a `raise` inside a closure or block that is not run in place: the closure " ++
            "cannot abort its caller (a fold whose algebra raises needs K4, an early exit from a " ++
            "kernel fold, which is open)"⟩
        -- A closure sees no capability of the enclosing body, and no handler of `Fail`; a `with`
        -- or a `try` inside it is its own.
        let M' ← trC k { cx with caps := [], fnCaps := [], fail := none, fnFail := false } [] false
          false M
        pure ([], match V with
          | .thunk .. => .thunk sp M' | .thunkv .. => .thunkv sp M'
          | .bangThunk .. => .bangThunk sp M' | _ => .bangThunkv sp M')
    | V => pure ([], V)

/-- The value of a borrow or `with` block whose body hands back the capabilities `csM` beside its
result, and answers a sum when `rM`: the capabilities bound again after it, and an error aborts
there in turn; the block's value is `(place, result)` again. -/
def blockResult : Nat → Cx → List Cap → Span → Val → List Cap → Bool → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | _ + 1, cx, cs, sp, blk, csM, rM => do
    let t ← fresh "fx_b"
    let pl ← fresh "fx_pl"
    let q ← fresh "fx_q"
    let r ← fresh "fx_v"
    let bind : Bind := fun N => do
      let rest ← if rM then splitSum sp csM q r N (cx.abort cs sp) else unpack sp csM r q N
      pure (.bind sp ⟨t, sp⟩ none (.ret sp blk) (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) rest) false)
    pure ([bind], .pair sp (.var sp pl) (.var sp r))

/-- A plain application, its parts elaborated. `return e` from a loop's body in a copy hands the
capabilities back too, and answers `inl e` in a function whose result is a sum. -/
def plainApp : Nat → Cx → List Cap → Span → Val → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, W => do
    if let .sugar _ .retE := f then
      let (b, W') ← goV k cx cs W
      let W'' := if cx.fnFail then Val.inl sp W' else W'
      return (b, .app sp f (capsTuple sp cx.fnCaps W''))
    let (b₁, f') ← goV k cx cs f
    let (b₂, W') ← goV k cx cs W
    pure (b₁ ++ b₂, .app sp f' W')

/-- `raise(W)`: an abort; what follows it is not run. -/
def raiseCall : Nat → Cx → List Cap → Span → Val → EM (List Bind × Val)
  | 0, _, _, sp, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, W => do
    if cx.fail.isNone then
      throw ⟨sp, "this `raise` is not handled: no `try`, `catch` or `map_err` is around it, and " ++
        "it is not in a function that can raise (a clause, a closure or `main`)"⟩
    let (b, W') ← goV k cx cs W
    report sp "call" ("raise (Fail) → an abort (final ctl): `inr e` to the innermost handler, " ++
      "or `break` out of the loop it is in")
    modify fun s => { s with aborts := s.aborts.push (sp, cx.scope) }
    let bind : Bind := fun _ => pure (cx.abort cs sp W')
    pure (b ++ [bind], .unit sp)

/-- `op(W)`: a call of the innermost handler's clause on the capability, which hands it back. -/
def opCall : Nat → Cx → List Cap → Span → String → OpSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, x, o, W => do
    let some c := cx.capOf o.eff
      | throw ⟨sp, s!"the operation `{x}` of `{o.eff}` is performed here, but no handler of " ++
          s!"`{o.eff}` is in scope"⟩
    noLend sp s!"the operation `{x}`" W
    let (b, W') ← goV k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    let call := Val.app sp (.var sp (clauseName c.h.name x)) (.pair sp (.var sp c.var) W')
    report sp "call" s!"{x} ({o.eff}) → `{clauseName c.h.name x}`, on the state of `{c.h.name}`"
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ (some (capsTy sp [c] o.decl.res)) (.ret sp call)
        (← unpack sp [c] r t N) false)
    pure (b ++ [bind], .var sp r)

/-- `f(W)` of a function with a row: a call of its copy under the handlers in scope, which takes
their capabilities first and hands them back first; when it raises, a branch on its answer. -/
def fnCall : Nat → Cx → List Cap → Span → Val → String → FSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, g, W => do
    let mut used : Array Cap := #[]
    for e in g.row do
      if e == failEff then
        if cx.fail.isNone then
          throw ⟨sp, s!"`{x}` raises (`Fail`), and nothing handles it here: call it inside `try`, " ++
            "`catch` or `map_err`, or from a function that can raise"⟩
      else match cx.capOf e with
        | some c => used := used.push c
        | none => throw ⟨sp, s!"`{x}` performs `{e}`, but no handler of `{e}` is in scope here"⟩
    let raises := g.row.contains failEff
    let usedL := used.toList
    if usedL.isEmpty && !raises then return ← plainApp k cx cs sp f W
    noLend sp s!"`{x}`" W
    let (b, W') ← goV k cx cs W
    let name ← if usedL.isEmpty then pure x else copyOf k cx.env sp g (usedL.map (·.h))
    let f' : Val := match f with
      | .defApp fsp _ As => .defApp fsp name As
      | _ => .var f.span name
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    if raises then modify fun s => { s with aborts := s.aborts.push (sp, cx.scope) }
    report sp "call" (s!"{x} ({", ".intercalate g.row}) → `{name}`" ++
      (if usedL.isEmpty then "" else ", passing the capabilities") ++
      (if raises then "; then a branch on its answer, an error aborting here" else ""))
    -- The binding is annotated when the result's type is known here, so that what follows is
    -- typed whatever the call's lifetimes.
    let res := (closedResult g.decl).map fun T =>
      match g.err, raises with
      | some E, true => VTy.sum sp T E
      | _, _ => T
    let ann := res.map (capsTy sp usedL)
    -- When the result's type is not known here (a template's instance), the capabilities are
    -- bound again at their own types, which are.
    let N' (N : Comp) : Comp := if ann.isSome then N else
      usedL.foldr (fun c K => .bind sp ⟨c.var, sp⟩ (some (capsTy sp [c] (.unit sp) |> fun
        | .tensor _ T _ => T
        | T => T)) (.ret sp (.var sp c.var)) K false) N
    let bind : Bind := fun N => do
      let rest ← if raises then splitSum sp usedL t r (N' N) (cx.abort cs sp)
        else unpack sp usedL r t (N' N)
      pure (.bind sp ⟨t, sp⟩ ann (.ret sp (.app sp f' (capsTuple sp usedL W'))) rest false)
    pure (b ++ [bind], .var sp r)

/-- `with h(P) { 'l, c -> M }`: a borrow block of the state's cell whose callback's parameter
`c` is the capability. -/
def withBlk : Nat → Cx → List Cap → Span → Span → Span → String → String → Val → Span → Span →
    Ident → VTy → Comp → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, sp₂, ksp, h, l, P, tsp, lsp, b, A, M => do
    let some hs := cx.env.handler? h
      | throw ⟨ksp, s!"no handler `{h}` is declared before this `with`"⟩
    let (bsP, P') ← goV k cx cs P
    let place ← match P' with
      | .lend _ x .mut => pure (Val.var x.span x.name)
      | .lend lsp' _ .imm => throw ⟨lsp', "a handler's state is lent `&mut`"⟩
      | V => pure (.app V.span (.sugar V.span (.call "alloc")) V)
    let cap : Cap := ⟨hs.eff, b.name, l, hs⟩
    let cx' : Cx := { cx.sub with caps := cap :: cx.caps.filter (·.eff != hs.eff),
                                  scope := b.span :: cx.scope }
    let csM := cx'.needC M
    let outer := csM.filter (·.eff != hs.eff)
    let rM := cx.raisesC M
    let where_ := match P' with
      | .lend _ x _ => s!"lent from `{x.name}`"
      | _ => "in a cell scoped to the block"
    report ksp "lowering" (s!"with {h} ({hs.eff}): a borrow block of its state ({where_}); its " ++
      "operations are calls of the clauses on the capability")
    -- The body hands back the enclosing capabilities it uses; its own is dropped at its end.
    let body ← trC k cx' outer true rM M
    let blk := Val.app sp (.app sp₂ (.sugar ksp (.borrow .mut l)) place)
      (.thunkv tsp (.lam lsp b A body))
    if outer.isEmpty && !rM then return (bsP, blk)
    let (bs, V') ← blockResult k cx cs sp blk outer rM
    pure (bsP ++ bs, V')

/-- The copy of `g` under the handlers `hs`, made once: its body elaborated with their
capabilities as parameters. -/
def copyOf : Nat → Env → Span → FSig → List HSig → EM String
  | 0, _, sp, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, g, hs => do
    let name := copyName g.name (hs.map (·.name))
    let st ← get
    if st.made.any (·.1 == name) || st.started.contains name then return name
    modify fun s => { s with started := name :: s.started }
    let .def_ dsp n ps A V mk := g.decl
      | throw ⟨sp, s!"internal error: `{g.name}` is not a function"⟩
    let q := (← get).quiet
    if env.lib.contains g.name then modify fun s => { s with quiet := true }
    let (A', V') ← fnCopy k env dsp n.name A V (g.row.filter (· != failEff)) hs g.err
    modify fun s => { s with quiet := q }
    report dsp "lowering" s!"copy `{name}`: `{g.name}` for {", ".intercalate (hs.map (·.name))}"
    modify fun s => { s with made := s.made.push (name, .def_ dsp ⟨name, n.span⟩ ps A' V' mk) }
    pure name

/-- A function's type and value with its body elaborated: taking the capabilities of `row`
(served by `hs`) first, and answering `T + E` when it raises `Fail[E]`. -/
def fnCopy : Nat → Env → Span → String → VTy → Val → List String → List HSig → Option VTy →
    EM (VTy × Val)
  | 0, _, sp, _, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, name, A, V, row, hs, err => do
    let f ← (fnParts sp name A V : Except Error FnParts)
    let cs := copyCaps row hs
    let raises := err.isSome
    let cx : Cx := { env, caps := cs, fnCaps := cs, fail := if raises then some false else none,
                     fnFail := raises, err }
    let body ← trC k cx cs true raises f.body
    let f := match err with
      | some E => { f with T := .sum sp f.T E }
      | none => f
    let f' ← if cs.isEmpty then pure { f with body } else takeCaps sp cs f body
    pure (f'.build sp)
end

/-! ### Handlers -/

/-- `bindParams`: the parameters `xs` bound from the tuple `p`. -/
def bindParams (sp : Span) (p : String) : List Ident → Comp → EM Comp
  | [], M => pure (.letUnit sp (.var sp p) M)
  | [x], M => pure (.bind sp x none (.ret sp (.var sp p)) M false)
  | [x, y], M => pure (.letPair sp x y (.var sp p) M)
  | x :: xs, M => do
    let r ← fresh "fx_p"
    pure (.letPair sp x ⟨r, sp⟩ (.var sp p) (← bindParams sp r xs M))

/-- The parameter tuple's type (`1` with no parameters). -/
def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- A computation with `f` applied at each terminal reached through tail positions. -/
def wrapTerms (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (wrapTerms f N) lin
  | .letUnit sp V M => .letUnit sp V (wrapTerms f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTerms f M)
  | .case sp V x M y N => .case sp V x (wrapTerms f M) y (wrapTerms f N)
  | .for_ sp x V M N => .for_ sp x V M (wrapTerms f N)
  | T => f T

/-- The clause of `h` for the operation `o`: `fn h__op<'l>(c: mut 'l S, x: A, …) -> mut 'l S * B`,
whose body runs the clause on the state by `modify` (`withswap`) and hands the borrow back. -/
def clauseDef (env : Env) (h : HSig) (o : OpDecl) (c : Clause) : EM Decl := do
  let sp := c.name.span
  unless c.params.length == o.params.length do
    throw ⟨sp, s!"the clause `{c.name.name}` of `{h.name}` takes {c.params.length} parameters, " ++
      s!"and the operation {o.params.length}"⟩
  if let some e := (rowC env fuel c.body).head? then
    throw ⟨sp, s!"the clause `{c.name.name}` of `{h.name}` performs an operation of `{e}`: a clause " ++
      "is code over the handler's state, and performs no operation"⟩
  let l := "fx_l"
  let cv := "fx_c"
  let st := h.st.name
  let v ← fresh "fx_v"
  let w ← fresh "fx_w"
  -- The clause's answer at the operation's result type; a terminal that lends a place is bound
  -- first, since a lend cannot be in an annotated binding.
  let body := wrapTerms (fun T =>
    let hand := Comp.ret T.span (.pair T.span (.var T.span st) (.var T.span v))
    match T with
    | .ret _ V => if V.lends then
        .bind T.span ⟨w, T.span⟩ none T
          (.bind T.span ⟨v, T.span⟩ (some o.res) (.ret T.span (.var T.span w)) hand false) false
      else .bind T.span ⟨v, T.span⟩ (some o.res) T hand false
    | _ => .bind T.span ⟨v, T.span⟩ (some o.res) T hand false) c.body
  let modifyV : Val := .app sp (.app sp (.sugar sp (.borrow .modify "")) (.var sp cv))
    (.thunkv sp (.lam sp h.st (.name sp "_") body))
  let b ← fresh "fx_b"
  let r ← fresh "fx_r"
  let inner : Comp := .bind sp ⟨b, sp⟩ none (.ret sp modifyV)
    (.letPair sp ⟨cv, sp⟩ ⟨r, sp⟩ (.var sp b) (.ret sp (.pair sp (.var sp cv) (.var sp r)))) false
  let p ← fresh "fx_p"
  let inner ← bindParams sp p c.params inner
  let pp ← fresh "fx_pp"
  let cap : Cap := ⟨h.eff, cv, l, h⟩
  let P := tupleTy sp (o.params.map (·.2))
  let f : FnParts := ⟨true, [(⟨l, sp⟩, .top sp)], capsTy sp [cap] P, capsTy sp [cap] o.res, ⟨pp, sp⟩,
    .letPair sp ⟨cv, sp⟩ ⟨p, sp⟩ (.var sp pp) inner⟩
  let (A, V) := f.build sp
  pure (.def_ sp ⟨clauseName h.name c.name.name, sp⟩ [] A V .none)

/-! ### Programs -/

/-- The names a declaration defines. -/
def Decl.defName : Decl → Option String
  | .def_ _ n _ _ _ _ => some n.name
  | _ => none

mutual
/-- A function with a row named in a value other than as the head of a call. -/
def valueUse (env : Env) : Nat → Val → Bool
  | 0, _ => false
  | n + 1, V => match V with
    | .var _ x => (env.fn? x).isSome
    | .app _ f W => (match headName f with
        | some x => (env.fn? x).isNone && valueUse env n f
        | none => valueUse env n f) || valueUse env n W
    | .pair _ V W => valueUse env n V || valueUse env n W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => valueUse env n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => valueUseC env n M
    | _ => false

/-- `valueUse` of a computation. -/
def valueUseC (env : Env) : Nat → Comp → Bool
  | 0, _ => false
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => valueUse env n V
    | .bind _ _ _ M N _ | .with_ _ M N => valueUseC env n M || valueUseC env n N
    | .letUnit _ V M | .letPair _ _ _ V M => valueUse env n V || valueUseC env n M
    | .case _ V _ M _ N | .for_ _ _ V M N =>
      valueUse env n V || valueUseC env n M || valueUseC env n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => valueUseC env n M
    | _ => false
end

/-- The mark of a definition without its written row, and the row. -/
def splitRow : Mark → List (Ident × List VTy) × Mark
  | .row es m => (es, m)
  | m => ([], m)

/-- Anything for this pass to do: an effect, a handler, a written row, a `raise` or a `try`. -/
def hasEffects (ds : List Decl) : Bool :=
  ds.any fun
    | .effect .. | .handler .. => true
    | .def_ _ _ _ _ V mk => (match mk with | .row .. => true | _ => false) || failIn fuel V
    | .main _ _ M => failIn.failInC fuel M
    | _ => false

/-- The program with its effects elaborated, the reports for `bcc check`, and the abort points
(each `raise` or raising call, with the binders in scope there): the effect and handler
declarations are removed, each handler's clauses become functions, each function with a row of
answering effects is replaced by its copies under the handlers it is called under, each function
that raises answers a sum, and each `with` becomes a borrow block.  `[spec §18]` -/
def elaborate (ds : List Decl) (lib : List String := []) :
    Except Error (List Decl × List (Span × String) × List (Span × List Span)) := do
  if !hasEffects ds then return (ds, [], [])
  let names := ds.filterMap Decl.defName
  if let some d := ds.find? (fun d => Decl.defName d == some raiseOp) then
    throw ⟨match d with | .def_ _ n .. => n.span | _ => Span.none,
      "`raise` is the operation of `Fail`: a function cannot be named so"⟩
  let go : EM (List Decl) := do
    let mut env : Env := { lib }
    let mut out : Array Decl := #[]
    for d in ds do
      match d with
      | .effect sp e ops =>
        if e.name == failEff then throw ⟨e.span, "`Fail` is the error effect, declared already"⟩
        if env.ops.any (·.eff == e.name) then throw ⟨e.span, s!"the effect `{e.name}` is declared twice"⟩
        for o in ops do
          if env.ops.any (·.decl.name.name == o.name.name) || names.contains o.name.name ||
              o.name.name == raiseOp then
            throw ⟨o.name.span, s!"`{o.name.name}` is already declared: an operation's name is its own"⟩
        env := { env with ops := env.ops ++ ops.map (⟨e.name, ·⟩) }
        report sp "effect" (s!"{e.name}: " ++ ", ".intercalate (ops.map (·.name.name)))
      | .handler sp h st S e cs =>
        let ops := env.ops.filter (·.eff == e.name)
        if ops.isEmpty then throw ⟨e.span, s!"no effect `{e.name}` is declared before this handler"⟩
        let hs : HSig := ⟨h.name, e.name, st, S, cs, sp⟩
        for o in ops do
          unless cs.any (·.name.name == o.decl.name.name) do
            throw ⟨sp, s!"the handler `{h.name}` has no clause for `{o.decl.name.name}`"⟩
        for c in cs do
          let some o := ops.find? (·.decl.name.name == c.name.name)
            | throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e.name}`"⟩
          out := out.push (← clauseDef env hs o.decl c)
        env := { env with handlers := env.handlers ++ [hs] }
        report sp "lowering" (s!"handler {h.name} ({e.name}): call — each clause resumes once, in " ++
          "tail position (fun): a direct call on the lent state (withswap), with no allocation and " ++
          "no dispatch")
      | .def_ sp n ps A V mk =>
        modify fun s => { s with quiet := lib.contains n.name }
        let (written, mk) := splitRow mk
        let row := rowV env fuel V
        if !written.isEmpty then
          if let some e := row.find? (fun e => !written.any (·.1.name == e)) then
            throw ⟨n.span, s!"`{n.name}` performs `{e}`, which its written row does not list"⟩
        let err ← if row.contains failEff then
            match written.find? (·.1.name == failEff) with
            | some (_, [E]) => pure (some E)
            | some (fe, _) => throw ⟨fe.span, "`Fail` takes one type, the error's: `Fail[E]`"⟩
            | none => match errV env fuel V with
              | some E => pure (some E)
              | none =>
                -- A function with `Fail` passed as a value is reported as such first.
                if valueUse env fuel V then discard (elabDef env V)
                throw ⟨n.span, s!"`{n.name}` raises, and the type of its error is not " ++
                  "determined: write it, `with Fail[E]`"⟩
          else pure none
        let answering := row.filter (· != failEff)
        let d₀ : Decl := .def_ sp n ps A V mk
        let rowTxt := ", ".intercalate (row.map fun e =>
          if e == failEff then s!"Fail[{(err.map (VTy.pp · 0)).getD "?"}]" else e)
        if !answering.isEmpty then
          env := { env with fns := env.fns ++ [⟨n.name, row, err, d₀⟩] }
          report sp "row" s!"{n.name}: {rowTxt}"
        else if err.isSome then
          -- Only `Fail`: the function itself answers a sum.
          let before := (← get).made.size
          let (A', V') ← fnCopy fuel env sp n.name A V [] [] err
          out := out ++ ((← get).made.extract before).map (·.2)
          out := out.push (.def_ sp n ps A' V' mk)
          env := { env with fns := env.fns ++ [⟨n.name, row, err, d₀⟩] }
          report sp "row" s!"{n.name}: {rowTxt}; it answers `inl` its value or `inr` the error"
        else
          let (V', copies) ← elabDef env V
          out := out ++ copies
          out := out.push (.def_ sp n ps A V' mk)
      | .main sp C M =>
        modify fun s => { s with quiet := false }
        let before := (← get).made.size
        let M' ← trC fuel { env, caps := [] } [] false false M
        out := out ++ ((← get).made.extract before).map (·.2)
        out := out.push (.main sp C M')
      | d => out := out.push d
    pure out.toList
  match go.run {} with
  | .ok (ds, st) => pure (ds, st.reports.toList, st.aborts.toList)
  | .error e => throw e
where
  /-- A function with no row: its `with`s and `try`s elaborated, and the copies they made. -/
  elabDef (env : Env) (V : Val) : EM (Val × Array Decl) := do
    let before := (← get).made.size
    let (bs, V') ← trV fuel { env, caps := [] } [] V
    unless bs.isEmpty do throw ⟨V.span, "internal error: a definition's value was taken apart"⟩
    pure (V', ((← get).made.extract before).map (·.2))

end Frontend.Elab.Effects
