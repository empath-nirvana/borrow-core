import Frontend.Parser

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

Resolution is lexical: an operation goes to the innermost `with` of its effect around it, or to
the capability the enclosing function was given.

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

/-- A function with a non-empty row: its declaration and the effects it performs. -/
structure FSig where
  name : String
  row : List String
  decl : Decl

/-- What the elaboration knows: the operations, the handlers and the functions with a row, each
declared before the point being elaborated. -/
structure Env where
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

abbrev EM := StateT St (Except Error)

def fresh (pre : String) : EM String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

def report (sp : Span) (msg : String) : EM Unit :=
  modify fun s => { s with reports := s.reports.push (sp, msg) }

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
    | .app _ f W =>
      let head := match headName f with
        | some x => match env.op? x, env.fn? x with
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

/-- The capabilities of `cx` for the effects `row`, in the order of `cx.caps`. -/
def Cx.need (cx : Cx) (row : List String) : List Cap := cx.caps.filter (row.contains ·.eff)

def Cx.needV (cx : Cx) (V : Val) : List Cap := cx.need (rowV cx.env fuel V)
def Cx.needC (cx : Cx) (M : Comp) : List Cap := cx.need (rowC cx.env fuel M)

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
        if !(cx.needV V).isEmpty then do pure (.app sp f (← liftPlain cx k W))
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

/-- A lend in the arguments of a call that threads a capability is not provided. -/
def noLend (sp : Span) (what : String) (W : Val) : EM Unit := do
  if W.lends then
    throw ⟨sp, s!"a place is lent (`&mut x`) in the arguments of {what}, which also threads a " ++
      "capability: lend it in a call of its own"⟩

mutual
/-- `M` with its operations made calls on the capabilities `cs`, handing them back beside its
result: each terminal answering `v` answers `(c₁, (…, (cₙ, v)))`. With `wrap := false` (the body
of a loop, which threads them by name), the terminals are kept, and the capabilities are only
bound again. A `with` inside is elaborated either way. -/
def trC : Nat → Cx → List Cap → Bool → Comp → EM Comp
  | 0, _, _, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, M => do
    match M with
    | .ret sp V =>
      let (bs, V') ← trV n cx cs V
      let T := if isExit V' || !wrap then Comp.ret sp V' else .ret sp (capsTuple sp cs V')
      chain bs T
    | .bind sp x A M N lin =>
      let N' ← trC n cx cs wrap N
      let csM := cx.needC M
      if csM.isEmpty then
        pure (.bind sp x A (← trC n cx [] false M) N' lin)
      else if let .ret rsp V := M then
        -- A value: its effectful calls bound before the binding, which keeps its form.
        let (bs, V') ← trV n cx cs V
        chain bs (.bind sp x A (.ret rsp V') N' lin)
      else
        -- `M` hands back the capabilities it uses, which are bound again for `N`.
        let t ← fresh "fx_b"
        let M' ← trC n cx csM true M
        let body ← if lin then do
            let r ← fresh "fx_v"
            unpack sp csM r t (.bind sp x none (.ret sp (.var sp r)) N' true)
          else unpack sp csM x.name t N'
        pure (bindFlat sp t (A.map (capsTy sp csM)) M' body)
    | .letUnit sp V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letUnit sp V' (← trC n cx cs wrap M))
    | .letPair sp x y V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letPair sp x y V' (← trC n cx cs wrap M))
    | .case sp V x M y N =>
      let (bs, V') ← trV n cx cs V
      chain bs (.case sp V' x (← trC n cx cs wrap M) y (← trC n cx cs wrap N))
    | .for_ sp x V M N =>
      let (bs, V') ← trV n cx cs V
      -- The body rebinds the capabilities it uses by name, and the loop threads them.
      chain bs (.for_ sp x V' (← trC n cx [] false M) (← trC n cx cs wrap N))
    | .absurd sp V =>
      let (bs, V') ← trV n cx cs V
      chain bs (.absurd sp V')
    | T =>
      if let some c := (cx.needC T).head? then
        throw ⟨T.span, s!"an operation of `{c.eff}` is performed here, in a form that does not " ++
          "thread its capability"⟩
      if !wrap || cs.isEmpty then return T
      let r ← fresh "fx_t"
      pure (.bind T.span ⟨r, T.span⟩ none T (.ret T.span (capsTuple T.span cs (.var T.span r))) false)

/-- A value with its effectful calls lifted out before it, as bindings that thread the
capabilities `cs`; the value refers to their results. Every plain call evaluated before an
effectful one is lifted too, so the calls keep their order. -/
def trV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | n + 1, cx, cs, V => do
    let needs := !(cx.needV V).isEmpty
    -- An effect with no handler in scope is reported where it is performed (`goV`).
    let unhandled := (rowV cx.env fuel V).any fun e => (cx.capOf e).isNone
    if !needs && !unhandled && !withInV fuel V then return ([], V)
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
      if csM.isEmpty then
        let M' ← trC k cx [] false M
        return (bsP, .app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M')))
      let M' ← trC k cx csM true M
      let blk := Val.app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M'))
      let t ← fresh "fx_b"
      let pl ← fresh "fx_pl"
      let q ← fresh "fx_q"
      let r ← fresh "fx_v"
      let bind : Bind := fun N => do
        pure (.bind sp ⟨t, sp⟩ none (.ret sp blk)
          (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) (← unpack sp csM r q N)) false)
      pure (bsP ++ [bind], .pair sp (.var sp pl) (.var sp r))
    | .app sp f W => do
      match headName f with
      | some x =>
        match cx.env.op? x, cx.env.fn? x with
        | some o, _ => opCall k cx cs sp x o W
        | none, some g =>
          if (cx.need g.row).isEmpty && !(g.row.isEmpty) then
            throw ⟨sp, s!"`{x}` performs `{", ".intercalate g.row}`, but no handler of it is in " ++
              "scope here"⟩
          else fnCall k cx cs sp f x g W
        | none, none => plainApp k cx cs sp f W
      | none => plainApp k cx cs sp f W
    | .var sp x => do
      match cx.env.fn? x with
      | some g =>
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
      if csM.isEmpty then return ([], .run sp (← trC k cx [] false M))
      let M' ← trC k cx csM true M
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      let bind : Bind := fun N => do
        pure (bindFlat sp t none M' (← unpack sp csM r t N))
      pure ([bind], .var sp r)
    | .thunk sp M | .thunkv sp M | .bangThunk sp M | .bangThunkv sp M => do
      match (cx.needC M).head? with
      | some c => throw (notInClosure sp c.eff)
      | none =>
        -- A closure sees no capability of the enclosing body; a `with` inside it is its own.
        let M' ← trC k { cx with caps := [], fnCaps := [] } [] false M
        pure ([], match V with
          | .thunk .. => .thunk sp M' | .thunkv .. => .thunkv sp M'
          | .bangThunk .. => .bangThunk sp M' | _ => .bangThunkv sp M')
    | V => pure ([], V)

/-- A plain application, its parts elaborated. `return e` from a loop's body in a copy hands the
capabilities back too. -/
def plainApp : Nat → Cx → List Cap → Span → Val → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, W => do
    if let .sugar _ .retE := f then
      let (b, W') ← goV k cx cs W
      return (b, .app sp f (if cx.fnCaps.isEmpty then W' else capsTuple sp cx.fnCaps W'))
    let (b₁, f') ← goV k cx cs f
    let (b₂, W') ← goV k cx cs W
    pure (b₁ ++ b₂, .app sp f' W')

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
    report sp s!"{x} ({o.eff}): a call of `{clauseName c.h.name x}` on the state of `{c.h.name}`"
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ (some (capsTy sp [c] o.decl.res)) (.ret sp call)
        (← unpack sp [c] r t N) false)
    pure (b ++ [bind], .var sp r)

/-- `f(W)` of a function with a row: a call of its copy under the handlers in scope, which takes
their capabilities first and hands them back first. -/
def fnCall : Nat → Cx → List Cap → Span → Val → String → FSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, g, W => do
    let mut used : Array Cap := #[]
    for e in g.row do
      match cx.capOf e with
      | some c => used := used.push c
      | none => throw ⟨sp, s!"`{x}` performs `{e}`, but no handler of `{e}` is in scope here"⟩
    noLend sp s!"`{x}`" W
    let (b, W') ← goV k cx cs W
    let usedL := used.toList
    let name ← copyOf k cx.env sp g (usedL.map (·.h))
    let f' : Val := match f with
      | .defApp fsp _ As => .defApp fsp name As
      | _ => .var f.span name
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    report sp s!"{x} ({", ".intercalate g.row}): a call of `{name}`, passing the capabilities"
    -- The binding is annotated when the result's type is known here, so that what follows is
    -- typed whatever the call's lifetimes.
    let ann := (closedResult g.decl).map (capsTy sp usedL)
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ ann (.ret sp (.app sp f' (capsTuple sp usedL W')))
        (← unpack sp usedL r t N) false)
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
    let cx' : Cx := { cx with caps := cap :: cx.caps.filter (·.eff != hs.eff) }
    let csM := cx'.needC M
    let outer := csM.filter (·.eff != hs.eff)
    let where_ := match P' with
      | .lend _ x _ => s!"lent from `{x.name}`"
      | _ => "in a cell scoped to the block"
    report ksp (s!"with {h} ({hs.eff}): a borrow block of its state ({where_}); each operation a " ++
      "call of its clause")
    -- The body hands back the enclosing capabilities it uses; its own is dropped at its end.
    let body ← trC k cx' outer true M
    let blk := Val.app sp (.app sp₂ (.sugar ksp (.borrow .mut l)) place)
      (.thunkv tsp (.lam lsp b A body))
    if outer.isEmpty then return (bsP, blk)
    let t ← fresh "fx_b"
    let pl ← fresh "fx_pl"
    let q ← fresh "fx_q"
    let r ← fresh "fx_v"
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ none (.ret sp blk)
        (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) (← unpack sp outer r q N)) false)
    pure (bsP ++ [bind], .pair sp (.var sp pl) (.var sp r))

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
    let f ← (fnParts dsp n.name A V : Except Error FnParts)
    let cs := copyCaps g.row hs
    let cx : Cx := ⟨env, cs, cs⟩
    let body ← trC k cx cs true f.body
    let f' ← takeCaps dsp cs f body
    let (A', V') := f'.build dsp
    report dsp s!"{g.name} under {", ".intercalate (hs.map (·.name))}: the copy `{name}`"
    modify fun s => { s with made := s.made.push (name, .def_ dsp ⟨name, n.span⟩ ps A' V' mk) }
    pure name
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

/-- The program with its effects elaborated, and the reports for `bcc check`: the effect and
handler declarations are removed, each handler's clauses become functions, each function with a
row is replaced by its copies under the handlers it is called under, and each `with` becomes a
borrow block.  `[spec §18]` -/
def elaborate (ds : List Decl) : Except Error (List Decl × List (Span × String)) := do
  if !(ds.any fun | .effect .. | .handler .. => true | _ => false) then return (ds, [])
  let names := ds.filterMap Decl.defName
  let go : EM (List Decl) := do
    let mut env : Env := {}
    let mut out : Array Decl := #[]
    for d in ds do
      match d with
      | .effect sp e ops =>
        if env.ops.any (·.eff == e.name) then throw ⟨e.span, s!"the effect `{e.name}` is declared twice"⟩
        for o in ops do
          if env.ops.any (·.decl.name.name == o.name.name) || names.contains o.name.name then
            throw ⟨o.name.span, s!"`{o.name.name}` is already declared: an operation's name is its own"⟩
        env := { env with ops := env.ops ++ ops.map (⟨e.name, ·⟩) }
        report sp (s!"effect {e.name}: " ++ ", ".intercalate (ops.map (·.name.name)))
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
        report sp (s!"handler {h.name} ({e.name}): each clause answers once, in tail position: a " ++
          "direct call on the lent state (withswap), with no allocation and no dispatch")
      | .def_ sp n _ _ V _ =>
        let row := rowV env fuel V
        if row.isEmpty then
          let (V', copies) ← elabDef env V
          out := out ++ copies
          out := out.push (match d with
            | .def_ sp n ps A _ mk => .def_ sp n ps A V' mk
            | d => d)
        else
          env := { env with fns := env.fns ++ [⟨n.name, row, d⟩] }
          report sp (s!"effects {n.name}: " ++ ", ".intercalate row)
      | .main sp C M =>
        let before := (← get).made.size
        let M' ← trC fuel ⟨env, [], []⟩ [] false M
        out := out ++ ((← get).made.extract before).map (·.2)
        out := out.push (.main sp C M')
      | d => out := out.push d
    pure out.toList
  match go.run {} with
  | .ok (ds, st) => pure (ds, st.reports.toList)
  | .error e => throw e
where
  /-- A function with no row: its `with`s elaborated, and the copies they made. -/
  elabDef (env : Env) (V : Val) : EM (Val × Array Decl) := do
    let before := (← get).made.size
    let (bs, V') ← trV fuel ⟨env, [], []⟩ [] V
    unless bs.isEmpty do throw ⟨V.span, "internal error: a definition's value was taken apart"⟩
    pure (V', ((← get).made.extract before).map (·.2))

end Frontend.Elab.Effects
