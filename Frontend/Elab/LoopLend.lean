import Frontend.Elab.Meta
import Frontend.Check.Steps

/-!
# Frontend — Elab — borrow scopes over loops, per observation  `[spec §14]`

A borrow block's body is one computation: `withbor`'s callback returns before the block ends. A
loop is codata, observed one step at a time, so a block whose body loops cannot keep its borrow
open while the loop runs. What it can do is lend again at every step (`lib/lend.bc`,
`experiments/LoopBorrow`): the owner moves into the loop's state, and each step borrows it for that
step only, by an ordinary `withbor` inside one observation.

This module rewrites a borrow block whose body loops into that form, at the surface, before the
sugar is elaborated. For

    borrow imm t { 'x, b -> PRE; for y in V { M }; POST }

it gives the sequence

    let (t, vs) = borrow imm t { 'x, b -> PRE; vs };      -- when PRE uses the borrow
    for y in V { let (t, ws) = borrow imm t { 'x, b -> M; ws } };
    borrow imm t { 'x, b -> POST }

spliced into the enclosing body, so that the `for` is on its spine and is elaborated as any `for`
is (SPEC §14): the loop threads `t`, which each step rebinds. `vs` are the variables `PRE` binds
that what follows reads, and `ws` those that `M` assigns. A stretch of the body that does not use
the borrow is left outside any block. Nothing else changes: the blocks are ordinary borrow blocks,
elaborated by `Frontend/Sugar.lean`, and the checker sees only core.

The rewrite is sound for the same reason the per-observation lend is: every borrow it makes is
opened and closed inside one computation. It applies when what the loop holds between steps
outlives `'x`: the iterator does not hold the borrow (`iterError`), and what `PRE` hands on does
not have the borrow's lifetime in its type (`escapeError`, reported at the block).

The same rewrite serves three more forms:

* `let r = &x; S` (or `&mut x`) is the borrow block `borrow imm x { r -> S }` over the rest of
  the body, so a loop-invariant borrow is lent per observation (`lendLet`).
* A div function that takes a borrow, `!(all 'a < b. P => Q)` with one component `imm 'a A` of
  `P`, takes the owner `ref A` there instead and hands it back first; its body is a borrow block
  of the owner (`lentDef`). A call lends the place, `f(&t)`; inside a borrow block, the block's
  borrow passed to it is the place lent instead (`Env.lendCall`).
* A call `f(W)` of a function with lifetime parameters, written without them, is applied to the
  lifetimes `W`'s type gives them (`genericCall` in `Frontend/Sugar.lean`), so a borrow is passed
  as `f(b, …)`.
-/

namespace Frontend.Elab.LoopLend
open Frontend.Check (mentionsV mentionsC)

/-- A borrow block as the parser gives it: `borrow k P { 'x, b -> S }`. -/
structure Block where
  sp : Span
  ksp : Span
  k : BorrowKind
  x : String
  P : Val
  tsp : Span
  lsp : Span
  b : Ident
  S : Comp

/-- A borrow block (not `modify`). -/
def Block.of? : Val → Option Block
  | .app sp (.app _ (.sugar ksp (.borrow k x)) P) (.thunkv tsp (.lam lsp b _ S)) =>
    if k == .modify then none else some ⟨sp, ksp, k, x, P, tsp, lsp, b, S⟩
  | _ => none

/-- The same block on the place `P`, with the body `S`. -/
def Block.val (B : Block) (P : Val) (S : Comp) : Val :=
  .app B.sp (.app B.sp (.sugar B.ksp (.borrow B.k B.x)) P)
    (.thunkv B.tsp (.lam B.lsp B.b (.name B.lsp "_") S))

/-- The names a computation binds on its spine: those it binds for what follows, and those a
`for` or a `case` arm binds (a `for` threads the variables its body assigns). -/
def spineNames : Nat → Comp → List String
  | 0, _ => []
  | n + 1, .bind _ x _ _ N _ => x.name :: spineNames n N
  | n + 1, .letPair _ x y _ M => x.name :: y.name :: spineNames n M
  | n + 1, .letUnit _ _ M => spineNames n M
  | n + 1, .case _ _ x M y N => x.name :: y.name :: (spineNames n M ++ spineNames n N)
  | n + 1, .loop _ _ _ _ M N => spineNames n M ++ spineNames n N
  | _, _ => []

def fuel : Nat := 1 <<< 16

/-- Apply `f` to every terminal of a computation: through binds, `let`s, `case` arms and what
follows a `for`. -/
def spliceTail (f : Comp → Comp) : Nat → Comp → Comp
  | 0, M => M
  | n + 1, .bind sp x A M N lin => .bind sp x A M (spliceTail f n N) lin
  | n + 1, .letUnit sp V M => .letUnit sp V (spliceTail f n M)
  | n + 1, .letPair sp x y V M => .letPair sp x y V (spliceTail f n M)
  | n + 1, .case sp V x M y N => .case sp V x (spliceTail f n M) y (spliceTail f n N)
  | n + 1, .loop sp ℓ src V M N => .loop sp ℓ src V M (spliceTail f n N)
  | _, T => f T

/-- A right-nested tuple of variables (`()` when empty). -/
def tupleVal (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (tupleVal sp xs)

/-- Bind the names of a right-nested tuple held in `v`, then `K`. -/
def destruct (sp : Span) (v : String) : List String → Comp → Comp
  | [], K => .letUnit sp (.var sp v) K
  | [x], K => .bind sp ⟨x, sp⟩ none (.ret sp (.var sp v)) K false
  | [x, y], K => .letPair sp ⟨x, sp⟩ ⟨y, sp⟩ (.var sp v) K
  | x :: xs, K => .letPair sp ⟨x, sp⟩ ⟨v ++ "_t", sp⟩ (.var sp v) (destruct sp (v ++ "_t") xs K)

/-- A call in the head of a binding that makes the body loop: a call of a div function. -/
def isLoopHead (divCall : Val → Bool) : Comp → Bool
  | .ret _ V => divCall V
  | _ => false

/-- A `for x in V { M }; N` that is total: over a bounded source, elaborated to a counted loop
(SPEC §16, the total `for`; `boundedFor` in `Frontend/Sugar.lean`). It is one computation, not a
loop: a borrow block around it keeps its borrow open for the whole loop. -/
abbrev Finite := Val → Comp → Comp → Bool

/-- A loop is total by `fin`: only a `for` can be; a `while` or a `loop` never is. -/
def _root_.Frontend.LoopSrc.fin (src : LoopSrc) (fin : Finite) (V : Val) (M N : Comp) : Bool :=
  match src with
  | .each _ => fin V M N
  | _ => false

/-- A computation loops on its spine: a `for` that is not total, or a call of a div function in
the head of a binding or at a terminal. -/
def loopsOnSpine (divCall : Val → Bool) (fin : Finite) : Nat → Comp → Bool
  | 0, _ => false
  | n + 1, .bind _ _ _ M N _ => isLoopHead divCall M || loopsOnSpine divCall fin n N
  | n + 1, .letUnit _ _ M | n + 1, .letPair _ _ _ _ M => loopsOnSpine divCall fin n M
  | n + 1, .case _ _ _ M _ N => loopsOnSpine divCall fin n M || loopsOnSpine divCall fin n N
  | n + 1, .loop _ _ src V M N => !src.fin fin V M N || loopsOnSpine divCall fin n N
  | _ + 1, T => isLoopHead divCall T

/-- What the rewrite of one block works with. -/
structure Env where
  B : Block
  /-- The place as a value: a name, or a pair of names for a family. -/
  place : Val
  /-- The names the place is rebound to. -/
  placeNames : List String
  /-- The block's parameter and the names its pattern binds from it. -/
  aliases : List String
  /-- The pattern's bindings, at the start of each block's body. -/
  pre : Comp → Comp
  /-- A call of a div function. -/
  divCall : Val → Bool
  /-- A total `for`. -/
  fin : Finite

/-- Fresh names, by the block's position and a counter. -/
abbrev LM := StateT Nat (Except Error)

def Env.fresh (E : Env) (what : String) : LM String :=
  modifyGet fun k => (s!"io_{what}{E.B.sp.start.line}_{E.B.sp.start.col}_{k}", k + 1)

def Env.usesV (E : Env) (V : Val) : Bool := E.aliases.any (mentionsV · V)

def Env.usesC (E : Env) (M : Comp) : Bool := E.aliases.any (mentionsC · M)

/-- `(place, r)` held in `v`: rebind the place, and bind `r`. -/
def Env.rebind (E : Env) (sp : Span) (v r : String) (K : Comp) : Comp :=
  match E.placeNames with
  | [t] => .letPair sp ⟨t, sp⟩ ⟨r, sp⟩ (.var sp v) K
  | ps =>
    .letPair sp ⟨v ++ "_pl", sp⟩ ⟨r, sp⟩ (.var sp v) (destruct sp (v ++ "_pl") ps K)

/-- A borrow block around `body`, whose result is the tuple of `vs`, then `K` with the place and
`vs` rebound. -/
def Env.blockBind (E : Env) (sp : Span) (body : Comp) (vs : List String) (K : Comp) : LM Comp := do
  let v ← E.fresh "lb"
  let r ← E.fresh "lr"
  pure (.bind sp ⟨v, sp⟩ none (.ret sp (E.B.val E.place (E.pre body)))
    (E.rebind sp v r (destruct sp r vs K)) false)

/-- A stretch of the body's spine not yet placed: the bindings, the names they bind, and whether
they use the borrow. -/
structure Seg where
  wrap : Comp → Comp := id
  names : List String := []
  uses : Bool := false

def Seg.push (s : Seg) (f : Comp → Comp) (ns : List String) (u : Bool) : Seg :=
  { wrap := s.wrap ∘ f, names := s.names ++ ns, uses := s.uses || u }

/-- Place a stretch before `rest`: in a borrow block when it uses the borrow, handing on the
names it binds that `rest` reads. -/
def Env.flush (E : Env) (sp : Span) (s : Seg) (rest : Comp) : LM (Comp → Comp) := do
  if !s.uses then return s.wrap
  let vs := s.names.eraseDups.filter fun y => !E.aliases.contains y && mentionsC y rest
  let n ← get
  -- Build with a placeholder for the continuation, then substitute it.
  let hole := s!"io_lk{E.B.sp.start.line}_{E.B.sp.start.col}_{n}"
  set (n + 1)
  let L ← E.blockBind sp (s.wrap (.ret sp (tupleVal sp vs))) vs (.force sp ⟨hole, sp⟩)
  pure fun K => spliceTail (fun T => match T with
    | .force _ h => if h.name == hole then K else T
    | T => T) fuel L

/-- The body of a `for` inside the block: in a borrow block of its own when it uses the borrow,
handing on the variables in scope that it assigns. -/
def Env.forBody (E : Env) (scope : List String) (sp : Span) (ys : List String) (M : Comp) : LM Comp := do
  if !E.usesC M then return M
  let ws := (spineNames fuel M).eraseDups.filter fun z =>
    scope.contains z && !E.aliases.contains z && !ys.contains z
  let body := spliceTail (fun T => .bind T.span ⟨"io_u", T.span⟩ none T
    (.ret T.span (tupleVal T.span ws)) false) fuel M
  E.blockBind sp body ws (.ret sp (.unit sp))

/-- A terminal of the block's body, after the stretch `s`: the block's result `(place, r)`. -/
def Env.terminal (E : Env) (s : Seg) (T : Comp) : LM Comp := do
  if s.uses || E.usesC T then return .ret T.span (E.B.val E.place (E.pre (s.wrap T)))
  -- A value is paired with the place as it is, so that its components keep their names (a
  -- residual is handed back by name, SPEC §14).
  if let .ret sp V := T then return s.wrap (.ret sp (.pair sp E.place V))
  let r ← E.fresh "lt"
  pure (s.wrap (.bind T.span ⟨r, T.span⟩ none T (.ret T.span (.pair T.span E.place (.var T.span r))) false))

/-- The block's borrow passed to a call of a div function, `f(b)` (or `f['x](b)`): the call lends
the place instead, `f(&t)`, and the div function, elaborated to take the owner (`lentDef`), lends
it at each step of its loop. Only the block's parameter itself, once, on a single place. -/
def Env.lendCall (E : Env) : Comp → LM Comp
  | M@(.ret sp (.app asp f W)) => do
    if !E.usesC M then return M
    let b := E.B.b.name
    let f := match f with
      | .inst _ g _ => g
      | g => g
    let tooMuch := E.aliases.any (fun a => a != b && mentionsV a W) || mentionsV b f
    let m : Mode := if E.B.k == .mut then .mut else .imm
    match E.placeNames, tooMuch with
    | [t], false =>
      match replaceOnce b (.lend sp ⟨t, sp⟩ m) W with
      | some W' => pure (.ret sp (.app asp f W'))
      | none => throw (callError E M.span)
    | _, _ => throw (callError E M.span)
  | M => pure M
where
  /-- `W` with its one occurrence of the variable `b` (at a tuple position) replaced by `L`. -/
  replaceOnce (b : String) (L : Val) : Val → Option Val
    | .var _ y => if y == b then some L else none
    | .pair sp V W =>
      match mentionsV b V, mentionsV b W with
      | true, false => (replaceOnce b L V).map (.pair sp · W)
      | false, true => (replaceOnce b L W).map (.pair sp V ·)
      | _, _ => none
    | _ => none
  callError (E : Env) (sp : Span) : Error :=
    ⟨sp, s!"this call of a div function takes the borrow of `{E.B.b.name}` other than as an " ++
      "argument of its own: a borrow block over a loop lends its place again at each step, and " ++
      s!"the call's loop can take the place only as a lend, `&{E.placeNames.headD "x"}` " ++
      "(SPEC §14, borrow scopes over loops)"⟩

/-- The error for a borrow block whose result has the block's lifetime `'x` in its type `T`. -/
def escapeError (sp : Span) (x T : String) : Error :=
  ⟨sp, s!"this borrow block's result has type `{T}`, which has the block's lifetime `'{x}`: " ++
    s!"nothing borrowed at `'{x}` outlives the block. When the body loops, each step borrows the " ++
    "place again, so the loop cannot keep what is borrowed before it (SPEC §14, borrow scopes " ++
    "over loops)"⟩

/-- The error for an iterator that holds the borrow. -/
def iterError (E : Env) (src : LoopSrc) (sp : Span) : Error :=
  match src with
  | .each _ =>
    ⟨sp, s!"the iterator of this `for` holds the borrow of `{E.B.b.name}`: a borrow block over a " ++
      "loop lends its place again at each step, so what the loop holds between steps must not " ++
      "hold the borrow (SPEC §14, borrow scopes over loops)"⟩
  | _ =>
    ⟨sp, s!"the condition of this {src.what} uses the borrow of `{E.B.b.name}`: a borrow block " ++
      "over a loop lends its place again at each step, to the loop's body only, not to its " ++
      "condition (SPEC §14, borrow scopes over loops)"⟩

/-- The block's body, rewritten: each stretch that uses the borrow in a block of its own, each
`for` on the spine with its body lent per step. `scope` is the names in scope. -/
def Env.walk (E : Env) : Nat → List String → Seg → Comp → LM Comp
  | 0, _, _, M => throw ⟨M.span, "internal error: a borrow block over a loop nested too deeply"⟩
  | n + 1, scope, s, S@(.bind sp z A M N lin) => do
    if isLoopHead E.divCall M then
      let M ← E.lendCall M
      let pre ← E.flush sp s S
      pure (pre (.bind sp z A M (← E.walk n (scope ++ s.names ++ [z.name]) {} N) lin))
    else
      E.walk n (scope ++ [z.name]) (s.push (fun K => .bind sp z A M K lin) [z.name] (E.usesC M)) N
  | n + 1, scope, s, .letUnit sp V M =>
    E.walk n scope (s.push (fun K => .letUnit sp V K) [] (E.usesV V)) M
  | n + 1, scope, s, .letPair sp y z V M =>
    E.walk n (scope ++ [y.name, z.name])
      (s.push (fun K => .letPair sp y z V K) [y.name, z.name] (E.usesV V)) M
  | n + 1, scope, s, .loop sp ℓ src V M N =>
    if src.fin E.fin V M N then
      -- A total `for` is one computation: a statement of the stretch it is in.
      E.walk n scope (s.push (fun K => .loop sp ℓ src V M K) (spineNames fuel M)
        (E.usesV V || E.usesC M)) N
    else do
      if E.usesV V then throw (iterError E src V.span)
      let S := Comp.loop sp ℓ src V M N
      let pre ← E.flush sp s S
      let scope' := scope ++ s.names
      let M' ← E.forBody scope' sp src.bound M
      pure (pre (.loop sp ℓ src V M' (← E.walk n scope' {} N)))
  | n + 1, scope, s, S@(.case sp V y M z N) => do
    if !(loopsOnSpine E.divCall E.fin fuel M || loopsOnSpine E.divCall E.fin fuel N) then
      return (← E.terminal s S)
    -- The scrutinee is computed in the stretch before the arms, which are rewritten on their own.
    let (s, V) ← if E.usesV V then do
        let v ← E.fresh "ls"
        pure (s.push (fun K => .bind sp ⟨v, sp⟩ none (.ret sp V) K false) [v] true, Val.var sp v)
      else pure (s, V)
    let pre ← E.flush sp s (.case sp V y M z N)
    let scope' := scope ++ s.names
    pure (pre (.case sp V y (← E.walk n (scope' ++ [y.name]) {} M) z
      (← E.walk n (scope' ++ [z.name]) {} N)))
  | _ + 1, _, s, T => do
    if isLoopHead E.divCall T then
      -- A call of a div function at the end: bound, then the place and its result.
      let T ← E.lendCall T
      let pre ← E.flush T.span s T
      let r ← E.fresh "lt"
      return pre (.bind T.span ⟨r, T.span⟩ none T
        (.ret T.span (.pair T.span E.place (.var T.span r))) false)
    E.terminal s T

/-- The bindings of the block's pattern at the start of its body, `let (p, q) = b; …` (the
parser's, for a pattern), whose names borrow as `b` does: the names, the bindings, and the rest. -/
def patternPrefix : Nat → List String → Comp → List String × (Comp → Comp) × Comp
  | 0, as, M => (as, id, M)
  | n + 1, as, M@(.letPair sp x y (.var vsp v) N) =>
    if as.contains v then
      let (as', f, rest) := patternPrefix n (as ++ [x.name, y.name]) N
      (as', fun K => .letPair sp x y (.var vsp v) (f K), rest)
    else (as, id, M)
  | n + 1, as, M@(.letUnit sp (.var vsp v) N) =>
    if as.contains v then
      let (as', f, rest) := patternPrefix n as N
      (as', fun K => .letUnit sp (.var vsp v) (f K), rest)
    else (as, id, M)
  | _, as, M => (as, id, M)

/-- `x <- return B; N` where `B` is a borrow block whose body loops, rewritten per observation and
spliced into the enclosing body: `none` when `B` is not such a block. `c` is the typing context at
the binding.  `[spec §14]` -/
def lendBind (c : TCx) (divCall : Val → Bool) (fin' : TCx → Finite) (sp : Span) (x : Ident)
    (A : Option VTy) (V : Val) (N : Comp) (lin : Bool) : Except Error (Option Comp) := do
  let some B := Block.of? V | return none
  -- A `for` in the block's body is read in the body's context, where the block's borrow is bound:
  -- on an owned array it is a view, and a `for` over it a counted loop (SPEC §16).
  let cB : TCx := match c.tyV B.P, c.elabL (.dom B.lsp) with
    | some T, some dom =>
      let c₁ := c.pushLife B.x dom
      match c₁.E.lenv.lookup B.x with
      | some v =>
        let Tb : Option Frontend.Check.CVTy := match B.k, T with
          | .imm, .fam (.ref A) => some (.fam (.imm (.var v) A))
          | .mut, .fam (.ref A) => some (.fam (.mut (.var v) A))
          | .imm, .ref A => some (.imm (.var v) A)
          | .mut, .ref A => some (.mut (.var v) A)
          | _, _ => none
        c₁.push B.b.name Tb
      | none => c
    | _, _ => c
  let fin := fin' cB
  if !loopsOnSpine divCall fin fuel B.S then return none
  -- The place: a name, a pair of names (a family), or a value bound to a name first.
  let (bindP, place, placeNames) : (Comp → Comp) × Val × List String := match B.P with
    | .var vsp t => (id, .var vsp t, [t])
    | .pair psp (.var s₁ a) (.var s₂ b) => (id, .pair psp (.var s₁ a) (.var s₂ b), [a, b])
    | P =>
      let t := s!"io_lp{B.sp.start.line}_{B.sp.start.col}"
      (fun K => .bind P.span ⟨t, P.span⟩ none (.ret P.span P) K false, .var P.span t, [t])
  let (aliases, pre, S) := patternPrefix fuel [B.b.name] B.S
  let outer := c.locals.map (·.1)
  -- The rewrite puts the block's loop, and what its stretches bind, in the enclosing body. A name
  -- of the enclosing body that the block binds again (a `let` or an assignment) and that is read
  -- after the block would then see the block's binding: rejected rather than changed in meaning.
  for y in (spineNames fuel S).eraseDups do
    if outer.contains y && !aliases.contains y && mentionsC y N then
      throw ⟨B.sp, s!"`{y}` is bound inside this borrow block, which loops, and read after it: " ++
        "the block is lent per observation in the enclosing body, where its bindings would " ++
        s!"reach the code after it. Rename `{y}` inside the block, or read it there (SPEC §14, " ++
        "borrow scopes over loops)"⟩
  let E : Env := ⟨B, place, placeNames, aliases, pre, divCall, fin⟩
  let (L, _) ← (E.walk fuel outer {} S).run 0
  -- `x <- B; return x` is `B`'s rewrite itself.
  let rest : Comp → Comp := match N, A with
    | .ret _ (.var _ y), none => if y == x.name then id else fun T => .bind sp x A T N lin
    | _, _ => fun T => .bind sp x A T N lin
  pure (some (bindP (spliceTail rest fuel L)))

/-- `let r = &x; S` (or `&mut x`), with `x` a name: the borrow block `borrow imm x { r -> S }`
(`borrow mut`) over the rest of the body, after which `x` is rebound. The place may not be used
in `S`, where it is lent. `none` when the binding is not such a lend. -/
def lendLet (sp : Span) (r : Ident) (A : Option VTy) (M N : Comp) : Except Error (Option Comp) := do
  let .ret _ (.lend lsp x m) := M | return none
  -- A name the parser generated holds a lend it passes on (`f!(&mut c)`), not a `let r = &x`.
  if r.name.startsWith "io_" then return none
  if A.isSome then throw ⟨sp, s!"`let {r.name} = &{x.name}` takes its type from `{x.name}`: " ++
    "write it without an annotation"⟩
  if mentionsC x.name N then
    throw ⟨lsp, s!"`{x.name}` is lent to `{r.name}` for the rest of the block, so it cannot be " ++
      s!"used after `let {r.name} = {if m == .mut then "&mut " else "&"}{x.name}`"⟩
  let k : BorrowKind := if m == .mut then .mut else .imm
  let l := s!"io_ll{lsp.start.line}_{lsp.start.col}"
  let B := Val.app lsp (.app lsp (.sugar lsp (.borrow k l)) (.var x.span x.name))
    (.thunkv lsp (.lam lsp r (.name lsp "_") N))
  let v := s!"io_lv{lsp.start.line}_{lsp.start.col}"
  let res := s!"io_lr{lsp.start.line}_{lsp.start.col}"
  pure (some (.bind sp ⟨v, sp⟩ none (.ret sp B)
    (.letPair sp x ⟨res, sp⟩ (.var sp v) (.ret sp (.var sp res))) false))

/-- A call of a div function: its callee's result is a loop, with or without a lifetime binder. -/
def divCallIn (c : TCx) : Val → Bool
  | .app _ f _ => match c.tyV f with
    | some (.bang (.thunk (.all _ _ (.ret F)))) | some (.thunk (.all _ _ (.ret F))) =>
      (loopFnOf F).isSome
    | some F => (loopFnOf F).isSome
    | none => false
  | _ => false

/-! ### Div functions taking a borrow -/

/-- The components of a right-nested tuple type. -/
def spineTy : VTy → List VTy
  | .tensor _ A B => A :: spineTy B
  | A => [A]

/-- The right-nested tuple type of the components. -/
def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- The destructuring of a parameter `x` along its tuple's spine at the start of a body, as the
parser writes a pattern: `let (a, r) = x; let (b, c) = r; M` gives `[a, b, c]` and `M`. -/
def spinePattern : Nat → Nat → String → Comp → Option (List Ident × Comp)
  | 0, _, _, _ => none
  | _, 1, x, M => some ([⟨x, M.span⟩], M)
  | f + 1, k + 1, x, .letPair _ a r (.var _ v) M =>
    if v == x then (spinePattern f k r.name M).map fun (ns, M) => (a :: ns, M) else none
  | _, _, _, _ => none

/-- A div function taking a borrow of a cell, `!(all 'a < b. P => Q)` with a component
`imm 'a A` (or `mut 'a A`) of `P`, whose body loops: elaborated to take the owner, `ref A`, in
that component and hand it back first, `!(P' => ref A * Q)`, with its body in a borrow block of
the owner, which the per-observation lend then rewrites (`lendBind`). A call lends the place,
`f(&t)`. So a div function over a borrow is called in direct style from a borrow scope with no
spanning lend: each step of its loop borrows the owner for that step. `none` when the `def` is
not of that form.  `[spec §14]` -/
def lentDef (c : TCx) (fin' : TCx → Finite) : Decl → Except Error (Option Decl)
  | .def_ sp n [] (.bang asp (.all lsp y bd (.lolli fsp P Q)))
      (.bangThunkv vsp (.lamL _ y' _ (.ret _ (.thunkv _ (.lam lamsp x _ M))))) mk => do
    if y.name != y'.name then return none
    let some bl := c.elabL bd | return none
    let c' := c.pushLife y.name bl
    let ps := spineTy P
    -- The parameters, bound in the context a `for` of the body is read in.
    let one : List Ident := match M with
      | .bind _ y _ (.ret _ (.var _ z)) _ _ => if z == x.name then [x, y] else [x]
      | _ => [x]
    let cP := match (if ps.length == 1 then some (one, M) else spinePattern fuel ps.length x.name M) with
      | some (names, _) =>
        if ps.length == 1 then names.foldl (fun c nm => c.push nm.name (c.elabV P)) c'
        else (names.zip ps).foldl (fun c (nm, T) => c.push nm.name (c.elabV T)) c'
      | none => c'
    if !loopsOnSpine (divCallIn c') (fin' cP) fuel M then return none
    -- The one component borrowed at the parameter's lifetime.
    let borrowed := (ps.zip (List.range ps.length)).filterMap fun
      | (.imm _ (.var _ a) A, i) => if a == y.name then some (i, BorrowKind.imm, A) else none
      | (.mut _ (.var _ a) A, i) => if a == y.name then some (i, BorrowKind.mut, A) else none
      | _ => none
    let [(i, k, A)] := borrowed
      | throw ⟨lsp, s!"`{n.name}` loops, so it is called in direct style one step at a time, and " ++
          s!"a borrow at `'{y.name}` cannot stay open across its steps: it may take one borrow " ++
          s!"of a cell at `'{y.name}`, `imm '{y.name} A` or `mut '{y.name} A`, which it borrows " ++
          "again at each step (SPEC §14, borrow scopes over loops)"⟩
    let some (names, M) := if ps.length == 1 then some ([x], M)
        else spinePattern fuel ps.length x.name M
      | throw ⟨lamsp, s!"`{n.name}` loops and takes a borrow in a tuple: destructure its " ++
          "parameter first, `let (b, …) = p;` (SPEC §14, borrow scopes over loops)"⟩
    let own := s!"io_own_{n.name}"
    let arg := s!"io_arg_{n.name}"
    let ps' := ps.set i (.ref asp A)
    let names' := (names.set i ⟨own, lamsp⟩).map (·.name)
    let blk := Val.app lamsp (.app lamsp (.sugar lamsp (.borrow k y.name)) (.var lamsp own))
      (.thunkv lamsp (.lam lamsp (names.getD i x) (.name lamsp "_") M))
    let v := s!"io_lb_{n.name}"
    let body := destruct lamsp arg names'
      (.bind lamsp ⟨v, lamsp⟩ none (.ret lamsp blk) (.ret lamsp (.var lamsp v)) false)
    let A' := VTy.bang asp (.lolli fsp (tupleTy fsp ps') (.tensor fsp (.ref asp A) Q))
    pure (some (.def_ sp n [] A' (.bangThunkv vsp (.lam lamsp ⟨arg, lamsp⟩ (tupleTy fsp ps') body))
      mk))
  | _ => pure none

/-- The binding `x <- M; N` of a body, rewritten when `M` is a borrow block over a loop or
`N` follows a `let r = &x`.  `[spec §14]` -/
def hook (c : TCx) (fin : TCx → Finite) (sp : Span) (x : Ident) (A : Option VTy) (M N : Comp)
    (lin : Bool) : Except Error (Option Comp) := do
  if let some L ← lendLet sp x A M N then return some L
  match M with
  | .ret _ V => lendBind c (divCallIn c) fin sp x A V N lin
  | _ => pure none

end Frontend.Elab.LoopLend
