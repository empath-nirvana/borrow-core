import Frontend.Lexer
import Frontend.Consts
import Frontend.FloatLit
import Frontend.Elab.Hygiene
import Frontend.Elab.Data
import Frontend.Elab.Frames
/-!
# Frontend — Parser

Recursive descent over the tokens of `Frontend/Lexer.lean`, following the grammar,
precedence and scoping of syntax-core §3–§6 and §10.

**Types are sorted after parsing** (syntax-core §4). A type is first parsed into `RTy`, one
tree for value and computation types with the precedence of §4, and then sorted by `RTy.toV`
and `RTy.toC` into `VTy`/`CTy`; a type of the wrong sort (`F A * B`) is reported there with its
span. Terms need no such pass: which category a position takes is fixed by the grammar (§6).

**Termination.** Every parsing function takes a fuel argument and recurses structurally on
it: each call passes `fuel - 1` to the functions it calls, and the loops over suffixes and
declarations pass `fuel - 1` to their next iteration. Fuel therefore bounds the depth of the
call tree. Along any chain of calls at most a fixed number of calls (`fuelPerToken`) are made
before a token is consumed, so `fuelPerToken * (tokens + 1)` suffices for every input; running
out is reported as an error ("expression nested too deeply") rather than assumed impossible.
-/

namespace Frontend

open BoCa (Width)

/-! ### Raw types -/

/-- A type before sorting: the union of the value and computation formers, with `-o` and
    `=>` kept apart. -/
inductive RTy where
  | unit (sp : Span)
  | zero (sp : Span)
  | tensor (sp : Span) (A B : RTy)
  | sum (sp : Span) (A B : RTy)
  | U (sp : Span) (C : RTy)
  | F (sp : Span) (A : RTy)
  | ref (sp : Span) (A : RTy)
  | imm (sp : Span) (a : Life) (A : RTy)
  | mut (sp : Span) (a : Life) (A : RTy)
  | box (sp : Span) (a : Life) (A : RTy)
  | bang (sp : Span) (A : RTy)
  | unk (sp : Span)
  | int (sp : Span) (w : Width)
  | handle (sp : Span) (k : HostKind)
  | mu (sp : Span) (X : Ident) (A : RTy)
  | name (sp : Span) (n : String)
  /-- `A => B`. -/
  | lolli (sp : Span) (A B : RTy)
  /-- `A -o C`. -/
  | arr (sp : Span) (A C : RTy)
  | all (sp : Span) (x : Ident) (b : Life) (A : RTy)
  | forall_ (sp : Span) (x : Ident) (b : Life) (C : RTy)
  | amp (sp : Span) (C D : RTy)
  | top (sp : Span)
  | block (sp : Span) (σ : Shape)
  | val (sp : Span) (σ : Shape)
  | fam (sp : Span) (m : Mode) (a : Life) (σ : Shape)
  | view (sp : Span) (a : Life) (A : RTy)
  | array (sp : Span) (A : RTy)
  | arrayImm (sp : Span) (a : Life) (A : RTy)
  | arrayMut (sp : Span) (a : Life) (A : RTy)
  | sized (sp : Span) (D S A : RTy)
  | nu (sp : Span) (X : Ident) (C : RTy)
  | delay (sp : Span) (A : RTy)
  | stream (sp : Span) (A : RTy)
  | iter (sp : Span) (A R R' : RTy)
  | loop (sp : Span) (A B : RTy)
  | pull (sp : Span) (A B R : RTy)
  /-- `F[…] A`, the row's types already sorted. -/
  | eff (sp : Span) (r : Row) (A : RTy)
  /-- `N[A, …]` and `N[…]<'a, …>`, curried: the arguments of a parameterised `type`. -/
  | app (sp : Span) (F A : RTy)
  | lapp (sp : Span) (F : RTy) (a : Life)
  /-- `(A => B with E₁, E₂[T])`: a function type with a provided row (`VTy.rowed`).  `[spec §33]` -/
  | rowed (sp : Span) (F : RTy) (effs : List (Ident × List VTy))

def RTy.span : RTy → Span
  | .unit sp | .zero sp | .tensor sp _ _ | .sum sp _ _ | .U sp _ | .F sp _ | .ref sp _
  | .imm sp _ _ | .mut sp _ _ | .box sp _ _ | .bang sp _ | .unk sp | .int sp _ | .handle sp _ | .mu sp _ _
  | .name sp _ | .lolli sp _ _ | .arr sp _ _ | .all sp _ _ _ | .forall_ sp _ _ _ | .amp sp _ _
  | .top sp | .block sp _ | .val sp _ | .fam sp _ _ _ | .view sp _ _ | .nu sp _ _ | .delay sp _
  | .stream sp _ | .iter sp _ _ _ | .loop sp _ _ | .pull sp _ _ _ | .array sp _ | .arrayImm sp _ _
  | .arrayMut sp _ _ | .sized sp _ _ _ | .eff sp _ _ | .app sp _ _ | .lapp sp _ _
  | .rowed sp _ _ => sp

/-- What a raw type is, for sort errors. -/
def RTy.former : RTy → String
  | .F .. => "`F A`" | .arr .. => "`A -o C`" | .forall_ .. => "`forall 'x < @. C`"
  | .amp .. => "`C & D`" | .top .. => "`top`" | .nu .. => "`nu X. C`" | .delay .. => "`delay A`"
  | .stream .. => "`stream A`" | .iter .. => "`iter A R R'`" | .loop .. => "`loop A B`"
  | .pull .. => "`pull A B R`" | .eff .. => "`F[…] A`"
  | _ => "this type"

private def sortErr (t : RTy) (isComp : Bool) : Except Error α :=
  if isComp then
    .error ⟨t.span, s!"{t.former} is a computation type, but a value type is expected here"⟩
  else
    .error ⟨t.span, "this is a value type, but a computation type is expected here"⟩

mutual
/-- Sort a raw type as a value type. -/
def RTy.toV : RTy → Except Error VTy
  | .unit sp => pure (.unit sp)
  | .zero sp => pure (.zero sp)
  | .tensor sp A B => return .tensor sp (← A.toV) (← B.toV)
  | .sum sp A B => return .sum sp (← A.toV) (← B.toV)
  | .U sp (.name sp' X) => pure (.thunk sp (.name sp' X))
  | .U sp C => return .thunk sp (← C.toC)
  | .ref sp A => return .ref sp (← A.toV)
  | .imm sp a A => return .imm sp a (← A.toV)
  | .mut sp a A => return .mut sp a (← A.toV)
  | .box sp a A => return .box sp a (← A.toV)
  | .bang sp A => return .bang sp (← A.toV)
  | .unk sp => pure (.unk sp)
  | .int sp w => pure (.int sp w)
  | .handle sp o => pure (.handle sp o)
  | .mu sp X A => return .mu sp X (← A.toV)
  | .name sp n => pure (.name sp n)
  | .lolli sp A B => return .lolli sp (← A.toV) (← B.toV)
  | .all sp x b A => return .all sp x b (← A.toV)
  | .block sp σ => pure (.block sp σ)
  | .val sp σ => pure (.val sp σ)
  | .fam sp m a σ => pure (.fam sp m a σ)
  | .view sp a A => return .view sp a (← A.toV)
  | .array sp A => return .array sp (← A.toV)
  | .arrayImm sp a A => return .arrayImm sp a (← A.toV)
  | .arrayMut sp a A => return .arrayMut sp a (← A.toV)
  | .sized sp D S A => return .sized sp (← D.toV) (← S.toV) (← A.toV)
  | .app sp G A => return .app sp (← G.toV) (← A.toV)
  | .lapp sp G a => return .lapp sp (← G.toV) a
  | .rowed sp G es => do
    match ← G.toV with
    | H@(.lolli ..) => pure (.rowed sp H (VTy.ofRowEffs sp es))
    | H => .error ⟨H.span, "a provided row `with E` is written on a function type `A => B`"⟩
  | t@(.F ..) | t@(.arr ..) | t@(.forall_ ..) | t@(.amp ..) | t@(.top ..) | t@(.nu ..)
  | t@(.delay ..) | t@(.stream ..) | t@(.iter ..) | t@(.loop ..) | t@(.pull ..)
  | t@(.eff ..) => sortErr t true

/-- Sort a raw type as a computation type. -/
def RTy.toC : RTy → Except Error CTy
  | .F sp A => return .ret sp (← A.toV)
  | .arr sp A C => return .arr sp (← A.toV) (← C.toC)
  | .amp sp C D => return .amp sp (← C.toC) (← D.toC)
  | .top sp => pure (.top sp)
  | .forall_ sp x b C => return .all sp x b (← C.toC)
  | .nu sp X C => return .nu sp X (← C.toC)
  | .delay sp A => return .delay sp (← A.toV)
  | .stream sp A => return .stream sp (← A.toV)
  | .iter sp A R R' => return .iter sp (← A.toV) (← R.toV) (← R'.toV)
  | .loop sp A B => return .loop sp (← A.toV) (← B.toV)
  | .pull sp A B R => return .pull sp (← A.toV) (← B.toV) (← R.toV)
  | .eff sp r A => return .eff sp r (← A.toV)
  | t => sortErr t false
end

/-! ### The parser monad -/

/-- `BCC_FRAMES=1`: `let mut` elaborated by the frame rules (#632, a prototype behind a flag): a
`let mut` is a slot of its body's frame (`Frontend.Elab.Frames`).  `[spec §43]` -/
initialize framesEnv : Bool ← do return (← IO.getEnv "BCC_FRAMES") == some "1"

/-- `BCC_FRAMES_LIB=thread`: the library modules keep the threading elaboration under
`BCC_FRAMES=1`, so that a program's own `let mut`s are measured apart from the library's. -/
initialize framesLibEnv : Bool ← do return (← IO.getEnv "BCC_FRAMES_LIB") != some "thread"

structure PState where
  toks : Array Token
  pos : Nat
  /-- The end of the last consumed token. -/
  lastStop : Pos
  /-- The next number for a generated name. -/
  fresh : Nat := 0
  /-- Inside `< M, N >`, where `>` is not an operator. -/
  angle : Bool := false
  /-- The `let mut` variables in scope. -/
  muts : List String := []
  /-- The `let mut` variables assigned since the enclosing `match` or `if` arm began. -/
  assigned : List String := []
  /-- The variables the `match` or `if` just parsed assigns, which it must hand on. -/
  joined : List String := []
  /-- Inside the body of a loop of a function's body (and not inside a closure or block in it),
  where a statement `return e` returns from the function from any depth of its loops. -/
  inLoop : Bool := false
  /-- In the body of a surface `fn` or `main ->` (not a core `def`), where a loop's body may
  `return` from the function. -/
  surf : Bool := false
  /-- The variables the borrow block just read hands back beside its result: the `let mut`
  variables it assigns and the places it lends (`borrowBlock`). -/
  blockThreads : List String := []
  /-- Resolution (SPEC §41, rule R1): on for a program's source, off for the elaborator's
  templates, whose rebindings are threading it generated. -/
  resolve : Bool := false
  /-- The variables in scope: each name as written, the binder it resolves to, and the binder's
  number (`occs`), innermost first. -/
  scope : List (String × String × Nat) := []
  /-- The number of the next binder. -/
  nextBinder : Nat := 0
  /-- The names a renamed binder may not take: every name the source writes, and the binders
  renamed so far. -/
  taken : List String := []
  /-- Each renamed binder, and the name the source writes it with. -/
  renamed : List (String × String) := []
  /-- A `run` just read that hands back what it writes (`blockThreads`): its binding must take
  them apart (SPEC §41, rule R3). -/
  pendingRun : Option Span := none
  /-- Each name of the source that resolution resolved to a variable: where it is written, as
  written, and the number of its binder, one per binder of the source (`resolutionOf`,
  `bcc alpha`). -/
  occs : List (Pos × String × String × Nat) := []
  /-- The `data` declarations in scope (SPEC §42): the prelude's, the included modules', and the
  program's own, wherever they are in it. -/
  data : Data.Table := []
  /-- In the value of a field update `x.f = e` (SPEC §42, E6): the variable `x` resolves to, and
  the record `r` its body takes apart; `x.g` in `e` reads `r`'s field `g`, the variable `r_g`. -/
  updating : Option (String × String) := none
  /-- Where a record's field is written by its name alone, `N { f }` for `N { f: f }`, in a
  literal or a pattern (SPEC §42): the name there is a field's and a variable's, so a renaming of
  the variable writes `f: f'` (`bcc alpha`). -/
  shorthands : List Pos := []
  /-- The frame elaboration of `let mut` (`framesEnv`), in a resolved source. -/
  frameMode : Bool := false
  /-- The frame's slots in scope (`frameMode`): each `let mut` variable is its cell. -/
  slots : List String := []
  /-- `x <- M` of a slot binds a fresh variable, stored into the slot after it (`frameMode`). -/
  slotStores : List (String × String) := []
  /-- Inside a closure, a block or a callback (`frameMode`): Core code, which sees no slot. -/
  inCode : Bool := false

abbrev P := StateT PState (Except Error)

/-- The capabilities, which are passed and handed back by name (SPEC §11). -/
def capabilityNames : List String := ["stdin", "stdout", "stderr", "clock", "args"]

/-- Record that the name written `x` at `sp` resolved to the variable `y`, the binder numbered
`b`. -/
def noteOcc (sp : Span) (x y : String) (b : Nat) : P Unit := do
  let s ← get
  if s.resolve && s.surf && sp != Span.none && !capabilityNames.contains x then
    set { s with occs := (sp.start, x, y, b) :: s.occs }

/-- A binder written `x` at `sp`, resolved to the variable `y`, in scope from here: a binder of
the source of its own (`occs`). -/
def pushBinder (x : Ident) (y : String) : P Unit := do
  let b := (← get).nextBinder
  modify fun s => { s with scope := (x.name, y, b) :: s.scope, nextBinder := b + 1 }
  noteOcc x.span x.name y b

/-- The binder an occurrence of the name `x` (written at `sp`) resolves to: the innermost in
scope, or `x` itself (a declaration, or a name the source does not bind). -/
def lookName (x : String) (sp : Span := Span.none) : P String := do
  match (← get).scope.lookup x with
  | some (y, b) => noteOcc sp x y b; pure y
  | none => pure x

/-- `x` resolved, as an `Ident`. -/
def lookIdent (x : Ident) : P Ident := return { x with name := ← lookName x.name x.span }

/-- A name for a binder that shadows `x`: `x1`, `x2`, …, the first no source name or earlier
renamed binder has; messages name it as `written`. -/
def freshVar (x : String) (written : String := x) : P String := do
  let s ← get
  let rec go : Nat → Nat → String
    | 0, k => s!"{x}{k}"
    | f + 1, k => let c := s!"{x}{k}"; if s.taken.contains c then go f (k + 1) else c
  let y := go (s.taken.length + 1) 1
  set { s with taken := y :: s.taken, renamed := (y, written) :: s.renamed }
  pure y

/-- A name the elaboration generates names with: `io_…`, `fx_…`, `hy{n}…` (Hygiene). Generated
code binds and recognises these names, so a binder of the source never has one. -/
def generatedName (x : String) : Bool :=
  x.startsWith "io_" || x.startsWith "fx_" ||
    (x.startsWith "hy" && ((x.toList.drop 2).head?.map Char.isDigit).getD false)

/-- A binder of the name `x`, in scope from here to the end of the enclosing `withScope`: its own
name, or a fresh one when a binder of `x` is already in scope, so that no binder shadows another,
or when `x` is a name the elaboration generates (`generatedName`), so that no binder is taken for
generated code's (SPEC §41, rule R1). -/
def bindName (x : Ident) : P Ident := do
  let s ← get
  -- Core text has no assignment: a binding of a name in scope is how it passes a variable on.
  if !s.resolve || !s.surf || x.name == "_" then return x
  -- A capability is a place named by the platform: a binder of its name rebinds it (SPEC §11).
  if capabilityNames.contains x.name then
    pushBinder x x.name
    return x
  let y ← if s.scope.any (·.1 == x.name) then freshVar x.name
    else if generatedName x.name then freshVar ("u" ++ x.name) x.name
    else pure x.name
  pushBinder x y
  pure { x with name := y }

/-- Run `p` with the scope as it is now restored after it: the binders `p` makes are local to it. -/
def withScope {α} (p : P α) : P α := do
  let sc := (← get).scope
  let r ← p
  modify fun s => { s with scope := sc }
  pure r

/-- The `let mut` variable a name written `x` resolves to, if it resolves to one. -/
def mutOf? (x : String) : P (Option String) := do
  let s ← get
  if !s.resolve || !s.surf then return none
  let y := ((s.scope.lookup x).map (·.1)).getD x
  pure (if s.muts.contains y then some y else none)

/-- The components of a call's argument, a right-nested tuple. -/
def argsOf : Val → List Val
  | .pair _ V W => V :: argsOf W
  | V => [V]

/-- Whether `let (x, …) = V` moves the place `x` and rebinds it (typed elaboration §5.1): `V` is
a call one of whose arguments is the variable `x` resolves to, which it is then given back
first. The variable, when it does. -/
def rebindOf? (x : Ident) (V : Val) : P (Option String) := do
  let s ← get
  if !s.resolve || !s.surf then return none
  let some (y, _) := s.scope.lookup x.name | return none
  match V with
  | .app _ _ A => pure (if (argsOf A).any (fun | .var _ z => z == y | _ => false) then some y else none)
  | _ => pure none

/-- A place `x` the construct being read rebinds (a lend, a borrow block's place): in a surface
body, a write of `x` when it is a `let mut` variable (SPEC §41, rule R2). Core text, a printed
program included, writes its joins out. -/
def notePlaceWrite (x : String) : P Unit := do
  let s ← get
  if s.resolve && s.surf && s.muts.contains x then set { s with assigned := x :: s.assigned }

/-- The binder of `x <- M`: when `x` resolves to a `let mut` variable, an assignment of it
(SPEC §41, rule R2), else a new binder. -/
def bindOrAssign (x : Ident) : P Ident := do
  match ← mutOf? x.name with
  | some y =>
    modify fun s => { s with assigned := y :: s.assigned }
    if let some (_, b) := (← get).scope.lookup x.name then noteOcc x.span x.name y b
    pure { x with name := y }
  | none => bindName x

/-- Parse a closure, block or borrow block's body: a statement `return e` in it is the core's. -/
def inClosure {α} (p : P α) : P α := do
  let l₀ := (← get).inLoop
  let c₀ := (← get).inCode
  modify fun s => { s with inLoop := false, inCode := true }
  let r ← p
  modify fun s => { s with inLoop := l₀, inCode := c₀ }
  pure r

/-- A frame of the write rule (SPEC §41, rule R2): `p` read with a write set of its own, and the
enclosing `let mut` variables it writes, in the order they were declared. What it writes, the
enclosing frame writes too. The `let mut`s it declares are its own, and so is what its last
construct leaves to be handed on (`joined`, `blockThreads`, `pendingRun`). Every construct
whose parts write reads them in a frame: a binding's head, an arm, a block, a closure, a borrow
block, `with`, `modify` and `run`. -/
def frame (p : P α) : P (α × List String) := do
  let s₀ ← get
  set { s₀ with assigned := [] }
  let M ← p
  let a := (← get).assigned
  modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned ++ a, joined := s₀.joined,
                           blockThreads := s₀.blockThreads, pendingRun := s₀.pendingRun }
  pure (M, (s₀.muts.filter a.contains).reverse)

/-- Parse a loop's body: in a function's body, a statement `return e` in it returns from the
function (`VSugar.retE`). -/
def withLoop {α} (p : P α) : P α := do
  let l₀ := (← get).inLoop
  modify fun s => { s with inLoop := s.surf }
  let r ← p
  modify fun s => { s with inLoop := l₀ }
  pure r

def fuelPerToken : Nat := 16

def peekAt (k : Nat) : P Token := do
  let s ← get
  pure (s.toks[s.pos + k]?.getD (s.toks.back?.getD default))

def peek : P Token := peekAt 0

def bump : P Token := do
  let t ← peek
  modify fun s => { s with pos := if t.tok == .eof then s.pos else s.pos + 1,
                           lastStop := t.span.stop }
  pure t

/-- The next tokens begin a `data` declaration, `data N`, which ends the declaration before it
(SPEC §42). -/
def dataStart : P Bool := do
  let t ← peek
  let t1 ← peekAt 1
  pure (t.tok == .ident "data" && (match t1.tok with | .uident _ => true | _ => false))

def startPos : P Pos := return (← peek).span.start

def spanFrom (start : Pos) : P Span := return ⟨start, (← get).lastStop⟩

def failAt {α} (sp : Span) (msg : String) : P α := throw ⟨sp, msg⟩

def expected {α} (what : String) : P α := do
  let t ← peek
  failAt t.span s!"expected {what}, found {t.tok.describe}"

def isSym (s : String) : P Bool := return (← peek).tok == .sym s
def isKw (s : String) : P Bool := return (← peek).tok == .kw s

def expectSym (s : String) : P Unit := do
  if ← isSym s then discard bump else expected s!"`{s}`"

def expectKw (s : String) : P Unit := do
  if ← isKw s then discard bump else expected s!"`{s}`"

def ident (what : String := "a name") : P Ident := do
  let t ← peek
  match t.tok with
  | .ident s => discard bump; pure ⟨s, t.span⟩
  | _ => expected what

def uident (what : String := "an upper-case name") : P Ident := do
  let t ← peek
  match t.tok with
  | .uident s => discard bump; pure ⟨s, t.span⟩
  | _ => expected what

def lifeVar : P Ident := do
  let t ← peek
  match t.tok with
  | .life s => discard bump; pure ⟨s, t.span⟩
  | _ => expected "a lifetime variable `'x`"

def outOfFuel {α} : P α := do
  let t ← peek
  failAt t.span "expression nested too deeply"

/-! ### Lifetimes (syntax-core §3) -/

mutual
/-- `'x`, `top`, `dom` or `(@)`. -/
def lifeAtom : Nat → P Life
  | 0 => outOfFuel
  | n + 1 => do
    let t ← peek
    match t.tok with
    | .life s => discard bump; pure (.var t.span s)
    | .kw "top" => discard bump; pure (.top t.span)
    | .kw "dom" => discard bump; pure (.dom t.span)
    | .sym "(" =>
      discard bump
      let l ← life n
      expectSym ")"
      pure l
    | _ => expected "a lifetime"

/-- `/\`-chains, associating to the right. -/
def lifeMeet : Nat → P Life
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let a ← lifeAtom n
    if ← isSym "/\\" then
      discard bump
      let b ← lifeMeet n
      pure (.meet (← spanFrom st) a b)
    else pure a

/-- A lifetime: `\/`-chains of `/\`-chains, both associating to the right. -/
def life : Nat → P Life
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let a ← lifeMeet n
    if ← isSym "\\/" then
      discard bump
      let b ← life n
      pure (.join (← spanFrom st) a b)
    else pure a
end

/-! ### Types and shapes (syntax-core §4, §5) -/

/-- Tokens that begin a type binder: `forall`, `all`, `mu`, `nu`. -/
def isTyBinderStart (t : Tok) : Bool :=
  t == .kw "forall" || t == .kw "all" || t == .kw "mu" || t == .kw "nu"

mutual
/-- A full type: a binder, which extends as far right as possible, or an arrow chain. -/
def rty : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .kw "forall" | .kw "all" =>
      discard bump
      let x ← lifeVar
      expectSym "<"
      let b ← life n
      expectSym "."
      let A ← rty n
      let sp ← spanFrom st
      pure (if t.tok == .kw "all" then .all sp x b A else .forall_ sp x b A)
    | .kw "mu" =>
      discard bump
      let X ← uident "a type variable"
      expectSym "."
      let A ← rty n
      pure (.mu (← spanFrom st) X A)
    | .kw "nu" =>
      discard bump
      let X ← uident "a type variable"
      expectSym "."
      let C ← rty n
      pure (.nu (← spanFrom st) X C)
    | _ => rtyArrow n

/-- `-o` and `=>`, associating to the right. -/
def rtyArrow : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let A ← rtyAmp n
    if ← isSym "-o" then
      discard bump
      let C ← rty n
      pure (.arr (← spanFrom st) A C)
    else if ← isSym "=>" then
      discard bump
      let B ← rty n
      pure (.lolli (← spanFrom st) A B)
    else pure A

/-- `&`, associating to the right. The right operand of `&`, `+` and `*` may be a binder,
    which then extends as far right as possible. -/
def rtyAmp : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let C ← rtySum n
    if ← isSym "&" then
      discard bump
      let D ← (if isTyBinderStart (← peek).tok then rty n else rtyAmp n)
      pure (.amp (← spanFrom st) C D)
    else pure C

/-- `+`, associating to the right. -/
def rtySum : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let A ← rtyTensor n
    if ← isSym "+" then
      discard bump
      let B ← (if isTyBinderStart (← peek).tok then rty n else rtySum n)
      pure (.sum (← spanFrom st) A B)
    else pure A

/-- `*`, associating to the right. -/
def rtyTensor : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let A ← rtyPrefix n
    if ← isSym "*" then
      discard bump
      let B ← (if isTyBinderStart (← peek).tok then rty n else rtyTensor n)
      pure (.tensor (← spanFrom st) A B)
    else pure A

/-- A prefix former applied to its operand, or an atom. The operand of a prefix former is
    itself a prefix former or an atom, so `!U (…)` is `!(U (…))`. -/
def rtyPrefix : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    let unary (k : Span → RTy → RTy) : P RTy := do
      discard bump
      let A ← rtyPrefix n
      pure (k (← spanFrom st) A)
    let withLife (k : Span → Life → RTy → RTy) : P RTy := do
      discard bump
      let a ← lifeAtom n
      let A ← rtyPrefix n
      pure (k (← spanFrom st) a A)
    match t.tok with
    | .kw "U" => unary .U
    | .kw "F" =>
      if (← peekAt 1).tok == .sym "[" then
        -- `F[…] A`: a row (SPEC §19); `F[] A` is `F A`.
        discard bump
        discard bump
        let r ← rowEntries n
        expectSym "]"
        let A ← rtyPrefix n
        let sp ← spanFrom st
        pure (match r with
          | .nil => .F sp A
          | r => .eff sp r A)
      else unary .F
    | .kw "ref" => unary .ref
    | .kw "array" => unary .array
    | .kw "array_imm" => withLife .arrayImm
    | .kw "array_mut" => withLife .arrayMut
    | .sym "!" => unary .bang
    | .kw "delay" => unary .delay
    | .kw "stream" | .kw "str" => unary .stream
    | .kw "loop" =>
      discard bump
      let A ← rtyPrefix n
      let B ← rtyPrefix n
      pure (.loop (← spanFrom st) A B)
    | .kw "iter" =>
      discard bump
      let A ← rtyPrefix n
      let R ← rtyPrefix n
      let R' ← rtyPrefix n
      pure (.iter (← spanFrom st) A R R')
    -- `pull A B R`, read in a type only: `pull` is not reserved.
    | .ident "pull" =>
      discard bump
      let A ← rtyPrefix n
      let B ← rtyPrefix n
      let R ← rtyPrefix n
      pure (.pull (← spanFrom st) A B R)
    | .kw "sized" =>
      discard bump
      let D ← rtyPrefix n
      let S ← rtyPrefix n
      let A ← rtyPrefix n
      pure (.sized (← spanFrom st) D S A)
    | .kw "imm" => withLife .imm
    | .kw "mut" => withLife .mut
    -- The buffer and text abbreviations (`docs/strings-slices-design.md` §2.2): `buf A` is
    -- `array A * i32`, `text 'a` is `array_imm 'a u8` and `text_mut 'a` is `array_mut 'a u8`.
    | .ident "buf" => unary fun sp A => .tensor sp (.array sp A) (.int sp .w32)
    | .ident "text" | .ident "text_mut" =>
      discard bump
      let a ← lifeAtom n
      let sp ← spanFrom st
      pure (if t.tok == .ident "text" then .arrayImm sp a (.int sp .w8) else .arrayMut sp a (.int sp .w8))
    -- `box @ A` is the lifetime box (§23); `box A`, with no lifetime, is a cell, `ref A`: a
    -- `data` field's (SPEC §42, typed elaboration §5.3).
    | .kw "box" =>
      let isLife (k : Tok) : Bool := match k with
        | .life _ | .kw "top" | .kw "dom" => true
        | _ => false
      let t1 ← peekAt 1
      let t2 ← peekAt 2
      if isLife t1.tok || (t1.tok == .sym "(" && isLife t2.tok) then withLife .box
      else unary .ref
    | .kw "view" => withLife .view
    | .kw "block" =>
      discard bump
      let σ ← shapeAtom n
      pure (.block (← spanFrom st) σ)
    | .kw "val" =>
      discard bump
      let σ ← shapeAtom n
      pure (.val (← spanFrom st) σ)
    | .kw "fam" =>
      discard bump
      let m ← if ← isKw "mut" then bump *> pure Mode.mut
        else if ← isKw "imm" then bump *> pure Mode.imm
        else expected "`mut` or `imm`"
      let a ← lifeAtom n
      let σ ← shapeAtom n
      pure (.fam (← spanFrom st) m a σ)
    | _ => rtyAtom n

/-- `1`, `0`, `unk`, `i32`, `i64`, `u8`, `input`, `output`, `top`, a name, or a parenthesized type. -/
def rtyAtom : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let t ← peek
    match t.tok with
    | .int 1 => discard bump; pure (.unit t.span)
    | .int 0 => discard bump; pure (.zero t.span)
    -- `never`, the empty type `0` (an abortive operation's answer, SPEC §19).
    | .ident "never" => discard bump; pure (.zero t.span)
    | .kw "unk" => discard bump; pure (.unk t.span)
    | .kw "i32" => discard bump; pure (.int t.span .w32)
    | .kw "i64" => discard bump; pure (.int t.span .w64)
    | .kw "u8" => discard bump; pure (.int t.span .w8)
    | .kw "f32" => discard bump; pure (.int t.span .f32)
    | .kw "f64" => discard bump; pure (.int t.span .f64)
    | .kw "input" => discard bump; pure (.handle t.span .input)
    | .kw "output" => discard bump; pure (.handle t.span .output)
    -- `clock` and `args`, the clock's and the arguments' resources (SPEC §34): names, so that
    -- `clock` and `args` are also variables'.
    | .ident "clock" => discard bump; pure (.handle t.span .clock)
    | .ident "args" => discard bump; pure (.handle t.span .args)
    | .kw "top" => discard bump; pure (.top t.span)
    -- `bool` is `1 + 1`, `inr ()` for true (the prelude, typed elaboration §5.4).
    | .ident "bool" => discard bump; pure (.sum t.span (.unit t.span) (.unit t.span))
    -- `string` is `buf u8`, and `lit`, a literal, is `i32 * !(i32 => u8)` (design §2.2, §5.7).
    | .ident "string" => discard bump
                         let sp := t.span
                         pure (.tensor sp (.array sp (.int sp .w8)) (.int sp .w32))
    | .ident "lit" => discard bump
                      let sp := t.span
                      pure (.tensor sp (.int sp .w32) (.bang sp (.lolli sp (.int sp .w32) (.int sp .w8))))
    | .uident s =>
      discard bump
      -- `N[A, …]<'a, …>`: the arguments of a parameterised `type`, curried.
      let mut F : RTy := .name t.span s
      if ← isSym "[" then
        discard bump
        repeat
          let A ← rty n
          F := .app (← spanFrom t.span.start) F A
          if ← isSym "," then discard bump else break
        expectSym "]"
      if (← isSym "<") && (← peekAt 1).tok matches .life _ then
        discard bump
        repeat
          let a ← life n
          F := .lapp (← spanFrom t.span.start) F a
          if ← isSym "," then discard bump else break
        expectSym ">"
      pure F
    | .sym "(" =>
      let st ← startPos
      discard bump
      let A ← rty n
      -- `(A => B with E₁, E₂[T, …])`: a function type with a provided row (SPEC §33).
      if ← isKw "with" then
        discard bump
        let mut es : Array (Ident × List VTy) := #[]
        repeat
          let e ← uident "an effect name"
          let mut As : Array VTy := #[]
          if ← isSym "[" then
            discard bump
            repeat
              As := As.push (← rvty n)
              if ← isSym "," then discard bump else break
            expectSym "]"
          es := es.push (e, As.toList)
          if ← isSym "," then discard bump else break
        expectSym ")"
        return .rowed (← spanFrom st) A es.toList
      expectSym ")"
      pure A
    | _ => expected "a type"

/-- A value type, sorted where it is read. -/
def rvty : Nat → P VTy
  | 0 => outOfFuel
  | n + 1 => do
    match (← rty n).toV with
    | .ok A => pure A
    | .error e => throw e

/-- `n.i` as written: the lexer reads it as a float literal's text (`Tok.flt`). -/
def nDotI? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "." with
  | [a, b] =>
    if !a.isEmpty && !b.isEmpty && a.all Char.isDigit && b.all Char.isDigit then
      some (a.toNat!, b.toNat!)
    else none
  | _ => none

/-- An operation `n.i`. -/
def opNameNI (what : String) : P (Nat × Nat) := do
  let t ← peek
  match t.tok with
  | .flt s =>
    match nDotI? s with
    | some ki => discard bump; pure ki
    | none => expected what
  | _ => expected what

/-- The entries of a row up to its `]`: `n.i q A ~> B`, separated by `,`; `q` is `lin`, `aff` or
`unr`, read as a name here and nowhere else. -/
def rowEntries : Nat → P Row
  | 0 => outOfFuel
  | n + 1 => do
    if ← isSym "]" then return .nil
    let (k, i) ← opNameNI "an operation `n.i` of a row"
    let tq ← peek
    let q ← match tq.tok with
      | .ident "lin" => discard bump; pure Qual.lin
      | .ident "aff" => discard bump; pure Qual.aff
      | .ident "unr" => discard bump; pure Qual.unr
      | _ => expected "a qualifier `lin`, `aff` or `unr`"
    let A ← rvty n
    expectSym "~>"
    let B ← rvty n
    if ← isSym "," then
      discard bump
      return .cons k i q A B (← rowEntries n)
    pure (.cons k i q A B .nil)

/-- A shape: `leaf A`, `node σ τ`, or a shape atom. -/
def shape : Nat → P Shape
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    if ← isKw "leaf" then
      discard bump
      let A ← rtyPrefix n
      match A.toV with
      | .ok A => pure (.leaf (← spanFrom st) A)
      | .error e => throw e
    else if ← isKw "node" then
      discard bump
      let σ ← shapeAtom n
      let τ ← shapeAtom n
      pure (.node (← spanFrom st) σ τ)
    else shapeAtom n

/-- A shape name or a parenthesized shape. -/
def shapeAtom : Nat → P Shape
  | 0 => outOfFuel
  | n + 1 => do
    let t ← peek
    match t.tok with
    | .uident s => discard bump; pure (.name t.span s)
    | .sym "(" =>
      discard bump
      let σ ← shape n
      expectSym ")"
      pure σ
    | _ => expected "a shape"
end

def liftSort {α} : Except Error α → P α
  | .ok a => pure a
  | .error e => throw e

/-- A value type. -/
def vty (n : Nat) : P VTy := do liftSort (← rty n).toV

/-- A computation type. -/
def cty (n : Nat) : P CTy := do liftSort (← rty n).toC

/-! ### Bracket arguments -/

def arg (n : Nat) : ArgKind → P Arg
  | .ty => .ty <$> vty n
  | .cty => .cty <$> cty n
  | .life => .life <$> life n
  | .binder => .binder <$> lifeVar
  | .shape => .shape <$> shape n
  | .row => do
    expectSym "["
    let r ← rowEntries n
    expectSym "]"
    pure (.row r)
  | .nat => do
    let t ← peek
    match t.tok with
    | .int k => discard bump; pure (.nat k)
    | _ => expected "an integer literal"
  | .op => do
    let t ← peek
    match t.tok with
    | .ident s =>
      match hostOpOfName s with
      | some o => discard bump; pure (.op o)
      | none => failAt t.span s!"unknown host operation `{s}`"
    | _ => expected "a host operation name"

/-- The arguments of the kinds listed, separated by `,`. -/
def args (n : Nat) : List ArgKind → P (List Arg)
  | [] => pure []
  | [k] => return [← arg n k]
  | k :: ks => do
    let a ← arg n k
    expectSym ","
    return a :: (← args n ks)

/-- `[A₁, …, Aₙ]` after a `def` name, at least one type. -/
def tyList (n : Nat) : Nat → P (List VTy)
  | 0 => outOfFuel
  | m + 1 => do
    let A ← vty n
    if ← isSym "," then
      discard bump
      return A :: (← tyList n m)
    else pure [A]

/-! ### Terms (syntax-core §6, and draft 0's surface, docs/surface-cbpv.md)

The core forms and the surface forms are one grammar (decision 36's successor, typed
elaboration §8, decision 4): a file may mix them. The surface forms that need no type are
desugared here into core nodes, at their own spans: `let` with patterns, `match`, a statement
`e;`, a tail expression `e`, forces `t!` and `f!(e)`, and the rebinding of a borrowed place. The
surface forms that need types (literals, operators, constants without brackets, `{ … }`, borrow
blocks) are `Val.sugar` nodes, elaborated by `Frontend/Sugar.lean`. -/

/-- A pattern of `let`, `match` and closures: a name, `_`, `()` or a pair. -/
inductive Pat where
  | var (x : Ident)
  | wild (sp : Span)
  | unit (sp : Span)
  | pair (sp : Span) (p q : Pat)
  deriving Inhabited

/-- A fresh name with the prefix `pre`, reserved for generated code. -/
def freshName (pre : String) : P String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

/-- A pattern's binders, each in scope from here (`bindName`), in order. -/
def bindPatNames : Pat → P Pat
  | .var x => return .var (← bindName x)
  | .pair sp p q => do
    let p ← bindPatNames p
    return .pair sp p (← bindPatNames q)
  | p => pure p

/-- A right-nested tuple pattern. -/
def nestPat (sp : Span) : List Pat → Pat
  | [] => .unit sp
  | [p] => p
  | p :: ps => .pair sp p (nestPat sp ps)

/-- A pattern with no constructor, literal or `box` (`Data.MPat.plain`), as `let` reads it. -/
def plainPat : Data.MPat → Pat
  | .var x => .var x
  | .wild sp => .wild sp
  | .tuple sp ps => nestPat sp (go ps)
  | p => .wild p.span
where
  go : List Data.MPat → List Pat
    | [] => []
    | p :: ps => plainPat p :: go ps

/-- The `k` components of a right-nested tuple `(V₁, (…, Vₖ))`. -/
def splitTuple : Nat → Val → List Val
  | 0, _ => []
  | 1, V => [V]
  | k + 2, .pair _ V W => V :: splitTuple (k + 1) W
  | _, V => [V]

mutual
/-- A pattern. -/
def pat : Nat → P Pat
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .ident "_" => discard bump; pure (.wild t.span)
    | .ident x => discard bump; pure (.var ⟨x, t.span⟩)
    | .sym "(" =>
      discard bump
      if ← isSym ")" then discard bump; return .unit (← spanFrom st)
      let p ← pat n
      expectSym ","
      -- `(p₁, p₂, …, pₙ)` is right-nested, as a tuple is.
      let qs ← pats n
      expectSym ")"
      let sp ← spanFrom st
      pure (.pair sp p (nestPat sp qs))
    | _ => expected "a pattern: a name, `_`, `()` or `(p, q)`"

/-- The components after the first of a tuple pattern, at least one. -/
def pats : Nat → P (List Pat)
  | 0 => outOfFuel
  | n + 1 => do
    let p ← pat n
    if ← isSym "," then discard bump; return p :: (← pats n)
    pure [p]

end

/-- `let p = V; M`, the value `V` already bound or a value without a lent capability. -/
def bindPat (sp : Span) : Nat → Pat → Val → Comp → P Comp
  | 0, _, _, M => pure M
  | _ + 1, .var x, V, M => pure (.bind sp x none (.ret sp V) M false)
  | _ + 1, .wild sp', V, M => do
    pure (.bind sp ⟨← freshName "io_d", sp'⟩ none (.ret sp V) M false)
  | _ + 1, .unit _, V, M => pure (.letUnit sp V M)
  | n + 1, .pair _ p q, V, M => do
    let x : Ident := match p with
      | .var x => x
      | _ => ⟨"", sp⟩
    let y : Ident := match q with
      | .var y => y
      | _ => ⟨"", sp⟩
    let x ← if x.name == "" then pure ⟨← freshName (if p matches .wild _ then "io_d" else "io_p"), sp⟩
      else pure x
    let y ← if y.name == "" then pure ⟨← freshName (if q matches .wild _ then "io_d" else "io_p"), sp⟩
      else pure y
    -- A name or `_` is bound by the pair itself (an unused name is dropped).
    let M ← match q with
      | .var _ | .wild _ => pure M
      | q => bindPat sp n q (.var sp y.name) M
    let M ← match p with
      | .var _ | .wild _ => pure M
      | p => bindPat sp n p (.var sp x.name) M
    pure (.letPair sp x y V M)

/-- A `&c` in a value, outside nested computations. -/
def Val.lends : Val → Bool
  | .lend .. => true
  | .pair _ V W | .app _ V W => V.lends || W.lends
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.lends
  | _ => false

mutual
/-- The places lent in a value, outside nested computations; with `vars`, the variables it names
too. -/
def Val.lentNames (vars : Bool := false) : Val → List String
  | .lend _ x _ => [x.name]
  | .var _ x => if vars then [x] else []
  -- A borrow block's body runs in place: what it lends and names is the block's.
  | .app _ (.app _ (.sugar _ (.borrow _ _)) P) (.thunkv _ (.lam _ _ _ M))
  | .app _ (.app _ (.sugar _ (.handle _ _ _ _)) P) (.thunkv _ (.lam _ _ _ M)) =>
    P.lentNames vars ++ M.lentNames vars
  | .pair _ V W | .app _ V W => V.lentNames vars ++ W.lentNames vars
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.lentNames vars
  | .run _ M => M.lentNames vars
  | _ => []

/-- The places lent in a computation, outside nested closures; with `vars`, the variables it
names too. -/
def Comp.lentNames (vars : Bool := false) : Comp → List String
  | .ret _ V | .absurd _ V => V.lentNames vars
  | .bind _ _ _ M N _ => M.lentNames vars ++ N.lentNames vars
  | .letUnit _ V M | .letPair _ _ _ V M => V.lentNames vars ++ M.lentNames vars
  | .case _ V _ M _ N | .loop _ _ _ V M N => V.lentNames vars ++ M.lentNames vars ++ N.lentNames vars
  | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M => M.lentNames vars
  | .perform _ _ _ V | .abort _ _ _ V => V.lentNames vars
  | .handle _ _ _ hr hc M => hr.lentNames vars ++ hc.lentNames vars ++ M.lentNames vars
  | .unwind _ _ _ M D N => M.lentNames vars ++ D.lentNames vars ++ N.lentNames vars
  | _ => []
end

mutual
/-- The cells lent to a `with h(&mut c)` in a value, outside nested closures, that are not bound
in `local`: an enclosing block hands them back (SPEC §18). -/
def Val.withPlaces (loc : List String) : Val → List String
  | .app _ (.app _ (.sugar _ (.handle _ _ _ _)) P) (.thunkv _ (.lam _ b _ M)) =>
    (match P with
      | .lend _ x _ => if loc.contains x.name then [] else [x.name]
      | _ => []) ++ M.withPlaces (b.name :: loc)
  | .app _ (.app _ (.sugar _ (.borrow _ _)) P) (.thunkv _ (.lam _ b _ M)) =>
    P.withPlaces loc ++ M.withPlaces (b.name :: loc)
  | .pair _ V W | .app _ V W => V.withPlaces loc ++ W.withPlaces loc
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.withPlaces loc
  | .run _ M => M.withPlaces loc
  | _ => []

/-- `Val.withPlaces` of a computation. -/
def Comp.withPlaces (loc : List String) : Comp → List String
  | .ret _ V | .absurd _ V => V.withPlaces loc
  | .bind _ x _ M N _ => M.withPlaces loc ++ N.withPlaces (x.name :: loc)
  | .letUnit _ V M => V.withPlaces loc ++ M.withPlaces loc
  | .letPair _ x y V M => V.withPlaces loc ++ M.withPlaces (x.name :: y.name :: loc)
  | .case _ V x M y N =>
    V.withPlaces loc ++ M.withPlaces (x.name :: loc) ++ N.withPlaces (y.name :: loc)
  | .loop _ _ src V M N => V.withPlaces loc ++ M.withPlaces (src.bound ++ loc) ++ N.withPlaces loc
  | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M => M.withPlaces loc
  | .perform _ _ _ V | .abort _ _ _ V => V.withPlaces loc
  | .handle _ _ _ hr hc M => hr.withPlaces loc ++ hc.withPlaces loc ++ M.withPlaces loc
  | .unwind _ x _ M D N => M.withPlaces loc ++ D.withPlaces loc ++ N.withPlaces (x.name :: loc)
  | _ => []
end

/-- The names a computation binds, outside nested closures. -/
def Comp.boundNames : Comp → List String
  | .bind _ x _ M N _ => x.name :: (M.boundNames ++ N.boundNames)
  | .letPair _ x y _ M => x.name :: y.name :: M.boundNames
  | .case _ _ x M y N => x.name :: y.name :: (M.boundNames ++ N.boundNames)
  | .loop _ _ src _ M N => src.bound ++ (M.boundNames ++ N.boundNames)
  | .lam _ x _ M => x.name :: M.boundNames
  | .letUnit _ _ M | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M =>
    M.boundNames
  | .handle _ _ _ _ _ M => M.boundNames
  | .unwind _ x _ M D N => x.name :: (M.boundNames ++ D.boundNames ++ N.boundNames)
  | _ => []

/-- A borrow block or `modify` on a place that is a name (or, for a family, a pair of names): the
names it rebinds. -/
def Val.rebinds : Val → Option Pat
  | .app _ (.app _ (.sugar _ (.borrow _ _)) P) _ => placeNames P
  -- `with h(&mut c) { … }` hands the cell `c` back; a `with` whose body hands back the
  -- variables it assigns hands back its place beside them, which is dropped. Any other `with`
  -- answers its result alone.
  | .app sp (.app _ (.sugar _ (.handle _ _ _ _)) P) (.thunkv _ (.lam _ _ _ M)) => match P with
    | .lend _ x _ => some (.var x)
    | _ => if M.boundNames.contains "io_bt" then some (.wild sp) else none
  | _ => none
where
  placeNames : Val → Option Pat
    | .var sp x => some (.var ⟨x, sp⟩)
    | .pair sp (.var s₁ x) (.var s₂ y) => some (.pair sp (.var ⟨x, s₁⟩) (.var ⟨y, s₂⟩))
    -- A literal lent by a borrow block is handed back, and dropped.
    | .sugar sp (.str _) => some (.wild sp)
    -- A load `borrow imm *g { … }` hands back nothing: its value is `((), B)`.
    | .app sp (.sugar _ .deref) _ => some (.wild sp)
    | _ => none

/-- The pattern of the variables `xs`. -/
def varPat (sp : Span) : List String → Pat
  | [] => .unit sp
  | [x] => .var ⟨x, sp⟩
  | x :: xs => .pair sp (.var ⟨x, sp⟩) (varPat sp xs)

/-- A frame that hands back what it writes beside its value, with no place to rebind: `run M`, and
`modify &mut x { … }`, whose lend rebinds `x` (SPEC §41, rule R3). -/
def Val.handsBack : Val → Bool
  | .run .. => true
  | .app _ (.app _ (.sugar _ (.borrow .modify _)) (.lend ..)) _ => true
  | _ => false

/-- A `run` that writes, read in the value `V` of a statement or binding, is `V` itself: inside an
expression what it writes could not be handed back (SPEC §41, rule R3). -/
def checkRun (V : Val) : P Unit := do
  if let some sp := (← get).pendingRun then
    unless V matches .run .. do
      failAt sp ("this `run` assigns an enclosing `let mut` variable inside an expression, where " ++
        "what it writes cannot be handed back: bind it first, `let r = run …;` (SPEC §41, rule R3)")

/-- `p = V; M` for a value `V`: a borrow block or `modify` on a place rebinds the place, which the
block hands back first; a value with a lent capability is bound first; the core forms
`let () = V` and `let (x, y) = V` are kept. -/
def letVal (sp : Span) (n : Nat) (p : Pat) (A : Option VTy) (V : Val) (M : Comp)
    (thr : List String := []) : P Comp := do
  if let some place := V.rebinds then
    let b ← freshName "io_b"
    -- The variables the block hands back beside its result are rebound too.
    let p := if thr.isEmpty then p else .pair sp p (varPat sp thr)
    return .bind sp ⟨b, sp⟩ none (.ret sp V) (← bindPat sp n (.pair sp place p) (.var sp b) M) false
  -- `run M` and `modify &mut x { … }` hand back what they write beside their value.
  if !thr.isEmpty && V.handsBack then
    let b ← freshName "io_b"
    return .bind sp ⟨b, sp⟩ none (.ret sp V) (← bindPat sp n (.pair sp p (varPat sp thr)) (.var sp b) M) false
  match p, A with
  | .var x, _ => pure (.bind sp x A (.ret sp V) M false)
  | .wild sp', _ => pure (.bind sp ⟨← freshName "io_d", sp'⟩ A (.ret sp V) M false)
  | .unit _, none => if V.lends then viaBind else bindPat sp n p V M
  | .pair _ (.var _) (.var _), none => if V.lends then viaBind else bindPat sp n p V M
  | _, _ => viaBind
where
  viaBind : P Comp := do
    let t ← freshName "io_t"
    pure (.bind sp ⟨t, sp⟩ A (.ret sp V) (← bindPat sp n p (.var sp t) M) false)

/-- The constant keyword of a token, if it is one. -/
def constKw? : Tok → Option CKw
  | .kw s => CKw.ofString? s
  | _ => none

/-- The constants that may be written without their bracket arguments, applied: `alloc(e)`. -/
def bracketless : List String := ["alloc", "free", "swap"]

/-- Tokens that begin a value atom, hence an argument of `V W`. A `{` does not: it would be read
as the block of a keyword (`case V {`, `for x in V {`). -/
def startsValAtom (t : Tok) : Bool :=
  match t with
  | .ident _ | .sym "(" | .sym "&" | .int _ | .flt _ | .str _ | .kw "clone" | .kw "box" => true
  | _ => (constKw? t).isSome

/-- Tokens that begin a computation, as against a value statement. -/
def startsComp (t : Tok) : Bool :=
  match t with
  | .kw "return" | .kw "absurd" | .kw "nu_in" | .kw "delay_in" | .kw "stream_in" | .kw "nu_out"
  | .kw "delay_out" | .kw "stream_out" | .kw "force" | .sym "<" | .kw "case" | .kw "match"
  | .kw "if" | .kw "perform" | .kw "abort" | .kw "handle_with" | .kw "withbor2r" => true
  | _ => false

/-- A binary operator: one of the surface's arithmetic and comparisons, or `&&`/`||`, which are
`case`s (they do not evaluate their right operand when the left decides). -/
inductive BinTok where
  | op (o : SurfOp)
  | and
  | or
  /-- `a |> s` (SPEC §33): `VSugar.pipe` applied to the pair. -/
  | pipe

/-- The operator of a token, with its precedence: `|>` 0, `||` 1, `&&` 2, comparisons 3, `+`/`-`
4, `*`, `/` and `%` 5. -/
def opOf (angle : Bool) : Tok → Option (BinTok × Nat)
  | .sym "|>" => some (.pipe, 0)
  | .sym "||" => some (.or, 1) | .sym "&&" => some (.and, 2)
  | .sym "==" => some (.op .eq, 3) | .sym "!=" => some (.op .ne, 3) | .sym "<" => some (.op .lt, 3)
  | .sym "<=" => some (.op .le, 3) | .sym ">=" => some (.op .ge, 3)
  | .sym ">" => if angle then none else some (.op .gt, 3)
  | .sym "+" => some (.op .add, 4) | .sym "-" => some (.op .sub, 4) | .sym "*" => some (.op .mul, 5)
  | .sym "/" => some (.op .div, 5) | .sym "%" => some (.op .rem, 5)
  | _ => none

/-- `a && b` and `a || b` as `case`s on `a`, `inr ()` being true; `b` runs only when needed. -/
def shortCircuit (sp : Span) (isAnd : Bool) (a b : Val) : Val :=
  let lit (tru : Bool) : Val :=
    .ascribe sp (if tru then .inr sp (.unit sp) else .inl sp (.unit sp))
      (.sum sp (.unit sp) (.unit sp))
  let u : Ident := ⟨"io_sc", sp⟩
  .run sp (if isAnd then .case sp a u (.ret sp (lit false)) u (.ret sp b)
    else .case sp a u (.ret sp b) u (.ret sp (lit true)))

/-- A right-nested tuple of the values (the value itself when there is one). -/
def nest (sp : Span) : List Val → Val
  | [] => .unit sp
  | [V] => V
  | V :: Vs => .pair sp V (nest sp Vs)

/-- A computation with `f` applied at each terminal reached through tail positions. -/
def wrapTerms (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (wrapTerms f N) lin
  | .letUnit sp V M => .letUnit sp V (wrapTerms f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTerms f M)
  | .case sp V x M y N => .case sp V x (wrapTerms f M) y (wrapTerms f N)
  | .loop sp ℓ src V M N => .loop sp ℓ src V M (wrapTerms f N)
  | T => f T

/-- A closure `V` that writes the enclosing `let mut` variables `xs`, marked with them (SPEC §41,
rule R3); itself when it writes none. -/
def writesOf (sp : Span) (xs : List String) (V : Val) : Val :=
  if xs.isEmpty then V else .app sp (.sugar sp (.writes xs)) V

/-- The tuple of the variables `xs`. -/
def varTuple (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (varTuple sp xs)

/-- An exit of a loop's body as the parser writes it: `break`, `break e`, `continue`, `return e`. -/
def Val.isExit : Val → Bool
  | .sugar _ .brk | .sugar _ .cont | .app _ (.sugar _ .brk) _ | .app _ (.sugar _ .retE) _ => true
  | _ => false

/-- How a frame hands on what it writes (SPEC §41, rule R3): the frame's value bound at each
terminal (`t`, typed `A`), and the value beside the variables, or the variables alone when the
value is dropped (`keep`). -/
structure HandOn where
  t : String
  A : Option VTy := none
  keep : Bool := true
  /-- A terminal that is a value hands it on as it is, with no binding: a join's. A frame whose
  later elaboration reads the binding (`io_bt`: a borrow block, `with`, `modify`, `run`) keeps it. -/
  direct : Bool := false

/-- The frame `M` handing on the `let mut` variables `xs` it writes (SPEC §41, rule R3): each
terminal reached through tail positions ends by handing them on (`HandOn`). This is the one way
a frame's writes leave it: an arm and a binding's head (the joins of typed elaboration §5.2), a
borrow block, `with`, `modify` and `run`. -/
def handOn (h : HandOn) (xs : List String) (M : Comp) : Comp :=
  let bound (T : Comp) : Comp :=
    .bind T.span ⟨h.t, T.span⟩ h.A T
      (.ret T.span (if h.keep then .pair T.span (.var T.span h.t) (varTuple T.span xs)
        else varTuple T.span xs)) false
  wrapTerms (fun T => match h.direct, h.keep, h.A, T with
    | true, true, none, .ret sp V =>
      -- An exit (`break`, `continue`, `return e` in a loop) stays a terminal of its own.
      if V.isExit then bound T else .ret sp (.pair sp V (varTuple sp xs))
    | true, false, _, .ret sp (.unit _) => .ret sp (varTuple sp xs)
    | _, _, _, T => bound T) M

/-- `M` handing on `xs`, bound before `N` (`j <- M; N`): the pattern `p` of its value, beside
the variables bound again, or the variables alone when there is no value (`p` none). -/
def joinBind (sp : Span) (n : Nat) (xs : List String) (p : Option Pat) (M : Comp) (N : Comp) :
    P Comp := do
  let j ← freshName "io_j"
  let q := match p with
    | some p => .pair sp p (varPat sp xs)
    | none => varPat sp xs
  return .bind sp ⟨j, sp⟩ none M (← bindPat sp n q (.var sp j) N) false

/-- A `match`'s or `if`'s arms handing on the variables `xs` alone (a statement's join). -/
def handArms (xs : List String) : Comp → Comp
  | .case sp V x M y N =>
    let h : HandOn := { t := "io_ju", keep := false, direct := true }
    .case sp V x (handOn h xs M) y (handOn h xs N)
  -- A compiled `match` (SPEC §42): its terminals, through the bindings of its decision tree.
  | M@(.bind ..) | M@(.letPair ..) | M@(.letUnit ..) =>
    handOn { t := "io_ju", keep := false, direct := true } xs M
  | M => M

/-- `x <- M; N`, `x : A <- M; N` or `linear x <- M; N`, with the finaliser `unwind (D)` when it has
one. A head that writes the enclosing `let mut` variables `xs` hands them on beside its value, and
`x` is bound to the value. -/
def bindForm (sp : Span) (n : Nat) (x : Ident) (A : Option VTy) (M : Comp) (D : Option Comp)
    (N : Comp) (lin : Bool) (xs : List String) : P Comp := do
  let mk (M : Comp) : Comp := match D with
    | some D => .unwind sp x A M D N
    | none => .bind sp x A M N lin
  if xs.isEmpty then return mk M
  let v ← freshName "io_jv"
  joinBind sp n xs (some (.var ⟨v, sp⟩)) (handOn { t := "io_jr", A, direct := true } xs M)
    (mk (.ret sp (.var sp v)))

/-- The loop's value, bound after it (`let r = for …`): `forRes`, applied to the thunk of the
`else` value when there is one. -/
def forResOf (sp : Span) : Option Comp → Val
  | some d => .app sp (.sugar sp .forRes) (.thunk sp d)
  | none => .sugar sp .forRes

/-- A binder type to be filled by the elaborator (a closure's, a borrow callback's). -/
def holeTy (sp : Span) : VTy := .name sp "_"

/-! ### `let mut` as a frame's slots (`frameMode`, #632)  `[spec §43]`

The frame rules of `experiments/Frames`, applied to a surface body (`Frontend.Elab.Frames`): a
`let mut` is a slot, each use of it is one lend of its cell, and a construct whose arms use slots
hands them back by the rule `case`. -/

/-- A frames builder over the parser's fresh names. -/
def runFM {α} (m : Frames.FM α) : P α := do
  let (a, n) := m.run (← get).fresh
  modify fun s => { s with fresh := n }
  pure a

/-- The slots in scope that `M` mentions, innermost first. -/
def slotsOf (M : Comp) : P (List String) := do
  pure ((← get).slots.filter (fun y => Frames.cNames y M))

/-- Whether `M` has arms through its tail positions, so that a construct after it is a join. -/
def Comp.hasArms : Comp → Bool
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N | .loop _ _ _ _ _ N => N.hasArms
  | .case .. => true
  | _ => false

/-- **The rules `case` and `bind` at a join** (`frameMode`): the arms of `M` hand back the slots
`ps` they mention, `p` binds `M`'s value (dropped when none), and `N` takes the slots apart. -/
def slotJoin (sp : Span) (n : Nat) (ps : List String) (p : Option Pat) (M N : Comp) : P Comp := do
  let j ← freshName "io_fj"
  let t ← freshName "io_ft"
  let q := Pat.pair sp (p.getD (.wild sp)) (varPat sp ps)
  return .bind sp ⟨j, sp⟩ none (Frames.handSlots t ps M) (← bindPat sp n q (.var sp j) N) false

/-- The refusal of a write of a slot inside Core code (`frameMode`): a closure, a block or a
callback that writes a slot is a frame-typed block (`callBlock`), which this prototype does not
build (D4). -/
def slotCodeWrite (sp : Span) (y : String) : P Unit := do
  if (← get).inCode then
    failAt sp (s!"frames (BCC_FRAMES=1): this closure, block or callback assigns the slot `{y}`. " ++
      "A body that writes a slot is a frame-typed block (`callBlock`, generic in its slots at " ++
      "its callee, D4), which this prototype does not build")

/-- `x <- M` of a slot (`frameMode`): `M` bound to a fresh variable, stored into the slot after
it. The binder, and the slot when it is one. -/
def slotBinder (x : Ident) : P (Ident × Option String) := do
  let s ← get
  -- A slot is in scope only under the flag: `frameMode` is read only where one is, so that the
  -- elaboration of a program without one reduces in the kernel (`Frontend/Tests.lean`).
  if !s.slots.isEmpty then
    if let some (y, b) := s.scope.lookup x.name then
      if s.slots.contains y then
        slotCodeWrite x.span y
        let t ← freshName "io_fpt"
        noteOcc x.span x.name y b
        return ({ x with name := t }, some y)
  return (← bindOrAssign x, none)

/-- **The rule `lend` at a callback** (`frameMode`): a borrow block's or a `with`'s body that uses
slots is a frame inside the lend: it hands back the slots it uses beside its result and the
variables `thr` the block hands back, and the binding takes them apart (`blockThreads`). Outside
the flag, or when the body uses no slot, the block's own hand-on of `thr`. -/
def callbackSlots (M : Comp) (thr : List String) : P (Comp × List String) := do
  if !(← get).slots.isEmpty && !(M.boundNames.contains "io_bt") then
    let ps ← slotsOf M
    unless ps.isEmpty do
      let thr := thr ++ ps
      return (Frames.handSlots "io_bt" thr M, thr)
  pure (if thr.isEmpty then M else handOn { t := "io_bt" } thr M, thr)

/-- A value that lends slots, with each lend through its slot's swap (`frameMode`,
`Frames.wrapLends`); `mk` builds the innermost value. -/
def slotLendsV (V : Val) (mk : Val → Val := id) (except : List String := []) : P Val := do
  let s ← get
  if s.slots.isEmpty then return mk V
  let ys := Frames.lentSlots (s.slots.filter (!except.contains ·)) V
  if ys.isEmpty then return mk V
  runFM (Frames.wrapLends V.span mk ys V)

/-- A tail value bound before it is returned when it lends (`frameMode`): a lend is made in the
head of a binding, and what is around the tail (a turn's state, a join's slots) pairs it. -/
def slotTail (sp : Span) (S : Comp) : P Comp := do
  if (← get).slots.isEmpty then return S
  match S with
  | .ret _ V =>
    if V.lends || (match V with | .app _ (.app _ (.sugar _ (.borrow .modify _)) _) _ => true | _ => false) then
      let t ← freshName "io_fv"
      return .bind sp ⟨t, sp⟩ none S (.ret sp (.var sp t)) false
    pure S
  | _ => pure S

/-- The store of `t` into the slot `y`, before `N` (the rule `use` with `withswap`). -/
def slotStored (sp : Span) (t : String) : Option String → Comp → P Comp
  | none, N => pure N
  | some y, N => do
    let o ← freshName "io_fo"
    let d ← freshName "io_fs"
    let sw := Frames.swapV sp y o (.ret sp (.pair sp (.var sp t) (.unit sp)))
    pure (.bind sp ⟨d, sp⟩ none (.ret sp sw) N false)

mutual
/-- A value-judged expression: a binding form (`thunk`, `thunkv`, `!thunk`, `!thunkv`), which
    extends as far right as possible, a block `{ … }` or `!{ … }`, or an operator expression. -/
def val : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .kw "thunk" => discard bump; closureOf n st .thunk
    | .kw "thunkv" => discard bump; closureOf n st .thunkv
    | .sym "!" =>
      discard bump
      if ← isKw "thunk" then discard bump; closureOf n st .bangThunk
      else if ← isKw "thunkv" then discard bump; closureOf n st .bangThunkv
      else if ← isSym "{" then brace n st true
      else expected "`thunk`, `thunkv` or `{` after `!`"
    | .sym "{" => brace n st false
    | _ => do
      let a ← valOps n 0
      -- `a..b`: a count (`VSugar.count`).
      let d₁ ← peek
      let d₂ ← peekAt 1
      if d₁.tok == .sym "." && d₂.tok == .sym "." && !d₂.spaced then
        discard bump; discard bump
        let b ← valOps n 0
        let sp ← spanFrom st
        return .app sp (.sugar d₁.span .count) (.pair sp a b)
      pure a

/-- Operators, by precedence `lvl` and above, associating to the left. -/
def valOps : Nat → Nat → P Val
  | 0, _ => outOfFuel
  | n + 1, lvl => do
    let st ← startPos
    let a ← if lvl ≥ 5 then valPrefix n else valOps n (lvl + 1)
    opsLoop n lvl st a

/-- The operators of precedence `lvl` after the operand `a`. -/
def opsLoop : Nat → Nat → Pos → Val → P Val
  | 0, _, _, _ => outOfFuel
  | m + 1, lvl, st, a => do
    let t ← peek
    match opOf (← get).angle t.tok with
    | some (o, l) =>
      if l != lvl then return a
      let osp := t.span
      discard bump
      -- A stage of `|>` is a spine.
      let b ← if lvl ≥ 5 || o matches .pipe then valPrefix m else valOps m (lvl + 1)
      let sp ← spanFrom st
      let v := match o with
        | .op o => Val.app sp (.sugar osp (.op o)) (.pair sp a b)
        | .and => shortCircuit sp true a b
        | .or => shortCircuit sp false a b
        | .pipe => Val.app sp (.sugar osp .pipe) (.pair sp a b)
      -- Comparisons do not associate.
      if lvl == 3 then return v else opsLoop m lvl st v
    | none => return a

/-- The components after the first of a tuple, at least one. -/
def rest : Nat → P (List Val)
  | 0 => outOfFuel
  | n + 1 => do
    let W ← val n
    if ← isSym "," then discard bump; return W :: (← rest n)
    pure [W]

/-- `thunk M`, `thunkv M` and their `!` forms (`k`): a closure, marked with the enclosing `let mut`
variables it writes (`writesOf`). -/
def closureOf : Nat → Pos → (Span → Comp → Val) → P Val
  | 0, _, _ => outOfFuel
  | n + 1, st, k => do
    let (M, w) ← inClosure (frame (comp n))
    let sp ← spanFrom st
    pure (writesOf sp w (k sp M))

/-- A block: `{ S }`, or a closure `{ p -> S }`; `!` before it makes it persistent. -/
def brace : Nat → Pos → Bool → P Val
  | 0, _, _ => outOfFuel
  | n + 1, st, bang => inClosure do
    expectSym "{"
    -- A closure when a pattern and `->` come first.
    let saved ← get
    let p? ← try
        let p ← pat n
        if ← isSym "->" then discard bump; pure (some p) else set saved; pure none
      catch _ => set saved; pure none
    match p? with
    | some p => withScope do
      let p ← bindPatNames p
      let (M, w) ← frame (comp n)
      expectSym "}"
      let sp ← spanFrom st
      let (x, M) ← match p with
        | .var x => pure (x, M)
        | p => do
          let x : Ident := ⟨← freshName "io_c", sp⟩
          pure (x, ← bindPat sp n p (.var sp x.name) M)
      let lam := Comp.lam sp x (holeTy sp) M
      pure (writesOf sp w (if bang then .bangThunkv sp lam else .thunkv sp lam))
    | none =>
      let (M, w) ← frame (comp n)
      expectSym "}"
      let sp ← spanFrom st
      pure (writesOf sp w (.app sp (.sugar sp .brace) (if bang then .bangThunk sp M else .thunk sp M)))

/-- A prefix keyword applied to a prefix expression, or a spine. -/
def valPrefix : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    let unary (k : Span → Val → Val) : P Val := do
      discard bump
      let V ← valPrefix n
      pure (k (← spanFrom st) V)
    match t.tok with
    | .kw "inl" => unary .inl
    | .kw "inr" => unary .inr
    | .kw "roll" => unary .roll
    | .kw "unroll" => unary .unroll
    | .kw "unbang" => unary .unbang
    | .kw "unbox" => unary .unbox
    | .kw "boxed" =>
      discard bump
      expectSym "["
      let a ← life n
      expectSym "]"
      let V ← valPrefix n
      pure (.boxed (← spanFrom st) a V)
    | .kw "run" =>
      -- `run M` hands back what `M` writes beside its value, which its binding takes apart
      -- (SPEC §41, rule R3).
      discard bump
      let (M, w) ← inClosure (do
        -- `run M` is a frame inside its binding (the rule `bind`), not Core code.
        modify fun s => { s with inCode := false }
        frame (compPrefix n))
      let sp ← spanFrom st
      if w.isEmpty && !(← get).slots.isEmpty then
        let ps ← slotsOf M
        unless ps.isEmpty do
          modify fun s => { s with blockThreads := ps, joined := [], pendingRun := some sp }
          return .run sp (Frames.handSlots "io_bt" ps M)
      if w.isEmpty then return .run sp M
      modify fun s => { s with blockThreads := w, joined := [], pendingRun := some sp }
      pure (.run sp (handOn { t := "io_bt" } w M))
    | .kw "writes" =>
      -- `writes(x, …) V`, as `bcc print` writes a closure that assigns (SPEC §41, rule R3); in a
      -- surface body the parser finds what a closure writes itself.
      discard bump
      if (← get).resolve && (← get).surf then
        failAt t.span "`writes(…)` is the printed form of a closure that assigns; in a surface body it is not written"
      expectSym "("
      let mut xs : Array String := #[]
      for _ in [0:n] do
        if ← isSym ")" then break
        xs := xs.push (← ident "a variable").name
        if ← isSym "," then discard bump
      expectSym ")"
      let V ← valPrefix n
      pure (.app (← spanFrom st) (.sugar t.span (.writes xs.toList)) V)
    | .kw "shorten_mut" | .kw "shorten_imm" =>
      discard bump
      expectSym "["
      let σ ← shape n
      expectSym ","
      let a ← life n
      expectSym "]"
      let V ← valPrefix n
      let m := if t.tok == .kw "shorten_mut" then Mode.mut else Mode.imm
      pure (.shorten (← spanFrom st) m σ a V)
    | .kw "borrow" | .kw "modify" => borrowBlock n
    | .kw "with" => withBlock n
    | .sym "*" =>
      discard bump
      let V ← valPrefix n
      let sp ← spanFrom st
      pure (.app sp (.sugar t.span .deref) V)
    -- A block after a prefix keyword (`return { … }`); as an argument it is parenthesized.
    | .sym "{" => brace n st false
    | .sym "!" =>
      if (← peekAt 1).tok == .sym "{" then do discard bump; brace n st true
      else let V ← valAtom n; valSuffixes n st V
    | _ =>
      let V ← valAtom n
      valSuffixes n st V

/-- A field's name: a name, or a word the core reserves (`val`, `free`), which is only ever a
field's there (SPEC §42). -/
def fieldName : P Ident := do
  let t ← peek
  match t.tok with
  | .ident x | .kw x => discard bump; pure ⟨x, t.span⟩
  | _ => expected "a field name"

/-- The result of an elaboration rule of `Frontend/Elab/Data.lean`. -/
def liftE {α} : Except Error α → P α
  | .ok a => pure a
  | .error e => throw e

/-- `V.f.g…`: the fields `f`, `g`, … of `V` (SPEC §42, E5), each a typed sugar node with the
declarations it may be of. In a field update's value (`updating`), `x.f` is the variable `r_f` of
the record `r` taken apart. `(r).{f = e}` is the printed form of a field update's rebuilt record
(`VSugar.update`). -/
def fieldSuffixes : Nat → Pos → Val → P Val
  | 0, _, _ => outOfFuel
  | n + 1, st, V => do
    let t ← peek
    let t1 ← peekAt 1
    unless t.tok == .sym "." && !t.spaced && !t1.spaced do return V
    if t1.tok == .sym "{" then
      discard bump; discard bump
      let x ← fieldName
      expectSym "="
      let e ← val n
      expectSym "}"
      let cands ← match Data.fieldCands (← get).data x.name with
        | .ok cs => pure cs
        | .error m => failAt x.span m
      let sp ← spanFrom st
      return ← fieldSuffixes n st (.app sp (.sugar x.span (.update x.name cands)) (.pair sp V e))
    let f ← match t1.tok with
      | .ident f | .kw f => pure f
      | _ => return V
    discard bump
    discard bump
    let cands ← match Data.fieldCands (← get).data f with
      | .ok cs => pure cs
      | .error m => failAt t1.span m
    let sp ← spanFrom st
    let V := match (← get).updating, V with
      | some (y, r), .var _ x => if x == y then .var sp s!"{r}_{f}" else .app sp (.sugar t1.span (.field f cands)) V
      | _, _ => .app sp (.sugar t1.span (.field f cands)) V
    fieldSuffixes n st V

/-- A pattern of `match` (SPEC §42): a name, `_`, `()`, `(p, …)`, `C`, `C(p, …)`, `box C(p, …)`,
`N { f: p, … }`, `N { f, … }`, an integer, byte or character literal, `true`, `false`, `inl p`,
`inr p`. -/
def mpat : Nat → P Data.MPat
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .ident "_" => discard bump; pure (.wild t.span)
    | .ident "true" => discard bump; pure (.bool t.span true)
    | .ident "false" => discard bump; pure (.bool t.span false)
    | .ident x => discard bump; pure (.var ⟨x, t.span⟩)
    | .kw "inl" | .kw "inr" =>
      discard bump
      let p ← mpat n
      pure (.inj (← spanFrom st) (t.tok == .kw "inl") p)
    | .int k => discard bump; pure (.lit t.span (.sugar t.span (.lit k)) s!"{k}")
    | .kw "i32" | .kw "i64" | .kw "u8" =>
      let V ← valAtom n
      pure (.lit (← spanFrom st) V (match V.strip with
        | .const _ (.lit c) => s!"{reprStr c}"
        | _ => s!"{reprStr V.strip}"))
    | .sym "(" =>
      discard bump
      if ← isSym ")" then discard bump; return .tuple (← spanFrom st) []
      let mut ps : Array Data.MPat := #[]
      for _ in [0:n] do
        ps := ps.push (← mpat n)
        if ← isSym "," then discard bump else break
      expectSym ")"
      match ps.toList with
      | [p] => pure p
      | qs => pure (.tuple (← spanFrom st) qs)
    | .kw "box" =>
      discard bump
      let c ← uident "a constructor (`box C(…)`)"
      conPat n st c true
    | .uident c => discard bump; conPat n st ⟨c, t.span⟩ false
    | _ => expected "a pattern: a name, `_`, `()`, `(p, …)`, a constructor, or a literal"

/-- A constructor pattern after its name: `C`, `C(p, …)`, or a record's `N { f: p, … }`, its fields
in the declaration's order and those left out `_`. -/
def conPat : Nat → Pos → Ident → Bool → P Data.MPat
  | 0, _, _, _ => outOfFuel
  | n + 1, st, c, b => do
    if ← isSym "(" then
      discard bump
      let mut ps : Array Data.MPat := #[]
      for _ in [0:n] do
        if ← isSym ")" then break
        ps := ps.push (← mpat n)
        if ← isSym "," then discard bump else break
      expectSym ")"
      return .con (← spanFrom st) c.name b ps.toList
    if ← isSym "{" then
      let some d := (← get).data.decl? c.name
        | failAt c.span s!"no `data` declaration `{c.name}`"
      let [k] := d.cons | failAt c.span s!"`{c.name}` has several constructors: match one of them"
      discard bump
      let mut fs : List (String × Data.MPat) := []
      for _ in [0:n] do
        if ← isSym "}" then break
        let x ← fieldName
        let p ← if ← isSym ":" then do discard bump; mpat n else do
          modify fun s => { s with shorthands := x.span.start :: s.shorthands }
          pure (.var x)
        unless k.fields.any (·.name.map (·.name) == some x.name) do
          failAt x.span s!"`{c.name}` has no field `{x.name}`"
        fs := fs ++ [(x.name, p)]
        if ← isSym "," then discard bump else break
      expectSym "}"
      let sp ← spanFrom st
      let ps := k.fields.map fun f => match f.name.bind (fs.lookup ·.name) with
        | some p => p
        | none => Data.MPat.wild sp
      return .con sp k.name.name b ps
    pure (.con (← spanFrom st) c.name b [])

/-- A pattern's binders, each in scope from here (`bindName`), in order. -/
def bindMPatNames : Nat → Data.MPat → P Data.MPat
  | 0, p => pure p
  | n + 1, p => match p with
    | .var x => return .var (← bindName x)
    | .tuple sp ps => return .tuple sp (← ps.mapM (bindMPatNames n))
    | .con sp c b ps => return .con sp c b (← ps.mapM (bindMPatNames n))
    | .inj sp l q => return .inj sp l (← bindMPatNames n q)
    | .free sp q => return .free sp (← bindMPatNames n q)
    | p => pure p

/-- A constructor `C`, `C(e, …)`, or a record literal `N { f: e, … }`, after its name; `boxed`
after `box` (SPEC §42, E1, E2, E4). -/
def dataValue : Nat → Pos → Ident → Bool → P Val
  | 0, _, _, _ => outOfFuel
  | n + 1, st, c, boxed => do
    let tab := (← get).data
    let t1 ← peek
    let t2 ← peekAt 1
    let t3 ← peekAt 2
    let isRec := t1.tok == .sym "{" && (tab.decl? c.name).isSome && (match t2.tok, t3.tok with
      | .ident _, .sym ":" | .ident _, .sym "," | .ident _, .sym "}" => true
      | _, _ => false)
    let angle := (← get).angle
    modify fun s => { s with angle := false }
    let V ← if isRec then do
        discard bump
        let mut fs : Array (Ident × Val) := #[]
        for _ in [0:n] do
          if ← isSym "}" then break
          let x ← fieldName
          let V ← if ← isSym ":" then do discard bump; val n
            else do
              modify fun s => { s with shorthands := x.span.start :: s.shorthands }
              pure (Val.var x.span (← lookName x.name x.span))
          fs := fs.push (x, V)
          if ← isSym "," then discard bump else break
        expectSym "}"
        let sp ← spanFrom st
        let mut vars : List (String × String) := []
        for (x, _) in fs do vars := vars ++ [(x.name, ← freshName "io_rf")]
        liftE (Data.recordVal tab sp c.name boxed fs.toList fun f => (vars.lookup f).getD f)
      else do
        let args ← if ← isSym "(" then do
            discard bump
            let mut vs : Array Val := #[]
            for _ in [0:n] do
              if ← isSym ")" then break
              vs := vs.push (← val n)
              if ← isSym "," then discard bump else break
            expectSym ")"
            pure vs.toList
          else pure []
        liftE (Data.conVal tab (← spanFrom st) c.name boxed args)
    modify fun s => { s with angle }
    pure V

/-- A borrow block: `borrow imm V { 'x, p -> S }`, `borrow mut V { … }`, `borrow mut (V, W)
{ … }` (a family), or `modify V { p -> S }`. The lifetime `'x` may be left out. -/
def borrowBlock : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    inClosure do
    -- The body is a frame inside the lend (the rule `lend`), not Core code.
    modify fun s => { s with inCode := false }
    let st ← startPos
    let t ← bump
    let k ← if t.tok == .kw "modify" then pure BorrowKind.modify else
      if ← isKw "imm" then discard bump; pure .imm
      else if ← isKw "mut" then discard bump; pure .mut
      else expected "`imm` or `mut` after `borrow`"
    let place ← valPrefix n
    -- A borrow block of a slot lends its cell (`frameMode`, the rule `use`).
    let slots₀ := (← get).slots
    let slotPlace : Option String := match Frames.mark? place with
      | some y => if slots₀.contains y && k != .modify then some y else none
      | none => none
    let place := match Frames.mark? place with
      | some y => if slots₀.contains y then
          (if k == .modify then Val.lend place.span ⟨y, place.span⟩ .mut else Val.var place.span y)
        else place
      | none => place
    -- A borrow block rebinds its place: a write of a `let mut` place (SPEC §41, rule R2).
    if let .var _ x := place then notePlaceWrite x
    let k := match k, place with
      | .mut, .pair .. => BorrowKind.famMut
      | k, _ => k
    expectSym "{"
    let x ← if (match (← peek).tok with | .life _ => true | _ => false)
      then do let x ← lifeVar; expectSym ","; pure x.name
      else if k == .modify then pure "" else freshName "io_l"
    let p ← pat n
    expectSym "->"
    let ((p, M), w) ← frame (withScope do
      let p ← bindPatNames p
      pure (p, ← comp n))
    expectSym "}"
    let sp ← spanFrom st
    -- The variables the block hands back beside its result, as a `for` hands back what its body
    -- assigns: the enclosing `let mut` variables it writes, the places it lends that it does not
    -- bind itself (a capability lent with `&mut stdout`, a buffer lent to `push`), and the
    -- standard capabilities it uses.
    let bound := M.boundNames ++ (match p with | .var b => [b.name] | _ => [])
    let caps := ["stdin", "stdout", "stderr"].filter (M.lentNames true).contains
    let thr := (w ++ (M.lentNames.filter (fun x => !bound.contains x)) ++
      M.withPlaces (match p with | .var b => [b.name] | _ => []) ++ caps).eraseDups
    -- A body already handing its variables back (a printed program read again) is kept. A
    -- `modify` hands back only the variables it writes: its body's value is the place's new
    -- content.
    let thr := if bound.contains "io_bt" then [] else if k == .modify then w else thr
    let (M, thr) ← callbackSlots M thr
    modify fun s => { s with blockThreads := thr, joined := [] }
    let (b, M) ← match p with
      | .var b => pure (b, M)
      | p => do
        let b : Ident := ⟨← freshName "io_c", sp⟩
        pure (b, ← bindPat sp n p (.var sp b.name) M)
    -- A borrow block of a slot borrows its content by the value's own rules (`frameMode`): the
    -- content swapped out of the cell, borrowed, and swapped back, `modify &mut y { v -> borrow
    -- k v { … } }` (the rule `use`); the block's value `(v, r)` is the swap's.
    if let some y := slotPlace then
      let v ← freshName "io_fbv"
      let blk : Val := .app sp (.app sp (.sugar t.span (.borrow k x)) (.var sp v))
        (.thunkv sp (.lam sp b (holeTy sp) M))
      return Frames.swapV sp y v (.ret sp blk)
    pure (.app sp (.app sp (.sugar t.span (.borrow k x)) place)
      (.thunkv sp (.lam sp b (holeTy sp) M)))

/-- `with h(e) { S }` (SPEC §18): the handler `h` installed over `S`, its state the value `e`, or
`&mut c` for a state lent from the cell `c`. It is read as a borrow block is: the enclosing
`let mut` variables the body assigns and the places it lends are handed back beside its result,
and `&mut c` rebinds `c`. The printed form names the lifetime and the capability,
`with h(e) { 'x, c -> S }`. -/
def withBlock : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    inClosure do
    -- The body is a frame inside the handler (the rules `lend` and `under`), not Core code.
    modify fun s => { s with inCode := false }
    let st ← startPos
    let t ← bump
    -- `with n = h(…) { S }`: the handler named `n` (SPEC §38).
    let nm ← if (← peekAt 1).tok == .sym "=" then do
        let n ← ident "the handler's name"
        expectSym "="
        pure (some n.name)
      else pure none
    let h ← ident "a handler name"
    -- `with h[A, …](e, …) { S }`: written type arguments, then the arguments (none: `()`).
    let As ← if ← isSym "[" then do
        discard bump
        let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
        expectSym "]"
        pure As
      else pure []
    let place ← if ← isSym "(" then do
        let psp ← startPos
        discard bump
        let mut vs : Array Val := #[]
        for _ in [0:n] do
          if ← isSym ")" then break
          vs := vs.push (← val n)
          if ← isSym "," then discard bump
        expectSym ")"
        let sp ← spanFrom psp
        pure (vs.toList.foldr (fun v acc => match acc with
          | none => some v
          | some w => some (Val.pair sp v w)) none |>.getD (Val.unit sp))
      else pure (Val.unit t.span)
    expectSym "{"
    let (x, b) ← if (match (← peek).tok with | .life _ => true | _ => false) then do
        let x ← lifeVar
        expectSym ","
        let b ← ident "the capability's name"
        expectSym "->"
        pure (x.name, b)
      else pure (← freshName "fx_l", (⟨← freshName "fx_c", t.span⟩ : Ident))
    let ((b, M), w) ← frame (withScope do
      let b ← bindName b
      pure (b, ← comp n))
    expectSym "}"
    let sp ← spanFrom st
    let bound := b.name :: M.boundNames
    let caps := ["stdin", "stdout", "stderr"].filter (M.lentNames true).contains
    let thr := (w ++ (M.lentNames.filter (fun x => !bound.contains x)) ++ M.withPlaces [b.name] ++
      caps).eraseDups
    let thr := if bound.contains "io_bt" then [] else thr
    let (M, thr) ← callbackSlots M thr
    modify fun s => { s with blockThreads := thr, joined := [] }
    pure (.app sp (.app sp (.sugar t.span (.handle h.name x As nm)) place)
      (.thunkv sp (.lam sp b (holeTy sp) M)))

/-- The suffixes of a value spine, associating to the left: argument atoms and `[@]`. -/
def valSuffixes : Nat → Pos → Val → P Val
  | 0, _, _ => outOfFuel
  | n + 1, st, V => do
    let t ← peek
    if t.tok == .sym "[" then
      discard bump
      let a ← life n
      expectSym "]"
      valSuffixes n st (.inst (← spanFrom st) V a)
    else if startsValAtom t.tok && !(← dataStart) then
      let W ← valAtom n
      valSuffixes n st (.app (← spanFrom st) V W)
    else pure V

/-- A value atom: a name, `name[A, …]`, a constant, an integer, `()`, `(V)`, `(V, W)`, `(V : A)`,
    `(V :> @)`. -/
def valAtom : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .ident s =>
      discard bump
      let nx ← peek
      -- `x.f`: a field of the variable `x` (SPEC §42); `n.op`: the operation `op` at the handler
      -- named `n` (SPEC §38), which is no variable.
      if nx.tok == .sym "." && !nx.spaced && !(← peekAt 1).spaced then
        let ps ← get
        let local_ := ps.resolve && ps.surf && (ps.scope.lookup s).isSome
        match (← peekAt 1).tok with
        | .ident _ | .kw _ | .sym "{" =>
          if local_ then
            let x ← lookName s t.span
            return ← fieldSuffixes n st (.var t.span x)
        | _ => pure ()
        if let .ident op := (← peekAt 1).tok then
          discard bump
          discard bump
          return .sugar (← spanFrom st) (.named s op)
      if nx.tok == .sym "[" && !nx.spaced then
        discard bump
        let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
        expectSym "]"
        pure (.defApp (← spanFrom st) s As)
      else
        let y ← lookName s t.span
        -- A read of a slot is a load (`frameMode`, `Frames.slotLoads`).
        if (← get).slots.contains y then return Frames.mark t.span y
        pure (.var t.span y)
    | .int k => discard bump; pure (.sugar t.span (.lit k))
    | .flt x => discard bump; let (m, e) := decOfText x; pure (.sugar t.span (.flit m e))
    | .str bs => discard bump; pure (.sugar t.span (.str bs))
    -- `box buf[A](cap)`, `box string(cap)`, `box array(n, f)`: the allocating constructors of the
    -- buffer and text libraries (`buf_new[A]`, `string_new`, `array_tab`).
    | .uident c =>
      -- A constructor or a record literal (SPEC §42).
      discard bump
      dataValue n st ⟨c, t.span⟩ false
    | .kw "box" =>
      discard bump
      let k ← peek
      if let .uident c := k.tok then
        discard bump
        return ← dataValue n st ⟨c, k.span⟩ true
      let callee : Val ← match k.tok with
        | .ident "buf" =>
          discard bump
          expectSym "["
          let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
          expectSym "]"
          pure (.defApp (← spanFrom st) "buf_new" As)
        | .ident "string" => discard bump; pure (.var (← spanFrom st) "string_new")
        | .kw "array" => discard bump; pure (.var (← spanFrom st) "array_tab")
        | _ => expected "`buf[A]`, `string` or `array` after `box`"
      let W ← valAtom n
      pure (.app (← spanFrom st) callee W)
    | .kw "break" =>
      -- `break e`: the whole expression after it is the loop's value.
      discard bump
      let nx ← peek
      let ends := match nx.tok with
        | .sym ";" | .sym "}" | .sym "|" | .sym ")" | .sym "," | .kw "else" | .eof => true
        | _ => false
      if ends then pure (.sugar t.span .brk)
      else
        let V ← val n
        pure (.app (← spanFrom st) (.sugar t.span .brk) V)
    | .kw "continue" => discard bump; pure (.sugar t.span .cont)
    | .kw "clone" => discard bump; pure (.sugar t.span (.call "clone"))
    | .sym "(" =>
      discard bump
      if ← isSym ")" then
        discard bump
        return .unit (← spanFrom st)
      -- Inside parentheses `>` is an operator again.
      let angle := (← get).angle
      modify fun s => { s with angle := false }
      let V ← val n
      let t' ← peek
      let r ← match t'.tok with
        | .sym ")" => discard bump; pure V
        | .sym "," =>
          discard bump
          -- `(V₁, V₂, …, Vₙ)` is the right-nested `(V₁, (V₂, … Vₙ))`: the argument of an n-ary
          -- call (draft 0 §2.2).
          let Ws ← rest n
          expectSym ")"
          let sp ← spanFrom st
          pure (.pair sp V (nest sp Ws))
        | .sym ":" =>
          discard bump
          let A ← vty n
          expectSym ")"
          pure (.ascribe (← spanFrom st) V A)
        | .sym ":>" =>
          discard bump
          let a ← life n
          expectSym ")"
          pure (.sub (← spanFrom st) V a)
        | _ => expected "`)`, `,`, `:` or `:>`"
      modify fun s => { s with angle }
      -- `(V).f`: a field of `V` (SPEC §42).
      fieldSuffixes n st r
    | .sym "&" =>
      discard bump
      let m ← if ← isKw "mut" then do discard bump; pure Mode.mut else pure Mode.imm
      let x ← lookIdent (← ident "the name of a place")
      -- A lend rebinds its place: a write of a `let mut` place (SPEC §41, rule R2).
      notePlaceWrite x.name
      pure (.lend (← spanFrom st) x m)
    | tok =>
      match constKw? tok with
      | some k =>
        discard bump
        if bracketless.contains k.str && (← isSym "(") then
          return .sugar t.span (.call k.str)
        let as ← if k.sig.isEmpty then pure [] else do
          expectSym "["
          let as ← args n k.sig
          expectSym "]"
          pure as
        match Const.ofArgs k as with
        | some c => pure (.const (← spanFrom st) c)
        | none => failAt (← spanFrom st) s!"malformed arguments of `{k.str}`"
      | none => expected "a value"

/-- A computation in sequence position: a binding form or a statement sequence. -/
def comp : Nat → P Comp
  | 0 => outOfFuel
  | n + 1 => compG n false

/-- A computation: a binding form (`x <- M; N`, `x : A <- M; N`, `linear x <- M; N`, `let`,
    `fun`, `Fun`, `for`), which extends as far right as possible, or a statement. In the head `M`
    of `x <- M; N` (`head`), a statement is not followed by `; N`: the `;` is the binding's. -/
def compG : Nat → Bool → P Comp
  | 0, _ => outOfFuel
  | n + 1, head => do
    let st ← startPos
    let t ← peek
    let t1 ← peekAt 1
    match t.tok, t1.tok with
    | .ident x, .sym "<-" =>
      discard bump; discard bump
      let (M, xs) ← frame (compG n true)
      -- `x <- M unwind (D); N` (SPEC §19).
      let D ← unwindOf n
      expectSym ";"
      withScope do
      let (x, sl) ← slotBinder ⟨x, t.span⟩
      let N ← comp n
      let sp ← spanFrom st
      let N ← slotStored sp x.name sl N
      let M ← match M with
        | .ret rsp V => do pure (Comp.ret rsp (← slotLendsV V))
        | M => pure M
      if M.hasArms && D.isNone && !(← get).slots.isEmpty then
        let ps ← slotsOf M
        unless ps.isEmpty do return ← slotJoin sp n ps (some (.var x)) M N
      bindForm sp n x none M D N false xs
    | .ident x, .sym ":" =>
      discard bump; discard bump
      let A ← vty n
      expectSym "<-"
      let (M, xs) ← frame (compG n true)
      let D ← unwindOf n
      expectSym ";"
      withScope do
      let (x, sl) ← slotBinder ⟨x, t.span⟩
      let N ← comp n
      let sp ← spanFrom st
      let N ← slotStored sp x.name sl N
      let M ← match M with
        | .ret rsp V => do pure (Comp.ret rsp (← slotLendsV V))
        | M => pure M
      if M.hasArms && D.isNone && !(← get).slots.isEmpty then
        let ps ← slotsOf M
        unless ps.isEmpty do
          let j ← freshName "io_fj"
          let v ← freshName "io_fv"
          let N' := Comp.bind sp x (some A) (.ret sp (.var sp v)) N false
          return ← slotJoin sp n ps (some (.var ⟨v, sp⟩)) M N'
      bindForm sp n x (some A) M D N false xs
    | .ident x₀, .sym "=" =>
      -- `x = e`: a `let mut` variable rebound (typed elaboration §5.2), the variable the name
      -- resolves to (SPEC §41, rule R2).
      discard bump; discard bump
      let x ← lookName x₀ t.span
      if (← get).slots.contains x then
        return ← slotStore n st head x t.span
      unless (← get).muts.contains x do
        failAt t.span s!"`{x₀}` is assigned, but it is not declared `let mut`"
      modify fun s => { s with assigned := x :: s.assigned, blockThreads := [], pendingRun := none }
      let V ← val n
      let thr := (← get).blockThreads
      checkRun V
      let isFrame := V.rebinds.isSome || (!thr.isEmpty && V.handsBack)
      if !head && (← isSym ";") then
        discard bump
        let N ← comp n
        let sp ← spanFrom st
        -- A frame's value is rebound as `let x = …` binds it (`letVal`).
        if isFrame then return ← letVal sp n (.var ⟨x, t.span⟩) none V N thr
        pure (.bind sp ⟨x, t.span⟩ none (.ret V.span V) N false)
      else
        let sp ← spanFrom st
        if isFrame then return ← letVal sp n (.var ⟨x, t.span⟩) none V (.ret sp (.unit sp)) thr
        pure (.bind sp ⟨x, t.span⟩ none (.ret V.span V) (.ret sp (.unit sp)) false)
    | .kw "linear", .ident x =>
      discard bump
      let xt ← bump
      let A ← if ← isSym ":" then do discard bump; pure (some (← vty n)) else pure none
      expectSym "<-"
      let (M, xs) ← frame (compG n true)
      expectSym ";"
      withScope do
      let (x, sl) ← slotBinder ⟨x, xt.span⟩
      let N ← comp n
      let N ← slotStored (← spanFrom st) x.name sl N
      if M.hasArms && !(← get).slots.isEmpty then
        let ps ← slotsOf M
        unless ps.isEmpty do
          let sp ← spanFrom st
          let v ← freshName "io_fv"
          let N' := Comp.bind sp x A (.ret sp (.var sp v)) N true
          return ← slotJoin sp n ps (some (.var ⟨v, sp⟩)) M N'
      bindForm (← spanFrom st) n x A M none N true xs
    | .kw "for", _ | .kw "while", _ | .kw "loop", .sym "{" => loopC n st none
    | .life l, .sym ":" =>
      -- `'ℓ: for …`, `'ℓ: while …`, `'ℓ: loop …`: a labelled loop.
      discard bump; discard bump
      let t₂ ← peek
      unless t₂.tok == .kw "for" || t₂.tok == .kw "while" || t₂.tok == .kw "loop" do
        failAt t.span s!"a label `'{l}:` comes before a `for`, a `while` or a `loop`"
      loopC n st (some ⟨l, t.span⟩)
    | .kw "let", _ =>
      discard bump
      -- `let C(p, …) = e; N`: a constructor pattern, a match of one arm (SPEC §42, M3).
      if (match (← peek).tok with | .uident _ | .kw "box" => true | _ => false) then
        let q ← mpat n
        expectSym "="
        let V ← val n
        expectSym ";"
        let (q, N) ← withScope do
          let q ← bindMPatNames n q
          pure (q, ← comp n)
        let (M, fresh) ← liftE (Data.matchComp (← get).data (← spanFrom st) [V] [([q], N)] (← get).fresh)
        modify fun s => { s with fresh }
        return M
      let isMut ← if ← isKw "mut" then do discard bump; pure true else pure false
      let p ← pat n
      if isMut then
        match p with
        | .var _ => pure ()
        | _ => failAt (← spanFrom st) "`let mut` binds a name"
      -- The pattern's names are in scope after the bound computation, and a `let mut`'s name is
      -- a `let mut` variable there (SPEC §41, rule R1).
      let bindP (V? : Option Val := none) : P Pat := do
        let p ← match p, V? with
          | .pair psp (.var x) q, some V => do
            match ← rebindOf? x V with
            | some y =>
              -- `let (x, q) = f(…, x, …)`: the place `x` moved and rebound (typed elaboration
              -- §5.1), so `x` is the variable it was, and an assignment when it is `let mut`
              -- (SPEC §41, rule R2).
              let b := (((← get).scope.lookup x.name).map (·.2)).getD 0
              modify fun s => { s with scope := (x.name, y, b) :: s.scope,
                                       assigned := if s.muts.contains y then y :: s.assigned
                                         else s.assigned }
              noteOcc x.span x.name y b
              pure (.pair psp (.var { x with name := y }) (← bindPatNames q))
            | none => bindPatNames p
          | p, _ => bindPatNames p
        if isMut then if let .var x := p then modify fun s => { s with muts := x.name :: s.muts }
        pure p
      withScope do
      let A ← if ← isSym ":" then do discard bump; pure (some (← vty n)) else pure none
      expectSym "="
      -- `let r = 'ℓ: for …`: the label, before the `for`.
      let ℓ ← match (← peek).tok, (← peekAt 1).tok, (← peekAt 2).tok with
        | .life l, .sym ":", .kw "for" => do
          let lt ← bump; discard bump; pure (some (⟨l, lt.span⟩ : Ident))
        | _, _, _ => pure none
      if (← peek).tok == .kw "for" then
        -- `let r = for x in V { M }; N`: the loop's value, what its iterator finishes with or
        -- what a `break e` gives, bound in what follows it.
        unless p matches .var _ do failAt (← spanFrom st) "`let … = for …` binds a name"
        discard bump
        let x ← ident
        expectKw "in"
        let V ← val n
        expectSym "{"
        let (x, M) ← withScope do
          let x ← bindName x
          pure (x, ← withLoop (comp n))
        expectSym "}"
        let els ← forElse n
        expectSym ";"
        let r ← match ← bindP with
          | .var r => pure r
          | _ => failAt (← spanFrom st) "`let … = for …` binds a name"
        let N ← comp n
        let sp ← spanFrom st
        return .loop sp ℓ (.each x) V M (.bind sp r A (.ret sp (forResOf sp els)) N false)
      if (← peek).tok == .kw "match" || (← peek).tok == .kw "if" then
        let (M, xs) ← frame (compPrefix n)
        expectSym ";"
        let p ← bindP
        let N ← comp n
        let sp ← spanFrom st
        if M.hasArms && !(← get).slots.isEmpty then
          let ps ← slotsOf M
          unless ps.isEmpty do return ← slotJoin sp n ps (some p) M N
        -- The `let mut` variables its arms assign are handed on to what follows.
        unless xs.isEmpty do
          return ← joinBind sp n xs (some p) (handOn { t := "io_jr", A, direct := true } xs M) N
        match p with
        | .var x => return .bind sp x A M N false
        | p =>
          let tv ← freshName "io_t"
          return .bind sp ⟨tv, sp⟩ A M (← bindPat sp n p (.var sp tv) N) false
      modify fun s => { s with blockThreads := [], pendingRun := none }
      let V ← val n
      -- `let y = x.f;`: the place `x` lent for the read, and rebound (SPEC §42, E5).
      let V ← match p, V with
        | .var _, .app sp (.sugar fsp (.field f cs)) (.var vsp x) => do
          let ps ← get
          if ps.resolve && ps.surf && ps.scope.any (·.2.1 == x) then
            notePlaceWrite x
            pure (Val.app sp (.sugar fsp (.field f cs)) (.lend vsp ⟨x, vsp⟩ .imm))
          else pure V
        | _, V => pure V
      let thr := (← get).blockThreads
      checkRun V
      expectSym ";"
      let V ← slotLendsV V
      -- `let mut x = V; N`: a slot (the rule `new`).
      if isMut && (← get).frameMode then
        if let .var x := p then
          if !capabilityNames.contains x.name then
            let x ← bindName x
            let sp ← spanFrom st
            let V := match A with | some A => Val.ascribe sp V A | none => V
            return ← slotScope n sp x V
      -- `let (x, q) = f(…, x, …)` of a slot: the swap `modify &mut x { o -> f(…, o, …) }`.
      if let (.pair _ (.var x) q, .app _ _ args) := (p, V) then
        if let some (y, b) := (← get).scope.lookup x.name then
          if (← get).slots.contains y && (argsOf args).any (Frames.mark? · == some y) then
            slotCodeWrite x.span y
            noteOcc x.span x.name y b
            let o ← freshName "io_fo"
            let q ← bindPatNames q
            let N ← comp n
            let sp ← spanFrom st
            return ← letVal sp n q A (Frames.swapV sp y o (.ret sp (Frames.vReads y o V))) N thr
      let p ← bindP (some V)
      let N ← comp n
      letVal (← spanFrom st) n p A V N thr
    | .kw "fun", _ =>
      discard bump
      expectSym "("
      let x ← ident
      expectSym ":"
      let A ← vty n
      expectSym ")"
      expectSym "->"
      withScope do
      let x ← bindName x
      let M ← inClosure (comp n)
      pure (.lam (← spanFrom st) x A M)
    | .kw "Fun", _ =>
      discard bump
      let x ← lifeVar
      expectSym "<"
      let b ← life n
      expectSym "."
      let M ← comp n
      pure (.lamL (← spanFrom st) x b M)
    | _, _ => statement n st head

/-- **The rule `new`** (`frameMode`): `let mut x = V; N` is the cell `alloc(V)`, the slot `x` of
`N`'s frame. `N`'s reads of `x` are loads (`Frames.slotLoads`); at `N`'s normal end the cell is
freed and its last content read where `N`'s value reads `x` (`Frames.slotEnd`). -/
def slotScope : Nat → Span → Ident → Val → P Comp
  | 0, _, _, _ => outOfFuel
  | n + 1, sp, x, V => do
    let s₀ := (← get).slots
    modify fun s => { s with slots := x.name :: s.slots }
    let N ← comp n
    modify fun s => { s with slots := s₀ }
    let d ← freshName "io_fd"
    let N ← runFM (Frames.slotLoads x.name (Frames.slotEnd x.name d N))
    pure (.bind sp x none (.ret sp (.app sp (.sugar sp (.call "alloc")) V)) N false)

/-- `x = V` of the slot `x` (`frameMode`): the store `modify &mut x { o -> (V, ()) }`, `V` reading
`x` as `o`, the old content (the rule `use` with `withswap`); then what follows. -/
def slotStore : Nat → Pos → Bool → String → Span → P Comp
  | 0, _, _, _, _ => outOfFuel
  | n + 1, st, head, x, xsp => do
    slotCodeWrite xsp x
    let V ← val n
    let o ← freshName "io_fo"
    let d ← freshName "io_fs"
    -- A value that does not read the slot is evaluated first, as Core code, and stored after:
    -- the swap's callback then does nothing but the store. One that reads it takes the old
    -- content `o` in the swap (`x = push(x, 1)` of a linear content).
    let (pre, V) ← if Frames.vNames x V then pure (none, V) else do
      let t ← freshName "io_fst"
      pure (some t, V)
    let sw ← match pre with
      | some t => pure (Frames.swapV xsp x o (.ret xsp (.pair xsp (.var xsp t) (.unit xsp))))
      | none =>
        let mk : Val → Val := fun W => Frames.swapV xsp x o (.ret xsp (.pair xsp (Frames.vReads x o W) (.unit xsp)))
        slotLendsV V (except := [x]) mk
    let wrapPre (M : Comp) : P Comp := match pre with
      | some t => do
        let V' ← slotLendsV V
        pure (.bind V.span ⟨t, V.span⟩ none (.ret V.span V') M false)
      | none => pure M
    if !head && (← isSym ";") then
      discard bump
      let N ← comp n
      let sp ← spanFrom st
      return ← wrapPre (.bind sp ⟨d, sp⟩ none (.ret sp sw) N false)
    let sp ← spanFrom st
    wrapPre (.bind sp ⟨d, sp⟩ none (.ret sp sw) (.ret sp (.var sp d)) false)

/-- `x.f = e`, a field update (SPEC §42, E6): `modify &mut x { r -> (r).{f = e} }` of a `let mut`
`x`, or `modify x { r -> … }`, whose body rebuilds the record `r` with `e` at `f` (`VSugar.update`,
a typed rule), `x.g` in `e` read as the field `g` of `r` taken apart (`r_g`). `none` when the
statement is not one. -/
def fieldUpdate : Nat → P (Option Val)
  | 0 => outOfFuel
  | n + 1 => do
    let ps ← get
    let t ← peek
    let t1 ← peekAt 1
    let t2 ← peekAt 2
    let t3 ← peekAt 3
    let .ident x₀ := t.tok | return none
    let f ← match t2.tok with
      | .ident f | .kw f => pure f
      | _ => return none
    unless t1.tok == .sym "." && !t1.spaced && !t2.spaced && t3.tok == .sym "=" do return none
    unless ps.resolve && ps.surf && (ps.scope.lookup x₀).isSome do return none
    let st ← startPos
    discard bump; discard bump; discard bump; discard bump
    let y ← lookName x₀ t.span
    let cands ← match Data.fieldCands ps.data f with
      | .ok cs => pure cs
      | .error m => failAt t2.span m
    let r ← freshName "io_fr"
    let saved := (← get).updating
    modify fun s => { s with updating := some (y, r) }
    let (e, w) ← frame (val n)
    modify fun s => { s with updating := saved }
    unless w.isEmpty do
      failAt (← spanFrom st) "the value of a field update assigns a `let mut` variable: bind it first, `let v = …;`"
    let sp ← spanFrom st
    -- When the declarations with a field `f` agree on its place, the record is taken apart here,
    -- so that the passes before the typed one see `r_g` bound; otherwise the type chooses
    -- (`VSugar.update`).
    let body := match cands with
      | cd :: rest =>
        if rest.all (fun e => e.idx == cd.idx && e.names == cd.names && e.rolls == cd.rolls) then
          let vars := cd.names.zipIdx.map fun (g, i) => if g == "" then s!"{r}__{i}" else s!"{r}_{g}"
          let comps := vars.zipIdx.map fun (x, i) => if i == cd.idx then e else Val.var sp x
          let rebuilt := Data.tupleV sp comps
          let rebuilt := if cd.rolls then
              (if cd.tps.isEmpty then Val.ascribe sp (.roll sp rebuilt) (.name sp cd.decl) else .roll sp rebuilt)
            else rebuilt
          let R : Val := if cd.rolls then .unroll sp (.var sp r) else .var sp r
          Data.letTuple sp R vars (.ret sp (.pair sp rebuilt (.unit sp))) (· ++ "r")
        else Comp.ret sp (.app sp (.sugar t2.span (.update f cands)) (.pair sp (.var sp r) e))
      | [] => Comp.ret sp (.app sp (.sugar t2.span (.update f cands)) (.pair sp (.var sp r) e))
    let place : Val := if (← get).muts.contains y then .lend t.span ⟨y, t.span⟩ .mut
      else .var t.span y
    -- The update rebinds its place: a write of a `let mut` place (SPEC §41, rule R2).
    notePlaceWrite y
    modify fun s => { s with blockThreads := [], joined := [] }
    pure (some (.app sp (.app sp (.sugar t.span (.borrow .modify "")) place)
      (.thunkv sp (.lam sp ⟨r, sp⟩ (holeTy sp) body))))

/-- A statement: a computation, a force `t!` or `f!(e)`, or an expression `e`, which is returned.
    Outside the head of a binding, `S; N` sequences it (its result is dropped), and a borrow
    block or `modify` on a place rebinds the place. -/
def statement : Nat → Pos → Bool → P Comp
  | 0, _, _ => outOfFuel
  | n + 1, st, head => do
    let t ← peek
    let t1 ← peekAt 1
    modify fun s => { s with joined := [], blockThreads := [], pendingRun := none }
    -- A statement expression, and the place it rebinds.
    let (S, rebind) ← match t.tok, t1.tok with
      | .kw "return", _ =>
        if (← get).inLoop && !head then
          -- `return e` in a loop's body: the function returns `e`.
          discard bump
          let V ← if t1.tok == .sym "}" || t1.tok == .sym ";" then pure (Val.unit t.span)
            else val n
          let sp ← spanFrom st
          pure (Comp.ret sp (.app sp (.sugar t.span .retE) V), none)
        else pure (← compPrefix n, none)
      | .ident f₀, .sym "!" =>
        discard bump; discard bump
        let f ← lookName f₀ t.span
        if ← isSym "(" then
          let V ← valAtom n
          let sp ← spanFrom st
          let a ← freshName "io_a"
          pure (Comp.bind sp ⟨a, sp⟩ none (.ret sp V) (.app sp (.force t.span ⟨f, t.span⟩) ⟨a, sp⟩)
            false, none)
        else pure (Comp.force (← spanFrom st) ⟨f, t.span⟩, none)
      | tok, _ =>
        if startsComp tok then pure (← compPrefix n, none)
        else if tok == .sym "(" then
          -- A value, or else a parenthesized computation (`(force t).1`, `(M : C)`): the value
          -- reading first, since a computation spine can also read `(f) ['x] b`.
          let saved ← get
          let V? ← try Sum.inl <$> val n catch e => set saved; pure (.inr e)
          match V? with
          | .inl V => pure (Comp.ret (← spanFrom st) V, V.rebinds)
          | .inr e₁ =>
            let M? ← try Sum.inl <$> compPrefix n catch e₂ => pure (.inr e₂)
            match M? with
            | .inl M => pure (M, none)
            -- Neither: report the attempt that got further.
            | .inr e₂ => throw (if e₂.span.start.later e₁.span.start then e₂ else e₁)
        else if let some V ← fieldUpdate n then pure (Comp.ret (← spanFrom st) V, V.rebinds)
        else do
          let V ← val n
          let W ← slotLendsV V
          pure (Comp.ret (← spanFrom st) W, if W == V then V.rebinds else none)
    let joined := (← get).joined
    let thr := (← get).blockThreads
    -- A frame's value: a borrow block or `modify` on a place, which rebinds it, or a frame that
    -- hands back what it writes beside its value.
    let frameV : Option Val := match S with
      | .ret _ V => if rebind.isSome || (!thr.isEmpty && V.handsBack) then some V else none
      | _ => none
    match S with
    | .ret _ V => checkRun V
    | _ => pure ()
    if !head && (← isSym ";") then
      discard bump
      let N ← comp n
      let sp ← spanFrom st
      -- A `match` or `if` that assigns `let mut` variables hands them on to what follows.
      if !joined.isEmpty then
        return ← joinBind sp n joined none (handArms joined S) N
      -- A construct whose arms use slots hands them back (`frameMode`, the rule `case`).
      if S.hasArms && !(← get).slots.isEmpty then
        let ps ← slotsOf S
        unless ps.isEmpty do return ← slotJoin sp n ps none S N
      match frameV with
      | some V => letVal sp n (.wild sp) none V N thr
      | none =>
        let d ← freshName "io_s"
        pure (.bind sp ⟨d, sp⟩ none S N false)
    else
      match frameV with
      | some V =>
        -- A tail frame hands back its result; the place is rebound, and dropped.
        let sp ← spanFrom st
        let v ← freshName "io_v"
        letVal sp n (.var ⟨v, sp⟩) none V (.ret sp (.var sp v)) thr
      | none => slotTail (← spanFrom st) S

/-- A prefix keyword applied to its operand, or a spine. -/
def compPrefix : Nat → P Comp
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    let unary (k : Span → Comp → Comp) : P Comp := do
      discard bump
      let M ← compPrefix n
      pure (k (← spanFrom st) M)
    match t.tok with
    | .kw "return" =>
      discard bump
      let t' ← peek
      if t'.tok == .kw "return" then
        -- A generator's early `return e`, as it is printed: `return return e`.
        discard bump
        let V ← val n
        let sp ← spanFrom st
        return .ret sp (.app sp (.sugar t'.span .retE) V)
      let V ← valPrefix n
      pure (.ret (← spanFrom st) V)
    | .kw "absurd" =>
      discard bump
      let V ← valPrefix n
      pure (.absurd (← spanFrom st) V)
    | .kw "nu_in" | .kw "delay_in" | .kw "stream_in" => unary .nuIn
    | .kw "nu_out" | .kw "delay_out" | .kw "stream_out" => unary .nuOut
    | .kw "perform" | .kw "abort" =>
      -- `perform[n.i] V`, `abort[n.i] V` (SPEC §19).
      discard bump
      expectSym "["
      let (k, i) ← opNameNI "the name `n.i` of an operation"
      expectSym "]"
      let V ← valPrefix n
      let sp ← spanFrom st
      pure (if t.tok == .kw "perform" then .perform sp k i V else .abort sp k i V)
    | .kw "handle_with" =>
      -- `handle_with[n](V, W) M` (SPEC §19): the answer clause and the clauses, values.
      discard bump
      expectSym "["
      let k ← match (← peek).tok with
        | .int k => discard bump; pure k
        | _ => expected "the name `n` of a handler"
      expectSym "]"
      expectSym "("
      let angle := (← get).angle
      modify fun s => { s with angle := false }
      let hr ← val n
      expectSym ","
      let hc ← val n
      expectSym ")"
      modify fun s => { s with angle }
      let M ← compPrefix n
      pure (.handle (← spanFrom st) k none hr hc M)
    | .kw "withbor2r" =>
      -- `withbor2r['x, @b, A, B, [ROW]](p, m) M`, the relaxed lend (SPEC §29).
      discard bump
      expectSym "["
      let as ← args n CKw.withbor2U.sig
      expectSym "]"
      let some (.withbor2U x b A B r) := Const.ofArgs .withbor2U as
        | failAt (← spanFrom st) "malformed arguments of `withbor2r`"
      expectSym "("
      let p ← lookIdent (← ident "the lent place")
      expectSym ","
      let m ← ident "the view"
      expectSym ")"
      withScope do
      let m ← bindName m
      let M ← compPrefix n
      pure (.withbor2r (← spanFrom st) x b A B r p m M)
    | _ =>
      let M ← compAtom n
      compSuffixes n st M

/-- The suffixes of a computation spine, associating to the left: variable arguments, `.1`,
    `.2` and `[@]`. -/
def compSuffixes : Nat → Pos → Comp → P Comp
  | 0, _, _ => outOfFuel
  | n + 1, st, M => do
    let t ← peek
    match t.tok with
    | .ident x =>
      if ← dataStart then return M
      discard bump
      compSuffixes n st (.app (← spanFrom st) M ⟨← lookName x t.span, t.span⟩)
    | .sym "." =>
      discard bump
      let i ← peek
      match i.tok with
      | .int 1 => discard bump; compSuffixes n st (.proj (← spanFrom st) true M)
      | .int 2 => discard bump; compSuffixes n st (.proj (← spanFrom st) false M)
      | _ => expected "`1` or `2` after `.`"
    | .sym "[" =>
      discard bump
      let a ← life n
      expectSym "]"
      compSuffixes n st (.inst (← spanFrom st) M a)
    | _ => pure M

/-- The finaliser `unwind (D)` after the head of a binding, when it has one (SPEC §19). -/
def unwindOf : Nat → P (Option Comp)
  | 0 => outOfFuel
  | n + 1 => do
    unless ← isKw "unwind" do return none
    discard bump
    expectSym "("
    let D ← comp n
    expectSym ")"
    pure (some D)

/-- A loop's `else { d }`, when it has one: the loop's value when its source ends. -/
def forElse : Nat → P (Option Comp)
  | 0 => outOfFuel
  | n + 1 => do
    unless ← isKw "else" do return none
    let st ← startPos
    discard bump
    expectSym "{"
    let (d, w) ← inClosure (frame (comp n))
    expectSym "}"
    if let x :: _ := w then
      failAt (← spanFrom st) (s!"this `else` value assigns `{x}`: a `for`'s `else` value is " ++
        "not provided with an assignment of an enclosing `let mut` (SPEC §41, rule R3)")
    pure (some d)

/-- A loop, from its keyword (`for`, `while` or `loop`), labelled `ℓ`; `st` is where it starts
(at its label when it has one). -/
def loopC : Nat → Pos → Option Ident → P Comp
  | 0, _, _ => outOfFuel
  | n + 1, st, ℓ => do
    let t ← peek
    match t.tok with
    | .kw "for" =>
      discard bump
      let x ← ident
      expectKw "in"
      let V ← val n
      expectSym "{"
      let (x, M) ← withScope do
        let x ← bindName x
        pure (x, ← withLoop (comp n))
      expectSym "}"
      -- `else { d }`: the loop's value when its source ends (`VSugar.forRes`).
      let els ← forElse n
      let sp₀ ← spanFrom st
      -- A `for` last in a body is a statement: what follows it is `()`, or, with `else`, the
      -- loop's value.
      let r ← if els.isSome then freshName "io_fr" else pure ""
      if ← isSym ";" then
        discard bump
        let N ← comp n
        let sp ← spanFrom st
        pure (.loop sp ℓ (.each x) V M (match els with
          | some d => .bind sp ⟨r, sp⟩ none (.ret sp (forResOf sp (some d))) N false
          | none => N))
      else
        pure (.loop sp₀ ℓ (.each x) V M (match els with
          | some d => .bind sp₀ ⟨r, sp₀⟩ none (.ret sp₀ (forResOf sp₀ (some d))) (.ret sp₀ (.var sp₀ r)) false
          | none => .ret sp₀ (.unit sp₀)))
    | .kw "while" =>
      -- `while c { M }; N`: the condition is tested before each turn.
      discard bump
      let c ← val n
      expectSym "{"
      let M ← withLoop (comp n)
      expectSym "}"
      -- Last in a body, what follows it is `()`.
      let N ← if ← isSym ";" then do discard bump; comp n else pure (.ret t.span (.unit t.span))
      let sp ← spanFrom st
      pure (.loop sp ℓ .while_ c M N)
    | .kw "loop" =>
      -- `loop { M }`: no source, so what follows it runs only after a `break`.
      discard bump
      expectSym "{"
      let M ← withLoop (comp n)
      expectSym "}"
      let N ← if ← isSym ";" then do discard bump; comp n else pure (.ret t.span (.unit t.span))
      let sp ← spanFrom st
      pure (.loop sp ℓ .forever (.unit t.span) M N)
    | _ => expected "`for`, `while` or `loop`"

/-- A computation atom: `force x`, `<>`, `<M, N>`, `case V { … }`, `match V { … }`, `if`,
    `(M)`, `(M : C)`. -/
def compAtom : Nat → P Comp
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .kw "force" =>
      discard bump
      let x ← lookIdent (← ident "a variable (`force` takes a variable)")
      pure (.force (← spanFrom st) x)
    | .sym "<" =>
      discard bump
      if ← isSym ">" then
        discard bump
        return .top (← spanFrom st)
      -- Inside `< M, N >`, `>` closes the pair and is not an operator.
      let angle := (← get).angle
      modify fun s => { s with angle := true }
      let M ← comp n
      expectSym ","
      let N ← comp n
      expectSym ">"
      modify fun s => { s with angle }
      pure (.with_ (← spanFrom st) M N)
    | .kw "case" =>
      discard bump
      let outer := (← get).muts
      let V ← val n
      expectSym "{"
      expectKw "inl"
      let x ← ident
      expectSym "->"
      let (x, M, a₁) ← withScope do
        let x ← bindName x
        let (M, a) ← frame (comp n)
        pure (x, M, a)
      expectSym "|"
      expectKw "inr"
      let y ← ident
      expectSym "->"
      let (y, N, a₂) ← withScope do
        let y ← bindName y
        let (N, a) ← frame (comp n)
        pure (y, N, a)
      expectSym "}"
      -- In the order the variables were declared.
      modify fun s => { s with joined := (outer.filter (a₁ ++ a₂).contains).reverse }
      pure (.case (← spanFrom st) V x M y N)
    | .kw "match" =>
      discard bump
      let outer := (← get).muts
      let V ← val n
      expectSym "{"
      if ← isSym "|" then discard bump
      let mut arms : Array (Data.MPat × Comp) := #[]
      let mut as_ : List String := []
      for _ in [0:n] do
        let p ← mpat n
        expectSym "->"
        let (p, M, a) ← withScope do
          let p ← bindMPatNames n p
          let (M, a) ← frame (comp n)
          pure (p, M, a)
        arms := arms.push (p, M)
        as_ := as_ ++ a
        if ← isSym "|" then discard bump else break
      expectSym "}"
      -- In the order the variables were declared.
      modify fun s => { s with joined := (outer.filter as_.contains).reverse }
      let sp ← spanFrom st
      -- Draft 0's form, `inl p -> M | inr q -> N` with no constructor in `p` or `q`.
      if let [(.inj _ true p, M), (.inj _ false q, N)] := arms.toList then
        if p.plain && q.plain then
          let arm (p : Data.MPat) (M : Comp) : P (Ident × Comp) := match p with
            | .var x => pure (x, M)
            | p => do
              let x : Ident := ⟨← freshName "io_m", sp⟩
              pure (x, ← bindPat sp n (plainPat p) (.var sp x.name) M)
          let (x, M) ← arm p M
          let (y, N) ← arm q N
          return .case sp V x M y N
      -- Match compilation (SPEC §42, M1, M2): the columns are a written tuple's components
      -- when every arm is a tuple of them.
      let arity := arms.toList.findSome? fun (p, _) => match p with
        | .tuple _ ps => some ps.length
        | _ => none
      let split := match V, arity with
        | .pair .., some k => k ≥ 2 && arms.all fun (p, _) => match p with
          | .tuple _ ps => ps.length == k
          | .wild _ => true
          | _ => false
        | _, _ => false
      let (cols, rows) := if split then
          let k := arity.getD 1
          (splitTuple k V, arms.toList.map fun (p, M) => match p with
            | .tuple _ ps => (ps, M)
            | p => ((List.range k).map (fun _ => Data.MPat.wild p.span), M))
        else ([V], arms.toList.map fun (p, M) => ([p], M))
      let (M, fresh) ← liftE (Data.matchComp (← get).data sp cols rows (← get).fresh)
      modify fun s => { s with fresh }
      pure M
    | .kw "if" =>
      -- `if V { S₁ } else { S₂ }`: `inr ()` is true (typed elaboration §5.4).
      discard bump
      let outer := (← get).muts
      let V ← val n
      expectSym "{"
      let (M, a₁) ← frame (comp n)
      expectSym "}"
      let (N, a₂) ← if ← isKw "else" then do
          discard bump
          if ← isKw "if" then frame (compAtom n)
          else do
            expectSym "{"
            let r ← frame (comp n)
            expectSym "}"
            pure r
        else do
          let sp ← spanFrom st
          pure (Comp.ret sp (.unit sp), [])
      let sp ← spanFrom st
      -- In the order the variables were declared.
      modify fun s => { s with joined := (outer.filter (a₁ ++ a₂).contains).reverse }
      pure (.case sp V ⟨"io_else", sp⟩ N ⟨"io_then", sp⟩ M)
    | .sym "(" =>
      discard bump
      let angle := (← get).angle
      modify fun s => { s with angle := false }
      let M ← comp n
      let r ← if ← isSym ":" then do
          discard bump
          let C ← cty n
          expectSym ")"
          pure (Comp.ascribe (← spanFrom st) M C)
        else do
          expectSym ")"
          pure M
      modify fun s => { s with angle }
      pure r
    | _ => expected "a computation"
end

/-! ### Declarations (syntax-core §10) -/

/-- The fields of a `data` constructor, `f: A` or `A`, or of a record, `f: A` (`named`): up to
the closing bracket, a trailing `,` allowed.  `[spec §42]` -/
def dataFields (n : Nat) (named : Bool) (close : String) : P (List DField) := do
  let mut fs : Array DField := #[]
  for _ in [0:n] do
    if ← isSym close then break
    let t ← peek
    let t1 ← peekAt 1
    -- A field's name may be a word the core reserves (`val`): it is only ever a field's.
    let f ← match t.tok, t1.tok with
      | .ident x, .sym ":" | .kw x, .sym ":" => do
        discard bump
        expectSym ":"
        pure (DField.mk (some ⟨x, t.span⟩) (← vty n))
      | _, _ =>
        if named then expected "a field `f: A`"
        else pure (DField.mk none (← vty n))
    fs := fs.push f
    if ← isSym "," then discard bump else break
  pure fs.toList

/-- `data N[P, …]<'l, …> = C₁ | C₂(A, …) | C₃(f: A, …) | …`, or a record
`data N[…] = { f: A, … }`, read from its `data` (SPEC §42).  `[spec §42]` -/
def dataDecl (n : Nat) : P DataDecl := do
  discard bump
  let x ← uident "the declared type's name"
  let mut tps : List Ident := []
  if ← isSym "[" then
    discard bump
    for _ in [0:n] do
      tps := tps ++ [← uident "a type parameter"]
      if ← isSym "," then discard bump else break
    expectSym "]"
  let mut lps : List Ident := []
  if ← isSym "<" then
    discard bump
    for _ in [0:n] do
      lps := lps ++ [← lifeVar]
      if ← isSym "," then discard bump else break
    expectSym ">"
  expectSym "="
  if ← isSym "{" then
    discard bump
    let fs ← dataFields n true "}"
    expectSym "}"
    return ⟨x, tps, lps, true, [⟨x, fs⟩]⟩
  if ← isSym "|" then discard bump
  let mut cons : Array DCon := #[]
  for _ in [0:n] do
    let c ← uident "a constructor"
    let fs ← if ← isSym "(" then do
        discard bump
        let fs ← dataFields n false ")"
        expectSym ")"
        pure fs
      else pure []
    cons := cons.push ⟨c, fs⟩
    if ← isSym "|" then discard bump else break
  pure ⟨x, tps, lps, false, cons.toList⟩

def decl (n : Nat) : P Decl := do
  let st ← startPos
  let t ← peek
  match t.tok with
  | .kw "type" =>
    -- `type N[T, …]<'a, …> = A` (SPEC §7): the parameters, both lists possibly absent.
    discard bump
    let x ← uident "a type name"
    let mut tps : List Ident := []
    if ← isSym "[" then
      discard bump
      repeat
        tps := tps ++ [← uident "a type parameter"]
        if ← isSym "," then discard bump else break
      expectSym "]"
    let mut lps : List Ident := []
    if ← isSym "<" then
      discard bump
      repeat
        lps := lps ++ [← lifeVar]
        if ← isSym "," then discard bump else break
      expectSym ">"
    expectSym "="
    let A ← vty n
    pure (.type (← spanFrom st) x tps lps A)
  | .kw "shape" =>
    discard bump
    let x ← uident "a shape name"
    expectSym "="
    let σ ← shape n
    pure (.shape (← spanFrom st) x σ)
  | .kw "total" | .kw "div" =>
    discard bump
    let mk := if t.tok == .kw "total" then Mark.total else .div
    if (← peek).tok == .kw "fn" then discard bump; return ← fnRest st mk
    unless (← peek).tok == .kw "def" do expected "`def` or `fn` after `total` or `div`"
    discard bump
    defRest st mk
  | .kw "fn" =>
    discard bump
    fnRest st .none
  | .kw "poly" =>
    -- `poly f[T]<'a, …>(x: A, …) -> B`, a family; `poly f[P, …]<'h, …> at H = S`, a case;
    -- `poly (+) at H = S`, a case of an operator's family; and the printed forms
    -- `poly def f[T] : A = V` and `poly def f[P, …]<'h, …> at H = V`.  `[spec §36]`
    discard bump
    let printed ← if ← isKw "def" then discard bump; pure true else pure false
    let x ← if ← isSym "(" then do
        discard bump
        let t ← bump
        let nm ← match t.tok with
          | .sym "+" => pure "op_add" | .sym "-" => pure "op_sub" | .sym "*" => pure "op_mul"
          | .sym "/" => pure "op_div" | .sym "%" => pure "op_rem" | .sym "==" => pure "op_eq"
          | .sym "!=" => pure "op_ne" | .sym "<" => pure "op_lt"
          | .sym "<=" => pure "op_le" | .sym ">" => pure "op_gt" | .sym ">=" => pure "op_ge"
          | _ => failAt t.span "an operator family is one of `(+)`, `(-)`, `(*)`, `(/)`, `(%)`, `(==)`, `(!=)`, `(<)`, `(<=)`, `(>)`, `(>=)`"
        expectSym ")"
        pure (⟨nm, t.span⟩ : Ident)
      else ident "a `poly` name"
    let tps ← typeParams
    let lives ← lifeParams
    if (← peek).tok == .ident "at" then
      discard bump
      let H ← vty n
      expectSym "="
      let V ← if printed then val n else do
        modify fun s => { s with muts := [], slots := [], assigned := [], surf := true }
        let M ← comp n
        modify fun s => { s with surf := false }
        pure (Val.thunk M.span M)
      return .poly (← spanFrom st) x tps (lives.map (·.1)) (some H) (.unit x.span) V
    if printed then
      expectSym ":"
      let A ← vty n
      expectSym "="
      let V ← val n
      return .poly (← spanFrom st) x tps [] none A V
    unless tps.length == 1 do
      failAt x.span s!"a `poly` family has one type parameter, the type its case is chosen by: `poly {x.name}[T](…) -> B`"
    expectSym "("
    let ps ← if ← isSym ")" then pure [] else params n
    expectSym ")"
    expectSym "->"
    let T ← rty n
    let sp ← spanFrom st
    let A := tupleTy sp (ps.map (·.2))
    let pn ← paramVar (ps.map (·.1))
    let body ← bindParams sp pn (ps.map (·.1)) (.force sp ⟨"io_poly_body", sp⟩)
    let lam := Comp.lam sp ⟨pn, sp⟩ A body
    let fnTy ← match T.toV with
      | .ok B => pure (VTy.lolli sp A B)
      | .error _ => do let C ← liftSort T.toC; pure (VTy.thunk sp (.arr sp A C))
    let (ty, V) := withLives sp lives fnTy lam
    pure (.poly sp x tps [] none ty V)
  | .kw "include" =>
    discard bump
    let x ← ident "the name of a library module"
    pure (.include (← spanFrom st) x)
  | .ident "data" =>
    unless (match (← peekAt 1).tok with | .uident _ => true | _ => false) do
      expected "a declaration (`type`, `shape`, `def`, `fn`, `extern`, `effect`, `handler` or `main`)"
    let d ← dataDecl n
    pure (.data (← spanFrom st) d)
  | .kw "effect" =>
    -- `effect E[T, …] { fn op(x: A, …) -> B; ctl op(…) -> B; … }` (SPEC §18, §19); `-> B` left
    -- out is `-> 1`. `ctl` is affine; `linear ctl` linear, `multi ctl` unrestricted.
    discard bump
    let x ← uident "an effect name"
    let tps ← if ← isSym "[" then do
        discard bump
        let ps ← uidents n
        expectSym "]"
        pure ps
      else pure []
    expectSym "{"
    let mut ops : Array OpDecl := #[]
    for _ in [0:n] do
      if ← isSym "}" then break
      let kind ← if ← isKw "fn" then do discard bump; pure OpKind.fn
        else do
          let q ← if ← isKw "linear" then do discard bump; pure Qual.lin
            else match (← peek).tok with
              | .ident "multi" => do discard bump; pure Qual.unr
              | _ => pure Qual.aff
          match (← peek).tok with
          | .ident "ctl" => do discard bump; pure (OpKind.ctl q)
          | _ => expected "`fn` or `ctl` (an operation)"
      let o ← ident "an operation name"
      -- `fn op<'b, …>(…)`: an answering operation's lifetime parameters (SPEC §34).
      let lps ← lifeParams
      unless lps.isEmpty || kind == OpKind.fn do
        failAt o.span s!"`{o.name}`: only an answering operation (`fn`) takes lifetime parameters"
      expectSym "("
      let ps ← if ← isSym ")" then pure [] else params n
      expectSym ")"
      let B ← if ← isSym "->" then do discard bump; vty n else pure (VTy.unit o.span)
      ops := ops.push ⟨o, ps, B, kind, lps⟩
      if ← isSym ";" then discard bump
    expectSym "}"
    pure (.effect (← spanFrom st) x tps ops.toList)
  | .kw "handler" =>
    -- A handler is a value implementing an effect (SPEC §18, §19). An answering handler,
    -- `handler h(mut s: S): E = { op(x, …) = e; … }`, has its state as a `mut` parameter, a
    -- `let mut` variable in each clause. A control handler,
    -- `handler h[T, …](p: A, …): E[A, …], A -> R with E₂[…] = { return(x) = M; op(x, …, k) = N; … }`,
    -- names the type `A` of the body it handles and its answer `R`; `k` is the continuation of
    -- a non-abortive operation; `with E₂[…]` is what its clauses perform.
    discard bump
    let h ← ident "a handler name"
    let tps ← if ← isSym "[" then do
        discard bump
        let ps ← uidents n
        expectSym "]"
        pure ps
      else pure []
    -- `<'d, …>`: a control handler's lifetime parameters (SPEC §32).
    let hlps ← lifeParams
    let mut ps : Array (Ident × VTy) := #[]
    let mut mutPs : List String := []
    let mut lent := false
    if ← isSym "(" then
      discard bump
      for _ in [0:n] do
        if ← isSym ")" then break
        -- `&mut s: S`: an answering handler whose clauses are given the state lent (SPEC §34).
        if ← isSym "&" then
          discard bump
          unless ← isKw "mut" do expected "`mut` after `&` (a handler's lent state, `&mut s: S`)"
          lent := true
        if ← isKw "mut" then
          discard bump
          let x ← ident "a parameter name"
          mutPs := mutPs ++ [x.name]
          expectSym ":"
          ps := ps.push (x, ← vty n)
        else
          let x ← ident "a parameter name"
          expectSym ":"
          ps := ps.push (x, ← vty n)
        if ← isSym "," then discard bump
      expectSym ")"
    expectSym ":"
    let e ← uident "an effect name"
    let As ← if ← isSym "[" then do
        discard bump
        let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
        expectSym "]"
        pure As
      else pure []
    let sig ← if ← isSym "," then do
        discard bump
        let A ← vty n
        expectSym "->"
        let R ← vty n
        pure (some (A, R))
      else pure none
    let row ← if ← isKw "with" then do discard bump; rowList n else pure []
    expectSym "="
    expectSym "{"
    -- The handler's parameters: one binder each, in scope in every clause.
    modify fun s => { s with surf := true, scope := [] }
    for x in ps.toList.map (·.1) do pushBinder x x.name
    let pScope := (← get).scope
    let mut cs : Array Clause := #[]
    let mut ret : Option (Ident × Comp) := none
    for _ in [0:n] do
      if ← isSym "}" then break
      let isRet ← isKw "return"
      let o ← if isRet then do let t ← bump; pure (⟨"return", t.span⟩ : Ident)
        else ident "an operation name"
      expectSym "("
      let mut xs : Array Ident := #[]
      for _ in [0:n] do
        if ← isSym ")" then break
        xs := xs.push (← ident "a parameter name")
        if ← isSym "," then discard bump
      expectSym ")"
      expectSym "="
      modify fun s => { s with muts := mutPs, slots := [], assigned := [], surf := true, scope := pScope }
      for x in xs.toList do pushBinder x x.name
      let M ← if ← isSym "{" then do
          discard bump
          let M ← comp n
          expectSym "}"
          pure M
        else compG n true
      modify fun s => { s with muts := [], slots := [], assigned := [], surf := false, scope := [] }
      if isRet then
        let some x := xs[0]? | failAt o.span "`return(x) = M`: the return clause binds the body's value"
        ret := some (x, M)
      else cs := cs.push ⟨o, xs.toList, M⟩
      if ← isSym ";" then discard bump
    expectSym "}"
    modify fun s => { s with surf := false, scope := [] }
    let sp ← spanFrom st
    match sig with
    | some (A, R) =>
      if lent then failAt h.span s!"`{h.name}`: only an answering handler's state is lent (`&mut s: S`)"
      let some (x, M) := ret | failAt h.span s!"the control handler `{h.name}` has no return clause, `return(x) = M`"
      pure (.chandler sp ⟨h, tps, ps.toList, e, As, row, R, (x, A, M), cs.toList, hlps, mutPs⟩)
    | none =>
      match ps.toList, mutPs, tps, As, row, ret with
      | [(sv, S)], [_], [], [], [], none =>
        unless hlps.isEmpty do failAt h.span s!"`{h.name}`: an answering handler has no lifetime parameters"
        pure (.handler sp h sv S e cs.toList lent)
      | _, _, _, _, _, _ => failAt h.span (s!"`{h.name}`: an answering handler is `handler h(mut s: S): E = " ++
          "{ op(x) = e; … }` (or `handler h(&mut s: S): E = …`, its state lent to each clause), " ++
          "and a control handler names its body's type and its answer, " ++
          "`handler h[…](…): E[…], A -> R = { return(x) = M; op(x, k) = N; … }`")
  | .kw "def" =>
    discard bump
    defRest st .none
  | .kw "extern" =>
    discard bump
    let x ← ident "an `extern` name"
    expectSym ":"
    let A ← vty n
    pure (.extern (← spanFrom st) x A)
  | .kw "main" =>
    discard bump
    -- `main -> T = S` (draft 0): the result is `F T` when `T` is a value type.
    if ← isSym "->" then
      discard bump
      let T ← rty n
      let C ← match T.toV with
        | .ok A => pure (CTy.ret A.span A)
        | .error _ => liftSort T.toC
      expectSym "="
      -- Each declaration's `let mut` variables are its own.
      modify fun s => { s with surf := true, muts := [], slots := [], assigned := [], scope := [] }
      let M ← comp n
      modify fun s => { s with surf := false }
      return .main (← spanFrom st) C M
    expectSym ":"
    let C ← cty n
    expectSym "="
    modify fun s => { s with muts := [], slots := [], assigned := [], scope := [] }
    let M ← comp n
    pure (.main (← spanFrom st) C M)
  | _ => expected "a declaration (`type`, `shape`, `def`, `fn`, `extern`, `effect`, `handler` or `main`)"
where
  /-- A `def` after its keyword: `name[P₁, …] : A = V`. -/
  defRest (st : Pos) (mk : Mark) : P Decl := do
    let x ← ident "a `def` name"
    let ps ← if ← isSym "[" then do
        discard bump
        let ps ← uidents n
        expectSym "]"
        pure ps
      else pure []
    -- `fn def f[S, …] where S: 'c : A = V`: a template's printed bounds.
    let bs ← whereBounds ps []
    let mk := match mk with
      | .template m _ => .template m bs
      | mk => mk
    expectSym ":"
    let A ← vty n
    expectSym "="
    modify fun s => { s with muts := [], slots := [], assigned := [], scope := [] }
    let V ← val n
    pure (.def_ (← spanFrom st) x ps A V mk)
  /-- A `fn` after its keyword (draft 0 §2.5): `name[P₁, …]<'a, …>(x₁: A₁, …, xₙ: Aₙ) -> T = S`,
  the type parameters and the lifetime parameters each optional. It is the persistent
  `def name : !(A₁ * … * Aₙ => T) = !thunkv fun (p : A₁ * … * Aₙ) -> …`, the parameters bound
  from `p` and the body `S` a statement sequence; with no parameter, `p : 1`. When `T` is a
  computation type `C`, the result is `C` itself: `!U (A -o C)`. Each lifetime parameter `'a`
  (bounded by `top`, or by `@` when written `'a < @`) is an `all 'a < @.` around the function,
  outermost first, and a `Fun 'a < @.` around its body. With type parameters, the `fn` is a
  template, instantiated at each use (`Mark.template`), printed `fn def name[P₁, …] : A = V`. -/
  fnRest (st : Pos) (mk : Mark) : P Decl := do
    -- `fn def f[A, …] : T = V`: a template's printed form (`Decl.pp`).
    if ← isKw "def" then
      discard bump
      return ← defRest st (.template mk)
    let x ← ident "a `fn` name"
    let tps ← typeParams
    let lives ← lifeParams
    expectSym "("
    let ps ← if ← isSym ")" then pure [] else params n
    expectSym ")"
    expectSym "->"
    let T ← rty n
    -- `with E₁, E₂[A]`: a written row (SPEC §18).
    let nes ← if ← isKw "with" then do discard bump; namedRowList n else pure []
    let es := nes.map (·.2)
    let ns := if nes.all (·.1.isNone) then [] else nes.map (·.1)
    let bs ← whereBounds tps (lives.map (·.1.name))
    expectSym "="
    modify fun s => { s with muts := [], slots := [], assigned := [], surf := true, scope := [] }
    for x in ps.map (·.1) do pushBinder x x.name
    let M ← comp n
    modify fun s => { s with surf := false, scope := [] }
    let sp ← spanFrom st
    let A := tupleTy sp (ps.map (·.2))
    let pn ← paramVar (ps.map (·.1))
    let body ← bindParams sp pn (ps.map (·.1)) M
    let lam := Comp.lam sp ⟨pn, sp⟩ A body
    let fnTy ← match T.toV with
      | .ok B => pure (VTy.lolli sp A B)
      | .error _ => do let C ← liftSort T.toC; pure (VTy.thunk sp (.arr sp A C))
    let (ty, V) := withLives sp lives fnTy lam
    let mk := if tps.isEmpty then mk else .template mk bs
    pure (.def_ sp x tps ty V (if es.isEmpty then mk else .row es mk ns))
  /-- `E₁, E₂[A, …], …`: the effects of a written row, at least one; `src: E` names an entry
  (SPEC §38). -/
  rowList : Nat → P (List (Ident × List VTy))
    | n' => do pure ((← namedRowList n').map (·.2))
  namedRowList : Nat → P (List (Option Ident × Ident × List VTy))
    | 0 => outOfFuel
    | m + 1 => do
      let x ← if (match (← peek).tok with | .ident _ => true | _ => false) &&
          (← peekAt 1).tok == .sym ":" then do
          let x ← ident "the entry's name"
          expectSym ":"
          pure (some x)
        else pure none
      let e ← uident "an effect name"
      let As ← if ← isSym "[" then do
          discard bump
          let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
          expectSym "]"
          pure As
        else pure []
      if ← isSym "," then
        discard bump
        return (x, e, As) :: (← namedRowList m)
      else pure [(x, e, As)]
  /-- `where S: 'c, …`: lifetime bounds on the type parameters `tps`, each by a lifetime
  parameter (one of `lives`, when they are given), or none. `where` is a word here, not a
  keyword.  `[spec §23]` -/
  whereBounds (tps : List Ident) (lives : List String) : P (List (Ident × Ident)) := do
    if (← peek).tok != .ident "where" then return []
    let w ← bump
    if tps.isEmpty then failAt w.span "a lifetime bound `where S: 'c` is on a type parameter"
    let mut acc : Array (Ident × Ident) := #[]
    for _ in [0:n] do
      let S ← uident "a type parameter"
      unless tps.any (·.name == S.name) do
        failAt S.span s!"`{S.name}` is not a type parameter of this function"
      expectSym ":"
      let c ← lifeVar
      unless lives.isEmpty || lives.contains c.name do
        failAt c.span s!"`'{c.name}` is not a lifetime parameter of this function"
      acc := acc.push (S, c)
      if ← isSym "," then discard bump else break
    pure acc.toList
  /-- `[P₁, …]` after a name: type parameters, or none. -/
  typeParams : P (List Ident) := do
    if ← isSym "[" then
      discard bump
      let ps ← uidents n
      expectSym "]"
      pure ps
    else pure []
  /-- `<'a, 'b < @, …>` after a name: lifetime parameters with their bounds (`top` when not
  written), or none. -/
  lifeParams : P (List (Ident × Life)) := do
    if !(← isSym "<") then return []
    discard bump
    let mut acc : Array (Ident × Life) := #[]
    for _ in [0:n] do
      let a ← lifeVar
      let b ← if ← isSym "<" then do discard bump; life n else pure (.top a.span)
      acc := acc.push (a, b)
      if ← isSym "," then discard bump else break
    expectSym ">"
    pure acc.toList
  /-- The persistent function of type `F` (`A => T` or `U (A -o C)`) whose code is `lam`, generic
  in the lifetimes `lives`: `!(all 'a < @. … F)` and `!thunkv Fun 'a < @. return (thunkv …)`. -/
  withLives (sp : Span) (lives : List (Ident × Life)) (F : VTy) (lam : Comp) : VTy × Val :=
    match lives with
    | [] => (.bang sp F, .bangThunkv sp lam)
    | (a, b) :: ls =>
      let rec inner : List (Ident × Life) → VTy × Comp
        | [] => (F, lam)
        | (a, b) :: ls =>
          let (T, M) := inner ls
          (.all sp a b T, .lamL sp a b (.ret sp (.thunkv sp M)))
      let (T, M) := inner ls
      (.bang sp (.all sp a b T), .bangThunkv sp (.lamL sp a b (.ret sp (.thunkv sp M))))
  /-- `x₁: A₁, …, xₙ: Aₙ`, at least one. -/
  params : Nat → P (List (Ident × VTy))
    | 0 => outOfFuel
    | m + 1 => do
      let x ← ident "a parameter name"
      expectSym ":"
      let A ← vty n
      if ← isSym "," then
        discard bump
        return (x, A) :: (← params m)
      else pure [(x, A)]
  /-- The parameter tuple's type (`1` with no parameters). -/
  tupleTy (sp : Span) : List VTy → VTy
    | [] => .unit sp
    | [A] => A
    | A :: As => .tensor sp A (tupleTy sp As)
  /-- The variable a function's parameters arrive in: the one parameter itself, or a tuple
  `io_pN` of none or several. -/
  paramVar : List Ident → P String
    | [x] => pure x.name
    | _ => freshName "io_p"
  /-- Bind the parameters from the tuple `p`: a parameter that is `p` itself is not bound
  again. -/
  bindParams (sp : Span) (p : String) : List Ident → Comp → P Comp
    | [], M => pure (.letUnit sp (.var sp p) M)
    | [x], M => pure (if x.name == p then M else .bind sp x none (.ret sp (.var sp p)) M false)
    | [x, y], M => pure (.letPair sp x y (.var sp p) M)
    | x :: xs, M => do
      let r ← freshName "io_p"
      pure (.letPair sp x ⟨r, sp⟩ (.var sp p) (← bindParams sp r xs M))
  /-- `P₁, …, Pₙ`: a `def`'s type parameters, at least one. -/
  uidents : Nat → P (List Ident)
    | 0 => outOfFuel
    | m + 1 => do
      let p ← uident "a type parameter"
      if ← isSym "," then
        discard bump
        return p :: (← uidents m)
      else pure [p]

/-- `with[E₁, E₂[A]] def …`: a definition with a written row, as it is printed (SPEC §18). -/
def rowDecl (n : Nat) : P Decl := do
  let t ← bump
  expectSym "["
  let nes ← decl.namedRowList n n
  expectSym "]"
  let ns := if nes.all (·.1.isNone) then [] else nes.map (·.1)
  match ← decl n with
  | .def_ sp x ps A V mk => pure (.def_ sp x ps A V (.row (nes.map (·.2)) mk ns))
  | _ => failAt t.span "a written row is on a function"

/-- Declarations until the end of input. -/
def decls (n : Nat) : Nat → List Decl → P (List Decl)
  | 0, _ => outOfFuel
  | m + 1, acc => do
    if (← peek).tok == .eof then pure acc.reverse
    else
      let d ← if (← peek).tok == .kw "with" then rowDecl n else decl n
      decls n m (d :: acc)

/-! ### Entry points -/

/-- Run a parser over the tokens of `src`, requiring it to consume all of them. With `resolve`,
each name is resolved to its binder (SPEC §41, rule R1), and no fresh binder is named as a name
of the source. -/
def runPS {α} (p : Nat → P α) (src : String) (resolve : Bool := false) (data : Data.Table := [])
    (isLib : Bool := false) : Except Error (α × PState) := do
  let toks ← lex src
  let fuel := fuelPerToken * (toks.size + 1)
  let go : P α := do
    let a ← p fuel
    if (← peek).tok != .eof then expected "end of input"
    pure a
  let taken := if resolve then toks.toList.filterMap (fun t => match t.tok with
    | .ident s => some s
    | _ => none) |>.eraseDups else []
  go.run { toks, pos := 0, lastStop := ⟨1, 1⟩, resolve, taken, data,
           frameMode := resolve && framesEnv && (!isLib || framesLibEnv) }

/-- The `data` declarations written in the tokens `toks`, each read where it is (SPEC §42): a
declaration is in scope in its whole module. A declaration that does not read is left to the
parse proper, which reports it. -/
def dataIn (toks : Array Token) : List DataDecl := Id.run do
  let fuel := fuelPerToken * (toks.size + 1)
  let mut out : List DataDecl := []
  for i in [0:toks.size] do
    let isData := toks[i]!.tok == .ident "data" &&
      (match toks[i + 1]?.map Token.tok with | some (Tok.uident _) => true | _ => false)
    if isData then
      match (dataDecl fuel).run { toks, pos := i, lastStop := ⟨1, 1⟩ } with
      | .ok (d, _) => out := out ++ [d]
      | .error _ => pure ()
  out

/-- The modules the tokens `toks` include. -/
def includesIn (toks : Array Token) : List String := Id.run do
  let mut out : List String := []
  for i in [0:toks.size] do
    if toks[i]!.tok == .kw "include" then
      if let some (Tok.ident m) := toks[i + 1]?.map Token.tok then out := out ++ [m]
  out

/-- The `data` declarations of the modules `ms` and of the modules they include, each once,
`lib` giving a module's source: what has been read, and the modules read. -/
def dataOfModules (lib : String → Option String) : Nat → List String → List String →
    Data.Table × List String
  | 0, _, seen => ([], seen)
  | _ + 1, [], seen => ([], seen)
  | k + 1, m :: ms, seen =>
    if seen.contains m then dataOfModules lib k ms seen else
    match (lib m).map lex with
    | some (.ok toks) =>
      let (inner, seen) := dataOfModules lib k (includesIn toks) (m :: seen)
      let (rest, seen) := dataOfModules lib k ms seen
      (inner ++ dataIn toks ++ rest, seen)
    | _ => dataOfModules lib k ms (m :: seen)

def runP {α} (p : Nat → P α) (src : String) (resolve : Bool := false) : Except Error α :=
  (·.1) <$> runPS p src resolve

/-- The `data` declarations in scope in the source `src` (SPEC §42): the prelude's, the included
modules', and its own, `lib` giving a module's source. -/
def dataOf (lib : String → Option String) (src : String) : Data.Table :=
  match lex src with
  | .ok toks => (dataOfModules lib 64 ("prelude" :: includesIn toks) []).1 ++ dataIn toks
  | .error _ => []

/-- The declarations of a source file. At most one `main` is accepted. Its names are resolved
(`resolve`) unless it is code the elaborator generated. -/
def parseProgram (src : String) (resolve : Bool := true)
    (lib : String → Option String := fun _ => none) (isLib : Bool := false) :
    Except Error Program := do
  -- The `data` declarations in scope (SPEC §42): the prelude's, the included modules', the
  -- program's own.
  let ds ← (·.1) <$> runPS (fun n => decls n n []) src resolve (dataOf lib src) isLib
  let mains := ds.filter fun | .main .. => true | _ => false
  match mains with
  | _ :: .main sp _ _ :: _ => .error ⟨sp, "a program has at most one `main`"⟩
  | _ => pure ⟨ds⟩

def parseVal (src : String) : Except Error Val := runP val src
def parseComp (src : String) : Except Error Comp := runP comp src
def parseVTy (src : String) : Except Error VTy := runP vty src
def parseCTy (src : String) : Except Error CTy := runP cty src

/-- The binders resolution renamed in `src` (SPEC §41, rule R1), each with the name the source
writes it with. -/
def renamesOf (src : String) (lib : String → Option String := fun _ => none) :
    List (String × String) :=
  match runPS (fun n => decls n n []) src true (dataOf lib src) with
  | .ok (_, s) => s.renamed
  | .error _ => []

/-- Each name of `src` that resolution resolved to a variable (SPEC §41, rule R1): where it is
written, as written, the variable, and the number of its binder, in the order of the source. -/
def resolutionOf (src : String) (lib : String → Option String := fun _ => none) :
    Except Error (List (Pos × String × String × Nat)) := do
  let (_, s) ← runPS (fun n => decls n n []) src true (dataOf lib src)
  pure s.occs.reverse

/-- Where the source `src` writes a record's field by its name alone (`PState.shorthands`). -/
def shorthandsOf (src : String) (lib : String → Option String := fun _ => none) : List Pos :=
  match runPS (fun n => decls n n []) src true (dataOf lib src) with
  | .ok (_, s) => s.shorthands
  | .error _ => []

/-- `s` with each word that is a renamed binder of `rs`, or a binder Hygiene renamed
(`Hygiene.written`), replaced by the name the source writes it with. A fresh name is no name of
the source, so a word spelt as one is that binder. -/
def unrename (rs : List (String × String)) (s : String) : String :=
  let isW (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
  let flush (w out : List Char) : List Char :=
    let ws := String.ofList w.reverse
    ((Hygiene.written ((rs.lookup ws).getD ws)).toList.reverse) ++ out
  let (w, out) := s.toList.foldl (fun (w, out) c =>
    if isW c then (c :: w, out) else ([], c :: flush w out)) ([], [])
  String.ofList (flush w out).reverse

/-- An error about the program `src`, rendered with each renamed binder named as the source writes
it (`unrename`). -/
def Error.renderIn (src : String) (e : Error) (lib : String → Option String := fun _ => none) :
    String :=
  { e with msg := unrename (renamesOf src lib) e.msg }.render

end Frontend
