import Frontend.Lexer
import Frontend.Consts
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
  | handle (sp : Span) (out : Bool)
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

def RTy.span : RTy → Span
  | .unit sp | .zero sp | .tensor sp _ _ | .sum sp _ _ | .U sp _ | .F sp _ | .ref sp _
  | .imm sp _ _ | .mut sp _ _ | .box sp _ _ | .bang sp _ | .unk sp | .int sp _ | .handle sp _ | .mu sp _ _
  | .name sp _ | .lolli sp _ _ | .arr sp _ _ | .all sp _ _ _ | .forall_ sp _ _ _ | .amp sp _ _
  | .top sp | .block sp _ | .val sp _ | .fam sp _ _ _ | .view sp _ _ | .nu sp _ _ | .delay sp _
  | .stream sp _ | .iter sp _ _ _ | .loop sp _ _ | .pull sp _ _ _ | .array sp _ | .arrayImm sp _ _
  | .arrayMut sp _ _ | .sized sp _ _ _ | .eff sp _ _ => sp

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

abbrev P := StateT PState (Except Error)

/-- Parse a closure, block or borrow block's body: a statement `return e` in it is the core's. -/
def inClosure {α} (p : P α) : P α := do
  let l₀ := (← get).inLoop
  modify fun s => { s with inLoop := false }
  let r ← p
  modify fun s => { s with inLoop := l₀ }
  pure r

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
    | .kw "box" => withLife .box
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
    | .kw "input" => discard bump; pure (.handle t.span false)
    | .kw "output" => discard bump; pure (.handle t.span true)
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
    | .uident s => discard bump; pure (.name t.span s)
    | .sym "(" =>
      discard bump
      let A ← rty n
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

/-- The entries of a row up to its `]`: `n.i q A ~> B`, separated by `,`; `q` is `lin`, `aff` or
`unr`, read as a name here and nowhere else. -/
def rowEntries : Nat → P Row
  | 0 => outOfFuel
  | n + 1 => do
    if ← isSym "]" then return .nil
    let t ← peek
    let k ← match t.tok with
      | .int k => discard bump; pure k
      | _ => expected "an operation `n.i` of a row"
    expectSym "."
    let t' ← peek
    let i ← match t'.tok with
      | .int i => discard bump; pure i
      | _ => expected "the index `i` of an operation `n.i`"
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

/-- A right-nested tuple pattern. -/
def nestPat (sp : Span) : List Pat → Pat
  | [] => .unit sp
  | [p] => p
  | p :: ps => .pair sp p (nestPat sp ps)

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
  | .app _ (.app _ (.sugar _ (.handle _ _ _)) P) (.thunkv _ (.lam _ _ _ M)) =>
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
  | .case _ V _ M _ N | .for_ _ _ V M N => V.lentNames vars ++ M.lentNames vars ++ N.lentNames vars
  | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M => M.lentNames vars
  | .perform _ _ _ V | .abort _ _ _ V => V.lentNames vars
  | .handle _ _ _ _ M => M.lentNames vars
  | .unwind _ _ _ M D N => M.lentNames vars ++ D.lentNames vars ++ N.lentNames vars
  | _ => []
end

mutual
/-- The cells lent to a `with h(&mut c)` in a value, outside nested closures, that are not bound
in `local`: an enclosing block hands them back (SPEC §18). -/
def Val.withPlaces (loc : List String) : Val → List String
  | .app _ (.app _ (.sugar _ (.handle _ _ _)) P) (.thunkv _ (.lam _ b _ M)) =>
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
  | .for_ _ x V M N => V.withPlaces loc ++ M.withPlaces (x.name :: loc) ++ N.withPlaces loc
  | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M => M.withPlaces loc
  | .perform _ _ _ V | .abort _ _ _ V => V.withPlaces loc
  | .handle _ _ _ _ M => M.withPlaces loc
  | .unwind _ x _ M D N => M.withPlaces loc ++ D.withPlaces loc ++ N.withPlaces (x.name :: loc)
  | _ => []
end

/-- The names a computation binds, outside nested closures. -/
def Comp.boundNames : Comp → List String
  | .bind _ x _ M N _ => x.name :: (M.boundNames ++ N.boundNames)
  | .letPair _ x y _ M => x.name :: y.name :: M.boundNames
  | .case _ _ x M y N => x.name :: y.name :: (M.boundNames ++ N.boundNames)
  | .for_ _ x _ M N => x.name :: (M.boundNames ++ N.boundNames)
  | .lam _ x _ M => x.name :: M.boundNames
  | .letUnit _ _ M | .app _ M _ | .proj _ _ M | .inst _ M _ | .ascribe _ M _ | .nuOut _ M =>
    M.boundNames
  | .handle _ _ _ _ M => M.boundNames
  | .unwind _ x _ M D N => x.name :: (M.boundNames ++ D.boundNames ++ N.boundNames)
  | _ => []

/-- A borrow block or `modify` on a place that is a name (or, for a family, a pair of names): the
names it rebinds. -/
def Val.rebinds : Val → Option Pat
  | .app _ (.app _ (.sugar _ (.borrow _ _)) P) _ => placeNames P
  -- `with h(&mut c) { … }` hands the cell `c` back; a `with` whose body hands back the
  -- variables it assigns hands back its place beside them, which is dropped. Any other `with`
  -- answers its result alone.
  | .app sp (.app _ (.sugar _ (.handle _ _ _)) P) (.thunkv _ (.lam _ _ _ M)) => match P with
    | .lend _ x _ => some (.var x)
    | _ => if M.boundNames.contains "io_bt" then some (.wild sp) else none
  | _ => none
where
  placeNames : Val → Option Pat
    | .var sp x => some (.var ⟨x, sp⟩)
    | .pair sp (.var s₁ x) (.var s₂ y) => some (.pair sp (.var ⟨x, s₁⟩) (.var ⟨y, s₂⟩))
    -- A literal lent by a borrow block is handed back, and dropped.
    | .sugar sp (.str _) => some (.wild sp)
    | _ => none

/-- The pattern of the variables `xs`. -/
def varPat (sp : Span) : List String → Pat
  | [] => .unit sp
  | [x] => .var ⟨x, sp⟩
  | x :: xs => .pair sp (.var ⟨x, sp⟩) (varPat sp xs)

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
  | .ident _ | .sym "(" | .sym "&" | .int _ | .str _ | .kw "clone" | .kw "box" => true
  | _ => (constKw? t).isSome

/-- Tokens that begin a computation, as against a value statement. -/
def startsComp (t : Tok) : Bool :=
  match t with
  | .kw "return" | .kw "absurd" | .kw "nu_in" | .kw "delay_in" | .kw "stream_in" | .kw "nu_out"
  | .kw "delay_out" | .kw "stream_out" | .kw "force" | .sym "<" | .kw "case" | .kw "match"
  | .kw "if" | .kw "perform" | .kw "abort" | .kw "handle_with" => true
  | _ => false

/-- A binary operator: one of the surface's arithmetic and comparisons, or `&&`/`||`, which are
`case`s (they do not evaluate their right operand when the left decides). -/
inductive BinTok where
  | op (o : SurfOp)
  | and
  | or

/-- The operator of a token, with its precedence: `||` 0, `&&` 1, comparisons 2, `+`/`-` 3,
`*` 4. -/
def opOf (angle : Bool) : Tok → Option (BinTok × Nat)
  | .sym "||" => some (.or, 0) | .sym "&&" => some (.and, 1)
  | .sym "==" => some (.op .eq, 2) | .sym "!=" => some (.op .ne, 2) | .sym "<" => some (.op .lt, 2)
  | .sym "<=" => some (.op .le, 2) | .sym ">=" => some (.op .ge, 2)
  | .sym ">" => if angle then none else some (.op .gt, 2)
  | .sym "+" => some (.op .add, 3) | .sym "-" => some (.op .sub, 3) | .sym "*" => some (.op .mul, 4)
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
  | .for_ sp x V M N => .for_ sp x V M (wrapTerms f N)
  | T => f T

/-- The tuple of the variables `xs`. -/
def varTuple (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (varTuple sp xs)

/-- A `match` or `if` whose arms assign the `let mut` variables `xs`: each arm ends by handing
them on (the join; typed elaboration §5.2). -/
def joinArms (xs : List String) : Comp → Comp
  | .case sp V x M y N =>
    let hand (T : Comp) : Comp :=
      .bind T.span ⟨"io_ju", T.span⟩ none T (.ret T.span (varTuple T.span xs)) false
    .case sp V x (wrapTerms hand M) y (wrapTerms hand N)
  | M => M

/-- The loop's value, bound after it (`let r = for …`): `forRes`, applied to the thunk of the
`else` value when there is one. -/
def forResOf (sp : Span) : Option Comp → Val
  | some d => .app sp (.sugar sp .forRes) (.thunk sp d)
  | none => .sugar sp .forRes

/-- A binder type to be filled by the elaborator (a closure's, a borrow callback's). -/
def holeTy (sp : Span) : VTy := .name sp "_"

mutual
/-- A value-judged expression: a binding form (`thunk`, `thunkv`, `!thunk`, `!thunkv`), which
    extends as far right as possible, a block `{ … }` or `!{ … }`, or an operator expression. -/
def val : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .kw "thunk" => discard bump; let M ← inClosure (comp n); pure (.thunk (← spanFrom st) M)
    | .kw "thunkv" => discard bump; let M ← inClosure (comp n); pure (.thunkv (← spanFrom st) M)
    | .sym "!" =>
      discard bump
      if ← isKw "thunk" then
        discard bump; let M ← inClosure (comp n); pure (.bangThunk (← spanFrom st) M)
      else if ← isKw "thunkv" then
        discard bump; let M ← inClosure (comp n); pure (.bangThunkv (← spanFrom st) M)
      else if ← isSym "{" then brace n st true
      else expected "`thunk`, `thunkv` or `{` after `!`"
    | .sym "{" => pipes n st (← brace n st false)
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
      pipes n st a

/-- `a |> g(…) |> …`, associating to the left (decision 50): each `VSugar.pipe`. -/
def pipes : Nat → Pos → Val → P Val
  | 0, _, _ => outOfFuel
  | n + 1, st, a => do
    let t ← peek
    if t.tok != .sym "|>" then return a
    discard bump
    let g ← valPrefix n
    let sp ← spanFrom st
    pipes n st (.app sp (.sugar t.span .pipe) (.pair sp a g))

/-- Operators, by precedence `lvl` and above, associating to the left. -/
def valOps : Nat → Nat → P Val
  | 0, _ => outOfFuel
  | n + 1, lvl => do
    let st ← startPos
    let a ← if lvl ≥ 4 then valPrefix n else valOps n (lvl + 1)
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
      let b ← if lvl ≥ 4 then valPrefix m else valOps m (lvl + 1)
      let sp ← spanFrom st
      let v := match o with
        | .op o => Val.app sp (.sugar osp (.op o)) (.pair sp a b)
        | .and => shortCircuit sp true a b
        | .or => shortCircuit sp false a b
      -- Comparisons do not associate.
      if lvl == 2 then return v else opsLoop m lvl st v
    | none => return a

/-- The components after the first of a tuple, at least one. -/
def rest : Nat → P (List Val)
  | 0 => outOfFuel
  | n + 1 => do
    let W ← val n
    if ← isSym "," then discard bump; return W :: (← rest n)
    pure [W]

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
    | some p =>
      let M ← blockBody n
      expectSym "}"
      let sp ← spanFrom st
      let (x, M) ← match p with
        | .var x => pure (x, M)
        | p => do
          let x : Ident := ⟨← freshName "io_c", sp⟩
          pure (x, ← bindPat sp n p (.var sp x.name) M)
      let lam := Comp.lam sp x (holeTy sp) M
      pure (if bang then .bangThunkv sp lam else .thunkv sp lam)
    | none =>
      let M ← blockBody n
      expectSym "}"
      let sp ← spanFrom st
      pure (.app sp (.sugar sp .brace) (if bang then .bangThunk sp M else .thunk sp M))

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
      discard bump
      let M ← compPrefix n
      pure (.run (← spanFrom st) M)
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

/-- A borrow block: `borrow imm V { 'x, p -> S }`, `borrow mut V { … }`, `borrow mut (V, W)
{ … }` (a family), or `modify V { p -> S }`. The lifetime `'x` may be left out. -/
def borrowBlock : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    inClosure do
    let st ← startPos
    let t ← bump
    let k ← if t.tok == .kw "modify" then pure BorrowKind.modify else
      if ← isKw "imm" then discard bump; pure .imm
      else if ← isKw "mut" then discard bump; pure .mut
      else expected "`imm` or `mut` after `borrow`"
    let place ← valPrefix n
    let k := match k, place with
      | .mut, .pair .. => BorrowKind.famMut
      | k, _ => k
    expectSym "{"
    let x ← if (match (← peek).tok with | .life _ => true | _ => false)
      then do let x ← lifeVar; expectSym ","; pure x.name
      else if k == .modify then pure "" else freshName "io_l"
    let p ← pat n
    expectSym "->"
    let s₀ ← get
    set { s₀ with assigned := [] }
    let M ← comp n
    let assigned := (← get).assigned
    modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned }
    expectSym "}"
    let sp ← spanFrom st
    -- The variables the block hands back beside its result, as a `for` hands back what its body
    -- assigns: the enclosing `let mut` variables it assigns, the places it lends that it does not
    -- bind itself (a capability lent with `&mut stdout`, a buffer lent to `push`), and the
    -- standard capabilities it uses.
    let bound := M.boundNames ++ (match p with | .var b => [b.name] | _ => [])
    let caps := ["stdin", "stdout", "stderr"].filter (M.lentNames true).contains
    let thr := ((s₀.muts.filter assigned.contains).reverse ++
      (M.lentNames.filter (fun x => !bound.contains x)) ++ M.withPlaces (match p with | .var b => [b.name] | _ => []) ++ caps).eraseDups
    -- A body already handing its variables back (a printed program read again) is kept.
    let thr := if k == .modify || bound.contains "io_bt" then [] else thr
    let M := if thr.isEmpty then M else
      wrapTerms (fun T => .bind T.span ⟨"io_bt", T.span⟩ none T
        (.ret T.span (.pair T.span (.var T.span "io_bt") (varTuple T.span thr))) false) M
    -- The `let mut` variables the block hands back are assigned where the block is.
    modify fun s => { s with blockThreads := thr, joined := [],
                             assigned := s.assigned ++ thr.filter s₀.muts.contains }
    let (b, M) ← match p with
      | .var b => pure (b, M)
      | p => do
        let b : Ident := ⟨← freshName "io_c", sp⟩
        pure (b, ← bindPat sp n p (.var sp b.name) M)
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
    let st ← startPos
    let t ← bump
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
    let s₀ ← get
    set { s₀ with assigned := [] }
    let M ← comp n
    let assigned := (← get).assigned
    modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned }
    expectSym "}"
    let sp ← spanFrom st
    let bound := b.name :: M.boundNames
    let caps := ["stdin", "stdout", "stderr"].filter (M.lentNames true).contains
    let thr := ((s₀.muts.filter assigned.contains).reverse ++
      (M.lentNames.filter (fun x => !bound.contains x)) ++ M.withPlaces [b.name] ++ caps).eraseDups
    let thr := if bound.contains "io_bt" then [] else thr
    let M := if thr.isEmpty then M else
      wrapTerms (fun T => .bind T.span ⟨"io_bt", T.span⟩ none T
        (.ret T.span (.pair T.span (.var T.span "io_bt") (varTuple T.span thr))) false) M
    modify fun s => { s with blockThreads := thr, joined := [],
                             assigned := s.assigned ++ thr.filter s₀.muts.contains }
    pure (.app sp (.app sp (.sugar t.span (.handle h.name x As)) place)
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
    else if startsValAtom t.tok then
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
      if nx.tok == .sym "[" && !nx.spaced then
        discard bump
        let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
        expectSym "]"
        pure (.defApp (← spanFrom st) s As)
      else pure (.var t.span s)
    | .int k => discard bump; pure (.sugar t.span (.lit k))
    | .str bs => discard bump; pure (.sugar t.span (.str bs))
    -- `box buf[A](cap)`, `box string(cap)`, `box array(n, f)`: the allocating constructors of the
    -- buffer and text libraries (`buf_new[A]`, `string_new`, `array_tab`).
    | .kw "box" =>
      discard bump
      let k ← peek
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
      pure r
    | .sym "&" =>
      discard bump
      let m ← if ← isKw "mut" then do discard bump; pure Mode.mut else pure Mode.imm
      let x ← ident "the name of a place"
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
      let M ← compG n true
      -- `x <- M unwind (D); N` (SPEC §19).
      let D ← unwindOf n
      expectSym ";"
      let N ← comp n
      let sp ← spanFrom st
      pure (match D with
        | some D => .unwind sp ⟨x, t.span⟩ none M D N
        | none => .bind sp ⟨x, t.span⟩ none M N false)
    | .ident x, .sym ":" =>
      discard bump; discard bump
      let A ← vty n
      expectSym "<-"
      let M ← compG n true
      let D ← unwindOf n
      expectSym ";"
      let N ← comp n
      let sp ← spanFrom st
      pure (match D with
        | some D => .unwind sp ⟨x, t.span⟩ (some A) M D N
        | none => .bind sp ⟨x, t.span⟩ (some A) M N false)
    | .ident x, .sym "=" =>
      -- `x = e`: a `let mut` variable rebound (typed elaboration §5.2).
      discard bump; discard bump
      unless (← get).muts.contains x do
        failAt t.span s!"`{x}` is assigned, but it is not declared `let mut`"
      modify fun s => { s with assigned := x :: s.assigned, blockThreads := [] }
      let V ← val n
      let thr := (← get).blockThreads
      if !head && (← isSym ";") then
        discard bump
        let N ← comp n
        let sp ← spanFrom st
        -- A block's value is rebound as `let x = …` binds it (`letVal`).
        if V.rebinds.isSome then return ← letVal sp n (.var ⟨x, t.span⟩) none V N thr
        pure (.bind sp ⟨x, t.span⟩ none (.ret V.span V) N false)
      else
        let sp ← spanFrom st
        if V.rebinds.isSome then return ← letVal sp n (.var ⟨x, t.span⟩) none V (.ret sp (.unit sp)) thr
        pure (.bind sp ⟨x, t.span⟩ none (.ret V.span V) (.ret sp (.unit sp)) false)
    | .kw "linear", .ident x =>
      discard bump
      let xt ← bump
      let A ← if ← isSym ":" then do discard bump; pure (some (← vty n)) else pure none
      expectSym "<-"
      let M ← compG n true
      expectSym ";"
      let N ← comp n
      pure (.bind (← spanFrom st) ⟨x, xt.span⟩ A M N true)
    | .kw "for", _ =>
      discard bump
      let x ← ident
      expectKw "in"
      let V ← val n
      expectSym "{"
      let M ← withLoop (comp n)
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
        pure (.for_ sp x V M (match els with
          | some d => .bind sp ⟨r, sp⟩ none (.ret sp (forResOf sp (some d))) N false
          | none => N))
      else
        pure (.for_ sp₀ x V M (match els with
          | some d => .bind sp₀ ⟨r, sp₀⟩ none (.ret sp₀ (forResOf sp₀ (some d))) (.ret sp₀ (.var sp₀ r)) false
          | none => .ret sp₀ (.unit sp₀)))
    | .kw "while", _ =>
      -- `while c { M }; N`: a `for` whose iterator is the condition (a generator's loop).
      discard bump
      let c ← val n
      expectSym "{"
      let M ← withLoop (comp n)
      expectSym "}"
      -- Last in a body, what follows it is `()`.
      let N ← if ← isSym ";" then do discard bump; comp n else pure (.ret t.span (.unit t.span))
      let sp ← spanFrom st
      pure (.for_ sp ⟨"io_while", t.span⟩ (.app c.span (.sugar t.span .while_) c) M N)
    | .kw "loop", .sym "{" =>
      -- `loop { M }`: a `while` whose condition never fails (`VSugar.forever`). What follows it
      -- runs only after a `break`.
      discard bump
      expectSym "{"
      let M ← withLoop (comp n)
      expectSym "}"
      let N ← if ← isSym ";" then do discard bump; comp n else pure (.ret t.span (.unit t.span))
      let sp ← spanFrom st
      pure (.for_ sp ⟨"io_while", t.span⟩ (.app t.span (.sugar t.span .while_) (.sugar t.span .forever)) M N)
    | .kw "let", _ =>
      discard bump
      let isMut ← if ← isKw "mut" then do discard bump; pure true else pure false
      let p ← pat n
      if isMut then
        match p with
        | .var x => modify fun s => { s with muts := x.name :: s.muts }
        | _ => failAt (← spanFrom st) "`let mut` binds a name"
      let A ← if ← isSym ":" then do discard bump; pure (some (← vty n)) else pure none
      expectSym "="
      if (← peek).tok == .kw "for" then
        -- `let r = for x in V { M }; N`: the loop's value, what its iterator finishes with or
        -- what a `break e` gives, bound in what follows it.
        let r ← match p with
          | .var r => pure r
          | _ => failAt (← spanFrom st) "`let … = for …` binds a name"
        discard bump
        let x ← ident
        expectKw "in"
        let V ← val n
        expectSym "{"
        let M ← withLoop (comp n)
        expectSym "}"
        let els ← forElse n
        expectSym ";"
        let N ← comp n
        let sp ← spanFrom st
        return .for_ sp x V M (.bind sp r A (.ret sp (forResOf sp els)) N false)
      if (← peek).tok == .kw "match" || (← peek).tok == .kw "if" then
        let M ← compPrefix n
        expectSym ";"
        let N ← comp n
        let sp ← spanFrom st
        match p with
        | .var x => return .bind sp x A M N false
        | p =>
          let tv ← freshName "io_t"
          return .bind sp ⟨tv, sp⟩ A M (← bindPat sp n p (.var sp tv) N) false
      modify fun s => { s with blockThreads := [] }
      let V ← val n
      let thr := (← get).blockThreads
      expectSym ";"
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

/-- A statement: a computation, a force `t!` or `f!(e)`, or an expression `e`, which is returned.
    Outside the head of a binding, `S; N` sequences it (its result is dropped), and a borrow
    block or `modify` on a place rebinds the place. -/
def statement : Nat → Pos → Bool → P Comp
  | 0, _, _ => outOfFuel
  | n + 1, st, head => do
    let t ← peek
    let t1 ← peekAt 1
    modify fun s => { s with joined := [], blockThreads := [] }
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
      | .ident f, .sym "!" =>
        discard bump; discard bump
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
        else do
          let V ← val n
          pure (Comp.ret (← spanFrom st) V, V.rebinds)
    let joined := (← get).joined
    let thr := (← get).blockThreads
    if !head && (← isSym ";") then
      discard bump
      let N ← comp n
      let sp ← spanFrom st
      -- A `match` or `if` that assigns `let mut` variables hands them on to what follows.
      if !joined.isEmpty then
        let j ← freshName "io_j"
        return .bind sp ⟨j, sp⟩ none (joinArms joined S)
          (← bindPat sp n (varPat sp joined) (.var sp j) N) false
      match S, rebind with
      | .ret _ V, some _ =>
        letVal sp n (.wild sp) none V N thr
      | S, _ =>
        let d ← freshName "io_s"
        pure (.bind sp ⟨d, sp⟩ none S N false)
    else
      match S, rebind with
      | .ret _ V, some _ =>
        -- A tail borrow block hands back its result; the place is rebound, and dropped.
        let sp ← spanFrom st
        let v ← freshName "io_v"
        letVal sp n (.var ⟨v, sp⟩) none V (.ret sp (.var sp v)) thr
      | S, _ => pure S

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
      let k ← match (← peek).tok with
        | .int k => discard bump; pure k
        | _ => expected "the name `n` of an operation `n.i`"
      expectSym "."
      let i ← match (← peek).tok with
        | .int i => discard bump; pure i
        | _ => expected "the index `i` of an operation `n.i`"
      expectSym "]"
      let V ← valPrefix n
      let sp ← spanFrom st
      pure (if t.tok == .kw "perform" then .perform sp k i V else .abort sp k i V)
    | .kw "handle_with" =>
      -- `handle_with[n](hr, hc) M` (SPEC §19).
      discard bump
      expectSym "["
      let k ← match (← peek).tok with
        | .int k => discard bump; pure k
        | _ => expected "the name `n` of a handler"
      expectSym "]"
      expectSym "("
      let hr ← ident "the variable of the answer clause"
      expectSym ","
      let hc ← ident "the variable of the clauses"
      expectSym ")"
      let M ← compPrefix n
      pure (.handle (← spanFrom st) k hr hc M)
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
      discard bump
      compSuffixes n st (.app (← spanFrom st) M ⟨x, t.span⟩)
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

/-- An arm of a `match` or `if`: its computation, and the `let mut` variables it assigns. The
`let mut`s it declares are its own. -/
def armOf : Nat → P (Comp × List String)
  | 0 => outOfFuel
  | n + 1 => do
    let s₀ ← get
    set { s₀ with assigned := [] }
    let M ← comp n
    let a := (← get).assigned
    modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned ++ a }
    pure (M, a)

/-- `else if …`: an `if` as the arm, with what it assigns. -/
def armIf : Nat → P (Comp × List String)
  | 0 => outOfFuel
  | n + 1 => do
    let s₀ ← get
    set { s₀ with assigned := [] }
    let M ← compAtom n
    let a := (← get).assigned
    modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned ++ a }
    pure (M, a)

/-- A block's body: assignments inside it are not the enclosing arm's. -/
def blockBody : Nat → P Comp
  | 0 => outOfFuel
  | n + 1 => do
    let s₀ ← get
    let M ← comp n
    modify fun s => { s with muts := s₀.muts, assigned := s₀.assigned }
    pure M

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
    discard bump
    expectSym "{"
    let d ← inClosure (blockBody n)
    expectSym "}"
    pure (some d)

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
      let x ← ident "a variable (`force` takes a variable)"
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
      let V ← val n
      expectSym "{"
      expectKw "inl"
      let x ← ident
      expectSym "->"
      let M ← comp n
      expectSym "|"
      expectKw "inr"
      let y ← ident
      expectSym "->"
      let N ← comp n
      expectSym "}"
      pure (.case (← spanFrom st) V x M y N)
    | .kw "match" =>
      discard bump
      let outer := (← get).muts
      let V ← val n
      expectSym "{"
      expectKw "inl"
      let p ← pat n
      expectSym "->"
      let (M, a₁) ← armOf n
      expectSym "|"
      expectKw "inr"
      let q ← pat n
      expectSym "->"
      let (N, a₂) ← armOf n
      expectSym "}"
      -- In the order the variables were declared.
      modify fun s => { s with joined := (outer.filter (a₁ ++ a₂).contains).reverse }
      let sp ← spanFrom st
      let arm (p : Pat) (M : Comp) : P (Ident × Comp) := match p with
        | .var x => pure (x, M)
        | p => do
          let x : Ident := ⟨← freshName "io_m", sp⟩
          pure (x, ← bindPat sp n p (.var sp x.name) M)
      let (x, M) ← arm p M
      let (y, N) ← arm q N
      pure (.case sp V x M y N)
    | .kw "if" =>
      -- `if V { S₁ } else { S₂ }`: `inr ()` is true (typed elaboration §5.4).
      discard bump
      let outer := (← get).muts
      let V ← val n
      expectSym "{"
      let (M, a₁) ← armOf n
      expectSym "}"
      let (N, a₂) ← if ← isKw "else" then do
          discard bump
          if ← isKw "if" then armIf n
          else do
            expectSym "{"
            let r ← armOf n
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

def decl (n : Nat) : P Decl := do
  let st ← startPos
  let t ← peek
  match t.tok with
  | .kw "type" =>
    discard bump
    let x ← uident "a type name"
    expectSym "="
    let A ← vty n
    pure (.type (← spanFrom st) x A)
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
  | .kw "include" =>
    discard bump
    let x ← ident "the name of a library module"
    pure (.include (← spanFrom st) x)
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
      expectSym "("
      let ps ← if ← isSym ")" then pure [] else (·.map fun (x, A, _) => (x, A)) <$> params n
      expectSym ")"
      let B ← if ← isSym "->" then do discard bump; vty n else pure (VTy.unit o.span)
      ops := ops.push ⟨o, ps, B, kind⟩
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
    let mut ps : Array (Ident × VTy) := #[]
    let mut mutPs : List String := []
    if ← isSym "(" then
      discard bump
      for _ in [0:n] do
        if ← isSym ")" then break
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
      modify fun s => { s with muts := mutPs, assigned := [], surf := true }
      let M ← if ← isSym "{" then do
          discard bump
          let M ← comp n
          expectSym "}"
          pure M
        else compG n true
      modify fun s => { s with muts := [], assigned := [], surf := false }
      if isRet then
        let some x := xs[0]? | failAt o.span "`return(x) = M`: the return clause binds the body's value"
        ret := some (x, M)
      else cs := cs.push ⟨o, xs.toList, M⟩
      if ← isSym ";" then discard bump
    expectSym "}"
    let sp ← spanFrom st
    match sig with
    | some (A, R) =>
      let some (x, M) := ret | failAt h.span s!"the control handler `{h.name}` has no return clause, `return(x) = M`"
      pure (.chandler sp ⟨h, tps, ps.toList, e, As, row, R, (x, A, M), cs.toList⟩)
    | none =>
      match ps.toList, mutPs, tps, As, row, ret with
      | [(sv, S)], [_], [], [], [], none => pure (.handler sp h sv S e cs.toList)
      | _, _, _, _, _, _ => failAt h.span (s!"`{h.name}`: an answering handler is `handler h(mut s: S): E = " ++
          "{ op(x) = e; … }`, and a control handler names its body's type and its answer, " ++
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
      modify fun s => { s with surf := true }
      let M ← comp n
      modify fun s => { s with surf := false }
      return .main (← spanFrom st) C M
    expectSym ":"
    let C ← cty n
    expectSym "="
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
    expectSym ":"
    let A ← vty n
    expectSym "="
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
    let ps₃ ← if ← isSym ")" then pure [] else params n
    let ps := ps₃.map fun (x, A, _) => (x, A)
    expectSym ")"
    expectSym "->"
    let T ← rty n
    -- `with E₁, E₂[A]`: a written row (SPEC §18).
    let es ← if ← isKw "with" then do discard bump; rowList n else pure []
    expectSym "="
    modify fun s => { s with muts := [], assigned := [], surf := true }
    let M ← comp n
    modify fun s => { s with surf := false }
    let sp ← spanFrom st
    let A := tupleTy sp (ps.map (·.2))
    let pn ← freshName "io_p"
    let body ← bindParams sp pn (ps.map (·.1)) M
    let lam := Comp.lam sp ⟨pn, sp⟩ A body
    let fnTy ← match T.toV with
      | .ok B => pure (VTy.lolli sp A B)
      | .error _ => do let C ← liftSort T.toC; pure (VTy.thunk sp (.arr sp A C))
    let (ty, V) := withLives sp lives fnTy lam
    let mk := if tps.isEmpty then mk else .template mk
    -- The provided rows of the computation parameters (SPEC §22), outside the template mark.
    let mk := ps₃.foldr (fun (x, _, es) m => if es.isEmpty then m else .provides x es m) mk
    pure (.def_ sp x tps ty V (if es.isEmpty then mk else .row es mk))
  /-- `E₁, E₂[A, …], …`: the effects of a written row, at least one. -/
  rowList : Nat → P (List (Ident × List VTy))
    | 0 => outOfFuel
    | m + 1 => do
      let e ← uident "an effect name"
      let As ← if ← isSym "[" then do
          discard bump
          let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
          expectSym "]"
          pure As
        else pure []
      if ← isSym "," then
        discard bump
        return (e, As) :: (← rowList m)
      else pure [(e, As)]
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
  /-- `x₁: A₁, …, xₙ: Aₙ`, at least one; a computation parameter's type may be followed by its
  provided row, `x: A => B with E₁, E₂[A]` (SPEC §22). -/
  params : Nat → P (List (Ident × VTy × List (Ident × List VTy)))
    | 0 => outOfFuel
    | m + 1 => do
      let x ← ident "a parameter name"
      expectSym ":"
      let A ← vty n
      let es ← if ← isKw "with" then do discard bump; paramRow m else pure []
      if ← isSym "," then
        discard bump
        return (x, A, es) :: (← params m)
      else pure [(x, A, es)]
  /-- The provided row of a parameter: `E₁, E₂[A, …]`, up to a `,` that is followed by the next
  parameter's name or the `)`. -/
  paramRow : Nat → P (List (Ident × List VTy))
    | 0 => outOfFuel
    | m + 1 => do
      let e ← uident "an effect name"
      let As ← if ← isSym "[" then do
          discard bump
          let As ← tyList n (fuelPerToken * ((← get).toks.size + 1))
          expectSym "]"
          pure As
        else pure []
      let more := (← isSym ",") && (match (← peekAt 1).tok with | .uident _ => true | _ => false)
      if more then
        discard bump
        return (e, As) :: (← paramRow m)
      else pure [(e, As)]
  /-- The parameter tuple's type (`1` with no parameters). -/
  tupleTy (sp : Span) : List VTy → VTy
    | [] => .unit sp
    | [A] => A
    | A :: As => .tensor sp A (tupleTy sp As)
  /-- Bind the parameters from the tuple `p`. -/
  bindParams (sp : Span) (p : String) : List Ident → Comp → P Comp
    | [], M => pure (.letUnit sp (.var sp p) M)
    | [x], M => pure (.bind sp x none (.ret sp (.var sp p)) M false)
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

/-- `with[E₁, E₂[A]] def …`: a definition with a written row, as it is printed (SPEC §18); and
`with[x: E₁, …] def …`, the provided row of its parameter `x` (SPEC §22). -/
def rowDecl : Nat → P Decl
  | 0 => outOfFuel
  | n + 1 => do
    let t ← bump
    expectSym "["
    let x? ← match (← peek).tok, (← peekAt 1).tok with
      | .ident _, .sym ":" => do let x ← ident; expectSym ":"; pure (some x)
      | _, _ => pure none
    let es ← decl.rowList n n
    expectSym "]"
    let d ← if (← peek).tok == .kw "with" then rowDecl n else decl n
    match d, x? with
    | .def_ sp x ps A V mk, none => pure (.def_ sp x ps A V (.row es mk))
    | .def_ sp x ps A V mk, some p => pure (.def_ sp x ps A V (.provides p es mk))
    | _, _ => failAt t.span "a written row is on a function"

/-- Declarations until the end of input. -/
def decls (n : Nat) : Nat → List Decl → P (List Decl)
  | 0, _ => outOfFuel
  | m + 1, acc => do
    if (← peek).tok == .eof then pure acc.reverse
    else
      let d ← if (← peek).tok == .kw "with" then rowDecl n else decl n
      decls n m (d :: acc)

/-! ### Entry points -/

/-- Run a parser over the tokens of `src`, requiring it to consume all of them. -/
def runP {α} (p : Nat → P α) (src : String) : Except Error α := do
  let toks ← lex src
  let fuel := fuelPerToken * (toks.size + 1)
  let go : P α := do
    let a ← p fuel
    if (← peek).tok != .eof then expected "end of input"
    pure a
  (·.1) <$> go.run { toks, pos := 0, lastStop := ⟨1, 1⟩ }

/-- The declarations of a source file. At most one `main` is accepted. -/
def parseProgram (src : String) : Except Error Program := do
  let ds ← runP (fun n => decls n n []) src
  let mains := ds.filter fun | .main .. => true | _ => false
  match mains with
  | _ :: .main sp _ _ :: _ => .error ⟨sp, "a program has at most one `main`"⟩
  | _ => pure ⟨ds⟩

def parseVal (src : String) : Except Error Val := runP val src
def parseComp (src : String) : Except Error Comp := runP comp src
def parseVTy (src : String) : Except Error VTy := runP vty src
def parseCTy (src : String) : Except Error CTy := runP cty src

end Frontend
