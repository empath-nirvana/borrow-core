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
  | delay (sp : Span) (A : RTy)
  | stream (sp : Span) (A : RTy)

def RTy.span : RTy → Span
  | .unit sp | .zero sp | .tensor sp _ _ | .sum sp _ _ | .U sp _ | .F sp _ | .ref sp _
  | .imm sp _ _ | .mut sp _ _ | .box sp _ _ | .bang sp _ | .unk sp | .int sp _ | .mu sp _ _
  | .name sp _ | .lolli sp _ _ | .arr sp _ _ | .all sp _ _ _ | .forall_ sp _ _ _ | .amp sp _ _
  | .top sp | .block sp _ | .val sp _ | .fam sp _ _ _ | .view sp _ _ | .delay sp _
  | .stream sp _ => sp

/-- What a raw type is, for sort errors. -/
def RTy.former : RTy → String
  | .F .. => "`F A`" | .arr .. => "`A -o C`" | .forall_ .. => "`forall 'x < @. C`"
  | .amp .. => "`C & D`" | .top .. => "`top`" | .delay .. => "`delay A`"
  | .stream .. => "`stream A`" | _ => "this type"

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
  | .U sp C => return .thunk sp (← C.toC)
  | .ref sp A => return .ref sp (← A.toV)
  | .imm sp a A => return .imm sp a (← A.toV)
  | .mut sp a A => return .mut sp a (← A.toV)
  | .box sp a A => return .box sp a (← A.toV)
  | .bang sp A => return .bang sp (← A.toV)
  | .unk sp => pure (.unk sp)
  | .int sp w => pure (.int sp w)
  | .mu sp X A => return .mu sp X (← A.toV)
  | .name sp n => pure (.name sp n)
  | .lolli sp A B => return .lolli sp (← A.toV) (← B.toV)
  | .all sp x b A => return .all sp x b (← A.toV)
  | .block sp σ => pure (.block sp σ)
  | .val sp σ => pure (.val sp σ)
  | .fam sp m a σ => pure (.fam sp m a σ)
  | .view sp a A => return .view sp a (← A.toV)
  | t@(.F ..) | t@(.arr ..) | t@(.forall_ ..) | t@(.amp ..) | t@(.top ..) | t@(.delay ..)
  | t@(.stream ..) => sortErr t true

/-- Sort a raw type as a computation type. -/
def RTy.toC : RTy → Except Error CTy
  | .F sp A => return .ret sp (← A.toV)
  | .arr sp A C => return .arr sp (← A.toV) (← C.toC)
  | .amp sp C D => return .amp sp (← C.toC) (← D.toC)
  | .top sp => pure (.top sp)
  | .forall_ sp x b C => return .all sp x b (← C.toC)
  | .delay sp A => return .delay sp (← A.toV)
  | .stream sp A => return .stream sp (← A.toV)
  | t => sortErr t false
end

/-! ### The parser monad -/

structure PState where
  toks : Array Token
  pos : Nat
  /-- The end of the last consumed token. -/
  lastStop : Pos

abbrev P := StateT PState (Except Error)

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

/-- Tokens that begin a type binder: `forall`, `all`, `mu`. -/
def isTyBinderStart (t : Tok) : Bool :=
  t == .kw "forall" || t == .kw "all" || t == .kw "mu"

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
    | .kw "F" => unary .F
    | .kw "ref" => unary .ref
    | .sym "!" => unary .bang
    | .kw "delay" => unary .delay
    | .kw "stream" | .kw "str" => unary .stream
    | .kw "imm" => withLife .imm
    | .kw "mut" => withLife .mut
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

/-- `1`, `0`, `unk`, `i32`, `i64`, `top`, a name, or a parenthesized type. -/
def rtyAtom : Nat → P RTy
  | 0 => outOfFuel
  | n + 1 => do
    let t ← peek
    match t.tok with
    | .int 1 => discard bump; pure (.unit t.span)
    | .int 0 => discard bump; pure (.zero t.span)
    | .kw "unk" => discard bump; pure (.unk t.span)
    | .kw "i32" => discard bump; pure (.int t.span .w32)
    | .kw "i64" => discard bump; pure (.int t.span .w64)
    | .kw "top" => discard bump; pure (.top t.span)
    | .uident s => discard bump; pure (.name t.span s)
    | .sym "(" =>
      discard bump
      let A ← rty n
      expectSym ")"
      pure A
    | _ => expected "a type"

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
  | .life => .life <$> life n
  | .binder => .binder <$> lifeVar
  | .shape => .shape <$> shape n
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

/-! ### Terms (syntax-core §6) -/

/-- The keyword of a constant, if the token is one. -/
def constKw? : Tok → Option CKw
  | .kw s => CKw.ofString? s
  | _ => none

/-- Tokens that begin a value atom, hence an argument of `V W`. -/
def startsValAtom (t : Tok) : Bool :=
  match t with
  | .ident _ | .sym "(" => true
  | _ => (constKw? t).isSome

mutual
/-- A value-judged expression: a binding form (`thunk`, `thunkv`, `!thunk`, `!thunkv`), which
    extends as far right as possible, or a prefix expression. -/
def val : Nat → P Val
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    match t.tok with
    | .kw "thunk" => discard bump; let M ← comp n; pure (.thunk (← spanFrom st) M)
    | .kw "thunkv" => discard bump; let M ← comp n; pure (.thunkv (← spanFrom st) M)
    | .sym "!" =>
      discard bump
      if ← isKw "thunk" then
        discard bump; let M ← comp n; pure (.bangThunk (← spanFrom st) M)
      else if ← isKw "thunkv" then
        discard bump; let M ← comp n; pure (.bangThunkv (← spanFrom st) M)
      else expected "`thunk` or `thunkv` after `!`"
    | _ => valPrefix n

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
    | _ =>
      let V ← valAtom n
      valSuffixes n st V

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

/-- A value atom: a name, `name[A, …]`, a constant, `()`, `(V)`, `(V, W)`, `(V : A)`,
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
    | .sym "(" =>
      discard bump
      if ← isSym ")" then
        discard bump
        return .unit (← spanFrom st)
      let V ← val n
      let t' ← peek
      match t'.tok with
      | .sym ")" => discard bump; pure V
      | .sym "," =>
        discard bump
        let W ← val n
        expectSym ")"
        pure (.pair (← spanFrom st) V W)
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
    | tok =>
      match constKw? tok with
      | some k =>
        discard bump
        let as ← if k.sig.isEmpty then pure [] else do
          expectSym "["
          let as ← args n k.sig
          expectSym "]"
          pure as
        match Const.ofArgs k as with
        | some c => pure (.const (← spanFrom st) c)
        | none => failAt (← spanFrom st) s!"malformed arguments of `{k.str}`"
      | none => expected "a value"

/-- A computation: a binding form (`x <- M; N`, `x : A <- M; N`, `linear x <- M; N`, `let`,
    `fun`, `Fun`), which extends as far right as possible, or a prefix expression. -/
def comp : Nat → P Comp
  | 0 => outOfFuel
  | n + 1 => do
    let st ← startPos
    let t ← peek
    let t1 ← peekAt 1
    match t.tok, t1.tok with
    | .ident x, .sym "<-" =>
      discard bump; discard bump
      let M ← comp n
      expectSym ";"
      let N ← comp n
      pure (.bind (← spanFrom st) ⟨x, t.span⟩ none M N false)
    | .ident x, .sym ":" =>
      discard bump; discard bump
      let A ← vty n
      expectSym "<-"
      let M ← comp n
      expectSym ";"
      let N ← comp n
      pure (.bind (← spanFrom st) ⟨x, t.span⟩ (some A) M N false)
    | .kw "linear", .ident x =>
      discard bump
      let xt ← bump
      let A ← if ← isSym ":" then do discard bump; pure (some (← vty n)) else pure none
      expectSym "<-"
      let M ← comp n
      expectSym ";"
      let N ← comp n
      pure (.bind (← spanFrom st) ⟨x, xt.span⟩ A M N true)
    | .kw "let", _ =>
      discard bump
      expectSym "("
      if ← isSym ")" then
        discard bump
        expectSym "="
        let V ← val n
        expectSym ";"
        let M ← comp n
        pure (.letUnit (← spanFrom st) V M)
      else
        let x ← ident "a name or `)`"
        expectSym ","
        let y ← ident
        expectSym ")"
        expectSym "="
        let V ← val n
        expectSym ";"
        let M ← comp n
        pure (.letPair (← spanFrom st) x y V M)
    | .kw "fun", _ =>
      discard bump
      expectSym "("
      let x ← ident
      expectSym ":"
      let A ← vty n
      expectSym ")"
      expectSym "->"
      let M ← comp n
      pure (.lam (← spanFrom st) x A M)
    | .kw "Fun", _ =>
      discard bump
      let x ← lifeVar
      expectSym "<"
      let b ← life n
      expectSym "."
      let M ← comp n
      pure (.lamL (← spanFrom st) x b M)
    | _, _ => compPrefix n

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
      let V ← valPrefix n
      pure (.ret (← spanFrom st) V)
    | .kw "absurd" =>
      discard bump
      let V ← valPrefix n
      pure (.absurd (← spanFrom st) V)
    | .kw "delay_in" => unary .delayIn
    | .kw "delay_out" => unary .delayOut
    | .kw "stream_in" => unary .streamIn
    | .kw "stream_out" => unary .streamOut
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

/-- A computation atom: `force x`, `<>`, `<M, N>`, `case V { … }`, `(M)`, `(M : C)`. -/
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
      let M ← comp n
      expectSym ","
      let N ← comp n
      expectSym ">"
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
    | .sym "(" =>
      discard bump
      let M ← comp n
      if ← isSym ":" then
        discard bump
        let C ← cty n
        expectSym ")"
        pure (.ascribe (← spanFrom st) M C)
      else
        expectSym ")"
        pure M
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
  | .kw "def" =>
    discard bump
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
    pure (.def_ (← spanFrom st) x ps A V)
  | .kw "extern" =>
    discard bump
    let x ← ident "an `extern` name"
    expectSym ":"
    let A ← vty n
    pure (.extern (← spanFrom st) x A)
  | .kw "main" =>
    discard bump
    expectSym ":"
    let C ← cty n
    expectSym "="
    let M ← comp n
    pure (.main (← spanFrom st) C M)
  | _ => expected "a declaration (`type`, `shape`, `def`, `extern` or `main`)"
where
  /-- `P₁, …, Pₙ`: a `def`'s type parameters, at least one. -/
  uidents : Nat → P (List Ident)
    | 0 => outOfFuel
    | m + 1 => do
      let p ← uident "a type parameter"
      if ← isSym "," then
        discard bump
        return p :: (← uidents m)
      else pure [p]

/-- Declarations until the end of input. -/
def decls (n : Nat) : Nat → List Decl → P (List Decl)
  | 0, _ => outOfFuel
  | m + 1, acc => do
    if (← peek).tok == .eof then pure acc.reverse
    else
      let d ← decl n
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
  (·.1) <$> go.run ⟨toks, 0, ⟨1, 1⟩⟩

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
