import Frontend.Parser
/-!
# Frontend — `bcc respell`: today's spelling to SPEC §82's

The translator of SPEC §82: a program in today's spelling, printed in the new one, with the same
core term. It is driven by today's parser: the parse records, for each construct whose spelling
changes, the tokens a rewrite needs (`Respell.Ev`, `Frontend/RespellEv.lean`), and this module
turns those records into edits of the source text. An edit replaces a range of the source by
literal text and sub-ranges of the source, each rendered with the edits inside it, so comments,
blank lines and layout survive, and a construct can move its parts (`with h(e) { M }` to
`handle { M } with h(e)`).

Comments are the gaps between tokens: the lexer skips only whitespace and `--` comments there,
so each `--` that opens a comment in a gap becomes `#`.

What the translator cannot write in the new spelling is left as it is, marked at the end of its
line with a comment `#?respell: <form>`; `bcc respell` then exits non-zero.  `[spec §82]`
-/

namespace Frontend.Respell

open Frontend

/-- The first line of a source text in the new spelling (SPEC §82).  `[spec §82]` -/
def pragma : String := "#! dialect 82"

/-- A part of an edit's text: literal text, or a range of the source (character offsets), itself
rendered with the edits inside it. -/
inductive Piece where
  | lit (s : String)
  | src (a b : Nat)
  deriving Repr, Inhabited

/-- Where an insertion stands among the edits at its offset: a close ends a construct, so it
comes before what starts there; an open starts one. -/
inductive Kind where
  | close | open_ | repl
  deriving Repr, Inhabited, BEq

/-- An edit: the source's characters `a` to `b` replaced by `ps`. An insertion has `a = b`. -/
structure Edit where
  a : Nat
  b : Nat
  ps : List Piece
  kind : Kind := .repl
  /-- The order it was made in. -/
  ord : Nat := 0
  deriving Repr, Inhabited

/-- The source text, its tokens, and the character offset of each token's start and stop. -/
structure Src where
  cs : Array Char
  toks : Array Token
  lineStart : Array Nat

def Src.ofString (src : String) (toks : Array Token) : Src := Id.run do
  let cs := src.toList.toArray
  let mut ls : Array Nat := #[0]
  for i in [0:cs.size] do
    if cs[i]! == '\n' then ls := ls.push (i + 1)
  pure ⟨cs, toks, ls⟩

def Src.off (s : Src) (p : Pos) : Nat :=
  (s.lineStart[p.line - 1]?.getD s.cs.size) + (p.col - 1)

/-- The offset where token `i` starts, and where it stops. -/
def Src.ts (s : Src) (i : Nat) : Nat := s.off (s.toks[i]?.getD default).span.start
def Src.te (s : Src) (i : Nat) : Nat := s.off (s.toks[i]?.getD default).span.stop

def Src.tok (s : Src) (i : Nat) : Tok := (s.toks[i]?.getD default).tok
def Src.line (s : Src) (i : Nat) : Nat := (s.toks[i]?.getD default).span.start.line
def Src.text (s : Src) (a b : Nat) : String := String.ofList (s.cs.extract a b).toList

/-- The offset of the end of the line the offset `o` is on (its `\n`, or the end of the text). -/
def Src.eol (s : Src) (o : Nat) : Nat := Id.run do
  let mut k := o
  while k < s.cs.size && s.cs[k]! != '\n' do k := k + 1
  pure k

/-- Whether the gap between token `i` and the next holds only spaces, no line break or comment. -/
def Src.flatGap (s : Src) (i : Nat) : Bool :=
  (s.cs.extract (s.te i) (s.ts (i + 1))).all (· == ' ')

/-! ### The rewrites -/

def binops : List String :=
  ["+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||", "|>", ">|"]

/-- A token a line may end with and the statement go on (the layout rule of SPEC §82). -/
def endsOpen (t : Tok) : Bool := match t with
  | .sym s => binops.contains s || [",", "->", "=", ":", "<-", "(", "[", "{"].contains s
  | .kw "in" => true
  | _ => false

/-- A token a line may start with and continue the line before (the layout rule of SPEC §82, and
the prefix forms that are also operators, Q10). -/
def startsOpen (t : Tok) : Bool := match t with
  | .sym s => binops.contains s || [".", "&", "|", ")", "]", "}"].contains s
  | .kw "else" | .kw "with" => true
  | .ident "finally" => true
  | _ => false

/-- A token after which a dropped `;` is never missed: it begins a statement plainly. -/
def startsPlain (t : Tok) : Bool := match t with
  | .ident _ | .uident _ | .int _ | .flt _ | .str _ | .life _ => true
  | .kw k => !(["else", "with", "in"].contains k)
  | _ => false

/-- The depth change of a bracket token. -/
def depthOf (t : Tok) : Int := match t with
  | .sym "(" | .sym "[" | .sym "{" => 1
  | .sym ")" | .sym "]" | .sym "}" => -1
  | _ => 0

/-- The index of the token closing the bracket opened at `i` (within `[i, hi)`). -/
def Src.closing (s : Src) (i hi : Nat) : Option Nat := Id.run do
  let mut d : Int := 0
  for k in [i:hi] do
    d := d + depthOf (s.tok k)
    if d == 0 then return some k
  pure none

/-- Whether the tokens `a`…`b-1` are one bracketed group `( … )`. -/
def Src.parened (s : Src) (a b : Nat) : Bool :=
  b > a + 1 && s.tok a == .sym "(" && s.closing a b == some (b - 1)

/-- The indices of the tokens of `[a, b)` at depth 0 for which `p` holds. -/
def Src.atDepth0 (s : Src) (a b : Nat) (p : Tok → Bool) : List Nat := Id.run do
  let mut d : Int := 0
  let mut out : Array Nat := #[]
  for k in [a:b] do
    let t := s.tok k
    if d == 0 && p t then out := out.push k
    d := d + depthOf t
  pure out.toList

/-- The rewriter's state: the edits so far, and the marks (an offset and a form). -/
structure W where
  edits : Array Edit := #[]
  marks : Array (Nat × String) := #[]
  /-- The lends rewritten by a construct already (`let r = &x`). -/
  doneLends : List Nat := []

abbrev RM := StateM W

def emit (e : Edit) : RM Unit :=
  modify fun w => { w with edits := w.edits.push { e with ord := w.edits.size } }

def repl (a b : Nat) (s : String) : RM Unit := emit ⟨a, b, [.lit s], .repl, 0⟩
def openAt (o : Nat) (s : String) : RM Unit := emit ⟨o, o, [.lit s], .open_, 0⟩
def closeAt (o : Nat) (s : String) : RM Unit := emit ⟨o, o, [.lit s], .close, 0⟩
def mark (o : Nat) (form : String) : RM Unit :=
  modify fun w => { w with marks := w.marks.push (o, form) }

/-- Replace token `i` by `s`. -/
def replTok (S : Src) (i : Nat) (s : String) : RM Unit := repl (S.ts i) (S.te i) s

/-- Delete token `i`, with the spaces after it when the next token is on its line. -/
def delTok (S : Src) (i : Nat) : RM Unit :=
  if S.line (i + 1) == S.line i && S.flatGap i then repl (S.ts i) (S.ts (i + 1)) ""
  else repl (S.ts i) (S.te i) ""

/-- `with E₁, E₂` from the `with` at `w` to `e`: `/ E₁ + E₂`. -/
def rowRespell (S : Src) (w e : Nat) : RM Unit := do
  replTok S w "/"
  for k in S.atDepth0 (w + 1) e (· == .sym ",") do replTok S k " +"

/-- A `;` at `i` that ends a statement or a declaration's item: dropped when a new line follows
and the line after it plainly starts a new statement (the layout rule, Q10). -/
def dropSemi (S : Src) (i : Nat) : RM Unit := do
  unless S.tok i == .sym ";" do return
  if S.line (i + 1) > S.line i && startsPlain (S.tok (i + 1)) && !endsOpen (S.tok (i - 1)) then
    repl (S.ts i) (S.te i) ""

/-- The close of a block that wraps the tokens up to `last`: on its own line when the next token
is on a later line (after a comment ending that line), else right after `last`. `ind` is the
indentation the close takes on its own line. -/
def closeAfter (S : Src) (last : Nat) (ind : String) : RM Unit :=
  if S.line (last + 1) > S.line last then closeAt (S.eol (S.te last)) ("\n" ++ ind ++ "}")
  else closeAt (S.te last) " }"

/-- The indentation of the line token `i` is on. -/
def indentOf (S : Src) (i : Nat) : String := Id.run do
  let ls := S.lineStart[S.line i - 1]?.getD 0
  let mut k := ls
  while k < S.cs.size && (S.cs[k]! == ' ' || S.cs[k]! == '\t') do k := k + 1
  pure (S.text ls k)

/-- Whether the body `[a, b)` is several statements, or one that is not an expression: then it is
written as a block. -/
def isStmts (S : Src) (a b : Nat) : Bool :=
  !(S.atDepth0 a b (· == .sym ";")).isEmpty ||
  (match S.tok a, S.tok (a + 1) with
    | .kw "let", _ | .kw "for", _ | .kw "while", _ | .kw "loop", _ | .kw "fun", _ | .kw "Fun", _ => true
    | .life _, .sym ":" => true
    | .ident _, .sym "=" | .ident _, .sym "<-" | .ident _, .sym ":" => true
    | _, _ => false)

/-- A body `= S` (D1, D6, A6): `= e` for one expression, `{ S }` for statements. `eq` is the `=`,
`[eq + 1, e)` the body, `ind` the declaration's indentation. -/
def bodyRespell (S : Src) (eq e : Nat) (ind : String) : RM Unit := do
  if e ≤ eq + 1 then return
  if isStmts S (eq + 1) e then
    replTok S eq "{"
    closeAfter S (e - 1) ind

/-- An arm's or a clause's body `[a, b)` (A7): several statements need a block; a body that is a
block value `{ … }` is parenthesised, since a block there is statements. -/
def armRespell (S : Src) (a b : Nat) : RM Unit := do
  if b ≤ a then return
  if isStmts S a b then
    openAt (S.te (a - 1)) " {"
    if S.line (b - 1) == S.line a then closeAt (S.te (b - 1)) " }"
    else closeAfter S (b - 1) (indentOf S (a - 1))
  else if S.tok a == .sym "{" && S.closing a b == some (b - 1) then
    openAt (S.ts a) "("
    closeAt (S.te (b - 1)) ")"

/-- `A => B` with `A` from `a` and `=>` at `i` (T1, T2): `(A) -> B`. -/
def arrowRespell (S : Src) (a i : Nat) : RM Unit := do
  unless S.parened a i do
    openAt (S.ts a) "("
    closeAt (S.te (i - 1)) ")"
  replTok S i "->"

/-- The top-level components of a call's arguments `[a, b)`: each a range. -/
def argComps (S : Src) (a b : Nat) : List (Nat × Nat) :=
  if S.parened a b then
    let cs := S.atDepth0 (a + 1) (b - 1) (· == .sym ",")
    let starts := (a + 1) :: cs.map (· + 1)
    let stops := cs ++ [b - 1]
    starts.zip stops
  else [(a, b)]

/-! ### Parameter modes (P1–P6, A2) -/

/-- Whether a parameter of type `A` is by value (answers A2): after its aliases are expanded, a
scalar, `bool`, `lit`, `1`, `0`, `never`, a `!` type, or a product or sum of these. `bool` and
`lit` are read as `1 + 1` and `i32 * !(i32 => u8)` already. `fuel` bounds alias expansion. -/
def byValue (tbl : Data.Table) : Nat → VTy → Bool
  | 0, _ => false
  | _ + 1, .unit _ | _ + 1, .zero _ | _ + 1, .int _ _ | _ + 1, .bang _ _ => true
  | f + 1, .tensor _ A B | f + 1, .sum _ A B => byValue tbl f A && byValue tbl f B
  | f + 1, .name _ n => match tbl.abbrevs.reverse.find? (·.name == n) with
    | some ab => ab.tps.isEmpty && ab.lps.isEmpty && byValue tbl f ab.body
    | none => false
  | _, _ => false

/-- The heads of a parameter's type that are written as they are: a borrow former. -/
def borrowHead (t : Tok) : Bool := match t with
  | .kw "imm" | .kw "mut" | .kw "view" | .kw "array_imm" | .kw "array_mut" => true
  | .ident "text" | .ident "text_mut" => true
  | _ => false

/-- The written lifetime parameters `<…>` in `[a, b)`: each binder's name and token range. -/
def binders (S : Src) (a b : Nat) : List (String × Nat × Nat) :=
  if b ≤ a + 2 then [] else
  let cs := S.atDepth0 (a + 1) (b - 1) (· == .sym ",")
  let starts := (a + 1) :: cs.map (· + 1)
  let stops := cs ++ [b - 1]
  (starts.zip stops).filterMap fun (x, y) => match S.tok x with
    | .life l => some (l, x, y)
    | _ => none

/-- A `fn` header's parameters in the new spelling (P1–P6): a fresh shared or mutable borrow is a
mode, `x: T`, `x: array A`, `x: inout T`, `x: inout array A`, its lifetime dropped from `<…>`; an
owned parameter not by value is `x: sink T`; the rest are as written. A lifetime is fresh when the
declaration (`[lv.1, e)`) names it only at its binder, which has no bound, and at this parameter;
a shared or mutable borrow of a by-value type keeps its explicit type, as bare it reads by value
(P5). -/
def fnModes (S : Src) (tbl : Data.Table) (lv : Nat × Nat) (ps : List (Nat × Nat × VTy)) (e : Nat) :
    RM Unit := do
  let bs := binders S lv.1 lv.2
  let uses (l : String) : Nat := ((List.range (e - lv.1)).filter fun k => S.tok (lv.1 + k) == .life l).length
  let mut dropped : List String := []
  for (n, _, A) in ps do
    let t := n + 2
    let fresh := match S.tok (t + 1) with
      | .life l => (bs.any fun (b, x, y) => b == l && y == x + 1) && uses l == 2
      | _ => false
    let base := match A with
      | .imm _ _ B | .mut _ _ B | .arrayImm _ _ B | .arrayMut _ _ B => some B
      | _ => none
    match S.tok t, base, S.tok (t + 1) with
    | .kw k, some B, .life l =>
      if fresh && ["imm", "mut", "array_imm", "array_mut"].contains k &&
          !((k == "imm" || k == "mut") && byValue tbl 16 B) then
        let mode := match k with
          | "imm" => "" | "array_imm" => "array " | "mut" => "inout " | _ => "inout array "
        repl (S.ts t) (S.ts (t + 2)) mode
        dropped := l :: dropped
    | tk, _, _ =>
      unless borrowHead tk || byValue tbl 16 A do openAt (S.ts t) "sink "
  unless dropped.isEmpty do
    let kept := bs.filter fun (b, _, _) => !dropped.contains b
    let txt := if kept.isEmpty then "" else
      "<" ++ ", ".intercalate (kept.map fun (_, x, y) => S.text (S.ts x) (S.te (y - 1))) ++ ">"
    repl (S.ts lv.1) (S.te (lv.2 - 1)) txt

/-- The edits of the events `evs` of a parse of `S`; `sigs` the parameters of each `fn` and `poly`
family the program may call, by name; `tbl` its `data` and `type` table. -/
def rewrite (S : Src) (evs : Array Ev) (sigs : List (String × List VTy)) (tbl : Data.Table) :
    RM Unit := do
  let calls := evs.toList.filterMap fun | .callArgs a b c => some (a, b, c) | _ => none
  -- Each argument of a call, with the callee's parameter type there when it is known.
  let callComps := calls.flatMap fun (a, b, c) =>
    let ps := (c.bind fun f => sigs.lookup f).getD []
    (argComps S a b).zipIdx.map fun (r, i) => (r, ps[i]?)
  -- `fn` headers: their lifetime parameters and parameters, until the header ends.
  let mut lv : Nat × Nat := (0, 0)
  let mut ps : Array (Nat × Nat × VTy) := #[]
  for e in evs do
    match e with
    | .fnLives a b => lv := (a, b); ps := #[]
    | .param n t A => ps := ps.push (n, t, A)
    | .fnHead _ _ _ _ bodyEnd => fnModes S tbl lv ps.toList bodyEnd; ps := #[]
    | .polyFam _ | .opDecl .. => ps := #[]
    | .hParam n _ A =>
      unless borrowHead (S.tok (n + 2)) || byValue tbl 16 A do openAt (S.ts (n + 2)) "sink "
    | _ => pure ()
  let loopSrcs := evs.toList.filterMap fun | .loopSrc a b => some (a, b) | _ => none
  let mut stmts : List (Nat × Nat) := []
  -- P9 first, so that the lend it takes is not rewritten again.
  for e in evs do
    if let .letRef l semi restEnd := e then
      -- `let r = &x;`: `let`, `r`, `=`, `&`, `x`, `;`. A `let r = &mut x` is P7's.
      if S.tok (l + 4) == .kw "mut" then pure ()
      else if S.tok (l + 2) == .sym "=" && S.tok (l + 3) == .sym "&" && semi == l + 5 then
        repl (S.ts l) (S.te semi) s!"borrow imm {S.text (S.ts (l + 4)) (S.te (l + 4))} \{ {S.text (S.ts (l + 1)) (S.te (l + 1))} ->"
        closeAfter S (restEnd - 1) (indentOf S l)
        modify fun w => { w with doneLends := (l + 3) :: w.doneLends }
      else mark (S.ts l) "`let r = &x` (P9)"
  for e in evs do
    match e with
    | .include i => replTok S i "import"
    | .fnHead arrow w rowEnd eq bodyEnd =>
      replTok S arrow ":"
      if let some w := w then
        -- An arrow result with a row is parenthesised: the row is the function's.
        if evs.any (fun | .arrow a _ => a == arrow + 1 | _ => false) then
          openAt (S.ts (arrow + 1)) "("
          closeAt (S.te (w - 1)) ")"
        rowRespell S w rowEnd
      bodyRespell S eq bodyEnd (indentOf S arrow)
    | .mainHead m arrow eq bodyEnd =>
      repl (S.ts m) (S.te arrow) "fn main() :"
      bodyRespell S eq bodyEnd (indentOf S m)
    | .polyFam arrow => replTok S arrow ":"
    | .polyAt eq bodyEnd => bodyRespell S eq bodyEnd (indentOf S eq)
    | .opDecl fn arrow rp =>
      if let some f := fn then delTok S f
      match arrow with
      | some a => replTok S a ":"
      | none => closeAt (S.te rp) " : 1"
    | .declSep i => dropSemi S i
    | .hLent amp =>
      if S.tok (amp + 1) == .kw "mut" && S.tok (amp + 3) == .sym ":" then
        repl (S.ts amp) (S.ts (amp + 2)) ""
        replTok S (amp + 3) ": inout"
      else mark (S.ts amp) "lent handler state (D18)"
    | .hSig a b =>
      unless S.parened a b do
        openAt (S.ts a) "("
        closeAt (S.te (b - 1)) ")"
    | .hRow w e => rowRespell S w e
    | .hEq eq => delTok S eq
    | .clause eq a b =>
      replTok S eq "->"
      unless S.tok a == .sym "{" && S.closing a b == some (b - 1) do
        if isStmts S a b then
          openAt (S.te eq) " {"
          closeAfter S (b - 1) (indentOf S eq)
    | .arrow a i => arrowRespell S a i
    | .rowed w c => rowRespell S w c
    | .seq i => dropSemi S i
    | .stmt a b => stmts := (a, b) :: stmts
    | .bind x arrow asg =>
      -- `let` never assigns: an assignment `x <- M` of a `var` is `x = M`.
      if asg then
        if arrow == x + 1 then replTok S arrow "=" else mark (S.ts x) "an assignment `x : A <- M`"
      else
        openAt (S.ts x) "let "
        replTok S arrow "="
    | .ret i => delTok S i
    | .letMut i => repl (S.ts i) (S.te (i + 1)) "var"
    | .lend a b m =>
      if (← get).doneLends.contains a then pure ()
      else if let some (_, P) := callComps.find? (·.1 == (a, b)) then
        -- A shared lend at a parameter that is no shared borrow (a capability lent, §11) is
        -- `&x`: today's `&mut x` there is the same term (route.md §5).
        let shared := match P with
          | some (.imm ..) | some (.arrayImm ..) | none => true
          | some _ => false
        if m then delTok S (a + 1) else if shared then delTok S a
      else if loopSrcs.contains (a, b) then pure ()
      else if m then delTok S (a + 1)
      else mark (S.ts a) "a shared lend `&x` outside a call (P8)"
    | .arm a b => armRespell S a b
    | .withBlk w nm h₀ h₁ lb rb =>
      let named := match nm with
        | some n => [Piece.lit s!" as {S.text (S.ts n) (S.te n)}"]
        | none => []
      emit ⟨S.ts w, S.te rb, [.lit "handle ", .src (S.ts lb) (S.te rb), .lit " with ",
        .src (S.ts h₀) (S.te (h₁ - 1))] ++ named, .repl, 0⟩
    | _ => pure ()
  -- The layout rule (Q10): a statement broken across lines where a new line would end it is
  -- joined onto one line, or marked when a comment is in the break.
  for (a, b) in stmts.eraseDups do
    let mut d : Int := 0
    for k in [a:b - 1] do
      d := d + depthOf (S.tok k)
      if d == 0 && S.line (k + 1) > S.line k && !endsOpen (S.tok k) && !startsOpen (S.tok (k + 1)) then
        if (S.cs.extract (S.te k) (S.ts (k + 1))).all (fun c => c == ' ' || c == '\n' || c == '\t') then
          repl (S.te k) (S.ts (k + 1)) " "
        else mark (S.ts k) "a statement broken across lines (layout rule)"
  -- `handle` is a reserved word of the new spelling.
  for i in [0:S.toks.size] do
    if S.tok i == .ident "handle" then mark (S.ts i) "`handle` used as a name"

/-- The `--` comments of the gaps between tokens, as `#`. -/
def comments (S : Src) : RM Unit := do
  let mut prev := 0
  for i in [0:S.toks.size] do
    let a := prev
    let b := S.ts i
    let mut k := a
    while k + 1 < b do
      if S.cs[k]! == '-' && S.cs[k + 1]! == '-' then
        repl k (k + 2) "#"
        k := S.eol k
      else k := k + 1
    prev := max prev (S.te i)

/-! ### Rendering -/

/-- The order edits starting at one offset are applied in: closes (inner first), opens (outer
first), then replacements (widest first). -/
def Edit.key (e : Edit) : Nat × Nat × Int :=
  match e.kind with
  | .close => (e.a, 0, e.ord)
  | .open_ => (e.a, 1, -(e.ord : Int))
  | .repl => (e.a, 2, -((e.b - e.a : Nat) : Int))

def keyLt (x y : Nat × Nat × Int) : Bool :=
  x.1 < y.1 || (x.1 == y.1 && (x.2.1 < y.2.1 || (x.2.1 == y.2.1 && x.2.2 < y.2.2)))

/-- The text of the source's characters `[a, b)` with the edits inside it applied, `es` sorted by
`Edit.key`. In a piece (`inner`), a close at its end belongs to the construct around it. `fuel`
bounds the nesting, which is at most the number of edits. -/
def render (S : Src) (es : Array Edit) : Nat → Nat → Nat → Bool → String
  | 0, a, b, _ => S.text a b
  | fuel + 1, a, b, inner => Id.run do
    let mut out := ""
    let mut cur := a
    for e in es do
      if e.a < cur || e.b > b || e.a > b then continue
      if e.a == e.b && inner && e.a == b && e.kind == .close then continue
      out := out ++ S.text cur e.a
      for p in e.ps do
        match p with
        | .lit s => out := out ++ s
        | .src x y => out := out ++ render S es fuel x y true
      cur := e.b
    out ++ S.text cur b

/-- The parameter types of each `fn` and `poly` family the events declare. -/
def sigsOf (evs : Array Ev) : List (String × List VTy) :=
  evs.toList.filterMap fun | .sig f ps => some (f, ps) | _ => none

/-- The signatures of the library modules `ms` and those they include, each read once (`seen`). -/
def modSigs (lib : String → Option String) : Nat → List String → List String → List (String × List VTy)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | k + 1, m :: ms, seen =>
    if seen.contains m then modSigs lib k ms seen else
    match lib m with
    | none => modSigs lib k ms (m :: seen)
    | some msrc =>
      let own := match runPS (fun n => decls n n []) msrc true (dataOf lib msrc) (file := m)
          (respell := true) with
        | .ok (_, st) => sigsOf st.rs.evs
        | .error _ => []
      let incs := match lex msrc m with
        | .ok ts => includesIn ts
        | .error _ => []
      modSigs lib k (incs ++ ms) (m :: seen) ++ own

/-- The new spelling of the program `src` (today's), `lib` giving the library modules: its text,
with the pragma first, and each mark's line and form.  `[spec §82]` -/
def respell (src : String) (lib : String → Option String := fun _ => none) :
    Except Error (String × List (Nat × String)) := do
  let toks ← lex src
  let (_, st) ← runPS (fun n => decls n n []) src true (dataOf lib src) (respell := true)
  let S := Src.ofString src toks
  let sigs := sigsOf st.rs.evs ++ modSigs lib 64 ("prelude" :: includesIn toks) []
  let ((), w) := (do comments S; rewrite S st.rs.evs sigs st.data : RM Unit).run {}
  let marks := w.marks.toList
  let ((), w) := (do
      for (o, f) in marks do closeAt (S.eol o) s!"  #?respell: {f}" : RM Unit).run w
  let es := w.edits.qsort fun x y => keyLt x.key y.key
  let lineOf (o : Nat) : Nat := (S.lineStart.toList.filter (· ≤ o)).length
  pure (pragma ++ "\n" ++ render S es (es.size + 1) 0 S.cs.size false,
    marks.map fun (o, f) => (lineOf o, f))

end Frontend.Respell
