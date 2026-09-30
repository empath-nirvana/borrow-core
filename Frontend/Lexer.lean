import Frontend.Syntax
/-!
# Frontend — Lexer

Tokens of syntax-core §2: lower-case names, upper-case names, lifetime variables `'x`,
integer literals (decimal and `0x` hexadecimal), keywords and symbols, with `--` comments
skipped. Every Unicode spelling of the table in §2 is read as its ASCII spelling, so the parser
sees one spelling of each token.

**Termination.** `lexGo` recurses on a fuel argument that starts at the length of the input
plus one. Every step consumes at least one character, so the fuel is never exhausted before
the input is; running out is reported as an error rather than assumed impossible.
-/

namespace Frontend

/-- The kinds of token. Keywords and symbols are held in their ASCII spelling. -/
inductive Tok where
  /-- A lower-case name `[a-z_][A-Za-z0-9_']*` that is not a keyword. -/
  | ident (s : String)
  /-- An upper-case name `[A-Z][A-Za-z0-9_]*` that is not a keyword. -/
  | uident (s : String)
  /-- A lifetime variable `'x`, held without the `'`. -/
  | life (s : String)
  | int (n : Nat)
  | kw (s : String)
  | sym (s : String)
  | eof
  deriving DecidableEq, Repr, Inhabited

/-- A token, its span, and whether whitespace or a comment separates it from the token
    before it. -/
structure Token where
  tok : Tok
  span : Span
  spaced : Bool
  deriving Repr, Inhabited

/-- An error with the span it is reported at. -/
structure Error where
  span : Span
  msg : String
  deriving Repr

def Error.render (e : Error) : String := s!"{e.span.start.render}: {e.msg}"

/-- The reserved lower-case words. -/
def keywords : List String :=
  [ -- declarations
    "type", "shape", "def", "extern", "main", "total", "div", "fn", "include",
    -- terms
    "return", "force", "fun", "let", "linear", "case", "match", "borrow", "modify", "inl", "inr",
    "if", "else", "gen", "yield", "while", "break", "clone",
    "thunk", "thunkv", "unbang",
    "boxed", "unbox", "roll", "unroll", "run", "absurd",
    "nu_in", "nu_out", "delay_in", "delay_out", "stream_in", "stream_out",
    -- types, lifetimes, shapes
    "ref", "imm", "mut", "box", "unk", "i32", "i64", "u8", "input", "output", "mu", "all", "forall", "top", "dom",
    "block", "val", "fam", "view", "nu", "delay", "loop", "stream", "str", "iter", "leaf",
    "for", "in",
    "node", "array", "array_imm", "array_mut",
    -- constants and derived forms
    "alloc", "free", "swap", "copy", "copy_bang", "forget_imm", "forget_mut", "forget_unk",
    "forget_bang", "withbor1", "withbor2", "withbor3", "withload", "withswap",
    "fold_imm", "fold_own", "fold_reuse", "fixd", "unfold_s", "unfold", "host",
    "alloc_s", "free_s", "withbor_s_mut", "withbor_s_imm", "withbor_f2_mut", "withbor_f2_imm",
    "shorten_mut", "shorten_imm", "array_new", "array_free", "array_size", "array_replace",
    "slice_borrow_mut", "slice_borrow_imm", "slice_get_mut", "slice_len_mut", "count_fold", "count_try",
    "slice_split_imm", "slice_split_mut", "slice_empty_imm", "slice_empty_mut",
    "slice_replace_mut", "slice_swap_mut",
    "array_len", "array_get", "array_copy", "array_forget" ]

/-- The reserved upper-case words. -/
def upperKeywords : List String := ["U", "F", "Fun"]

def Tok.describe : Tok → String
  | .ident s => s!"name `{s}`"
  | .uident s => s!"name `{s}`"
  | .life s => s!"lifetime `'{s}`"
  | .int n => s!"integer `{n}`"
  | .kw s => s!"`{s}`"
  | .sym s => s!"`{s}`"
  | .eof => "end of input"

private def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
private def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def isHex (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
private def hexVal (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- The longest prefix of `cs` whose characters satisfy `p`, and the rest. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r => if p c then let (a, b) := spanChars p r; (c :: a, b) else ([], c :: r)

/-- Two-character symbols, in their ASCII spelling. -/
private def twoCharSyms : List (Char × Char × String) :=
  [('-', 'o', "-o"), ('-', '>', "->"), ('<', '-', "<-"), (':', '>', ":>"), ('=', '>', "=>"),
   ('/', '\\', "/\\"), ('\\', '/', "\\/"), ('=', '=', "=="), ('!', '=', "!="), ('<', '=', "<="),
   ('>', '=', ">="), ('&', '&', "&&"), ('|', '|', "||")]

/-- One-character symbols. -/
private def oneCharSyms : List Char :=
  ['(', ')', '[', ']', '{', '}', ',', ';', ':', '.', '=', '|', '<', '>', '*', '+', '&', '!', '-']

/-- The Unicode spellings of syntax-core §2 that are one character, with their ASCII token.
    `⊓Δ` (`dom`) and `Imm̲` (`view`) are two- and four-character spellings, handled in `lexGo`. -/
private def unicodeToks : List (Char × Tok) :=
  [('⊗', .sym "*"), ('⊕', .sym "+"), ('⊸', .sym "-o"), ('⊤', .kw "top"), ('∀', .kw "forall"),
   ('⊏', .sym "<"), ('⊓', .sym "/\\"), ('⊔', .sym "\\/"), ('μ', .kw "mu"), ('λ', .kw "fun"),
   ('Λ', .kw "Fun")]

private def advance (p : Pos) (n : Nat) : Pos := ⟨p.line, p.col + n⟩

private def natOfDigits (base : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * base + hexVal c) 0

/-- The byte of an escaped byte literal `b'\e'`: `\n`, `\t`, `\r`, `\0`, `\\`, `\'`. -/
def byteEscape : Char → Option Nat
  | 'n' => some 10 | 't' => some 9 | 'r' => some 13 | '0' => some 0
  | '\\' => some 92 | '\'' => some 39 | _ => none

/-- The lexer loop. `pos` is the position of the head of `cs`; `spaced` records whether
    whitespace was skipped since the last token. A byte literal `b'c'` is read as the tokens of
    `u8[n]`, `n` the ASCII code of `c` (strings S1, `docs/decisions.md` 43). -/
def lexGo : Nat → List Char → Pos → Bool → Array Token → Except Error (Array Token)
  | 0, _, pos, _, _ => .error ⟨⟨pos, pos⟩, "lexer ran out of fuel"⟩
  | fuel + 1, cs, pos, spaced, acc =>
    let push (t : Tok) (n : Nat) (rest : List Char) :=
      let stop := advance pos n
      lexGo fuel rest stop false (acc.push ⟨t, ⟨pos, stop⟩, spaced⟩)
    match cs with
    | [] => .ok (acc.push ⟨.eof, ⟨pos, pos⟩, spaced⟩)
    | '\n' :: r => lexGo fuel r ⟨pos.line + 1, 1⟩ true acc
    | '-' :: '-' :: r =>
      let (skipped, rest) := spanChars (· ≠ '\n') r
      lexGo fuel rest (advance pos (skipped.length + 2)) true acc
    | '⊓' :: 'Δ' :: r => push (.kw "dom") 2 r
    | 'b' :: '\'' :: '\\' :: e :: '\'' :: r =>
      match byteEscape e with
      | some n =>
        let stop := advance pos 5
        let sp : Span := ⟨pos, stop⟩
        lexGo fuel r stop false (acc.push ⟨.kw "u8", sp, spaced⟩ |>.push ⟨.sym "[", sp, false⟩
          |>.push ⟨.int n, sp, false⟩ |>.push ⟨.sym "]", sp, false⟩)
      | none => .error ⟨⟨pos, advance pos 5⟩, s!"unknown escape `\\{e}` in a byte literal"⟩
    | 'b' :: '\'' :: c :: '\'' :: r =>
      if c.toNat < 128 && c.toNat ≥ 32 && c != '\\' && c != '\'' then
        let stop := advance pos 4
        let sp : Span := ⟨pos, stop⟩
        lexGo fuel r stop false (acc.push ⟨.kw "u8", sp, spaced⟩ |>.push ⟨.sym "[", sp, false⟩
          |>.push ⟨.int c.toNat, sp, false⟩ |>.push ⟨.sym "]", sp, false⟩)
      else .error ⟨⟨pos, advance pos 4⟩, "a byte literal `b'c'` holds a printable ASCII character"⟩
    | 'I' :: 'm' :: 'm' :: '̲' :: r => push (.kw "view") 4 r
    | c :: r =>
      if c == ' ' || c == '\t' || c == '\r' then lexGo fuel r (advance pos 1) true acc
      else match r, twoCharSyms.find? (fun (a, b, _) => a == c && r.head? == some b) with
      | _ :: r', some (_, _, s) => push (.sym s) 2 r'
      | _, _ =>
      if oneCharSyms.contains c then push (.sym c.toString) 1 r
      else if let some (_, t) := unicodeToks.find? (·.1 == c) then push t 1 r
      else if c == '\'' then
        match r with
        | d :: r' =>
          if isLower d then
            let (rest, r'') := spanChars (fun e => isLower e || isDigit e || e == '_') r'
            push (.life (String.ofList (d :: rest))) (rest.length + 2) r''
          else .error ⟨⟨pos, advance pos 1⟩,
            "a lifetime variable is `'` followed by a lower-case letter"⟩
        | [] => .error ⟨⟨pos, advance pos 1⟩,
            "a lifetime variable is `'` followed by a lower-case letter"⟩
      else if isLower c || c == '_' then
        let (rest, r') :=
          spanChars (fun e => isLower e || isUpper e || isDigit e || e == '_' || e == '\'') r
        let s := String.ofList (c :: rest)
        push (if keywords.contains s then .kw s else .ident s) (rest.length + 1) r'
      else if isUpper c then
        let (rest, r') := spanChars (fun e => isLower e || isUpper e || isDigit e || e == '_') r
        let s := String.ofList (c :: rest)
        push (if upperKeywords.contains s then .kw s else .uident s) (rest.length + 1) r'
      else if c == '0' && (r.head? == some 'x' || r.head? == some 'X') then
        let (ds, r') := spanChars isHex (r.drop 1)
        if ds.isEmpty then .error ⟨⟨pos, advance pos 2⟩, "expected hexadecimal digits after `0x`"⟩
        else push (.int (natOfDigits 16 ds)) (ds.length + 2) r'
      else if isDigit c then
        let (ds, r') := spanChars isDigit r
        push (.int (natOfDigits 10 (c :: ds))) (ds.length + 1) r'
      else .error ⟨⟨pos, advance pos 1⟩, s!"unexpected character `{c}`"⟩

/-- The tokens of a source text, ending with `eof`. -/
def lex (src : String) : Except Error (Array Token) :=
  let cs := src.toList
  lexGo (cs.length + 1) cs ⟨1, 1⟩ true #[]

end Frontend
