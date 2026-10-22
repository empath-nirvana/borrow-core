import Frontend.Consts
/-!
# Frontend — Printer

Prints the AST back to source text in the ASCII spelling. It parenthesizes by the precedence
levels of syntax-core §4 and §6.5, so that parsing the output gives the AST back up to spans:
`(parse (print t)).strip = t.strip`. The corpus runner (`bcc parse`) checks this on every file
it parses, and `Frontend/Tests.lean` checks it on small cases.

Levels, loosest first. Types: 0 binders and arrows, 1 `&`, 2 `+`, 3 `*`, 4 prefix formers,
5 atoms. Terms: 0 binding forms, 1 prefix keywords, 2 spines, 3 atoms. A node printed where a
tighter level is required is parenthesized.
-/

namespace Frontend

def paren (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

def Life.level : Life → Nat
  | .join .. => 0
  | .meet .. => 1
  | _ => 2

def Life.pp (l : Life) (lvl : Nat := 0) : String :=
  paren (l.level < lvl) <| match l with
    | .var _ x => "'" ++ x
    | .top _ => "top"
    | .dom _ => "dom"
    | .meet _ a b => a.pp 2 ++ " /\\ " ++ b.pp 1
    | .join _ a b => a.pp 1 ++ " \\/ " ++ b.pp 0

def Mode.pp : Mode → String
  | .mut => "mut"
  | .imm => "imm"

def VTy.level : VTy → Nat
  | .mu .. | .all .. | .lolli .. => 0
  | .sum .. => 2
  | .tensor .. => 3
  | .thunk .. | .ref .. | .imm .. | .mut .. | .box .. | .bang .. | .block .. | .val ..
  | .fam .. | .view .. | .array .. | .arrayImm .. | .arrayMut .. | .sized .. => 4
  | _ => 5

def CTy.level : CTy → Nat
  | .arr .. | .all .. | .nu .. => 0
  | .amp .. => 1
  | .ret .. | .delay .. | .stream .. | .iter .. | .loop .. | .pull .. | .eff .. => 4
  | .top .. | .name .. => 5

def widthName : BoCa.Width → String
  | .w32 => "i32"
  | .w64 => "i64"
  | .w8 => "u8"
  | .f32 => "f32"
  | .f64 => "f64"

/-- A printed shape as a shape atom: a name as it is, anything else parenthesized. -/
def ppShapeAtom (σ : Shape) (printed : String) : String :=
  match σ with
  | .name _ n => n
  | _ => "(" ++ printed ++ ")"

/-- `N[A, …]<'a, …>` from its printed parts. -/
def ppApp (h : String) (ts ls : List String) : String :=
  h ++ (if ts.isEmpty then "" else "[" ++ ", ".intercalate ts ++ "]") ++
    (if ls.isEmpty then "" else "<" ++ ", ".intercalate ls ++ ">")

mutual
def VTy.pp (A : VTy) (lvl : Nat := 0) : String :=
  paren (A.level < lvl) <| match A with
    | .unit _ => "1"
    | .zero _ => "0"
    | .tensor _ A B => A.pp 4 ++ " * " ++ B.pp 3
    | .sum _ A B => A.pp 3 ++ " + " ++ B.pp 2
    | .thunk _ C => "U " ++ C.pp 4
    | .ref _ A => "ref " ++ A.pp 4
    | .imm _ a A => "imm " ++ a.pp 2 ++ " " ++ A.pp 4
    | .mut _ a A => "mut " ++ a.pp 2 ++ " " ++ A.pp 4
    | .box _ a A => "box " ++ a.pp 2 ++ " " ++ A.pp 4
    | .bang _ A => "!" ++ A.pp 4
    | .unk _ => "unk"
    | .int _ w => widthName w
    | .handle _ k => k.name
    | .mu _ X A => "mu " ++ X.name ++ ". " ++ A.pp 0
    | .name _ n => n
    | .lolli _ A B => A.pp 1 ++ " => " ++ B.pp 0
    | .all _ x b A => "all '" ++ x.name ++ " < " ++ b.pp ++ ". " ++ A.pp 0
    | .block _ σ => "block " ++ ppShapeAtom σ σ.pp
    | .val _ σ => "val " ++ ppShapeAtom σ σ.pp
    | .fam _ m a σ => "fam " ++ m.pp ++ " " ++ a.pp 2 ++ " " ++ ppShapeAtom σ σ.pp
    | .view _ a A => "view " ++ a.pp 2 ++ " " ++ A.pp 4
    | .array _ A => "array " ++ A.pp 4
    | .arrayImm _ a A => "array_imm " ++ a.pp 2 ++ " " ++ A.pp 4
    | .arrayMut _ a A => "array_mut " ++ a.pp 2 ++ " " ++ A.pp 4
    | .sized _ D S A => "sized " ++ D.pp 5 ++ " " ++ S.pp 5 ++ " " ++ A.pp 5
    | .app _ G B =>
      let (h, ts, ls) := G.ppArgs
      ppApp h (ts ++ [B.pp 0]) ls
    | .lapp _ G a =>
      let (h, ts, ls) := G.ppArgs
      ppApp h ts (ls ++ [a.pp 0])
    | .rowed _ F r =>
      let (_, ts, _) := r.ppArgs
      "(" ++ F.pp 0 ++ " with " ++ ", ".intercalate ts ++ ")"

/-- `N[A, …]<'a, …>`: the head name, the printed type arguments and lifetime arguments. -/
def VTy.ppArgs : VTy → String × List String × List String
  | .app _ G A => let (h, ts, ls) := G.ppArgs; (h, ts ++ [A.pp 0], ls)
  | .lapp _ G a => let (h, ts, ls) := G.ppArgs; (h, ts, ls ++ [a.pp 0])
  | .name _ n => (n, [], [])
  | _ => ("_", [], [])

def CTy.pp (C : CTy) (lvl : Nat := 0) : String :=
  paren (C.level < lvl) <| match C with
    | .ret _ A => "F " ++ A.pp 4
    | .arr _ A C => A.pp 1 ++ " -o " ++ C.pp 0
    | .amp _ C D => C.pp 2 ++ " & " ++ D.pp 1
    | .top _ => "top"
    | .all _ x b C => "forall '" ++ x.name ++ " < " ++ b.pp ++ ". " ++ C.pp 0
    | .nu _ X C => "nu " ++ X.name ++ ". " ++ C.pp 0
    | .name _ n => n
    | .delay _ A => "delay " ++ A.pp 4
    | .stream _ A => "stream " ++ A.pp 4
    | .iter _ A R R' => "iter " ++ A.pp 5 ++ " " ++ R.pp 5 ++ " " ++ R'.pp 5
    | .loop _ A B => "loop " ++ A.pp 5 ++ " " ++ B.pp 5
    | .pull _ A B R => "pull " ++ A.pp 5 ++ " " ++ B.pp 5 ++ " " ++ R.pp 5
    | .eff _ .nil A => "F " ++ A.pp 4
    | .eff _ r A => "F[" ++ r.pp ++ "] " ++ A.pp 4

/-- A row's entries, `n.i q A ~> B, …`, without the brackets. -/
def Row.pp : Row → String
  | .nil => ""
  | .cons n i q A B .nil => s!"{n}.{i} {q.str} " ++ A.pp ++ " ~> " ++ B.pp
  | .cons n i q A B r => s!"{n}.{i} {q.str} " ++ A.pp ++ " ~> " ++ B.pp ++ ", " ++ r.pp

def Shape.pp : Shape → String
  | .leaf _ A => "leaf " ++ A.pp 4
  | .node _ σ τ => "node " ++ ppShapeAtom σ σ.pp ++ " " ++ ppShapeAtom τ τ.pp
  | .name _ n => n
end

def Arg.pp : Arg → String
  | .ty A => A.pp
  | .cty C => C.pp
  | .life a => a.pp
  | .binder x => "'" ++ x.name
  | .shape σ => σ.pp
  | .nat n => toString n
  | .op o => hostOpName o
  | .row r => "[" ++ r.pp ++ "]"

def Const.pp (c : Const) : String :=
  let (k, as) := c.toArgs
  if as.isEmpty then k.str else k.str ++ "[" ++ ", ".intercalate (as.map Arg.pp) ++ "]"

/-- A closure `{ x -> M }` of the surface: its binder's type is a hole. -/
def isHole : VTy → Bool
  | .name _ "_" => true
  | _ => false

def Val.level : Val → Nat
  | .mark _ _ V => V.level
  | .thunkv _ (.lam _ _ A _) | .bangThunkv _ (.lam _ _ A _) => if isHole A then 2 else 0
  | .app _ (.sugar _ (.op _)) _ => 3
  -- `alloc(e)`, `clone(x)`: an application, parenthesized as an argument.
  | .app _ (.sugar _ (.call _)) _ => 2
  | .app _ (.sugar _ .deref) _ => 2
  | .app _ (.sugar _ (.field ..)) _ | .app _ (.sugar _ (.update ..)) _ => 3
  | .app _ (.sugar _ .retE) _ | .app _ (.sugar _ (.forSite _)) _ | .app _ (.sugar _ (.pullSite _)) _ => 1
  | .app _ (.sugar _ (.writes _)) _ => 1
  | .app _ (.sugar _ .brace) _
  | .app _ (.app _ (.sugar _ (.borrow ..)) _) _ => 2
  | .thunk .. | .thunkv .. | .bangThunk .. | .bangThunkv .. => 0
  | .inl .. | .inr .. | .roll .. | .unroll .. | .unbang .. | .unbox .. | .boxed .. | .run ..
  | .shorten .. => 1
  | .app .. | .inst .. => 2
  | _ => 3

def Comp.level : Comp → Nat
  | .bind .. | .letUnit .. | .letPair .. | .lam .. | .lamL .. | .loop .. => 0
  | .unwind .. => 0
  | .ret .. | .absurd .. | .nuIn .. | .nuOut .. | .perform .. | .abort .. | .handle .. => 1
  | .withbor2r .. => 1
  | .app .. | .proj .. | .inst .. => 2
  | _ => 3

/-- `linear ` before a `linear` binder. -/
def linKw (lin : Bool) : String := if lin then "linear " else ""

/-- A newline followed by `k` spaces. -/
def nl (k : Nat) : String := "\n" ++ "".pushn ' ' k

/-- A loop's label as written before it, `'ℓ: `, or nothing. -/
def lbl : Option Ident → String
  | some ℓ => "'" ++ ℓ.name ++ ": "
  | none => ""

/-- A string literal: printable ASCII as itself, the escapes `\n`, `\t`, `\r`, `\0`, `\\` and
`\"`, and any other byte as `\xNN`. The lexer reads it back to the same bytes. -/
def strLit (bs : List Nat) : String :=
  let hex (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  "\"" ++ String.join (bs.map fun b =>
    if b == 10 then "\\n" else if b == 9 then "\\t" else if b == 13 then "\\r"
    else if b == 0 then "\\0" else if b == 92 then "\\\\" else if b == 34 then "\\\""
    else if 32 ≤ b && b < 127 then (Char.ofNat b).toString
    else "\\x" ++ (hex (b / 16 % 16)).toString ++ (hex (b % 16)).toString) ++ "\""

mutual
/-- A value-judged expression at level `lvl`, indented by `k` after each line break. -/
def Val.pp (V : Val) (lvl : Nat := 0) (k : Nat := 0) : String :=
  paren (V.level < lvl) <| match V with
    | .var _ x => x
    -- `clone(x)` prints as the variable it checks as: the printed core is checked without the
    -- check of implicit copies (`run_io`'s wrapper, `Frontend/Check/Externs.lean`).
    | .clone _ x => x
    | .defApp _ n As => n ++ "[" ++ ", ".intercalate (As.map (VTy.pp · 0)) ++ "]"
    | .unit _ => "()"
    | .pair _ V W => "(" ++ V.pp 0 k ++ ", " ++ W.pp 0 k ++ ")"
    | .inl _ V => "inl " ++ V.pp 1 k
    | .inr _ V => "inr " ++ V.pp 1 k
    | .thunkv _ (.lam _ x A M) =>
      if isHole A then "{ " ++ x.name ++ " -> " ++ M.pp 0 (k + 2) ++ " }"
      else "thunkv fun (" ++ x.name ++ " : " ++ A.pp ++ ") ->" ++ nl (k + 4) ++ M.pp 0 (k + 4)
    | .bangThunkv _ (.lam _ x A M) =>
      if isHole A then "!{ " ++ x.name ++ " -> " ++ M.pp 0 (k + 2) ++ " }"
      else "!thunkv fun (" ++ x.name ++ " : " ++ A.pp ++ ") ->" ++ nl (k + 4) ++ M.pp 0 (k + 4)
    | .app _ (.sugar _ (.op o)) (.pair _ a b) => "(" ++ a.pp 2 k ++ " " ++ o.str ++ " " ++ b.pp 2 k ++ ")"
    | .app _ (.sugar _ (.call c)) W => c ++ "(" ++ W.pp 0 k ++ ")"
    | .app _ (.sugar _ .count) (.pair _ a b) => "(" ++ a.pp 2 k ++ ".." ++ b.pp 2 k ++ ")"
    | .app _ (.sugar _ .pipe) (.pair _ a s) => "(" ++ a.pp 1 k ++ " |> " ++ s.pp 2 k ++ ")"
    | .app _ (.sugar _ .deref) V => "*" ++ V.pp 3 k
    | .app _ (.sugar _ (.field f _)) V => "(" ++ V.pp 0 k ++ ")." ++ f
    | .app _ (.sugar _ (.update f _)) (.pair _ r e) => "(" ++ r.pp 0 k ++ ").{" ++ f ++ " = " ++ e.pp 0 k ++ "}"
    | .app _ (.sugar _ .retE) V => "return " ++ V.pp 1 k
    | .app _ (.sugar _ (.writes xs)) V => "writes(" ++ ", ".intercalate xs ++ ") " ++ V.pp 1 k
    | .app _ (.sugar _ (.forSite i)) V => s!"for_site[{i.n}] " ++ V.pp 1 k
    | .app _ (.sugar _ (.pullSite i)) V => s!"pull_site[{i.n}] " ++ V.pp 1 k
    | .app _ (.sugar _ .brace) (.thunk _ M) => "{ " ++ M.pp 0 (k + 2) ++ " }"
    | .app _ (.sugar _ .brace) (.bangThunk _ M) => "!{ " ++ M.pp 0 (k + 2) ++ " }"
    | .app _ (.app _ (.sugar _ (.borrow bk x)) P) (.thunkv _ (.lam _ b _ M)) =>
      let kw := match bk with
        | .imm => "borrow imm " | .mut | .famMut => "borrow mut " | .modify => "modify "
      let lt := if x == "" then "" else "'" ++ x ++ ", "
      kw ++ P.pp 3 k ++ " { " ++ lt ++ b.name ++ " ->" ++ nl (k + 2) ++ M.pp 0 (k + 2) ++ " }"
    | .app _ (.app _ (.sugar _ (.handle h x As nm)) P) (.thunkv _ (.lam _ b _ M)) =>
      "with " ++ (match nm with | some n => n ++ " = " | none => "") ++ h ++ (if As.isEmpty then "" else "[" ++ ", ".intercalate (As.map (VTy.pp · 0)) ++ "]") ++
        "(" ++ P.pp 0 k ++ ") { '" ++ x ++ ", " ++ b.name ++ " ->" ++ nl (k + 2) ++
        M.pp 0 (k + 2) ++ " }"
    | .thunk _ M => "thunk " ++ M.pp 0 (k + 2)
    | .thunkv _ M => "thunkv " ++ M.pp 0 (k + 2)
    | .bangThunk _ M => "!thunk " ++ M.pp 0 (k + 2)
    | .bangThunkv _ M => "!thunkv " ++ M.pp 0 (k + 2)
    | .unbang _ V => "unbang " ++ V.pp 1 k
    | .boxed _ a V => "boxed[" ++ a.pp ++ "] " ++ V.pp 1 k
    | .unbox _ V => "unbox " ++ V.pp 1 k
    | .sub _ V a => "(" ++ V.pp 1 k ++ " :> " ++ a.pp ++ ")"
    | .roll _ V => "roll " ++ V.pp 1 k
    | .unroll _ V => "unroll " ++ V.pp 1 k
    | .run _ M => "run " ++ M.pp 1 k
    | .app _ V W => V.pp 2 k ++ " " ++ W.pp 3 k
    | .inst _ V a => V.pp 2 k ++ " [" ++ a.pp ++ "]"
    | .ascribe _ V A => "(" ++ V.pp 1 k ++ " : " ++ A.pp ++ ")"
    | .const _ c => c.pp
    | .shorten _ m σ a V =>
      "shorten_" ++ m.pp ++ "[" ++ σ.pp ++ ", " ++ a.pp ++ "] " ++ V.pp 1 k
    | .lend _ x m => (if m == .mut then "&mut " else "&") ++ x.name
    | .sugar _ (.lit n) => toString n
    | .sugar _ (.flit m e) => s!"{m}e{e}"
    | .sugar _ (.str bs) => strLit bs
    | .sugar _ .brk => "break"
    | .sugar _ .cont => "continue"
    | .sugar _ (.named n op) => n ++ "." ++ op
    | .sugar _ s => s!"<{reprStr s}>"
    -- A marked scheme prints as the value it marks: the mark is the checker's, not the source's.
    | .mark _ _ V => V.pp 0 k

/-- A computation at level `lvl`, indented by `k` after each line break. -/
def Comp.pp (M : Comp) (lvl : Nat := 0) (k : Nat := 0) : String :=
  paren (M.level < lvl) <| match M with
    | .ret _ V => "return " ++ V.pp 1 k
    | .bind _ x none M N lin => linKw lin ++ x.name ++ " <- " ++ M.pp 1 (k + 2) ++ ";" ++ nl k ++ N.pp 0 k
    | .bind _ x (some A) M N lin =>
      linKw lin ++ x.name ++ " : " ++ A.pp ++ " <- " ++ M.pp 1 (k + 2) ++ ";" ++ nl k ++ N.pp 0 k
    | .unwind _ x A M D N =>
      x.name ++ (match A with | some A => " : " ++ A.pp | none => "") ++ " <- " ++ M.pp 1 (k + 2) ++
        " unwind (" ++ D.pp 0 (k + 2) ++ ");" ++ nl k ++ N.pp 0 k
    | .perform _ n i V => s!"perform[{n}.{i}] " ++ V.pp 1 k
    | .abort _ n i V => s!"abort[{n}.{i}] " ++ V.pp 1 k
    | .handle _ n _ hr hc M =>
      s!"handle_with[{n}](" ++ hr.pp 0 (k + 2) ++ ", " ++ hc.pp 0 (k + 2) ++ ") " ++ M.pp 1 k
    | .withbor2r _ x b A B r p m M =>
      let as := (Const.withbor2U x b A B r).toArgs.2
      "withbor2r[" ++ ", ".intercalate (as.map Arg.pp) ++ s!"]({p.name}, {m.name}) " ++ M.pp 1 k
    | .force _ x => "force " ++ x.name
    | .lam _ x A M => "fun (" ++ x.name ++ " : " ++ A.pp ++ ") ->" ++ nl (k + 2) ++ M.pp 0 (k + 2)
    | .app _ M x => M.pp 2 k ++ " " ++ x.name
    | .with_ _ M N => "< " ++ M.pp 0 (k + 2) ++ "," ++ nl (k + 2) ++ N.pp 0 (k + 2) ++ " >"
    | .proj _ i M => M.pp 2 k ++ (if i then ".1" else ".2")
    | .top _ => "<>"
    | .letUnit _ V M => "let () = " ++ V.pp 1 k ++ ";" ++ nl k ++ M.pp 0 k
    | .letPair _ x y V M =>
      "let (" ++ x.name ++ ", " ++ y.name ++ ") = " ++ V.pp 1 k ++ ";" ++ nl k ++ M.pp 0 k
    | .case _ V x M y N =>
      "case " ++ V.pp 1 k ++ " {" ++ nl (k + 2) ++ "inl " ++ x.name ++ " -> " ++ M.pp 0 (k + 4) ++
        nl k ++ "| inr " ++ y.name ++ " -> " ++ N.pp 0 (k + 4) ++ nl k ++ "}"
    | .absurd _ V => "absurd " ++ V.pp 1 k
    | .lamL _ x b M => "Fun '" ++ x.name ++ " < " ++ b.pp ++ "." ++ nl (k + 2) ++ M.pp 0 (k + 2)
    | .inst _ M a => M.pp 2 k ++ " [" ++ a.pp ++ "]"
    | .nuIn _ M => "nu_in " ++ M.pp 1 k
    | .nuOut _ M => "nu_out " ++ M.pp 1 k
    | .ascribe _ M C => "(" ++ M.pp 1 k ++ " : " ++ C.pp ++ ")"
    | .loop _ ℓ .forever _ M N =>
      lbl ℓ ++ "loop {" ++ nl (k + 2) ++ M.pp 0 (k + 2) ++ nl k ++ "};" ++ nl k ++ N.pp 0 k
    | .loop _ ℓ .while_ c M N =>
      lbl ℓ ++ "while " ++ c.pp 1 k ++ " {" ++ nl (k + 2) ++
        M.pp 0 (k + 2) ++ nl k ++ "};" ++ nl k ++ N.pp 0 k
    | .loop _ ℓ (.each x) V M (.bind _ r A (.ret _ (.app _ (.sugar _ .forRes) (.thunk _ d))) N _) =>
      "let " ++ r.name ++ (match A with | some A => " : " ++ A.pp | none => "") ++ " = " ++
        lbl ℓ ++ "for " ++ x.name ++ " in " ++ V.pp 1 k ++ " {" ++ nl (k + 2) ++
        M.pp 0 (k + 2) ++ nl k ++ "} else {" ++ nl (k + 2) ++ d.pp 0 (k + 2) ++ nl k ++ "};" ++
        nl k ++ N.pp 0 k
    | .loop _ ℓ (.each x) V M (.bind _ r A (.ret _ (.sugar _ .forRes)) N _) =>
      "let " ++ r.name ++ (match A with | some A => " : " ++ A.pp | none => "") ++ " = " ++
        lbl ℓ ++ "for " ++ x.name ++ " in " ++ V.pp 1 k ++ " {" ++ nl (k + 2) ++
        M.pp 0 (k + 2) ++ nl k ++ "};" ++ nl k ++ N.pp 0 k
    | .loop _ ℓ (.each x) V M N =>
      lbl ℓ ++ "for " ++ x.name ++ " in " ++ V.pp 1 k ++ " {" ++ nl (k + 2) ++
        M.pp 0 (k + 2) ++ nl k ++ "};" ++ nl k ++ N.pp 0 k
end

/-- The printed form of a `poly` declaration (`Decl.poly`): `poly def f[T] : A = V` for a family,
`poly def f[P, …]<'h, …> at H = V` for a case.  `[spec §36]` -/
def Decl.ppPoly (n : Ident) (tps lps : List Ident) (H : Option VTy) (A : VTy) (V : Val) : String :=
  let params := if tps.isEmpty then "" else "[" ++ ", ".intercalate (tps.map (·.name)) ++ "]"
  let lives := if lps.isEmpty then "" else "<" ++ ", ".intercalate (lps.map ("'" ++ ·.name)) ++ ">"
  match H with
  | none => "poly def " ++ n.name ++ params ++ " : " ++ A.pp ++ " =" ++ nl 2 ++ V.pp 0 2
  | some H => "poly def " ++ n.name ++ params ++ lives ++ " at " ++ H.pp ++ " =" ++ nl 2 ++ V.pp 0 2

def Decl.pp : Decl → String
  | .type _ n ps ls A =>
    "type " ++ n.name ++ (if ps.isEmpty then "" else "[" ++ ", ".intercalate (ps.map (·.name)) ++ "]") ++
      (if ls.isEmpty then "" else "<" ++ ", ".intercalate (ls.map ("'" ++ ·.name)) ++ ">") ++
      " = " ++ A.pp
  | .shape _ n σ => "shape " ++ n.name ++ " = " ++ σ.pp
  | .def_ _ n ps A V m =>
    let params := if ps.isEmpty then "" else "[" ++ ", ".intercalate (ps.map (·.name)) ++ "]"
    let rec mk : Mark → String
      | .none => "" | .total => "total " | .div => "div "
      | .template m _ => mk m ++ "fn "
      | .row es m ns => "with[" ++ ", ".intercalate (es.zipIdx.map fun ((e, As), j) =>
          (match ns[j]? with | some (some x) => x.name ++ ": " | _ => "") ++ e.name ++ (if As.isEmpty then "" else "[" ++ ", ".intercalate (As.map (VTy.pp · 0)) ++ "]")) ++
          "] " ++ mk m
    let bounds := if m.bounds.isEmpty then "" else
      " where " ++ ", ".intercalate (m.bounds.map fun (S, c) => S.name ++ ": '" ++ c.name)
    let mk := mk m
    mk ++ "def " ++ n.name ++ params ++ bounds ++ " : " ++ A.pp ++ " =" ++ nl 2 ++ V.pp 0 2
  | .extern _ n A => "extern " ++ n.name ++ " : " ++ A.pp
  | .main _ C M => "main : " ++ C.pp ++ " =" ++ nl 2 ++ M.pp 0 2
  | .include _ n => "include " ++ n.name
  | .effect _ n tps ops =>
    let op (o : OpDecl) : String :=
      (match o.kind with
        | .fn => "fn "
        | .ctl .lin => "linear ctl "
        | .ctl _ => "ctl ") ++
      o.name.name ++
        (if o.lives.isEmpty then "" else "<" ++ ", ".intercalate (o.lives.map fun (a, b) =>
          (Life.var a.span a.name).pp ++ (match b with | .top _ => "" | b => " < " ++ b.pp)) ++ ">") ++
        "(" ++ ", ".intercalate (o.params.map fun (x, A) => x.name ++ ": " ++ A.pp) ++
        ") -> " ++ o.res.pp
    "effect " ++ n.name ++ (if tps.isEmpty then "" else "[" ++ ", ".intercalate (tps.map (·.name)) ++ "]") ++
      " {" ++ String.join (ops.map fun o => nl 2 ++ op o ++ ";") ++ nl 0 ++ "}"
  | .handler _ n st S e cs l =>
    let cl (c : Clause) : String :=
      c.name.name ++ "(" ++ ", ".intercalate (c.params.map (·.name)) ++ ") = {" ++ nl 4 ++
        c.body.pp 0 4 ++ nl 2 ++ "}"
    "handler " ++ n.name ++ (if l then "(&mut " else "(mut ") ++ st.name ++ ": " ++ S.pp ++ "): " ++ e.name ++ " = {" ++
      String.join (cs.map fun c => nl 2 ++ cl c ++ ";") ++ nl 0 ++ "}"
  | .poly _ n tps lps H A V => Decl.ppPoly n tps lps H A V
  | .data _ d =>
    let field (f : DField) : String := (match f.name with
      | some x => x.name ++ ": "
      | none => "") ++ f.ty.pp
    let params := if d.tps.isEmpty then "" else "[" ++ ", ".intercalate (d.tps.map (·.name)) ++ "]"
    let lives := if d.lps.isEmpty then "" else "<" ++ ", ".intercalate (d.lps.map ("'" ++ ·.name)) ++ ">"
    "data " ++ d.name.name ++ params ++ lives ++ " = " ++
      (if d.record then
        "{ " ++ ", ".intercalate ((d.cons.head?.map (·.fields)).getD [] |>.map field) ++ " }"
      else " | ".intercalate (d.cons.map fun c => c.name.name ++
        (if c.fields.isEmpty then "" else "(" ++ ", ".intercalate (c.fields.map field) ++ ")")))
  | .chandler _ h =>
    let tys (As : List VTy) : String :=
      if As.isEmpty then "" else "[" ++ ", ".intercalate (As.map (VTy.pp · 0)) ++ "]"
    let cl (x : String) (xs : List Ident) (M : Comp) : String :=
      x ++ "(" ++ ", ".intercalate (xs.map (·.name)) ++ ") = {" ++ nl 4 ++ M.pp 0 4 ++ nl 2 ++ "}"
    let (rx, rA, rM) := h.ret
    "handler " ++ h.name.name ++
      (if h.tps.isEmpty then "" else "[" ++ ", ".intercalate (h.tps.map (·.name)) ++ "]") ++
      (if h.lps.isEmpty then "" else "<" ++ ", ".intercalate (h.lps.map fun (a, b) =>
        (Life.var a.span a.name).pp ++ (match b with | .top _ => "" | b => " < " ++ b.pp)) ++ ">") ++
      (if h.params.isEmpty then "" else
        "(" ++ ", ".intercalate (h.params.map fun (x, A) =>
          (if h.mutPs.contains x.name then "mut " else "") ++ x.name ++ ": " ++ A.pp) ++ ")") ++
      ": " ++ h.eff.name ++ tys h.effArgs ++ ", " ++ rA.pp ++ " -> " ++ h.res.pp ++
      (if h.row.isEmpty then "" else " with " ++ ", ".intercalate (h.row.map fun (e, As) => e.name ++ tys As)) ++
      " = {" ++ nl 2 ++ cl "return" [rx] rM ++ ";" ++
      String.join (h.clauses.map fun c => nl 2 ++ cl c.name.name c.params c.body ++ ";") ++ nl 0 ++ "}"

def Program.pp (p : Program) : String :=
  "\n\n".intercalate (p.decls.map Decl.pp) ++ "\n"

end Frontend
