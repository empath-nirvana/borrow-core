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
  | .fam .. | .view .. | .array .. | .arrayImm .. => 4
  | _ => 5

def CTy.level : CTy → Nat
  | .arr .. | .all .. | .nu .. => 0
  | .amp .. => 1
  | .ret .. | .delay .. | .stream .. | .iter .. => 4
  | .top .. | .name .. => 5

def widthName : BoCa.Width → String
  | .w32 => "i32"
  | .w64 => "i64"

/-- A printed shape as a shape atom: a name as it is, anything else parenthesized. -/
def ppShapeAtom (σ : Shape) (printed : String) : String :=
  match σ with
  | .name _ n => n
  | _ => "(" ++ printed ++ ")"

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
    | .handle _ o => if o then "output" else "input"
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

def Const.pp (c : Const) : String :=
  let (k, as) := c.toArgs
  if as.isEmpty then k.str else k.str ++ "[" ++ ", ".intercalate (as.map Arg.pp) ++ "]"

def Val.level : Val → Nat
  | .thunk .. | .thunkv .. | .bangThunk .. | .bangThunkv .. => 0
  | .inl .. | .inr .. | .roll .. | .unroll .. | .unbang .. | .unbox .. | .boxed .. | .run ..
  | .shorten .. => 1
  | .app .. | .inst .. => 2
  | _ => 3

def Comp.level : Comp → Nat
  | .bind .. | .letUnit .. | .letPair .. | .lam .. | .lamL .. => 0
  | .ret .. | .absurd .. | .nuIn .. | .nuOut .. => 1
  | .app .. | .proj .. | .inst .. => 2
  | _ => 3

/-- `linear ` before a `linear` binder. -/
def linKw (lin : Bool) : String := if lin then "linear " else ""

/-- A newline followed by `k` spaces. -/
def nl (k : Nat) : String := "\n" ++ "".pushn ' ' k

mutual
/-- A value-judged expression at level `lvl`, indented by `k` after each line break. -/
def Val.pp (V : Val) (lvl : Nat := 0) (k : Nat := 0) : String :=
  paren (V.level < lvl) <| match V with
    | .var _ x => x
    | .defApp _ n As => n ++ "[" ++ ", ".intercalate (As.map (VTy.pp · 0)) ++ "]"
    | .unit _ => "()"
    | .pair _ V W => "(" ++ V.pp 0 k ++ ", " ++ W.pp 0 k ++ ")"
    | .inl _ V => "inl " ++ V.pp 1 k
    | .inr _ V => "inr " ++ V.pp 1 k
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

/-- A computation at level `lvl`, indented by `k` after each line break. -/
def Comp.pp (M : Comp) (lvl : Nat := 0) (k : Nat := 0) : String :=
  paren (M.level < lvl) <| match M with
    | .ret _ V => "return " ++ V.pp 1 k
    | .bind _ x none M N lin => linKw lin ++ x.name ++ " <- " ++ M.pp 1 (k + 2) ++ ";" ++ nl k ++ N.pp 0 k
    | .bind _ x (some A) M N lin =>
      linKw lin ++ x.name ++ " : " ++ A.pp ++ " <- " ++ M.pp 1 (k + 2) ++ ";" ++ nl k ++ N.pp 0 k
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
end

def Decl.pp : Decl → String
  | .type _ n A => "type " ++ n.name ++ " = " ++ A.pp
  | .shape _ n σ => "shape " ++ n.name ++ " = " ++ σ.pp
  | .def_ _ n ps A V =>
    let params := if ps.isEmpty then "" else "[" ++ ", ".intercalate (ps.map (·.name)) ++ "]"
    "def " ++ n.name ++ params ++ " : " ++ A.pp ++ " =" ++ nl 2 ++ V.pp 0 2
  | .extern _ n A => "extern " ++ n.name ++ " : " ++ A.pp
  | .main _ C M => "main : " ++ C.pp ++ " =" ++ nl 2 ++ M.pp 0 2

def Program.pp (p : Program) : String :=
  "\n\n".intercalate (p.decls.map Decl.pp) ++ "\n"

end Frontend
