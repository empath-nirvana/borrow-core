import Support.Syntax.Integers
/-!
# Frontend — Syntax

The abstract syntax of the core language (`docs/syntax-core.md`, draft 1), as the parser
produces it. It keeps the written names: term variables, `def` names, lifetime variables,
type and shape names are strings. Resolving them to de Bruijn indices and `LifeVar` numbers
is the checker's work, because it depends on the types (syntax-core §1, §3, §6.3).

Every node carries the `Span` of the source text it was parsed from. `strip` sets every span
to `Span.none`, and the round-trip property of `Frontend/Print.lean` is stated modulo spans.
-/

namespace Frontend

open BoCa (Width IntLit HostOp)

/-- A source position: line and column, both from 1. -/
structure Pos where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The source text a node was parsed from: its first character and one past its last. -/
structure Span where
  start : Pos
  stop : Pos
  deriving DecidableEq, Repr, Inhabited

/-- The span of a node that was not parsed from source. -/
def Span.none : Span := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

/-- The span from the start of `a` to the end of `b`. -/
def Span.join (a b : Span) : Span := ⟨a.start, b.stop⟩

def Pos.render (p : Pos) : String := s!"{p.line}:{p.col}"

/-- A name at a binding or declaring occurrence. -/
structure Ident where
  name : String
  span : Span
  deriving DecidableEq, Repr, Inhabited

def Ident.strip (x : Ident) : Ident := { x with span := .none }

/-- Lifetimes `@ ::= 'x | top | dom | @ /\ @ | @ \/ @` (syntax-core §3). The variable is
    stored without its leading `'`. -/
inductive Life where
  | var (sp : Span) (x : String)
  | top (sp : Span)
  /-- `dom`: `Δ.meetOfDom` at the point where it is written. -/
  | dom (sp : Span)
  /-- `@ /\ @`. -/
  | meet (sp : Span) (a b : Life)
  /-- `@ \/ @`. -/
  | join (sp : Span) (a b : Life)
  deriving DecidableEq, Repr, Inhabited

/-- The mode of a borrow family, shortening or block borrow: `mut` or `imm`. -/
inductive Mode where
  | mut
  | imm
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Value types (syntax-core §4), with the built-in abbreviations as nodes of their own:
    the checker expands them. -/
inductive VTy where
  | unit (sp : Span)
  | zero (sp : Span)
  /-- `A * B`. -/
  | tensor (sp : Span) (A B : VTy)
  /-- `A + B`. -/
  | sum (sp : Span) (A B : VTy)
  /-- `U C`. -/
  | thunk (sp : Span) (C : CTy)
  | ref (sp : Span) (A : VTy)
  | imm (sp : Span) (a : Life) (A : VTy)
  | mut (sp : Span) (a : Life) (A : VTy)
  /-- `box @ A`, that is `[@] A`. -/
  | box (sp : Span) (a : Life) (A : VTy)
  /-- `!A`. -/
  | bang (sp : Span) (A : VTy)
  | unk (sp : Span)
  /-- `i32` / `i64`. -/
  | int (sp : Span) (w : Width)
  /-- `input` / `output` (`out = true`): the host stream types (SPEC §11). -/
  | handle (sp : Span) (out : Bool)
  /-- `mu X. A`. -/
  | mu (sp : Span) (X : Ident) (A : VTy)
  /-- An upper-case name: a `mu`-bound variable, a `type` abbreviation, or a `def`'s type
      parameter. Which one is the checker's decision. -/
  | name (sp : Span) (n : String)
  /-- `A => B`, the abbreviation `U (A -o F B)`. -/
  | lolli (sp : Span) (A B : VTy)
  /-- `all 'x < @. A`, the abbreviation `U (forall 'x < @. F A)`. -/
  | all (sp : Span) (x : Ident) (b : Life) (A : VTy)
  /-- `block σ`. -/
  | block (sp : Span) (σ : Shape)
  /-- `val σ`. -/
  | val (sp : Span) (σ : Shape)
  /-- `fam m @ σ`. -/
  | fam (sp : Span) (m : Mode) (a : Life) (σ : Shape)
  /-- `view @ A`, that is `Imm̲ @ A`. -/
  | view (sp : Span) (a : Life) (A : VTy)
  /-- `array A`: an owned array, the family of its cells (SPEC §9). -/
  | array (sp : Span) (A : VTy)
  /-- `array_imm @ A`: the family of leaf views of an array (SPEC §9). -/
  | arrayImm (sp : Span) (a : Life) (A : VTy)

/-- Computation types (syntax-core §4). -/
inductive CTy where
  /-- `F A`. -/
  | ret (sp : Span) (A : VTy)
  /-- `A -o C`. -/
  | arr (sp : Span) (A : VTy) (C : CTy)
  /-- `C & D`. -/
  | amp (sp : Span) (C D : CTy)
  | top (sp : Span)
  /-- `forall 'x < @. C`. -/
  | all (sp : Span) (x : Ident) (b : Life) (C : CTy)
  /-- `nu X. C`: `U X` in `C` is the rest (SPEC §7). -/
  | nu (sp : Span) (X : Ident) (C : CTy)
  /-- `X`, a `nu`-bound variable; it may occur only as `U X`. -/
  | name (sp : Span) (n : String)
  /-- `delay A`, `stream A` and `iter A R R'`: abbreviations over `nu`. -/
  | delay (sp : Span) (A : VTy)
  | stream (sp : Span) (A : VTy)
  | iter (sp : Span) (A R R' : VTy)
  /-- `loop A B`: `nu X. F (A + U X) & F B` (SPEC §7). -/
  | loop (sp : Span) (A B : VTy)

/-- Shapes `σ ::= leaf A | node σ σ | Name` (syntax-core §5). -/
inductive Shape where
  | leaf (sp : Span) (A : VTy)
  | node (sp : Span) (σ τ : Shape)
  | name (sp : Span) (n : String)
end

deriving instance DecidableEq for VTy, CTy, Shape
deriving instance Repr for VTy, CTy, Shape

/-- One bracket argument of a constant or derived form. -/
inductive Arg where
  | ty (A : VTy)
  | life (a : Life)
  /-- A binder argument `'x`. -/
  | binder (x : Ident)
  | shape (σ : Shape)
  /-- The literal of `i32[n]` / `i64[n]`, as written (reduced by `IntLit` construction). -/
  | nat (n : Nat)
  /-- The operation name of `host[op]`. -/
  | op (o : HostOp)
  /-- A computation type, the `nu` type of `unfold[C, S]`. -/
  | cty (C : CTy)
  deriving DecidableEq, Repr

/-- The constants of syntax-core §8 and §8a, and the derived forms of §9 that are typed
    values (`shorten_*` takes an operand and is a `Val` node). Each constructor holds every
    bracket argument of its rule, in the written order. -/
inductive Const where
  | alloc (A : VTy)
  | free (A : VTy)
  | swap (A B : VTy)
  | copy (a : Life) (A : VTy)
  | copyBang (A : VTy)
  | forgetImm (a : Life) (A : VTy)
  | forgetMut (a : Life) (A : VTy)
  | forgetUnk
  | forgetBang (A : VTy)
  | withbor1 (x : Ident) (A B : VTy)
  | withbor2 (x : Ident) (b : Life) (A B : VTy)
  | withbor3 (a : Life) (x : Ident) (A B : VTy)
  | withload (a : Life) (x : Ident) (A B : VTy)
  | withswap (a : Life) (A B : VTy)
  /-- `fold_imm[F, 'y, @c, R]`: `F` is a type in which `X` is the recursive position. -/
  | foldImm (F : VTy) (y : Ident) (c : Life) (R : VTy)
  | foldOwn (F R : VTy)
  | foldReuse (F R : VTy)
  | fixd (A S : VTy)
  | unfoldS (A S : VTy)
  /-- `unfold[C, S]`: coiteration at the `nu` type `C` (SPEC §7). -/
  | unfold (C : CTy) (S : VTy)
  /-- `i32[n]` / `i64[n]`, read modulo 2^32 / 2^64. -/
  | lit (c : IntLit)
  | host (op : HostOp)
  | allocS (σ : Shape)
  | freeS (σ : Shape)
  /-- `withbor_s_mut[σ, 'c, T]` / `withbor_s_imm[σ, 'c, T]`. -/
  | withborS (m : Mode) (σ : Shape) (c : Ident) (T : VTy)
  /-- `withbor_f2_mut['c, 'a, 'b, @w, A, B, T]`. -/
  | withborF2Mut (c a b : Ident) (w : Life) (A B T : VTy)
  /-- `withbor_f2_imm['c, 'a, 'b, A, B, T]`. -/
  | withborF2Imm (c a b : Ident) (A B T : VTy)
  /-- The array constants of SPEC §9: `array_new[A]`, `array_free[A]`, `array_size[A]`,
      `array_replace[A]`, and on a family of leaf views `array_len[@, A]`, `array_get[@, A]`,
      `array_copy[@, A]`, `array_forget[@, A]`. -/
  | arrayNew (A : VTy)
  | arrayFree (A : VTy)
  | arraySize (A : VTy)
  | arrayReplace (A : VTy)
  | arrayLen (a : Life) (A : VTy)
  | arrayGet (a : Life) (A : VTy)
  | arrayCopy (a : Life) (A : VTy)
  | arrayForget (a : Life) (A : VTy)
  deriving DecidableEq, Repr

mutual
/-- Value-judged expressions (syntax-core §6.1), checked at a value type. -/
inductive Val where
  /-- A lower-case name: a term variable or a `def` without arguments. -/
  | var (sp : Span) (x : String)
  /-- `name[A, …]`: a `def` at value-type arguments. -/
  | defApp (sp : Span) (name : String) (args : List VTy)
  | unit (sp : Span)
  | pair (sp : Span) (V W : Val)
  | inl (sp : Span) (V : Val)
  | inr (sp : Span) (V : Val)
  /-- `thunk M`, `M : F A`. -/
  | thunk (sp : Span) (M : Comp)
  /-- `thunkv N`, `N` a literal λ. -/
  | thunkv (sp : Span) (N : Comp)
  /-- `!thunk M`. -/
  | bangThunk (sp : Span) (M : Comp)
  /-- `!thunkv N`. -/
  | bangThunkv (sp : Span) (N : Comp)
  | unbang (sp : Span) (V : Val)
  /-- `boxed[@] V`. -/
  | boxed (sp : Span) (a : Life) (V : Val)
  | unbox (sp : Span) (V : Val)
  /-- `(V :> @)`: `⊑Imm` or `⊑Mut`, by the type of `V`. -/
  | sub (sp : Span) (V : Val) (a : Life)
  | roll (sp : Span) (V : Val)
  | unroll (sp : Span) (V : Val)
  /-- `run M`, `M : F A` (`ofRet`). -/
  | run (sp : Span) (M : Comp)
  /-- `V W` (`lolliE`). -/
  | app (sp : Span) (V W : Val)
  /-- `V [@]` (`allEV`). -/
  | inst (sp : Span) (V : Val) (a : Life)
  /-- `(V : A)`. -/
  | ascribe (sp : Span) (V : Val) (A : VTy)
  | const (sp : Span) (c : Const)
  /-- `shorten_mut[σ, @a] V` / `shorten_imm[σ, @a] V`. -/
  | shorten (sp : Span) (m : Mode) (σ : Shape) (a : Life) (V : Val)
  /-- `&x`: lend the capability `x` to one call, elaborated away before checking (SPEC §11). -/
  | lend (sp : Span) (x : Ident)

/-- Computations (syntax-core §6.2), checked at a computation type. -/
inductive Comp where
  | ret (sp : Span) (V : Val)
  /-- `x <- M; N`, or `x : A <- M; N` with the annotation; `lin` for `linear x <- M; N`, whose
  variable is not dropped implicitly (SPEC §12). -/
  | bind (sp : Span) (x : Ident) (A : Option VTy) (M N : Comp) (lin : Bool)
  /-- `force x`. -/
  | force (sp : Span) (x : Ident)
  /-- `fun (x : A) -> M`. -/
  | lam (sp : Span) (x : Ident) (A : VTy) (M : Comp)
  /-- `M x`. -/
  | app (sp : Span) (M : Comp) (x : Ident)
  /-- `<M, N>`. -/
  | with_ (sp : Span) (M N : Comp)
  /-- `M.1` (`i = 1`) and `M.2` (`i = 2`). -/
  | proj (sp : Span) (i : Bool) (M : Comp)
  /-- `<>`. -/
  | top (sp : Span)
  /-- `let () = V; M`. -/
  | letUnit (sp : Span) (V : Val) (M : Comp)
  /-- `let (x, y) = V; M`. -/
  | letPair (sp : Span) (x y : Ident) (V : Val) (M : Comp)
  /-- `case V { inl x -> M | inr y -> N }`. -/
  | case (sp : Span) (V : Val) (x : Ident) (M : Comp) (y : Ident) (N : Comp)
  | absurd (sp : Span) (V : Val)
  /-- `Fun 'x < @. M`. -/
  | lamL (sp : Span) (x : Ident) (b : Life) (M : Comp)
  /-- `M [@]`. -/
  | inst (sp : Span) (M : Comp) (a : Life)
  /-- `nu_in M`: `M` at the unrolling of a `nu` type (also `delay_in`, `stream_in`). -/
  | nuIn (sp : Span) (M : Comp)
  /-- `nu_out M` (also `delay_out`, `stream_out`). -/
  | nuOut (sp : Span) (M : Comp)
  /-- `(M : C)`. -/
  | ascribe (sp : Span) (M : Comp) (C : CTy)
  /-- `for x in V { M }; N`, at the end of a `main` with ambient capabilities, elaborated away
  before checking (SPEC §11). -/
  | for_ (sp : Span) (x : Ident) (V : Val) (M N : Comp)
end

deriving instance DecidableEq for Val, Comp
deriving instance Repr for Val, Comp

/-- A `def`'s effect marker (SPEC §14): none, `total` (it must not loop) or `div` (it loops,
or may one day). Divergence is inferred, so `div` is never needed. -/
inductive Mark where
  | none
  | total
  | div
  deriving DecidableEq, Repr, Inhabited

/-- Declarations (syntax-core §10). -/
inductive Decl where
  | type (sp : Span) (n : Ident) (A : VTy)
  | shape (sp : Span) (n : Ident) (σ : Shape)
  /-- `def name[P₁, …, Pₙ] : A = V`; `params` is empty for `def name : A = V`. `mark` is the
  `total` or `div` written before `def`. -/
  | def_ (sp : Span) (n : Ident) (params : List Ident) (A : VTy) (V : Val) (mark : Mark)
  | extern (sp : Span) (n : Ident) (A : VTy)
  | main (sp : Span) (C : CTy) (M : Comp)
  deriving DecidableEq, Repr

/-- A source file: its declarations in order. -/
structure Program where
  decls : List Decl
  deriving DecidableEq, Repr

/-! ### Erasing spans -/

def Life.strip : Life → Life
  | .var _ x => .var .none x
  | .top _ => .top .none
  | .dom _ => .dom .none
  | .meet _ a b => .meet .none a.strip b.strip
  | .join _ a b => .join .none a.strip b.strip

mutual
def VTy.strip : VTy → VTy
  | .unit _ => .unit .none
  | .zero _ => .zero .none
  | .tensor _ A B => .tensor .none A.strip B.strip
  | .sum _ A B => .sum .none A.strip B.strip
  | .thunk _ C => .thunk .none C.strip
  | .ref _ A => .ref .none A.strip
  | .imm _ a A => .imm .none a.strip A.strip
  | .mut _ a A => .mut .none a.strip A.strip
  | .box _ a A => .box .none a.strip A.strip
  | .bang _ A => .bang .none A.strip
  | .unk _ => .unk .none
  | .int _ w => .int .none w
  | .handle _ o => .handle .none o
  | .mu _ X A => .mu .none X.strip A.strip
  | .name _ n => .name .none n
  | .lolli _ A B => .lolli .none A.strip B.strip
  | .all _ x b A => .all .none x.strip b.strip A.strip
  | .block _ σ => .block .none σ.strip
  | .val _ σ => .val .none σ.strip
  | .fam _ m a σ => .fam .none m a.strip σ.strip
  | .view _ a A => .view .none a.strip A.strip
  | .array _ A => .array .none A.strip
  | .arrayImm _ a A => .arrayImm .none a.strip A.strip

def CTy.strip : CTy → CTy
  | .ret _ A => .ret .none A.strip
  | .arr _ A C => .arr .none A.strip C.strip
  | .amp _ C D => .amp .none C.strip D.strip
  | .top _ => .top .none
  | .all _ x b C => .all .none x.strip b.strip C.strip
  | .nu _ X C => .nu .none X.strip C.strip
  | .name _ n => .name .none n
  | .delay _ A => .delay .none A.strip
  | .stream _ A => .stream .none A.strip
  | .iter _ A R R' => .iter .none A.strip R.strip R'.strip
  | .loop _ A B => .loop .none A.strip B.strip

def Shape.strip : Shape → Shape
  | .leaf _ A => .leaf .none A.strip
  | .node _ σ τ => .node .none σ.strip τ.strip
  | .name _ n => .name .none n
end

def Const.strip : Const → Const
  | .alloc A => .alloc A.strip
  | .free A => .free A.strip
  | .swap A B => .swap A.strip B.strip
  | .copy a A => .copy a.strip A.strip
  | .copyBang A => .copyBang A.strip
  | .forgetImm a A => .forgetImm a.strip A.strip
  | .forgetMut a A => .forgetMut a.strip A.strip
  | .forgetUnk => .forgetUnk
  | .forgetBang A => .forgetBang A.strip
  | .withbor1 x A B => .withbor1 x.strip A.strip B.strip
  | .withbor2 x b A B => .withbor2 x.strip b.strip A.strip B.strip
  | .withbor3 a x A B => .withbor3 a.strip x.strip A.strip B.strip
  | .withload a x A B => .withload a.strip x.strip A.strip B.strip
  | .withswap a A B => .withswap a.strip A.strip B.strip
  | .foldImm F y c R => .foldImm F.strip y.strip c.strip R.strip
  | .foldOwn F R => .foldOwn F.strip R.strip
  | .foldReuse F R => .foldReuse F.strip R.strip
  | .fixd A S => .fixd A.strip S.strip
  | .unfoldS A S => .unfoldS A.strip S.strip
  | .unfold C S => .unfold C.strip S.strip
  | .lit c => .lit c
  | .host op => .host op
  | .allocS σ => .allocS σ.strip
  | .freeS σ => .freeS σ.strip
  | .withborS m σ c T => .withborS m σ.strip c.strip T.strip
  | .withborF2Mut c a b w A B T =>
      .withborF2Mut c.strip a.strip b.strip w.strip A.strip B.strip T.strip
  | .withborF2Imm c a b A B T => .withborF2Imm c.strip a.strip b.strip A.strip B.strip T.strip
  | .arrayNew A => .arrayNew A.strip
  | .arrayFree A => .arrayFree A.strip
  | .arraySize A => .arraySize A.strip
  | .arrayReplace A => .arrayReplace A.strip
  | .arrayLen a A => .arrayLen a.strip A.strip
  | .arrayGet a A => .arrayGet a.strip A.strip
  | .arrayCopy a A => .arrayCopy a.strip A.strip
  | .arrayForget a A => .arrayForget a.strip A.strip

mutual
def Val.strip : Val → Val
  | .var _ x => .var .none x
  | .defApp _ n args => .defApp .none n (args.map VTy.strip)
  | .unit _ => .unit .none
  | .pair _ V W => .pair .none V.strip W.strip
  | .inl _ V => .inl .none V.strip
  | .inr _ V => .inr .none V.strip
  | .thunk _ M => .thunk .none M.strip
  | .thunkv _ M => .thunkv .none M.strip
  | .bangThunk _ M => .bangThunk .none M.strip
  | .bangThunkv _ M => .bangThunkv .none M.strip
  | .unbang _ V => .unbang .none V.strip
  | .boxed _ a V => .boxed .none a.strip V.strip
  | .unbox _ V => .unbox .none V.strip
  | .sub _ V a => .sub .none V.strip a.strip
  | .roll _ V => .roll .none V.strip
  | .unroll _ V => .unroll .none V.strip
  | .run _ M => .run .none M.strip
  | .app _ V W => .app .none V.strip W.strip
  | .inst _ V a => .inst .none V.strip a.strip
  | .ascribe _ V A => .ascribe .none V.strip A.strip
  | .const _ c => .const .none c.strip
  | .shorten _ m σ a V => .shorten .none m σ.strip a.strip V.strip
  | .lend _ x => .lend .none x.strip

def Comp.strip : Comp → Comp
  | .ret _ V => .ret .none V.strip
  | .bind _ x A M N lin => .bind .none x.strip (A.map VTy.strip) M.strip N.strip lin
  | .force _ x => .force .none x.strip
  | .lam _ x A M => .lam .none x.strip A.strip M.strip
  | .app _ M x => .app .none M.strip x.strip
  | .with_ _ M N => .with_ .none M.strip N.strip
  | .proj _ i M => .proj .none i M.strip
  | .top _ => .top .none
  | .letUnit _ V M => .letUnit .none V.strip M.strip
  | .letPair _ x y V M => .letPair .none x.strip y.strip V.strip M.strip
  | .case _ V x M y N => .case .none V.strip x.strip M.strip y.strip N.strip
  | .absurd _ V => .absurd .none V.strip
  | .lamL _ x b M => .lamL .none x.strip b.strip M.strip
  | .inst _ M a => .inst .none M.strip a.strip
  | .nuIn _ M => .nuIn .none M.strip
  | .nuOut _ M => .nuOut .none M.strip
  | .ascribe _ M C => .ascribe .none M.strip C.strip
  | .for_ _ x V M N => .for_ .none x.strip V.strip M.strip N.strip
end

def Decl.strip : Decl → Decl
  | .type _ n A => .type .none n.strip A.strip
  | .shape _ n σ => .shape .none n.strip σ.strip
  | .def_ _ n ps A V m => .def_ .none n.strip (ps.map Ident.strip) A.strip V.strip m
  | .extern _ n A => .extern .none n.strip A.strip
  | .main _ C M => .main .none C.strip M.strip

def Program.strip (p : Program) : Program := ⟨p.decls.map Decl.strip⟩

/-- The span of a value-judged expression. -/
def Val.span : Val → Span
  | .var sp _ | .defApp sp _ _ | .unit sp | .pair sp _ _ | .inl sp _ | .inr sp _
  | .thunk sp _ | .thunkv sp _ | .bangThunk sp _ | .bangThunkv sp _ | .unbang sp _
  | .boxed sp _ _ | .unbox sp _ | .sub sp _ _ | .roll sp _ | .unroll sp _ | .run sp _
  | .app sp _ _ | .inst sp _ _ | .ascribe sp _ _ | .const sp _ | .shorten sp _ _ _ _
  | .lend sp _ => sp

/-- The span of a computation. -/
def Comp.span : Comp → Span
  | .ret sp _ | .bind sp _ _ _ _ _ | .force sp _ | .lam sp _ _ _ | .app sp _ _ | .with_ sp _ _
  | .proj sp _ _ | .top sp | .letUnit sp _ _ | .letPair sp _ _ _ _ | .case sp _ _ _ _ _
  | .absurd sp _ | .lamL sp _ _ _ | .inst sp _ _ | .nuIn sp _ | .nuOut sp _
  | .ascribe sp _ _ | .for_ sp _ _ _ _ => sp

def Life.span : Life → Span
  | .var sp _ | .top sp | .dom sp | .meet sp _ _ | .join sp _ _ => sp

def VTy.span : VTy → Span
  | .unit sp | .zero sp | .tensor sp _ _ | .sum sp _ _ | .thunk sp _ | .ref sp _ | .imm sp _ _
  | .mut sp _ _ | .box sp _ _ | .bang sp _ | .unk sp | .int sp _ | .handle sp _ | .mu sp _ _ | .name sp _
  | .lolli sp _ _ | .all sp _ _ _ | .block sp _ | .val sp _ | .fam sp _ _ _ | .view sp _ _
  | .array sp _ | .arrayImm sp _ _ => sp

def CTy.span : CTy → Span
  | .ret sp _ | .arr sp _ _ | .amp sp _ _ | .top sp | .all sp _ _ _ | .nu sp _ _ | .name sp _
  | .delay sp _ | .stream sp _ | .iter sp _ _ _ | .loop sp _ _ => sp

def Shape.span : Shape → Span
  | .leaf sp _ | .node sp _ _ | .name sp _ => sp

end Frontend
