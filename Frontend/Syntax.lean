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

/-- `p` comes after `q` in the source. -/
def Pos.later (p q : Pos) : Bool := p.line > q.line || (p.line == q.line && p.col > q.col)

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

/-- The qualifier of an operation's continuation in a row (SPEC §19): linear, affine or
unrestricted. -/
inductive Qual where
  | lin
  | aff
  | unr
  deriving DecidableEq, Repr, Inhabited

def Qual.str : Qual → String
  | .lin => "lin"
  | .aff => "aff"
  | .unr => "unr"

/-- The host resource kinds the surface names (SPEC §11, §34): `input`, `output`, `clock`,
`args`. -/
inductive HostKind where
  | input
  | output
  | clock
  | args
  deriving DecidableEq, Repr, Inhabited

/-- The surface name of a host resource kind. -/
def HostKind.name : HostKind → String
  | .input => "input"
  | .output => "output"
  | .clock => "clock"
  | .args => "args"

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
  /-- `input`, `output`, `clock`, `args`: the host resource types (SPEC §11, §34). -/
  | handle (sp : Span) (k : HostKind)
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
  /-- `array_mut @ A`: the family of `mut` leaf borrows of an array (SPEC §9). -/
  | arrayMut (sp : Span) (a : Life) (A : VTy)
  /-- `sized D S A`: a sized iterator over the data `D` with its own state `S`, yielding `A`
  (SPEC §16), the abbreviation `D * (S * !(D * S => (D * S) * (A + (1 + 1))))`. -/
  | sized (sp : Span) (D S A : VTy)
  /-- `N[A₁, …]`: the type arguments of a parameterised `type` declaration, curried, with `F` the
  name or a shorter application.  `[spec §7]` -/
  | app (sp : Span) (F A : VTy)
  /-- `N[…]<'a, …>`: its lifetime arguments, curried after the type arguments.  `[spec §7]` -/
  | lapp (sp : Span) (F : VTy) (a : Life)
  /-- `(A => B with E₁, E₂[T, …])`: a function type with a provided row, the type of a
  computation parameter (SPEC §33). The callee serves the effects of the row for the argument.
  `F` is the function type `A => B`, and `row` the effects: the empty name applied to their
  instances in order, each the effect's name applied to its type arguments (`VTy.rowEffs`).
  Elaborated away by `Frontend.Elab.Effects`.  `[spec §33]` -/
  | rowed (sp : Span) (F : VTy) (row : VTy)

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
  /-- `pull A B R`: `nu X. F (A * U X + (B + U X)) & F R`, a stored generator (SPEC §15): `next`
  gives an `A` with the rest, finishes with `B`, or skips a step; `close` hands back `R`. -/
  | pull (sp : Span) (A B R : VTy)
  /-- `F[n.i q A ~> B, …] R`: `F_Σ R`, the row's operations stacked over `F R`.  `[spec §19]` -/
  | eff (sp : Span) (row : Row) (A : VTy)

/-- An effect row (SPEC §19): each entry the operation `i` of the handler name `n`, `A ↠^q B`.
`[spec §19]` -/
inductive Row where
  | nil
  | cons (n i : Nat) (q : Qual) (A B : VTy) (rest : Row)

/-- Shapes `σ ::= leaf A | node σ σ | Name` (syntax-core §5). -/
inductive Shape where
  | leaf (sp : Span) (A : VTy)
  | node (sp : Span) (σ τ : Shape)
  | name (sp : Span) (n : String)
end

deriving instance DecidableEq for VTy, CTy, Row, Shape

/-- The expansion of `sized D S A` (SPEC §16): the data, the state, and the step, which answers
the next data and state with an element, a skip (`inr (inl ())`) or the end (`inr (inr ())`). -/
def VTy.sizedExpand (sp : Span) (D S A : VTy) : VTy :=
  .tensor sp D (.tensor sp S (.bang sp (.lolli sp (.tensor sp D S)
    (.tensor sp (.tensor sp D S) (.sum sp A (.sum sp (.unit sp) (.unit sp)))))))
deriving instance Repr for VTy, CTy, Row, Shape

/-- A field of a `data` constructor: its name when it is written (`C(f: A)`, a record's), and its
type as written; `box A` is a cell of its own (SPEC §42).  `[spec §42]` -/
structure DField where
  name : Option Ident
  ty : VTy
  deriving DecidableEq, Repr

/-- A constructor of a `data` declaration, its fields in order.  `[spec §42]` -/
structure DCon where
  name : Ident
  fields : List DField
  deriving DecidableEq, Repr

/-- `data N[P, …]<'l, …> = C₁(…) | …`, or a record `data N[…] = { f: A, … }`, which is one
constructor named `N` (`record`).  `[spec §42]` -/
structure DataDecl where
  name : Ident
  tps : List Ident
  lps : List Ident
  record : Bool
  cons : List DCon
  deriving DecidableEq, Repr

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
  /-- A row `[n.i q A ~> B, …]`, of an unwinding borrow constant (SPEC §19). -/
  | row (r : Row)
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
  /-- The slice borrows of SPEC §9: `slice_borrow_mut['x, @b, A, B]`,
      `slice_borrow_imm['x, @b, A, B]`, and on a `mut` family `slice_get_mut[@, A]`,
      `slice_len_mut[@, A]`. -/
  | sliceBorrowMut (x : Ident) (b : Life) (A B : VTy)
  | sliceBorrowImm (x : Ident) (b : Life) (A B : VTy)
  | sliceGetMut (a : Life) (A : VTy)
  | sliceLenMut (a : Life) (A : VTy)
  /-- The splits and writes of SPEC §9: `slice_split_imm[@, A]`, `slice_split_mut[@, A]`,
      `slice_empty_imm[@, A]`, `slice_empty_mut[@, A]`, and on a `mut` family
      `slice_replace_mut[@, A]`, `slice_swap_mut[@, A]`. -/
  | sliceSplitImm (a : Life) (A : VTy)
  | sliceSplitMut (a : Life) (A : VTy)
  | sliceEmptyImm (a : Life) (A : VTy)
  | sliceEmptyMut (a : Life) (A : VTy)
  | sliceReplaceMut (a : Life) (A : VTy)
  | sliceSwapMut (a : Life) (A : VTy)
  /-- `count_fold[S]`: the counted loop of SPEC §16. -/
  | countFold (S : VTy)
  /-- `count_try[S, E]`: the counted loop with an exit of SPEC §16. -/
  | countTry (S E : VTy)
  /-- `bounded_fix[A, C]`: the fuelled fixed point of SPEC §20. -/
  | boundedFix (A : VTy) (C : CTy)
  /-- The unwinding borrows of SPEC §19, each at the row `r` of its callback:
  `withbor1u['x, A, B, [r]]`, `withbor2u['x, @b, A, B, [r]]`, `withbor3u[@a, 'x, A, B, [r]]`,
  `withloadu[@a, 'x, A, B, [r]]`, `slice_borrow_mut_u['x, @b, A, B, [r]]`,
  `slice_borrow_imm_u['x, @b, A, B, [r]]`.  `[spec §19]` -/
  | withbor1U (x : Ident) (A B : VTy) (r : Row)
  | withbor2U (x : Ident) (b : Life) (A B : VTy) (r : Row)
  | withbor3U (a : Life) (x : Ident) (A B : VTy) (r : Row)
  | withloadU (a : Life) (x : Ident) (A B : VTy) (r : Row)
  | sliceBorrowMutU (x : Ident) (b : Life) (A B : VTy) (r : Row)
  | sliceBorrowImmU (x : Ident) (b : Life) (A B : VTy) (r : Row)
  /-- `iterate[S, B, R, [r]]`: the loop of SPEC §14 with state `S`, result `B` and residual `R`,
  at the row `r`, which holds `Div`.  `[spec §14]` -/
  | iterate (St B R : VTy) (r : Row)
  deriving DecidableEq, Repr

/-- A binary operator of the surface (draft 0 §2.12), resolved by the width of its operands.
`rem` is `%` (SPEC §39). -/
inductive SurfOp where
  | add | sub | mul | div | eq | ne | lt | le | gt | ge | rem
  deriving DecidableEq, Repr, Inhabited

def SurfOp.str : SurfOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .eq => "==" | .ne => "!=" | .lt => "<"
  | .le => "<=" | .gt => ">" | .ge => ">=" | .rem => "%"

/-- The kinds of borrow block (draft 0 §2.6). -/
inductive BorrowKind where
  /-- `borrow imm r { … }`: `withbor1`. -/
  | imm
  /-- `borrow mut r { … }`: `withbor2`. -/
  | mut
  /-- `borrow mut (r₁, r₂) { … }`: `withbor_f2_mut`, a family of two cells at one lifetime. -/
  | famMut
  /-- `modify m { … }`: `withswap`. -/
  | modify
  deriving DecidableEq, Repr, Inhabited

/-- What a handler site is, as `Frontend.Elab.Effects` makes it: a `with` of a control handler, a
`for`'s site of an iteration effect, whose clause is the loop's body (`VSugar.forSite`), or a stored
generator's, whose clause keeps the continuation (`VSugar.pullSite`).  `[spec §15, §19]` -/
inductive SiteKind where
  | handler
  | forSite
  | pullSite
  deriving DecidableEq, Repr, Inhabited

/-- A handler site as `Frontend.Elab.Effects` records it for the checker, by its static name `n`:
the effect it serves and its type arguments there, the handler (a control handler's name, or the
function a `for` or a stored generator runs), the name the `with` gives it (`with n = h(…)`,
SPEC §38), what kind of site it is, its operations `(q, A, B)` at the site, and the handler's
state: its parameters, when its clauses are passed them as a state (SPEC §19, *Handler state*),
else none. It travels with the site's sugar (`HInfo.site`, `ItInfo.site`) to the `handle` node the
typed elaboration assembles, whose `site` it is, with its types in the frame of that node's code;
the checker reads it there.  `[spec §19]` -/
structure SiteRec where
  n : Nat
  eff : String
  args : List VTy
  handler : String
  slot : Option String := none
  kind : SiteKind := .handler
  ents : List (Qual × VTy × VTy)
  state : List (String × VTy) := []
  deriving DecidableEq, Repr, Inhabited

/-- A handler site of a control effect, as `Frontend.Elab.Effects` leaves it for the typed
elaboration (SPEC §19): the handler, the site's static name, its operations `(q, A, B)` in order
(closed), the handler's type parameters still to be determined and those already known, its
parameters, the type of its return clause's binder and its answer type (each over the type
parameters). A site whose operations are all abortive answers `inl` the body's value or `inr` an
operation's argument, and its clauses run after it (SPEC §19): `after` is then the handler's own
answer type, which the typed elaboration gives the type name `fx_res{n}` once its type parameters
are determined. A clause that takes its continuation out of a box (`unbox k`) receives it boxed
at `top`, `[@⊤] K` (`boxK`, SPEC §28's BOXED-κ, §30). -/
structure HInfo where
  name : String
  n : Nat
  ents : List (Qual × VTy × VTy)
  tps : List String
  known : List (String × VTy)
  params : List (String × VTy)
  retA : VTy
  res : VTy
  after : Option VTy := none
  boxK : Bool := false
  /-- The handler's lifetime parameters (SPEC §32): instantiated at the site at the meet of the
  lifetimes in scope (`dom`); `κ`, when boxed, is boxed at the first, else at `top`. -/
  lives : List String := []
  /-- The elaboration's record of the site, its types in the frame of the site's code, over the
  type parameters still to be determined (`tps`) and the lifetime parameters (`lives`). -/
  site : SiteRec
  deriving DecidableEq, Repr

/-- **The elaborator's key of a `def` it generates** (SPEC §3): the template, function or group it
is a copy of (`origin`), a template instance's type arguments (`targs`), and a copy's keys: the
handlers that serve its effects, the static names of the sites that do (`n…`), and its blocks'
(`keys`). Copies that differ only in their sites' names are one body (`body`: the origin and its
keys but the sites'). -/
structure DefKey where
  name : String
  origin : String
  targs : List VTy := []
  keys : List String := []
  body : String
  deriving DecidableEq, Repr, Inhabited

/-- A copy's key that is a site's static name (`n7`). -/
def DefKey.isSite (k : String) : Bool := k.startsWith "n" && (k.drop 1).all Char.isDigit && k.length > 1

/-- The key of a copy of `origin` at `keys`, named `name`. -/
def DefKey.copy (name origin : String) (keys : List String) : DefKey :=
  { name, origin, keys, body := origin ++ "__" ++ "_".intercalate (keys.filter (!DefKey.isSite ·)) }

/-- A handler site of an iteration effect (SPEC §15), as `Frontend.Elab.Effects` leaves it for the
typed elaboration: the site's static name, the type of the element its operation passes, the
variable a `for`'s site threads through the operation (its copy of the callee takes it first and
hands it back first), the callee as written, for messages, and the elaboration's record of the
site, its types in the frame of the callee's declaration (over its type parameters). -/
structure ItInfo where
  n : Nat
  T : VTy
  w : String
  callee : String
  site : SiteRec
  deriving DecidableEq, Repr

/-- A declaration a field `e.f` may be of (SPEC §42, *Fields*): its name and type parameters, its
fields' names in order (`""` for a field with none), the field's index, and whether the
declaration is a `μ`.  `[spec §42]` -/
structure FieldCand where
  decl : String
  tps : List String
  names : List String
  idx : Nat
  rolls : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A surface form that needs types to elaborate (docs/typed-elaboration.md §5): a leaf, applied
to its operands as values, and elaborated to core by the typed pass of `Frontend/Sugar.lean`. -/
inductive VSugar where
  /-- An integer literal, `i32` or `i64` by the type expected of it (`i32` by default). -/
  | lit (n : Nat)
  /-- A float literal `m × 10^e`, `f64` or `f32` by the type expected of it (`f64` by default).
  `[spec §37]` -/
  | flit (m : Nat) (e : Int)
  /-- A binary operator, applied to a pair of operands. -/
  | op (o : SurfOp)
  /-- `checked_div(a, b)`, `checked_rem(a, b)` (`o` is `div` or `rem`), applied to the pair of
  operands: the quotient or remainder `inl q`, or `inr e`, `e : DivError` (`inl ()` for a zero
  divisor, `inr ()` for an overflow) (SPEC §39). Written by `Frontend/Elab/Divisions.lean` for a
  division that can fail; a call of either name is one in the typed elaboration when the program
  declares no function of it (`Elab.Instances.checkedOp?`). -/
  | checked (o : SurfOp)
  /-- A constant written without its bracket arguments, `alloc(e)`, `free(e)`, `swap(c, e)`,
  applied to its operands; or `clone(x)`, an explicit copy of a persistent variable. -/
  | call (k : String)
  /-- `{ S }`: applied to the thunk it marks. A block whose body loops runs nothing until the
  loop is first observed (`div_defer`). -/
  | brace
  /-- A borrow block at the lifetime `'x`, applied to the place and then to the callback. -/
  | borrow (k : BorrowKind) (x : String)
  /-- `*e`: the content of a borrow or a cell, applied to it. -/
  | deref
  /-- `break` in a loop's body: the loop ends. -/
  | brk
  /-- `continue` in a loop's body: the rest of the body is skipped, and the loop goes on. -/
  | cont
  /-- `a..b`, applied to the pair of its ends: the count `a, a + 1, …, b − 1`, a source of `for`
  (SPEC §16). -/
  | count
  /-- `return e` in a loop's body, applied to the value: the function returns it, from any depth
  of its loops. -/
  | retE
  /-- `let r = for x in V { M }; N`: the loop's value, bound in what follows it as
  `r <- return <forRes>; N` (what the iterator finishes with, or a `break e`). -/
  | forRes
  /-- A string literal `"…"`, its bytes: a `lit`, the persistent value `(n, t)` of its length and
  the function from an index to its byte. -/
  | str (bs : List Nat)
  /-- `with h[A, …](e, …) { S }`: the handler `h` installed over `S` (SPEC §18, §19), with its
  written type arguments, applied to its arguments (a tuple, `()` with none; an answering
  handler's one argument is its state, a value or `&mut c`) and then to the callback whose
  parameter is the capability an answering handler's operations are performed on (`'x` its
  lifetime). `with n = h(…) { S }` names the handler `n` (SPEC §38). Elaborated away by
  `Frontend.Elab.Effects` before the rest of the sugar. -/
  | handle (h : String) (x : String) (targs : List VTy) (name : Option String)
  /-- `n.op`: the operation `op` performed at the handler named `n` (SPEC §38), applied to its
  argument. Elaborated away by `Frontend.Elab.Effects`. -/
  | named (n : String) (op : String)
  /-- A handler site of a control effect (SPEC §19), resolved by `Frontend.Elab.Effects` and
  assembled with its clauses where the types are known (`Frontend.Sugar`): applied to the
  handler's arguments, its return clause, the tuple of its operation clauses and the thunk of its
  body. -/
  | hndCtl (info : HInfo)
  /-- `for x in f(e) { M }`, `f` performing an iteration effect (SPEC §15): the `for`'s source,
  applied to the call of `f`'s copy for the site, whose first argument is the threaded variable. -/
  | forSite (info : ItInfo)
  /-- The stored generator of a call of a function that performs an iteration effect (SPEC §15),
  applied to the call of its copy for the site. -/
  | pullSite (info : ItInfo)
  /-- `e |> s`, applied to the pair of `e` and the stage `s` (SPEC §33): a handler `h(…)` is
  `with h(…) { e }`; a function whose first parameter is a computation parameter takes `e`
  suspended, `f({ () -> e }, …)`; any other function takes `e` first, `f(e, …)`. Elaborated away
  by `Frontend.Elab.Effects`.  `[spec §33]` -/
  | pipe
  /-- `writes(x, …) V`: the closure `V` assigns the enclosing body's `let mut` variables `x, …`
  (SPEC §41, rule R3). It is given at a block parameter of a call, which passes them in and back
  out at each call of it; anywhere else it is refused. Elaborated away by `Frontend.Elab.Effects`.
  `[spec §41]` -/
  | writes (xs : List String)
  /-- `e.f`, applied to the receiver: the field `f` of one of the declarations `cands` that have
  one, the receiver's type choosing which and how it is read (SPEC §42, *Fields*); a receiver
  `&x` is the place `x`, read at a binding `let y = x.f;`, which rebinds it.  `[spec §42]` -/
  | field (f : String) (cands : List FieldCand)
  /-- `x.f = e`'s record rebuilt: applied to the pair of the record `r` and `e`, in which the
  variable `r_g` is the record's field `g`; the record's declaration is one of `cands`, as
  `field`'s.  `[spec §42]` -/
  | update (f : String) (cands : List FieldCand)
  deriving DecidableEq, Repr, Inhabited

/-- What a loop walks, as the program writes it (`docs/loops.md` §2.1), with the loop's value
`V` (`Comp.loop`). Which source an `each` walks, a count, data, a generator's call or a drain,
is decided from `V` and its type. -/
inductive LoopSrc where
  /-- `for x in V`: `V` is the source, and `x` its element, bound in the body. -/
  | each (x : Ident)
  /-- `while V`: `V` is the condition, tested before each turn. -/
  | while_
  /-- `loop`: no source, so the loop ends only by an exit. `V` is `()`. -/
  | forever
  deriving DecidableEq, Repr, Inhabited

/-- The construct a loop is written as: `for`, `while` or `loop`, in backticks, for messages. -/
def LoopSrc.what : LoopSrc → String
  | .each _ => "`for`"
  | .while_ => "`while`"
  | .forever => "`loop`"

/-- The element a loop binds in its body: `for`'s variable. -/
def LoopSrc.var? : LoopSrc → Option Ident
  | .each x => some x
  | _ => none

/-- The name of `for`'s variable, or none. -/
def LoopSrc.bound (s : LoopSrc) : List String := s.var?.toList.map (·.name)

def LoopSrc.strip : LoopSrc → LoopSrc
  | .each x => .each x.strip
  | s => s

/-- A fixed scheme the elaborator writes, recorded on the value it wrote (`Val.mark`): the checker
checks the value as written and builds the scheme's derived node over it (SPEC §3). -/
inductive SchemeMark where
  /-- A string literal's table (SPEC §17): the `!` function from an index to the bytes `bs`. -/
  | litFn (bs : List Nat)
  /-- A division by the literal `c` at which it cannot fail, by the host operation `op`
  (SPEC §39). -/
  | divLit (op : BoCa.HostOp) (c : BoCa.IntLit)
  /-- A counted walk of a view (SPEC §16): `count_try` over the view's length; `m` the view is
  `mut`. -/
  | walk (m : Bool)
  /-- A counted walk's read of its view at its index (SPEC §46): `array_get(v, i)` of the shared
  view's copy at the counter, or `slice_get_mut(h, 0)` of the head a split of one gives; `m` the
  view is `mut`. -/
  | walkGet (m : Bool)
  /-- The record of a recursive group's members, read off its self-reference to call member `j`
  of `n` (SPEC §20). -/
  | selfCall (j n : Nat)
  /-- The lend of a cell allocated for it (SPEC §35): `withbor (alloc v) cb`; `m` the lend is
  `mut`. -/
  | lendCell (m : Bool)
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Value-judged expressions (syntax-core §6.1), checked at a value type. -/
inductive Val where
  /-- A lower-case name: a term variable or a `def` without arguments. -/
  | var (sp : Span) (x : String)
  /-- `clone(x)`: the variable `x`, its use written as an explicit copy (SPEC §10): checked as
  `x`, and its typed node records that the program writes the copy. -/
  | clone (sp : Span) (x : String)
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
  /-- `&mut x` (`mut`) or `&x` (`imm`): lend the place `x` to one call, which hands it back,
  elaborated away before checking (SPEC §11; typed elaboration §5.1). -/
  | lend (sp : Span) (x : Ident) (m : Mode)
  /-- A surface form that needs types, elaborated away before checking. -/
  | sugar (sp : Span) (s : VSugar)
  /-- `V`, a fixed scheme the elaborator wrote, marked `k`: checked as `V`, its typed node the
  scheme's derived node (SPEC §3). It is printed as `V`. -/
  | mark (sp : Span) (k : SchemeMark) (V : Val)
  /-- `reify[B, R, [r]](res)`: the constant `reify_res` of SPEC §14 at the row `r` (which does not
  hold `Div`), making a loop value `U(Loop_r B R)` of a computation at the row `div, r`; `res`,
  a closed value `!U(B ⊸ F_r R)`, hands back the residual of a finished result.  `[spec §14]` -/
  | reify (sp : Span) (B R : VTy) (r : Row) (res : Val)

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
  /-- A loop, `for x in V { M }; N`, `while V { M }; N` or `loop { M }; N` by its source `src`,
  labelled `ℓ` when the program writes `'ℓ:` before it (`docs/loops.md` §2.1, §2.8). An exit
  names the innermost loop. Elaborated away before checking (SPEC §14, §16). -/
  | loop (sp : Span) (ℓ : Option Ident) (src : LoopSrc) (V : Val) (M N : Comp)
  /-- `perform[n.i] V`: the non-abortive operation `i` of the name `n` of the current row
  (`[perform]`).  `[spec §19]` -/
  | perform (sp : Span) (n i : Nat) (V : Val)
  /-- `abort[n.i] V`: the abortive operation `i` of the name `n` (SPEC §19's abortive rule).  `[spec §19]` -/
  | abort (sp : Span) (n i : Nat) (V : Val)
  /-- `handle_with[n](hr, hc) M`: `M` under the handler of the name `n` whose answer clause is
  the value `hr` and whose clauses are the tuple `hc` (`[handle]`), each a value form: the
  elaboration writes both inline, a program may write variables. `site` is the elaboration's
  record of the handler site, with its types in the frame of this node's code; none when the
  program writes the node.  `[spec §19]` -/
  | handle (sp : Span) (n : Nat) (site : Option SiteRec) (hr hc : Val) (M : Comp)
  /-- `x <- M unwind (D); N` (`x : A <- …` with the annotation): `M then x. N unwind D`, the
  finaliser `D` under one dead binder (`[then]`).  `[spec §19]` -/
  | unwind (sp : Span) (x : Ident) (A : Option VTy) (M D N : Comp)
  /-- `withbor2r['x, @b, A, B, [ROW]](p, m) M`: the relaxed lend R1 (SPEC §29). The owned cell
  `p : ref A` is lent as `m : mut 'x A` to `M`, which may perform the resuming operations of the
  row and sees only `m`; its value is `(p, B)`.  `[spec §29]` -/
  | withbor2r (sp : Span) (x : Ident) (b : Life) (A B : VTy) (r : Row) (p m : Ident) (M : Comp)
end

deriving instance DecidableEq for Val, Comp
deriving instance Repr for Val, Comp

/-- A `def`'s effect marker (SPEC §14): none, `total` (it must not loop) or `div` (it loops,
or may one day). Divergence is inferred, so `div` is never needed. -/
inductive Mark where
  | none
  | total
  | div
  /-- `fn f[A, …](…)`: a function generic in types, marked `m` (`none`, `total` or `div`). It is a
  template: each use is a call of its instance at that use's types, elaborated as a `fn`.
  `bounds` are its lifetime bounds `where S: 'c`, a type parameter and a lifetime parameter each.
  `[spec §23]` -/
  | template (m : Mark) (bounds : List (Ident × Ident) := [])
  /-- `fn f(…) -> T with E₁, E₂[A] = …`: a written row (SPEC §18), a promise that the inferred
  row is within it, and gives the type arguments of an effect it performs directly. The function
  is marked `m` besides. `names` are the entries' names, `with src: E` (SPEC §38): empty, or one
  per entry. -/
  | row (effs : List (Ident × List VTy)) (m : Mark) (names : List (Option Ident))
  deriving DecidableEq, Repr, Inhabited

/-- The kind of an operation (SPEC §19): answering (`fn`), or control (`ctl`) with the structural
qualifier of its continuation (`ctl` affine, `linear ctl`, `multi ctl` unrestricted). -/
inductive OpKind where
  | fn
  | ctl (q : Qual)
  deriving DecidableEq, Repr, Inhabited

/-- An operation of an `effect` declaration: `fn op(x₁: A₁, …) -> B` or `ctl op(…) -> B`
(SPEC §18, §19). An answering operation may take lifetime parameters, `fn op<'b, …>(…)`, which its
parameters and its answer may name (SPEC §34). -/
structure OpDecl where
  name : Ident
  params : List (Ident × VTy)
  res : VTy
  kind : OpKind
  lives : List (Ident × Life) := []
  deriving DecidableEq, Repr

/-- A clause of a `handler` declaration: `op(x₁, …) -> { S }`, with the handler's state in scope
in `S` as a `let mut` variable (SPEC §18). -/
structure Clause where
  name : Ident
  params : List Ident
  body : Comp
  deriving DecidableEq, Repr

/-- A handler of a control effect (SPEC §19):
`handler h[T, …](p: A, …) for E[A, …] with E₂[…], … -> R { return(x: A) -> M; op(x, …, k) -> N; … }`.
`k` is the continuation of a non-abortive operation; the handler may perform the operations of
its row `with …`. -/
structure CHandler where
  name : Ident
  tps : List Ident
  params : List (Ident × VTy)
  eff : Ident
  effArgs : List VTy
  row : List (Ident × List VTy)
  res : VTy
  /-- The return clause: its binder, the binder's type, and its body. -/
  ret : Ident × VTy × Comp
  clauses : List Clause
  /-- The lifetime parameters `<'d, …>`, with their bounds: each instantiated at a site at the
  meet of the lifetimes in scope there; a clause that keeps its continuation receives it boxed at
  the first (SPEC §32).  `[spec §32]` -/
  lps : List (Ident × Life) := []
  /-- The parameters written `mut`: `let mut` variables in each clause (SPEC §41). -/
  mutPs : List String := []
  deriving DecidableEq, Repr

/-- Declarations (syntax-core §10). -/
inductive Decl where
  /-- `type N[T, …]<'a, …> = A`: an abbreviation, with type parameters `tps` and lifetime
  parameters `lps` (both empty for `type N = A`), instantiated by substitution at each use.
  `[spec §7]` -/
  | type (sp : Span) (n : Ident) (tps : List Ident) (lps : List Ident) (A : VTy)
  | shape (sp : Span) (n : Ident) (σ : Shape)
  /-- `def name[P₁, …, Pₙ] : A = V`; `params` is empty for `def name : A = V`. `mark` is the
  `total` or `div` written before `def`. -/
  | def_ (sp : Span) (n : Ident) (params : List Ident) (A : VTy) (V : Val) (mark : Mark)
  | extern (sp : Span) (n : Ident) (A : VTy)
  | main (sp : Span) (C : CTy) (M : Comp)
  /-- `include name`: the declarations of the library module `name` (`lib/name.bc`). -/
  | include (sp : Span) (name : Ident)
  /-- `effect E[T, …] { fn op(x: A, …) -> B; ctl op(…) -> B; … }`: an effect, its type
  parameters and its operations (SPEC §18, §19). -/
  | effect (sp : Span) (n : Ident) (tps : List Ident) (ops : List OpDecl)
  /-- `handler h(mut s: S): E = { op(x, …) = { M }; … }`: a handler of `E` whose state is `s : S`
  (SPEC §18). With `lent`, written `handler h(&mut s: S): E = …`, each clause is given the state
  lent, `s : mut 'l S`, which it hands back (SPEC §34). -/
  | handler (sp : Span) (n : Ident) (st : Ident) (S : VTy) (eff : Ident) (clauses : List Clause)
      (lent : Bool)
  /-- A handler of a control effect (SPEC §19). -/
  | chandler (sp : Span) (h : CHandler)
  /-- `poly f[T]<'a, …>(x₁: A₁, …) -> B`: a family of functions, one case per type `T` (`head` is
  `none`; `A` and `V` are the type and the code the `fn` would have, `V`'s body the hole
  `io_poly_body!`). `poly f[P, …]<'h, …> at H = S`: the case of `f` at the type `H` (`head` is
  `some H`; `tps` are the case's type parameters, `lps` the lifetimes `H` names, `V` is
  `thunk S`). An operator's family is named for it, `(+)` as `op_add`.  `[spec §36]` -/
  | poly (sp : Span) (n : Ident) (tps : List Ident) (lps : List Ident) (head : Option VTy)
      (A : VTy) (V : Val)
  /-- A `data` declaration (SPEC §42): elaborated to `type` and `shape` declarations
  (`Frontend.Data.typeDecls`) after the program's modules are in. -/
  | data (sp : Span) (d : DataDecl)
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
  | .arrayMut _ a A => .arrayMut .none a.strip A.strip
  | .sized _ D S A => .sized .none D.strip S.strip A.strip
  | .app _ G A => .app .none G.strip A.strip
  | .lapp _ G a => .lapp .none G.strip a.strip
  | .rowed _ F r => .rowed .none F.strip r.strip

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
  | .pull _ A B R => .pull .none A.strip B.strip R.strip
  | .eff _ r A => .eff .none r.strip A.strip

def Row.strip : Row → Row
  | .nil => .nil
  | .cons n i q A B r => .cons n i q A.strip B.strip r.strip

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
  | .sliceBorrowMut x b A B => .sliceBorrowMut x.strip b.strip A.strip B.strip
  | .sliceBorrowImm x b A B => .sliceBorrowImm x.strip b.strip A.strip B.strip
  | .sliceGetMut a A => .sliceGetMut a.strip A.strip
  | .sliceLenMut a A => .sliceLenMut a.strip A.strip
  | .sliceSplitImm a A => .sliceSplitImm a.strip A.strip
  | .sliceSplitMut a A => .sliceSplitMut a.strip A.strip
  | .sliceEmptyImm a A => .sliceEmptyImm a.strip A.strip
  | .sliceEmptyMut a A => .sliceEmptyMut a.strip A.strip
  | .sliceReplaceMut a A => .sliceReplaceMut a.strip A.strip
  | .sliceSwapMut a A => .sliceSwapMut a.strip A.strip
  | .countFold S => .countFold S.strip
  | .countTry S E => .countTry S.strip E.strip
  | .boundedFix A C => .boundedFix A.strip C.strip
  | .withbor1U x A B r => .withbor1U x.strip A.strip B.strip r.strip
  | .withbor2U x b A B r => .withbor2U x.strip b.strip A.strip B.strip r.strip
  | .withbor3U a x A B r => .withbor3U a.strip x.strip A.strip B.strip r.strip
  | .withloadU a x A B r => .withloadU a.strip x.strip A.strip B.strip r.strip
  | .sliceBorrowMutU x b A B r => .sliceBorrowMutU x.strip b.strip A.strip B.strip r.strip
  | .sliceBorrowImmU x b A B r => .sliceBorrowImmU x.strip b.strip A.strip B.strip r.strip
  | .iterate St B R r => .iterate St.strip B.strip R.strip r.strip

/-- The record with `f` applied to each of its types. -/
def SiteRec.mapTy (f : VTy → VTy) (r : SiteRec) : SiteRec :=
  { r with args := r.args.map f, ents := r.ents.map (fun (q, A, B) => (q, f A, f B)),
           state := r.state.map (fun (x, A) => (x, f A)) }

def SiteRec.strip (r : SiteRec) : SiteRec := r.mapTy VTy.strip

/-- A surface form with the spans of its types erased. -/
def VSugar.strip : VSugar → VSugar
  | .handle h x As n => .handle h x (As.map VTy.strip) n
  | .hndCtl i => .hndCtl { i with
      ents := i.ents.map (fun (q, A, B) => (q, A.strip, B.strip)),
      known := i.known.map (fun (x, A) => (x, A.strip)),
      params := i.params.map (fun (x, A) => (x, A.strip)), retA := i.retA.strip, res := i.res.strip,
      site := i.site.strip }
  | s => s

mutual
def Val.strip : Val → Val
  | .var _ x => .var .none x
  | .clone _ x => .clone .none x
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
  | .lend _ x m => .lend .none x.strip m
  | .sugar _ s => .sugar .none s.strip
  | .mark _ k V => .mark .none k V.strip
  | .reify _ B R r V => .reify .none B.strip R.strip r.strip V.strip

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
  | .loop _ ℓ src V M N => .loop .none (ℓ.map Ident.strip) src.strip V.strip M.strip N.strip
  | .perform _ n i V => .perform .none n i V.strip
  | .abort _ n i V => .abort .none n i V.strip
  | .handle _ n st hr hc M => .handle .none n (st.map SiteRec.strip) hr.strip hc.strip M.strip
  | .unwind _ x A M D N => .unwind .none x.strip (A.map VTy.strip) M.strip D.strip N.strip
  | .withbor2r _ x b A B r p m M =>
      .withbor2r .none x.strip b.strip A.strip B.strip r.strip p.strip m.strip M.strip
end

/-- The lifetime bounds of a template, under its row.  `[spec §23]` -/
def Mark.bounds : Mark → List (Ident × Ident)
  | .template _ bs => bs
  | .row _ m _ => m.bounds
  | _ => []

def Mark.strip : Mark → Mark
  | .template m bs => .template m.strip (bs.map fun (S, c) => (S.strip, c.strip))
  | .row es m ns => .row (es.map fun (e, As) => (e.strip, As.map VTy.strip)) m.strip (ns.map (·.map Ident.strip))
  | m => m

def Decl.strip : Decl → Decl
  | .type _ n ps ls A => .type .none n.strip (ps.map Ident.strip) (ls.map Ident.strip) A.strip
  | .shape _ n σ => .shape .none n.strip σ.strip
  | .def_ _ n ps A V m => .def_ .none n.strip (ps.map Ident.strip) A.strip V.strip m.strip
  | .extern _ n A => .extern .none n.strip A.strip
  | .main _ C M => .main .none C.strip M.strip
  | .include _ n => .include .none n.strip
  | .effect _ n tps ops => .effect .none n.strip (tps.map Ident.strip) (ops.map fun o =>
      ⟨o.name.strip, o.params.map (fun (x, A) => (x.strip, A.strip)), o.res.strip, o.kind,
        o.lives.map fun (a, b) => (a.strip, b.strip)⟩)
  | .handler _ n st S e cs l => .handler .none n.strip st.strip S.strip e.strip (cs.map fun c =>
      ⟨c.name.strip, c.params.map Ident.strip, c.body.strip⟩) l
  | .chandler _ h => .chandler .none
      { name := h.name.strip, tps := h.tps.map Ident.strip,
        params := h.params.map (fun (x, A) => (x.strip, A.strip)), eff := h.eff.strip,
        effArgs := h.effArgs.map VTy.strip, row := h.row.map (fun (e, As) => (e.strip, As.map VTy.strip)),
        res := h.res.strip, ret := (h.ret.1.strip, h.ret.2.1.strip, h.ret.2.2.strip),
        clauses := h.clauses.map fun c => ⟨c.name.strip, c.params.map Ident.strip, c.body.strip⟩,
        lps := h.lps.map fun (a, b) => (a.strip, b.strip) }
  | .poly _ n tps lps H A V => .poly .none n.strip (tps.map Ident.strip) (lps.map Ident.strip)
      (H.map VTy.strip) A.strip V.strip
  | .data _ d => .data .none (DataDecl.mk d.name.strip (d.tps.map Ident.strip) (d.lps.map Ident.strip)
      d.record (d.cons.map fun c => DCon.mk c.name.strip (c.fields.map fun f => DField.mk (f.name.map Ident.strip) f.ty.strip)))

def Program.strip (p : Program) : Program := ⟨p.decls.map Decl.strip⟩

/-- The span of a value-judged expression. -/
def Val.span : Val → Span
  | .var sp _ | .clone sp _ | .defApp sp _ _ | .unit sp | .pair sp _ _ | .inl sp _ | .inr sp _
  | .thunk sp _ | .thunkv sp _ | .bangThunk sp _ | .bangThunkv sp _ | .unbang sp _
  | .boxed sp _ _ | .unbox sp _ | .sub sp _ _ | .roll sp _ | .unroll sp _ | .run sp _
  | .app sp _ _ | .inst sp _ _ | .ascribe sp _ _ | .const sp _ | .shorten sp _ _ _ _
  | .lend sp _ _ | .sugar sp _ | .mark sp _ _ | .reify sp _ _ _ _ => sp

/-- The span of a computation. -/
def Comp.span : Comp → Span
  | .ret sp _ | .bind sp _ _ _ _ _ | .force sp _ | .lam sp _ _ _ | .app sp _ _ | .with_ sp _ _
  | .proj sp _ _ | .top sp | .letUnit sp _ _ | .letPair sp _ _ _ _ | .case sp _ _ _ _ _
  | .absurd sp _ | .lamL sp _ _ _ | .inst sp _ _ | .nuIn sp _ | .nuOut sp _
  | .ascribe sp _ _ | .loop sp _ _ _ _ _ | .perform sp _ _ _ | .abort sp _ _ _ | .handle sp _ _ _ _ _
  | .unwind sp _ _ _ _ _ | .withbor2r sp _ _ _ _ _ _ _ _ => sp

def Life.span : Life → Span
  | .var sp _ | .top sp | .dom sp | .meet sp _ _ | .join sp _ _ => sp

def VTy.span : VTy → Span
  | .unit sp | .zero sp | .tensor sp _ _ | .sum sp _ _ | .thunk sp _ | .ref sp _ | .imm sp _ _
  | .mut sp _ _ | .box sp _ _ | .bang sp _ | .unk sp | .int sp _ | .handle sp _ | .mu sp _ _ | .name sp _
  | .lolli sp _ _ | .all sp _ _ _ | .block sp _ | .val sp _ | .fam sp _ _ _ | .view sp _ _
  | .array sp _ | .arrayImm sp _ _ | .arrayMut sp _ _ | .sized sp _ _ _ | .app sp _ _
  | .lapp sp _ _ | .rowed sp _ _ => sp

def CTy.span : CTy → Span
  | .ret sp _ | .arr sp _ _ | .amp sp _ _ | .top sp | .all sp _ _ _ | .nu sp _ _ | .name sp _
  | .delay sp _ | .stream sp _ | .iter sp _ _ _ | .loop sp _ _ | .pull sp _ _ _ | .eff sp _ _ => sp

def Shape.span : Shape → Span
  | .leaf sp _ | .node sp _ _ | .name sp _ => sp

/-- An effect instance of a provided row (`VTy.rowed`): the effect's name applied to its type
arguments. -/
def VTy.effInst : VTy → Option (Ident × List VTy)
  | .name sp e => some (⟨e, sp⟩, [])
  | .app _ G A => (G.effInst).map fun (e, As) => (e, As ++ [A])
  | _ => none

/-- The effect instances of a provided row (`VTy.rowed`): the arguments of its application to the
empty name, in order. -/
def VTy.rowEffs : VTy → List (Ident × List VTy)
  | .app _ G A => G.rowEffs ++ A.effInst.toList
  | _ => []

/-- A provided row from its effect instances: the inverse of `VTy.rowEffs`. -/
def VTy.ofRowEffs (sp : Span) (es : List (Ident × List VTy)) : VTy :=
  es.foldl (fun R (e, As) => .app sp R (As.foldl (fun G A => .app sp G A) (.name e.span e.name)))
    (.name sp "")

mutual
/-- A surface leaf satisfying `p` in a value. -/
def Val.anySugar (p : VSugar → Bool) : Val → Bool
  | .sugar _ s => p s
  | .pair _ V W | .app _ V W => V.anySugar p || W.anySugar p
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V | .reify _ _ _ _ V => V.anySugar p
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.anySugar p
  | _ => false

/-- A surface leaf satisfying `p` in a computation. -/
def Comp.anySugar (p : VSugar → Bool) : Comp → Bool
  | .ret _ V | .absurd _ V => V.anySugar p
  | .bind _ _ _ M N _ | .with_ _ M N => M.anySugar p || N.anySugar p
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.anySugar p
  | .letUnit _ V M | .letPair _ _ _ V M => V.anySugar p || M.anySugar p
  | .case _ V _ M _ N => V.anySugar p || M.anySugar p || N.anySugar p
  | .loop _ _ _ V M N => V.anySugar p || M.anySugar p || N.anySugar p
  | .perform _ _ _ V | .abort _ _ _ V => V.anySugar p
  | .handle _ _ _ hr hc M => hr.anySugar p || hc.anySugar p || M.anySugar p
  | .unwind _ _ _ M D N => M.anySugar p || D.anySugar p || N.anySugar p
  | .withbor2r _ _ _ _ _ _ _ _ M => M.anySugar p
  | .force .. | .top _ => false
end

/-- The variable a value copies, up to an ascription or a clone: `a`, `(a : T)`, `clone a`. A
binding `x <- return V` of such a value is a copy: what the elaboration identifies by a binder
(a borrow, a block parameter, a continuation, a residual) it follows through copies, never by a
name (SPEC §41, #617). -/
def Val.copyOf? : Val → Option String
  | .var _ a | .clone _ a => some a
  | .ascribe _ V _ => V.copyOf?
  | _ => none

end Frontend
