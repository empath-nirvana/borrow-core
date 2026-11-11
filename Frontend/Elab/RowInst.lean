import Frontend.Elab.Effects

/-!
# Frontend — Elab — instances of definitions generic over rows and sites  `[spec §76]`

A `def name[A, row r, site s] : T = V` or a `type N[A, row r, site s] = T` (`Decl.gen`) is a
template. Each use writes its arguments, `f[T, row (ROW), site k]`, and is an instance made by
substitution: the template's types, rows (`..r`, `Row.var`) and sites (`siteOfName`) replaced by
the use's. The checker sees only instances, each a plain `def`, and the kernel nothing new.

* **An instance** of a `def` is named `f__r{k}`, `k` counting `f`'s instances from 1, and keyed by
  its type arguments, its row arguments and its public site arguments. It is made once and shared
  by the uses with its key. Its type parameters are those of the code it is used in that its
  arguments mention, passed on at the use.
* **The pure use**, every row argument `()` and no site parameter, is the definition as written:
  named `f`, its type parameters kept for the checker.
* **A private site**, a site parameter the template's type does not mention, is never written:
  each instance takes a fresh site: at or above the effects pass's next site, which it reads from
  that pass's result, and above every literal site of the program.
* **A `type`** with row or site parameters is expanded at each use, in a `shape` too.
* **A template's body is core text:** a surface form in it is refused.

Refused, at the use, naming the template: a row argument under which the template's body performs
an operation its instance's type does not have; a row argument that gives an operation a second
signature; a row argument naming a lifetime; a row argument not written (inferring it is slice
2). Refused, needing a row binder in the kernel (decision 62's row variables), which Core does not
have: polymorphic recursion over rows. A definition checked once for all rows is refused by the
parser (`..r` with no row parameter `r`). An error the checker finds inside an instance names the
instance, its template and its use (`Origin.rowInst`).

The pass runs after `Frontend.Elab.Effects`. It is the identity on a program with no template.
-/

namespace Frontend.Elab.RowInst

open Frontend

/-- The kernel row binder a refused form needs.  `[spec §76]` -/
def needsBinder : String :=
  "it needs a row binder in the kernel (decision 62's row variables), which Core does not have " ++
  "(SPEC §76 *Open*)"

/-- A template: a `def` (`val`, `mark`) or a `type` (`isType`) with its type parameters, row
parameters and site parameters, and its type (for a `type`, its body). -/
structure Tmpl where
  sp : Span
  name : String
  tps : List String
  rows : List String
  sites : List String
  isType : Bool
  ty : VTy
  val : Val := .unit .none
  mark : Mark := .none

/-- The templates of a program. -/
def templates (ds : List Decl) : List Tmpl :=
  ds.filterMap fun
    | .gen sp rs ss (.def_ _ n ps A V mk) =>
      some { sp, name := n.name, tps := ps.map (·.name), rows := rs.map (·.name),
             sites := ss.map (·.name), isType := false, ty := A, val := V, mark := mk }
    | .gen sp rs ss (.type _ n ps _ A) =>
      some { sp, name := n.name, tps := ps.map (·.name), rows := rs.map (·.name),
             sites := ss.map (·.name), isType := true, ty := A }
    | _ => none

/-! ### Sites and operations a term names -/

mutual
/-- The operations `n.i` of the rows a type writes; `n` alone (`i = 0`) for a site argument. -/
def _root_.Frontend.VTy.ents : VTy → List (Nat × Nat)
  | .tensor _ A B | .sum _ A B | .lolli _ A B | .app _ A B => A.ents ++ B.ents
  | .thunk _ C => C.ents
  | .ref _ A | .imm _ _ A | .mut _ _ A | .box _ _ A | .bang _ A | .view _ _ A | .array _ A
  | .arrayImm _ _ A | .arrayMut _ _ A | .lapp _ A _ | .all _ _ _ A | .mu _ _ A => A.ents
  | .sized _ D S A => D.ents ++ S.ents ++ A.ents
  | .rowed _ F r => F.ents ++ r.ents
  | .rowArg _ r => r.ents
  | .siteArg _ n => [(n, 0)]
  | .block _ σ | .val _ σ | .fam _ _ _ σ => σ.ents
  | _ => []

def _root_.Frontend.CTy.ents : CTy → List (Nat × Nat)
  | .ret _ A | .delay _ A | .stream _ A => A.ents
  | .arr _ A C => A.ents ++ C.ents
  | .amp _ C D => C.ents ++ D.ents
  | .all _ _ _ C | .nu _ _ C => C.ents
  | .iter _ A R R' | .pull _ A R R' => A.ents ++ R.ents ++ R'.ents
  | .loop _ A B => A.ents ++ B.ents
  | .eff _ r A => r.ents ++ A.ents
  | _ => []

def _root_.Frontend.Row.ents : Row → List (Nat × Nat)
  | .cons n i _ A B f r => (n, i) :: (A.ents ++ B.ents ++ f.ents ++ r.ents)
  | .splice _ r => r.ents
  | _ => []

def _root_.Frontend.Shape.ents : Shape → List (Nat × Nat)
  | .leaf _ A => A.ents
  | .node _ σ τ => σ.ents ++ τ.ents
  | .name _ _ => []
end

/-- The operations a constant's bracket arguments write.  `[spec §76]` -/
def constEnts (k : Const) : List (Nat × Nat) :=
  k.toArgs.2.flatMap fun
    | .ty A => A.ents
    | .cty C => C.ents
    | .shape σ => σ.ents
    | .row r => r.ents
    | _ => []

mutual
/-- The sites a term names: each `(true, n, i)` an operation it performs at a site `n` no handler
of the term installs, each `(false, n, i)` any other (a handler's site, an annotation's row). -/
def _root_.Frontend.Val.sitesIn (h : List Nat) : Val → List (Bool × Nat × Nat)
  | .defApp _ _ As => As.flatMap fun A => A.ents.map ((false, ·))
  | .pair _ V W | .app _ V W => V.sitesIn h ++ W.sitesIn h
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .shorten _ _ _ _ V | .mark _ _ V => V.sitesIn h
  | .ascribe _ V A => V.sitesIn h ++ A.ents.map ((false, ·))
  | .const _ k => (constEnts k).map ((false, ·))
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.sitesIn h
  | _ => []

def _root_.Frontend.Comp.sitesIn (h : List Nat) : Comp → List (Bool × Nat × Nat)
  | .ret _ V | .absurd _ V => V.sitesIn h
  | .bind _ _ A M N =>
    ((A.map VTy.ents).getD []).map ((false, ·)) ++ M.sitesIn h ++ N.sitesIn h
  | .lam _ _ A M => A.ents.map ((false, ·)) ++ M.sitesIn h
  | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M => M.sitesIn h
  | .with_ _ M N => M.sitesIn h ++ N.sitesIn h
  | .letUnit _ V M | .letPair _ _ _ V M => V.sitesIn h ++ M.sitesIn h
  | .case _ V _ M _ N | .loop _ _ _ V M N => V.sitesIn h ++ M.sitesIn h ++ N.sitesIn h
  | .ascribe _ M C => M.sitesIn h ++ C.ents.map ((false, ·))
  | .perform _ n i V | .abort _ n i V => (!h.contains n, n, i) :: V.sitesIn h
  | .handle _ n _ hr hc M => (false, n, 0) :: (hr.sitesIn h ++ hc.sitesIn h ++ M.sitesIn (n :: h))
  | .unwind _ _ A M D N =>
    ((A.map VTy.ents).getD []).map ((false, ·)) ++ M.sitesIn h ++ D.sitesIn h ++ N.sitesIn h
  | .withbor2r _ _ _ A B r _ _ M =>
    (A.ents ++ B.ents ++ r.ents).map ((false, ·)) ++ M.sitesIn h
  | _ => []
end

/-- The largest literal site a declaration names (a site parameter's number is not one). -/
def _root_.Frontend.Decl.maxSite (d : Decl) : Nat :=
  let ns : List Nat := match d with
    | .def_ _ _ _ A V _ => A.ents.map (·.1) ++ (V.sitesIn []).map (·.2.1)
    | .main _ C M => C.ents.map (·.1) ++ (M.sitesIn []).map (·.2.1)
    | .extern _ _ A | .type _ _ _ _ A => A.ents.map (·.1)
    | .shape _ _ σ => σ.ents.map (·.1)
    | _ => []
  (ns.filter (· < 2 ^ 32)).foldl max 0

mutual
/-- The span of a surface form in a term, elaborated by the passes before the instances are made
(`Val.sugar`, `&x`, loops): none in core text.  `[spec §76]` -/
def _root_.Frontend.Val.surface? : Val → Option Span
  | .sugar sp _ | .lend sp _ _ => some sp
  | .pair _ V W | .app _ V W => V.surface? <|> W.surface?
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .shorten _ _ _ _ V | .mark _ _ V | .ascribe _ V _ => V.surface?
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.surface?
  | _ => none

/-- The span of a surface form in a computation (`Val.surface?`).  `[spec §76]` -/
def _root_.Frontend.Comp.surface? : Comp → Option Span
  | .loop sp .. => some sp
  | .ret _ V | .absurd _ V => V.surface?
  | .bind _ _ _ M N | .with_ _ M N => M.surface? <|> N.surface?
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ | .withbor2r _ _ _ _ _ _ _ _ M => M.surface?
  | .letUnit _ V M | .letPair _ _ _ V M => V.surface? <|> M.surface?
  | .case _ V _ M _ N => V.surface? <|> M.surface? <|> N.surface?
  | .perform _ _ _ V | .abort _ _ _ V => V.surface?
  | .handle _ _ _ hr hc M => hr.surface? <|> hc.surface? <|> M.surface?
  | .unwind _ _ _ M D N => M.surface? <|> D.surface? <|> N.surface?
  | _ => none
end

/-! ### Substitution -/

/-- An instance made: its name, and the type parameters of the code it was made for that its
uses pass on. -/
structure Inst where
  name : String
  tps : List String

structure St where
  /-- The instances made, by their keys: the template's name and the use's arguments. -/
  insts : List ((String × List VTy) × Inst) := []
  /-- The number of instances made of each template. -/
  count : List (String × Nat) := []
  /-- The next fresh site. -/
  site : Nat
  /-- The instances made since the last declaration was emitted, each after those it uses. -/
  out : Array Decl := #[]
  /-- Each instance made: its name, its template's, and the use it was made for. -/
  made : Array (String × String × Span) := #[]

abbrev M := StateT St (Except Error)

/-- What a substitution is under: the templates, the type parameters, rows and sites substituted,
the type parameters of the code it is in, and the templates being instantiated, innermost first,
each with the use that asked for it. -/
structure Cx where
  tmpls : List Tmpl
  tys : TySubst := []
  rows : List (String × Row) := []
  sites : List (Nat × Nat) := []
  tps : List String := []
  stack : List (String × Span) := []

def Cx.site (c : Cx) (n : Nat) : Nat := (c.sites.lookup n).getD n

def Cx.tmpl? (c : Cx) (x : String) (isType : Bool) : Option Tmpl :=
  c.tmpls.find? fun t => t.name == x && t.isType == isType

/-- An entry of a row being instantiated, `n.i q[f] A ~> B` as a one-entry row, with where it came
from: written in the template (`true`) or spliced from a row argument (`false`).  `[spec §76]` -/
abbrev REnt := Bool × Row

/-- A row argument's entries, each spliced (`false`), and its tail. -/
def splicedOf : Row → List REnt × Row
  | .cons n i q A B f r => let (es, t) := splicedOf r; ((false, .cons n i q A B f .nil) :: es, t)
  | t => ([], t)

/-- Entries ahead of a tail, as a row. -/
def toRow : List REnt → Row → Row
  | [], t => t
  | (_, .cons n i q A B f _) :: es, t => .cons n i q A B f (toRow es t)
  | _ :: es, t => toRow es t

/-- A row's entries in written order, merged as SPEC §76 says: a written entry and a spliced one with
the same signature are one entry (§38), the first kept; repeats from two splices, within one
argument, or of two written entries are kept, since a row is a list whose repeats are significant (a
continuation's cancel branch is `fin ++ Σ`, read back by its length, §27). An operation given two
signatures anywhere in the row is refused.  `[spec §76]` -/
def mergeEnts (sp : Span) (who : String) : List (Bool × Nat × Nat × Row) → List REnt →
    Except Error (List REnt)
  | _, [] => pure []
  | seen, (w, e) :: es => match e with
    | .cons n i _ _ _ _ _ => do
      let key := e.strip
      if seen.any fun (_, n', i', k) => n' == n && i' == i && k != key then
        throw ⟨sp, s!"the row argument of `{who}` gives `{sitePp n}.{i}` a second signature"⟩
      if seen.any fun (w', n', i', _) => w' != w && n' == n && i' == i then
        mergeEnts sp who seen es
      else
        pure ((w, e) :: (← mergeEnts sp who ((w, n, i, key) :: seen) es))
    | _ => mergeEnts sp who seen es

/-- The type arguments, row arguments and site arguments of a use, each in order. -/
def splitArgs (As : List VTy) : List VTy × List Row × List Nat :=
  (As.filter fun | .rowArg .. | .siteArg .. => false | _ => true,
   As.filterMap fun | .rowArg _ r => some r | _ => none,
   As.filterMap fun | .siteArg _ n => some n | _ => none)

/-- The lifetimes a row's entries name. -/
def rowLives : Row → List String
  | .cons _ _ _ A B f r => A.lifeVars ++ B.lifeVars ++ rowLives f ++ rowLives r
  | .splice _ r => rowLives r
  | _ => []

/-- The fuel of a substitution: its depth in a term. -/
def fuel : Nat := 1000000

/-- How deep instances may be made inside instances. -/
def maxDepth : Nat := 64

mutual
def substV : Nat → Cx → VTy → M VTy
  | 0, _, A => throw ⟨A.span, "a type nested too deeply"⟩
  | n + 1, c, A => match A with
    | .unit sp => pure (.unit sp)
    | .zero sp => pure (.zero sp)
    | .tensor sp A B => return .tensor sp (← substV n c A) (← substV n c B)
    | .sum sp A B => return .sum sp (← substV n c A) (← substV n c B)
    | .thunk sp C => return .thunk sp (← substC n c C)
    | .ref sp A => return .ref sp (← substV n c A)
    | .imm sp a A => return .imm sp a (← substV n c A)
    | .mut sp a A => return .mut sp a (← substV n c A)
    | .box sp a A => return .box sp a (← substV n c A)
    | .bang sp A => return .bang sp (← substV n c A)
    | .unk sp => pure (.unk sp)
    | .int sp w => pure (.int sp w)
    | .handle sp o => pure (.handle sp o)
    | .mu sp X A => return .mu sp X (← substV n { c with tys := c.tys.filter (·.1 != X.name) } A)
    | .name sp x =>
      match c.tys.lookup x with
      | some T => pure T
      | none =>
        if (c.tmpl? x true).isSome then
          throw ⟨sp, s!"the type `{x}` has row or site parameters: write its arguments, " ++
            s!"`{x}[…, row (…)]` (SPEC §76)"⟩
        else pure (.name sp x)
    | .lolli sp A B => return .lolli sp (← substV n c A) (← substV n c B)
    | .all sp x b A => return .all sp x b (← substV n c A)
    | .block sp σ => return .block sp (← substS n c σ)
    | .val sp σ => return .val sp (← substS n c σ)
    | .fam sp m a σ => return .fam sp m a (← substS n c σ)
    | .view sp a A => return .view sp a (← substV n c A)
    | .array sp A => return .array sp (← substV n c A)
    | .arrayImm sp a A => return .arrayImm sp a (← substV n c A)
    | .arrayMut sp a A => return .arrayMut sp a (← substV n c A)
    | .sized sp D S A => return .sized sp (← substV n c D) (← substV n c S) (← substV n c A)
    | .app sp G B =>
      match A.spine with
      | some (x, As, []) =>
        match c.tmpl? x true with
        | some t => do expandTy n c sp t (← As.mapM (substV n c))
        | none => return .app sp (← substV n c G) (← substV n c B)
      | _ => return .app sp (← substV n c G) (← substV n c B)
    | .lapp sp G a => return .lapp sp (← substV n c G) a
    | .rowed sp G r => return .rowed sp (← substV n c G) (← substV n c r)
    | .rowArg sp r => return .rowArg sp (← substR n c sp r)
    | .siteArg sp k => pure (.siteArg sp (c.site k))

/-- The use `N[As]` of the `type` template `t`, its arguments substituted: `t`'s body at them. -/
def expandTy : Nat → Cx → Span → Tmpl → List VTy → M VTy
  | 0, _, sp, _, _ => throw ⟨sp, "a type nested too deeply"⟩
  | n + 1, c, sp, t, As => do
    let (Ts, Rs, Ss) := splitArgs As
    unless Ts.length == t.tps.length && Rs.length == t.rows.length && Ss.length == t.sites.length do
      throw ⟨sp, s!"the type `{t.name}` takes {t.tps.length} type argument(s), " ++
        s!"{t.rows.length} row argument(s) `row (…)` and {t.sites.length} site argument(s) `site k`"⟩
    if c.stack.length ≥ maxDepth then
      throw ⟨sp, s!"the type `{t.name}` is expanded inside itself without end"⟩
    substV n { c with tys := t.tps.zip Ts, rows := t.rows.zip Rs,
                      sites := (t.sites.map siteOfName).zip Ss,
                      stack := (t.name, sp) :: c.stack } t.ty

def substC : Nat → Cx → CTy → M CTy
  | 0, _, C => throw ⟨C.span, "a type nested too deeply"⟩
  | n + 1, c, C => match C with
    | .ret sp A => return .ret sp (← substV n c A)
    | .arr sp A C => return .arr sp (← substV n c A) (← substC n c C)
    | .amp sp C D => return .amp sp (← substC n c C) (← substC n c D)
    | .top sp => pure (.top sp)
    | .all sp x b C => return .all sp x b (← substC n c C)
    | .nu sp X C => return .nu sp X (← substC n c C)
    | .name sp x => pure (.name sp x)
    | .delay sp A => return .delay sp (← substV n c A)
    | .stream sp A => return .stream sp (← substV n c A)
    | .iter sp A R R' => return .iter sp (← substV n c A) (← substV n c R) (← substV n c R')
    | .loop sp A B => return .loop sp (← substV n c A) (← substV n c B)
    | .pull sp A B R => return .pull sp (← substV n c A) (← substV n c B) (← substV n c R)
    | .eff sp r A => return .eff sp (← substR n c sp r) (← substV n c A)

/-- A row with its row parameters and its sites substituted, its entries merged as SPEC §76 says
(`mergeEnts`).  `[spec §76]` -/
def substR : Nat → Cx → Span → Row → M Row
  | 0, _, sp, _ => throw ⟨sp, "a row nested too deeply"⟩
  | n + 1, c, sp, r => do
    let (es, t) ← substEnts n c sp r
    if c.rows.isEmpty then pure (toRow es t) else
      match mergeEnts ((c.stack.head?.map (·.2)).getD sp) ((c.stack.head?.map (·.1)).getD "") [] es with
      | .ok es => pure (toRow es t)
      | .error e => throw e

/-- A row's entries substituted, each with where it came from (`REnt`), and its tail: each `..r`
replaced by `r`'s argument, spliced in written order.  `[spec §76]` -/
def substEnts : Nat → Cx → Span → Row → M (List REnt × Row)
  | 0, _, sp, _ => throw ⟨sp, "a row nested too deeply"⟩
  | n + 1, c, sp, r => match r with
    | .cons k i q A B f r => do
      let f' ← match f with
        | .top => pure .top
        | f => substR n c sp f
      let e : Row := .cons (c.site k) i q (← substV n c A) (← substV n c B) f' .nil
      let (es, t) ← substEnts n c sp r
      return ((true, e) :: es, t)
    | .nil => pure ([], .nil)
    | .top => pure ([], .top)
    | .var x => match c.rows.lookup x with
      | some a => pure (splicedOf a)
      | none => pure ([], .var x)
    | .splice x r => do
      let (es, t) ← substEnts n c sp r
      match c.rows.lookup x with
      | some a =>
        let (as, ta) := splicedOf a
        unless ta == .nil do
          throw ⟨sp, s!"`..{x}` is spliced ahead of more entries, so its argument is a list of entries"⟩
        pure (as ++ es, t)
      | none => pure ([], .splice x (toRow es t))

def substS : Nat → Cx → Shape → M Shape
  | 0, _, σ => throw ⟨σ.span, "a shape nested too deeply"⟩
  | n + 1, c, σ => match σ with
    | .leaf sp A => return .leaf sp (← substV n c A)
    | .node sp σ τ => return .node sp (← substS n c σ) (← substS n c τ)
    | .name sp x => pure (.name sp x)

def substConst : Nat → Cx → Span → Const → M Const
  | 0, _, sp, _ => throw ⟨sp, "a term nested too deeply"⟩
  | n + 1, c, sp, k => do
    let (kw, as) := k.toArgs
    let as' ← as.mapM fun
      | .ty A => return Arg.ty (← substV n c A)
      | .cty C => return .cty (← substC n c C)
      | .shape σ => return .shape (← substS n c σ)
      | .row r => return .row (← substR n c sp r)
      | a => pure a
    pure ((Const.ofArgs kw as').getD k)

def substVal : Nat → Cx → Val → M Val
  | 0, _, V => throw ⟨V.span, "a term nested too deeply"⟩
  | n + 1, c, V => match V with
    | .var sp x =>
      match c.tmpl? x false with
      | some t => use n c sp t [] true
      | none => pure (.var sp x)
    | .clone sp x => return .clone sp (← ident n c ⟨x, sp⟩).name
    | .defApp sp x As => do
      let As' ← As.mapM (substV n c)
      match c.tmpl? x false with
      | some t => use n c sp t As' false
      | none => pure (.defApp sp x As')
    | .unit sp => pure (.unit sp)
    | .pair sp V W => return .pair sp (← substVal n c V) (← substVal n c W)
    | .inl sp V => return .inl sp (← substVal n c V)
    | .inr sp V => return .inr sp (← substVal n c V)
    | .thunk sp M => return .thunk sp (← substComp n c M)
    | .thunkv sp M => return .thunkv sp (← substComp n c M)
    | .bangThunk sp M => return .bangThunk sp (← substComp n c M)
    | .bangThunkv sp M => return .bangThunkv sp (← substComp n c M)
    | .unbang sp V => return .unbang sp (← substVal n c V)
    | .boxed sp a V => return .boxed sp a (← substVal n c V)
    | .unbox sp V => return .unbox sp (← substVal n c V)
    | .sub sp V a => return .sub sp (← substVal n c V) a
    | .roll sp V => return .roll sp (← substVal n c V)
    | .unroll sp V => return .unroll sp (← substVal n c V)
    | .run sp M => return .run sp (← substComp n c M)
    | .app sp V W => return .app sp (← substVal n c V) (← substVal n c W)
    | .inst sp V a => return .inst sp (← substVal n c V) a
    | .ascribe sp V A => return .ascribe sp (← substVal n c V) (← substV n c A)
    | .const sp k => return .const sp (← substConst n c sp k)
    | .shorten sp m σ a V => return .shorten sp m (← substS n c σ) a (← substVal n c V)
    | .lend sp x m => return .lend sp (← ident n c x) m
    -- A form the effects pass left for the sugar: its types substituted.
    | .sugar sp s => pure ((Val.sugar sp s).subst c.tys)
    | .mark sp k V => return .mark sp k (← substVal n c V)

def substComp : Nat → Cx → Comp → M Comp
  | 0, _, M => throw ⟨M.span, "a term nested too deeply"⟩
  | n + 1, c, M => match M with
    | .ret sp V => return .ret sp (← substVal n c V)
    | .bind sp x A M N => do
      let A' ← match A with
        | some A => some <$> substV n c A
        | none => pure none
      return .bind sp x A' (← substComp n c M) (← substComp n c N)
    | .force sp x => return .force sp (← ident n c x)
    | .lam sp x A M => return .lam sp x (← substV n c A) (← substComp n c M)
    | .app sp M x => return .app sp (← substComp n c M) (← ident n c x)
    | .with_ sp M N => return .with_ sp (← substComp n c M) (← substComp n c N)
    | .proj sp i M => return .proj sp i (← substComp n c M)
    | .top sp => pure (.top sp)
    | .letUnit sp V M => return .letUnit sp (← substVal n c V) (← substComp n c M)
    | .letPair sp x y V M => return .letPair sp x y (← substVal n c V) (← substComp n c M)
    | .case sp V x M y N =>
      return .case sp (← substVal n c V) x (← substComp n c M) y (← substComp n c N)
    | .absurd sp V => return .absurd sp (← substVal n c V)
    | .lamL sp x b M => return .lamL sp x b (← substComp n c M)
    | .inst sp M a => return .inst sp (← substComp n c M) a
    | .nuIn sp M => return .nuIn sp (← substComp n c M)
    | .nuOut sp M => return .nuOut sp (← substComp n c M)
    | .ascribe sp M C => return .ascribe sp (← substComp n c M) (← substC n c C)
    | .loop sp ℓ src V M N =>
      return .loop sp ℓ src (← substVal n c V) (← substComp n c M) (← substComp n c N)
    | .perform sp k i V => return .perform sp (c.site k) i (← substVal n c V)
    | .abort sp k i V => return .abort sp (c.site k) i (← substVal n c V)
    | .handle sp k st hr hc M =>
      return .handle sp (c.site k) (st.map (SiteRec.mapTy (VTy.subst c.tys)))
        (← substVal n c hr) (← substVal n c hc) (← substComp n c M)
    | .unwind sp x A M D N => do
      let A' ← match A with
        | some A => some <$> substV n c A
        | none => pure none
      return .unwind sp x A' (← substComp n c M) (← substComp n c D) (← substComp n c N)
    | .withbor2r sp x b A B r p m M =>
      return .withbor2r sp x b (← substV n c A) (← substV n c B) (← substR n c sp r) p m
        (← substComp n c M)

/-- A name an application or a `force` takes: a template's bare use, its instance's name.
`[spec §76]` -/
def ident : Nat → Cx → Ident → M Ident
  | 0, _, x => pure x
  | n + 1, c, x => match c.tmpl? x.name false with
    | some t => do
      match ← use n c x.span t [] true with
      | .var _ y => pure { x with name := y }
      | _ => throw ⟨x.span, s!"internal error: the instance of `{t.name}` is not a name"⟩
    | none => pure x

/-- The use at `sp` of the `def` template `t` with the arguments `As`, substituted already
(`bare` when it is written with no brackets): a use of its instance, made when it is new.
`[spec §76]` -/
def use : Nat → Cx → Span → Tmpl → List VTy → Bool → M Val
  | 0, _, sp, _, _, _ => throw ⟨sp, "a term nested too deeply"⟩
  | n + 1, c, sp, t, As, bare => do
    let (Ts, Rs, Ss) := splitArgs As
    -- A site the template's type mentions is public, written at each use; any other private.
    let mentions (s : String) : Bool := t.ty.ents.any (·.1 == siteOfName s)
    let pub := t.sites.filter mentions
    let priv := t.sites.filter (!mentions ·)
    if bare && !(t.tps.isEmpty && t.rows.isEmpty && pub.isEmpty) then
      throw ⟨sp, s!"`{t.name}` is used without its arguments: its row and site arguments are " ++
        s!"written at each use, `{t.name}[…, row (…)]`; reading them off the call is not built " ++
        "in slice 1 (SPEC §76)"⟩
    if Rs.length < t.rows.length then
      throw ⟨sp, s!"`{t.name}` takes {t.rows.length} row argument(s) `row (…)`, and this use " ++
        s!"writes {Rs.length}: reading a row argument off the call is not built in slice 1 " ++
        "(SPEC §76)"⟩
    unless Ts.length == t.tps.length && Rs.length == t.rows.length && Ss.length == pub.length do
      throw ⟨sp, s!"`{t.name}` takes {t.tps.length} type argument(s), {t.rows.length} row " ++
        s!"argument(s) `row (…)` and {pub.length} site argument(s) `site k`" ++
        (if priv.isEmpty then "" else
          s!" (its site(s) {", ".intercalate (priv.map (s!"`{·}`"))} are its own, not written)")⟩
    -- Lifetimes in a row argument would be the instance's lifetime parameters (slice 2).
    for r in Rs do
      unless (rowLives r).isEmpty do
        throw ⟨sp, s!"a row argument of `{t.name}` names a lifetime: not provided (SPEC §76, " ++
          "slice 1)"⟩
    let isPure := Rs.all (· == .nil) && t.sites.isEmpty
    -- The type parameters of the code it is used in that its arguments mention: the instance's
    -- own, and part of its key, so that a parameter `T` and a global type `T` are two keys.
    let tps := if isPure then t.tps else
      c.tps.filter fun x => As.any fun A => A.subst [(x, .zero .none)] != A
    let key : String × List VTy :=
      (t.name, if isPure then [] else As.map VTy.strip ++ tps.map (VTy.name .none))
    let ref (i : Inst) : Val :=
      let args := if isPure then Ts else i.tps.map (VTy.name sp)
      if args.isEmpty then .var sp i.name else .defApp sp i.name args
    if let some i := (← get).insts.lookup key then return ref i
    -- A new instance of a template being instantiated: polymorphic recursion.
    if let some (_, sp₀) := c.stack.find? (·.1 == t.name) then
      throw ⟨sp, s!"`{t.name}` is used inside its own instance at other arguments " ++
        s!"({", ".intercalate (As.map (VTy.pp · 0))}; the instance was asked for at " ++
        s!"{sp₀.start.line}:{sp₀.start.col}): polymorphic recursion over rows is not provided; " ++
        needsBinder⟩
    if c.stack.length ≥ maxDepth then
      throw ⟨sp, s!"`{t.name}`'s instances are made inside each other without end: polymorphic " ++
        s!"recursion over rows is not provided; {needsBinder}"⟩
    let k := ((← get).count.lookup t.name).getD 0 + 1
    let name := if isPure then t.name else s!"{t.name}__r{k}"
    let inst : Inst := ⟨name, tps⟩
    let fresh := (← get).site
    modify fun s => { s with insts := (key, inst) :: s.insts,
                             count := if isPure then s.count else (t.name, k) :: s.count.filter (·.1 != t.name),
                             site := s.site + priv.length }
    let σs : List (Nat × Nat) :=
      (pub.map siteOfName).zip Ss ++ (priv.map siteOfName).zip ((List.range priv.length).map (fresh + ·))
    -- The instance's own type parameters take fresh names, `T__p` for the caller's `T`, so that
    -- a global type the template names is not captured by them.
    let own := tps.map (· ++ "__p")
    let ρ : TySubst := tps.zip (own.map (VTy.name .none))
    let Ts' := Ts.map (·.subst ρ)
    let Rs' := Rs.map (·.subst ρ)
    let c' : Cx := { tmpls := c.tmpls, tys := if isPure then [] else t.tps.zip Ts',
                     rows := t.rows.zip Rs', sites := σs, tps := if isPure then tps else own,
                     stack := (t.name, sp) :: c.stack }
    let A ← substV n c' t.ty
    -- A wrong row argument, reported here rather than inside the instance: an operation the
    -- body performs outside every handler it installs that the instance's type does not have.
    let has := A.ents
    for (out, k₀, i) in t.val.sitesIn [] do
      let k := c'.site k₀
      if out && !has.contains (k, i) then
        let rows := ", ".intercalate (Rs.map fun r => s!"({r.pp})")
        throw ⟨sp, s!"`{t.name}` used at row {rows}, but `{t.name}`'s body performs " ++
          s!"`{sitePp k}.{i}` outside it"⟩
    let V ← substVal n c' t.val
    let d : Decl := .def_ t.sp ⟨name, t.sp⟩ ((if isPure then tps else own).map fun x => ⟨x, t.sp⟩)
      A V t.mark
    modify fun s => { s with out := s.out.push d, made := s.made.push (name, t.name, sp) }
    return ref inst
end

/-- The program with each template's uses made instances, each instance just before the first
declaration that uses it, and the templates removed; and each instance made, with its template
and the use it was made for. A program with no template is unchanged. `floor` is the next site
the effects pass would give: a fresh site is at or above it, and above every literal site.
`[spec §76]` -/
def run (ds : List Decl) (floor : Nat) :
    Except Error (List Decl × List (String × String × Span)) := do
  let tmpls := templates ds
  if tmpls.isEmpty then return (ds, [])
  -- A template's body is core text: the passes that elaborate surface forms ran before it is
  -- instantiated.
  for t in tmpls do
    if let some sp := t.val.surface? then
      throw ⟨sp, s!"the body of `{t.name}`, which has row or site parameters, is core text in " ++
        "slice 1: this surface form is not elaborated in it (SPEC §76)"⟩
  let c : Cx := { tmpls }
  let site0 := max floor (ds.foldl (fun m d => max m d.maxSite) 0 + 1)
  let go : M (Array Decl) := do
    let mut acc : Array Decl := #[]
    for d in ds do
      let d' ← match d with
        | .gen .. => pure none
        | .def_ sp n ps A V mk => do
          let c := { c with tps := ps.map (·.name) }
          pure (some (Decl.def_ sp n ps (← substV fuel c A) (← substVal fuel c V) mk))
        | .main sp C M => do pure (some (Decl.main sp (← substC fuel c C) (← substComp fuel c M)))
        | .extern sp n A => do pure (some (Decl.extern sp n (← substV fuel c A)))
        | .type sp n ps ls A => do
          pure (some (Decl.type sp n ps ls (← substV fuel { c with tps := ps.map (·.name) } A)))
        | .shape sp n σ => do pure (some (Decl.shape sp n (← substS fuel c σ)))
        | d => pure (some d)
      acc := acc ++ (← get).out
      modify fun s => { s with out := #[] }
      if let some d' := d' then acc := acc.push d'
    pure acc
  let (acc, st) ← go.run { site := site0 }
  pure (acc.toList, st.made.toList)

end Frontend.Elab.RowInst
