import Frontend.Check.Program

/-!
# Rewrite — the read-back  `[spec §54]`

The rewriter (#680) works on the typed program and hands the kernel a program to check once
(`Rewrite/Driver.lean`). This module reads a typed term back into core syntax: one rule per
`TExpr` constructor, emitting the form the checker typed the node from.

* **Types** are read back structurally (`rbV`, `rbC`, `rbRow`, `rbShape`): a type of the typed term
  is closed over the lifetimes in scope, so no `type` or `shape` name is needed. A lifetime
  variable `v` is written `'l{v}` at its binder and at its uses (`lname`), and the meet of the
  node's lifetime context `⊓Δ` is written `dom` (`rbL`), so that a key's body checked under a
  use's binders reads back as the program writes it; a `μ` or `ν` variable is named by its depth.
* **Nodes the checker inserts stay implicit**, by the rule of the node they are inserted at:
  the drops of SPEC §12 (`unitE` over a variable's destructor, which no program writes), the
  `[sub]` coercions of SPEC §19 (`effSub`, which no program writes) where the rule of the
  position inserts one (`liftRow` at a bound computation, `atRow` at a synthesized body, `convC`
  at a computation checked against a row, `return` checked at a row), the drop glue of `[then]`
  (its finaliser, unless the node records that the program writes it, `TInfo.written`), and the
  η-thunk of codata (`nuEta`).
* **What the checker's input writes and no node holds**, the checker records in the node's
  `TInfo`: a binding's annotation and `linear` (`ann`, `lin`), and a borrow's witness lifetime
  (`wit`).
* **An ascription is written exactly where the node's form is checked and its position
  synthesizes**: `inl`, `inr`, `roll`, `absurd`, `abort` at an answer other than `0`, a `[sub]` no
  rule of the position inserts, a `[let]` or `[then]` whose body was checked against the row (not
  lifted to it), and a thunk whose type holds a row (a thunk synthesized is checked at no row).
  The ascribed type is the node's judgment.
* **A use of a `def`** (`TExpr.use`) reads back as a reference to the monomorphic declaration of
  its key `(decl, targs)` (`Key`), whose body is read back once from the use's typed body.

Every traversal is bounded by a fuel whose exhaustion is an error (§1.3 of the scope).
-/

namespace Rewrite
open Frontend (Span Ident Val Comp Decl Program SiteRec HForm OpCount Const)
open Frontend.Check (CVTy CCTy CShape CLife CRow CCount COpSig CntTable Scope effRow? lookupVar)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo HSite)
open BoCa.Fig16.LogRel.Core (Jdg FShape)

/-- The read-back's errors: a node or type it has no rule for, or a typed term that is not the
checker's. -/
abbrev RB := Except String

/-- The depth bound of every traversal of the read-back. -/
def fuel : Nat := 1 <<< 20

/-! ### Types -/

/-- The name a lifetime variable is written by. -/
def lname (v : Nat) : String := s!"l{v}"

/-- What the read-back of a type knows: the counts the rows are written at, and the term's
lifetime context `Δ` at the node the type is read at. -/
structure TyCx where
  tbl : CntTable
  Δ : BoCa.Lifetime.LifeCtx

/-- A lifetime, at the term's lifetime context `Δ`: `dom` where it is `Δ`'s meet (`⊓Δ`,
`Frontend.Check.elabLifeS`), at a context that binds a variable; otherwise by its variables. -/
def rbL (Δ : BoCa.Lifetime.LifeCtx) (sp : Span) : CLife → Frontend.Life
  | .var v => domOr Δ sp (.var v) (.var sp (lname v))
  | .top => domOr Δ sp .top (.top sp)
  | .meet a b => domOr Δ sp (.meet a b) (.meet sp (rbL Δ sp a) (rbL Δ sp b))
  | .join a b => domOr Δ sp (.join a b) (.join sp (rbL Δ sp a) (rbL Δ sp b))
where
  domOr (Δ : BoCa.Lifetime.LifeCtx) (sp : Span) (a : CLife) (l : Frontend.Life) : Frontend.Life :=
    if !Δ.entries.isEmpty && a == Δ.meetOfDom then .dom sp else l

/-- The name of the `μ` or `ν` variable bound at depth `d`. -/
def tvName (d : Nat) : String := s!"X%{d}"

/-- The surface qualifier at which the row entry `n.i`, answering `B`, elaborates to the count `c`
at the counts `tbl` (`Scope.cntOf`): `lin`, `aff` or `ctl`, the first that does. -/
def qualOf (tbl : CntTable) (n i : Nat) (c : CCount) (B : CVTy) : RB Frontend.Qual :=
  let sc : Scope := { decls := #[], upto := 0, cnts := tbl }
  match [Frontend.Qual.lin, .aff, .infer].find? (fun q => sc.cntOf n i q B == c) with
  | some q => pure q
  | none => throw s!"the row entry {n}.{i} at the count {repr c} is written by no qualifier"

mutual
/-- A value type, under the `μ`/`ν` variables `mu` (innermost first; a `ν` variable's entry is
`"U X"`, as `Frontend.Check.elabV` keeps them). -/
def rbV (tc : TyCx) (sp : Span) : Nat → List String → CVTy → RB Frontend.VTy
  | 0, _, _ => throw "read-back: a type nested too deeply"
  | f + 1, mu, A => match A with
    | .unit => pure (.unit sp)
    | .zero => pure (.zero sp)
    | .tensor A B => return .tensor sp (← rbV tc sp f mu A) (← rbV tc sp f mu B)
    | .sum A B => return .sum sp (← rbV tc sp f mu A) (← rbV tc sp f mu B)
    | .thunk C => return .thunk sp (← rbC tc sp f [] C)
    | .ref A => return .ref sp (← rbV tc sp f mu A)
    | .imm a A => return .imm sp (rbL tc.Δ sp a) (← rbV tc sp f mu A)
    | .mut a A => return .mut sp (rbL tc.Δ sp a) (← rbV tc sp f mu A)
    | .box a A => return .box sp (rbL tc.Δ sp a) (← rbV tc sp f mu A)
    | .bang A => return .bang sp (← rbV tc sp f mu A)
    | .unk => pure (.unk sp)
    | .tvar n => match mu[n]? with
      | some x =>
        if x.startsWith "U " then pure (.thunk sp (.name sp (x.drop 2).toString))
        else pure (.name sp x)
      | none => throw s!"read-back: the type variable {n} is free"
    | .mu A => do
      let x := tvName mu.length
      return .mu sp ⟨x, sp⟩ (← rbV tc sp f (x :: mu) A)
    | .int w => pure (.int sp w)
    | .fam (.ref A) => return .array sp (← rbV tc sp f mu A)
    | .fam (.imm a A) => return .arrayImm sp (rbL tc.Δ sp a) (← rbV tc sp f mu A)
    | .fam (.mut a A) => return .arrayMut sp (rbL tc.Δ sp a) (← rbV tc sp f mu A)
    | .fam _ => throw "read-back: a family type `[L]` whose leaf is not a `ref`, `imm` or `mut`"
    | .opq k => pure (.handle sp (match k with
      | .input => .input
      | .output => .output
      | .clock => .clock
      | .args => .args))
/-- A computation type. -/
def rbC (tc : TyCx) (sp : Span) : Nat → List String → CCTy → RB Frontend.CTy
  | 0, _, _ => throw "read-back: a type nested too deeply"
  | f + 1, mu, C => match C with
    | .ret A => return .ret sp (← rbV tc sp f mu A)
    | .arr A C => return .arr sp (← rbV tc sp f mu A) (← rbC tc sp f mu C)
    | .amp C D => return .amp sp (← rbC tc sp f mu C) (← rbC tc sp f mu D)
    | .top => pure (.top sp)
    | .all x b C => return .all sp ⟨lname x, sp⟩ (rbL tc.Δ sp b) (← rbC tc sp f mu C)
    | .nu C => do
      let x := tvName mu.length
      return .nu sp ⟨x, sp⟩ (← rbC tc sp f ["U " ++ x] C)
    | C@(.eff ..) => match effRow? C with
      | some (S, R) => return .eff sp (← rbRow tc sp f mu S) (← rbV tc sp f mu R)
      | none => throw "read-back: a row over a computation type that is not `F R`"
/-- A row: each entry at the qualifier its count is written by (`qualOf`), at the world `⊤` and
the empty cancel row, which are the only ones a row elaborates to (`Frontend.Check.elabRow`). -/
def rbRow (tc : TyCx) (sp : Span) : Nat → List String → CRow → RB Frontend.Row
  | 0, _, _ => throw "read-back: a row nested too deeply"
  | _ + 1, _, [] => pure .nil
  | f + 1, mu, o :: os => do
    unless o.fin == .ret .unit do
      throw s!"read-back: the row entry {o.n}.{o.i} has a cancel row, which no row writes"
    let q ← qualOf tc.tbl o.n.toNat o.i.toNat o.cnt o.B
    return .cons o.n.toNat o.i.toNat q (← rbV tc sp f mu o.A) (← rbV tc sp f mu o.B)
      (← rbRow tc sp f mu os)
end

/-- A shape. -/
def rbShape (tc : TyCx) (sp : Span) : Nat → CShape → RB Frontend.Shape
  | 0, _ => throw "read-back: a shape nested too deeply"
  | _ + 1, .leaf A => return .leaf sp (← rbV tc sp fuel [] A)
  | f + 1, .node s t => return .node sp (← rbShape tc sp f s) (← rbShape tc sp f t)

/-- A fold's shape, as the type it is decoded from: its recursive position the variable `X`
(`Frontend.Check.elabFShape`). -/
def rbFShape (tc : TyCx) (sp : Span) : Nat → FShape → RB Frontend.VTy
  | 0, _ => throw "read-back: a fold shape nested too deeply"
  | _ + 1, .leaf A => rbV tc sp fuel ["X"] A
  | _ + 1, .refX => pure (.ref sp (.name sp "X"))
  | _ + 1, .varX => pure (.name sp "X")
  | f + 1, .tensor F G => return .tensor sp (← rbFShape tc sp f F) (← rbFShape tc sp f G)
  | f + 1, .sum F G => return .sum sp (← rbFShape tc sp f F) (← rbFShape tc sp f G)

/-! ### Terms -/

/-- A `def`'s key: its declaration and type arguments. -/
abbrev Key := Nat × List CVTy

/-- What the read-back of a term knows besides the term: the name of each slot of the checker's
context (`Env.vars`: a dead slot or a hidden one has none), the number of extern slots at its end,
the declaration name of each key, and the counts the rows are written at. -/
structure Cx where
  vars : List (Option String)
  nExt : Nat
  names : List (Key × String)
  tbl : CntTable
  /-- The term's lifetime context at the node: `Fun`'s and R1's binders, outermost last. -/
  Δ : BoCa.Lifetime.LifeCtx := ⟨[]⟩

/-- The read-back of the types at the node. -/
def Cx.tc (cx : Cx) : TyCx := ⟨cx.tbl, cx.Δ⟩

def Cx.push (cx : Cx) (x : Option String) : Cx := { cx with vars := x :: cx.vars }

/-- The name of the slot `i`, which resolves to it. -/
def Cx.slot (cx : Cx) (i : Nat) : RB String :=
  match cx.vars[i]? with
  | some (some x) =>
    if lookupVar x cx.vars == some i then pure x
    else throw s!"read-back: the name `{x}` of the slot {i} does not resolve to it"
  | _ => throw s!"read-back: the slot {i} has no name"

/-- The name a binder is written with: its source name when the node records one, else a name no
program writes, by the binder's depth. -/
def Cx.binder (cx : Cx) (nm : Option String) : String :=
  match nm with
  | some x => if x.isEmpty then s!"_%{cx.vars.length}" else x
  | none => s!"_%{cx.vars.length}"

/-- The declaration name of a key. -/
def Cx.keyName (cx : Cx) (k : Key) : RB String :=
  match cx.names.lookup k with
  | some x => pure x
  | none => throw s!"read-back: the use of the declaration {k.1} at a key with no declaration"

/-- A read-back value or computation. -/
inductive Syn where
  | v (V : Val)
  | c (M : Comp)

def Syn.val : Syn → RB Val
  | .v V => pure V
  | .c _ => throw "read-back: a computation where a value is expected"

def Syn.comp : Syn → RB Comp
  | .c M => pure M
  | .v _ => throw "read-back: a value where a computation is expected"

/-- The value type of a value-judged node. -/
def jV : Jdg → RB CVTy
  | .val A => pure A
  | .comp _ => throw "read-back: a computation where a value is expected"

/-- The computation type of a computation-judged node. -/
def jC : Jdg → RB CCTy
  | .comp C => pure C
  | .val _ => throw "read-back: a value where a computation is expected"

/-- The node is the drop of SPEC §12 (`rDrop`): `unitE` over the application of a variable's
destructor, which no program writes. -/
def dropOf? : TExpr → Option TExpr
  | .unitE _ _ _ _ (.lolliE _ _ _ _ _ (.var ..) (.dtor ..)) tM => some tM
  | _ => none

/-- The computation forms the checker checks against a type by synthesizing them and converting
(`chkC`'s last case, `convC`): at a row, a `[sub]` over one of them is `convC`'s. -/
def synthForm : TExpr → Bool
  | .effPerform .. | .effHandleV .. | .effHandleVB .. | .effHandleT .. | .effHandleL .. | .force ..
  | .app .. | .proj₁ .. | .proj₂ .. | .allE .. | .nuOut .. | .effSub .. => true
  | _ => false

mutual
/-- The type holds a row: an operation of an effect, anywhere in it. -/
def rowInV : CVTy → Bool
  | .tensor A B | .sum A B => rowInV A || rowInV B
  | .thunk C => rowInC C
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => rowInV A
  | _ => false
/-- The computation type holds a row. -/
def rowInC : CCTy → Bool
  | .eff .. => true
  | .ret A => rowInV A
  | .arr A C => rowInV A || rowInC C
  | .amp C D => rowInC C || rowInC D
  | .all _ _ C | .nu C => rowInC C
  | .top => false
end

/-- An operation's count as a rule-written handler's form names it. -/
def opCount : CCount → OpCount
  | .zero => .zero
  | .one => .one
  | .opt => .opt

/-- The record of a handler site (`SiteRec`) that the checker's `siteOf` elaborates to the node's
site `s`, at the node's name `n` and operations `E`: the node's record carried verbatim, its types
read back (no rule reads it). At a `for`'s site the record's answer types
are not read but through the count each elaborates to (`recOps`, `Scope.cntOf`), and are written
`0` where the count is `0` and `1` otherwise. -/
def siteRec (tc : TyCx) (sp : Span) (n : Nat) (E : List (CCount × CVTy × CVTy)) (s : HSite) :
    RB SiteRec := do
  let ty (A : CVTy) := rbV tc sp fuel [] A
  unless s.decl.length == E.length do
    throw "read-back: a site's record has other operations than its node"
  let ents ← (s.decl.zip E).mapM fun (q, c, A, B) => do
    match s.kind with
    | .forSite =>
      let A₀ := match A with
        | .tensor A₀ _ => A₀
        | A => A
      let B₀ : CVTy := if c == .zero then .zero else .unit
      pure (q, ← ty A₀, ← ty B₀)
    | _ => pure (q, ← ty A, ← ty B)
  pure { n, eff := s.eff, args := ← s.args.mapM ty, handler := s.handler, slot := s.slot,
         kind := s.kind, ents, state := ← s.state.mapM fun (x, A) => do pure (x, ← ty A) }

/-- The witness lifetime the node records (`TInfo.wit`): a borrow whose rule takes one. -/
def witOf (Δ : BoCa.Lifetime.LifeCtx) (sp : Span) (i : TInfo) : RB Frontend.Life :=
  match i.wit with
  | some a => pure (rbL Δ sp a)
  | none => throw "read-back: a borrow whose witness lifetime the node does not record"

/-- A constant node's constant. -/
def constOf (tc : TyCx) (sp : Span) (i : TInfo) : TExpr → RB (Option Const)
  | t => do
    let ty (A : CVTy) := rbV tc sp fuel [] A
    let row (S : CRow) := rbRow tc sp fuel [] S
    let l (a : CLife) := rbL tc.Δ sp a
    let b (x : Nat) : Ident := ⟨lname x, sp⟩
    match t with
    | .alloc _ _ A => return some (.alloc (← ty A))
    | .free _ _ A => return some (.free (← ty A))
    | .swap _ _ A B => return some (.swap (← ty A) (← ty B))
    | .copy _ _ a A => return some (.copy (l a) (← ty A))
    | .copyBang _ _ A => return some (.copyBang (← ty A))
    | .forgetImm _ _ a A => return some (.forgetImm (l a) (← ty A))
    | .forgetMut _ _ a A => return some (.forgetMut (l a) (← ty A))
    | .forgetUnk _ _ => return some .forgetUnk
    | .forgetBang _ _ A => return some (.forgetBang (← ty A))
    | .withbor1 _ _ A B x => return some (.withbor1 (b x) (← ty A) (← ty B))
    | .withbor2 _ _ A B x => return some (.withbor2 (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B))
    | .withbor3 _ _ a A B x => return some (.withbor3 (l a) (b x) (← ty A) (← ty B))
    | .withload _ _ a A B x => return some (.withload (l a) (b x) (← ty A) (← ty B))
    | .withswap _ _ a A B => return some (.withswap (l a) (← ty A) (← ty B))
    | .foldImm _ _ F y c R => return some (.foldImm (← rbFShape tc sp fuel F) (b y) (l c) (← ty R))
    | .foldOwn _ _ F R => return some (.foldOwn (← rbFShape tc sp fuel F) (← ty R))
    | .foldReuse _ _ F R => return some (.foldReuse (← rbFShape tc sp fuel F) (← ty R))
    | .unfoldN _ _ C S => return some (.unfold (← rbC tc sp fuel [] (.nu C)) (← ty S))
    | .lit _ _ c => return some (.lit c)
    | .hostOp _ _ op => return some (.host op)
    | .allocS _ _ σ => return some (.allocS (← rbShape tc sp fuel σ))
    | .freeS _ _ σ => return some (.freeS (← rbShape tc sp fuel σ))
    | .withborSM _ _ σ c T => return some (.withborS .mut (← rbShape tc sp fuel σ) (b c) (← ty T))
    | .withborSI _ _ σ c T => return some (.withborS .imm (← rbShape tc sp fuel σ) (b c) (← ty T))
    | .withborF2M _ _ c x y A B T =>
      return some (.withborF2Mut (b c) (b x) (b y) (← witOf tc.Δ sp i) (← ty A) (← ty B) (← ty T))
    | .withborF2I _ _ c x y A B T => return some (.withborF2Imm (b c) (b x) (b y) (← ty A) (← ty B) (← ty T))
    | .arrNew _ _ A => return some (.arrayNew (← ty A))
    | .arrFree _ _ A => return some (.arrayFree (← ty A))
    | .arrSize _ _ A => return some (.arraySize (← ty A))
    | .arrReplace _ _ A => return some (.arrayReplace (← ty A))
    | .arrLen _ _ a A => return some (.arrayLen (l a) (← ty A))
    | .arrGet _ _ a A => return some (.arrayGet (l a) (← ty A))
    | .arrCopy _ _ a A => return some (.arrayCopy (l a) (← ty A))
    | .arrForget _ _ a A => return some (.arrayForget (l a) (← ty A))
    | .countFold _ _ S => return some (.countFold (← ty S))
    | .countTry _ _ S E => return some (.countTry (← ty S) (← ty E))
    | .boundedFix _ _ A C => return some (.boundedFix (← ty A) (← rbC tc sp fuel [] C))
    | .sliceBorrowM _ _ A B x => return some (.sliceBorrowMut (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B))
    | .sliceBorrowI _ _ A B x => return some (.sliceBorrowImm (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B))
    | .sliceGetM _ _ a A => return some (.sliceGetMut (l a) (← ty A))
    | .sliceLenM _ _ a A => return some (.sliceLenMut (l a) (← ty A))
    | .sliceSplitI _ _ a A => return some (.sliceSplitImm (l a) (← ty A))
    | .sliceSplitM _ _ a A => return some (.sliceSplitMut (l a) (← ty A))
    | .sliceEmptyI _ _ a A => return some (.sliceEmptyImm (l a) (← ty A))
    | .sliceEmptyM _ _ a A => return some (.sliceEmptyMut (l a) (← ty A))
    | .sliceReplaceM _ _ a A => return some (.sliceReplaceMut (l a) (← ty A))
    | .sliceSwapM _ _ a A => return some (.sliceSwapMut (l a) (← ty A))
    | .withbor1U _ _ A B S x _ => return some (.withbor1U (b x) (← ty A) (← ty B) (← row S))
    | .withbor2U _ _ A B S x _ =>
      return some (.withbor2U (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B) (← row S))
    | .withbor3U _ _ a A B S x _ => return some (.withbor3U (l a) (b x) (← ty A) (← ty B) (← row S))
    | .withloadU _ _ a A B S x => return some (.withloadU (l a) (b x) (← ty A) (← ty B) (← row S))
    | .sliceBorrowMU _ _ A B S x _ =>
      return some (.sliceBorrowMutU (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B) (← row S))
    | .sliceBorrowIU _ _ A B S x _ =>
      return some (.sliceBorrowImmU (b x) (← witOf tc.Δ sp i) (← ty A) (← ty B) (← row S))
    | _ => return none

/-- **The read-back of a node** `t` at the context `cx`, at a position that checks it (`chk`) or
synthesizes it, and, for a computation, whether the position's rule inserts a `[sub]` over it
(`ins`: `liftRow` at a bound computation, `atRow` at a synthesized body or arm). -/
def rd : Nat → Cx → Bool → Bool → TExpr → RB Syn
  | 0, _, _, _, _ => throw "read-back: a term nested too deeply"
  | f + 1, cx, chk, ins, t => do
    let sp := t.info.sp
    let ty (A : CVTy) := rbV cx.tc sp fuel [] A
    let cty (C : CCTy) := rbC cx.tc sp fuel [] C
    let val (cx : Cx) (chk : Bool) (t : TExpr) : RB Val := do (← rd f cx chk false t).val
    let comp (cx : Cx) (chk ins : Bool) (t : TExpr) : RB Comp := do (← rd f cx chk ins t).comp
    -- A form the checker only checks, at a position that synthesizes: the program ascribes it.
    let ascV (V : Val) : RB Syn := do
      if chk then pure (.v V) else pure (.v (.ascribe sp V (← ty (← jV t.jdg))))
    if let some tM := dropOf? t then return ← rd f cx chk ins tM
    if let some c ← constOf cx.tc sp t.info t then return .v (.const sp c)
    match t with
    | .var i _ k _ => do
      let x ← cx.slot k
      pure (.v (if i.clone then .clone sp x else .var sp x))
    | .unitI .. => pure (.v (.unit sp))
    | .tensorI _ _ _ _ _ t₁ t₂ => return .v (.pair sp (← val cx chk t₁) (← val cx chk t₂))
    | .sumI₁ _ _ _ _ c => ascV (.inl sp (← val cx true c))
    | .sumI₂ _ _ _ _ c => ascV (.inr sp (← val cx true c))
    -- A thunk synthesized has a body checked at no row (`Env.forVal`): one whose type holds a
    -- row was checked against its type, and the program ascribes it.
    | .thunkF _ (.val A) _ _ | .thunkV _ (.val A) _ _ | .nuEta _ (.val A) _ _ _
    | .bangThunkF _ (.val A) _ _ | .bangThunkV _ (.val A) _ _ =>
      if !chk && rowInV A then return .v (.ascribe sp (← val cx true t) (← ty A))
      else match t with
        | .thunkF _ _ _ c => return .v (.thunk sp (← comp (cx.push none) chk false c))
        | .thunkV _ _ _ c => return .v (.thunkv sp (← comp cx chk false c))
        | .nuEta _ _ _ _ c => rd f cx chk ins c
        | .bangThunkF _ _ _ c => return .v (.bangThunk sp (← comp (cx.push none) chk false c))
        | .bangThunkV _ _ _ c => return .v (.bangThunkv sp (← comp cx chk false c))
        | _ => throw "read-back: a thunk"
    | .thunkF .. | .thunkV .. | .nuEta .. | .bangThunkF .. | .bangThunkV .. =>
      throw "read-back: a thunk at a computation type"
    | .bangE _ _ _ c => return .v (.unbang sp (← val cx chk c))
    | .boxI _ _ a _ c => return .v (.boxed sp (rbL cx.Δ sp a) (← val cx chk c))
    | .boxE _ _ _ _ c => return .v (.unbox sp (← val cx false c))
    | .immSub _ _ a _ _ c | .mutSub _ _ a _ _ c => return .v (.sub sp (← val cx false c) (rbL cx.Δ sp a))
    | .roll _ _ _ c => ascV (.roll sp (← val cx true c))
    | .unroll _ _ _ c => return .v (.unroll sp (← val cx false c))
    | .ofRet _ _ _ c => return .v (.run sp (← comp cx chk false c))
    | .lolliE _ _ _ _ _ ta tf => return .v (.app sp (← val cx false tf) (← val cx true ta))
    | .allEV _ _ _ _ a _ c => return .v (.inst sp (← val cx false c) (rbL cx.Δ sp a))
    | .litFn _ _ bs c => return .v (.mark sp (.litFn bs) (← val cx chk c))
    | .divLit _ _ op n c => return .v (.mark sp (.divLit op n) (← val cx chk c))
    | .walk _ _ m _ c => return .v (.mark sp (.walk m) (← val cx chk c))
    | .walkGet _ _ m c => return .v (.mark sp (.walkGet m) (← val cx chk c))
    | .selfCall _ _ j n c => return .v (.mark sp (.selfCall j n) (← val cx chk c))
    | .lendCell _ _ m c => return .v (.mark sp (.lendCell m) (← val cx chk c))
    | .use _ _ _ decl targs _ _ => return .v (.var sp (← cx.keyName (decl, targs)))
    -- Computations.
    | .effSub _ j _ _ _ c =>
      if ins then rd f cx false false c
      else if chk then
        -- `convC` over a form the checker synthesizes, or `return` at a row (`chkC`'s `.ret`);
        -- over any other form, the program ascribes it.
        if synthForm c then rd f cx false false c
        else if c matches .ret .. then rd f cx true false c
        else return .c (.ascribe sp (← comp cx true false c) (← cty (← jC c.jdg)))
      else return .c (.ascribe sp (← comp cx true false t) (← cty (← jC j)))
    | .ret _ _ _ c => return .c (.ret sp (← val cx chk c))
    | .bind i _ A _ _ tM tN => do
      -- The head is checked at the annotation when the program writes one (`bindHead`).
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      return .c (.bind sp ⟨x, sp⟩ oA (← comp cx i.ann false tM) (← comp (cx.push x) chk false tN) i.lin)
    | .force _ _ k _ => return .c (.force sp ⟨← cx.slot k, sp⟩)
    | .lam i _ A _ c => do
      let x := cx.binder (some i.name)
      return .c (.lam sp ⟨x, sp⟩ (← ty A) (← comp (cx.push x) chk false c))
    | .lamDead _ _ _ _ c => do
      let x := cx.binder none
      return .c (.lam sp ⟨x, sp⟩ (.unit sp) (← comp (cx.push x) chk false c))
    | .app _ _ k _ _ _ tM => match tM with
      | .nilDead _ _ _ (.lam _ _ _ _ (.lendR _ _ x b A B S _ tR)) => do
        -- R1's relaxed lend (`rLendR`): its body at the view alone.
        let m := s!"_%view{cx.vars.length}"
        let p ← cx.slot k
        let cxR : Cx := { cx with vars := [some m], nExt := 0, Δ := cx.Δ.extend x b }
        return .c (.withbor2r sp ⟨lname x, sp⟩ (rbL cx.Δ sp b) (← ty A) (← ty B)
          (← rbRow cx.tc sp fuel [] S) ⟨p, sp⟩ ⟨m, sp⟩ (← comp cxR true false tR))
      | _ => do
        return .c (.app sp (← comp cx false false tM) ⟨← cx.slot k, sp⟩)
    | .withI _ _ _ _ tM tN => do
      let cx2 := (cx.push none).push none
      return .c (.with_ sp (← comp cx2 chk false tM) (← comp cx2 chk false tN))
    | .proj₁ _ _ _ _ c => return .c (.proj sp true (← comp cx false false c))
    | .proj₂ _ _ _ _ c => return .c (.proj sp false (← comp cx false false c))
    | .topI .. => pure (.c (.top sp))
    | .unitE _ _ _ _ tV tM => return .c (.letUnit sp (← val cx true tV) (← comp cx chk false tM))
    | .tensorE i _ _ _ _ _ tV tM => do
      let x := cx.binder i.binders.head?
      let y := (cx.push x).binder (i.binders.drop 1).head?
      return .c (.letPair sp ⟨x, sp⟩ ⟨y, sp⟩ (← val cx false tV)
        (← comp ((cx.push x).push y) chk false tM))
    | .sumE i _ _ _ _ _ tV t₁ t₂ => do
      let x := cx.binder i.binders.head?
      let y := cx.binder (i.binders.drop 1).head?
      -- At a position that synthesizes, either arm may be synthesized and lifted to the row
      -- (`atRow`, `chkC`'s fallbacks).
      return .c (.case sp (← val cx false tV) ⟨x, sp⟩ (← comp (cx.push x) chk (!chk) t₁) ⟨y, sp⟩
        (← comp (cx.push y) chk (!chk) t₂))
    | .zeroE _ j _ _ tV => do
      let M : Comp := .absurd sp (← val cx true tV)
      if chk then pure (.c M) else return .c (.ascribe sp M (← cty (← jC j)))
    | .allI _ _ x b _ _ c =>
      return .c (.lamL sp ⟨lname x, sp⟩ (rbL cx.Δ sp b)
        (← comp { cx.push none with Δ := cx.Δ.extend x b } chk false c))
    | .allE _ _ _ _ a _ c => return .c (.inst sp (← comp cx false false c) (rbL cx.Δ sp a))
    | .nuIn _ _ _ c => return .c (.nuIn sp (← comp cx chk false c))
    | .nuOut _ _ _ c => return .c (.nuOut sp (← comp cx false false c))
    | .effPerform _ _ _ o c => return .c (.perform sp o.n.toNat o.i.toNat (← val cx true c))
    | .effRaise _ j _ o B c => do
      -- Synthesized, an abortive operation answers `0` (`abortIt` at `.zero`): at another answer,
      -- the program ascribes it.
      let M : Comp := .abort sp o.n.toNat o.i.toNat (← val cx true c)
      if chk || B == .zero then pure (.c M) else return .c (.ascribe sp M (← cty (← jC j)))
    | .effLet i j A _ _ _ tM tN => do
      -- Synthesized, the body is lifted to the row (`atRow`): a body that is not was checked
      -- against the row, and the program ascribes the binding.
      if !chk && !(tN matches .effSub ..) then
        return .c (.ascribe sp (← comp cx true false t) (← cty (← jC j)))
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      return .c (.bind sp ⟨x, sp⟩ oA (← comp cx i.ann true tM) (← comp (cx.push x) chk (!chk) tN) i.lin)
    | .effThen i j A _ _ _ _ _ tM tN tD => do
      if !chk && !(tN matches .effSub ..) then
        return .c (.ascribe sp (← comp cx true false t) (← cty (← jC j)))
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      let M ← comp cx i.ann true tM
      let N ← comp (cx.push x) chk (!chk) tN
      if i.written then
        return .c (.unwind sp ⟨x, sp⟩ oA M (← comp (cx.push none) true false tD) N)
      else return .c (.bind sp ⟨x, sp⟩ oA M N i.lin)
    | .effHandleV _ _ _ E _ n _ _ _ _ site _ tc te
    | .effHandleVB _ _ _ E _ n _ _ _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr tcl := tc | throw "read-back: a handler's pair is not a pair"
      let site ← site.mapM (siteRec cx.tc sp n.toNat E)
      return .c (.handle sp n.toNat .clauses site (← val cx false tr) (← val cx false tcl)
        (← comp cx true false te))
    | .effHandleT _ _ _ _ E _ n _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr tcl := tc | throw "read-back: a handler's pair is not a pair"
      let site ← site.mapM (siteRec cx.tc sp n.toNat E)
      return .c (.handle sp n.toNat (.tail (E.map fun e => opCount e.1)) site (← val cx false tr)
        (← val cx false tcl) (← comp cx true false te))
    | .effHandleL _ _ _ _ E _ _ n _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr (.tensorI _ _ _ _ _ tw tn) := tc
        | throw "read-back: a `handle_last`'s clauses are not `(works, exits)`"
      let site ← site.mapM (siteRec cx.tc sp n.toNat E)
      return .c (.handle sp n.toNat (.last (E.map fun e => opCount e.1)) site (← val cx false tr)
        (.pair sp (← val cx false tw) (← val cx false tn)) (← comp cx true false te))
    | .dtor .. => throw "read-back: a destructor outside a drop"
    | .lendR .. => throw "read-back: R1's lend outside its application"
    | .nilDead .. => throw "read-back: `nilDead` outside R1's lend"
    | .letPoly .. | .lendLoopR .. | .iterate .. | .divFuel .. | .reify .. =>
      throw "read-back: a node the checker does not produce"
    | t => throw s!"read-back: no rule for the node at {t.info.sp.start.render}"

end Rewrite
