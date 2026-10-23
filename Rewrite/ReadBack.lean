import Frontend.Check.Program

/-!
# Rewrite — the read-back  `[spec §54]`

The rewriter (#680) works on the typed program and hands the kernel a program to check once
(`Rewrite/Driver.lean`). This module reads a typed term back into core syntax: one rule per
`TExpr` constructor, emitting the form the checker typed the node from.

* **Types and lifetimes** are read back structurally (`rbV`, `rbC`, `rbRow`, `rbShape`, `rbL`): a
  lifetime variable `v` is written `'l{v}` at its binder and at its uses (`lname`), and a `μ` or
  `ν` variable is named by its depth. No `type` or `shape` name is needed.
* **Nodes the checker inserts stay implicit**: the drops of SPEC §12 (`unitE` over a variable's
  destructor, which no program writes), the `[sub]` coercions the checker records it inserts
  (`TInfo.ins`: `liftRow`, `convC`, `return` checked at a row), the drop glue of `[then]` (unless
  the node records that the program writes its finaliser, `TInfo.written`), and the η-thunk of
  codata (`nuEta`).
* **What the program writes and no node's rule holds** is read from the facts the checker records
  in `TInfo`: an ascription (`asc`, on the root of the ascribed term's check), a binding's
  annotation and `linear` (`ann`, `lin`), a borrow's witness lifetime (`wit`), a bound or witness
  written `dom` (`dom`), and a handler site's record (`srec`). An ascription is written exactly where `asc` is set, at the node's judgment.
* **A use of a `def`** (`TExpr.use`) reads back as a reference to the declaration of its instance
  (`Key`: the checker's instance key, its declaration, type arguments, lifetime context and extern
  context), instantiated at the use's lifetimes when the declaration is lifetime-polymorphic
  (`Rewrite/Driver.lean`).

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

/-- A lifetime, by its variables. -/
def rbL (sp : Span) : CLife → Frontend.Life
  | .var v => .var sp (lname v)
  | .top => .top sp
  | .meet a b => .meet sp (rbL sp a) (rbL sp b)
  | .join a b => .join sp (rbL sp a) (rbL sp b)

/-- The name of the `μ` or `ν` variable bound at depth `d`. -/
def tvName (d : Nat) : String := s!"X%{d}"

/-- The surface qualifier a count is written by: its tag (`Count.toQual`), `lin` at `1` and `aff`
at `0` and `1?`. A row entry whose count the qualifier does not elaborate back to at the counts
`tbl` (`Scope.cntOf`) is an error. -/
def qualOf (tbl : CntTable) (n i : Nat) (c : CCount) (B : CVTy) : RB Frontend.Qual := do
  let q : Frontend.Qual := match c.toQual with
    | .lin => .lin
    | _ => .aff
  let sc : Scope := { decls := #[], upto := 0, cnts := tbl }
  if sc.cntOf n i q B == c then pure q
  else throw s!"read-back: the row entry {n}.{i} at the count {repr c} is not written by its tag"

mutual
/-- A value type, under the `μ`/`ν` variables `mu` (innermost first; a `ν` variable's entry is
`"U X"`, as `Frontend.Check.elabV` keeps them). -/
def rbV (tbl : CntTable) (sp : Span) : Nat → List String → CVTy → RB Frontend.VTy
  | 0, _, _ => throw "read-back: a type nested too deeply"
  | f + 1, mu, A => match A with
    | .unit => pure (.unit sp)
    | .zero => pure (.zero sp)
    | .tensor A B => return .tensor sp (← rbV tbl sp f mu A) (← rbV tbl sp f mu B)
    | .sum A B => return .sum sp (← rbV tbl sp f mu A) (← rbV tbl sp f mu B)
    | .thunk C => return .thunk sp (← rbC tbl sp f [] C)
    | .ref A => return .ref sp (← rbV tbl sp f mu A)
    | .imm a A => return .imm sp (rbL sp a) (← rbV tbl sp f mu A)
    | .mut a A => return .mut sp (rbL sp a) (← rbV tbl sp f mu A)
    | .box a A => return .box sp (rbL sp a) (← rbV tbl sp f mu A)
    | .bang A => return .bang sp (← rbV tbl sp f mu A)
    | .unk => pure (.unk sp)
    | .tvar n => match mu[n]? with
      | some x =>
        if x.startsWith "U " then pure (.thunk sp (.name sp (x.drop 2).toString))
        else pure (.name sp x)
      | none => throw s!"read-back: the type variable {n} is free"
    | .mu A => do
      let x := tvName mu.length
      return .mu sp ⟨x, sp⟩ (← rbV tbl sp f (x :: mu) A)
    | .int w => pure (.int sp w)
    | .fam (.ref A) => return .array sp (← rbV tbl sp f mu A)
    | .fam (.imm a A) => return .arrayImm sp (rbL sp a) (← rbV tbl sp f mu A)
    | .fam (.mut a A) => return .arrayMut sp (rbL sp a) (← rbV tbl sp f mu A)
    | .fam _ => throw "read-back: a family type `[L]` whose leaf is not a `ref`, `imm` or `mut`"
    | .opq k => pure (.handle sp (match k with
      | .input => .input
      | .output => .output
      | .clock => .clock
      | .args => .args))
/-- A computation type. -/
def rbC (tbl : CntTable) (sp : Span) : Nat → List String → CCTy → RB Frontend.CTy
  | 0, _, _ => throw "read-back: a type nested too deeply"
  | f + 1, mu, C => match C with
    | .ret A => return .ret sp (← rbV tbl sp f mu A)
    | .arr A C => return .arr sp (← rbV tbl sp f mu A) (← rbC tbl sp f mu C)
    | .amp C D => return .amp sp (← rbC tbl sp f mu C) (← rbC tbl sp f mu D)
    | .top => pure (.top sp)
    | .all x b C => return .all sp ⟨lname x, sp⟩ (rbL sp b) (← rbC tbl sp f mu C)
    | .nu C => do
      let x := tvName mu.length
      return .nu sp ⟨x, sp⟩ (← rbC tbl sp f ["U " ++ x] C)
    | C@(.eff ..) => match effRow? C with
      | some (S, R) => return .eff sp (← rbRow tbl sp f mu S) (← rbV tbl sp f mu R)
      | none => throw "read-back: a row over a computation type that is not `F R`"
/-- A row: each entry at the qualifier its count is written by (`qualOf`), at the world `⊤` and
the empty cancel row, which are the only ones a row elaborates to (`Frontend.Check.elabRow`). -/
def rbRow (tbl : CntTable) (sp : Span) : Nat → List String → CRow → RB Frontend.Row
  | 0, _, _ => throw "read-back: a row nested too deeply"
  | _ + 1, _, [] => pure .nil
  | f + 1, mu, o :: os => do
    unless o.fin == .ret .unit do
      throw s!"read-back: the row entry {o.n}.{o.i} has a cancel row, which no row writes"
    let q ← qualOf tbl o.n.toNat o.i.toNat o.cnt o.B
    return .cons o.n.toNat o.i.toNat q (← rbV tbl sp f mu o.A) (← rbV tbl sp f mu o.B)
      (← rbRow tbl sp f mu os)
end

/-- A shape. -/
def rbShape (tbl : CntTable) (sp : Span) : Nat → CShape → RB Frontend.Shape
  | 0, _ => throw "read-back: a shape nested too deeply"
  | _ + 1, .leaf A => return .leaf sp (← rbV tbl sp fuel [] A)
  | f + 1, .node s t => return .node sp (← rbShape tbl sp f s) (← rbShape tbl sp f t)

/-- A fold's shape, as the type it is decoded from: its recursive position the variable `X`
(`Frontend.Check.elabFShape`). -/
def rbFShape (tbl : CntTable) (sp : Span) : Nat → FShape → RB Frontend.VTy
  | 0, _ => throw "read-back: a fold shape nested too deeply"
  | _ + 1, .leaf A => rbV tbl sp fuel ["X"] A
  | _ + 1, .refX => pure (.ref sp (.name sp "X"))
  | _ + 1, .varX => pure (.name sp "X")
  | f + 1, .tensor F G => return .tensor sp (← rbFShape tbl sp f F) (← rbFShape tbl sp f G)
  | f + 1, .sum F G => return .sum sp (← rbFShape tbl sp f F) (← rbFShape tbl sp f G)

/-! ### Terms -/

/-- **The checker's instance key of a `def`** (`DefEntry`, `Checker.lean`'s `hit?`): its
declaration, its type arguments, the lifetime context it is checked at, and the number of extern
slots of its context. -/
abbrev Key := Nat × List CVTy × List (Nat × CLife) × Nat

/-- The declaration of an instance: its name, and the lifetime variables it is polymorphic in,
outermost first (none for a monomorphic one). -/
structure DeclOf where
  name : String
  vars : List Nat

/-- What the read-back of a term knows besides the term: the name of each slot of the checker's
context (`Env.vars`: a dead slot or a hidden one has none), the number of extern slots at its end,
the term's lifetime context, the declaration of each instance, and the counts the rows are
written at. -/
structure Cx where
  vars : List (Option String)
  nExt : Nat
  Δ : BoCa.Lifetime.LifeCtx := ⟨[]⟩
  decls : List (Key × DeclOf)
  tbl : CntTable

def Cx.push (cx : Cx) (x : Option String) : Cx := { cx with vars := x :: cx.vars }

/-- The name of the slot `i`, which resolves to it. -/
def Cx.slot (cx : Cx) (i : Nat) : RB String :=
  match cx.vars[i]? with
  | some (some x) =>
    if lookupVar x cx.vars == some i then pure x
    else throw s!"read-back: the name `{x}` of the slot {i} does not resolve to it"
  | _ => throw s!"read-back: the slot {i} has no name"

/-- The name a binder is written with: its source name when the node records one, else a name no
program writes, by the binder's depth; a binder a rule writes (named by the rule, `%R0`) is
numbered by its depth too. -/
def Cx.binder (cx : Cx) (nm : Option String) : String :=
  match nm with
  | some x =>
    if x.isEmpty then s!"_%{cx.vars.length}"
    else if x.startsWith "%" then s!"{x}.{cx.vars.length}"
    else x
  | none => s!"_%{cx.vars.length}"

/-- The declaration of an instance. -/
def Cx.declOf (cx : Cx) (k : Key) : RB DeclOf :=
  match cx.decls.lookup k with
  | some d => pure d
  | none => throw s!"read-back: the use of the declaration {k.1} at an instance with no declaration"

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

/-- The node is the drop of SPEC §12 (`rDrop`): `unitE` over the application of a variable's
destructor, which no program writes. -/
def dropOf? : TExpr → Option TExpr
  | .unitE _ _ _ _ (.lolliE _ _ _ _ _ (.var ..) (.dtor ..)) tM => some tM
  | _ => none

/-- An operation's count as a rule-written handler's form names it. -/
def opCount : CCount → OpCount
  | .zero => .zero
  | .one => .one
  | .opt => .opt

/-- A bound or witness the node's rule takes: `dom` where the node records that the program writes
it so (`TInfo.dom`), the lifetime read back otherwise. -/
def boundOf (sp : Span) (i : TInfo) (a : CLife) : Frontend.Life :=
  if i.dom then .dom sp else rbL sp a

/-- The witness lifetime the node records (`TInfo.wit`): a borrow whose rule takes one. -/
def witOf (sp : Span) (i : TInfo) : RB Frontend.Life :=
  match i.wit with
  | some a => pure (boundOf sp i a)
  | none => throw "read-back: a borrow whose witness lifetime the node does not record"

/-- The record of a handler site the node carries (`TInfo.srec`), as the program writes it. -/
def siteRecOf (i : TInfo) (site : Option HSite) : RB (Option SiteRec) :=
  match site, i.srec with
  | none, none => pure none
  | some _, some r => pure (some r)
  | some _, none => throw "read-back: a handler site whose record the node does not carry"
  | none, some _ => throw "read-back: a handler site's record at a node with no site"

/-- A constant node's constant. -/
def constOf (tbl : CntTable) (sp : Span) (i : TInfo) : TExpr → RB (Option Const)
  | t => do
    let ty (A : CVTy) := rbV tbl sp fuel [] A
    let row (S : CRow) := rbRow tbl sp fuel [] S
    let l (a : CLife) := rbL sp a
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
    | .withbor2 _ _ A B x => return some (.withbor2 (b x) (← witOf sp i) (← ty A) (← ty B))
    | .withbor3 _ _ a A B x => return some (.withbor3 (l a) (b x) (← ty A) (← ty B))
    | .withload _ _ a A B x => return some (.withload (l a) (b x) (← ty A) (← ty B))
    | .withswap _ _ a A B => return some (.withswap (l a) (← ty A) (← ty B))
    | .foldImm _ _ F y c R => return some (.foldImm (← rbFShape tbl sp fuel F) (b y) (l c) (← ty R))
    | .foldOwn _ _ F R => return some (.foldOwn (← rbFShape tbl sp fuel F) (← ty R))
    | .foldReuse _ _ F R => return some (.foldReuse (← rbFShape tbl sp fuel F) (← ty R))
    | .unfoldN _ _ C S => return some (.unfold (← rbC tbl sp fuel [] (.nu C)) (← ty S))
    | .lit _ _ c => return some (.lit c)
    | .hostOp _ _ op => return some (.host op)
    | .allocS _ _ σ => return some (.allocS (← rbShape tbl sp fuel σ))
    | .freeS _ _ σ => return some (.freeS (← rbShape tbl sp fuel σ))
    | .withborSM _ _ σ c T => return some (.withborS .mut (← rbShape tbl sp fuel σ) (b c) (← ty T))
    | .withborSI _ _ σ c T => return some (.withborS .imm (← rbShape tbl sp fuel σ) (b c) (← ty T))
    | .withborF2M _ _ c x y A B T =>
      return some (.withborF2Mut (b c) (b x) (b y) (← witOf sp i) (← ty A) (← ty B) (← ty T))
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
    | .boundedFix _ _ A C => return some (.boundedFix (← ty A) (← rbC tbl sp fuel [] C))
    | .sliceBorrowM _ _ A B x => return some (.sliceBorrowMut (b x) (← witOf sp i) (← ty A) (← ty B))
    | .sliceBorrowI _ _ A B x => return some (.sliceBorrowImm (b x) (← witOf sp i) (← ty A) (← ty B))
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
      return some (.withbor2U (b x) (← witOf sp i) (← ty A) (← ty B) (← row S))
    | .withbor3U _ _ a A B S x _ => return some (.withbor3U (l a) (b x) (← ty A) (← ty B) (← row S))
    | .withloadU _ _ a A B S x => return some (.withloadU (l a) (b x) (← ty A) (← ty B) (← row S))
    | .sliceBorrowMU _ _ A B S x _ =>
      return some (.sliceBorrowMutU (b x) (← witOf sp i) (← ty A) (← ty B) (← row S))
    | .sliceBorrowIU _ _ A B S x _ =>
      return some (.sliceBorrowImmU (b x) (← witOf sp i) (← ty A) (← ty B) (← row S))
    | _ => return none

mutual
/-- **The read-back of a node** `t` at the context `cx`: the ascription the node records
(`TInfo.asc`) around the read-back of its form (`rdForm`). -/
def rd : Nat → Cx → TExpr → RB Syn
  | 0, _, _ => throw "read-back: a term nested too deeply"
  | f + 1, cx, t => do
    let sp := t.info.sp
    if t.info.asc then
      match t.jdg, ← rdForm f cx t with
      | .val A, .v V => return .v (.ascribe sp V (← rbV cx.tbl sp fuel [] A))
      | .comp C, .c M => return .c (.ascribe sp M (← rbC cx.tbl sp fuel [] C))
      | _, _ => throw "read-back: an ascription at a node of the other judgment"
    else rdForm f cx t

/-- **The form of a node**: one rule per constructor. -/
def rdForm : Nat → Cx → TExpr → RB Syn
  | 0, _, _ => throw "read-back: a term nested too deeply"
  | f + 1, cx, t => do
    let sp := t.info.sp
    let ty (A : CVTy) := rbV cx.tbl sp fuel [] A
    let val (cx : Cx) (t : TExpr) : RB Val := do (← rd f cx t).val
    let comp (cx : Cx) (t : TExpr) : RB Comp := do (← rd f cx t).comp
    if let some tM := dropOf? t then return ← rd f cx tM
    if let some c ← constOf cx.tbl sp t.info t then return .v (.const sp c)
    match t with
    | .var i _ k _ => do
      let x ← cx.slot k
      pure (.v (if i.clone then .clone sp x else .var sp x))
    | .unitI .. => pure (.v (.unit sp))
    | .tensorI _ _ _ _ _ t₁ t₂ => return .v (.pair sp (← val cx t₁) (← val cx t₂))
    | .sumI₁ _ _ _ _ c => return .v (.inl sp (← val cx c))
    | .sumI₂ _ _ _ _ c => return .v (.inr sp (← val cx c))
    | .thunkF _ _ _ c => return .v (.thunk sp (← comp (cx.push none) c))
    | .thunkV _ _ _ c => return .v (.thunkv sp (← comp cx c))
    | .nuEta _ _ _ _ c => rd f cx c
    | .bangThunkF _ _ _ c => return .v (.bangThunk sp (← comp (cx.push none) c))
    | .bangThunkV _ _ _ c => return .v (.bangThunkv sp (← comp cx c))
    | .bangE _ _ _ c => return .v (.unbang sp (← val cx c))
    | .boxI _ _ a _ c => return .v (.boxed sp (rbL sp a) (← val cx c))
    | .boxE _ _ _ _ c => return .v (.unbox sp (← val cx c))
    | .immSub _ _ a _ _ c | .mutSub _ _ a _ _ c => return .v (.sub sp (← val cx c) (rbL sp a))
    | .roll _ _ _ c => return .v (.roll sp (← val cx c))
    | .unroll _ _ _ c => return .v (.unroll sp (← val cx c))
    | .ofRet _ _ _ c => return .v (.run sp (← comp cx c))
    | .lolliE _ _ _ _ _ ta tf => return .v (.app sp (← val cx tf) (← val cx ta))
    | .allEV _ _ _ _ a _ c => return .v (.inst sp (← val cx c) (rbL sp a))
    | .litFn _ _ bs c => return .v (.mark sp (.litFn bs) (← val cx c))
    | .divLit _ _ op n c => return .v (.mark sp (.divLit op n) (← val cx c))
    | .walk _ _ m _ c => return .v (.mark sp (.walk m) (← val cx c))
    | .walkGet _ _ m c => return .v (.mark sp (.walkGet m) (← val cx c))
    | .selfCall _ _ j n c => return .v (.mark sp (.selfCall j n) (← val cx c))
    | .lendCell _ _ m c => return .v (.mark sp (.lendCell m) (← val cx c))
    | .use _ _ _ decl targs _ _ => do
      -- The instance's declaration, instantiated at the use's lifetimes when it is polymorphic.
      let d ← cx.declOf (decl, targs, cx.Δ.entries, cx.nExt)
      return .v (d.vars.foldl (fun V x => .inst sp V (.var sp (lname x))) (.var sp d.name))
    -- Computations.
    | .effSub i _ _ _ _ c =>
      if i.ins then rd f cx c
      else throw "read-back: a `[sub]` the checker does not record inserting"
    | .ret _ _ _ c => return .c (.ret sp (← val cx c))
    | .bind i _ A _ _ tM tN => do
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      return .c (.bind sp ⟨x, sp⟩ oA (← comp cx tM) (← comp (cx.push x) tN) i.lin)
    | .force _ _ k _ => return .c (.force sp ⟨← cx.slot k, sp⟩)
    | .lam i _ A _ c => do
      let x := cx.binder (some i.name)
      return .c (.lam sp ⟨x, sp⟩ (← ty A) (← comp (cx.push x) c))
    | .lamDead _ _ _ _ c => do
      let x := cx.binder none
      return .c (.lam sp ⟨x, sp⟩ (.unit sp) (← comp (cx.push x) c))
    | .app _ _ k _ _ _ tM => match tM with
      | .nilDead _ _ _ (.lam _ _ _ _ (.lendR iR _ x b A B S _ tR)) => do
        -- R1's relaxed lend (`rLendR`): its body at the view alone.
        let m := cx.binder iR.binders.head?
        let p ← cx.slot k
        let cxR : Cx := { cx with vars := [some m], nExt := 0, Δ := cx.Δ.extend x b }
        return .c (.withbor2r sp ⟨lname x, sp⟩ (boundOf sp iR b) (← ty A) (← ty B)
          (← rbRow cx.tbl sp fuel [] S) ⟨p, sp⟩ ⟨m, sp⟩ (← comp cxR tR))
      | _ => return .c (.app sp (← comp cx tM) ⟨← cx.slot k, sp⟩)
    | .withI _ _ _ _ tM tN => do
      let cx2 := (cx.push none).push none
      return .c (.with_ sp (← comp cx2 tM) (← comp cx2 tN))
    | .proj₁ _ _ _ _ c => return .c (.proj sp true (← comp cx c))
    | .proj₂ _ _ _ _ c => return .c (.proj sp false (← comp cx c))
    | .topI .. => pure (.c (.top sp))
    | .unitE _ _ _ _ tV tM => return .c (.letUnit sp (← val cx tV) (← comp cx tM))
    | .tensorE i _ _ _ _ _ tV tM => do
      let x := cx.binder i.binders.head?
      let y := (cx.push x).binder (i.binders.drop 1).head?
      return .c (.letPair sp ⟨x, sp⟩ ⟨y, sp⟩ (← val cx tV) (← comp ((cx.push x).push y) tM))
    | .sumE i _ _ _ _ _ tV t₁ t₂ => do
      let x := cx.binder i.binders.head?
      let y := cx.binder (i.binders.drop 1).head?
      return .c (.case sp (← val cx tV) ⟨x, sp⟩ (← comp (cx.push x) t₁) ⟨y, sp⟩
        (← comp (cx.push y) t₂))
    | .zeroE _ _ _ _ tV => return .c (.absurd sp (← val cx tV))
    | .allI i _ x b _ _ c =>
      return .c (.lamL sp ⟨lname x, sp⟩ (boundOf sp i b) (← comp { cx.push none with Δ := cx.Δ.extend x b } c))
    | .allE _ _ _ _ a _ c => return .c (.inst sp (← comp cx c) (rbL sp a))
    | .nuIn _ _ _ c => return .c (.nuIn sp (← comp cx c))
    | .nuOut _ _ _ c => return .c (.nuOut sp (← comp cx c))
    | .effPerform _ _ _ o c => return .c (.perform sp o.n.toNat o.i.toNat (← val cx c))
    | .effRaise _ _ _ o _ c => return .c (.abort sp o.n.toNat o.i.toNat (← val cx c))
    | .effLet i _ A _ _ _ tM tN => do
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      return .c (.bind sp ⟨x, sp⟩ oA (← comp cx tM) (← comp (cx.push x) tN) i.lin)
    | .effThen i _ A _ _ _ _ _ tM tN tD => do
      let x := cx.binder i.binders.head?
      let oA ← if i.ann then some <$> ty A else pure none
      let M ← comp cx tM
      let N ← comp (cx.push x) tN
      if i.written then return .c (.unwind sp ⟨x, sp⟩ oA M (← comp (cx.push none) tD) N)
      else return .c (.bind sp ⟨x, sp⟩ oA M N i.lin)
    | .effHandleV i _ _ _ _ n _ _ _ _ site _ tc te
    | .effHandleVB i _ _ _ _ n _ _ _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr tcl := tc | throw "read-back: a handler's pair is not a pair"
      return .c (.handle sp n.toNat .clauses (← siteRecOf i site) (← val cx tr) (← val cx tcl)
        (← comp cx te))
    | .effHandleT i _ _ _ E _ n _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr tcl := tc | throw "read-back: a handler's pair is not a pair"
      return .c (.handle sp n.toNat (.tail (E.map fun e => opCount e.1)) (← siteRecOf i site)
        (← val cx tr) (← val cx tcl) (← comp cx te))
    | .effHandleL i _ _ _ E _ _ n _ _ _ site _ tc te => do
      let .tensorI _ _ _ _ _ tr (.tensorI _ _ _ _ _ tw tn) := tc
        | throw "read-back: a `handle_last`'s clauses are not `(works, exits)`"
      return .c (.handle sp n.toNat (.last (E.map fun e => opCount e.1)) (← siteRecOf i site)
        (← val cx tr) (.pair sp (← val cx tw) (← val cx tn)) (← comp cx te))
    | .dtor .. => throw "read-back: a destructor outside a drop"
    | .lendR .. => throw "read-back: R1's lend outside its application"
    | .nilDead .. => throw "read-back: `nilDead` outside R1's lend"
    | .letPoly .. | .lendLoopR .. | .iterate .. | .divFuel .. | .reify .. =>
      throw "read-back: a node the checker does not produce"
    | t => throw s!"read-back: no rule for the node at {t.info.sp.start.render}"

end

end Rewrite
