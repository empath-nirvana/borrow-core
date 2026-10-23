import Frontend.Check.Program

/-!
# Rewrite — the report  `[spec §54]`

What a run of the rewriter did, and the identity criterion of its step 0 (the scope's M4): the
rewritten `main`'s typed term against the source's, node by node and field by field modulo spans
(`cmpT`), at every use of every instance. A use's own name, declaration and type arguments are
the rewritten declaration's, and its key is compared but for its name; at a lifetime-polymorphic
declaration, the use is the declaration's instantiation at the use's lifetimes, and its body,
under the abstraction's binders, is compared with the source's body moved past them.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo HSite)

/-- The constructor of a node, by name. -/
def kindOf : TExpr → String
  | .var .. => "var"
  | .unitI .. => "unitI"
  | .tensorI .. => "tensorI"
  | .sumI₁ .. => "sumI₁"
  | .sumI₂ .. => "sumI₂"
  | .thunkF .. => "thunkF"
  | .thunkV .. => "thunkV"
  | .ret .. => "ret"
  | .bind .. => "bind"
  | .force .. => "force"
  | .lam .. => "lam"
  | .lamDead .. => "lamDead"
  | .app .. => "app"
  | .withI .. => "withI"
  | .proj₁ .. => "proj₁"
  | .proj₂ .. => "proj₂"
  | .topI .. => "topI"
  | .unitE .. => "unitE"
  | .tensorE .. => "tensorE"
  | .sumE .. => "sumE"
  | .zeroE .. => "zeroE"
  | .allI .. => "allI"
  | .allE .. => "allE"
  | .bangThunkF .. => "bangThunkF"
  | .bangThunkV .. => "bangThunkV"
  | .bangE .. => "bangE"
  | .copyBang .. => "copyBang"
  | .forgetBang .. => "forgetBang"
  | .boxI .. => "boxI"
  | .boxE .. => "boxE"
  | .immSub .. => "immSub"
  | .mutSub .. => "mutSub"
  | .alloc .. => "alloc"
  | .free .. => "free"
  | .swap .. => "swap"
  | .copy .. => "copy"
  | .forgetImm .. => "forgetImm"
  | .forgetMut .. => "forgetMut"
  | .forgetUnk .. => "forgetUnk"
  | .lit .. => "lit"
  | .hostOp .. => "hostOp"
  | .arrNew .. => "arrNew"
  | .arrFree .. => "arrFree"
  | .arrSize .. => "arrSize"
  | .arrReplace .. => "arrReplace"
  | .arrLen .. => "arrLen"
  | .arrGet .. => "arrGet"
  | .arrCopy .. => "arrCopy"
  | .arrForget .. => "arrForget"
  | .countFold .. => "countFold"
  | .countTry .. => "countTry"
  | .boundedFix .. => "boundedFix"
  | .iterate .. => "iterate"
  | .divFuel .. => "divFuel"
  | .reify .. => "reify"
  | .sliceBorrowM .. => "sliceBorrowM"
  | .sliceBorrowI .. => "sliceBorrowI"
  | .sliceGetM .. => "sliceGetM"
  | .sliceLenM .. => "sliceLenM"
  | .sliceSplitI .. => "sliceSplitI"
  | .sliceSplitM .. => "sliceSplitM"
  | .sliceEmptyI .. => "sliceEmptyI"
  | .sliceEmptyM .. => "sliceEmptyM"
  | .sliceReplaceM .. => "sliceReplaceM"
  | .sliceSwapM .. => "sliceSwapM"
  | .withbor1 .. => "withbor1"
  | .withbor2 .. => "withbor2"
  | .withbor3 .. => "withbor3"
  | .withload .. => "withload"
  | .withswap .. => "withswap"
  | .withbor1U .. => "withbor1U"
  | .withbor2U .. => "withbor2U"
  | .withbor3U .. => "withbor3U"
  | .withloadU .. => "withloadU"
  | .sliceBorrowMU .. => "sliceBorrowMU"
  | .sliceBorrowIU .. => "sliceBorrowIU"
  | .lolliE .. => "lolliE"
  | .allEV .. => "allEV"
  | .ofRet .. => "ofRet"
  | .roll .. => "roll"
  | .unroll .. => "unroll"
  | .foldImm .. => "foldImm"
  | .foldOwn .. => "foldOwn"
  | .foldReuse .. => "foldReuse"
  | .nuIn .. => "nuIn"
  | .nuOut .. => "nuOut"
  | .unfoldN .. => "unfoldN"
  | .effSub .. => "effSub"
  | .effPerform .. => "effPerform"
  | .effRaise .. => "effRaise"
  | .effLet .. => "effLet"
  | .effThen .. => "effThen"
  | .effHandleV .. => "effHandleV"
  | .effHandleVB .. => "effHandleVB"
  | .effHandleT .. => "effHandleT"
  | .effHandleL .. => "effHandleL"
  | .letPoly .. => "letPoly"
  | .lendR .. => "lendR"
  | .lendLoopR .. => "lendLoopR"
  | .nilDead .. => "nilDead"
  | .dtor .. => "dtor"
  | .allocS .. => "allocS"
  | .freeS .. => "freeS"
  | .withborSM .. => "withborSM"
  | .withborSI .. => "withborSI"
  | .withborF2M .. => "withborF2M"
  | .withborF2I .. => "withborF2I"
  | .litFn .. => "litFn"
  | .divLit .. => "divLit"
  | .walk .. => "walk"
  | .walkGet .. => "walkGet"
  | .selfCall .. => "selfCall"
  | .lendCell .. => "lendCell"
  | .nuEta .. => "nuEta"
  | .use .. => "use"

/-- What a run did: the instances read back as declarations, the declarations among them that are
lifetime-polymorphic, and the rules applied (none at step 0). -/
structure Report where
  keys : Nat
  decls : Nat
  poly : Nat := 0
  rules : List String := []
  deriving Inhabited

/-- **The identity criterion**: whether `main`'s erasure is the source's (`same`), or differs only
by the instantiations of lifetime-polymorphic declarations (`beta`, when the typed terms agree
everywhere else); and the typed terms' mismatches, by node kind and field. -/
structure Identity where
  erasure : String
  uses : Nat
  mismatches : List (String × Nat)
  deriving Inhabited

/-- Two judgments are the same. -/
def jdgEq : BoCa.Fig16.LogRel.Core.Jdg → BoCa.Fig16.LogRel.Core.Jdg → Bool
  | .val A, .val B => decide (A = B)
  | .comp C, .comp D => decide (C = D)
  | _, _ => false

/-- Count a mismatch. -/
def bump (acc : List (String × Nat)) (k : String) : List (String × Nat) :=
  match acc.lookup k with
  | some n => (acc.filter (·.1 != k)) ++ [(k, n + 1)]
  | none => acc ++ [(k, 1)]

/-- Two elaborator's keys, but for the declaration they name. -/
def keyEq : Option Frontend.DefKey → Option Frontend.DefKey → Bool
  | none, none => true
  | some a, some b => a.origin == b.origin && a.targs == b.targs && a.keys == b.keys && a.body == b.body
  | _, _ => false

/-- The fields of two nodes' sources that differ, modulo spans; at a use, its key but for its
name (`keyEq`). -/
def infoDiff (k : String) (a b : TInfo) (acc : List (String × Nat)) : List (String × Nat) :=
  let f (lab : String) (eq : Bool) (acc : List (String × Nat)) := if eq then acc else bump acc s!"{k}.info.{lab}"
  acc |> f "name" (a.name == b.name) |> f "clone" (a.clone == b.clone)
    |> f "binders" (a.binders == b.binders) |> f "key" (keyEq a.key b.key)
    |> f "written" (a.written == b.written) |> f "ann" (a.ann == b.ann) |> f "lin" (a.lin == b.lin)
    |> f "wit" (decide (a.wit = b.wit)) |> f "asc" (a.asc == b.asc) |> f "ins" (a.ins == b.ins)
    |> f "srec" (decide (a.srec = b.srec))

/-- Two functions agree below `n`. -/
def fnEq {α : Type} [DecidableEq α] (f g : Nat → α) (n : Nat) : Bool :=
  (List.range n).all fun k => decide (f k = g k)

/-- Two sites, field by field. -/
def hsiteEq : Option HSite → Option HSite → Bool
  | none, none => true
  | some a, some b => a.eff == b.eff && decide (a.args = b.args) && a.handler == b.handler &&
      a.slot == b.slot && a.kind == b.kind && decide (a.state = b.state) && a.decl == b.decl
  | _, _ => false

/-- Two fold shapes. -/
def fshapeEq : BoCa.Fig16.LogRel.Core.FShape → BoCa.Fig16.LogRel.Core.FShape → Bool
  | .leaf A, .leaf B => decide (A = B)
  | .refX, .refX | .varX, .varX => true
  | .tensor F G, .tensor F' G' | .sum F G, .sum F' G' => fshapeEq F F' && fshapeEq G G'
  | _, _ => false

/-- Two block shapes. -/
def shapeEq : BoCa.Fig16.LogRel.Core.Shape → BoCa.Fig16.LogRel.Core.Shape → Bool
  | .leaf A, .leaf B => decide (A = B)
  | .node s t, .node s' t' => shapeEq s s' && shapeEq t t'
  | _, _ => false

/-- Two frame sets, field by field. -/
def hinEq (a b : BoCa.Fig16.LogRel.Core.ClauseKinds.HIn) : Bool :=
  a.names == b.names && a.fin == b.fin && a.any == b.any

/-- The instantiations over a node: the node under them, and how many. -/
def peelInst : TExpr → Nat → TExpr × Nat
  | .allEV _ _ _ _ _ _ c, n => peelInst c (n + 1)
  | t, n => (t, n)

/-- The body of a lifetime-polymorphic declaration under its `n` abstractions
(`thunkv Fun 'x < @. return …`). -/
def peelAbs : Nat → TExpr → Option TExpr
  | 0, t => some t
  | n + 1, .thunkV _ _ _ (.allI _ _ _ _ _ _ (.ret _ _ _ c)) => peelAbs n c
  | _ + 1, _ => none

/-- **The typed terms compared**, the source's `a` and the rewritten `b`: node by node and field
by field modulo spans, each field that differs one mismatch, by node kind and field (prefixed
`pre`); a node of another kind is one mismatch and its subterms are not compared. A term nested
deeper than the fuel is an error. -/
def cmpT (pre : String) : Nat → TExpr → TExpr → List (String × Nat) →
    Except String (List (String × Nat))
  | 0, _, _, _ => throw "rewrite: a term nested too deeply to compare"
  | f + 1, .use i₁ j₁ _ _ _ ab₁ t₁, b, acc => do
    let (b', n) := peelInst b 0
    match b' with
    | .use i₂ _ _ _ _ ab₂ t₂ =>
      let mut acc := infoDiff (pre ++ "use") i₁ i₂ acc
      unless jdgEq j₁ b.jdg do acc := bump acc (pre ++ "use.jdg")
      if n == 0 then
        unless decide (ab₁ = ab₂) do acc := bump acc (pre ++ "use.ab")
      match peelAbs n t₂ with
      | some x =>
        if n == 0 then cmpT pre f t₁ x acc
        else
          -- A polymorphic declaration's body is checked at the use's lifetime context extended by
          -- its abstraction's binders: its erasure is the source's, and its fields are compared
          -- and reported apart (`poly:`).
          unless (t₁.shift n 0).erase == x.erase do acc := bump acc (pre ++ "use.erasure")
          cmpT "poly:" f (t₁.shift n 0) x acc
      | none => pure (bump acc (pre ++ "use.instantiation"))
    | b' => pure (bump acc (pre ++ s!"use→{kindOf b'}"))
  | f + 1, .var a_0 a_1 a_2 a_3, .var b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "var") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "var.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "var.i")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "var.A")
    pure acc
  | f + 1, .unitI a_0 a_1, .unitI b_0 b_1, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "unitI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "unitI.jdg")
    pure acc
  | f + 1, .tensorI a_0 a_1 a_2 a_3 a_4 a_5 a_6, .tensorI b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "tensorI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "tensorI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "tensorI.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "tensorI.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "tensorI.u")
    acc ← cmpT pre f a_5 b_5 acc
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .sumI₁ a_0 a_1 a_2 a_3 a_4, .sumI₁ b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sumI₁") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sumI₁.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sumI₁.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sumI₁.B")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .sumI₂ a_0 a_1 a_2 a_3 a_4, .sumI₂ b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sumI₂") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sumI₂.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sumI₂.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sumI₂.B")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .thunkF a_0 a_1 a_2 a_3, .thunkF b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "thunkF") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "thunkF.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "thunkF.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .thunkV a_0 a_1 a_2 a_3, .thunkV b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "thunkV") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "thunkV.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "thunkV.C")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .ret a_0 a_1 a_2 a_3, .ret b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "ret") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "ret.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "ret.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .bind a_0 a_1 a_2 a_3 a_4 a_5 a_6, .bind b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "bind") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "bind.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "bind.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "bind.C")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "bind.u")
    acc ← cmpT pre f a_5 b_5 acc
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .force a_0 a_1 a_2 a_3, .force b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "force") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "force.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "force.i")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "force.C")
    pure acc
  | f + 1, .lam a_0 a_1 a_2 a_3 a_4, .lam b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lam") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lam.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lam.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "lam.C")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .lamDead a_0 a_1 a_2 a_3 a_4, .lamDead b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lamDead") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lamDead.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lamDead.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "lamDead.B")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .app a_0 a_1 a_2 a_3 a_4 a_5 a_6, .app b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "app") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "app.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "app.i")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "app.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "app.C")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "app.u")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .withI a_0 a_1 a_2 a_3 a_4 a_5, .withI b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withI.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withI.D")
    acc ← cmpT pre f a_4 b_4 acc
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .proj₁ a_0 a_1 a_2 a_3 a_4, .proj₁ b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "proj₁") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "proj₁.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "proj₁.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "proj₁.D")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .proj₂ a_0 a_1 a_2 a_3 a_4, .proj₂ b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "proj₂") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "proj₂.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "proj₂.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "proj₂.D")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .topI a_0 a_1, .topI b_0 b_1, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "topI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "topI.jdg")
    pure acc
  | f + 1, .unitE a_0 a_1 a_2 a_3 a_4 a_5, .unitE b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "unitE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "unitE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "unitE.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "unitE.u")
    acc ← cmpT pre f a_4 b_4 acc
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .tensorE a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7, .tensorE b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "tensorE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "tensorE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "tensorE.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "tensorE.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "tensorE.C")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "tensorE.u")
    acc ← cmpT pre f a_6 b_6 acc
    acc ← cmpT pre f a_7 b_7 acc
    pure acc
  | f + 1, .sumE a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8, .sumE b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sumE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sumE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sumE.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sumE.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "sumE.C")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "sumE.u")
    acc ← cmpT pre f a_6 b_6 acc
    acc ← cmpT pre f a_7 b_7 acc
    acc ← cmpT pre f a_8 b_8 acc
    pure acc
  | f + 1, .zeroE a_0 a_1 a_2 a_3 a_4, .zeroE b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "zeroE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "zeroE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "zeroE.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "zeroE.u")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .allI a_0 a_1 a_2 a_3 a_4 a_5 a_6, .allI b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "allI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "allI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "allI.x")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "allI.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "allI.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "allI.C")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .allE a_0 a_1 a_2 a_3 a_4 a_5 a_6, .allE b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "allE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "allE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "allE.x")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "allE.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "allE.a")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "allE.C")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .bangThunkF a_0 a_1 a_2 a_3, .bangThunkF b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "bangThunkF") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "bangThunkF.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "bangThunkF.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .bangThunkV a_0 a_1 a_2 a_3, .bangThunkV b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "bangThunkV") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "bangThunkV.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "bangThunkV.C")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .bangE a_0 a_1 a_2 a_3, .bangE b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "bangE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "bangE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "bangE.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .copyBang a_0 a_1 a_2, .copyBang b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "copyBang") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "copyBang.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "copyBang.A")
    pure acc
  | f + 1, .forgetBang a_0 a_1 a_2, .forgetBang b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "forgetBang") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "forgetBang.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "forgetBang.A")
    pure acc
  | f + 1, .boxI a_0 a_1 a_2 a_3 a_4, .boxI b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "boxI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "boxI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "boxI.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "boxI.A")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .boxE a_0 a_1 a_2 a_3 a_4, .boxE b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "boxE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "boxE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "boxE.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "boxE.A")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .immSub a_0 a_1 a_2 a_3 a_4 a_5, .immSub b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "immSub") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "immSub.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "immSub.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "immSub.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "immSub.A")
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .mutSub a_0 a_1 a_2 a_3 a_4 a_5, .mutSub b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "mutSub") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "mutSub.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "mutSub.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "mutSub.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "mutSub.A")
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .alloc a_0 a_1 a_2, .alloc b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "alloc") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "alloc.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "alloc.A")
    pure acc
  | f + 1, .free a_0 a_1 a_2, .free b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "free") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "free.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "free.A")
    pure acc
  | f + 1, .swap a_0 a_1 a_2 a_3, .swap b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "swap") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "swap.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "swap.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "swap.B")
    pure acc
  | f + 1, .copy a_0 a_1 a_2 a_3, .copy b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "copy") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "copy.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "copy.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "copy.A")
    pure acc
  | f + 1, .forgetImm a_0 a_1 a_2 a_3, .forgetImm b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "forgetImm") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "forgetImm.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "forgetImm.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "forgetImm.A")
    pure acc
  | f + 1, .forgetMut a_0 a_1 a_2 a_3, .forgetMut b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "forgetMut") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "forgetMut.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "forgetMut.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "forgetMut.A")
    pure acc
  | f + 1, .forgetUnk a_0 a_1, .forgetUnk b_0 b_1, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "forgetUnk") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "forgetUnk.jdg")
    pure acc
  | f + 1, .lit a_0 a_1 a_2, .lit b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lit") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lit.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lit.c")
    pure acc
  | f + 1, .hostOp a_0 a_1 a_2, .hostOp b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "hostOp") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "hostOp.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "hostOp.op")
    pure acc
  | f + 1, .arrNew a_0 a_1 a_2, .arrNew b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrNew") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrNew.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrNew.A")
    pure acc
  | f + 1, .arrFree a_0 a_1 a_2, .arrFree b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrFree") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrFree.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrFree.A")
    pure acc
  | f + 1, .arrSize a_0 a_1 a_2, .arrSize b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrSize") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrSize.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrSize.A")
    pure acc
  | f + 1, .arrReplace a_0 a_1 a_2, .arrReplace b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrReplace") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrReplace.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrReplace.A")
    pure acc
  | f + 1, .arrLen a_0 a_1 a_2 a_3, .arrLen b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrLen") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrLen.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrLen.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "arrLen.A")
    pure acc
  | f + 1, .arrGet a_0 a_1 a_2 a_3, .arrGet b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrGet") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrGet.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrGet.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "arrGet.A")
    pure acc
  | f + 1, .arrCopy a_0 a_1 a_2 a_3, .arrCopy b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrCopy") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrCopy.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrCopy.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "arrCopy.A")
    pure acc
  | f + 1, .arrForget a_0 a_1 a_2 a_3, .arrForget b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "arrForget") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "arrForget.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "arrForget.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "arrForget.A")
    pure acc
  | f + 1, .countFold a_0 a_1 a_2, .countFold b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "countFold") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "countFold.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "countFold.S")
    pure acc
  | f + 1, .countTry a_0 a_1 a_2 a_3, .countTry b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "countTry") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "countTry.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "countTry.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "countTry.E")
    pure acc
  | f + 1, .boundedFix a_0 a_1 a_2 a_3, .boundedFix b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "boundedFix") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "boundedFix.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "boundedFix.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "boundedFix.C")
    pure acc
  | f + 1, .iterate a_0 a_1 a_2 a_3 a_4 a_5, .iterate b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "iterate") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "iterate.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "iterate.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "iterate.St")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "iterate.B")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "iterate.R")
    pure acc
  | f + 1, .divFuel a_0 a_1 a_2 a_3, .divFuel b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "divFuel") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "divFuel.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "divFuel.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "divFuel.A")
    pure acc
  | f + 1, .reify a_0 a_1 a_2 a_3 a_4 a_5, .reify b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "reify") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "reify.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "reify.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "reify.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "reify.R")
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .sliceBorrowM a_0 a_1 a_2 a_3 a_4, .sliceBorrowM b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceBorrowM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceBorrowM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceBorrowM.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceBorrowM.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "sliceBorrowM.x")
    pure acc
  | f + 1, .sliceBorrowI a_0 a_1 a_2 a_3 a_4, .sliceBorrowI b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceBorrowI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceBorrowI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceBorrowI.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceBorrowI.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "sliceBorrowI.x")
    pure acc
  | f + 1, .sliceGetM a_0 a_1 a_2 a_3, .sliceGetM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceGetM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceGetM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceGetM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceGetM.A")
    pure acc
  | f + 1, .sliceLenM a_0 a_1 a_2 a_3, .sliceLenM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceLenM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceLenM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceLenM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceLenM.A")
    pure acc
  | f + 1, .sliceSplitI a_0 a_1 a_2 a_3, .sliceSplitI b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceSplitI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceSplitI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceSplitI.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceSplitI.A")
    pure acc
  | f + 1, .sliceSplitM a_0 a_1 a_2 a_3, .sliceSplitM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceSplitM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceSplitM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceSplitM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceSplitM.A")
    pure acc
  | f + 1, .sliceEmptyI a_0 a_1 a_2 a_3, .sliceEmptyI b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceEmptyI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceEmptyI.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceEmptyI.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceEmptyI.A")
    pure acc
  | f + 1, .sliceEmptyM a_0 a_1 a_2 a_3, .sliceEmptyM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceEmptyM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceEmptyM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceEmptyM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceEmptyM.A")
    pure acc
  | f + 1, .sliceReplaceM a_0 a_1 a_2 a_3, .sliceReplaceM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceReplaceM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceReplaceM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceReplaceM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceReplaceM.A")
    pure acc
  | f + 1, .sliceSwapM a_0 a_1 a_2 a_3, .sliceSwapM b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceSwapM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceSwapM.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceSwapM.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceSwapM.A")
    pure acc
  | f + 1, .withbor1 a_0 a_1 a_2 a_3 a_4, .withbor1 b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor1") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor1.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor1.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor1.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor1.x")
    pure acc
  | f + 1, .withbor2 a_0 a_1 a_2 a_3 a_4, .withbor2 b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor2") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor2.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor2.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor2.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor2.x")
    pure acc
  | f + 1, .withbor3 a_0 a_1 a_2 a_3 a_4 a_5, .withbor3 b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor3") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor3.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor3.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor3.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor3.B")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withbor3.x")
    pure acc
  | f + 1, .withload a_0 a_1 a_2 a_3 a_4 a_5, .withload b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withload") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withload.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withload.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withload.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withload.B")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withload.x")
    pure acc
  | f + 1, .withswap a_0 a_1 a_2 a_3 a_4, .withswap b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withswap") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withswap.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withswap.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withswap.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withswap.B")
    pure acc
  | f + 1, .withbor1U a_0 a_1 a_2 a_3 a_4 a_5 a_6, .withbor1U b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor1U") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor1U.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor1U.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor1U.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor1U.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withbor1U.x")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .withbor2U a_0 a_1 a_2 a_3 a_4 a_5 a_6, .withbor2U b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor2U") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor2U.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor2U.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor2U.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor2U.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withbor2U.x")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .withbor3U a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7, .withbor3U b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withbor3U") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withbor3U.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withbor3U.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withbor3U.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withbor3U.B")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withbor3U.S")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "withbor3U.x")
    acc ← cmpT pre f a_7 b_7 acc
    pure acc
  | f + 1, .withloadU a_0 a_1 a_2 a_3 a_4 a_5 a_6, .withloadU b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withloadU") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withloadU.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withloadU.a")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withloadU.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withloadU.B")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withloadU.S")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "withloadU.x")
    pure acc
  | f + 1, .sliceBorrowMU a_0 a_1 a_2 a_3 a_4 a_5 a_6, .sliceBorrowMU b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceBorrowMU") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceBorrowMU.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceBorrowMU.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceBorrowMU.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "sliceBorrowMU.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "sliceBorrowMU.x")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .sliceBorrowIU a_0 a_1 a_2 a_3 a_4 a_5 a_6, .sliceBorrowIU b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "sliceBorrowIU") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "sliceBorrowIU.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "sliceBorrowIU.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "sliceBorrowIU.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "sliceBorrowIU.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "sliceBorrowIU.x")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .lolliE a_0 a_1 a_2 a_3 a_4 a_5 a_6, .lolliE b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lolliE") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lolliE.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lolliE.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "lolliE.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "lolliE.u")
    acc ← cmpT pre f a_5 b_5 acc
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .allEV a_0 a_1 a_2 a_3 a_4 a_5 a_6, .allEV b_0 b_1 b_2 b_3 b_4 b_5 b_6, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "allEV") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "allEV.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "allEV.x")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "allEV.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "allEV.a")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "allEV.A")
    acc ← cmpT pre f a_6 b_6 acc
    pure acc
  | f + 1, .ofRet a_0 a_1 a_2 a_3, .ofRet b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "ofRet") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "ofRet.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "ofRet.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .roll a_0 a_1 a_2 a_3, .roll b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "roll") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "roll.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "roll.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .unroll a_0 a_1 a_2 a_3, .unroll b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "unroll") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "unroll.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "unroll.A")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .foldImm a_0 a_1 a_2 a_3 a_4 a_5, .foldImm b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "foldImm") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "foldImm.jdg")
    unless fshapeEq a_2 b_2 do acc := bump acc (pre ++ "foldImm.F")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "foldImm.y")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "foldImm.c")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "foldImm.R")
    pure acc
  | f + 1, .foldOwn a_0 a_1 a_2 a_3, .foldOwn b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "foldOwn") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "foldOwn.jdg")
    unless fshapeEq a_2 b_2 do acc := bump acc (pre ++ "foldOwn.F")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "foldOwn.R")
    pure acc
  | f + 1, .foldReuse a_0 a_1 a_2 a_3, .foldReuse b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "foldReuse") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "foldReuse.jdg")
    unless fshapeEq a_2 b_2 do acc := bump acc (pre ++ "foldReuse.F")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "foldReuse.R")
    pure acc
  | f + 1, .nuIn a_0 a_1 a_2 a_3, .nuIn b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "nuIn") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "nuIn.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "nuIn.C")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .nuOut a_0 a_1 a_2 a_3, .nuOut b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "nuOut") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "nuOut.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "nuOut.C")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .unfoldN a_0 a_1 a_2 a_3, .unfoldN b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "unfoldN") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "unfoldN.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "unfoldN.C")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "unfoldN.S")
    pure acc
  | f + 1, .effSub a_0 a_1 a_2 a_3 a_4 a_5, .effSub b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effSub") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effSub.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effSub.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effSub.S'")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effSub.A")
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .effPerform a_0 a_1 a_2 a_3 a_4, .effPerform b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effPerform") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effPerform.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effPerform.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effPerform.o")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .effRaise a_0 a_1 a_2 a_3 a_4 a_5, .effRaise b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effRaise") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effRaise.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effRaise.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effRaise.o")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effRaise.B")
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .effLet a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7, .effLet b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effLet") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effLet.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effLet.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effLet.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effLet.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "effLet.u")
    acc ← cmpT pre f a_6 b_6 acc
    acc ← cmpT pre f a_7 b_7 acc
    pure acc
  | f + 1, .effThen a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10, .effThen b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effThen") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effThen.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effThen.A")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effThen.B")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effThen.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "effThen.SM")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "effThen.SD")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "effThen.u")
    acc ← cmpT pre f a_8 b_8 acc
    acc ← cmpT pre f a_9 b_9 acc
    acc ← cmpT pre f a_10 b_10 acc
    pure acc
  | f + 1, .effHandleV a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11 a_12 a_13, .effHandleV b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effHandleV") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effHandleV.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effHandleV.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effHandleV.E")
    unless fnEq a_4 b_4 a_3.length do acc := bump acc (pre ++ "effHandleV.fs")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "effHandleV.n")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "effHandleV.A")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "effHandleV.R")
    unless decide (a_8 = b_8) do acc := bump acc (pre ++ "effHandleV.u")
    unless decide (a_9 = b_9) do acc := bump acc (pre ++ "effHandleV.ks")
    unless hsiteEq a_10 b_10 do acc := bump acc (pre ++ "effHandleV.site")
    unless hinEq a_11 b_11 do acc := bump acc (pre ++ "effHandleV.inside")
    acc ← cmpT pre f a_12 b_12 acc
    acc ← cmpT pre f a_13 b_13 acc
    pure acc
  | f + 1, .effHandleVB a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11 a_12 a_13 a_14, .effHandleVB b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effHandleVB") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effHandleVB.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effHandleVB.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effHandleVB.E")
    unless fnEq a_4 b_4 a_3.length do acc := bump acc (pre ++ "effHandleVB.fs")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "effHandleVB.n")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "effHandleVB.A")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "effHandleVB.R")
    unless decide (a_8 = b_8) do acc := bump acc (pre ++ "effHandleVB.d")
    unless decide (a_9 = b_9) do acc := bump acc (pre ++ "effHandleVB.u")
    unless decide (a_10 = b_10) do acc := bump acc (pre ++ "effHandleVB.ks")
    unless hsiteEq a_11 b_11 do acc := bump acc (pre ++ "effHandleVB.site")
    unless hinEq a_12 b_12 do acc := bump acc (pre ++ "effHandleVB.inside")
    acc ← cmpT pre f a_13 b_13 acc
    acc ← cmpT pre f a_14 b_14 acc
    pure acc
  | f + 1, .effHandleT a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11 a_12 a_13, .effHandleT b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effHandleT") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effHandleT.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effHandleT.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effHandleT.SN")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effHandleT.E")
    unless fnEq a_5 b_5 a_4.length do acc := bump acc (pre ++ "effHandleT.fs")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "effHandleT.n")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "effHandleT.A")
    unless decide (a_8 = b_8) do acc := bump acc (pre ++ "effHandleT.R")
    unless decide (a_9 = b_9) do acc := bump acc (pre ++ "effHandleT.u")
    unless hsiteEq a_10 b_10 do acc := bump acc (pre ++ "effHandleT.site")
    unless hinEq a_11 b_11 do acc := bump acc (pre ++ "effHandleT.inside")
    acc ← cmpT pre f a_12 b_12 acc
    acc ← cmpT pre f a_13 b_13 acc
    pure acc
  | f + 1, .effHandleL a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11 a_12 a_13 a_14, .effHandleL b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11 b_12 b_13 b_14, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "effHandleL") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "effHandleL.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "effHandleL.S")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "effHandleL.SW")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "effHandleL.E")
    unless fnEq a_5 b_5 a_4.length do acc := bump acc (pre ++ "effHandleL.fs")
    unless fnEq a_6 b_6 a_4.length do acc := bump acc (pre ++ "effHandleL.Xs")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "effHandleL.n")
    unless decide (a_8 = b_8) do acc := bump acc (pre ++ "effHandleL.A")
    unless decide (a_9 = b_9) do acc := bump acc (pre ++ "effHandleL.R")
    unless decide (a_10 = b_10) do acc := bump acc (pre ++ "effHandleL.u")
    unless hsiteEq a_11 b_11 do acc := bump acc (pre ++ "effHandleL.site")
    unless hinEq a_12 b_12 do acc := bump acc (pre ++ "effHandleL.inside")
    acc ← cmpT pre f a_13 b_13 acc
    acc ← cmpT pre f a_14 b_14 acc
    pure acc
  | f + 1, .letPoly a_0 a_1 a_2 a_3 a_4 a_5, .letPoly b_0 b_1 b_2 b_3 b_4 b_5, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "letPoly") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "letPoly.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "letPoly.C")
    unless jdgEq a_3 b_3 do acc := bump acc (pre ++ "letPoly.j")
    acc ← cmpT pre f a_4 b_4 acc
    acc ← cmpT pre f a_5 b_5 acc
    pure acc
  | f + 1, .lendR a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8, .lendR b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lendR") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lendR.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lendR.x")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "lendR.b")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "lendR.T")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "lendR.B")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "lendR.S")
    acc ← cmpT pre f a_7 b_7 acc
    acc ← cmpT pre f a_8 b_8 acc
    pure acc
  | f + 1, .lendLoopR a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9, .lendLoopR b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lendLoopR") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lendLoopR.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lendLoopR.x")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "lendLoopR.A")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "lendLoopR.S")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "lendLoopR.B")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "lendLoopR.R")
    acc ← cmpT pre f a_7 b_7 acc
    acc ← cmpT pre f a_8 b_8 acc
    acc ← cmpT pre f a_9 b_9 acc
    pure acc
  | f + 1, .nilDead a_0 a_1 a_2 a_3, .nilDead b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "nilDead") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "nilDead.jdg")
    unless jdgEq a_2 b_2 do acc := bump acc (pre ++ "nilDead.j")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .dtor a_0 a_1 a_2, .dtor b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "dtor") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "dtor.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "dtor.A")
    pure acc
  | f + 1, .allocS a_0 a_1 a_2, .allocS b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "allocS") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "allocS.jdg")
    unless shapeEq a_2 b_2 do acc := bump acc (pre ++ "allocS.σ")
    pure acc
  | f + 1, .freeS a_0 a_1 a_2, .freeS b_0 b_1 b_2, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "freeS") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "freeS.jdg")
    unless shapeEq a_2 b_2 do acc := bump acc (pre ++ "freeS.σ")
    pure acc
  | f + 1, .withborSM a_0 a_1 a_2 a_3 a_4, .withborSM b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withborSM") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withborSM.jdg")
    unless shapeEq a_2 b_2 do acc := bump acc (pre ++ "withborSM.σ")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withborSM.c")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withborSM.T")
    pure acc
  | f + 1, .withborSI a_0 a_1 a_2 a_3 a_4, .withborSI b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withborSI") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withborSI.jdg")
    unless shapeEq a_2 b_2 do acc := bump acc (pre ++ "withborSI.σ")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withborSI.c")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withborSI.T")
    pure acc
  | f + 1, .withborF2M a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7, .withborF2M b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withborF2M") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withborF2M.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withborF2M.c")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withborF2M.x")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withborF2M.y")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withborF2M.A")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "withborF2M.B")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "withborF2M.T")
    pure acc
  | f + 1, .withborF2I a_0 a_1 a_2 a_3 a_4 a_5 a_6 a_7, .withborF2I b_0 b_1 b_2 b_3 b_4 b_5 b_6 b_7, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "withborF2I") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "withborF2I.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "withborF2I.c")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "withborF2I.x")
    unless decide (a_4 = b_4) do acc := bump acc (pre ++ "withborF2I.y")
    unless decide (a_5 = b_5) do acc := bump acc (pre ++ "withborF2I.A")
    unless decide (a_6 = b_6) do acc := bump acc (pre ++ "withborF2I.B")
    unless decide (a_7 = b_7) do acc := bump acc (pre ++ "withborF2I.T")
    pure acc
  | f + 1, .litFn a_0 a_1 a_2 a_3, .litFn b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "litFn") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "litFn.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "litFn.bs")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .divLit a_0 a_1 a_2 a_3 a_4, .divLit b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "divLit") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "divLit.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "divLit.op")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "divLit.c")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .walk a_0 a_1 a_2 a_3 a_4, .walk b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "walk") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "walk.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "walk.m")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "walk.read")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .walkGet a_0 a_1 a_2 a_3, .walkGet b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "walkGet") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "walkGet.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "walkGet.m")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .selfCall a_0 a_1 a_2 a_3 a_4, .selfCall b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "selfCall") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "selfCall.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "selfCall.j")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "selfCall.n")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | f + 1, .lendCell a_0 a_1 a_2 a_3, .lendCell b_0 b_1 b_2 b_3, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "lendCell") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "lendCell.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "lendCell.m")
    acc ← cmpT pre f a_3 b_3 acc
    pure acc
  | f + 1, .nuEta a_0 a_1 a_2 a_3 a_4, .nuEta b_0 b_1 b_2 b_3 b_4, acc => do
    let mut acc := acc
    acc := infoDiff (pre ++ "nuEta") a_0 b_0 acc
    unless jdgEq a_1 b_1 do acc := bump acc (pre ++ "nuEta.jdg")
    unless decide (a_2 = b_2) do acc := bump acc (pre ++ "nuEta.f")
    unless decide (a_3 = b_3) do acc := bump acc (pre ++ "nuEta.s")
    acc ← cmpT pre f a_4 b_4 acc
    pure acc
  | _ + 1, a, b, acc => pure (bump acc (pre ++ s!"{kindOf a}→{kindOf b}"))

/-- The pairs of subterms at which the source's `a` and the rewritten `b` differ in kind, at most
`n` of them (`bcc rewrite --diff`). -/
def mismatchPairs (n : Nat) : Nat → TExpr → TExpr → List (TExpr × TExpr) →
    Except String (List (TExpr × TExpr))
  | 0, _, _, _ => throw "rewrite: a term nested too deeply to compare"
  | f + 1, a, b, acc => do
    if acc.length ≥ n then return acc
    let (b', k) := match a with
      | .use .. => peelInst b 0
      | _ => (b, 0)
    if kindOf a != kindOf b' then return acc ++ [(a, b)]
    let cb := match a, b' with
      | .use .., .use _ _ _ _ _ _ t => ((peelAbs k t).map fun x => [x]).getD []
      | _, _ => b'.children.map (fun (p : BoCa.Fig16.LogRel.Core.Check.TScope × TExpr) => p.2)
    let ca := match a with
      | .use _ _ _ _ _ _ t => [t.shift k 0]
      | _ => a.children.map (fun (p : BoCa.Fig16.LogRel.Core.Check.TScope × TExpr) => p.2)
    if ca.length != cb.length then return acc ++ [(a, b)]
    (ca.zip cb).foldlM (fun acc (x, y) => mismatchPairs n f x y acc) acc

end Rewrite
