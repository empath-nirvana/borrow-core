import Frontend.Check.Program

/-!
# Rewrite — the report  `[spec §54]`

What a run of the rewriter did, and the identity criterion of its step 0 (the scope's M4): the
erasure of the rewritten `main` and of each key's body against the source's, and the typed
term's mismatches, by node kind.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core.Check (TExpr)

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

/-- What a run did: the keys read back as declarations, and the rules applied (none at step 0). -/
structure Report where
  keys : Nat
  decls : Nat
  rules : List String := []
  deriving Inhabited

/-- **The identity criterion**: whether `main`'s erasure is the source's, how many keys' bodies
erase to the source's of how many, and the typed term's mismatches: each pair of node kinds at
which the two terms first differ (a kind and a type, or a kind and another kind), with its count. -/
structure Identity where
  mainEq : Bool
  keysEq : Nat
  keys : Nat
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

/-- **The typed term's mismatches** between the source's `a` and the rewritten `b`, by node kind:
walking both, a node of another kind, another judgment or another number of children is one
mismatch, and its subterms are not compared. A term nested deeper than the fuel is an error. A `use` node is compared by its body: its name and
key are the monomorphic declaration's. -/
def mismatches : Nat → TExpr → TExpr → List (String × Nat) → Except String (List (String × Nat))
  | 0, _, _, _ => throw "rewrite: a term nested too deeply to compare"
  | f + 1, a, b, acc =>
    if kindOf a != kindOf b then pure (bump acc s!"{kindOf a}→{kindOf b}")
    else if !(a matches .use ..) && !jdgEq a.jdg b.jdg then pure (bump acc s!"{kindOf a}:type")
    else
      let ca := a.children.map (·.2)
      let cb := b.children.map (·.2)
      if ca.length != cb.length then pure (bump acc s!"{kindOf a}:children")
      else (ca.zip cb).foldlM (fun acc (x, y) => mismatches f x y acc) acc

/-- The pairs of subterms at which the source's `a` and the rewritten `b` first differ, as
`mismatches` finds them, at most `n` of them. -/
def mismatchPairs (n : Nat) : Nat → TExpr → TExpr → List (TExpr × TExpr) →
    Except String (List (TExpr × TExpr))
  | 0, _, _, _ => throw "rewrite: a term nested too deeply to compare"
  | f + 1, a, b, acc =>
    if acc.length ≥ n then pure acc
    else if kindOf a != kindOf b || (!(a matches .use ..) && !jdgEq a.jdg b.jdg) then pure (acc ++ [(a, b)])
    else
      let ca := a.children.map (·.2)
      let cb := b.children.map (·.2)
      if ca.length != cb.length then pure (acc ++ [(a, b)])
      else (ca.zip cb).foldlM (fun acc (x, y) => mismatchPairs n f x y acc) acc

end Rewrite
