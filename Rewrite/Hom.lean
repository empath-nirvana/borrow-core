import Frontend.Check.Program

/-!
# Rewrite — a homomorphic layer over the typed term  `[spec §54]`

A rule that translates types (R1, `Rewrite/Tail.lean`) rewrites most nodes homomorphically: the
node's own types translated, its children rewritten, every other field kept. `homLayer` is that one
layer, constructor by constructor: a rule handles the nodes its schema lists and hands every other
node to it, with itself for the children. Every field but the types is kept as the node has it
(`TInfo`, masks, kinds, sites, lifetimes), so no binder's name, id or declaration is rebuilt.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count Jdg FShape Shape)
open BoCa.Fig16.LogRel.Core.Check (TExpr)

/-- **A translation of types**: of value and computation types, of rows, and of operations'
signatures. -/
structure TyMap where
  v : VTy → VTy
  c : CTy → CTy
  row : Row → Row
  op : OpSig → OpSig

/-- A judgment, translated. -/
def TyMap.j (m : TyMap) : Jdg → Jdg
  | .val A => .val (m.v A)
  | .comp C => .comp (m.c C)

/-- A handler's operations, translated. -/
def TyMap.E (m : TyMap) (E : List (Count × VTy × VTy)) : List (Count × VTy × VTy) :=
  E.map fun (q, A, B) => (q, m.v A, m.v B)

/-- A fold's shape, its leaves translated. -/
def TyMap.fshape (m : TyMap) : FShape → FShape
  | .leaf A => .leaf (m.v A)
  | .refX => .refX
  | .varX => .varX
  | .tensor F G => .tensor (m.fshape F) (m.fshape G)
  | .sum F G => .sum (m.fshape F) (m.fshape G)

/-- A block's shape, its leaves translated. -/
def TyMap.shape (m : TyMap) : Shape → Shape
  | .leaf A => .leaf (m.v A)
  | .node s t => .node (m.shape s) (m.shape t)

/-- **One homomorphic layer**: the node `t` with its types translated by `m` and its children
rewritten by `f`, every other field kept. -/
def homLayer {M : Type → Type} [Monad M] (m : TyMap) (f : TExpr → M TExpr) (t : TExpr) : M TExpr :=
  let V := m.v
  let C := m.c
  let J := m.j
  let R := m.row
  match t with
  | .var i j k A => pure (.var i (J j) k (V A))
  | .unitI i j => pure (.unitI i (J j))
  | .tensorI i j A B u t₁ t₂ => return .tensorI i (J j) (V A) (V B) u (← f t₁) (← f t₂)
  | .sumI₁ i j A B c => return .sumI₁ i (J j) (V A) (V B) (← f c)
  | .sumI₂ i j A B c => return .sumI₂ i (J j) (V A) (V B) (← f c)
  | .thunkF i j A c => return .thunkF i (J j) (V A) (← f c)
  | .thunkV i j D c => return .thunkV i (J j) (C D) (← f c)
  | .ret i j A c => return .ret i (J j) (V A) (← f c)
  | .bind i j A D u tM tN => return .bind i (J j) (V A) (C D) u (← f tM) (← f tN)
  | .force i j k D => pure (.force i (J j) k (C D))
  | .lam i j A D c => return .lam i (J j) (V A) (C D) (← f c)
  | .lamDead i j S B c => return .lamDead i (J j) (R S) (V B) (← f c)
  | .app i j k A D u tM => return .app i (J j) k (V A) (C D) u (← f tM)
  | .withI i j D D' tM tN => return .withI i (J j) (C D) (C D') (← f tM) (← f tN)
  | .proj₁ i j D D' c => return .proj₁ i (J j) (C D) (C D') (← f c)
  | .proj₂ i j D D' c => return .proj₂ i (J j) (C D) (C D') (← f c)
  | .topI i j => pure (.topI i (J j))
  | .unitE i j D u tV tM => return .unitE i (J j) (C D) u (← f tV) (← f tM)
  | .tensorE i j A B D u tV tM => return .tensorE i (J j) (V A) (V B) (C D) u (← f tV) (← f tM)
  | .sumE i j A B D u tV t₁ t₂ =>
    return .sumE i (J j) (V A) (V B) (C D) u (← f tV) (← f t₁) (← f t₂)
  | .zeroE i j D u tV => return .zeroE i (J j) (C D) u (← f tV)
  | .allI i j x b S D c => return .allI i (J j) x b (V S) (C D) (← f c)
  | .allE i j x b l D c => return .allE i (J j) x b l (C D) (← f c)
  | .bangThunkF i j A c => return .bangThunkF i (J j) (V A) (← f c)
  | .bangThunkV i j D c => return .bangThunkV i (J j) (C D) (← f c)
  | .bangE i j A c => return .bangE i (J j) (V A) (← f c)
  | .copyBang i j A => pure (.copyBang i (J j) (V A))
  | .forgetBang i j A => pure (.forgetBang i (J j) (V A))
  | .boxI i j l A c => return .boxI i (J j) l (V A) (← f c)
  | .boxE i j l A c => return .boxE i (J j) l (V A) (← f c)
  | .immSub i j l b A c => return .immSub i (J j) l b (V A) (← f c)
  | .mutSub i j l b A c => return .mutSub i (J j) l b (V A) (← f c)
  | .alloc i j A => pure (.alloc i (J j) (V A))
  | .free i j A => pure (.free i (J j) (V A))
  | .swap i j A B => pure (.swap i (J j) (V A) (V B))
  | .copy i j l A => pure (.copy i (J j) l (V A))
  | .forgetImm i j l A => pure (.forgetImm i (J j) l (V A))
  | .forgetMut i j l A => pure (.forgetMut i (J j) l (V A))
  | .forgetUnk i j => pure (.forgetUnk i (J j))
  | .lit i j c => pure (.lit i (J j) c)
  | .hostOp i j op => pure (.hostOp i (J j) op)
  | .arrNew i j A => pure (.arrNew i (J j) (V A))
  | .arrFree i j A => pure (.arrFree i (J j) (V A))
  | .arrSize i j A => pure (.arrSize i (J j) (V A))
  | .arrReplace i j A => pure (.arrReplace i (J j) (V A))
  | .arrLen i j l A => pure (.arrLen i (J j) l (V A))
  | .arrGet i j l A => pure (.arrGet i (J j) l (V A))
  | .arrCopy i j l A => pure (.arrCopy i (J j) l (V A))
  | .arrForget i j l A => pure (.arrForget i (J j) l (V A))
  | .countFold i j S => pure (.countFold i (J j) (V S))
  | .countTry i j S E => pure (.countTry i (J j) (V S) (V E))
  | .boundedFix i j A D => pure (.boundedFix i (J j) (V A) (C D))
  | .iterate i j S St B R' => pure (.iterate i (J j) (R S) (V St) (V B) (V R'))
  | .divFuel i j S A => pure (.divFuel i (J j) (R S) (V A))
  | .reify i j S B R' c => return .reify i (J j) (R S) (V B) (V R') (← f c)
  | .sliceBorrowM i j A B x => pure (.sliceBorrowM i (J j) (V A) (V B) x)
  | .sliceBorrowI i j A B x => pure (.sliceBorrowI i (J j) (V A) (V B) x)
  | .sliceGetM i j l A => pure (.sliceGetM i (J j) l (V A))
  | .sliceLenM i j l A => pure (.sliceLenM i (J j) l (V A))
  | .sliceSplitI i j l A => pure (.sliceSplitI i (J j) l (V A))
  | .sliceSplitM i j l A => pure (.sliceSplitM i (J j) l (V A))
  | .sliceEmptyI i j l A => pure (.sliceEmptyI i (J j) l (V A))
  | .sliceEmptyM i j l A => pure (.sliceEmptyM i (J j) l (V A))
  | .sliceReplaceM i j l A => pure (.sliceReplaceM i (J j) l (V A))
  | .sliceSwapM i j l A => pure (.sliceSwapM i (J j) l (V A))
  | .withbor1 i j A B x => pure (.withbor1 i (J j) (V A) (V B) x)
  | .withbor2 i j A B x => pure (.withbor2 i (J j) (V A) (V B) x)
  | .withbor3 i j l A B x => pure (.withbor3 i (J j) l (V A) (V B) x)
  | .withload i j l A B x => pure (.withload i (J j) l (V A) (V B) x)
  | .withswap i j l A B => pure (.withswap i (J j) l (V A) (V B))
  | .withbor1U i j A B S x td => return .withbor1U i (J j) (V A) (V B) (R S) x (← f td)
  | .withbor2U i j A B S x td => return .withbor2U i (J j) (V A) (V B) (R S) x (← f td)
  | .withbor3U i j l A B S x td => return .withbor3U i (J j) l (V A) (V B) (R S) x (← f td)
  | .withloadU i j l A B S x => pure (.withloadU i (J j) l (V A) (V B) (R S) x)
  | .sliceBorrowMU i j A B S x td => return .sliceBorrowMU i (J j) (V A) (V B) (R S) x (← f td)
  | .sliceBorrowIU i j A B S x td => return .sliceBorrowIU i (J j) (V A) (V B) (R S) x (← f td)
  | .lolliE i j A B u ta tf => return .lolliE i (J j) (V A) (V B) u (← f ta) (← f tf)
  | .allEV i j x b l A c => return .allEV i (J j) x b l (V A) (← f c)
  | .ofRet i j A c => return .ofRet i (J j) (V A) (← f c)
  | .roll i j A c => return .roll i (J j) (V A) (← f c)
  | .unroll i j A c => return .unroll i (J j) (V A) (← f c)
  | .foldImm i j F y c R' => pure (.foldImm i (J j) (m.fshape F) y c (V R'))
  | .foldOwn i j F R' => pure (.foldOwn i (J j) (m.fshape F) (V R'))
  | .foldReuse i j F R' => pure (.foldReuse i (J j) (m.fshape F) (V R'))
  | .nuIn i j D c => return .nuIn i (J j) (C D) (← f c)
  | .nuOut i j D c => return .nuOut i (J j) (C D) (← f c)
  | .unfoldN i j D S => pure (.unfoldN i (J j) (C D) (V S))
  | .effSub i j S S' A c => return .effSub i (J j) (R S) (R S') (V A) (← f c)
  | .effPerform i j S o c => return .effPerform i (J j) (R S) (m.op o) (← f c)
  | .effRaise i j S o B c => return .effRaise i (J j) (R S) (m.op o) (V B) (← f c)
  | .effLet i j A B S u tM tN => return .effLet i (J j) (V A) (V B) (R S) u (← f tM) (← f tN)
  | .effThen i j A B S SM SD u tM tN tD =>
    return .effThen i (J j) (V A) (V B) (R S) (R SM) (R SD) u (← f tM) (← f tN) (← f tD)
  | .effHandleV i j S E fs nm A R' u ks site ins tc te =>
    return .effHandleV i (J j) (R S) (m.E E) (fun k => C (fs k)) nm (V A) (V R') u ks site ins
      (← f tc) (← f te)
  | .effHandleVB i j S E fs nm A R' d u ks site ins tc te =>
    return .effHandleVB i (J j) (R S) (m.E E) (fun k => C (fs k)) nm (V A) (V R') d u ks site ins
      (← f tc) (← f te)
  | .effHandleT i j S SN E fs nm A R' u site ins tc te =>
    return .effHandleT i (J j) (R S) (R SN) (m.E E) (fun k => C (fs k)) nm (V A) (V R') u site ins
      (← f tc) (← f te)
  | .effHandleL i j S SW E fs Xs nm A R' u site ins tc te =>
    return .effHandleL i (J j) (R S) (R SW) (m.E E) (fun k => C (fs k)) (fun k => V (Xs k)) nm (V A)
      (V R') u site ins (← f tc) (← f te)
  | .letPoly i j D j' tV tN => return .letPoly i (J j) (C D) (J j') (← f tV) (← f tN)
  | .lendR i j x b T B S td tM => return .lendR i (J j) x b (V T) (V B) (R S) (← f td) (← f tM)
  | .lendLoopR i j x A S B R' tN tK ts0 =>
    return .lendLoopR i (J j) x (V A) (V S) (V B) (V R') (← f tN) (← f tK) (← f ts0)
  | .nilDead i j j' c => return .nilDead i (J j) (J j') (← f c)
  | .dtor i j A => pure (.dtor i (J j) (V A))
  | .allocS i j σ => pure (.allocS i (J j) (m.shape σ))
  | .freeS i j σ => pure (.freeS i (J j) (m.shape σ))
  | .withborSM i j σ c T => pure (.withborSM i (J j) (m.shape σ) c (V T))
  | .withborSI i j σ c T => pure (.withborSI i (J j) (m.shape σ) c (V T))
  | .withborF2M i j c x y A B T => pure (.withborF2M i (J j) c x y (V A) (V B) (V T))
  | .withborF2I i j c x y A B T => pure (.withborF2I i (J j) c x y (V A) (V B) (V T))
  | .litFn i j bs c => return .litFn i (J j) bs (← f c)
  | .divLit i j op k c => return .divLit i (J j) op k (← f c)
  | .walk i j w r c => return .walk i (J j) w r (← f c)
  | .walkGet i j w c => return .walkGet i (J j) w (← f c)
  | .selfCall i j k n c => return .selfCall i (J j) k n (← f c)
  | .lendCell i j w c => return .lendCell i (J j) w (← f c)
  | .nuEta i j g s c => return .nuEta i (J j) g s (← f c)
  | .use i j nm decl targs ab c => return .use i (J j) nm decl (targs.map V) ab (← f c)

end Rewrite
