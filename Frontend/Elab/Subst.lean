import Frontend.Syntax

/-!
# Frontend — Elab — substituting type parameters  `[#109]`

`subst σ` replaces each type name `X` bound by `σ` with its type, in every type, bracket argument
and annotation of a term. It instantiates a template (`fn f[A, …]`, SPEC §15) at the types of
one call: the copy is an ordinary `fn` at those types. A `mu X. …` binds `X` in its
body, so a name it binds is not substituted there. The functions follow `respan`
(`Frontend/Elab/Respan.lean`).
-/

namespace Frontend

/-- A substitution of types for type names. -/
abbrev TySubst := List (String × VTy)

mutual
def VTy.subst (σ : TySubst) : VTy → VTy
  | .unit sp => .unit sp
  | .zero sp => .zero sp
  | .tensor sp A B => .tensor sp (A.subst σ) (B.subst σ)
  | .sum sp A B => .sum sp (A.subst σ) (B.subst σ)
  | .thunk sp C => .thunk sp (C.subst σ)
  | .ref sp A => .ref sp (A.subst σ)
  | .imm sp a A => .imm sp a (A.subst σ)
  | .mut sp a A => .mut sp a (A.subst σ)
  | .box sp a A => .box sp a (A.subst σ)
  | .bang sp A => .bang sp (A.subst σ)
  | .unk sp => .unk sp
  | .int sp w => .int sp w
  | .handle sp o => .handle sp o
  | .mu sp X A => .mu sp X (A.subst (σ.filter (·.1 != X.name)))
  | .name sp n => (σ.lookup n).getD (.name sp n)
  | .lolli sp A B => .lolli sp (A.subst σ) (B.subst σ)
  | .all sp x b A => .all sp x b (A.subst σ)
  | .block sp s => .block sp (s.subst σ)
  | .val sp s => .val sp (s.subst σ)
  | .fam sp m a s => .fam sp m a (s.subst σ)
  | .view sp a A => .view sp a (A.subst σ)
  | .array sp A => .array sp (A.subst σ)
  | .arrayImm sp a A => .arrayImm sp a (A.subst σ)
  | .arrayMut sp a A => .arrayMut sp a (A.subst σ)
  | .sized sp D S A => .sized sp (D.subst σ) (S.subst σ) (A.subst σ)
  | .app sp G A => .app sp (G.subst σ) (A.subst σ)
  | .lapp sp G a => .lapp sp (G.subst σ) a
  | .rowed sp G r => .rowed sp (G.subst σ) (r.subst σ)

def CTy.subst (σ : TySubst) : CTy → CTy
  | .ret sp A => .ret sp (A.subst σ)
  | .arr sp A C => .arr sp (A.subst σ) (C.subst σ)
  | .amp sp C D => .amp sp (C.subst σ) (D.subst σ)
  | .top sp => .top sp
  | .all sp x b C => .all sp x b (C.subst σ)
  | .nu sp X C => .nu sp X (C.subst σ)
  | .name sp n => .name sp n
  | .delay sp A => .delay sp (A.subst σ)
  | .stream sp A => .stream sp (A.subst σ)
  | .iter sp A R R' => .iter sp (A.subst σ) (R.subst σ) (R'.subst σ)
  | .loop sp A B => .loop sp (A.subst σ) (B.subst σ)
  | .pull sp A B R => .pull sp (A.subst σ) (B.subst σ) (R.subst σ)
  | .eff sp r A => .eff sp (r.subst σ) (A.subst σ)

def Row.subst (σ : TySubst) : Row → Row
  | .nil => .nil
  | .cons n i q A B r => .cons n i q (A.subst σ) (B.subst σ) (r.subst σ)

def Shape.subst (σ : TySubst) : Shape → Shape
  | .leaf sp A => .leaf sp (A.subst σ)
  | .node sp s t => .node sp (s.subst σ) (t.subst σ)
  | .name sp n => .name sp n
end

def Const.subst (σ : TySubst) : Const → Const
  | .alloc A => .alloc (A.subst σ)
  | .free A => .free (A.subst σ)
  | .swap A B => .swap (A.subst σ) (B.subst σ)
  | .copy a A => .copy a (A.subst σ)
  | .copyBang A => .copyBang (A.subst σ)
  | .forgetImm a A => .forgetImm a (A.subst σ)
  | .forgetMut a A => .forgetMut a (A.subst σ)
  | .forgetUnk => .forgetUnk
  | .forgetBang A => .forgetBang (A.subst σ)
  | .withbor1 x A B => .withbor1 x (A.subst σ) (B.subst σ)
  | .withbor2 x b A B => .withbor2 x b (A.subst σ) (B.subst σ)
  | .withbor3 a x A B => .withbor3 a x (A.subst σ) (B.subst σ)
  | .withload a x A B => .withload a x (A.subst σ) (B.subst σ)
  | .withswap a A B => .withswap a (A.subst σ) (B.subst σ)
  | .foldImm F y c R => .foldImm (F.subst σ) y c (R.subst σ)
  | .foldOwn F R => .foldOwn (F.subst σ) (R.subst σ)
  | .foldReuse F R => .foldReuse (F.subst σ) (R.subst σ)
  | .fixd A S => .fixd (A.subst σ) (S.subst σ)
  | .unfoldS A S => .unfoldS (A.subst σ) (S.subst σ)
  | .unfold C S => .unfold (C.subst σ) (S.subst σ)
  | .lit c => .lit c
  | .host op => .host op
  | .allocS s => .allocS (s.subst σ)
  | .freeS s => .freeS (s.subst σ)
  | .withborS m s c T => .withborS m (s.subst σ) c (T.subst σ)
  | .withborF2Mut c a b w A B T => .withborF2Mut c a b w (A.subst σ) (B.subst σ) (T.subst σ)
  | .withborF2Imm c a b A B T => .withborF2Imm c a b (A.subst σ) (B.subst σ) (T.subst σ)
  | .arrayNew A => .arrayNew (A.subst σ)
  | .arrayEmpty A => .arrayEmpty (A.subst σ)
  | .arrayFree A => .arrayFree (A.subst σ)
  | .arraySize A => .arraySize (A.subst σ)
  | .arrayReplace A => .arrayReplace (A.subst σ)
  | .arrayLen a A => .arrayLen a (A.subst σ)
  | .arrayGet a A => .arrayGet a (A.subst σ)
  | .arrayCopy a A => .arrayCopy a (A.subst σ)
  | .arrayForget a A => .arrayForget a (A.subst σ)
  | .sliceBorrowMut x b A B => .sliceBorrowMut x b (A.subst σ) (B.subst σ)
  | .sliceBorrowImm x b A B => .sliceBorrowImm x b (A.subst σ) (B.subst σ)
  | .sliceGetMut a A => .sliceGetMut a (A.subst σ)
  | .sliceLenMut a A => .sliceLenMut a (A.subst σ)
  | .sliceSplitImm a A => .sliceSplitImm a (A.subst σ)
  | .sliceSplitMut a A => .sliceSplitMut a (A.subst σ)
  | .sliceEmptyImm a A => .sliceEmptyImm a (A.subst σ)
  | .sliceEmptyMut a A => .sliceEmptyMut a (A.subst σ)
  | .sliceReplaceMut a A => .sliceReplaceMut a (A.subst σ)
  | .sliceSwapMut a A => .sliceSwapMut a (A.subst σ)
  | .countFold S => .countFold (S.subst σ)
  | .countTry S E => .countTry (S.subst σ) (E.subst σ)
  | .boundedFix A C => .boundedFix (A.subst σ) (C.subst σ)
  | .withbor1U x A B r => .withbor1U x (A.subst σ) (B.subst σ) (r.subst σ)
  | .withbor2U x b A B r => .withbor2U x b (A.subst σ) (B.subst σ) (r.subst σ)
  | .withbor3U a x A B r => .withbor3U a x (A.subst σ) (B.subst σ) (r.subst σ)
  | .withloadU a x A B r => .withloadU a x (A.subst σ) (B.subst σ) (r.subst σ)
  | .sliceBorrowMutU x b A B r => .sliceBorrowMutU x b (A.subst σ) (B.subst σ) (r.subst σ)
  | .sliceBorrowImmU x b A B r => .sliceBorrowImmU x b (A.subst σ) (B.subst σ) (r.subst σ)
  | .iterate St B R r => .iterate (St.subst σ) (B.subst σ) (R.subst σ) (r.subst σ)

/-- A control handler's site (SPEC §19) at a template's instance: its types, at the template's
type arguments. The handler's own type parameters the site leaves open (`tps`) are named apart
from the template's (`Frontend.Elab.Effects.withCtl`), and are not substituted. -/
def HInfo.subst (σ : TySubst) (i : HInfo) : HInfo :=
  let σ := σ.filter fun (x, _) => !i.tps.contains x
  { i with ents := i.ents.map fun (q, A, B) => (q, A.subst σ, B.subst σ),
           known := i.known.map fun (x, A) => (x, A.subst σ),
           params := i.params.map fun (x, A) => (x, A.subst σ),
           retA := i.retA.subst σ, res := i.res.subst σ, after := i.after.map (·.subst σ),
           site := i.site.mapTy (·.subst σ) }

mutual
def Val.subst (σ : TySubst) : Val → Val
  | .var sp x => .var sp x
  | .clone sp x => .clone sp x
  | .defApp sp n args => .defApp sp n (args.map (VTy.subst σ))
  | .unit sp => .unit sp
  | .pair sp V W => .pair sp (V.subst σ) (W.subst σ)
  | .inl sp V => .inl sp (V.subst σ)
  | .inr sp V => .inr sp (V.subst σ)
  | .thunk sp M => .thunk sp (M.subst σ)
  | .thunkv sp M => .thunkv sp (M.subst σ)
  | .bangThunk sp M => .bangThunk sp (M.subst σ)
  | .bangThunkv sp M => .bangThunkv sp (M.subst σ)
  | .unbang sp V => .unbang sp (V.subst σ)
  | .boxed sp a V => .boxed sp a (V.subst σ)
  | .unbox sp V => .unbox sp (V.subst σ)
  | .sub sp V a => .sub sp (V.subst σ) a
  | .roll sp V => .roll sp (V.subst σ)
  | .unroll sp V => .unroll sp (V.subst σ)
  | .run sp M => .run sp (M.subst σ)
  | .app sp V W => .app sp (V.subst σ) (W.subst σ)
  | .inst sp V a => .inst sp (V.subst σ) a
  | .ascribe sp V A => .ascribe sp (V.subst σ) (A.subst σ)
  | .const sp c => .const sp (c.subst σ)
  | .shorten sp m s a V => .shorten sp m (s.subst σ) a (V.subst σ)
  | .lend sp x m => .lend sp x m
  | .sugar sp (.forSite i) => .sugar sp (.forSite { i with T := i.T.subst σ })
  | .sugar sp (.pullSite i) => .sugar sp (.pullSite { i with T := i.T.subst σ })
  | .sugar sp (.hndCtl i) => .sugar sp (.hndCtl (i.subst σ))
  | .sugar sp s => .sugar sp s
  | .mark sp k V => .mark sp k (V.subst σ)
  | .reify sp B R r V => .reify sp (B.subst σ) (R.subst σ) (r.subst σ) (V.subst σ)

def Comp.subst (σ : TySubst) : Comp → Comp
  | .ret sp V => .ret sp (V.subst σ)
  | .bind sp x A M N lin => .bind sp x (A.map (VTy.subst σ)) (M.subst σ) (N.subst σ) lin
  | .force sp x => .force sp x
  | .lam sp x A M => .lam sp x (A.subst σ) (M.subst σ)
  | .app sp M x => .app sp (M.subst σ) x
  | .with_ sp M N => .with_ sp (M.subst σ) (N.subst σ)
  | .proj sp i M => .proj sp i (M.subst σ)
  | .top sp => .top sp
  | .letUnit sp V M => .letUnit sp (V.subst σ) (M.subst σ)
  | .letPair sp x y V M => .letPair sp x y (V.subst σ) (M.subst σ)
  | .case sp V x M y N => .case sp (V.subst σ) x (M.subst σ) y (N.subst σ)
  | .absurd sp V => .absurd sp (V.subst σ)
  | .lamL sp x b M => .lamL sp x b (M.subst σ)
  | .inst sp M a => .inst sp (M.subst σ) a
  | .nuIn sp M => .nuIn sp (M.subst σ)
  | .nuOut sp M => .nuOut sp (M.subst σ)
  | .ascribe sp M C => .ascribe sp (M.subst σ) (C.subst σ)
  | .loop sp ℓ src V M N => .loop sp ℓ src (V.subst σ) (M.subst σ) (N.subst σ)
  | .perform sp n i V => .perform sp n i (V.subst σ)
  | .abort sp n i V => .abort sp n i (V.subst σ)
  | .handle sp n st hr hc M =>
    .handle sp n (st.map (SiteRec.mapTy (VTy.subst σ)))
      (hr.subst σ) (hc.subst σ) (M.subst σ)
  | .unwind sp x A M D N => .unwind sp x (A.map (VTy.subst σ)) (M.subst σ) (D.subst σ) (N.subst σ)
  | .withbor2r sp x b A B r p m M =>
      .withbor2r sp x b (A.subst σ) (B.subst σ) (r.subst σ) p m (M.subst σ)
end

end Frontend
