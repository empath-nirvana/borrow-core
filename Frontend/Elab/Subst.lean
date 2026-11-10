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

/-- A type written as a whole replaced, before the names in it: a copy at a stored generator's
row has its parameter's type replaced wherever the body writes it (SPEC §15).  `[spec §15]` -/
abbrev TyHook := VTy → Option VTy

mutual
def VTy.subst (σ : TySubst) (h : TyHook := fun _ => none) (T : VTy) : VTy :=
  match h T with
  | some T' => T'
  | none => match T with
  | .unit sp => .unit sp
  | .zero sp => .zero sp
  | .tensor sp A B => .tensor sp (A.subst σ h) (B.subst σ h)
  | .sum sp A B => .sum sp (A.subst σ h) (B.subst σ h)
  | .thunk sp C => .thunk sp (C.subst σ h)
  | .ref sp A => .ref sp (A.subst σ h)
  | .imm sp a A => .imm sp a (A.subst σ h)
  | .mut sp a A => .mut sp a (A.subst σ h)
  | .box sp a A => .box sp a (A.subst σ h)
  | .bang sp A => .bang sp (A.subst σ h)
  | .unk sp => .unk sp
  | .int sp w => .int sp w
  | .handle sp o => .handle sp o
  | .mu sp X A => .mu sp X (A.subst (σ.filter (·.1 != X.name)) h)
  | .name sp n => (σ.lookup n).getD (.name sp n)
  | .lolli sp A B => .lolli sp (A.subst σ h) (B.subst σ h)
  | .all sp x b A => .all sp x b (A.subst σ h)
  | .block sp s => .block sp (s.subst σ h)
  | .val sp s => .val sp (s.subst σ h)
  | .fam sp m a s => .fam sp m a (s.subst σ h)
  | .view sp a A => .view sp a (A.subst σ h)
  | .array sp A => .array sp (A.subst σ h)
  | .arrayImm sp a A => .arrayImm sp a (A.subst σ h)
  | .arrayMut sp a A => .arrayMut sp a (A.subst σ h)
  | .sized sp D S A => .sized sp (D.subst σ h) (S.subst σ h) (A.subst σ h)
  | .app sp G A => .app sp (G.subst σ h) (A.subst σ h)
  | .lapp sp G a => .lapp sp (G.subst σ h) a
  | .rowed sp G r => .rowed sp (G.subst σ h) (r.subst σ h)

def CTy.subst (σ : TySubst) (h : TyHook := fun _ => none) : CTy → CTy
  | .ret sp A => .ret sp (A.subst σ h)
  | .arr sp A C => .arr sp (A.subst σ h) (C.subst σ h)
  | .amp sp C D => .amp sp (C.subst σ h) (D.subst σ h)
  | .top sp => .top sp
  | .all sp x b C => .all sp x b (C.subst σ h)
  | .nu sp X C => .nu sp X (C.subst σ h)
  | .name sp n => .name sp n
  | .delay sp A => .delay sp (A.subst σ h)
  | .stream sp A => .stream sp (A.subst σ h)
  | .iter sp A R R' => .iter sp (A.subst σ h) (R.subst σ h) (R'.subst σ h)
  | .loop sp A B => .loop sp (A.subst σ h) (B.subst σ h)
  | .pull sp A B R => .pull sp (A.subst σ h) (B.subst σ h) (R.subst σ h)
  | .eff sp r A => .eff sp (r.subst σ h) (A.subst σ h)

def Row.subst (σ : TySubst) (h : TyHook := fun _ => none) : Row → Row
  | .nil => .nil
  | .cons n i q A B f r => .cons n i q (A.subst σ h) (B.subst σ h) (f.subst σ h) (r.subst σ h)

def Shape.subst (σ : TySubst) (h : TyHook := fun _ => none) : Shape → Shape
  | .leaf sp A => .leaf sp (A.subst σ h)
  | .node sp s t => .node sp (s.subst σ h) (t.subst σ h)
  | .name sp n => .name sp n
end

def Const.subst (σ : TySubst) (h : TyHook := fun _ => none) : Const → Const
  | .alloc A => .alloc (A.subst σ h)
  | .free A => .free (A.subst σ h)
  | .swap A B => .swap (A.subst σ h) (B.subst σ h)
  | .copy a A => .copy a (A.subst σ h)
  | .copyBang A => .copyBang (A.subst σ h)
  | .releaseImm a A => .releaseImm a (A.subst σ h)
  | .releaseMut a A => .releaseMut a (A.subst σ h)
  | .releaseUnk => .releaseUnk
  | .tokMint => .tokMint
  | .tokBurn => .tokBurn
  | .releaseBang A => .releaseBang (A.subst σ h)
  | .withbor1 x A B => .withbor1 x (A.subst σ h) (B.subst σ h)
  | .withbor2 x b A B => .withbor2 x b (A.subst σ h) (B.subst σ h)
  | .withbor3 a x A B => .withbor3 a x (A.subst σ h) (B.subst σ h)
  | .withload a x A B => .withload a x (A.subst σ h) (B.subst σ h)
  | .withswap a A B => .withswap a (A.subst σ h) (B.subst σ h)
  | .foldImm F y c R => .foldImm (F.subst σ h) y c (R.subst σ h)
  | .foldOwn F R => .foldOwn (F.subst σ h) (R.subst σ h)
  | .foldReuse F R => .foldReuse (F.subst σ h) (R.subst σ h)
  | .fixd A S => .fixd (A.subst σ h) (S.subst σ h)
  | .unfoldS A S => .unfoldS (A.subst σ h) (S.subst σ h)
  | .unfold C S => .unfold (C.subst σ h) (S.subst σ h)
  | .lit c => .lit c
  | .host op => .host op
  | .allocS s => .allocS (s.subst σ h)
  | .freeS s => .freeS (s.subst σ h)
  | .withborS m s c T => .withborS m (s.subst σ h) c (T.subst σ h)
  | .withborF2Mut c a b w A B T => .withborF2Mut c a b w (A.subst σ h) (B.subst σ h) (T.subst σ h)
  | .withborF2Imm c a b A B T => .withborF2Imm c a b (A.subst σ h) (B.subst σ h) (T.subst σ h)
  | .arrayNew A => .arrayNew (A.subst σ h)
  | .arrayEmpty A => .arrayEmpty (A.subst σ h)
  | .arrayFree A => .arrayFree (A.subst σ h)
  | .arraySize A => .arraySize (A.subst σ h)
  | .arrayReplace A => .arrayReplace (A.subst σ h)
  | .arrayLen a A => .arrayLen a (A.subst σ h)
  | .arrayGet a A => .arrayGet a (A.subst σ h)
  | .arrayCopy a A => .arrayCopy a (A.subst σ h)
  | .arrayRelease a A => .arrayRelease a (A.subst σ h)
  | .sliceBorrowMut x b A B => .sliceBorrowMut x b (A.subst σ h) (B.subst σ h)
  | .sliceBorrowImm x b A B => .sliceBorrowImm x b (A.subst σ h) (B.subst σ h)
  | .sliceGetMut a A => .sliceGetMut a (A.subst σ h)
  | .sliceLenMut a A => .sliceLenMut a (A.subst σ h)
  | .sliceSplitImm a A => .sliceSplitImm a (A.subst σ h)
  | .sliceSplitMut a A => .sliceSplitMut a (A.subst σ h)
  | .sliceEmptyImm a A => .sliceEmptyImm a (A.subst σ h)
  | .sliceEmptyMut a A => .sliceEmptyMut a (A.subst σ h)
  | .sliceReplaceMut a A => .sliceReplaceMut a (A.subst σ h)
  | .sliceSwapMut a A => .sliceSwapMut a (A.subst σ h)
  | .countFold S => .countFold (S.subst σ h)
  | .countTry S E => .countTry (S.subst σ h) (E.subst σ h)
  | .boundedFix A C => .boundedFix (A.subst σ h) (C.subst σ h)
  | .withbor1U x A B r => .withbor1U x (A.subst σ h) (B.subst σ h) (r.subst σ h)
  | .withbor2U x b A B r => .withbor2U x b (A.subst σ h) (B.subst σ h) (r.subst σ h)
  | .withbor3U a x A B r => .withbor3U a x (A.subst σ h) (B.subst σ h) (r.subst σ h)
  | .withloadU a x A B r => .withloadU a x (A.subst σ h) (B.subst σ h) (r.subst σ h)
  | .sliceBorrowMutU x b A B r => .sliceBorrowMutU x b (A.subst σ h) (B.subst σ h) (r.subst σ h)
  | .sliceBorrowImmU x b A B r => .sliceBorrowImmU x b (A.subst σ h) (B.subst σ h) (r.subst σ h)

/-- A control handler's site (SPEC §19) at a template's instance: its types, at the template's
type arguments. The handler's own type parameters the site leaves open (`tps`) are named apart
from the template's (`Frontend.Elab.Effects.withCtl`), and are not substituted. -/
def HInfo.subst (σ : TySubst) (i : HInfo) (h : TyHook := fun _ => none) : HInfo :=
  let σ := σ.filter fun (x, _) => !i.tps.contains x
  { i with ents := i.ents.map fun (q, A, B) => (q, A.subst σ h, B.subst σ h),
           known := i.known.map fun (x, A) => (x, A.subst σ h),
           params := i.params.map fun (x, A) => (x, A.subst σ h),
           retA := i.retA.subst σ h, res := i.res.subst σ h, after := i.after.map (·.subst σ h),
           site := i.site.mapTy (·.subst σ h), fins := i.fins.map (·.subst σ h) }

mutual
def Val.subst (σ : TySubst) (h : TyHook := fun _ => none) : Val → Val
  | .var sp x => .var sp x
  | .clone sp x => .clone sp x
  | .defApp sp n args => .defApp sp n (args.map (VTy.subst σ h))
  | .unit sp => .unit sp
  | .pair sp V W => .pair sp (V.subst σ h) (W.subst σ h)
  | .inl sp V => .inl sp (V.subst σ h)
  | .inr sp V => .inr sp (V.subst σ h)
  | .thunk sp M => .thunk sp (M.subst σ h)
  | .thunkv sp M => .thunkv sp (M.subst σ h)
  | .bangThunk sp M => .bangThunk sp (M.subst σ h)
  | .bangThunkv sp M => .bangThunkv sp (M.subst σ h)
  | .unbang sp V => .unbang sp (V.subst σ h)
  | .boxed sp a V => .boxed sp a (V.subst σ h)
  | .unbox sp V => .unbox sp (V.subst σ h)
  | .sub sp V a => .sub sp (V.subst σ h) a
  | .roll sp V => .roll sp (V.subst σ h)
  | .unroll sp V => .unroll sp (V.subst σ h)
  | .run sp M => .run sp (M.subst σ h)
  | .app sp V W => .app sp (V.subst σ h) (W.subst σ h)
  | .inst sp V a => .inst sp (V.subst σ h) a
  | .ascribe sp V A => .ascribe sp (V.subst σ h) (A.subst σ h)
  | .const sp c => .const sp (c.subst σ h)
  | .shorten sp m s a V => .shorten sp m (s.subst σ h) a (V.subst σ h)
  | .lend sp x m => .lend sp x m
  | .sugar sp (.forSite i) => .sugar sp (.forSite { i with T := i.T.subst σ h })
  | .sugar sp (.pullSite i) => .sugar sp (.pullSite { i with T := i.T.subst σ h })
  | .sugar sp (.hndCtl i) => .sugar sp (.hndCtl (i.subst σ h))
  | .sugar sp s => .sugar sp s
  | .mark sp k V => .mark sp k (V.subst σ h)

def Comp.subst (σ : TySubst) (h : TyHook := fun _ => none) : Comp → Comp
  | .ret sp V => .ret sp (V.subst σ h)
  | .bind sp x A M N => .bind sp x (A.map (VTy.subst σ h)) (M.subst σ h) (N.subst σ h)
  | .force sp x => .force sp x
  | .lam sp x A M => .lam sp x (A.subst σ h) (M.subst σ h)
  | .app sp M x => .app sp (M.subst σ h) x
  | .with_ sp M N => .with_ sp (M.subst σ h) (N.subst σ h)
  | .proj sp i M => .proj sp i (M.subst σ h)
  | .top sp => .top sp
  | .letUnit sp V M => .letUnit sp (V.subst σ h) (M.subst σ h)
  | .letPair sp x y V M => .letPair sp x y (V.subst σ h) (M.subst σ h)
  | .case sp V x M y N => .case sp (V.subst σ h) x (M.subst σ h) y (N.subst σ h)
  | .absurd sp V => .absurd sp (V.subst σ h)
  | .lamL sp x b M => .lamL sp x b (M.subst σ h)
  | .inst sp M a => .inst sp (M.subst σ h) a
  | .nuIn sp M => .nuIn sp (M.subst σ h)
  | .nuOut sp M => .nuOut sp (M.subst σ h)
  | .ascribe sp M C => .ascribe sp (M.subst σ h) (C.subst σ h)
  | .loop sp ℓ src V M N => .loop sp ℓ src (V.subst σ h) (M.subst σ h) (N.subst σ h)
  | .perform sp n i V => .perform sp n i (V.subst σ h)
  | .abort sp n i V => .abort sp n i (V.subst σ h)
  | .handle sp n st hr hc M =>
    .handle sp n (st.map (SiteRec.mapTy (VTy.subst σ h)))
      (hr.subst σ h) (hc.subst σ h) (M.subst σ h)
  | .unwind sp x A M D N => .unwind sp x (A.map (VTy.subst σ h)) (M.subst σ h) (D.subst σ h) (N.subst σ h)
  | .withbor2r sp x b A B r p m M =>
      .withbor2r sp x b (A.subst σ h) (B.subst σ h) (r.subst σ h) p m (M.subst σ h)
end

end Frontend
