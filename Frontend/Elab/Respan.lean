import Frontend.Syntax

/-!
# Frontend — Elab — respanning generated syntax  `[#54]`

`respan sp` gives every node of a term, and every name, type and lifetime in it, the span `sp`.
The elaborator applies it to the core it generates for a sugar at `sp`, before filling the
template's holes with the program's own syntax, so that an error the checker finds in generated
code points at the sugar that produced it, not at an offset inside a template string. The
functions follow `strip` (`Frontend/Syntax.lean`), with `sp` for `Span.none`.
-/

namespace Frontend

def Ident.respan (sp : Span) (x : Ident) : Ident := { x with span := sp }

def Life.respan (sp : Span) : Life → Life
  | .var _ x => .var sp x
  | .top _ => .top sp
  | .dom _ => .dom sp
  | .meet _ a b => .meet sp (a.respan sp) (b.respan sp)
  | .join _ a b => .join sp (a.respan sp) (b.respan sp)

mutual
def VTy.respan (sp : Span) : VTy → VTy
  | .unit _ => .unit sp
  | .zero _ => .zero sp
  | .tensor _ A B => .tensor sp (A.respan sp) (B.respan sp)
  | .sum _ A B => .sum sp (A.respan sp) (B.respan sp)
  | .thunk _ C => .thunk sp (C.respan sp)
  | .ref _ A => .ref sp (A.respan sp)
  | .imm _ a A => .imm sp (a.respan sp) (A.respan sp)
  | .mut _ a A => .mut sp (a.respan sp) (A.respan sp)
  | .box _ a A => .box sp (a.respan sp) (A.respan sp)
  | .bang _ A => .bang sp (A.respan sp)
  | .unk _ => .unk sp
  | .int _ w => .int sp w
  | .handle _ o => .handle sp o
  | .mu _ X A => .mu sp (X.respan sp) (A.respan sp)
  | .name _ n => .name sp n
  | .lolli _ A B => .lolli sp (A.respan sp) (B.respan sp)
  | .all _ x b A => .all sp (x.respan sp) (b.respan sp) (A.respan sp)
  | .block _ σ => .block sp (σ.respan sp)
  | .val _ σ => .val sp (σ.respan sp)
  | .fam _ m a σ => .fam sp m (a.respan sp) (σ.respan sp)
  | .view _ a A => .view sp (a.respan sp) (A.respan sp)
  | .array _ A => .array sp (A.respan sp)
  | .arrayImm _ a A => .arrayImm sp (a.respan sp) (A.respan sp)
  | .arrayMut _ a A => .arrayMut sp (a.respan sp) (A.respan sp)
  | .sized _ D S A => .sized sp (D.respan sp) (S.respan sp) (A.respan sp)
  | .app _ G A => .app sp (G.respan sp) (A.respan sp)
  | .lapp _ G a => .lapp sp (G.respan sp) (a.respan sp)
  | .rowed _ G r => .rowed sp (G.respan sp) (r.respan sp)

def CTy.respan (sp : Span) : CTy → CTy
  | .ret _ A => .ret sp (A.respan sp)
  | .arr _ A C => .arr sp (A.respan sp) (C.respan sp)
  | .amp _ C D => .amp sp (C.respan sp) (D.respan sp)
  | .top _ => .top sp
  | .all _ x b C => .all sp (x.respan sp) (b.respan sp) (C.respan sp)
  | .nu _ X C => .nu sp (X.respan sp) (C.respan sp)
  | .name _ n => .name sp n
  | .delay _ A => .delay sp (A.respan sp)
  | .stream _ A => .stream sp (A.respan sp)
  | .iter _ A R R' => .iter sp (A.respan sp) (R.respan sp) (R'.respan sp)
  | .loop _ A B => .loop sp (A.respan sp) (B.respan sp)
  | .pull _ A B R => .pull sp (A.respan sp) (B.respan sp) (R.respan sp)
  | .eff _ r A => .eff sp (r.respan sp) (A.respan sp)

def Row.respan (sp : Span) : Row → Row
  | .nil => .nil
  | .cons n i q A B r => .cons n i q (A.respan sp) (B.respan sp) (r.respan sp)

def Shape.respan (sp : Span) : Shape → Shape
  | .leaf _ A => .leaf sp (A.respan sp)
  | .node _ σ τ => .node sp (σ.respan sp) (τ.respan sp)
  | .name _ n => .name sp n
end

def Const.respan (sp : Span) : Const → Const
  | .alloc A => .alloc (A.respan sp)
  | .free A => .free (A.respan sp)
  | .swap A B => .swap (A.respan sp) (B.respan sp)
  | .copy a A => .copy (a.respan sp) (A.respan sp)
  | .copyBang A => .copyBang (A.respan sp)
  | .forgetImm a A => .forgetImm (a.respan sp) (A.respan sp)
  | .forgetMut a A => .forgetMut (a.respan sp) (A.respan sp)
  | .forgetUnk => .forgetUnk
  | .forgetBang A => .forgetBang (A.respan sp)
  | .withbor1 x A B => .withbor1 (x.respan sp) (A.respan sp) (B.respan sp)
  | .withbor2 x b A B => .withbor2 (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp)
  | .withbor3 a x A B => .withbor3 (a.respan sp) (x.respan sp) (A.respan sp) (B.respan sp)
  | .withload a x A B => .withload (a.respan sp) (x.respan sp) (A.respan sp) (B.respan sp)
  | .withswap a A B => .withswap (a.respan sp) (A.respan sp) (B.respan sp)
  | .foldImm F y c R => .foldImm (F.respan sp) (y.respan sp) (c.respan sp) (R.respan sp)
  | .foldOwn F R => .foldOwn (F.respan sp) (R.respan sp)
  | .foldReuse F R => .foldReuse (F.respan sp) (R.respan sp)
  | .fixd A S => .fixd (A.respan sp) (S.respan sp)
  | .unfoldS A S => .unfoldS (A.respan sp) (S.respan sp)
  | .unfold C S => .unfold (C.respan sp) (S.respan sp)
  | .lit c => .lit c
  | .host op => .host op
  | .allocS σ => .allocS (σ.respan sp)
  | .freeS σ => .freeS (σ.respan sp)
  | .withborS m σ c T => .withborS m (σ.respan sp) (c.respan sp) (T.respan sp)
  | .withborF2Mut c a b w A B T =>
      .withborF2Mut (c.respan sp) (a.respan sp) (b.respan sp) (w.respan sp) (A.respan sp) (B.respan sp) (T.respan sp)
  | .withborF2Imm c a b A B T => .withborF2Imm (c.respan sp) (a.respan sp) (b.respan sp) (A.respan sp) (B.respan sp) (T.respan sp)
  | .arrayNew A => .arrayNew (A.respan sp)
  | .arrayFree A => .arrayFree (A.respan sp)
  | .arraySize A => .arraySize (A.respan sp)
  | .arrayReplace A => .arrayReplace (A.respan sp)
  | .arrayLen a A => .arrayLen (a.respan sp) (A.respan sp)
  | .arrayGet a A => .arrayGet (a.respan sp) (A.respan sp)
  | .arrayCopy a A => .arrayCopy (a.respan sp) (A.respan sp)
  | .arrayForget a A => .arrayForget (a.respan sp) (A.respan sp)
  | .sliceBorrowMut x b A B =>
      .sliceBorrowMut (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp)
  | .sliceBorrowImm x b A B =>
      .sliceBorrowImm (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp)
  | .sliceGetMut a A => .sliceGetMut (a.respan sp) (A.respan sp)
  | .sliceLenMut a A => .sliceLenMut (a.respan sp) (A.respan sp)
  | .sliceSplitImm a A => .sliceSplitImm (a.respan sp) (A.respan sp)
  | .sliceSplitMut a A => .sliceSplitMut (a.respan sp) (A.respan sp)
  | .sliceEmptyImm a A => .sliceEmptyImm (a.respan sp) (A.respan sp)
  | .sliceEmptyMut a A => .sliceEmptyMut (a.respan sp) (A.respan sp)
  | .sliceReplaceMut a A => .sliceReplaceMut (a.respan sp) (A.respan sp)
  | .sliceSwapMut a A => .sliceSwapMut (a.respan sp) (A.respan sp)
  | .countFold S => .countFold (S.respan sp)
  | .countTry S E => .countTry (S.respan sp) (E.respan sp)
  | .boundedFix A C => .boundedFix (A.respan sp) (C.respan sp)
  | .withbor1U x A B r => .withbor1U (x.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
  | .withbor2U x b A B r =>
      .withbor2U (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
  | .withbor3U a x A B r =>
      .withbor3U (a.respan sp) (x.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
  | .withloadU a x A B r =>
      .withloadU (a.respan sp) (x.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
  | .sliceBorrowMutU x b A B r =>
      .sliceBorrowMutU (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
  | .sliceBorrowImmU x b A B r =>
      .sliceBorrowImmU (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)

mutual
def Val.respan (sp : Span) : Val → Val
  | .var _ x => .var sp x
  | .defApp _ n args => .defApp sp n (args.map ((VTy.respan sp)))
  | .unit _ => .unit sp
  | .pair _ V W => .pair sp (V.respan sp) (W.respan sp)
  | .inl _ V => .inl sp (V.respan sp)
  | .inr _ V => .inr sp (V.respan sp)
  | .thunk _ M => .thunk sp (M.respan sp)
  | .thunkv _ M => .thunkv sp (M.respan sp)
  | .bangThunk _ M => .bangThunk sp (M.respan sp)
  | .bangThunkv _ M => .bangThunkv sp (M.respan sp)
  | .unbang _ V => .unbang sp (V.respan sp)
  | .boxed _ a V => .boxed sp (a.respan sp) (V.respan sp)
  | .unbox _ V => .unbox sp (V.respan sp)
  | .sub _ V a => .sub sp (V.respan sp) (a.respan sp)
  | .roll _ V => .roll sp (V.respan sp)
  | .unroll _ V => .unroll sp (V.respan sp)
  | .run _ M => .run sp (M.respan sp)
  | .app _ V W => .app sp (V.respan sp) (W.respan sp)
  | .inst _ V a => .inst sp (V.respan sp) (a.respan sp)
  | .ascribe _ V A => .ascribe sp (V.respan sp) (A.respan sp)
  | .const _ c => .const sp (c.respan sp)
  | .shorten _ m σ a V => .shorten sp m (σ.respan sp) (a.respan sp) (V.respan sp)
  | .lend _ x m => .lend sp (x.respan sp) m
  | .sugar _ s => .sugar sp s

def Comp.respan (sp : Span) : Comp → Comp
  | .ret _ V => .ret sp (V.respan sp)
  | .bind _ x A M N lin => .bind sp (x.respan sp) (A.map ((VTy.respan sp))) (M.respan sp) (N.respan sp) lin
  | .force _ x => .force sp (x.respan sp)
  | .lam _ x A M => .lam sp (x.respan sp) (A.respan sp) (M.respan sp)
  | .app _ M x => .app sp (M.respan sp) (x.respan sp)
  | .with_ _ M N => .with_ sp (M.respan sp) (N.respan sp)
  | .proj _ i M => .proj sp i (M.respan sp)
  | .top _ => .top sp
  | .letUnit _ V M => .letUnit sp (V.respan sp) (M.respan sp)
  | .letPair _ x y V M => .letPair sp (x.respan sp) (y.respan sp) (V.respan sp) (M.respan sp)
  | .case _ V x M y N => .case sp (V.respan sp) (x.respan sp) (M.respan sp) (y.respan sp) (N.respan sp)
  | .absurd _ V => .absurd sp (V.respan sp)
  | .lamL _ x b M => .lamL sp (x.respan sp) (b.respan sp) (M.respan sp)
  | .inst _ M a => .inst sp (M.respan sp) (a.respan sp)
  | .nuIn _ M => .nuIn sp (M.respan sp)
  | .nuOut _ M => .nuOut sp (M.respan sp)
  | .ascribe _ M C => .ascribe sp (M.respan sp) (C.respan sp)
  | .for_ _ x V M N => .for_ sp (x.respan sp) (V.respan sp) (M.respan sp) (N.respan sp)
  | .perform _ n i V => .perform sp n i (V.respan sp)
  | .abort _ n i V => .abort sp n i (V.respan sp)
  | .handle _ n hr hc M => .handle sp n (hr.respan sp) (hc.respan sp) (M.respan sp)
  | .unwind _ x A M D N =>
      .unwind sp (x.respan sp) (A.map (VTy.respan sp)) (M.respan sp) (D.respan sp) (N.respan sp)
  | .withbor2r _ x b A B r p m M =>
      .withbor2r sp (x.respan sp) (b.respan sp) (A.respan sp) (B.respan sp) (r.respan sp)
        (p.respan sp) (m.respan sp) (M.respan sp)
end

end Frontend
