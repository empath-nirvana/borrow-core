import Frontend.Syntax

/-!
# Frontend — Elab — renaming the lifetimes a term uses  `[spec §23]`

`renameLife f` replaces every lifetime variable `'x` a term, type or constant uses, at `s`, by
`f s x` (another variable, or a lifetime: `substLives`), and keeps every binder's name and every
span. `mentionsLife x M` holds when `M` uses the lifetime
`'x`: renaming `'x` changes it. The functions follow `respan` (`Frontend/Elab/Respan.lean`).
-/

namespace Frontend

/-- A binder's name is kept: only the lifetimes a term uses are renamed. -/
def Ident.renameLife (_f : Span → String → Life) (x : Ident) : Ident := x



def Life.renameLife (f : Span → String → Life) : Life → Life
  | .var s x => f s x
  | .top s => .top s
  | .dom s => .dom s
  | .meet s a b => .meet s (a.renameLife f) (b.renameLife f)
  | .join s a b => .join s (a.renameLife f) (b.renameLife f)

mutual
def VTy.renameLife (f : Span → String → Life) : VTy → VTy
  | .unit s => .unit s
  | .zero s => .zero s
  | .tensor s A B => .tensor s (A.renameLife f) (B.renameLife f)
  | .sum s A B => .sum s (A.renameLife f) (B.renameLife f)
  | .thunk s C => .thunk s (C.renameLife f)
  | .ref s A => .ref s (A.renameLife f)
  | .imm s a A => .imm s (a.renameLife f) (A.renameLife f)
  | .mut s a A => .mut s (a.renameLife f) (A.renameLife f)
  | .box s a A => .box s (a.renameLife f) (A.renameLife f)
  | .bang s A => .bang s (A.renameLife f)
  | .unk s => .unk s
  | .int s w => .int s w
  | .handle s o => .handle s o
  | .mu s X A => .mu s (X.renameLife f) (A.renameLife f)
  | .name s n => .name s n
  | .lolli s A B => .lolli s (A.renameLife f) (B.renameLife f)
  | .all s x b A => .all s (x.renameLife f) (b.renameLife f) (A.renameLife f)
  | .block s σ => .block s (σ.renameLife f)
  | .val s σ => .val s (σ.renameLife f)
  | .fam s m a σ => .fam s m (a.renameLife f) (σ.renameLife f)
  | .view s a A => .view s (a.renameLife f) (A.renameLife f)
  | .array s A => .array s (A.renameLife f)
  | .arrayImm s a A => .arrayImm s (a.renameLife f) (A.renameLife f)
  | .arrayMut s a A => .arrayMut s (a.renameLife f) (A.renameLife f)
  | .sized s D S A => .sized s (D.renameLife f) (S.renameLife f) (A.renameLife f)
  | .app s G A => .app s (G.renameLife f) (A.renameLife f)
  | .lapp s G a => .lapp s (G.renameLife f) (a.renameLife f)
  | .rowed s G r => .rowed s (G.renameLife f) (r.renameLife f)

def CTy.renameLife (f : Span → String → Life) : CTy → CTy
  | .ret s A => .ret s (A.renameLife f)
  | .arr s A C => .arr s (A.renameLife f) (C.renameLife f)
  | .amp s C D => .amp s (C.renameLife f) (D.renameLife f)
  | .top s => .top s
  | .all s x b C => .all s (x.renameLife f) (b.renameLife f) (C.renameLife f)
  | .nu s X C => .nu s (X.renameLife f) (C.renameLife f)
  | .name s n => .name s n
  | .delay s A => .delay s (A.renameLife f)
  | .stream s A => .stream s (A.renameLife f)
  | .iter s A R R' => .iter s (A.renameLife f) (R.renameLife f) (R'.renameLife f)
  | .loop s A B => .loop s (A.renameLife f) (B.renameLife f)
  | .pull s A B R => .pull s (A.renameLife f) (B.renameLife f) (R.renameLife f)
  | .eff s r A => .eff s (r.renameLife f) (A.renameLife f)

def Row.renameLife (f : Span → String → Life) : Row → Row
  | .nil => .nil
  | .cons n i q A B r => .cons n i q (A.renameLife f) (B.renameLife f) (r.renameLife f)

def Shape.renameLife (f : Span → String → Life) : Shape → Shape
  | .leaf s A => .leaf s (A.renameLife f)
  | .node s σ τ => .node s (σ.renameLife f) (τ.renameLife f)
  | .name s n => .name s n
end

def Const.renameLife (f : Span → String → Life) : Const → Const
  | .alloc A => .alloc (A.renameLife f)
  | .free A => .free (A.renameLife f)
  | .swap A B => .swap (A.renameLife f) (B.renameLife f)
  | .copy a A => .copy (a.renameLife f) (A.renameLife f)
  | .copyBang A => .copyBang (A.renameLife f)
  | .forgetImm a A => .forgetImm (a.renameLife f) (A.renameLife f)
  | .forgetMut a A => .forgetMut (a.renameLife f) (A.renameLife f)
  | .forgetUnk => .forgetUnk
  | .forgetBang A => .forgetBang (A.renameLife f)
  | .withbor1 x A B => .withbor1 (x.renameLife f) (A.renameLife f) (B.renameLife f)
  | .withbor2 x b A B => .withbor2 (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f)
  | .withbor3 a x A B => .withbor3 (a.renameLife f) (x.renameLife f) (A.renameLife f) (B.renameLife f)
  | .withload a x A B => .withload (a.renameLife f) (x.renameLife f) (A.renameLife f) (B.renameLife f)
  | .withswap a A B => .withswap (a.renameLife f) (A.renameLife f) (B.renameLife f)
  | .foldImm F y c R => .foldImm (F.renameLife f) (y.renameLife f) (c.renameLife f) (R.renameLife f)
  | .foldOwn F R => .foldOwn (F.renameLife f) (R.renameLife f)
  | .foldReuse F R => .foldReuse (F.renameLife f) (R.renameLife f)
  | .fixd A S => .fixd (A.renameLife f) (S.renameLife f)
  | .unfoldS A S => .unfoldS (A.renameLife f) (S.renameLife f)
  | .unfold C S => .unfold (C.renameLife f) (S.renameLife f)
  | .lit c => .lit c
  | .host op => .host op
  | .allocS σ => .allocS (σ.renameLife f)
  | .freeS σ => .freeS (σ.renameLife f)
  | .withborS m σ c T => .withborS m (σ.renameLife f) (c.renameLife f) (T.renameLife f)
  | .withborF2Mut c a b w A B T =>
      .withborF2Mut (c.renameLife f) (a.renameLife f) (b.renameLife f) (w.renameLife f) (A.renameLife f) (B.renameLife f) (T.renameLife f)
  | .withborF2Imm c a b A B T => .withborF2Imm (c.renameLife f) (a.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f) (T.renameLife f)
  | .arrayNew A => .arrayNew (A.renameLife f)
  | .arrayFree A => .arrayFree (A.renameLife f)
  | .arraySize A => .arraySize (A.renameLife f)
  | .arrayReplace A => .arrayReplace (A.renameLife f)
  | .arrayLen a A => .arrayLen (a.renameLife f) (A.renameLife f)
  | .arrayGet a A => .arrayGet (a.renameLife f) (A.renameLife f)
  | .arrayCopy a A => .arrayCopy (a.renameLife f) (A.renameLife f)
  | .arrayForget a A => .arrayForget (a.renameLife f) (A.renameLife f)
  | .sliceBorrowMut x b A B =>
      .sliceBorrowMut (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f)
  | .sliceBorrowImm x b A B =>
      .sliceBorrowImm (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f)
  | .sliceGetMut a A => .sliceGetMut (a.renameLife f) (A.renameLife f)
  | .sliceLenMut a A => .sliceLenMut (a.renameLife f) (A.renameLife f)
  | .sliceSplitImm a A => .sliceSplitImm (a.renameLife f) (A.renameLife f)
  | .sliceSplitMut a A => .sliceSplitMut (a.renameLife f) (A.renameLife f)
  | .sliceEmptyImm a A => .sliceEmptyImm (a.renameLife f) (A.renameLife f)
  | .sliceEmptyMut a A => .sliceEmptyMut (a.renameLife f) (A.renameLife f)
  | .sliceReplaceMut a A => .sliceReplaceMut (a.renameLife f) (A.renameLife f)
  | .sliceSwapMut a A => .sliceSwapMut (a.renameLife f) (A.renameLife f)
  | .countFold S => .countFold (S.renameLife f)
  | .countTry S E => .countTry (S.renameLife f) (E.renameLife f)
  | .boundedFix A C => .boundedFix (A.renameLife f) (C.renameLife f)
  | .withbor1U x A B r => .withbor1U (x.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)
  | .withbor2U x b A B r =>
      .withbor2U (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)
  | .withbor3U a x A B r =>
      .withbor3U (a.renameLife f) (x.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)
  | .withloadU a x A B r =>
      .withloadU (a.renameLife f) (x.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)
  | .sliceBorrowMutU x b A B r =>
      .sliceBorrowMutU (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)
  | .sliceBorrowImmU x b A B r =>
      .sliceBorrowImmU (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f) (r.renameLife f)

mutual
def Val.renameLife (f : Span → String → Life) : Val → Val
  | .var s x => .var s x
  | .clone s x => .clone s x
  | .defApp s n args => .defApp s n (args.map ((VTy.renameLife f)))
  | .unit s => .unit s
  | .pair s V W => .pair s (V.renameLife f) (W.renameLife f)
  | .inl s V => .inl s (V.renameLife f)
  | .inr s V => .inr s (V.renameLife f)
  | .thunk s M => .thunk s (M.renameLife f)
  | .thunkv s M => .thunkv s (M.renameLife f)
  | .bangThunk s M => .bangThunk s (M.renameLife f)
  | .bangThunkv s M => .bangThunkv s (M.renameLife f)
  | .unbang s V => .unbang s (V.renameLife f)
  | .boxed s a V => .boxed s (a.renameLife f) (V.renameLife f)
  | .unbox s V => .unbox s (V.renameLife f)
  | .sub s V a => .sub s (V.renameLife f) (a.renameLife f)
  | .roll s V => .roll s (V.renameLife f)
  | .unroll s V => .unroll s (V.renameLife f)
  | .run s M => .run s (M.renameLife f)
  | .app s V W => .app s (V.renameLife f) (W.renameLife f)
  | .inst s V a => .inst s (V.renameLife f) (a.renameLife f)
  | .ascribe s V A => .ascribe s (V.renameLife f) (A.renameLife f)
  | .const s c => .const s (c.renameLife f)
  | .shorten s m σ a V => .shorten s m (σ.renameLife f) (a.renameLife f) (V.renameLife f)
  | .lend s x m => .lend s (x.renameLife f) m
  | .sugar s g => .sugar s g

def Comp.renameLife (f : Span → String → Life) : Comp → Comp
  | .ret s V => .ret s (V.renameLife f)
  | .bind s x A M N lin => .bind s (x.renameLife f) (A.map ((VTy.renameLife f))) (M.renameLife f) (N.renameLife f) lin
  | .force s x => .force s (x.renameLife f)
  | .lam s x A M => .lam s (x.renameLife f) (A.renameLife f) (M.renameLife f)
  | .app s M x => .app s (M.renameLife f) (x.renameLife f)
  | .with_ s M N => .with_ s (M.renameLife f) (N.renameLife f)
  | .proj s i M => .proj s i (M.renameLife f)
  | .top s => .top s
  | .letUnit s V M => .letUnit s (V.renameLife f) (M.renameLife f)
  | .letPair s x y V M => .letPair s (x.renameLife f) (y.renameLife f) (V.renameLife f) (M.renameLife f)
  | .case s V x M y N => .case s (V.renameLife f) (x.renameLife f) (M.renameLife f) (y.renameLife f) (N.renameLife f)
  | .absurd s V => .absurd s (V.renameLife f)
  | .lamL s x b M => .lamL s (x.renameLife f) (b.renameLife f) (M.renameLife f)
  | .inst s M a => .inst s (M.renameLife f) (a.renameLife f)
  | .nuIn s M => .nuIn s (M.renameLife f)
  | .nuOut s M => .nuOut s (M.renameLife f)
  | .ascribe s M C => .ascribe s (M.renameLife f) (C.renameLife f)
  | .loop s ℓ src V M N => .loop s ℓ src (V.renameLife f) (M.renameLife f) (N.renameLife f)
  | .perform s n i V => .perform s n i (V.renameLife f)
  | .abort s n i V => .abort s n i (V.renameLife f)
  | .handle s n hr hc M => .handle s n (hr.renameLife f) (hc.renameLife f) (M.renameLife f)
  | .unwind s x A M D N =>
      .unwind s (x.renameLife f) (A.map (VTy.renameLife f)) (M.renameLife f) (D.renameLife f) (N.renameLife f)
  | .withbor2r s x b A B r p m M =>
      .withbor2r s (x.renameLife f) (b.renameLife f) (A.renameLife f) (B.renameLife f)
        (r.renameLife f) p m (M.renameLife f)
end

/-- The lifetime variables of `σ` replaced by their lifetimes.  `[spec §32]` -/
def substLives (σ : List (String × Life)) (s : Span) (x : String) : Life :=
  (σ.lookup x).getD (.var s x)

/-- `M` uses the lifetime `'x` (or binds a lifetime of that name).  `[spec §23]` -/
def Comp.mentionsLife (x : String) (M : Comp) : Bool :=
  M.renameLife (fun s y => .var s (if y == x then y ++ "'" else y)) != M

end Frontend
