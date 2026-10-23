import Frontend.Syntax

/-!
# Frontend — Elab — renaming the lifetimes a term uses  `[spec §23]`

`renameLife f` replaces every lifetime variable `'x` a term, type or constant uses, at `s`, by
`f s x` (another variable, or a lifetime: `substLives`), and keeps every binder's name and every
span. Both it and `requal g`, which maps each row entry's qualifier, are `mapLQ`. `mentionsLife x M` holds when `M` uses the lifetime
`'x`: renaming `'x` changes it. The functions follow `respan` (`Frontend/Elab/Respan.lean`).
-/

namespace Frontend

/-- A binder's name is kept: only the lifetimes a term uses are renamed. -/
def Ident.mapLQ (_f : Span → String → Life) (_g : Nat → Nat → Qual → Qual) (x : Ident) : Ident :=
  x



def Life.renameLife (f : Span → String → Life) : Life → Life
  | .var s x => f s x
  | .top s => .top s
  | .dom s => .dom s
  | .meet s a b => .meet s (a.renameLife f) (b.renameLife f)
  | .join s a b => .join s (a.renameLife f) (b.renameLife f)

/-- A lifetime holds no row entry: only its variables are renamed. -/
def Life.mapLQ (f : Span → String → Life) (_g : Nat → Nat → Qual → Qual) (a : Life) : Life :=
  a.renameLife f

mutual
def VTy.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : VTy → VTy
  | .unit s => .unit s
  | .zero s => .zero s
  | .tensor s A B => .tensor s (A.mapLQ f g) (B.mapLQ f g)
  | .sum s A B => .sum s (A.mapLQ f g) (B.mapLQ f g)
  | .thunk s C => .thunk s (C.mapLQ f g)
  | .ref s A => .ref s (A.mapLQ f g)
  | .imm s a A => .imm s (a.mapLQ f g) (A.mapLQ f g)
  | .mut s a A => .mut s (a.mapLQ f g) (A.mapLQ f g)
  | .box s a A => .box s (a.mapLQ f g) (A.mapLQ f g)
  | .bang s A => .bang s (A.mapLQ f g)
  | .unk s => .unk s
  | .int s w => .int s w
  | .handle s o => .handle s o
  | .mu s X A => .mu s (X.mapLQ f g) (A.mapLQ f g)
  | .name s n => .name s n
  | .lolli s A B => .lolli s (A.mapLQ f g) (B.mapLQ f g)
  | .all s x b A => .all s (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g)
  | .block s σ => .block s (σ.mapLQ f g)
  | .val s σ => .val s (σ.mapLQ f g)
  | .fam s m a σ => .fam s m (a.mapLQ f g) (σ.mapLQ f g)
  | .view s a A => .view s (a.mapLQ f g) (A.mapLQ f g)
  | .array s A => .array s (A.mapLQ f g)
  | .arrayImm s a A => .arrayImm s (a.mapLQ f g) (A.mapLQ f g)
  | .arrayMut s a A => .arrayMut s (a.mapLQ f g) (A.mapLQ f g)
  | .sized s D S A => .sized s (D.mapLQ f g) (S.mapLQ f g) (A.mapLQ f g)
  | .app s G A => .app s (G.mapLQ f g) (A.mapLQ f g)
  | .lapp s G a => .lapp s (G.mapLQ f g) (a.mapLQ f g)
  | .rowed s G r => .rowed s (G.mapLQ f g) (r.mapLQ f g)
  | .kont s n i q B C => .kont s n i (g n i q) (B.mapLQ f g) (C.mapLQ f g)

def CTy.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : CTy → CTy
  | .ret s A => .ret s (A.mapLQ f g)
  | .arr s A C => .arr s (A.mapLQ f g) (C.mapLQ f g)
  | .amp s C D => .amp s (C.mapLQ f g) (D.mapLQ f g)
  | .top s => .top s
  | .all s x b C => .all s (x.mapLQ f g) (b.mapLQ f g) (C.mapLQ f g)
  | .nu s X C => .nu s (X.mapLQ f g) (C.mapLQ f g)
  | .name s n => .name s n
  | .delay s A => .delay s (A.mapLQ f g)
  | .stream s A => .stream s (A.mapLQ f g)
  | .iter s A R R' => .iter s (A.mapLQ f g) (R.mapLQ f g) (R'.mapLQ f g)
  | .loop s A B => .loop s (A.mapLQ f g) (B.mapLQ f g)
  | .pull s A B R => .pull s (A.mapLQ f g) (B.mapLQ f g) (R.mapLQ f g)
  | .eff s r A => .eff s (r.mapLQ f g) (A.mapLQ f g)

def Row.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : Row → Row
  | .nil => .nil
  | .cons n i q A B r => .cons n i (g n i q) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)

def Shape.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : Shape → Shape
  | .leaf s A => .leaf s (A.mapLQ f g)
  | .node s σ τ => .node s (σ.mapLQ f g) (τ.mapLQ f g)
  | .name s n => .name s n
end

def Const.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : Const → Const
  | .alloc A => .alloc (A.mapLQ f g)
  | .free A => .free (A.mapLQ f g)
  | .swap A B => .swap (A.mapLQ f g) (B.mapLQ f g)
  | .copy a A => .copy (a.mapLQ f g) (A.mapLQ f g)
  | .copyBang A => .copyBang (A.mapLQ f g)
  | .forgetImm a A => .forgetImm (a.mapLQ f g) (A.mapLQ f g)
  | .forgetMut a A => .forgetMut (a.mapLQ f g) (A.mapLQ f g)
  | .forgetUnk => .forgetUnk
  | .forgetBang A => .forgetBang (A.mapLQ f g)
  | .withbor1 x A B => .withbor1 (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .withbor2 x b A B => .withbor2 (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .withbor3 a x A B => .withbor3 (a.mapLQ f g) (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .withload a x A B => .withload (a.mapLQ f g) (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .withswap a A B => .withswap (a.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .foldImm F y c R => .foldImm (F.mapLQ f g) (y.mapLQ f g) (c.mapLQ f g) (R.mapLQ f g)
  | .foldOwn F R => .foldOwn (F.mapLQ f g) (R.mapLQ f g)
  | .foldReuse F R => .foldReuse (F.mapLQ f g) (R.mapLQ f g)
  | .fixd A S => .fixd (A.mapLQ f g) (S.mapLQ f g)
  | .unfoldS A S => .unfoldS (A.mapLQ f g) (S.mapLQ f g)
  | .unfold C S => .unfold (C.mapLQ f g) (S.mapLQ f g)
  | .lit c => .lit c
  | .host op => .host op
  | .allocS σ => .allocS (σ.mapLQ f g)
  | .freeS σ => .freeS (σ.mapLQ f g)
  | .withborS m σ c T => .withborS m (σ.mapLQ f g) (c.mapLQ f g) (T.mapLQ f g)
  | .withborF2Mut c a b w A B T =>
      .withborF2Mut (c.mapLQ f g) (a.mapLQ f g) (b.mapLQ f g) (w.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (T.mapLQ f g)
  | .withborF2Imm c a b A B T => .withborF2Imm (c.mapLQ f g) (a.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (T.mapLQ f g)
  | .arrayNew A => .arrayNew (A.mapLQ f g)
  | .arrayFree A => .arrayFree (A.mapLQ f g)
  | .arraySize A => .arraySize (A.mapLQ f g)
  | .arrayReplace A => .arrayReplace (A.mapLQ f g)
  | .arrayLen a A => .arrayLen (a.mapLQ f g) (A.mapLQ f g)
  | .arrayGet a A => .arrayGet (a.mapLQ f g) (A.mapLQ f g)
  | .arrayCopy a A => .arrayCopy (a.mapLQ f g) (A.mapLQ f g)
  | .arrayForget a A => .arrayForget (a.mapLQ f g) (A.mapLQ f g)
  | .sliceBorrowMut x b A B =>
      .sliceBorrowMut (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .sliceBorrowImm x b A B =>
      .sliceBorrowImm (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
  | .sliceGetMut a A => .sliceGetMut (a.mapLQ f g) (A.mapLQ f g)
  | .sliceLenMut a A => .sliceLenMut (a.mapLQ f g) (A.mapLQ f g)
  | .sliceSplitImm a A => .sliceSplitImm (a.mapLQ f g) (A.mapLQ f g)
  | .sliceSplitMut a A => .sliceSplitMut (a.mapLQ f g) (A.mapLQ f g)
  | .sliceEmptyImm a A => .sliceEmptyImm (a.mapLQ f g) (A.mapLQ f g)
  | .sliceEmptyMut a A => .sliceEmptyMut (a.mapLQ f g) (A.mapLQ f g)
  | .sliceReplaceMut a A => .sliceReplaceMut (a.mapLQ f g) (A.mapLQ f g)
  | .sliceSwapMut a A => .sliceSwapMut (a.mapLQ f g) (A.mapLQ f g)
  | .countFold S => .countFold (S.mapLQ f g)
  | .countTry S E => .countTry (S.mapLQ f g) (E.mapLQ f g)
  | .boundedFix A C => .boundedFix (A.mapLQ f g) (C.mapLQ f g)
  | .withbor1U x A B r => .withbor1U (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)
  | .withbor2U x b A B r =>
      .withbor2U (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)
  | .withbor3U a x A B r =>
      .withbor3U (a.mapLQ f g) (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)
  | .withloadU a x A B r =>
      .withloadU (a.mapLQ f g) (x.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)
  | .sliceBorrowMutU x b A B r =>
      .sliceBorrowMutU (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)
  | .sliceBorrowImmU x b A B r =>
      .sliceBorrowImmU (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g) (r.mapLQ f g)

mutual
def Val.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : Val → Val
  | .var s x => .var s x
  | .clone s x => .clone s x
  | .defApp s n args => .defApp s n (args.map ((VTy.mapLQ f g)))
  | .unit s => .unit s
  | .pair s V W => .pair s (V.mapLQ f g) (W.mapLQ f g)
  | .inl s V => .inl s (V.mapLQ f g)
  | .inr s V => .inr s (V.mapLQ f g)
  | .thunk s M => .thunk s (M.mapLQ f g)
  | .thunkv s M => .thunkv s (M.mapLQ f g)
  | .bangThunk s M => .bangThunk s (M.mapLQ f g)
  | .bangThunkv s M => .bangThunkv s (M.mapLQ f g)
  | .unbang s V => .unbang s (V.mapLQ f g)
  | .boxed s a V => .boxed s (a.mapLQ f g) (V.mapLQ f g)
  | .unbox s V => .unbox s (V.mapLQ f g)
  | .sub s V a => .sub s (V.mapLQ f g) (a.mapLQ f g)
  | .roll s V => .roll s (V.mapLQ f g)
  | .unroll s V => .unroll s (V.mapLQ f g)
  | .run s M => .run s (M.mapLQ f g)
  | .app s V W => .app s (V.mapLQ f g) (W.mapLQ f g)
  | .inst s V a => .inst s (V.mapLQ f g) (a.mapLQ f g)
  | .ascribe s V A => .ascribe s (V.mapLQ f g) (A.mapLQ f g)
  | .const s c => .const s (c.mapLQ f g)
  | .shorten s m σ a V => .shorten s m (σ.mapLQ f g) (a.mapLQ f g) (V.mapLQ f g)
  | .lend s x m => .lend s (x.mapLQ f g) m
  | .sugar s g => .sugar s g
  | .mark s k V => .mark s k (V.mapLQ f g)

def Comp.mapLQ (f : Span → String → Life) (g : Nat → Nat → Qual → Qual) : Comp → Comp
  | .ret s V => .ret s (V.mapLQ f g)
  | .bind s x A M N lin => .bind s (x.mapLQ f g) (A.map ((VTy.mapLQ f g))) (M.mapLQ f g) (N.mapLQ f g) lin
  | .force s x => .force s (x.mapLQ f g)
  | .lam s x A M => .lam s (x.mapLQ f g) (A.mapLQ f g) (M.mapLQ f g)
  | .app s M x => .app s (M.mapLQ f g) (x.mapLQ f g)
  | .with_ s M N => .with_ s (M.mapLQ f g) (N.mapLQ f g)
  | .proj s i M => .proj s i (M.mapLQ f g)
  | .top s => .top s
  | .letUnit s V M => .letUnit s (V.mapLQ f g) (M.mapLQ f g)
  | .letPair s x y V M => .letPair s (x.mapLQ f g) (y.mapLQ f g) (V.mapLQ f g) (M.mapLQ f g)
  | .case s V x M y N => .case s (V.mapLQ f g) (x.mapLQ f g) (M.mapLQ f g) (y.mapLQ f g) (N.mapLQ f g)
  | .absurd s V => .absurd s (V.mapLQ f g)
  | .lamL s x b M => .lamL s (x.mapLQ f g) (b.mapLQ f g) (M.mapLQ f g)
  | .inst s M a => .inst s (M.mapLQ f g) (a.mapLQ f g)
  | .nuIn s M => .nuIn s (M.mapLQ f g)
  | .nuOut s M => .nuOut s (M.mapLQ f g)
  | .ascribe s M C => .ascribe s (M.mapLQ f g) (C.mapLQ f g)
  | .loop s ℓ src V M N => .loop s ℓ src (V.mapLQ f g) (M.mapLQ f g) (N.mapLQ f g)
  | .perform s n i V => .perform s n i (V.mapLQ f g)
  | .abort s n i V => .abort s n i (V.mapLQ f g)
  | .handle s n st hr hc M =>
    .handle s n (st.map (SiteRec.mapTy (VTy.mapLQ f g)))
      (hr.mapLQ f g) (hc.mapLQ f g) (M.mapLQ f g)
  | .unwind s x A M D N =>
      .unwind s (x.mapLQ f g) (A.map (VTy.mapLQ f g)) (M.mapLQ f g) (D.mapLQ f g) (N.mapLQ f g)
  | .withbor2r s x b A B r p m M =>
      .withbor2r s (x.mapLQ f g) (b.mapLQ f g) (A.mapLQ f g) (B.mapLQ f g)
        (r.mapLQ f g) p m (M.mapLQ f g)
end

/-- The qualifier map that keeps every row entry's. -/
def keepQ : Nat → Nat → Qual → Qual := fun _ _ q => q

/-- The variable map that keeps every lifetime. -/
def keepL : Span → String → Life := fun s x => .var s x

def VTy.renameLife (f : Span → String → Life) (A : VTy) : VTy := A.mapLQ f keepQ
def CTy.renameLife (f : Span → String → Life) (C : CTy) : CTy := C.mapLQ f keepQ
def Row.renameLife (f : Span → String → Life) (r : Row) : Row := r.mapLQ f keepQ
def Shape.renameLife (f : Span → String → Life) (σ : Shape) : Shape := σ.mapLQ f keepQ
def Const.renameLife (f : Span → String → Life) (c : Const) : Const := c.mapLQ f keepQ
def Val.renameLife (f : Span → String → Life) (V : Val) : Val := V.mapLQ f keepQ
def Comp.renameLife (f : Span → String → Life) (M : Comp) : Comp := M.mapLQ f keepQ

/-- **The row entries' qualifiers mapped** (SPEC §53): each entry `n.i q` of a row, and each
`kont[n.i q]`, at `g n i q`; lifetimes and spans kept. -/
def Comp.requal (g : Nat → Nat → Qual → Qual) (M : Comp) : Comp := M.mapLQ keepL g
def Val.requal (g : Nat → Nat → Qual → Qual) (V : Val) : Val := V.mapLQ keepL g
def VTy.requal (g : Nat → Nat → Qual → Qual) (A : VTy) : VTy := A.mapLQ keepL g
def CTy.requal (g : Nat → Nat → Qual → Qual) (C : CTy) : CTy := C.mapLQ keepL g

/-- A declaration's types and terms at `requal g`. -/
def Decl.requal (g : Nat → Nat → Qual → Qual) : Decl → Decl
  | .type sp n tps lps A => .type sp n tps lps (A.requal g)
  | .shape sp n σ => .shape sp n (σ.mapLQ keepL g)
  | .def_ sp n ps A V mk => .def_ sp n ps (A.requal g) (V.requal g) mk
  | .extern sp n A => .extern sp n (A.requal g)
  | .main sp C M => .main sp (C.requal g) (M.requal g)
  | d => d

/-- The lifetime variables of `σ` replaced by their lifetimes.  `[spec §32]` -/
def substLives (σ : List (String × Life)) (s : Span) (x : String) : Life :=
  (σ.lookup x).getD (.var s x)

/-- `M` uses the lifetime `'x` (or binds a lifetime of that name).  `[spec §23]` -/
def Comp.mentionsLife (x : String) (M : Comp) : Bool :=
  M.renameLife (fun s y => .var s (if y == x then y ++ "'" else y)) != M

end Frontend
