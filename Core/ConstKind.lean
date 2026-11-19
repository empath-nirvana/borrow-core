import Core.Compat
import Core.CodeRules
import Core.CodeNuOut
import Core.Integers
import Core.Arrays
import Core.SliceOps
import Core.SliceCopy
import Core.CountFold
import Core.BoundedFix
import Core.FoldReuse
import Core.FoldOwnG
import Core.Nu
import Core.EffFin
import Core.EffBorrow
import Core.EffBoxed
import Core.PolyLet
import Core.DivHandle
import Core.DivHandleLast
import Core.Tok
import Core.Alpha

/-!
# Core — the kernel's constants  `[spec §3, §6–§9, §11, §14, §16, §20, §23, §74]`

The constants of the typing judgment: a closed term at a type, over a consumed context, under side
conditions that read no derivation. `CDerivesX` has one rule for all of them, `constK`, indexed by a
`ConstKind`. A kind is data: it selects the term (`ConstKind.E`), the type at `⊓Δ`
(`ConstKind.ty`), the side condition (`ConstKind.OK`), the row a tied derivation ties
(`ConstKind.row`), and whether the type and side condition read the lifetime context
(`ConstKind.domFree`). Each constant's former rule is a theorem of the same name and type
(`Core/Judgment.lean`).
-/

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The kernel's constants, each with the data its term and type are read at.  `[spec §3]` -/
inductive ConstKind where
  /-- `() : 1`. -/
  | unitI
  /-- `copy : !A ⊸ !A ⊗ !A`. -/
  | copyBang (A : VTy)
  /-- `forget : !A ⊸ 1`. -/
  | releaseBang (A : VTy)
  /-- `alloc : A ⊸ Ref A`. -/
  | alloc (A : VTy)
  /-- `free : Ref A ⊸ A`. -/
  | free (A : VTy)
  /-- `mint : 1 ⊸ Tok`.  `[spec §11, §42]` -/
  | tokMint
  /-- `burn : Tok ⊸ 1`.  `[spec §11, §42]` -/
  | tokBurn
  | swap (A B : VTy)
  | copy (a : Lifetime.Life) (A : VTy)
  | releaseImm (a : Lifetime.Life) (A : VTy)
  | releaseMut (a : Lifetime.Life) (A : VTy)
  | releaseUnk
  /-- An integer literal.  `[spec §8]` -/
  | lit (c : IntLit)
  /-- A host operation.  `[spec §8]` -/
  | hostOp (op : HostOp)
  /-- `array_new`.  `[spec §9]` -/
  | arrNew (A : VTy)
  | arrFree (A : VTy)
  | arrSize (A : VTy)
  | arrReplace (A : VTy)
  | arrLen (a : Lifetime.Life) (A : VTy)
  | arrGet (a : Lifetime.Life) (A : VTy)
  | arrCopy (a : Lifetime.Life) (A : VTy)
  | arrRelease (a : Lifetime.Life) (A : VTy)
  /-- `count_fold`.  `[spec §16]` -/
  | countFold (S : VTy)
  | countTry (S E : VTy)
  /-- `bounded_fix`.  `[spec §20]` -/
  | boundedFix (A : VTy) (C : CTy)
  /-- `iterate` at a row holding `Div`.  `[spec §14]` -/
  | iterate (S : Row) (St B R : VTy)
  /-- `div_fuel`.  `[spec §14]` -/
  | divFuel (S : Row) (A : VTy)
  /-- `slice_borrow_mut`.  `[spec §9, §23]` -/
  | sliceBorrowM (A B : VTy) (x : LifeVar)
  | sliceBorrowI (A B : VTy) (x : LifeVar)
  | sliceGetM (a : Lifetime.Life) (A : VTy)
  | sliceLenM (a : Lifetime.Life) (A : VTy)
  | sliceSplitI (a : Lifetime.Life) (A : VTy)
  | sliceSplitM (a : Lifetime.Life) (A : VTy)
  | sliceEmptyI (a : Lifetime.Life) (A : VTy)
  | sliceEmptyM (a : Lifetime.Life) (A : VTy)
  | arrEmpty (A : VTy)
  | sliceReplaceM (a : Lifetime.Life) (A : VTy)
  | sliceSwapM (a : Lifetime.Life) (A : VTy)
  /-- `slice_copy_mut`.  `[spec §74]` -/
  | sliceCopyM (a b : Lifetime.Life) (A : VTy)
  /-- `withbor` (1)–(3).  `[spec §23]` -/
  | withbor1 (A B : VTy) (x : LifeVar)
  | withbor2 (A B : VTy) (x : LifeVar)
  | withbor3 (a : Lifetime.Life) (A B : VTy) (x : LifeVar)
  | withload (a : Lifetime.Life) (A B : VTy) (x : LifeVar)
  | withswap (a : Lifetime.Life) (A B : VTy)
  /-- The unwinding form of `withload`.  `[spec §19]` -/
  | withloadU (a : Lifetime.Life) (A B : VTy) (S : Row) (x : LifeVar)
  /-- The folds.  `[spec §6]` -/
  | foldImm (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy)
  | foldOwn (F : FShape) (R : VTy)
  | foldReuse (F : FShape) (R : VTy)
  | foldOwnG (B₀ : VTy) (Rs : List VTy)
  /-- Coiteration.  `[spec §7, §68]` -/
  | unfoldN (C : CTy) (S : VTy)
  | unfoldK (C : CTy) (G S : VTy)
  deriving Inhabited

namespace ConstKind

/-- The constant's term.  `[spec §3]` -/
def E : ConstKind → Expr
  | unitI => .val .unit
  | copyBang _ => BoCa.copy
  | releaseBang _ => BoCa.forget
  | alloc _ => .val (.prim .alloc)
  | free _ => .val (.prim .free)
  | tokMint => mintE
  | tokBurn => burnE
  | swap .. => BoCa.swap
  | copy .. => BoCa.copy
  | releaseImm .. => BoCa.forget
  | releaseMut .. => BoCa.forget
  | releaseUnk => BoCa.forget
  | lit c => .val ⟨.prim (.lit c), .prim⟩
  | hostOp op => .val (.prim (.host op))
  | arrNew _ => .val (.prim .tab)
  | arrFree _ => .val (.prim .drop)
  | arrSize _ => .val sizeV
  | arrReplace _ => .val replaceV
  | arrLen .. => .val arrLenV
  | arrGet .. => .val (.prim .idx)
  | arrCopy .. => .val copyV
  | arrRelease .. => .val releaseV
  | countFold _ => .val (.prim .count)
  | countTry .. => .val (.prim .countTry)
  | boundedFix .. => .val (.prim .boundedFix)
  | iterate .. => .val (.prim .iterate)
  | divFuel .. => .val divFuelV
  | sliceBorrowM .. => BoCa.withbor
  | sliceBorrowI .. => BoCa.withbor
  | sliceGetM .. => .val (.prim .idx)
  | sliceLenM .. => .val sizeV
  | sliceSplitI .. => .val (.prim .split)
  | sliceSplitM .. => .val (.prim .split)
  | sliceEmptyI .. => .val emptyFamV
  | sliceEmptyM .. => .val emptyFamV
  | arrEmpty _ => .val emptyFamV
  | sliceReplaceM .. => .val replaceV
  | sliceSwapM .. => .val swapV
  | sliceCopyM .. => .val sliceCopyV
  | withbor1 .. => BoCa.withbor
  | withbor2 .. => BoCa.withbor
  | withbor3 .. => BoCa.withbor
  | withload .. => BoCa.withload
  | withswap .. => BoCa.withswap
  | withloadU .. => BoCa.withload
  | foldImm F .. => .val (foldImmV F)
  | foldOwn F _ => .val (foldOwnV F)
  | foldReuse F _ => .val (foldReuseV F)
  | foldOwnG B₀ _ => .val (FoldP.foldOwnGV B₀)
  | unfoldN C _ => .val (unfoldV C)
  | unfoldK C .. => .val (unfoldV C)

/-- The constant's type, at the meet `bnd` of the lifetime context's domain (`⊓Δ`), which only
the lends read.  `[spec §3]` -/
def ty : ConstKind → Lifetime.Life → VTy
  | unitI, _ => .unit
  | copyBang A, _ => .thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))
  | releaseBang A, _ => .thunk (.arr (.bang A) (.ret .unit))
  | alloc A, _ => .lolli A (.ref A)
  | free A, _ => .lolli (.ref A) A
  | tokMint, _ => mintTy
  | tokBurn, _ => burnTy
  | swap A B, _ => axSwapTy A B
  | copy a A, _ => axCopyTy a A
  | releaseImm a A, _ => axForgetImmTy a A
  | releaseMut a A, _ => axForgetMutTy a A
  | releaseUnk, _ => axForgetUnkTy
  | lit c, _ => .int c.width
  | hostOp op, _ => .bang (hostSig op)
  | arrNew A, _ => arrNewTy A
  | arrFree A, _ => arrFreeTy A
  | arrSize A, _ => arrSizeTy A
  | arrReplace A, _ => arrReplaceTy A
  | arrLen a A, _ => arrLenTy a A
  | arrGet a A, _ => arrGetTy a A
  | arrCopy a A, _ => arrCopyTy a A
  | arrRelease a A, _ => arrReleaseTy a A
  | countFold S, _ => countFoldTy S
  | countTry S E, _ => countTryTy S E
  | boundedFix A C, _ => boundedFixTy A C
  | iterate S St B R, _ => iterTy S St B R
  | divFuel S A, _ => divFuelTy S A
  | sliceBorrowM A B x, bnd => sliceBorrowMTy x bnd A B
  | sliceBorrowI A B x, bnd => sliceBorrowITy x bnd A B
  | sliceGetM a A, _ => sliceGetMTy a A
  | sliceLenM a A, _ => sliceLenMTy a A
  | sliceSplitI a A, _ => sliceSplitITy a A
  | sliceSplitM a A, _ => sliceSplitMTy a A
  | sliceEmptyI a A, _ => .arrayImm a A
  | sliceEmptyM a A, _ => .sliceMut a A
  | arrEmpty A, _ => .array A
  | sliceReplaceM a A, _ => sliceReplaceMTy a A
  | sliceSwapM a A, _ => sliceSwapMTy a A
  | sliceCopyM a b A, _ => sliceCopyMTy a b A
  | withbor1 A B x, bnd => axWithbor1Ty x bnd A B
  | withbor2 A B x, bnd => axWithbor2Ty x bnd A B
  | withbor3 a A B x, bnd => axWithbor3Ty a x bnd A B
  | withload a A B x, bnd => axWithloadTy a x bnd A B
  | withswap a A B, _ => axWithswapTy a A B
  | withloadU a A B S x, bnd => withloadUTy a x bnd A B S
  | foldImm F y c R, _ => .lolli (algTy F y R) (foldTy F y c R)
  | foldOwn F R, _ => .lolli (algOTy F R) (foldOTy F R)
  | foldReuse F R, _ => .lolli (algRTy F R) (foldOTy F R)
  | foldOwnG B₀ Rs, _ => FoldP.foldGTy B₀ Rs
  | unfoldN C S, _ => unfoldTy C S
  | unfoldK C G S, _ => unfoldKTy C G S

/-- The constant's side condition at the lifetime context `Δ`; `True` where it has none.
`[spec §3]` -/
def OK : ConstKind → LifeCtx → Prop
  | iterate S .., _ => Row.divB S = true
  | divFuel S _, _ => ∀ o ∈ S, o.n ≠ divEff
  | sliceBorrowM A B x, Δ =>
      (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) ∧
        ¬ VFree x A ∧ ¬ VFree x B
  | sliceBorrowI A B x, Δ =>
      VScoped Δ A ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧
        (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) ∧ ¬ VFree x A ∧ ¬ VFree x B
  | sliceCopyM _ _ A, _ => A.Persistent
  | withbor1 A B x, Δ => Δ.find? x = none ∧ VScoped Δ A ∧ ¬ VFree x A ∧ ¬ VFree x B
  | withbor2 A B x, Δ =>
      Δ.find? x = none ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧ ¬ VFree x A ∧ ¬ VFree x B
  | withbor3 _ A B x, Δ => Δ.find? x = none ∧ ¬ VFree x A ∧ ¬ VFree x B
  | withload _ A B x, Δ => Δ.find? x = none ∧ ¬ VFree x A ∧ ¬ VFree x B
  | withloadU _ A B S x, Δ => Δ.find? x = none ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ S.Unwind x
  | foldImm F y _ R, _ =>
      F.WF ∧ F.Guarded ∧ ¬ VFree y (.mu F.ty) ∧ ¬ VFree y R ∧ ∀ Δ' a, VOutlives Δ' a R
  | foldOwn F _, _ => F.WF ∧ F.Guarded
  | foldReuse F _, _ => F.WF ∧ F.Guarded
  | foldOwnG B₀ _, _ => FoldP.PBody B₀
  | unfoldN C S, _ => C.NuOk ∧ C.BindsFresh S
  | unfoldK C G S, _ => C.NuOk ∧ G.forceTy = some (.arr S (C.instT S)) ∧ C.BindsFresh S
  | _, _ => True

/-- The row a tied derivation of the constant ties to its effect context: `iterate`'s row and
`div_fuel`'s handled row; `[]`, which every effect context ties, at every other constant.
`[spec §14, §19, §83]` -/
def row : ConstKind → Row
  | iterate S .. => S
  | divFuel S _ => tickSig :: S
  | _ => []

/-- Whether the constant's type and side condition do not read the lifetime context: false at the
lends, whose type is at `⊓Δ` and whose borrow variable is fresh for `Δ`.  `[spec §3]` -/
def domFree : ConstKind → Bool
  | sliceBorrowM .. | sliceBorrowI .. | withbor1 .. | withbor2 .. | withbor3 .. | withload ..
  | withloadU .. => false
  | _ => true

/-- A domain-free constant's type does not read `⊓Δ`. -/
theorem ty_domFree {k : ConstKind} (h : k.domFree = true) (b b' : Lifetime.Life) :
    k.ty b = k.ty b' := by
  cases k <;> first | rfl | simp [domFree] at h

/-- A domain-free constant's side condition holds at every lifetime context. -/
theorem OK_domFree {k : ConstKind} (h : k.domFree = true) {Δ Δ' : LifeCtx} (hk : k.OK Δ) :
    k.OK Δ' := by
  cases k <;> first | exact hk | simp [domFree] at h

/-- Every constant's term is closed. -/
theorem closed (k : ConstKind) : closedAt 0 k.E = true := by
  cases k with
  | divFuel => exact divFuelV_closed
  | foldImm F => exact foldImmV_closed F
  | foldOwn F => exact foldOwnV_closed F
  | foldReuse F => exact foldReuseV_closed F
  | foldOwnG B₀ => exact FoldP.foldOwnGV_closed B₀
  | unfoldN C | unfoldK C => exact unfoldV_closed C
  | _ => rfl

end ConstKind

end BoCa.Fig16.LogRel.Core
