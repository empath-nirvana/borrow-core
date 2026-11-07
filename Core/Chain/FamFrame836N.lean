import Core.Chain.Fam836N
import Core.Slices

/-!
# `withbor`'s body at a source, for `slice_borrow` and `slice_borrow_mut`  `[spec §9, §23]`

`withborAtV`: the body of `withbor` at the source `a`, after the first β step. `FamOpsKW835N`
(`slice_borrow_mut` at the pure row, `sliceBorrowM_compatN`) and `FamImmKW835N` (`slice_borrow`,
`sliceBorrowI_compatN`) run it.

Core's `wpTS_M_frameList` (`Core/SliceFrames.lean`) is one Mut Frame per place of a finite list,
around one expression, by induction on the list; `wpTS_M_frameFam` is its instance at an array's
range. On the chain it is `rwp_M_frameListN` (`FamOpsKW835N`), over the one-cell frame
`rwp_M_frame`; the callback receives every leaf at the innermost lifetime through `Mut`'s slack
`@aδ ⊑ b` (`mutLeafN`, `FrameListKW835N`), where Core uses `ptoMutS_antitone`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

/-- The body of `withbor` at the source `a`, after the first β step. -/
def withborAtV (a : Val) : Val :=
  Val.lam (.pair (.val a) (.app (.app BoCa.v0 unit') (.val a)))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
