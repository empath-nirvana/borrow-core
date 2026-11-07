import Core.Chain.Fam836N
import Core.Slices

/-!
# The `n`-cell Mut Frame and `slice_borrow_mut` at `SemJN₀`  `[spec §9, §23]`

Core's `wpTS_M_frameList` (`Core/SliceFrames.lean`) is one Mut Frame per place of a finite list,
around one expression, by induction on the list; `wpTS_M_frameFam` is its instance at an array's
range. `rwp_M_frameListN₀` is that induction at the chain, over the one-cell frame `rwp_M_frame`:
* frame `j` lends its leaf at a lifetime `αⱼ` fresh for the world the frames before it reached, at
  the key `(ℓⱼ, αⱼ)` (`LocTy.add`), the view moved to `αⱼ` at `ℓⱼ` (`LocTy.view_add`); one key per
  cell;
* `αⱼ` lies below the frame's rest, the payloads' stratum `β` and the result's stratum `β′`, as
  Core's `aF ⊓ β′ ⊓ β`; the frames after it are chosen below it (Core's `aR ⊓ α₁ ⊓ γH`);
* the callback receives every leaf at the innermost lifetime: a leaf lent at `αⱼ` is a value of
  `Mut 'x A` at every `α ⊑ αⱼ` through `Mut`'s slack `@aδ ⊑ b` (`mutLeafN₀`), where Core uses
  `ptoMutS_antitone`;
* a frame's postcondition returns its leaf and moves what the inner frames returned to the world
  without the frame's key (`vN_local₀`), the leaves and the result being in the frame's stratum.

`sliceBorrowM_compatN₀` is Core's `sliceBorrowM_compatX` against it, with `withbor2_compatN₀`'s
steps around the callback.
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

/-! ### `slice_borrow_mut` at the pure row -/

/-- The body of `withbor` at the source `a`, after the first β step. -/
def withborAtV (a : Val) : Val :=
  Val.lam (.pair (.val a) (.app (.app BoCa.v0 unit') (.val a)))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
