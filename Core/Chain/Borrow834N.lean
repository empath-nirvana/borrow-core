import Core.Chain.Rules834N

/-!
# `withswap` at `SemJN₀`  `[spec §62]`

Core's `withswap_compatX` (`Core/Compatibility.lean`), step by step, at the per-lend world and the
pure row. The source's cell is at its view lifetime and the view types it with its family
(`erwp_antiFrame_view`, the anti-frame at the view, Core's `wpTS_M_antiFrameX`); the content is
loaded (`rwp_load`), handed to the callback, framed beside the cell (`erwp_bind_frame`, Core's
`wpTS_bind_frame`), and the callback's first component stored back (`rwp_store`); the resealed cell
is a `Mut @a A` value again, at the content's index.
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
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- `withswap` as a value. -/
def withswapV : Val := ⟨withswap, .lam⟩

/-- A single owned cell is consistent with every view: it is in the top stratum. -/
theorem consistentX_single_own (c : Loc → Option Life) (l : Loc) (w : Val) :
    ConsistentX c (ResU.single l (CellU.ownOf w)) :=
  consistentX_of_top (ResU.inStratum_single_own _ l w) c

/-- The body of `withswap` at the source `ℓ`, after the first β step. -/
def withswapAt (l : Loc) : Val :=
  Val.lam (.letpair (.app BoCa.v0 (eLoad l))
    (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))

/-! ### `withbor (3)` at the pure row -/

/-! ### `withload` at the pure row -/

/-- `withload`'s inner abstraction at the source `ℓ`: `λf. f () (load ℓ)`. -/
def withloadAt (l : Loc) : Val :=
  Val.lam (.app (.app BoCa.v0 unit') (.app load' (.val (.loc l))))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
