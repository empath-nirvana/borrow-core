import Core.Chain.Rules834N

/-!
# `withswap` and `withload` as values  `[spec §62]`

The terms `withswap` and `withload` run, read at the chain: `withswapV` (`withswap` as a value),
`withswapAt` (its body at the source `ℓ`, after the first β step), `withloadAt` (`withload`'s inner
abstraction at `ℓ`), and `consistentX_single_own` (a single owned cell is consistent with every
view). `BorrowKW835N` (`withswap` at `SemJN`), `WithloadKW835N` and the family files use them.
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

/-- `withload`'s inner abstraction at the source `ℓ`: `λf. f () (load ℓ)`. -/
def withloadAt (l : Loc) : Val :=
  Val.lam (.app (.app BoCa.v0 unit') (.app load' (.val (.loc l))))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
