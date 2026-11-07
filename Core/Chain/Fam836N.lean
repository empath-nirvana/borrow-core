import Core.Chain.Borrow834N
import Core.Chain.Rules834N
import Core.CountFold
import Core.Tok
import Core.SliceOps

/-!
# The opaque token and the families at `SemJN₀`  `[spec §9, §11, §42]`

`docs/new-core/scope-831-interface.md` §11. Each rule's chain proof is Core's compatibility lemma
(`Core/Tok.lean`, `Core/Arrays.lean`, `Core/Slices.lean`, `Core/SliceOps.lean`), line by line,
against `vN₀`'s `opq` and family clauses:
* `Tok`: `tokMint_compatN₀`, `tokBurn_compatN₀`, the cell by `erwp_alloc`/`erwp_free`;
* a family whose leaves own nothing: `arrLen_compatN₀`, `arrGet_compatN₀`, `arrCopy_compatN₀`,
  `arrRelease_compatN₀`, `sliceGetM_compatN₀`, the leaves released by `erwp_garbage`;
* every family: `famSize_compatN₀` (`arrSize`, `sliceLenM`), `famEmpty_compatN₀` (`arrEmpty`,
  `sliceEmptyI`, `sliceEmptyM`), `famSplit_compatN₀` (`sliceSplitI`, `sliceSplitM`).
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

/-! ### The relation at a family -/

/-! ### The constants at a dead context -/

/-! ### `Tok`: `mint` and `burn` -/

/-- `mint`'s value. -/
def mintV : Val := ⟨mintE, .lam⟩

/-- `burn`'s value. -/
def burnV : Val := ⟨burnE, .lam⟩

/-! ### Families whose leaves own nothing -/

/-! ### Every family -/

/-! ### `array_free` -/

/-! ### `array_replace` -/

theorem eStore_storeV (c : Loc) (x : Val) :
    eStore c x = .app (.val (Val.storeV (Val.loc c))) (.val x) := rfl

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
