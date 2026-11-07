import Core.Chain.Borrow834N
import Core.Chain.Rules834N
import Core.CountFold
import Core.Tok
import Core.SliceOps

/-!
# The opaque token's and the families' values  `[spec §9, §11, §42]`

`mintV` and `burnV` (`Tok`'s constants as values) and `eStore_storeV` (a store as an application of
`storeV`), used by `FamKW835N` and `FamOpsKW835N`, where the token's and the families' rules are
read at `SemJN`.
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

/-! ### `Tok`: `mint` and `burn` -/

/-- `mint`'s value. -/
def mintV : Val := ⟨mintE, .lam⟩

/-- `burn`'s value. -/
def burnV : Val := ⟨burnE, .lam⟩

/-! ### `array_replace` -/

theorem eStore_storeV (c : Loc) (x : Val) :
    eStore c x = .app (.val (Val.storeV (Val.loc c))) (.val x) := rfl

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
