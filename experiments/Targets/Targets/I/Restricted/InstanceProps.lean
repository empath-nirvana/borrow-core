import Targets.I.Restricted.Core
import Targets.I.Routes
import Targets.B.BoLo

/-!
# The interaction — A's properties at our instance, discharged through B (RESTRUCTURE §4.3, §4.5)

A theorem that uses a B theorem to establish an A property lives here.

* `effSafe_tier1 : EffSafe tier1` (Core's form of P2), by `effSafeOfFL _ _ fl_core_tier1
  ⟨famEmpty_core, adequateEvery_core⟩`: FL at BoLo, the empty configuration and adequacy from every
  index.  PROVED AT σ=[].
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`EffSafe tier1`** (P2 for Core's typing, at unr-free rows). -/
theorem effSafe_tier1 : EffSafe (ℍ := ℍ) tier1 :=
  effSafeOfFL _ _ fl_core_tier1 ⟨famEmpty_core, adequateEvery_core⟩

end Targets

end
