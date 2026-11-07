import Core.Chain.Rules834N
import Core.Chain.Fuel835N
import Core.Chain.SI.LendCancelProg
import Core.Nu

/-!
# `νX. C` on the chain: a pure step is its configuration's only step  `[spec §7, §62]`

`docs/new-core/scope-831-interface.md` §12 (F9). `cN (νX. C)` is Core's greatest fixed point
(`Core/NuRel.lean`) at the chain's signature: a candidate below one unfolding of the observation
tree (`cBN`), the leaves read by `vNX` with `X` at the candidate. Here, Core's `cC_nu_iff`:

* `vNX_inst_occ`, `vNX_inst_poly`: `vNX` at the reading `vN S` of `X` is `vN` at `A[S/X]`
  (Core's `vCE_nuEnv`, `vC_inst_envS`), where `X` does not occur and at a polynomial `A`;
* `cBN_unroll`: one unfolding at `𝒞⟦νX. C⟧` is `𝒞⟦C[U(νX. C)/X]⟧` (Core's `cB_unroll`), the
  candidate at `δ₀` and the tree at `δ`, agreeing on the free variables of `νX. C`;
* `cN_nu_iff`: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at a positive `C`;
* `nuIn_compatN`, `nuOut_compatN` (Core's `nuIn_compatX`, `nuOut_compatX`);
* `unfoldN_compatN` (Core's `unfold_compatX`): coinduction at the greatest fixed point with the
  candidate `{unfold step s | s ∈ 𝒱⟦S⟧}` (`candNN`, `candNN_post`), through Core's terms and
  their reductions (`Core/Nu.lean`) and the chain's `map_okN`, `node_okN`. The candidate holds at
  the indices the step is valid at, at `OK` worlds and views consistent with the resource, which
  is where `U X` reads it.

Those are in `NuKW835N`. This file holds `step1Only_of_step1N` (a pure step is its configuration's
only step), which the coinduction's reductions read.
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
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (empty_ctxClosed)

/-! ### Coiteration -/

/-- A pure step is its configuration's only step. -/
theorem step1Only_of_step1N {μ : BoCa.BoLo.Heap} {e e' : Expr}
    (h : BoCa.BoLo.Step1N (ℍ := ℍ) μ e μ e') : Step1Only (ℍ := ℍ) μ e μ e' := by
  obtain ⟨K, a, a', rfl, rfl, hh, hn⟩ := h
  exact step1Only_plug hh hn K

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
