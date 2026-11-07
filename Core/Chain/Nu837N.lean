import Core.Chain.Rules834N
import Core.Chain.Fuel835N
import Core.Chain.SI.LendCancelProg
import Core.Nu

/-!
# `νX. C` at `SemJN₀`: the unrolling, `nuIn`, `nuOut`  `[spec §7, §62]`

`docs/new-core/scope-831-interface.md` §12 (F9). `cN₀ (νX. C)` is Core's greatest fixed point
(`Core/NuRel.lean`) at the chain's signature: a candidate below one unfolding of the observation
tree (`cBN₀`), the leaves read by `vNX₀` with `X` at the candidate. Here, Core's `cC_nu_iff`:

* `vNX_inst_occ₀`, `vNX_inst_poly₀`: `vNX₀` at the reading `vN₀ S` of `X` is `vN₀` at `A[S/X]`
  (Core's `vCE_nuEnv`, `vC_inst_envS`), where `X` does not occur and at a polynomial `A`;
* `cBN_unroll₀`: one unfolding at `𝒞⟦νX. C⟧` is `𝒞⟦C[U(νX. C)/X]⟧` (Core's `cB_unroll`), the
  candidate at `δ₀` and the tree at `δ`, agreeing on the free variables of `νX. C`;
* `cN_nu_iff₀`: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at a positive `C`;
* `nuIn_compatN₀`, `nuOut_compatN₀` (Core's `nuIn_compatX`, `nuOut_compatX`);
* `unfoldN_compatN₀` (Core's `unfold_compatX`): coinduction at the greatest fixed point with the
  candidate `{unfold step s | s ∈ 𝒱⟦S⟧}` (`candNN₀`, `candNN_post₀`), through Core's terms and
  their reductions (`Core/Nu.lean`) and the chain's `map_okN₀`, `node_okN₀`. The candidate holds at
  the indices the step is valid at, at `OK` worlds and views consistent with the resource, which
  is where `U X` reads it.
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
