import Core.Chain.TabK835N

/-!
# A run at `erwpK` may assume its resource valid  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §4. `erwpK_of_valid`: `erwp_of_valid` at `erwpK`, over any world
index. The rules at `SemJN` that split a valid resource use it.
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
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

variable {ι : Type}

/-- A run at `erwpK` may assume its resource valid (`erwp_of_valid`). -/
theorem erwpK_of_valid {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ResU.Valid ρ → erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  rw [erwpK_eq]
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  have h' := h (ResU.Valid.split hc hT.valid).2
  rw [erwpK_eq] at h'
  exact h' ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
