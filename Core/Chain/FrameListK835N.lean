import Core.Chain.TabK835N

/-!
# The `n`-cell Mut Frame at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §4. `erwp_M_frameListCRN` and `erwp_M_frameListRN₀`
(`FamCancel836N.lean`) are one list induction, each step a Mut Frame. `erwpK_M_frameList` is that
induction at `erwpK` over any world index: the run at the world `x`, its location family
`Φ Θ c` and its tables `TbL Θ c I` read at the location typing and the view the frames before it
reached and at the cells not yet lent; each step the frame `hstep` from the table at the inner
world to the table at the outer one, at `x` (`KFrame` with the invariant `· = x`). The lifetime of
each frame is chosen fresh and below the frame's rest, `β`, `β′` and `mb`, as in the originals.

Each original statement is proved again, word for word, from `erwpK_M_frameList` at one world
(`erwp_M_frameListCRN_of_K`, `erwp_M_frameListRN_of_K`): the step is the original's, the frame
(`erwp_M_frameCRR` / `erwp_M_frameRR`) and the claim joined to the inner frames' (`tabR_le`,
`OpTabN.Sub.le`), read at one world by `erwp_eq_erwpK`.
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

/-! ### The original statements at one world -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
