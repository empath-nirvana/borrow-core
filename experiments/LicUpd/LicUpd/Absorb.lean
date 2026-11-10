import LicUpd.Configs

/-!
# LicUpd — the absorption at a lifetime's end, and what stays open

**What is proved.**
- `lendEnd_absorb`: at a 6.64 lend's end, the outstanding images `c ∈ reb_α(ρ_P)` of the lent
  cell's escrow, at the lend's own lifetime `α`, are taken back by one absorption:
  6.52 (`six52_keep`), then 6.59 (`six59`), at `β := α`.
  - The conditions 6.52 and 6.59 ask, `ρ_b ∈ Res_α` and `ρ′ ∈ Res_α`, are the 6.64 frame's own
    `houtb` and `houtρ′` (`Core/FrameRules.lean`, `wpTS_I_frameX`).
  - `ρᵢ`, the frame cell `imm(s, v, ρ_P)`, is 6.59's `ρᵢ`.
  - So the walk equality behind 6.59 (`reb_frame_ag_eq`) is reached once per lifetime end. It
    is the existing lemma, at the lend's lifetime.
- `six59Lic_of_updV`: at a run that meets `↭`, the G1 form of 6.59 holds (conservativity).

**What is open, stated exactly** (not derived; obstruction not verified):
- `LicBridge`: a G1 run of the callback, with its new images `c` moved to its start and the
  frame cell factored out of both ends, is a `↭` run. This is `lendEnd_absorb`'s `hbridge`.
- `Six59Lic`: 6.59 with its update hypothesis weakened to `UpdVLic` and its conclusion to
  `UpdLic`. This is a bracketed reborrow at `β ⊏ α` whose inner run lets a persistent image at
  `α` appear.
- `LicFrame`: 6.48 at `UpdVLic`.

`k1_frame_copy` (`K1.lean`) is `LicFrame` at a one-cell frame. `UpdVLic.trans` is the
transitivity `LicFrame`'s use in bind needs.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- **One absorption at the lend's end.** The images `c` of the frame cell's escrow `ρ_P` at
the lend's lifetime `α`, outstanding in the callback's garbage `ρ⁺`, are subtracted
once. The result `χ = ρ⁺ ⊟ c|dom(ρ_P|mut,own)` lies in `Res_α`. The callback's start
`ρᵢ ● ρ_b` updates to `ρ′ ● χ ● ρᵢ`, which is the `↭` that 6.64's 6.38/6.39 then read.
`hbridge` is the callback run re-read with `c` at its start (`LicBridge`). -/
theorem lendEnd_absorb {α : Life} {ρP c ρb ρ' ρp ρρb ρ'p : WRes} {l₀ : Loc} {s : LSet}
    {v : Val} {hs : ρP.InStratum s.join}
    (hreb : ResU.Reb α ρP c)
    (hce : ResU.CompS c ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hbridge : ResU.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum α) (hs' : ρ'.InStratum α)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρP hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs))) :
    ∃ χ, ResU.SubKeep ρp (c.restrictDom ρP.exclPart) χ ∧
      ResU.CompS χ (c.restrictDom ρP.exclPart) ρp ∧ χ.InStratum α ∧
      ∀ Xi Y σX σY : WRes,
        ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb Xi →
        (∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρP hs)) Y) →
        ResU.Flat Xi σX → ResU.Flat Y σY → ResU.Upd Xi Y := by
  obtain ⟨χ, hsub, hsplit, hχ⟩ := ResU.six52_keep hreb hce hcp hbridge hsb hs'
  exact ⟨χ, hsub, hsplit, hχ, fun Xi Y σX σY hXc hYc hfX hfY =>
    ResU.six59 hreb hce hcp hbridge hsb hs' hh1 hh2 hsub hXc hYc hfX hfY⟩

/-- **Open: the bridge.** At a lend's end, the callback's run goes from `ρᵢ ● ρ_b` to
`ρ′ ● ρ⁺° ● ρᵢ` under G1, with its new images `c ∈ reb_α(ρ_P)` in `ρ⁺°`. Then the run with `c`
moved to its start and `ρᵢ` removed from both ends, `c ● ρ_b ↭ ρ′ ● ρ⁺°`, meets `↭`. -/
def LicBridge : Prop :=
  ∀ (α : Life) (ρP c ρb ρ' ρp ρρb ρ'p X Z : WRes) (l₀ : Loc) (s : LSet) (v : Val)
    (hs : ρP.InStratum s.join),
    ResU.Reb α ρP c → ResU.Le (c.restrictDom ρP.exclPart) ρp →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb X →
    ResU.CompS ρ' ρp ρ'p → ResU.CompS ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs)) Z →
    ResU.CompS c ρb ρρb →
    ρb.InStratum α → ρ'.InStratum α →
    UpdVLic X Z → ResU.UpdV ρρb ρ'p

/-- `lendEnd_absorb` with the bridge as its one hypothesis. -/
theorem lendEnd_absorb_lic (hB : LicBridge) {α : Life} {ρP c ρb ρ' ρp ρρb ρ'p X Z : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρP.InStratum s.join}
    (hreb : ResU.Reb α ρP c) (hin : ResU.Le (c.restrictDom ρP.exclPart) ρp)
    (hX : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb X)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hZ : ResU.CompS ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs)) Z)
    (hce : ResU.CompS c ρb ρρb)
    (hsb : ρb.InStratum α) (hs' : ρ'.InStratum α) (hrun : UpdVLic X Z)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρP hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs))) :
    ∃ χ, ResU.CompS χ (c.restrictDom ρP.exclPart) ρp ∧ χ.InStratum α ∧
      ∀ Xi Y σX σY : WRes,
        ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb Xi →
        (∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρP hs)) Y) →
        ResU.Flat Xi σX → ResU.Flat Y σY → ResU.Upd Xi Y := by
  have hbridge := hB α ρP c ρb ρ' ρp ρρb ρ'p X Z l₀ s v hs hreb hin hX hcp hZ hce hsb hs' hrun
  obtain ⟨χ, -, hsplit, hχ, hupd⟩ :=
    lendEnd_absorb (hs := hs) hreb hce hcp hbridge hsb hs' hh1 hh2
  exact ⟨χ, hsplit, hχ, hupd⟩

/-- **Open: 6.59 under G1.** A bracketed reborrow at `β` whose inner run is a G1 run, for
example one that lets a persistent image at some `α ⊐ β` appear. The walk equality
(`reb_frame_ag_eq`) is then asked modulo derivable images. -/
def Six59Lic : Prop :=
  ∀ (β : Life) (ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes) (l₀ : Loc) (s : LSet) (v : Val)
    (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ → ResU.CompS ρ ρb ρρb → ResU.CompS ρ' ρp ρ'p → UpdVLic ρρb ρ'p →
    ρb.InStratum β → ρ'.InStratum β →
    ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi →
    (∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) →
    ResU.Flat Xi σX → ResU.Flat Y σY → UpdLic Xi Y

/-- `Six59Lic` at a run that meets `↭`: 6.59 itself. -/
theorem six59Lic_of_updV {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ) (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p) (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) : UpdLic Xi Y :=
  UpdLic.of_upd (ResU.six59 hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY)

/-- **Open: 6.48 under G1.** -/
def LicFrame : Prop :=
  ∀ ρ π F X Z : WRes, UpdVLic ρ π → ResU.CompS F ρ X → ResU.CompS F π Z →
    ResU.Valid X → ResU.Valid Z → UpdVLic X Z

end BoCa.Fig16.LicUpd

end
