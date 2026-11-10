import LicUpd.Mut48

/-!
# LicUpd — the 6.59 family under growth: statements, and the lend's end from them

The restated family, as precise statements. These are the experiment's remaining targets, to
be proved in the build loop. Each follows the Paper lemma of the same name, with `↭` replaced
by the growth clause.
- `RebFrameAgLeG` (`reb_frame_ag_le`): one-sided absorption. The start's walk is absorbed by the
  end's, `CompR aL aY aY`, as printed. The inner run's `↭` becomes `UpdG`.
- `RebFrameSurplusG`: the half that replaces `reb_frame_ag_eq`'s reverse inequality. Every
  lifetime of the end walk's `imm` cell at `(l, v, w)` is the start walk's there, or is `DerLt`
  from it.
- `Six52G` (`six52_keep`): the bracket's images are found in the garbage, with the inner run at
  `UpdVG`.
- `Six59G` (`six59`): the inner run at `UpdVG`; the conclusion `UpdG`.

`lendEndG` is proved from `Six52G` and `Six59G` at `β := α`. It is the lend's end under growth,
and it replaces `LicBridgeAll`. The persistent images are 6.52's `ρ_reb` at the frame's own
lifetime, so no bridge is needed.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- `reb_frame_ag_le` with the inner run under growth. -/
def RebFrameAgLeG : Prop :=
  ∀ (β : Life) (ρ'i ρ L R Lreb Rreb aL aR areb ai aLr aRr aY eLr eRr σL σR es as pS : WRes)
    (l₀ : Loc) (s : LSet) (v : Val) (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ → L.InStratum β → UpdG Lreb Rreb →
    AgW L aL → AgW R aR → AgW (ρ.restrictDom ρ'i.exclPart) areb →
    AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai →
    ExR ρ'i es → AgW ρ'i as → ResU.CompR es as pS →
    ResU.CompR aL areb aLr → ResU.CompR aR areb aRr → ResU.CompR aR ai aY →
    AgW Lreb aLr → AgW Rreb aRr → ExS Lreb eLr → ExS Rreb eRr →
    ResU.CompS eLr aLr σL → ResU.CompS eRr aRr σR →
    ResU.CompR aL aY aY

/-- The surplus half: the end walk's lifetimes are the start walk's, or derivable from it. -/
def RebFrameSurplusG : Prop :=
  ∀ (β : Life) (ρ'i ρ L R Lreb Rreb aL aR areb ai aLr aRr aX aY eLr eRr σL σR es as pS : WRes)
    (l₀ : Loc) (s : LSet) (v : Val) (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ → L.InStratum β → R.InStratum β → UpdG Lreb Rreb →
    AgW L aL → AgW R aR → AgW (ρ.restrictDom ρ'i.exclPart) areb →
    AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai →
    ExR ρ'i es → AgW ρ'i as → ResU.CompR es as pS →
    ResU.CompR aL areb aLr → ResU.CompR aR areb aRr →
    ResU.CompR aL ai aX → ResU.CompR aR ai aY →
    AgW Lreb aLr → AgW Rreb aRr → ExS Lreb eLr → ExS Rreb eRr →
    ResU.CompS eLr aLr σL → ResU.CompS eRr aRr σR →
    ∀ (l : Loc) (t : LSet) (u : Val) (w : WRes) (ht : w.InStratum t.join) (x : Life),
      aY.get l = some (CellU.immOf t u w ht) → t.mem x →
        (∃ (t₀ : LSet) (h₀ : w.InStratum t₀.join),
          aX.get l = some (CellU.immOf t₀ u w h₀) ∧ t₀.mem x) ∨
        DerLt aX l u w x

/-- `six52_keep` with the inner run under growth. -/
def Six52G : Prop :=
  ∀ (α : Life) (ρ'i ρ ρe ρ'' ρp ρρe ρ'p : WRes),
    ResU.Reb α ρ'i ρ → ResU.CompS ρ ρe ρρe → ResU.CompS ρ'' ρp ρ'p → UpdVG ρρe ρ'p →
    ρe.InStratum α → ρ''.InStratum α →
    ∃ ψ, ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) ψ ∧
      ResU.CompS ψ (ρ.restrictDom ρ'i.exclPart) ρp ∧ ψ.InStratum α

/-- `six59` with the inner run under growth, concluding the growth clause. -/
def Six59G : Prop :=
  ∀ (β : Life) (ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes) (l₀ : Loc) (s : LSet) (v : Val)
    (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ → ResU.CompS ρ ρb ρρb → ResU.CompS ρ' ρp ρ'p → UpdVG ρρb ρ'p →
    ρb.InStratum β → ρ'.InStratum β →
    ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi →
    (∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) →
    ResU.Flat Xi σX → ResU.Flat Y σY → UpdG Xi Y

/-- **The lend's end under growth**, from `Six52G` and `Six59G` at the lend's own lifetime.
The callback's run, re-read from `c ● ρ_b` (its outstanding images `c` at its start, the frame
cell factored out), meets the growth clause. One subtraction of `c|dom(ρ_P|mut,own)` follows,
then the growth clause from the frame's start `ρᵢ ● ρ_b` to `ρ′ ● χ ● ρᵢ`. -/
theorem lendEndG (h52 : Six52G) (h59 : Six59G) {α : Life} {ρP c ρb ρ' ρp ρρb ρ'p : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρP.InStratum s.join}
    (hreb : ResU.Reb α ρP c)
    (hce : ResU.CompS c ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hrun : UpdVG ρρb ρ'p)
    (hsb : ρb.InStratum α) (hs' : ρ'.InStratum α)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρP hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρP hs))) :
    ∃ χ, ResU.CompS χ (c.restrictDom ρP.exclPart) ρp ∧ χ.InStratum α ∧
      ∀ Xi Y σX σY : WRes,
        ResU.CompS (ResU.single l₀ (CellU.immOf s v ρP hs)) ρb Xi →
        (∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρP hs)) Y) →
        ResU.Flat Xi σX → ResU.Flat Y σY → UpdG Xi Y := by
  obtain ⟨χ, hsub, hsplit, hχ⟩ := h52 α ρP c ρb ρ' ρp ρρb ρ'p hreb hce hcp hrun hsb hs'
  exact ⟨χ, hsplit, hχ, fun Xi Y σX σY hXc hYc hfX hfY =>
    h59 α ρP c ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs hreb hce hcp hrun hsb hs' hh1 hh2 hsub
      hXc hYc hfX hfY⟩

/-- `Six59G` at a run that meets `↭`: 6.59 itself. -/
theorem six59G_of_updV {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes} {l₀ : Loc}
    {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ) (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : ResU.UpdV ρρb ρ'p) (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧ ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) : UpdG Xi Y :=
  let h := ResU.six59 hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY
  ⟨UpdImmG.of_updImm h.1, h.2⟩

end BoCa.Fig16.LicUpd

end
