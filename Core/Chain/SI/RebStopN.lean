import Core.Chain.SI.RebRuleN

/-!
# `[TR]` 6.150 across a stop: the step not derived

**Not a transcription; an open step, named.** `rwp_reborrow` (6.150 at the index) chooses the
reborrow's lifetime `β` below the world `ρ_f ● ρ` of the run, after the frame `ρ_f` is known
(H11, with `fρ.InStratum β`), and the chooser's entry is `TW.reb`, whose premise
`StratumLe W β` asks the same of the world it extends.

Across a stop the borrow must be folded as at the Imm and Mut Frames: at the stop `⦇π⦈` holds the
reborrowed `imm({β}, …)` cells at the escrow's exclusive locations (`own ○ imm = imm`), where
`⦇ρ⦈` holds the escrow's own cells, so `↭`'s `imm` clause fails from right to left until 6.52
splits them off (`six52_keepN` applies at a stop with `ρ″ :=` the payload, if the payload is in
`Res_β`, and `ρ⁺ :=` the continuation's share and the garbage). At the resume the lender must
hand the continuation the **same** reborrow `χ` at the same `β` (the continuation's resource and
its `[β]` postcondition are at `β`). The resume's frame `ρ_f′` is any frame `rwpG` quantifies over,
and nothing bounds its lifetimes by `β`: a handler holding `κ` may enter an Imm Frame of its own at
a lifetime `A′ ⊏ β` and resume `κ` inside it. So the re-entry's `TW.reb` premise `StratumLe W′ β`
is not available at the resume world, and `TW` has no other constructor that adds a reborrow.

`RebReentryN` is `TW.reb` without that premise: the re-entry the across-stops 6.150 needs.
`TW.reb` uses the premise in `frameLife_reb_like` (`hβα : β ⊑ α` for every record proper), which
reads it only at records whose lineage meets the escrow's exclusive locations; a premise at those
records alone would serve there. That is a hypothesis about a refined `TW.reb`, not derived.

I have not derived `RebReentryN` and have not verified that any obstruction is real.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeVar)

/-- `TW.reb` without `StratumLe W β`: a reborrow of a record's cell at any `β` keeps the typed
world. The re-entry of 6.150 at a resume. -/
def RebReentryN : Prop :=
  ∀ (W W' c : WRes) (ps rs : List FrameRec) (r : FrameRec) (le : Loc) (s : LSet) (β : Life)
    (hs : r.R.InStratum s.join) (x : LifeVar),
    TW W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) → ¬ VFree x r.T →
    ResU.Reb β r.R c → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
    ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs

end BoCa.Fig16.LogRel.Core.Chain.SI

end
