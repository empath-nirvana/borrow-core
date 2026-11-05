import Core.Chain.SI.CanonAdv
import Core.Chain.SI.CanonN
import Core.Chain.SI.LinDisj

/-!
# Round 7's and round 8's resume worlds, at any list

`erwp_reborrow` re-enters a reborrow at the world and list the handler resumes at. It reads three
things there: the record is on the list (`rec_kept`, from `extF` at the lender's share), the
canonical image agrees with the world (`canon_escrowAgree`), and `TWNC.reb`'s `RebRecLe`
(`rebRecLe_global`). None reads the list's tags or compares it with the list the continuation
stopped at: `RebReentryG` states the three at every typed world at every list holding the record
and its cell.

* **Round 7's world** (`resume_frame_short`): the handler lends a cell of its own at any `A′` and
  resumes inside the lend. `resume_round7G`: the re-entry's premises hold there, with no condition
  on the list; `resume_round7C` asked every tag of the list to be longer than `β`.
* **Round 8's world** (`not_rebReentryAgreeN`): the handler reborrows the record while the
  continuation is stored. At `TWNC` its image is `canon cexRec β`; `resume_round8G`: the
  re-entry's premises hold at every typed world at every list holding the record's cell.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeVar)

/-- **The reborrow's re-entry premises at any resume world.** At a typed world at any list
holding the record and its cell `r.le ↦ imm(s, r.v, r.R)`, a reborrow at `β` no longer-lived than
the cell has `TWNC.reb`'s `RebRecLe`, and the canonical image agrees with the world. -/
def RebReentryG : Prop :=
  ∀ (W : WRes) (ps : List FrameRec) (ls : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (β : Life),
    TWNC W ps (rsOf ls) → r ∈ rsOf ls →
    ResU.Le (ResU.single r.le (CellU.immOf s r.v r.R hs)) W → (∀ y, s.mem y → β ⊑ y) →
    (∃ c, TmplSpec r c) →
    RebRecLe W ps r.R β ∧ ∀ a, AgW W a → EscrowAgree r.R (canon r β) a

theorem rebReentryG : RebReentryG := fun _ _ _ _ _ _ β hT hr hle hβs hex =>
  ⟨rebRecLe_global hT hr hle hβs, canon_escrowAgree hT hr (tmpl_spec hex) β⟩

/-- **Round 7's resume world, at any list.** At the world `resume_frame_shortC` builds (the
handler's `mut` cell at any `A`), the re-entry's premises hold: no condition on the tags of the
list. -/
theorem resume_round7G {W : WRes} {ps : List FrameRec} {ls : List SRec} {μ : Heap} {l : Loc}
    {β A : Life} (hT : TWNC W ps (rsOf ls)) (htg : Tagged W ps ls) (hL : ResU.Lower W μ)
    (hμ : μ l = none) (v : Val) {r : FrameRec} (hr : r ∈ rsOf ls) {s : LSet}
    {hs : r.R.InStratum s.join} (hle : ResU.Le (ResU.single r.le (CellU.immOf s r.v r.R hs)) W)
    (hβs : ∀ y, s.mem y → β ⊑ y) (hex : ∃ c, TmplSpec r c) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TWNC W' ps (rsOf ls) ∧
      Tagged W' ps ls ∧ ¬ W'.InStratum A ∧ RebRecLe W' ps r.R β ∧
      ∀ a, AgW W' a → EscrowAgree r.R (canon r β) a := by
  obtain ⟨W', hc, hT', htg', -, hnA⟩ := resume_frame_shortC hT htg hL hμ v A
  obtain ⟨τ, hτ⟩ := hle
  obtain ⟨τ', hτ', hW'⟩ := compS_reassoc hτ hc
  exact ⟨W', hc, hT', htg', hnA,
    rebReentryG W' ps ls r s hs β hT' hr ⟨τ', hW'⟩ hβs hex⟩

/-- **Round 8's resume world, at any list.** At every typed world at any list holding round 8's
record and its cell, the re-entry's premises hold: the handler's reborrow while the continuation
was stored entered at the canonical image, and nothing is read of the list but the record. -/
theorem resume_round8G (β : Life) (W : WRes) (ps : List FrameRec) (ls : List SRec) (s : LSet)
    (hs : cexRec.R.InStratum s.join) (hT : TWNC W ps (rsOf ls)) (hr : cexRec ∈ rsOf ls)
    (hle : ResU.Le (ResU.single cexRec.le (CellU.immOf s cexRec.v cexRec.R hs)) W)
    (hβs : ∀ y, s.mem y → β ⊑ y) :
    RebRecLe W ps cexRec.R β ∧ ∀ a, AgW W a → EscrowAgree cexRec.R (canon cexRec β) a :=
  rebReentryG W ps ls cexRec s hs β hT hr hle hβs (cex_canon β).1

end BoCa.Fig16.LogRel.Core.Chain.SI

end
