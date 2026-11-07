import Core.Chain.SI.TWNC
import Core.Chain.SI.ExtF

/-!
# Disjoint lineages, and `RebRecLe` read off the world

**New design, not a transcription.** `TWN.reb`'s premise `RebRecLe W ps r.R β` asks the frame
lifetime of every record proper whose lineage meets an exclusive location of `r`'s escrow. The
stop-free proof reads it off the tags (`rebRecLe_of_tags`): every tag of the list is longer than
`β`. At a resume the list is the handler's, and its tags are whatever the handler's frames chose.

The fact the premise needs is global, not a bound on the list: **two records proper never share an
exclusive location of their lineages** (`LinDisj`, `TWN.linDisj`). A new frame's escrow is owned
at the top of the world when the frame is taken, so its exclusive locations are in `ex(W)_●`;
every older lineage's exclusive locations are in `ag(W)` (`ExIn`); the two are disjoint
(`not_escrow_xex`). Lineages are read off the records, which no step changes.

So the only record proper whose lineage meets `r`'s escrow is `r`'s own root, and its frame is
no shorter than the views at `r.le` (`FrameLife`). A reborrow at `β` below the cell it reborrows
then has `RebRecLe` at every world holding the cell (`rebRecLe_global`), whatever the handler
added to the list.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- **Records proper have disjoint lineages**: no exclusive location lies in the lineages of two
of them. -/
def LinDisj (ps : List FrameRec) : Prop :=
  ∀ p₁ ∈ ps, ∀ p₂ ∈ ps, ∀ m, LinLoc p₁ m → LinLoc p₂ m → p₁ = p₂

/-- A new frame's lineage locations are exclusive locations of its escrow. -/
theorem linLoc_xex {p : FrameRec} {m : Loc} (h : LinLoc p m) : XEx p.R m := by
  obtain ⟨d, ⟨q, hq⟩, ζ, eζ, kζ⟩ := h
  exact ⟨q, d.R, ζ, hq.xpath, eζ, kζ⟩

/-- `immFrame` keeps `LinDisj`: the new record's lineage locations are exclusive in the world,
an old record's lie in `ag(W)`. -/
theorem linDisj_frame {W X Z R : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val}
    {T : VTy} {δ : BoCa.Lifetime.LSub} (hvW : ResU.Valid W) (hTI : TI W ps rs)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (h : LinDisj ps) : LinDisj (⟨l, v, R, T, δ⟩ :: ps) := by
  have hXW : ResU.Le X W := ⟨Z, hW⟩
  have cross : ∀ p₁ ∈ ps, ∀ m, LinLoc p₁ m → LinLoc ⟨l, v, R, T, δ⟩ m → False := by
    intro p₁ hp₁ m h₁ h₂
    obtain ⟨d, hd, ζ, eζ, kζ⟩ := h₁
    have hdR : d ∈ rs := (hTI.2.2.2.2.2.2.1 d).mpr ⟨p₁, hp₁, hd⟩
    exact not_escrow_xex hvW hTI hXW hdR eζ kζ ((linLoc_xex h₂).of_compS_right hX)
  intro p₁ hp₁ p₂ hp₂ m h₁ h₂
  rcases List.mem_cons.mp hp₁ with rfl | hp₁ <;> rcases List.mem_cons.mp hp₂ with rfl | hp₂
  · rfl
  · exact (cross p₂ hp₂ m h₂ h₁).elim
  · exact (cross p₁ hp₁ m h₁ h₂).elim
  · exact h p₁ hp₁ p₂ hp₂ m h₁ h₂

/-- **Every `TWN` world's records proper have disjoint lineages.** -/
theorem TWN.linDisj {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : LinDisj ps := by
  induction h with
  | empty => intro p hp; exact absurd hp (by simp)
  | immFrame T δ _ hW₀ _ hX hW _ _ _ _ ih => exact linDisj_frame hW₀.valid hW₀.inv hX hW ih
  | immEnd r _ _ _ _ _ _ hps _ ih =>
      exact fun p hp p' hp' m h₁ h₂ => ih p ((hps p).mp hp).1 p' ((hps p').mp hp').1 m h₁ h₂
  | alloc _ _ _ _ _ ih => exact ih
  | reb _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih

theorem TWNC.linDisj {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : LinDisj ps :=
  h.toN.linDisj

/-- **`RebRecLe` read off the world.** At a typed world holding the record's cell
`r.le ↦ imm(s, r.v, r.R)`, a reborrow at `β` no longer-lived than the cell has its premise: the
only record proper whose lineage meets `r`'s escrow is `r`'s root (`LinDisj`), and the views at
`r.le` are no longer-lived than the root's frame (`FrameLife`). -/
theorem rebRecLe_global {W : WRes} {ps rs : List FrameRec} (hT : TWNC W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {s : LSet} {hs : r.R.InStratum s.join}
    (hle : ResU.Le (ResU.single r.le (CellU.immOf s r.v r.R hs)) W) {β : Life}
    (hβs : ∀ y, s.mem y → β ⊑ y) : RebRecLe W ps r.R β := by
  have hTI := hT.inv
  intro p hp α hα ⟨m, hLp, ζ, eζ, kζ⟩
  obtain ⟨q, hq, hqr⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
  have hLq : LinLoc q m := ⟨r, hqr, ζ, eζ, kζ⟩
  obtain rfl : p = q := hT.linDisj p hp q hq m hLp hLq
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨ζl, tl, eζl, htl, hyl⟩ := ag_ls_of_le hle haW (ResU.single_get_self _ _)
    (CellU.lsOf_immOf _ _ _ _) s.meet_mem
  have hβy := hβs _ s.meet_mem
  rcases hqr.cases with rfl | ⟨path, hpath, hlp⟩
  · rw [← hα.1 aW haW ζl tl eζl htl s.meet hyl]; exact hβy
  · obtain ⟨d', hd', hsub⟩ := hlp.last hpath
    obtain ⟨-, -, ζ', eζ', kζ', -⟩ := hsub
    have hL : LinLoc p r.le := ⟨d', hd', ζ', eζ', by rw [kζ']; simp⟩
    exact le_trans hβy (hα.2 aW haW r.le hL ζl tl eζl htl s.meet hyl)

/-! ### Chain views -/

/-- `Chain`, built from its last step, with its length. -/
inductive ChainD (R : WRes) (T : VTy) (v : Val) : Nat → Option Loc → Loc → VTy → Val → Prop
  | one {l : Loc} {S : VTy} {u : Val} :
      RefPos T v l S → R.get l = some (CellU.ownOf u) → ChainD R T v 0 none l S u
  | snoc {n : Nat} {p : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {l : Loc} {S : VTy} {u : Val} :
      ChainD R T v n p l₀ S₀ u₀ → RefPos S₀ u₀ l S → R.get l = some (CellU.ownOf u) →
      ChainD R T v (n + 1) (some l₀) l S u

theorem ChainD.chain {R : WRes} {T : VTy} {v : Val} {n : Nat} {p : Option Loc} {l : Loc}
    {S : VTy} {u : Val} (h : ChainD R T v n p l S u) : Chain R T v p l S u := by
  induction h with
  | one hp e => exact Chain.one hp e
  | snoc _ hp e ih => exact ih.snoc hp e

theorem ChainD.cons {R : WRes} {T : VTy} {v : Val} {l₁ : Loc} {S₁ : VTy} {u₁ : Val}
    (hp : RefPos T v l₁ S₁) (e₁ : R.get l₁ = some (CellU.ownOf u₁)) {n : Nat} {p : Option Loc}
    {l : Loc} {S : VTy} {u : Val} (h : ChainD R S₁ u₁ n p l S u) :
    ChainD R T v (n + 1) (some (p.getD l₁)) l S u := by
  induction h with
  | one hp' e => exact ChainD.snoc (ChainD.one hp e₁) hp' e
  | snoc _ hp' e ih => exact ChainD.snoc ih hp' e

theorem Chain.chainD {R : WRes} {T : VTy} {v : Val} {p : Option Loc} {l : Loc} {S : VTy}
    {u : Val} (h : Chain R T v p l S u) : ∃ n, ChainD R T v n p l S u := by
  induction h with
  | one hp e => exact ⟨0, ChainD.one hp e⟩
  | step hp e₁ _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, ChainD.cons hp e₁ hn⟩

theorem get_of_del {q : WRes} {l m : Loc} {ζ : CellU Loc Val} (e : (q.del l).get m = some ζ) :
    q.get m = some ζ := by
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rwa [ResU.del_get_ne _ hm] at e

/-- **A chain view's escrow holds exclusively only what the record's escrow does.** The view at a
chain position of `r` is over a piece of `r.R`, or of its parent view's escrow (`DeepInv`); by
induction along the chain, every exclusive cell of its escrow is one of `r.R`. -/
theorem chainWit_excl {W : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {a : WRes} (ha : AgW W a) :
    ∀ {n p l S u}, ChainD r.R r.T r.v n p l S u → ∀ ψ : CellU Loc Val, a.get l = some ψ →
      ψ.kind ≠ Kind.own → ∀ m (ζ : CellU Loc Val), ψ.wit.get m = some ζ → ζ.kind ≠ Kind.imm →
      ∃ ζ' : CellU Loc Val, r.R.get m = some ζ' ∧ ζ'.kind ≠ Kind.imm := by
  have hD : DeepInv W r := hTI.1.1 r hr
  intro n p l S u h
  induction h with
  | @one l S u hp e =>
      intro ψ eψ kψ m ζ eζ kζ
      obtain ⟨-, -, -, h4, -⟩ := hD none l S u (Chain.one hp e) a ha ψ eψ kψ
      obtain ⟨q, ⟨τ, hτ⟩, -, hw⟩ := h4 rfl
      rw [hw] at eζ
      exact ⟨ζ, (ResU.CompS.get_left_of_ne_imm hτ (get_of_del eζ) kζ).2, kζ⟩
  | @snoc n p l₀ S₀ u₀ l S u c hp e ih =>
      intro ψ eψ kψ m ζ eζ kζ
      obtain ⟨-, -, -, -, h5⟩ := hD (some l₀) l S u (c.chain.snoc hp e) a ha ψ eψ kψ
      obtain ⟨ψ₀, eψ₀, kψ₀, q, ⟨τ, hτ⟩, -, hw⟩ := h5 l₀ rfl
      rw [hw] at eζ
      exact ih ψ₀ eψ₀ kψ₀ m ζ (ResU.CompS.get_left_of_ne_imm hτ (get_of_del eζ) kζ).2 kζ

/-- **`RebRecLe` read off the world, at a chain view.** As `rebRecLe_global`, for a reborrow of
the view `ℓ₀ ↦ imm(s, u₀, w₀)` at a chain position of `r`: `w₀`'s exclusive cells are `r.R`'s
(`chainWit_excl`), so the only record proper whose lineage meets them is `r`'s root, and `ℓ₀` is
in its lineage. -/
theorem rebRecLe_globalD {W : WRes} {ps rs : List FrameRec} (hT : TWNC W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val}
    (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {w₀ : WRes} {s : LSet} {hs : w₀.InStratum s.join}
    (hle : ResU.Le (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) W) {β : Life}
    (hβ : β ⊑ s.meet) : RebRecLe W ps w₀ β := by
  have hTI := hT.inv
  intro p hp α hα ⟨m, hLp, ζ, eζ, kζ⟩
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨τ, hτ⟩ := hle
  obtain ⟨ζl, eζl, kζl, -, wζl, lζl⟩ :=
    (icp_trans (icpAt_left (ResU.CompS.toCompR hτ) l₀ _ (ResU.single_get_self _ _))
      (icpAt_agW haW l₀)) (CellU.kind_immOf _ _ _ _)
  obtain ⟨n, hn⟩ := Chain.chainD hch
  obtain ⟨ζr, eζr, kζr⟩ := chainWit_excl hTI hr haW hn ζl eζl (by rw [kζl]; simp) m ζ
    (by rw [wζl, CellU.wit_immOf]; exact eζ) kζ
  obtain ⟨q, hq, hqr⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
  obtain rfl : p = q := hT.linDisj p hp q hq m hLp ⟨r, hqr, ζr, eζr, kζr⟩
  have hL : LinLoc p l₀ := ⟨r, hqr, _, Chain.own hch, by simp⟩
  obtain ⟨t, ht⟩ := lsOf_of_imm kζl
  exact le_trans hβ (hα.2 aW haW l₀ hL ζl t eζl ht s.meet
    (lζl _ t (CellU.lsOf_immOf _ _ _ _) ht s.meet s.meet_mem))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
