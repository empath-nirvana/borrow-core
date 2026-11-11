import Core.Wp

/-!
# `TWN`: the typed world with records-only reborrow premises

**New design, not a transcription.** `TWN` is `Core/World.lean`'s `TW` with two premises
replaced, and every other constructor copied unchanged:

* `reb`'s `StratumLe W β` becomes `RebRecLe W ps r.R β`: every record proper whose lineage meets
  an exclusive location of the reborrowed escrow has its frame no shorter than `β`;
* `rebEnd`'s `W′.InStratum β` becomes `RebEndRec W′ rs r.R β`: at every chain position of a record
  whose parent is an exclusive location of the reborrowed escrow, a view of `ag(W′)` no longer than
  `β` has a view no shorter at the parent.

## Soundness argument

`TW`'s two premises are read in exactly one place each. `StratumLe W β` is read in
`frameLife_reb_like` as `β ⊑ α` at a record proper whose lineage meets an exclusive location of
the escrow (`frameLife_reb_rec` takes it there only); `W′.InStratum β` is read in `ti_endReb`
for `NestLife`, at a chain position whose parent lost the lifetime `β`, and that parent is an
exclusive location of the escrow; there it rules out a child view no longer than `β` whose only
parent view no shorter was at `β`, and `RebEndRec` asks exactly that (`ti_endRebN`). So `TWN` keeps `TI` (`TWN.inv`) and `LinLife`
(`TWN.linLife`), the facts the development reads of a typed world.

`twN_of_tw` is the conservativity: every `TW` world is a `TWN` world (`rebRecLe_of_stratumLe`,
`rebEndRec_of_inStratum`).

The reason for the change is a configuration `TW` excludes and a stored continuation reaches:
a handler lends a cell of its own at `A′ ⊏ β` and resumes, inside that lend, a continuation
holding a reborrow at `β` (`resume_frame_short`, `SI/RebResumeN.lean`). The handler's cell is in
no record's lineage, so neither refined premise reads it.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-- **The records-only premise of `reb`.** Every record proper whose lineage meets an exclusive
location of the reborrowed escrow `w₀` has its frame no shorter than `β`. -/
def RebRecLe (W : WRes) (ps : List FrameRec) (w₀ : WRes) (β : Life) : Prop :=
  ∀ p ∈ ps, ∀ α, FrameLife W p α →
    (∃ m, LinLoc p m ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) → β ⊑ α

/-- **The chain-positions premise of `rebEnd`.** At a chain position of a record whose parent is
an exclusive location of the reborrowed escrow `w₀`, every view of `ag(W′)` no longer than `β` has a
view no shorter at the parent: the nesting of chain views survives the loss of `β` at the parent. -/
def RebEndRec (W' : WRes) (rs : List FrameRec) (w₀ : WRes) (β : Life) : Prop :=
  ∀ r ∈ rs, ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
    (∃ ζ : CellU Loc Val, w₀.get l₀ = some ζ ∧ ζ.kind ≠ Kind.imm) →
    ∀ a', AgW W' a' → ∀ (ψ : CellU Loc Val) s, a'.get m = some ψ → ψ.lsOf = some s →
      ∀ x, s.mem x → x ⊑ β →
      ∃ (ζ : CellU Loc Val) (t : LSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOf = some t ∧
        t.mem y ∧ x ⊑ y

/-- **The view premise of `rebDeep`.** The view of `ag(W)` at the reborrowed chain view has a
lifetime no shorter than `β`: the new views below it are nested in it. -/
def RebCellLe (W : WRes) (l₀ : Loc) (β : Life) : Prop :=
  ∀ a, AgW W a → ∃ (ψ : CellU Loc Val) (t : LSet) (y : Life), a.get l₀ = some ψ ∧
    ψ.lsOf = some t ∧ t.mem y ∧ β ⊑ y

/-- `W′ ∈ Res_β` gives the chain-positions premise: every view of `ag(W′)` is longer than `β`. -/
theorem rebEndRec_of_inStratum {W' : WRes} {rs : List FrameRec} {w₀ : WRes} {β : Life}
    (h : W'.InStratum β) : RebEndRec W' rs w₀ β := by
  intro _ _ _ m _ _ _ _ a' ha' ψ s e hs x hx hxβ
  have hin : β < s.meet := (Life.sqsupset_iff _ _).mp
    (CellU.sqsupset_of_lsOf hs (BoCa.Fig16.BoLo.AgW.inStratum ha' β h m ψ e))
  exact (lt_irrefl β (lt_of_lt_of_le hin (le_trans (s.meet_least x hx) hxβ))).elim

/-- The typed world with records-only reborrow premises: `TW` with `reb`'s `StratumLe W β`
replaced by `RebRecLe W ps r.R β` and `rebEnd`'s `W′.InStratum β` by `RebEndRec W′ rs r.R β`.
`[about ours: new design beside TW; SI/TWN.lean's header]` -/
inductive TWN : WRes → List FrameRec → List FrameRec → Prop
  | empty : TWN PMap.empty [] []
  | alloc {W W' : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TWN W ps rs → ResU.Lower W μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.ownOf v)) W' → ResU.Valid W' → TWN W' ps rs
  | immFrame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val} {α : Life}
      (T : VTy) (δ : BoCa.Lifetime.LSub) (h : R.InStratum (LSet.singleton α).join) :
      TWN W ps rs → AdmWf T δ → ResU.CompS (ResU.single l (CellU.ownOf v)) R X →
      ResU.CompS X Z W → vShape T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W' →
      ResU.Valid W' → (∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) →
      TWN W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} (x : LifeVar) :
      TWN W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) →
      ¬ VFree x r.T → ResU.Reb β r.R c →
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      RebRecLe W ps r.R β → ResU.CompS W c W' → ResU.Valid W' → TWN W' ps rs
  | rebDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc} {l₀ : Loc}
      {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join} {β : Life}
      (x : LifeVar) :
      TWN W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ¬ VFree x S₀ → ResU.Reb β w₀ c →
      vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      RebCellLe W l₀ β → RebRecLe W ps w₀ β →
      ResU.CompS W c W' → ResU.Valid W' → TWN W' ps rs
  | mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W →
      ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W' → ResU.Valid W' →
      TWN W' ps rs
  | mutUnfold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W' → ResU.Valid W' →
      TWN W' ps rs
  | free {W W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) W' W → ResU.Valid W' →
      TWN W' ps rs
  | store {W Z W' : WRes} {ps rs : List FrameRec} {l : Loc} {v₁ v₂ : Val} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v₂)) Z W' → ResU.Valid W' → TWN W' ps rs
  | immEnd {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} (r : FrameRec) {s : LSet}
      {hs : r.R.InStratum s.join} :
      TWN W ps rs → r ∈ ps → ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W →
      ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X' → ResU.CompS X' Y W' →
      ResU.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) → TWN W' ps' rs'
  | rebEnd {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} :
      TWN W ps rs → r ∈ rs → W'.get le = some (CellU.immOf s r.v r.R hs) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      RebEndRec W' rs r.R β → TWN W' ps rs
  | rebEndDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc}
      {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
      {β : Life} :
      TWN W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → RebEndRec W' rs w₀ β → TWN W' ps rs

theorem TWN.valid {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : ResU.Valid W := by
  induction h with
  | empty => exact ⟨_, flat_empty⟩
  | alloc _ _ _ _ hv _ => exact hv
  | immFrame _ _ _ _ _ _ _ _ _ hv _ _ => exact hv
  | reb _ _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | mutFold _ _ _ _ hv _ => exact hv
  | mutUnfold _ _ _ _ hv _ => exact hv
  | free _ _ hv _ => exact hv
  | store _ _ _ hv _ => exact hv
  | immEnd _ _ _ _ _ _ hv _ _ _ => exact hv
  | rebEnd _ _ _ _ _ hW _ ih => exact (ResU.Valid.split hW ih).1
  | rebEndDeep _ _ _ _ _ _ hW _ ih => exact (ResU.Valid.split hW ih).1

/-- `ti_endReb` with `RebEndRec` in place of `W′ ∈ Res_β`. -/
theorem ti_endRebN {W W' c w₀ : WRes} {ps rs : List FrameRec} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life}
    (hvW : ResU.Valid W) (hle : W'.get le = some (CellU.immOf s v w₀ hs))
    (hreb : ResU.Reb β w₀ c) (hW : ResU.CompS W' (c.restrictDom w₀.exclPart) W)
    (hβ : RebEndRec W' rs w₀ β)
    (hexcl : ∀ r ∈ rs, ∀ u, w₀.get r.le ≠ some (CellU.ownOf u))
    (h : TI W ps rs) : TI W' ps rs := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle4, hid, hio, hN, hM, hmem, hC⟩ := h
  have hv : ResU.Valid W' := (ResU.Valid.split hW hvW).1
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  obtain ⟨a'', acr, ha'', hacr, hcomp⟩ := (AgW.split hW).mp haW
  rw [AgW.functional ha'' ha'] at hcomp
  have crSrc : ∀ x (ψ : CellU Loc Val), (c.restrictDom w₀.exclPart).get x = some ψ →
      c.get x = some ψ ∧ ∃ ζ : CellU Loc Val, w₀.get x = some ζ ∧ ζ.kind ≠ Kind.imm := by
    intro x ψ e
    cases ex : w₀.exclPart.get x with
    | none => rw [ResU.restrictDom_get_of_none ex] at e; cases e
    | some ζ =>
        rw [ResU.restrictDom_get_of_some ex] at e
        exact ⟨e, ζ, (ResU.exclPart_eq_some.mp ex).1, (ResU.exclPart_eq_some.mp ex).2⟩
  obtain ⟨d', bi, hdb, hbi, hd'⟩ :=
    img_walk ha' hle hreb (fun x ψ e => (crSrc x ψ e).1) hacr
  have R1 : ∀ m (ψ : CellU Loc Val), a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro m ψ e hk
    obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp e hk
    exact ⟨ψ₀, e₀, k₀, w₀'.symm⟩
  have R3 : ∀ m (ψ₀ : CellU Loc Val), (c.restrictDom w₀.exclPart).get m = none →
      aW.get m = some ψ₀ → ψ₀.kind = Kind.imm →
      ∃ ψ : CellU Loc Val, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧
        ψ.wit = ψ₀.wit := by
    intro m ψ₀ hn e₀ k₀
    rcases imm_back_full hcomp e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · exact ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · rcases imm_back_full hdb e₁ k₁ with ⟨ψ₂, e₂, -, -, -⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
      · have := hd' m ψ₂ e₂; rw [hn] at this; cases this
      · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := hbi m ψ₂ e₂ k₂
        exact ⟨ζ, eζ, kζ, rζ.trans (r₂.trans r₁), wζ.trans (w₂.trans w₁)⟩
  have R4 : ∀ m (ζ : CellU Loc Val) t y, aW.get m = some ζ → ζ.lsOf = some t → t.mem y →
      (∃ (ζ' : CellU Loc Val) (t' : LSet), a'.get m = some ζ' ∧ ζ'.lsOf = some t' ∧ t'.mem y) ∨
      (y = β ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
    intro m ζ t y e ht hy
    rcases ResU.CompR.lsOf_inv hcomp e ht hy with h' | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
    · exact Or.inl h'
    · rcases ResU.CompR.lsOf_inv hdb e₁ ht₁ hy₁ with ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩ |
          ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩
      · obtain ⟨ec, ζw, eζw, kζw⟩ := crSrc m ξ₂ (hd' m ξ₂ e₂)
        rcases reb_cell_ls hreb ec with ⟨-, hl⟩ | ⟨ζ₃, eζ₃, kζ₃, -⟩
        · rw [hl] at ht₂; cases Option.some.inj ht₂; exact Or.inr ⟨hy₂, ζw, eζw, kζw⟩
        · rw [eζ₃] at eζw; cases Option.some.inj eζw; exact absurd kζ₃ kζw
      · exact Or.inl ((hbi m ξ₂ e₂).ls ht₂ hy₂)
  have tm : ∀ x, MutAt W' x → MutAt W x := fun x hm => MutAt.of_compS_left hW hm
  have kimm : ∀ r ∈ rs, ∀ p m S u, Chain r.R r.T r.v p m S u → ∀ ψ : CellU Loc Val,
      a'.get m = some ψ → ψ.kind ≠ Kind.own → ψ.kind = Kind.imm := by
    intro r hr p m S u hc ψ e hk
    cases hkk : ψ.kind with
    | own => exact absurd hkk hk
    | imm => rfl
    | «mut» => exact (hM.2 r hr m u hc.own (tm _ (agW_mut ha' m ψ e hkk))).elim
  have hN' : ∀ r ∈ rs, NestLife W' r := by
    intro r hr l₀ m S u hc a₁ ha₁ ψ s' e hs' x hx
    rw [AgW.functional ha₁ ha'] at e ⊢
    obtain ⟨ζ, t, eζ, ht, hxt⟩ := (icpAt_left hcomp m ψ e).ls hs' hx
    obtain ⟨ζ₀, t₀, y, e₀, ht₀, hy, hxy⟩ := hN r hr l₀ m S u hc aW haW ζ t eζ ht x hxt
    rcases R4 l₀ ζ₀ t₀ y e₀ ht₀ hy with ⟨ζ', t', e', ht', hy'⟩ | hβy
    · exact ⟨ζ', t', y, e', ht', hy', hxy⟩
    · obtain ⟨rfl, hex⟩ := hβy
      exact hβ r hr l₀ m S u hc hex a' ha' ψ s' e hs' x hx hxy
  have parent : ∀ r ∈ rs, ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ∀ ψ : CellU Loc Val, a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ : CellU Loc Val, a'.get l₀ = some ζ ∧ ζ.kind ≠ Kind.own := by
    intro r hr l₀ m S u hc ψ e hk
    obtain ⟨s', hs'⟩ := lsOf_of_imm (kimm r hr _ m S u hc ψ e hk)
    obtain ⟨ζ, t, y, eζ, ht, -, -⟩ := hN' r hr l₀ m S u hc a' ha' ψ s' e hs' s'.meet s'.meet_mem
    exact ⟨ζ, eζ, by rw [CellU.kind_of_lsOf ht]; simp⟩
  have hD' : ∀ r ∈ rs, DeepInv W' r := by
    intro r hr p m S u hc a₁ ha₁ ψ e hk
    rw [AgW.functional ha₁ ha'] at e ⊢
    obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := R1 m ψ e hk
    obtain ⟨-, d, o, b₁, b₂⟩ := h1 r hr p m S u hc aW haW ψ₀ e₀ k₀
    refine ⟨kimm r hr p m S u hc ψ e hk, w₀' ▸ d, w₀' ▸ o, fun hp => w₀' ▸ b₁ hp,
      fun l₀ hp => ?_⟩
    subst hp
    obtain ⟨ζ, eζ, kζ⟩ := parent r hr l₀ m S u hc ψ e hk
    obtain ⟨ζ₀, eζ₀, -, wζ⟩ := R1 l₀ ζ eζ kζ
    obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ rfl
    rw [eζ₀] at e₁; cases Option.some.inj e₁
    exact ⟨ζ, eζ, kζ, q, wζ ▸ hq, hql, w₀'.trans hw⟩
  have hle' : LeInv W' ps := by
    intro r hr a₁ ha₁
    rw [AgW.functional ha₁ ha']
    obtain ⟨ψ₀, e₀, k₀, r₀, w₀''⟩ := hle4 r hr aW haW
    have hrR : r ∈ rs := (hmem r).mpr ⟨r, hr, DescR.refl r⟩
    have hn : (c.restrictDom w₀.exclPart).get r.le = none := by
      cases ecr : (c.restrictDom w₀.exclPart).get r.le with
      | none => rfl
      | some φ =>
          exfalso
          obtain ⟨-, ζ, eζ, kζ⟩ := crSrc _ _ ecr
          rcases CellU.rep ζ with ⟨u', rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ |
              ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
          · exact hexcl r hrR u' eζ
          · exact kζ (CellU.kind_immOf _ _ _ _)
          · exact hM.1 r hr (tm _ (mutAt_of_cell hle (MutAt.top eζ (by simp))))
    obtain ⟨ψ, e, k, rr, ww⟩ := R3 r.le ψ₀ hn e₀ k₀
    exact ⟨ψ, e, k, rr.trans r₀, ww.trans w₀''⟩
  have h5' : ∀ r ∈ rs, JointAt W' r := by
    intro r hr
    rintro ⟨S, m, u, hR, a₁, ha₁, ψ, e, hk⟩
    rw [AgW.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgW.functional ha₂ ha'] at e₁
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  have h6' : ∀ r ∈ rs, JointDeep W' r := by
    intro r hr
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a₁, ha₁, ψ, e, hk⟩
    rw [AgW.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨w₁, hw₁, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
    obtain ⟨ζ, eζ, kζ⟩ := parent r hr l₀ m S u hc ψ e hk
    obtain ⟨ζ₀, eζ₀, -, wζ⟩ := R1 l₀ ζ eζ kζ
    obtain ⟨ψ₂, e₂, -, w₂⟩ := hw₁ aW haW
    rw [eζ₀] at e₂; cases Option.some.inj e₂
    refine ⟨w₁, fun a₂ ha₂ => ⟨ζ, by rw [AgW.functional ha₂ ha']; exact eζ, kζ, wζ.trans w₂⟩,
      β₀, x₀, c₀, q1, q2, q3, q4, fun m' S' u' hc' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgW.functional ha₂ ha'] at e₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ', eζ', wζ'⟩ := q5 m' S' u' hc' aW haW ψ₃ e₃ k₃
    exact ⟨ζ', eζ', w₃.trans wζ'⟩
  have h2' : ∀ r ∈ rs, ∀ m u, r.R.get m = some (CellU.ownOf u) → ∀ a, AgW W' a →
      ∃ ζ, a.get m = some ζ :=
    fun r hr m u hm => exIn_support (exIn_of hle' hmem hr) hm (by simp)
  refine ⟨⟨hD', h2', h3, h4, h5', h6'⟩, hle', hid, hio, hN',
    ⟨fun r hr hm => hM.1 r hr (tm _ hm), fun r hr l u hl hm => hM.2 r hr l u hl (tm _ hm)⟩,
    hmem, coverage_of_icp haW hC (fun a₁ ha₁ m => ?_)⟩
  rw [AgW.functional ha₁ ha']
  exact icpAt_left hcomp m



/-- A reborrow keeps `FrameLife` at a record whose frame is no shorter than `β`:
`frameLife_reb_like` with its premise read where it is used. -/
theorem frameLife_reb_rec {W W' c w₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (hvW : ResU.Valid W)
    (hle : W.get le = some (CellU.immOf s v w₀ hs)) (hreb : ResU.Reb β w₀ c)
    (hW : ResU.CompS W c W') {p : FrameRec} {α : Life}
    (hex : ∀ ζ : CellU Loc Val, w₀.get p.le = some ζ → ζ.kind = Kind.imm)
    (hβα : (∃ m, LinLoc p m ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      β ⊑ α)
    (h : FrameLife W p α) : FrameLife W' p α := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have newls : ∀ a', AgW W' a' → ∀ m (ψ : CellU Loc Val) s' x, a'.get m = some ψ →
      ψ.lsOf = some s' → s'.mem x →
      (∃ (ζ : CellU Loc Val) (t : LSet), aW.get m = some ζ ∧ ζ.lsOf = some t ∧ t.mem x) ∨
      (x = β ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
    intro a' ha' m ψ s' x e hs' hx
    obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgW.split hW).mp ha'
    rw [AgW.functional haW' haW] at hcomp
    rcases ResU.CompR.lsOf_inv hcomp e hs' hx with h₁ | ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · exact Or.inl h₁
    · rcases img_ls haW hle hreb (fun _ _ e => e) hac e₁ ht₁ hx₁ with h₂ | ⟨rfl, -, h₃⟩
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, h₃⟩
  refine ⟨fun a' ha' ζ t e ht y hy => ?_, fun a' ha' m hm ψ s' e hs' x hx => ?_⟩
  · rcases newls a' ha' p.le ζ t y e ht hy with ⟨ζ', t', e', ht', hy'⟩ | ⟨-, ζ', e', k'⟩
    · exact h.1 aW haW ζ' t' e' ht' y hy'
    · exact absurd (hex ζ' e') k'
  · rcases newls a' ha' m ψ s' x e hs' hx with ⟨ζ', t', e', ht', hx'⟩ | ⟨rfl, ζ', e', k'⟩
    · exact h.2 aW haW m hm ζ' t' e' ht' x hx'
    · exact hβα ⟨m, hm, ζ', e', k'⟩

/-- `ti_rebDeep` with `W ∈ Res_β` read where it is used: at the view's own cell, which is longer
than `β`. -/
theorem ti_rebDeepN {W W' c : WRes} {ps rs : List FrameRec} {r₀ : FrameRec} {p₀ : Option Loc}
    {l₁ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    {β : Life} {x : LifeVar}
    (hvW : ResU.Valid W) (hr₀ : r₀ ∈ rs) (hch₀ : Chain r₀.R r₀.T r₀.v p₀ l₁ S₀ u₀)
    (hcell : W.get l₁ = some (CellU.immOf s u₀ w₀ hs)) (hx : ¬ VFree x S₀)
    (hreb : ResU.Reb β w₀ c) (hden : vShape (S₀.immReborrow (.var x)) (r₀.δ.extend x β) u₀ c)
    (hβc : RebCellLe W l₁ β) (hW : ResU.CompS W c W') (hv : ResU.Valid W') (h : TI W ps rs) :
    TI W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  have hR₀ := (h3.2.2.2.1 r₀ hr₀).1
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
    h3.1 r₀ hr₀ p₀ l₁ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  have hl' := leInv_of_reb hvW hW hl
  obtain ⟨hN', hM'⟩ := nm_reb_like hvW hcell hreb hW hN hM
    (fun aW₁ haW₁ a' ha' r hr l₀ m S u hc u' hown hφ => by
      rw [AgW.functional haW₁ haW] at *
      have e₁ : r = r₀ := h3.2.2.1 r hr r₀ hr₀ m u u' hc.own (hw₀own m u' hown)
      subst e₁
      obtain ⟨φ, eφ⟩ := hφ
      obtain ⟨ζ, eζ, hpos⟩ := image_dom S₀ hden hw₀den eφ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S', hS'⟩ := hpos rfl
      have hl := (chain_unique_rec hR₀ hc (hch₀.snoc hS' (hw₀own m u' hown))).1
      have hl' : l₀ = l₁ := Option.some.inj hl
      subst hl'
      obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha'
      rw [AgW.functional haW' haW] at hcomp
      obtain ⟨ψ₁, t₁, y, e₁, ht₁, hy₁, hβy⟩ := hβc aW haW
      obtain ⟨ξ, t, eξ, ht, hy⟩ := (icpAt_left hcomp l₀ ψ₁ e₁).ls ht₁ hy₁
      exact ⟨ξ, t, y, eξ, ht, hy, hβy⟩)
  refine ⟨chainInv_rebDeep hvW hr₀ hch₀ hcell hx hreb hden hW hv h3, hl', hid, hio, hN', hM', hmem,
    ?_⟩
  refine cov_reb_like hvW hcell hreb hW hC (leInvW_of hl' hmem) (fun m u eζ ⟨ψ, ec⟩ => ?_)
    (fun m ζ eζ kζ ⟨ψ, ec⟩ => ?_)
  · obtain ⟨ζ', eζ', hpos⟩ := image_dom S₀ hden hw₀den ec
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨r₀, hr₀, some l₁, S, u, hch₀.snoc hS (hw₀own m u eζ)⟩
  · obtain ⟨S, hS⟩ := image_dom_mut S₀ hden hw₀den ec eζ kζ
    have hg : GPos r₀.R r₀.T r₀.v m S := GPos.of_chain hch₀ hS
    obtain ⟨ζ', eζ', kζ', -⟩ := gpos_mut_cell hg hR₀ (fun _ _ e => e)
    obtain ⟨p, hp, hpr⟩ := (hmem r₀).mp hr₀
    refine ⟨⟨m, ζ'.erase, ζ'.wit, S, r₀.δ⟩, (hmem _).mpr ⟨p, hp, hpr.sub ?_⟩, rfl⟩
    exact ⟨rfl, hg, ζ', eζ', kζ', rfl, rfl⟩

/-- Every `TWN` world satisfies `TI`. -/
theorem TWN.inv {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : TI W ps rs := by
  induction h with
  | empty =>
      refine ⟨⟨fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp)⟩,
        fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp),
        ⟨fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp)⟩,
        fun x => ⟨fun hx => absurd hx (by simp), fun ⟨p, hp, _⟩ => absurd hp (by simp)⟩, ?_⟩
      intro a ha m ψ e _
      rw [AgW.functional ha agW_empty, PMap.empty_get] at e; cases e
  | alloc _ _ _ hW _ ih =>
      refine ti_of_ag (fun a ha => alloc_ag hW ha) (fun x hm => ?_) ih
      rcases MutAt.split hW hm with h | h
      · exact h
      · exact (not_mutAt_single_own _ _ _ h).elim
  | immFrame T δ hα hW₀ hadm hX hW hden hW' hv hds ih =>
      exact ti_frame hW₀.valid hadm hX hW hden hW' hv hds ih
  | reb r x hW₀ hr hle hx hreb hden _ hW hv ih =>
      exact ti_reb hW₀.valid hr hle hx hreb hden hW hv ih
  | rebDeep r x hW₀ hr hch hcell hx hreb hden hβc _ hW hv ih =>
      exact ti_rebDeepN hW₀.valid hr hch hcell hx hreb hden hβc hW hv ih
  | mutFold hW₀ hX hW hW' _ ih => exact ti_mutFold hW₀.valid hX hW hW' ih
  | mutUnfold hW₀ hW hX hW' _ ih =>
      refine ti_of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) (fun x hm => ?_) ih
      rcases MutAt.split hW' hm with h | h
      · rcases MutAt.split hX h with h' | h'
        · exact (not_mutAt_single_own _ _ _ h').elim
        · refine MutAt.nest (ResU.CompS.get_left_of_ne_imm hW (ResU.single_get_self _ _)
            (by simp)).2 (by simp) ?_
          rw [CellU.wit_mutOf]; exact h'
      · exact MutAt.of_compS_right hW h
  | free hW₀ hW _ ih =>
      exact ti_of_ag (fun a ha => (own_cell_ag hW a).mpr ha)
        (fun x hm => MutAt.of_compS_right hW hm) ih
  | store hW₀ hW hW' _ ih =>
      refine ti_of_ag (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha))
        (fun x hm => ?_) ih
      rcases MutAt.split hW' hm with h | h
      · exact (not_mutAt_single_own _ _ _ h).elim
      · exact MutAt.of_compS_right hW h
  | immEnd r hW₀ hr hc hX' hW' hv hps hrs ih => exact ti_end hW₀.valid hr hc hX' hW' hv hps hrs ih
  | rebEnd r hW₀ hr hle hreb hW hβ ih =>
      exact ti_endRebN hW₀.valid hle hreb hW hβ (fun r' hr' u hu => ih.2.2.2.1 r' hr' r hr u hu) ih
  | @rebEndDeep W W' c ps rs r p l₀ S₀ u₀ s w₀ hs β hW₀ hr hch hle hreb hW hβ ih =>
      have hvW := hW₀.valid
      have hexcl : ∀ r' ∈ rs, ∀ u, w₀.get r'.le ≠ some (CellU.ownOf u) := by
        intro r' hr' u hu
        obtain ⟨aW, haW⟩ := agW_of_valid hvW
        obtain ⟨a', ha'⟩ := agW_of_valid (ResU.Valid.split hW hvW).1
        obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
        rw [AgW.functional ha'' ha'] at hcomp
        obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm ha' hle (CellU.kind_immOf _ _ _ _)
        obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp eχ (by rw [kχ]; simp)
        obtain ⟨-, -, o, -, -⟩ := ih.1.1 r hr p l₀ S₀ u₀ hch aW haW ψ₀ e₀ k₀
        rw [w₀', wχ, CellU.wit_immOf] at o
        exact ih.2.2.2.1 r' hr' r hr u (o _ u hu)
      exact ti_endRebN hvW hle hreb hW hβ hexcl ih


/-- Every `TWN` world satisfies `LinLife`. -/
theorem TWN.linLife {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : LinLife W ps := by
  induction h with
  | empty => intro p hp; exact absurd hp (by simp)
  | alloc _ _ _ hW _ ih => exact linLife_of_ag (fun a ha => alloc_ag hW ha) ih
  | immFrame T δ hα hW₀ hadm hX hW hden hW' hv hds ih =>
      exact linLife_frame hW₀.valid hX hW hW' hW₀.inv ih
  | @reb W W' c ps rs r le s β hs x hW₀ hr hle hx hreb hden hβ hW hv ih =>
      have hTI := hW₀.inv
      intro p hp
      obtain ⟨α, hα⟩ := ih p hp
      have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
      refine ⟨α, frameLife_reb_rec hW₀.valid hle hreb hW (fun ζ e => ?_) (hβ p hp α hα) hα⟩
      rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
      · exact (hTI.2.2.2.1 p hpR r hr u e).elim
      · exact CellU.kind_immOf _ _ _ _
      · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hle (MutAt.top e (by simp)))).elim
  | @rebDeep W W' c ps rs r p₀ l₁ S₀ u₀ s w₀ hs β x hW₀ hr hch hcell hx hreb hden _ hβ hW hv
      ih =>
      have hTI := hW₀.inv
      have hvW := hW₀.valid
      obtain ⟨aW, haW⟩ := agW_of_valid hvW
      obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
      rw [CellU.wit_immOf] at wχ
      obtain ⟨-, -, hw₀own, -, -⟩ :=
        hTI.1.1 r hr p₀ l₁ S₀ u₀ hch aW haW χ eχ (by rw [kχ]; simp)
      rw [wχ] at hw₀own
      intro p hp
      obtain ⟨α, hα⟩ := ih p hp
      have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
      refine ⟨α, frameLife_reb_rec hvW hcell hreb hW (fun ζ e => ?_) (hβ p hp α hα) hα⟩
      rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
      · exact (hTI.2.2.2.1 p hpR r hr u (hw₀own _ u e)).elim
      · exact CellU.kind_immOf _ _ _ _
      · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hcell (MutAt.top e (by simp)))).elim
  | mutFold hW₀ hX hW hW' _ ih =>
      exact linLife_of_ag (fun a ha => (mut_fold_ag hX hW hW' a).mpr ha) ih
  | mutUnfold hW₀ hW hX hW' _ ih =>
      exact linLife_of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) ih
  | free hW₀ hW _ ih => exact linLife_of_ag (fun a ha => (own_cell_ag hW a).mpr ha) ih
  | store hW₀ hW hW' _ ih =>
      exact linLife_of_ag (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha)) ih
  | @immEnd W Y X' W' ps rs ps' rs' r s hs hW₀ hr hc hX' hW' hv hps hrs ih =>
      have hvW := hW₀.valid
      obtain ⟨aW, haW⟩ := agW_of_valid hvW
      intro p hp
      obtain ⟨α, hα⟩ := ih p ((hps p).mp hp).1
      have backI : ∀ a', AgW W' a' → ∀ m, ICpAt aW a' m := by
        intro a' ha' m
        obtain ⟨aσ, aY, eR, aR, pR, heR, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
        exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
          (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
      exact ⟨α, frameLife_back hα (fun a' ha' =>
        ⟨aW, haW, backI a' ha' _, fun m _ => backI a' ha' m⟩)⟩
  | rebEnd r hW₀ hr hle hreb hW hβ ih =>
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.valid
      intro p hp
      obtain ⟨α, hα⟩ := ih p hp
      refine ⟨α, frameLife_back hα (fun a' ha' => ?_)⟩
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      exact ⟨aW, haW, icpAt_left hcomp _, fun m _ => icpAt_left hcomp m⟩
  | rebEndDeep r hW₀ hr hch hle hreb hW hβ ih =>
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.valid
      intro p hp
      obtain ⟨α, hα⟩ := ih p hp
      refine ⟨α, frameLife_back hα (fun a' ha' => ?_)⟩
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      exact ⟨aW, haW, icpAt_left hcomp _, fun m _ => icpAt_left hcomp m⟩


/-- `StratumLe` gives the records-only premise: `frameLife_reb_like`'s derivation of `β ⊑ α`. -/
theorem rebRecLe_of_stratumLe {W : WRes} {ps rs : List FrameRec} (hT : TW W ps rs) (w₀ : WRes)
    {β : Life} (hβ : StratumLe W β) : RebRecLe W ps w₀ β := by
  intro p hp α h _
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨ζ, e, k, -⟩ := hT.inv.2.1 p hp aW haW
  obtain ⟨t, ht⟩ := lsOf_of_imm k
  refine le_of_not_gt fun hlt => ?_
  have h₁ : t.meet ⊐ α := CellU.sqsupset_of_lsOf ht (AgW.inStratum haW α (hβ α hlt) _ ζ e)
  rw [h.1 aW haW ζ t e ht t.meet t.meet_mem] at h₁
  exact lt_irrefl _ h₁


/-! ### The records proper are roots, and `RebRecLe` from the tags -/

/-- No record proper is a proper sub-record of another. -/
def ProperRoot (ps : List FrameRec) : Prop := ∀ p ∈ ps, ∀ p' ∈ ps, DescR p' p → p' = p

theorem mutAt_of_xpath {A σ : WRes} {q : List Loc} (h : XPath A q σ) {l : Loc}
    (hm : MutAt σ l) : MutAt A l := by
  induction h with
  | nil => exact hm
  | cons e k _ ih => exact MutAt.nest e (by rw [k]; simp) (ih hm)

/-- `immFrame` keeps `ProperRoot`: the new record's location is `own` at the top of `W`, so no
record's escrow is `mut` there (`ag(W)` misses it, `ExIn` would put it there); an old record
proper below the new one would sit at a `mut` cell of the new escrow, `MutAt W`, which `NoMut`
excludes. -/
theorem properRoot_frame {W X Z R : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val}
    {T : VTy} {δ : BoCa.Lifetime.LSub} (hvW : ResU.Valid W) (hTI : TI W ps rs)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (h : ProperRoot ps) :
    ProperRoot (⟨l, v, R, T, δ⟩ :: ps) := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have hWl : W.get l = some (CellU.ownOf v) :=
    (ResU.CompS.get_left_of_ne_imm hW
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
  have hagl : aW.get l = none := ag_none_of_top hvW haW hWl (by simp)
  -- no old record proper is above the new one
  have up : ∀ p' ∈ ps, ¬ Desc p' ⟨l, v, R, T, δ⟩ := by
    rintro p' hp' ⟨q, hq, hpath⟩
    obtain ⟨d', hd', -, -, ζ, eζ, kζ, -⟩ := hpath.last hq
    have hd'R : d' ∈ rs := (hTI.2.2.2.2.2.2.1 d').mpr ⟨p', hp', hd'⟩
    obtain ⟨e, he, hlift⟩ := hTI.exIn hd'R aW haW
    obtain ⟨ζ₁, e₁, -⟩ := exR_cell he eζ (by rw [kζ]; simp)
    obtain ⟨ζ₂, e₂, -⟩ := hlift l ζ₁ e₁
    rw [hagl] at e₂; cases e₂
  -- and no old record proper is below it
  have down : ∀ p ∈ ps, ¬ Desc ⟨l, v, R, T, δ⟩ p := by
    rintro p hp ⟨q, hq, hpath⟩
    obtain ⟨d', ⟨q', hq'⟩, -, -, ζ, eζ, kζ, -⟩ := hpath.last hq
    have hR : MutAt R p.le := mutAt_of_xpath hq'.xpath (MutAt.top eζ kζ)
    have hX' : MutAt X p.le := MutAt.of_compS_right hX hR
    exact hTI.2.2.2.2.2.1.1 p hp (MutAt.of_compS_left hW hX')
  intro p hp p' hp' hd
  rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hp' with rfl | hp'
  · rfl
  · rcases hd.cases with rfl | hd
    · rfl
    · exact (up p' hp' hd).elim
  · rcases hd.cases with h' | hd
    · exact h'.symm
    · exact (down p hp hd).elim
  · exact h p hp p' hp' hd

/-- Every `TWN` world's records proper are roots. -/
theorem TWN.properRoot {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : ProperRoot ps := by
  induction h with
  | empty => intro p hp; exact absurd hp (by simp)
  | immFrame T δ _ hW₀ _ hX hW _ _ _ _ ih =>
      exact properRoot_frame hW₀.valid hW₀.inv hX hW ih
  | immEnd r _ _ _ _ _ _ hps _ ih =>
      exact fun p hp p' hp' hd => ih p ((hps p).mp hp).1 p' ((hps p').mp hp').1 hd
  | alloc _ _ _ _ _ ih => exact ih
  | reb _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih

/-- `tags_above` at `TWN`: a lifetime below the world is below every tag. -/
theorem tags_aboveN {W : WRes} {ps : List FrameRec} {ls : List SRec} {β : Life}
    (hTW : TWN W ps (rsOf ls)) (htag : Tagged W ps ls) (hβ : W.InStratum β) :
    ∀ y ∈ ls, y.2 ⊐ β := by
  intro y hy
  obtain ⟨p, hp, -, hFL⟩ := htag y hy
  obtain ⟨aW, haW⟩ := agW_of_valid hTW.valid
  obtain ⟨ψ, e, k, -, -⟩ := hTW.inv.2.1 p hp aW haW
  obtain ⟨t, ht⟩ := lsOf_of_imm k
  have h₁ : t.meet ⊐ β := CellU.sqsupset_of_lsOf ht (AgW.inStratum haW β hβ _ ψ e)
  rw [hFL.1 aW haW ψ t e ht t.meet t.meet_mem] at h₁
  exact h₁

/-- **`RebRecLe` from the tags.** At a tagged `TWN` world whose tags are all longer than `β`,
every record proper has its frame longer than `β`: the record is tagged (`TI`'s membership), the
tag's record proper is the record itself (`ProperRoot`), and `FrameLife` names one lifetime. -/
theorem rebRecLe_of_tags {W : WRes} {ps : List FrameRec} {ls : List SRec} {β : Life}
    (hT : TWN W ps (rsOf ls)) (htg : Tagged W ps ls) (hβ : ∀ y ∈ ls, y.2 ⊐ β) (w₀ : WRes) :
    RebRecLe W ps w₀ β := by
  intro p hp α hα _
  have hTI := hT.inv
  obtain ⟨t, ht⟩ := mem_rsOf.mp ((hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩)
  obtain ⟨p', hp', hd, hFL⟩ := htg _ ht
  obtain rfl : p' = p := hT.properRoot p hp p' hp' hd
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨ψ, e, k, -, -⟩ := hTI.2.1 p' hp' aW haW
  obtain ⟨s, hs⟩ := lsOf_of_imm k
  have h₁ := hα.1 aW haW ψ s e hs s.meet s.meet_mem
  have h₂ : s.meet = t := hFL.1 aW haW ψ s e hs s.meet s.meet_mem
  have hβt : β ⊏ t := hβ _ ht
  rw [← h₂, h₁] at hβt
  exact le_of_lt hβt

/-- `W′ ∈ Res_β` gives `rebEnd`'s premise at `TWN`; with `rebRecLe_of_stratumLe`, every `TW`
world is a `TWN` world. -/
theorem twN_of_tw {W : WRes} {ps rs : List FrameRec} (h : TW W ps rs) : TWN W ps rs := by
  induction h with
  | empty => exact .empty
  | alloc _ hL hμ hW hv ih => exact .alloc ih hL hμ hW hv
  | immFrame T δ hα _ hadm hX hW hden hW' hv hds ih =>
      exact .immFrame T δ hα ih hadm hX hW hden hW' hv hds
  | reb r x hW₀ hr hle hx hreb hden hβ hW hv ih =>
      exact .reb r x ih hr hle hx hreb hden (rebRecLe_of_stratumLe hW₀ _ hβ) hW hv
  | rebDeep r x hW₀ hr hch hcell hx hreb hden hβ hW hv ih =>
      refine .rebDeep r x ih hr hch hcell hx hreb hden (fun a ha => ?_)
        (rebRecLe_of_stratumLe hW₀ _ (stratumLe_of_inStratum hβ)) hW hv
      obtain ⟨ξ, t, eξ, ht, hy⟩ :=
        (icpAt_agW ha _ _ hcell).ls (CellU.lsOf_immOf _ _ _ _) (LSet.meet_mem _)
      exact ⟨ξ, t, _, eξ, ht, hy,
        ((Life.sqsupset_iff _ _).mp
          (CellU.sqsupset_of_lsOf (CellU.lsOf_immOf _ _ _ _) (hβ _ _ hcell))).le⟩
  | mutFold _ hX hW hW' hv ih => exact .mutFold ih hX hW hW' hv
  | mutUnfold _ hW hX hW' hv ih => exact .mutUnfold ih hW hX hW' hv
  | free _ hW hv ih => exact .free ih hW hv
  | store _ hW hW' hv ih => exact .store ih hW hW' hv
  | immEnd r _ hr hc hX' hW' hv hps hrs ih => exact .immEnd r ih hr hc hX' hW' hv hps hrs
  | rebEnd r _ hr hle hreb hW hβ ih =>
      exact .rebEnd r ih hr hle hreb hW (rebEndRec_of_inStratum hβ)
  | rebEndDeep r _ hr hch hle hreb hW hβ ih =>
      exact .rebEndDeep r ih hr hch hle hreb hW (rebEndRec_of_inStratum hβ)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
