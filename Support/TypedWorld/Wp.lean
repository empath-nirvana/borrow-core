import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Dynamics.Machine
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Entailments
import Support.Model.Flattening
import Support.Model.FlatteningCells
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Singletons
import Support.Model.UpdateFrame
import Support.Model.UpdateSymmetry
import Support.Model.WalkSplitting
import Support.Syntax.Terms
import Support.TypedWorld.Images
import Support.TypedWorld.Invariant
import Support.TypedWorld.Records
import Support.TypedWorld.World

/-!
# Support — TypedWorld — Wp

`[about ours]`.  Stratified record lists and `wp` at a tagged typed world: relevance, the Kripke order, the stratified `Mut` clause, tags, and the frame steps that only regroup.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem Rel.of_compS_left {r : FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Rel r ρ₁) : Rel r ρ := by
  obtain ⟨m, ψ, e, k, hm⟩ := h
  obtain ⟨ψ', e', k', -⟩ := compS_get_left' hc e
  exact ⟨m, ψ', e', k'.trans k, hm⟩

theorem Rel.of_compS_right {r : FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Rel r ρ₂) : Rel r ρ :=
  Rel.of_compS_left (ResU.CompS.comm hc) h

theorem Keeps.left {rs rs' : List FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Keeps rs rs' ρ) : Keeps rs rs' ρ₁ :=
  fun r hr hrel => h r hr (hrel.of_compS_left hc)

theorem Keeps.right {rs rs' : List FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Keeps rs rs' ρ) : Keeps rs rs' ρ₂ :=
  fun r hr hrel => h r hr (hrel.of_compS_right hc)

/-- `Keeps` composes: what `rs″` keeps of `rs′` it keeps of `rs`, if `rs′` kept it. -/
theorem Keeps.trans {rs rs' rs'' : List FrameRec} {ρ : WRes} (h₁ : Keeps rs rs' ρ)
    (h₂ : Keeps rs' rs'' ρ) : Keeps rs rs'' ρ :=
  fun r hr hrel => h₂ r (h₁ r hr hrel) hrel

/-- `Coh` needs only a record relevant to the borrow's cell. -/
theorem coh_keeps {rs rs' : List FrameRec} {l : Loc} {S : Ty} {δ : LSub} {ψ : CellU Loc Val}
    (hk : Keeps rs rs' (ResU.single l ψ)) (hψ : ψ.kind = Kind.imm) (h : Coh rs l S δ) :
    Coh rs' l S δ := by
  rcases h with ⟨r, hr, hm, hT, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
  · exact Or.inl ⟨r, hk r hr ⟨l, ψ, ResU.single_get_self _ _, hψ, Or.inl hm⟩, hm, hT, hag⟩
  · exact Or.inr ⟨r, hk r hr ⟨l, ψ, ResU.single_get_self _ _, hψ, Or.inr ⟨p, S, u, hch⟩⟩,
      p, u, hch, hag⟩

theorem mem_rsOf {ls : List SRec} {r : FrameRec} : r ∈ rsOf ls ↔ ∃ t, (r, t) ∈ ls := by
  simp [rsOf]

/-- Only `imm` cells compose, so a non-`imm` cell of a part is the whole's cell. -/
theorem compS_get_left_nonImm {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) (hk : ψ₁.kind ≠ Kind.imm) :
    ρ.get l = some ψ₁ := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact f
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    exact absurd (by rw [h₁]; rfl) hk

/-- A borrow cell of a part is a borrow cell of the whole, at the same or a shorter
lifetime: `●` unions the lifetime sets of two `imm` cells (`CellU.CompS.at`). -/
theorem CellIn.of_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {b : Life}
    (h : CellIn ρ₁ b) : CellIn ρ b := by
  obtain ⟨m, ψ, e, k, hb⟩ := h
  rcases ResU.Comp.get hc m with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁; exact ⟨m, _, f, k, hb⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    refine ⟨m, χ, f, by rw [CellU.CompS.kind hC]; simp, ?_⟩
    rw [CellU.CompS.at hC]
    exact le_trans inf_le_left hb

theorem CellIn.of_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {b : Life}
    (h : CellIn ρ₂ b) : CellIn ρ b := CellIn.of_left (ResU.CompS.comm hc) h

/-- A borrow cell of a resource in `Res_α` is strictly longer-lived than `α`. -/
theorem CellIn.of_stratum {σ : WRes} {α b : Life} (hσ : σ.InStratum α) (h : CellIn σ b) :
    b ⊐ α := by
  obtain ⟨m, ψ, e, k, hb⟩ := h
  have := hσ m ψ e
  have hat : ψ.at ⊐ α := by
    cases ψ
    · exact absurd rfl k
    · exact this
    · exact this
  exact lt_of_lt_of_le hat hb

/-- A cell at `m` is a borrow cell at its own lifetime. -/
theorem CellIn.single {l : Loc} {ψ : CellU Loc Val} (k : ψ.kind ≠ Kind.own) :
    CellIn (ResU.single l ψ) ψ.at := ⟨l, ψ, ResU.single_get_self _ _, k, le_rfl⟩

theorem Ext.left {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Ext ls ls' ρ) : Ext ls ls' ρ₁ :=
  ⟨h.1.left hc, fun b hb => h.2 b (hb.of_left hc)⟩

theorem Ext.right {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Ext ls ls' ρ) : Ext ls ls' ρ₂ :=
  ⟨h.1.right hc, fun b hb => h.2 b (hb.of_right hc)⟩

theorem Ext.trans {ls ls' ls'' : List SRec} {ρ : WRes} (h₁ : Ext ls ls' ρ)
    (h₂ : Ext ls' ls'' ρ) : Ext ls ls'' ρ :=
  ⟨h₁.1.trans h₂.1, fun b hb x hx => (h₁.2 b hb x hx).trans (h₂.2 b hb x hx)⟩

theorem Ext.refl (ls : List SRec) (ρ : WRes) : Ext ls ls ρ :=
  ⟨fun _ h _ => h, fun _ _ _ _ => Iff.rfl⟩

/-- The stored list is `Ext`-below the current one at the cell's content: `σ ∈ Res_b`, so
every `mut` cell of `σ` is longer-lived than `b`, and `ls₀` and `ls` agree above `b`. -/
theorem ext_stored_current {ls ls₀ : List SRec} {b c : Life} {σ : WRes}
    (hσ : σ.InStratum c) (hbc : b ⊑ c) (hls₀ : ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) :
    Ext ls₀ ls σ := by
  refine ⟨fun r hr _ => ?_, fun b' hb' x hx => ?_⟩
  · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    exact mem_rsOf.mpr ⟨t, ((hls₀ _).mp ht).1⟩
  · have hbb : b' ⊐ b := lt_of_le_of_lt hbc (hb'.of_stratum hσ)
    have hxb : x.2 ⊐ b := lt_trans hbb hx
    exact ⟨fun h => ((hls₀ x).mp h).1, fun h => (hls₀ x).mpr ⟨h, hxb⟩⟩

/-- The stratification fact at a write: every record relevant to the new content is
strictly longer-lived than the cell.  `[about ours]` -/
def LifeBound (ls : List SRec) (σ : WRes) (b : Life) : Prop :=
  ∀ x ∈ ls, Rel x.1 σ → x.2 ⊐ b

/-- At a lifetime shorter than every record, the stratified list is the whole list:
`[TR]` 6.65 picks `α ⊏ γ ⊓ β` after `ρf` is fixed, and the list is finite. -/
theorem strat_fresh {ls : List SRec} {b : Life} (h : ∀ x ∈ ls, x.2 ⊐ b) :
    ∀ x, x ∈ ls ↔ (x ∈ ls ∧ x.2 ⊐ b) :=
  fun x => ⟨fun hx => ⟨hx, h x hx⟩, fun hx => hx.1⟩

/-- A lifetime shorter than every record of a list exists. -/
theorem exists_fresh (ls : List SRec) : ∃ b : Life, ∀ x ∈ ls, x.2 ⊐ b := by
  refine ⟨OrderDual.toDual ((ls.map fun x => OrderDual.ofDual x.2).sum + 1), fun x hx => ?_⟩
  show OrderDual.ofDual x.2 < (ls.map fun x => OrderDual.ofDual x.2).sum + 1
  have : OrderDual.ofDual x.2 ≤ (ls.map fun x => OrderDual.ofDual x.2).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hx)
  omega

/-- Every record proper has a frame lifetime.  `[about ours]` -/
def LinLife (W : WRes) (ps : List FrameRec) : Prop := ∀ p ∈ ps, ∃ α, FrameLife W p α

theorem frameLife_of_ag {W W' : WRes} {p : FrameRec} {α : Life}
    (t : ∀ a, AgW W' a → AgW W a) (h : FrameLife W p α) : FrameLife W' p α :=
  ⟨fun a ha => h.1 a (t a ha), fun a ha => h.2 a (t a ha)⟩

/-- A step whose `ag` loses lifetimes only keeps `FrameLife`. -/
theorem frameLife_back {W W' : WRes} {p : FrameRec} {α : Life} (h : FrameLife W p α)
    (hb : ∀ a', AgW W' a' → ∃ aW, AgW W aW ∧ ICpAt aW a' p.le ∧
      ∀ m, LinLoc p m → ICpAt aW a' m) : FrameLife W' p α := by
  refine ⟨fun a' ha' ζ t e ht y hy => ?_, fun a' ha' m hm ψ s e hs x hx => ?_⟩
  · obtain ⟨aW, haW, h₁, -⟩ := hb a' ha'
    obtain ⟨ζ', t', e', ht', hy'⟩ := (h₁ ζ e).ls ht hy
    exact h.1 aW haW ζ' t' e' ht' y hy'
  · obtain ⟨aW, haW, -, h₂⟩ := hb a' ha'
    obtain ⟨ψ', s', e', hs', hx'⟩ := (h₂ m hm ψ e).ls hs hx
    exact h.2 aW haW m hm ψ' s' e' hs' x hx'

theorem linLife_of_ag {W W' : WRes} {ps : List FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (h : LinLife W ps) : LinLife W' ps := fun p hp => by
  obtain ⟨α, hα⟩ := h p hp
  exact ⟨α, frameLife_of_ag t hα⟩

/-- A reborrow keeps `FrameLife`: a new view is at a lifetime of `ag(W)` or at `β`, and
`β` is below the frame (`W.InStratum β`); the frame's own cell gets no `β`, since the
escrow reborrowed has no `own` or `mut` cell there. -/
theorem frameLife_reb_like {W W' c w₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (hvW : ResU.Valid W)
    (hle : W.get le = some (CellU.immOf s v w₀ hs)) (hreb : ResU.Reb β w₀ c)
    (hW : ResU.CompS W c W') (hβ : W.InStratum β) {p : FrameRec} {α : Life}
    (hex : ∀ ζ : CellU Loc Val, w₀.get p.le = some ζ → ζ.kind = Kind.imm)
    (hcell : ∀ a, AgW W a → ∃ ζ : CellU Loc Val, a.get p.le = some ζ ∧ ζ.kind = Kind.imm)
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
  have hβα : β ⊏ α := by
    obtain ⟨ζ, e, k⟩ := hcell aW haW
    obtain ⟨t, ht⟩ := lsOf_of_imm k
    have h₁ : t.meet ⊐ β := CellU.sqsupset_of_lsOf ht (AgW.inStratum haW β hβ _ ζ e)
    rw [h.1 aW haW ζ t e ht t.meet t.meet_mem] at h₁
    exact h₁
  refine ⟨fun a' ha' ζ t e ht y hy => ?_, fun a' ha' m hm ψ s' e hs' x hx => ?_⟩
  · rcases newls a' ha' p.le ζ t y e ht hy with ⟨ζ', t', e', ht', hy'⟩ | ⟨-, ζ', e', k'⟩
    · exact h.1 aW haW ζ' t' e' ht' y hy'
    · exact absurd (hex ζ' e') k'
  · rcases newls a' ha' m ψ s' x e hs' hx with ⟨ζ', t', e', ht', hx'⟩ | ⟨rfl, -⟩
    · exact h.2 aW haW m hm ζ' t' e' ht' x hx'
    · exact hβα

theorem lsOf_singleton_mem {α y : Life} {v : Val} {R : WRes}
    {h : R.InStratum (LSet.singleton α).join} {t : LSet}
    (ht : (CellU.immOf (LSet.singleton α) v R h).lsOf = some t) (hy : t.mem y) : y = α := by
  rw [CellU.lsOf_immOf] at ht
  cases Option.some.inj ht
  exact hy

/-- `immFrame` keeps `LinLife`: the new record's cell is `imm({α}, …)` and its lineage
carries no view (its cells were in `ex(W)_●`); an old record's cells are not `ℓ`. -/
theorem frameLife_frame {W X Z R W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val}
    {α : Life} (T : Ty) (δ : LSub) {hα : R.InStratum (LSet.singleton α).join}
    (hvW : ResU.Valid W)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R hα)) Z W')
    (hTI : TI W ps rs) :
    FrameLife W' ⟨l, v, R, T, δ⟩ α ∧ ∀ p ∈ ps, ∀ β, FrameLife W p β → FrameLife W' p β := by
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
  obtain ⟨eR, heR, hRW, hRl⟩ := frame_ex hX hW heW
  have Wl : W.get l = some (CellU.ownOf v) :=
    (ResU.CompS.get_left_of_ne_imm hW
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
  have lNone : aW.get l = none := by
    cases e : aW.get l with
    | none => rfl
    | some ζ => exact (ex_ag_disjoint hvW heW haW (ExS.get_of_ne_imm heW Wl (by simp)) e).elim
  -- the walk of `ag(W′)` against `ag(W)`
  have walks : ∀ a', AgW W' a' → ∃ z σc pc rw₀ eR',
      ExS R eR' ∧ ResU.CompR rw₀ z aW ∧ ResU.CompR eR' rw₀ pc ∧
      ResU.CompR (ResU.single l (CellU.immOf (LSet.singleton α) v R hα)) pc σc ∧
      ResU.CompR σc z a' := by
    intro a' ha'
    obtain ⟨eW', aW', rw₀, z, eR', σc, pc, -, haW', -, hrz, heR', -, -, hpc, hcp, hcz⟩ :=
      frame_walks hX hW hW' hvW ha'
    rw [AgW.functional haW' haW] at hrz
    exact ⟨z, σc, pc, rw₀, eR', heR', hrz, hpc, hcp, hcz⟩
  have backI : ∀ a', AgW W' a' → ∀ m, m ≠ l → ICpAt aW a' m := by
    intro a' ha' m hm
    obtain ⟨z, σc, pc, rw₀, eR', heR', hrz, hpc, hcp, hcz⟩ := walks a' ha'
    exact icpAt_comp hcz (icpAt_comp hcp (icpAt_none (single_ne _ hm))
      (icpAt_comp hpc (icpAt_of_immFree (ExS.immFree heR') m) (icpAt_left hrz m)))
      (icpAt_right hrz m)
  refine ⟨⟨fun a' ha' ζ t e ht y hy => ?_, fun a' ha' m hm ψ s e hs x hx => ?_⟩,
    fun p hp β hβ => ?_⟩
  -- the new record
  · obtain ⟨z, σc, pc, rw₀, eR', heR', hrz, hpc, hcp, hcz⟩ := walks a' ha'
    rcases ResU.CompR.lsOf_inv hcz e ht hy with ⟨ξ, t₁, e₁, ht₁, hy₁⟩ | ⟨ξ, -, e₁, -⟩
    · rcases ResU.CompR.lsOf_inv hcp e₁ ht₁ hy₁ with ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩ |
          ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩
      · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₂
        exact lsOf_singleton_mem ht₂ hy₂
      · rcases ResU.CompR.lsOf_inv hpc e₂ ht₂ hy₂ with ⟨ξ₃, t₃, e₃, ht₃, -⟩ | ⟨ξ₃, -, e₃, -⟩
        · exact absurd (CellU.kind_of_lsOf ht₃) (ExS.immFree heR' _ _ e₃)
        · obtain ⟨_, e₄⟩ := comp_some hrz e₃
          rw [lNone] at e₄; cases e₄
    · obtain ⟨_, e₄⟩ := comp_some_r hrz e₁
      rw [lNone] at e₄; cases e₄
  · exfalso
    obtain ⟨d, ⟨q, hq⟩, ζ, eζ, kζ⟩ := hm
    have eRm : eR.get m = some ζ := xpath_ex heR hq.xpath eζ kζ
    have hml : m ≠ l := fun e' => by rw [e', hRl] at eRm; cases eRm
    have aNone : aW.get m = none := by
      cases ea : aW.get m with
      | none => rfl
      | some ξ => exact (ex_ag_disjoint hvW heW haW (hRW m ζ eRm kζ) ea).elim
    obtain ⟨ξ, eξ, -⟩ := backI a' ha' m hml ψ e (CellU.kind_of_lsOf hs)
    rw [aNone] at eξ; cases eξ
  -- an old record
  · have hmem := hTI.2.2.2.2.2.2.1
    refine frameLife_back hβ (fun a' ha' => ⟨aW, haW, backI a' ha' p.le (fun e => ?_),
      fun m hm => backI a' ha' m (fun e => ?_)⟩)
    · obtain ⟨ψ, eψ, -⟩ := hTI.2.1 p hp aW haW
      rw [e, lNone] at eψ; cases eψ
    · obtain ⟨d, hd, ζ, eζ, kζ⟩ := hm
      have hdr : d ∈ rs := (hmem d).mpr ⟨p, hp, hd⟩
      obtain ⟨ξ, eξ⟩ := exIn_support (hTI.exIn hdr) eζ kζ aW haW
      rw [e, lNone] at eξ; cases eξ

theorem linLife_frame {W X Z R W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val}
    {α : Life} {T : Ty} {δ : LSub} {hα : R.InStratum (LSet.singleton α).join}
    (hvW : ResU.Valid W)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R hα)) Z W')
    (hTI : TI W ps rs) (h : LinLife W ps) :
    LinLife W' (⟨l, v, R, T, δ⟩ :: ps) := by
  obtain ⟨hnew, hold⟩ := frameLife_frame T δ hvW hX hW hW' hTI
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨α, hnew⟩
  · obtain ⟨β, hβ⟩ := h p hp
    exact ⟨β, hold p hp β hβ⟩

/-- Every `TW` world satisfies `LinLife`. -/
theorem TW.linLife {W : WRes} {ps rs : List FrameRec} (h : TW W ps rs) : LinLife W ps := by
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
      refine ⟨α, frameLife_reb_like hW₀.valid hle hreb hW hβ (fun ζ e => ?_)
        (fun a ha => by obtain ⟨ψ, e, k, -⟩ := hTI.2.1 p hp a ha; exact ⟨ψ, e, k⟩) hα⟩
      rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
      · exact (hTI.2.2.2.1 p hpR r hr u e).elim
      · exact CellU.kind_immOf _ _ _ _
      · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hle (MutAt.top e (by simp)))).elim
  | @rebDeep W W' c ps rs r p₀ l₁ S₀ u₀ s w₀ hs β x hW₀ hr hch hcell hx hreb hden hβ hW hv
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
      refine ⟨α, frameLife_reb_like hvW hcell hreb hW hβ (fun ζ e => ?_)
        (fun a ha => by obtain ⟨ψ, e, k, -⟩ := hTI.2.1 p hp a ha; exact ⟨ψ, e, k⟩) hα⟩
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

/-- A cell a record `x` is relevant through, other than the frame's own cell, is a lineage
location of every record proper whose lineage holds `x`. -/
theorem linLoc_of_rel {p x : FrameRec} (hpx : DescR p x) {m : Loc}
    (hm : m = x.le ∨ ∃ q S u, Chain x.R x.T x.v q m S u) :
    (x = p ∧ m = p.le) ∨ LinLoc p m := by
  rcases hm with rfl | ⟨q, S, u, hch⟩
  · rcases hpx.cases with rfl | ⟨q, hq, hqq⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨d', hd', -, -, ζ, eζ, kζ, -⟩ := hqq.last hq
      exact Or.inr ⟨d', hd', ζ, eζ, by rw [kζ]; simp⟩
  · exact Or.inr ⟨x, hpx, _, hch.own, by simp⟩

/-- A part of `W` has its `imm` cells' lifetimes in `ag(W)`. -/
theorem ag_ls_of_le {σ W aW : WRes} (hle : ResU.Le σ W) (haW : AgW W aW) {m : Loc}
    {ψ : CellU Loc Val} (e : σ.get m = some ψ) {s : LSet} (hs : ψ.lsOf = some s) {y : Life}
    (hy : s.mem y) : ∃ (ζ : CellU Loc Val) (t : LSet), aW.get m = some ζ ∧ ζ.lsOf = some t ∧ t.mem y := by
  obtain ⟨τ, hτ⟩ := hle
  exact (icp_trans (icpAt_left (ResU.CompS.toCompR hτ) m ψ e) (icpAt_agW haW m)).ls hs hy

/-- `LifeBound` at a write: content in `Res_b` that is a part of the
world is relevant only to records tagged `⊐ b`. -/
theorem lifeBound_of_tagged {W : WRes} {ps : List FrameRec} {ls : List SRec} {σ : WRes}
    {b : Life} (hvW : ResU.Valid W) (htag : Tagged W ps ls) (hle : ResU.Le σ W)
    (hσ : σ.InStratum b) : LifeBound ls σ b := by
  intro x hx hrel
  obtain ⟨p, -, hpx, hFL⟩ := htag x hx
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨m, ψ, e, k, hm⟩ := hrel
  obtain ⟨s, hs'⟩ := lsOf_of_imm k
  have hlow : s.meet ⊐ b := CellU.sqsupset_of_lsOf hs' (hσ m ψ e)
  obtain ⟨ζ, t, eζ, ht, hmt⟩ := ag_ls_of_le hle haW e hs' s.meet_mem
  rcases linLoc_of_rel hpx hm with ⟨-, rfl⟩ | hL
  · have := hFL.1 aW haW ζ t eζ ht s.meet hmt
    rw [this] at hlow; exact hlow
  · exact lt_trans hlow (hFL.2 aW haW m hL ζ t eζ ht s.meet hmt)

theorem tagged_of_frameLife {W W' : WRes} {ps : List FrameRec} {ls : List SRec}
    (t : ∀ p α, FrameLife W p α → FrameLife W' p α) (h : Tagged W ps ls) : Tagged W' ps ls :=
  fun x hx => by
    obtain ⟨p, hp, hd, hf⟩ := h x hx
    exact ⟨p, hp, hd, t p x.2 hf⟩

theorem tagged_of_ag {W W' : WRes} {ps : List FrameRec} {ls : List SRec}
    (t : ∀ a, AgW W' a → AgW W a) (h : Tagged W ps ls) : Tagged W' ps ls :=
  tagged_of_frameLife (fun _ _ hf => frameLife_of_ag t hf) h

/-- Same members give `Ext` at every resource. -/
theorem ext_of_same {ls ls' : List SRec} (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (ρ : WRes) :
    Ext ls ls' ρ :=
  ⟨fun r hr _ => by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr
      exact mem_rsOf.mpr ⟨t, (h _).mpr ht⟩,
    fun _ _ x _ => (h x).symm⟩

/-- `(P̂ ─⋆ Q̂)` at every list with the same members.  `[about ours: 6.146's wand at the lists
a run can return]` -/
def wandAllTS (ls : List SRec) (P Q : List SRec → Val → WProp) : WProp :=
  fun ρ => ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v, wand (P ls' v) (Q ls' v) ρ

/-- `ls′` is `ls` with records at `α` added.  `[about ours]` -/
def AddAt (ls ls' : List SRec) (α : Life) : Prop :=
  (∀ x ∈ ls, x ∈ ls') ∧ ∀ x ∈ ls', x ∉ ls → x.2 = α

/-- Adding records at `α` is `Ext` at a resource in `Res_α` (6.64's entry). -/
theorem ext_add {ls ls' : List SRec} {α : Life} (h : AddAt ls ls' α) {ρ : WRes}
    (hρ : ρ.InStratum α) : Ext ls ls' ρ := by
  refine ⟨fun r hr _ => ?_, fun b hb x hx => ⟨h.1 x, fun h' => ?_⟩⟩
  · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    exact mem_rsOf.mpr ⟨t, h.1 _ ht⟩
  · by_contra hn
    have e := h.2 x h' hn
    rw [e] at hx
    exact lt_irrefl _ (lt_trans hx (hb.of_stratum hρ))

/-- Dropping records at `α` is `Ext` at a resource in `Res_α` none of whose relevant records
is dropped (6.64's exit). -/
theorem ext_drop {ls ls' : List SRec} {α : Life} (h : AddAt ls ls' α) {ρ : WRes}
    (hρ : ρ.InStratum α) (hk : ∀ r ∈ rsOf ls', Rel r ρ → r ∈ rsOf ls) : Ext ls' ls ρ := by
  refine ⟨hk, fun b hb x hx => ⟨fun h' => ?_, h.1 x⟩⟩
  by_contra hn
  have e := h.2 x h' hn
  rw [e] at hx
  exact lt_irrefl _ (lt_trans hx (hb.of_stratum hρ))

/-- A resource in `Res_α`, whose `imm` cells are in `ag(W)` and none at `p.le`, holds no view
at `p`'s lineage — `[TR]` 6.52's *"there are no borrows … at any lifetime shorter than α"*
read through `FrameLife`. -/
theorem not_rel_lineage {W : WRes} {p : FrameRec} {α : Life} (hFL : FrameLife W p α)
    {aW : WRes} (haW : AgW W aW) {ρ : WRes} (hicp : ∀ m, ICpAt aW ρ m)
    (hα : ρ.InStratum α) (hl : ∀ ψ : CellU Loc Val, ρ.get p.le = some ψ → ψ.kind ≠ Kind.imm)
    {x : FrameRec} (hpx : DescR p x) : ¬ Rel x ρ := by
  rintro ⟨m, ψ, e, k, hm⟩
  obtain ⟨s, hs⟩ := lsOf_of_imm k
  have hlow : s.meet ⊐ α := CellU.sqsupset_of_lsOf hs (hα m ψ e)
  obtain ⟨ζ, t, eζ, ht, hmt⟩ := (hicp m ψ e).ls hs s.meet_mem
  rcases linLoc_of_rel hpx hm with ⟨-, rfl⟩ | hL
  · exact hl ψ e k
  · exact lt_asymm hlow (hFL.2 aW haW m hL ζ t eζ ht s.meet hmt)

/-- `FrameLife` names the lifetime of a record's cell. -/
theorem frameLife_eq {W : WRes} {p : FrameRec} {α β : Life} (hFL : FrameLife W p α)
    {aW : WRes} (haW : AgW W aW) {ζ : CellU Loc Val} {t : LSet} (e : aW.get p.le = some ζ)
    (ht : ζ.lsOf = some t) (hβ : t.mem β) : β = α :=
  hFL.1 aW haW ζ t e ht β hβ

/-- The tagged list after `immFrame`. -/
def frameList (p : FrameRec) (ds : List FrameRec) (α : Life) (ls : List SRec) : List SRec :=
  (p, α) :: (ds.map (fun d => (d, α)) ++ ls)

theorem rsOf_frameList (p : FrameRec) (ds : List FrameRec) (α : Life) (ls : List SRec) :
    rsOf (frameList p ds α ls) = p :: (ds ++ rsOf ls) := by
  simp [frameList, rsOf, Function.comp_def]

theorem addAt_frameList (p : FrameRec) (ds : List FrameRec) (α : Life) (ls : List SRec) :
    AddAt ls (frameList p ds α ls) α := by
  refine ⟨fun x hx => by simp [frameList, hx], fun x hx hn => ?_⟩
  simp only [frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
  rcases hx with rfl | ⟨d, -, rfl⟩ | hx
  · rfl
  · rfl
  · exact absurd hx hn

/-! ### Lemma 6.136 (wp-val) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.136 (`wp-val`) at `wpTS`. -/
theorem wpTS_val (ls : List SRec) (v : Val) (Q : List SRec → Val → WProp) :
    Entails (Q ls v) (wpTS ls (.val v) Q) := by
  intro ρ hQ ρf fρ ps hf hc hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  exact ⟨ρ, PMap.empty, fρ, fρ, ρ, v, μ, μ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), hμ,
    ResU.comp_empty_right fρ, hμ, Steps.refl _ _, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-! ### Lemma 6.137 (wp1) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- One deterministic head step in front of a `wpTS` (6.137–6.140). -/
theorem wpTS_head {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') (ls : List SRec)
    (Q : List SRec → Val → WProp) : Entails (wpTS ls e' Q) (wpTS ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇,
    .more (Step1.head (h μ)) h₈, h₉, hA, hB, hT', htg', hps, hls, hC⟩

/-- `[TR]` 6.137 (`wp1`) at `wpTS`. -/
theorem wpTS_1 (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls e Q) (wpTS ls (.seq (.val .unit) e) Q) :=
  wpTS_head (fun μ => .seq μ e) ls Q

/-! ### Lemma 6.138 (wp⊗) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.138 (`wp⊗`) at `wpTS`. -/
theorem wpTS_tensor (ls : List SRec) (v₁ v₂ : Val) (e : Expr) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁) Q)
      (wpTS ls (.letpair (.val (.pair v₁ v₂)) e) Q) :=
  wpTS_head (fun μ => .letpair μ v₁ v₂ e) ls Q

/-! ### Lemma 6.139 (wp⊕) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.139 (`wp⊕`) at `wpTS`, both summands. -/
theorem wpTS_sum₁ (ls : List SRec) (v : Val) (e₁ e₂ : Expr) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (e₁.subst 0 v) Q) (wpTS ls (.case (.val (.inj₁ v)) e₁ e₂) Q) :=
  wpTS_head (fun μ => .case₁ μ v e₁ e₂) ls Q

theorem wpTS_sum₂ (ls : List SRec) (v : Val) (e₁ e₂ : Expr) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (e₂.subst 0 v) Q) (wpTS ls (.case (.val (.inj₂ v)) e₁ e₂) Q) :=
  wpTS_head (fun μ => .case₂ μ v e₁ e₂) ls Q

/-! ### Lemma 6.140 (wp⊸) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.140 (`wp⊸`) at `wpTS`. -/
theorem wpTS_lolli (ls : List SRec) (b : Expr) (v : Val) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (b.subst 0 v) Q) (wpTS ls (.app (.val (.lam b)) (.val v)) Q) :=
  wpTS_head (fun μ => .beta μ b v) ls Q

/-! ### Lemma 6.141 (wp-alloc) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.141 (`wp-alloc`) at `wpTS`: the post-world is `TW.alloc`'s. -/
theorem wpTS_alloc (ls : List SRec) (v : Val) (Q : List SRec → Val → WProp) :
    Entails (all fun l : BoCa.Loc => wand (ptoOwn l v) (Q ls (.loc l)))
      (wpTS ls (.app (.val (.prim .alloc)) (.val v)) Q) := by
  intro ρ h ρf σ ps hf hσ hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨l, hl⟩ := PMap.exists_fresh loc_infinite τ
  have hμl : μ l = none := (lower_eq_none_iff hval).mpr hl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  have hT' : TW σ' ps (rsOf ls) := TW.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x)
  exact ⟨x, PMap.empty, σ', σ', x, .loc l, μ, BoCa.BoLo.Heap.upd μ l v, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hμ, ResU.comp_empty_right σ', hlow',
    Steps.one (Step1.head (Head.alloc μ v l hμl)), ResU.comp_empty_right x,
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2,
    noOwn_empty, hT', tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, h l _ x rfl hx⟩

/-! ### Lemma 6.142 (wp-free) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.142 (`wp-free`) at `wpTS`: the post-world is `TW.free`'s. -/
theorem wpTS_free (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoOwn l v) (Q ls v))
      (wpTS ls (.app (.val (.prim .free)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hQ⟩ ρf σ ps hf hσ hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  have hdel : BoCa.BoLo.Heap.del μ l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hnone]
    · rw [BoCa.BoLo.Heap.del_other e, hupd, BoCa.BoLo.Heap.upd_other e]
  have hT' : TW σ₂ ps (rsOf ls) :=
    TW.free hT (ResU.CompS.comm hσ₂σ) (hash_valid_comp h₂ hσ₂)
  refine ⟨ρ₂, PMap.empty, σ₂, σ₂, ρ₂, v, μ, μ₂, ps, ls,
    ResU.hash_symm h₂, hσ₂,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp h₂ hσ₂)),
    hμ, ResU.comp_empty_right σ₂, hlow₂, ?_, ResU.comp_empty_right ρ₂,
    (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm,
    noOwn_empty, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩
  rw [← hdel]
  exact Steps.one (Step1.head (Head.free μ l v hlv))

/-! ### Lemma 6.143 (wp-load) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.143 (`wp-load`) at `wpTS`. -/
theorem wpTS_load (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoOwn l v) (wand (ptoOwn l v) (Q ls v)))
      (wpTS ls (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf σ ps hf hσ hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  have hρ : ρ.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_right_none hcρ (ResU.compatS_single_own hcρ.1),
      ResU.single_get_self]
  have hlv : μ l = some v :=
    lower_get_own hμ (by
      rw [ResU.Comp.get_of_left_none hσ (get_eq_none_of_compatS_own
        (ResU.CompatS.symm hf.1) hρ)]
      exact hρ)
  exact ⟨ρ, PMap.empty, σ, σ, ρ, v, μ, μ, ps, ls,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hσ)),
    hμ, ResU.comp_empty_right σ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hwand _ ρ rfl (ResU.CompS.comm hcρ)⟩

/-! ### Lemma 6.144 (wp-load-I) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.144 (`wp-load-I`) at `wpTS`. -/
theorem wpTS_load_I (ls : List SRec) (l : BoCa.Loc) (α : Life) (P : Val → WProp)
    (Q : List SRec → Val → WProp) :
    Entails
      (sep (ptoImm l α P)
        (all fun v =>
          wand (ptoImm l α (fun v' => sep (pure (v = v')) (P v))) (Q ls v)))
      (wpTS ls (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρR, hcρ, ⟨s, v, σ, hs, rfl, hP, hα⟩, hR⟩ ρf τ ps hf hτ hT htg
  have hcell : ptoImm l α (fun v' => sep (pure (v = v')) (P v))
      (ResU.single l (CellU.immOf s v σ hs)) :=
    ⟨s, v, σ, hs, rfl, (pure_sep_biEntails rfl (P v)).2 σ hP, hα⟩
  have hQ : Q ls v ρ := hR v _ ρ hcell (ResU.CompS.comm hcρ)
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hτ
  obtain ⟨χ, hχ, heχ⟩ := compS_get_erase hcρ (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some v := by
    rw [lower_get hμ hχ', heχ', heχ]
    rfl
  exact ⟨ρ, PMap.empty, τ, τ, ρ, v, μ, μ, ps, ls,
    ResU.hash_symm hf, hτ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hτ)),
    hμ, ResU.comp_empty_right τ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-! ### Lemma 6.145 (wp-store) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.145 (`wp-store`) at `wpTS`: the post-world is `TW.store`'s. -/
theorem wpTS_store (ls : List SRec) (l : BoCa.Loc) (v₁ v₂ : Val) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoOwn l v₁) (wand (ptoOwn l v₂) (Q ls .unit)))
      (wpTS ls (.app (.val (.storeV (.loc l))) (.val v₂)) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf σ ps hf hσ hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₁)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ₂ (ResU.single l (CellU.ownOf v₂))).mpr
    (compatS_single_of_get_none (ResU.compatS_single_own hcρ.1))
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ₂ hlow₂ hnone hx
  have hstep : BoCa.BoLo.Heap.upd μ l v₂ = BoCa.BoLo.Heap.upd μ₂ l v₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.upd_same, BoCa.BoLo.Heap.upd_same]
    · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e, hupd,
        BoCa.BoLo.Heap.upd_other e]
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₂)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ₂
  have hT' : TW σ' ps (rsOf ls) :=
    TW.store hT (ResU.CompS.comm hσ₂σ) (ResU.CompS.comm hyσ') (hash_valid_comp hfx hσ'x)
  refine ⟨x, PMap.empty, σ', σ', x, .unit, μ, BoCa.BoLo.Heap.upd μ₂ l v₂, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hμ, ResU.comp_empty_right σ', hlow', ?_, ResU.comp_empty_right x, ?_,
    noOwn_empty, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr
      ((own_cell_ag (ResU.CompS.comm hyσ') a).mp ha)) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hwand _ x rfl hx⟩
  · rw [← hstep]
    exact Steps.one (Step1.head (Head.store μ l v₂ v₁ hlv))
  · exact ResU.UpdV.trans
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm
      (updV_compS_own hx (hash_valid h₂).2 (hash_valid hfx).2)

/-! ### Lemma 6.135 (wp-bind) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.135 (`wp-bind`) at `wpTS`: the continuation runs at the intermediate
typed world with the list the first run returned. -/
theorem wpTS_bind (K : Kont) (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls e fun ls' v => wpTS ls' (K.plug (.val v)) Q) (wpTS ls (K.plug e) Q) := by
  intro ρ hw ρf fρ ps hf h₄ hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps', hls', hC⟩ := hw ρf fρ ps hf h₄ hT htg
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  obtain ⟨ρ'', ρpp, Y'', Y''p, π'', v', ν, ν', ps'', ls'', k₁, k₂, k₃, k₅, k₆, k₇, k₈,
    k₉, kA, kB, kT, ktg, kps, kls, kC⟩ := hC z fρ'p ps' hz hzY hT' htg'
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁)
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  obtain ⟨ZZ, hZZ, hZF⟩ := (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  have hν : ν = μ' := ResU.Lower.functional k₅ h₇
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  refine ⟨ρ'', ZZ, F, Y''p, Yn, v', μ, ν', ps'', ls'', ResU.hash_symm hfρ'', hF, hZF,
    h₅, hFZ, k₇, (h₈.plug K).trans (hν ▸ k₈), hρ''Z, ?_,
    noOwn_compS hZZ' hB kB, kT, ktg, fun p => (kps p).trans (hps' p),
    fun x => (kls x).trans (hls' x), kC⟩
  exact ResU.UpdV.trans hA
    (updV_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ kA)

/-! ### Lemma 6.146 (wp-ramify) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.146 (`wp-ramify`) at `wpTS`. -/
theorem wpTS_ramify (ls : List SRec) (e : Expr) (P Q : List SRec → Val → WProp) :
    Entails (sep (wpTS ls e P) (wandAllTS ls P Q)) (wpTS ls e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hwp, hwand⟩ ρf fρ ps hf hc hT htg
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  obtain ⟨ρ', ρp, Y', Y'p, π', v, μ, μ', ps', ls', g₁, g₂, g₃, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gT, gtg, gps, gls, gC⟩ := hwp y fρ ps hy₁ hyfρ hT htg
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρ₂ ρf).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W ρf := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  refine ⟨W, ρp, Y', Y'p, πn, v, μ, μ', ps', ls', hWf, hfW, g₃, g₅, g₆, g₇, g₈,
    hWπ, ?_, gB, gT, gtg, gps, gls, hwand ls' gls v ρ' W gC hW⟩
  exact updV_frame (ResU.CompS.comm hcρ) hπn
    ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, (hash_valid hf).2⟩ h₂π gA

/-! ### Lemma 6.147 (wp[]) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.147 (`wp-box`) at `wpTS`. -/
theorem wpTS_box (ls : List SRec) (α : Life) (e : Expr) (Q : List SRec → Val → WProp) :
    Entails (box α (wpTS ls e Q)) (wpTS ls e fun ls' v => box α (Q ls' v)) := by
  rintro ρ ⟨hw, hout⟩ ρf fρ ps hf hc hT htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hT', htg', hps, hls, hC, ((outlives_comp h₉ α).mp (updV_outlives hout hA)).1⟩

/-! ### Lemma 6.148 (wp-M-forget) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- A frame with no owned cell passes through a `wpTS` run (6.148/6.149's shared argument). -/
theorem wpTS_frame_noOwn {R : WProp} (hR : ∀ ρ, R ρ → NoOwn ρ) (ls : List SRec) (e : Expr)
    (Q : List SRec → Val → WProp) : Entails (sep R (wpTS ls e Q)) (wpTS ls e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hR₁, hwp⟩ ρf fρ ps hf hc hT htg
  obtain ⟨y, hy, hy₂⟩ := (hash_shift ρf ρ₁ ρ₂).mp ⟨ρ, hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' hcρ hc
  cases ResU.CompS.functional hy' hy
  obtain ⟨ρ'', ρp, Y'', Y''p, π', v', μ, μ', ps', ls', g₁, g₂, g₃, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gT, gtg, gps, gls, gC⟩ := hwp y fρ ps hy₂ hyfρ hT htg
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hy (ResU.hash_symm g₁)
  obtain ⟨F, hF, hFv⟩ := hfρ''.2
  obtain ⟨F', hF', hFρ₁⟩ := compS_exch hy g₂
  cases ResU.CompS.functional hF' hF
  obtain ⟨Z, hZ, hZF⟩ :=
    (hash_shift ρp ρ₁ F).mp ⟨Y'', ResU.CompS.comm hFρ₁, g₃⟩
  obtain ⟨Z', hZ', hFZ⟩ := compS_reassoc hFρ₁ g₆
  cases ResU.CompS.functional (ResU.CompS.comm hZ') hZ
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hy g₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm g₃)
  obtain ⟨π'', hπ'', h₁π⟩ := (hash_shift ρ₁ ρ'' ρp).mpr ⟨d, hd, hdp⟩
  cases ResU.CompS.functional hπ'' g₉
  obtain ⟨πn, hπn, -⟩ := h₁π.2
  obtain ⟨ac, hac, hπZ⟩ := compS_lcomm g₉ hπn
  cases ResU.CompS.functional (ResU.CompS.comm hac) hZ
  refine ⟨ρ'', Z, F, Y''p, πn, v', μ, μ', ps', ls', ResU.hash_symm hfρ'', hF, hZF,
    g₅, hFZ, g₇, g₈, hπZ, ?_, noOwn_compS hZ gB (hR ρ₁ hR₁), gT, gtg, gps, gls, gC⟩
  exact updV_frame hcρ hπn ⟨hcρ.1, ρ, hcρ, (hash_valid hf).2⟩ h₁π gA

/-- `[TR]` 6.148 (`wp-M-forget`) at `wpTS`. -/
theorem wpTS_M_forget (ls : List SRec) (l : BoCa.Loc) (α : Life) (P : Val → WProp)
    (e : Expr) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoMut l α P) (wpTS ls e Q)) (wpTS ls e Q) := by
  refine wpTS_frame_noOwn (fun ρ h => ?_) ls e Q
  obtain ⟨b, v, σ, hs, R, hw, hα, rfl, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-! ### Lemma 6.149 (wp-I-forget) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` 6.149 (`wp-I-forget`) at `wpTS`. -/
theorem wpTS_I_forget (ls : List SRec) (l : BoCa.Loc) (α : Life) (P : Val → WProp)
    (e : Expr) (Q : List SRec → Val → WProp) :
    Entails (sep (ptoImm l α P) (wpTS ls e Q)) (wpTS ls e Q) := by
  refine wpTS_frame_noOwn (fun ρ h => ?_) ls e Q
  obtain ⟨s, v, σ, hs, rfl, -, -⟩ := h
  exact ResU.restrict_single_other (by simp)

end BoCa.Fig16.LogRel.Typed

end
