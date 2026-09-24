import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Dynamics.Machine
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Notation
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.ReborrowRule
import Support.Model.Strata
import Support.Model.Subtraction
import Support.Model.SubtractionKeep
import Support.Model.UpdateFrame
import Support.TypedWorld.Images
import Support.TypedWorld.Invariant
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.RelationFacts
import Support.TypedWorld.World
import Support.TypedWorld.Wp

/-!
# Support — TypedWorld — Reborrow

`[about ours]`.  `[TR]` Theorem 6.150 at `wpTS`: the chooser `RebChooseTW` that replaces `RebEscrow`, and the rule.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A reborrow keeps `Tagged` — `TW.linLife`'s `reb` case at the tag's lifetime. -/
theorem tagged_reb {W W' c : WRes} {ps rs : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {β : Life} {hs : r.R.InStratum s.join}
    (hW₀ : TW W ps rs) (hr : r ∈ rs) (hle : W.get le = some (CellU.immOf s r.v r.R hs))
    (hreb : ResU.Reb β r.R c) (hβ : W.InStratum β) (hW : ResU.CompS W c W')
    (htag : Tagged W ps ls) : Tagged W' ps ls := by
  have hTI := hW₀.inv
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
  refine ⟨p, hp, hd, frameLife_reb_like hW₀.valid hle hreb hW hβ (fun ζ e => ?_)
    (fun a ha => by obtain ⟨ψ, e, k, -⟩ := hTI.2.1 p hp a ha; exact ⟨ψ, e, k⟩) hα⟩
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
  · exact (hTI.2.2.2.1 p hpR r hr u e).elim
  · exact CellU.kind_immOf _ _ _ _
  · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hle (MutAt.top e (by simp)))).elim

/-- …and a reborrow at a chain view — `TW.linLife`'s `rebDeep` case. -/
theorem tagged_rebDeep {W W' c : WRes} {ps rs : List FrameRec} {ls : List SRec} {r : FrameRec}
    {p₀ : Option Loc} {l₁ : Loc} {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes}
    {hs : w₀.InStratum s.join} {β : Life}
    (hW₀ : TW W ps rs) (hr : r ∈ rs) (hch : Chain r.R r.T r.v p₀ l₁ S₀ u₀)
    (hcell : W.get l₁ = some (CellU.immOf s u₀ w₀ hs))
    (hreb : ResU.Reb β w₀ c) (hβ : W.InStratum β) (hW : ResU.CompS W c W')
    (htag : Tagged W ps ls) : Tagged W' ps ls := by
  have hTI := hW₀.inv
  have hvW := hW₀.valid
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  obtain ⟨-, -, hw₀own, -, -⟩ :=
    hTI.1.1 r hr p₀ l₁ S₀ u₀ hch aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀own
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
  refine ⟨p, hp, hd, frameLife_reb_like hvW hcell hreb hW hβ (fun ζ e => ?_)
    (fun a ha => by obtain ⟨ψ, e, k, -⟩ := hTI.2.1 p hp a ha; exact ⟨ψ, e, k⟩) hα⟩
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
  · exact (hTI.2.2.2.1 p hpR r hr u (hw₀own _ u e)).elim
  · exact CellU.kind_immOf _ _ _ _
  · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hcell (MutAt.top e (by simp)))).elim

/-- A reborrow's end keeps `Tagged` — `TW.linLife`'s `rebEnd` case: `ag` only loses
lifetimes. -/
theorem tagged_rebEnd {W W' D : WRes} {ps rs : List FrameRec} {ls : List SRec}
    (hW₀ : TW W ps rs) (hW : ResU.CompS W' D W) (htag : Tagged W ps ls) : Tagged W' ps ls := by
  obtain ⟨aW, haW⟩ := agW_of_valid hW₀.valid
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  refine ⟨p, hp, hd, frameLife_back hα (fun a' ha' => ?_)⟩
  obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
  rw [AgW.functional ha'' ha'] at hcomp
  exact ⟨aW, haW, icpAt_left hcomp _, fun m _ => icpAt_left hcomp m⟩

/-- 6.150's reborrow, chosen at the tagged world.  Given the handed `χ₀ ∈ reb_β(ρ′)` with
`P̂₀(β)(w)(χ₀)` (H16/H17), a world `W` holding the cell `ℓ ↦ imm(s̄, w, ρ′)` with frame `F`,
and `β` below `W`: some `χ ∈ reb_β(ρ′)` with `P̂(β)(w)(χ)`, the two inputs `[TR]` 6.55 adds
(`ag(χ)` defined and `EscrowAgree` at `F` and at the cell), the world `W ● χ` typed (entry), and
every world `W″` with `W″ ● χ|dom(ρ′|mut,own)` typed, holding the cell and in `Res_β`, typed
(exit).  `[about ours: our chooser at the typed world]` -/
def RebChooseTW (ls : List SRec) (l : Loc) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) : Prop :=
  ∀ (W F χ₀ σ : WRes) (ps : List FrameRec) (β : Life) (w : Val) (s : LSet)
    (hs : σ.InStratum s.join),
    TW W ps (rsOf ls) → Tagged W ps ls → W.InStratum β →
    ResU.CompS (ResU.single l (CellU.immOf s w σ hs)) F W → R w σ →
    ResU.Reb β σ χ₀ → P₀ β w χ₀ →
    ∃ χ, ResU.Reb β σ χ ∧ P β w χ ∧ (∃ A, AgW χ A) ∧
      (∀ a, AgW F a → EscrowAgree σ χ a) ∧
      (∀ a, AgW (ResU.single l (CellU.immOf s w σ hs)) a → EscrowAgree σ χ a) ∧
      (∀ W', ResU.CompS W χ W' → ResU.Valid W' → TW W' ps (rsOf ls) ∧ Tagged W' ps ls) ∧
      (∀ (ps' : List FrameRec) (ls' : List SRec) (Wp W'' : WRes),
        (∀ p, p ∈ ps' ↔ p ∈ ps) → (∀ x, x ∈ ls' ↔ x ∈ ls) →
        TW Wp ps' (rsOf ls') → Tagged Wp ps' ls' →
        (∃ (s' : LSet) (hs' : σ.InStratum s'.join), W''.get l = some (CellU.immOf s' w σ hs')) →
        ResU.CompS W'' (χ.restrictDom σ.exclPart) Wp → W''.InStratum β →
        TW W'' ps' (rsOf ls') ∧ Tagged W'' ps' ls')

/-- `RebChooseTW` at a record's cell, at `𝒱X`.  The cell's value and escrow are the
record's (`LeInvW`); the handed shaped image is typed at `𝒱X` by `image_vX_of_shape` (6.131 at
`𝒱X`) from the world's `WitLB`, the tag bound and `Coh`; `rebChooseO_top_tw` chooses;
entry is `TW.reb`, exit `TW.rebEnd`.  The payload input `R` is the program's own: the escrow
observable at the record's type.  `[about ours: our chooser, at the program's relation]` -/
theorem rebChooseTW_top {ls : List SRec} {r : FrameRec} {x : LifeVar} {δ' : LSub}
    (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ) (hx : ¬ LFree x r.T) :
    RebChooseTW ls r.le (fun w σ => vX wpTS false r.T ls δ' w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vX wpTS true (r.T.immReborrow (.var x)) ls (δ'.extend x β) w χ) := by
  intro W F χ₀ σ ps β w s hs hT htag hβ hW hR hreb₀ hP₀
  -- the cell's value and escrow are the record's
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨φ₁, eφ₁, -, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  obtain ⟨φ, eφ, -, rφ, wφ⟩ := hT.inv.leInvW r hr aW haW
  rw [eφ₁] at eφ; cases Option.some.inj eφ
  simp only [CellU.erase_immOf, CellU.wit_immOf] at rφ₁ wφ₁
  have hw : w = r.v := rφ₁.symm.trans rφ
  have hσ : σ = r.R := wφ₁.symm.trans wφ
  subst hw; subst hσ
  -- 6.131 at `𝒱X`: the handed image, typed from the world
  have agreeCoh : ∀ {S : Ty}, (∀ y, LFree y S → LFree y r.T) → ∀ m,
      Coh (rsOf ls) m S (r.δ.extend x β) → Coh (rsOf ls) m S (δ'.extend x β) := by
    intro S hfree m h
    refine (coh_congr (fun y hy => ?_)).mp h
    by_cases hxy : x = y
    · subst hxy; rw [find?_extend_self, find?_extend_self]
    · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
      exact (hag y (hfree y hy)).symm
  have hP₀' : vX wpTS true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v χ₀ :=
    image_vX_of_shape (witLB_of hT.valid htag hle) (tags_above hT htag hβ) r.T hx hreb₀ hP₀ hR
      (fun m S u hpos hown => agreeCoh (fun y => hpos.free) m (coh_root hr hx hpos hown))
      (fun m S hpos => agreeCoh (fun y => hpos.free) m (coh_mut hT hr hx hpos))
  -- the choice
  obtain ⟨χ, hreb, hPχ, hagχ, hEF, hEI⟩ :=
    rebChooseO_top_tw hT htag hβ hr hag hW hx hreb₀ hP₀' hR
  refine ⟨χ, hreb, hPχ, hagχ, hEF, hEI, fun W' hWc hv' => ?_, ?_⟩
  · -- entry: `TW.reb`, its shape premise from `vX_vShape`
    have hsh : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ := by
      rw [← vShape_immReb_agree hag]; exact vX_vShape true _ hPχ
    exact ⟨TW.reb r x hT hr hle hx hreb hsh hβ hWc hv',
      tagged_reb hT hr hle hreb hβ hWc htag⟩
  · -- exit: `TW.rebEnd`
    rintro ps' ls' Wp W'' - hls hTp htgp ⟨s'', hs'', hc''⟩ hcomp hβ''
    have hr' : r ∈ rsOf ls' := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (hls _).mpr ht⟩
    exact ⟨TW.rebEnd r hTp hr' hc'' hreb hcomp hβ'', tagged_rebEnd hTp hcomp htgp⟩

/-- `RebChooseTW` at a chain view, at `𝒱X`: the cell's value is the chain's own (`ExIn`);
`image_vX_of_shape` with `coh_child`/`coh_mut_child`; `rebChooseO_deep_tw` chooses; entry
`TW.rebDeep`, exit `TW.rebEndDeep`.  `[about ours: our chooser at a chain view]` -/
theorem rebChooseTW_deep {ls : List SRec} {r : FrameRec} {p₀ : Option Loc} {l₀ : Loc}
    {S₀ : Ty} {u₀ : Val} {x : LifeVar} {δ' : LSub}
    (hr : r ∈ rsOf ls) (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀) (hag : AgreeOn S₀ δ' r.δ)
    (hx : ¬ LFree x S₀) :
    RebChooseTW ls l₀ (fun w σ => vX wpTS false S₀ ls δ' w σ)
      (fun β w χ => vShape (S₀.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vX wpTS true (S₀.immReborrow (.var x)) ls (δ'.extend x β) w χ) := by
  intro W F χ₀ σ ps β w s hs hT htag hβ hW hR hreb₀ hP₀
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  -- the cell's value is the chain's (`ex(R)_○` lifts into `ag(W)`)
  obtain ⟨φ₁, eφ₁, kφ₁, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  obtain ⟨e₀, he₀, hlift⟩ := hT.inv.exIn hr aW haW
  obtain ⟨ζ, eζ, rζ, -⟩ := exR_cell he₀ hch.own (by simp)
  obtain ⟨ζ', eζ', rζ', -⟩ := hlift l₀ ζ eζ
  rw [eφ₁] at eζ'; cases Option.some.inj eζ'
  simp only [CellU.erase_immOf, CellU.erase_ownOf, CellU.wit_immOf] at rφ₁ rζ wφ₁
  have hw : w = u₀ := rφ₁.symm.trans (rζ'.trans rζ)
  subst hw
  -- the view's owned cells are the record's (`DeepInv`)
  obtain ⟨-, -, hw₀own, -, -⟩ :=
    hT.inv.1.1 r hr p₀ l₀ S₀ w hch aW haW φ₁ eφ₁ (by rw [kφ₁]; simp)
  rw [wφ₁] at hw₀own
  have hP₀' : vX wpTS true (S₀.immReborrow (.var x)) ls (δ'.extend x β) w χ₀ :=
    image_vX_of_shape (witLB_of hT.valid htag hle) (tags_above hT htag hβ) S₀ hx hreb₀ hP₀ hR
      (fun m S u hpos hown => coh_child hr hch hag hx hpos (hw₀own m u hown))
      (fun m S hpos => coh_mut_child hT hr hch hag hx hpos)
  obtain ⟨χ, hreb, hPχ, hagχ, hEF, hEI⟩ :=
    rebChooseO_deep_tw hT htag hβ hr hch hag hW hx hreb₀ hP₀' hR
  refine ⟨χ, hreb, hPχ, hagχ, hEF, hEI, fun W' hWc hv' => ?_, ?_⟩
  · have hsh : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) w χ := by
      rw [← vShape_immReb_agree hag]; exact vX_vShape true _ hPχ
    exact ⟨TW.rebDeep r x hT hr hch hle hx hreb hsh hβ hWc hv',
      tagged_rebDeep hT hr hch hle hreb hβ hWc htag⟩
  · rintro ps' ls' Wp W'' - hls hTp htgp ⟨s'', hs'', hc''⟩ hcomp hβ''
    have hr' : r ∈ rsOf ls' := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (hls _).mpr ht⟩
    exact ⟨TW.rebEndDeep r hTp hr' hch hc'' hreb hcomp hβ'', tagged_rebEnd hTp hcomp htgp⟩

/-! ### Theorem 6.150 (↺ rule) at the typed world; record in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` -/
/-- `[TR]` Theorem 6.150 (`↺` rule, p. 39) at the tagged `wpTS`:

    ℓ ↦ Imm α (R ∧ Иβ. ↺_β P̂₀) ⋆ (Иβ. ∀v. P̂(v) ─⋆ wp_{ls}(e){[β]Q̂}) ⊧ wp_{ls}(e){Q̂}

`Fig16.BoLo.wp_reborrow`'s proof, H1–H33, with the list carried (the inner run's list is the
outer one; `ps′ ≡ ps`, `ls′ ≡ ls` pass through) and the typed world stepped by the chooser's
entry and exit.  `[variant: the chooser `RebChooseTW` in place of `RebEscrow`; `β` also below
the world's stratum (H11); `P̂₀` for the handed image, `P̂` for the chosen one; `R` on the
cell's payload]` -/
theorem wpTS_reborrow (ls : List SRec) (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop)
    (P₀ P : Life → BoCa.Val → WProp) (e : Expr) (Q : List SRec → BoCa.Val → WProp)
    (hesc : RebChooseTW ls l R P₀ P) :
    Entails
      (ptoImm l α (fun v σ => R v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ) ⋆
        (fresh fun b => all fun v => P b v ─⋆ wpTS ls e (fun ls' v' => box b (Q ls' v'))))
      (wpTS ls e Q) := by
  rintro ρ ⟨ρi, ρb, hc, hpi, hpb⟩ ρf fρ ps hf hcf hT htg
  -- H4 unfolded: `ρᵢ = ℓ ↦ imm(ᾱ, v′, ρ′)`, H7 and H8.
  obtain ⟨s, v', σ, hs, hρi, ⟨hRv, hP7⟩, hα⟩ := hpi
  subst hρi
  -- H9 and H10 — the two `И` bounds.
  obtain ⟨gi, hP9⟩ := hP7
  obtain ⟨gb, hP10⟩ := hpb
  -- H11, with `β` also below the world.
  obtain ⟨γW, hγW⟩ := ResU.exists_stratum fρ
  obtain ⟨β, hβi', hβb⟩ := exists_shorter (gi ⊓ γW) gb
  have hβi : β ⊏ gi := lt_of_lt_of_le hβi' inf_le_left
  have hβW : fρ.InStratum β := hγW.mono (le_of_lt (lt_of_lt_of_le hβi' inf_le_right))
  obtain ⟨⟨χ₀, hreb₀, hPχ₀⟩, h13⟩ := hP9 β hβi
  obtain ⟨hwand0, h15⟩ := hP10 β hβb
  have hwand := hwand0 v'
  -- H18: by 6.10 with H2, `✓ρ`, and therefore `ρᵢ # ρ_b`.
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  have h18 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρb := ⟨hc.1, ρ, hc, hvρ⟩
  have hbi : ResU.Hash ρb (ResU.single l (CellU.immOf s v' σ hs)) := ResU.hash_symm h18
  obtain ⟨ρbf, hbf, hbfi⟩ :=
    (hash_shift ρf ρb (ResU.single l (CellU.immOf s v' σ hs))).mp ⟨ρ, ResU.CompS.comm hc, hf⟩
  -- the world is `ρᵢ ● (ρ_f ● ρ_b)`
  have hWcell : ResU.CompS (ResU.single l (CellU.immOf s v' σ hs)) ρbf fρ := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' (ResU.CompS.comm hc) hcf
    rw [ResU.CompS.functional hab hbf] at hab'
    exact ResU.CompS.comm hab'
  -- choose the reborrow, now that the frame `ρ_b ● ρ_f` and the world are known.
  obtain ⟨χ, hreb, hPχ, ⟨A, hagχ⟩, hEF, hEI, hentry, hexit⟩ :=
    hesc fρ ρbf χ₀ σ ps β v' s hs hT htg hβW hWcell hRv hreb₀ hPχ₀
  -- *"By similar reasoning, we have `ρ_P̂(v′) # ρ_b ● ρ_f`."*
  have h19' : ResU.Hash ρbf χ := ResU.six55 hreb hEF hagχ hbfi
  -- H19, by 6.11 from the line above.
  have h19 : ResU.Hash ρb χ := (ResU.Hash.split hbf h19').2
  obtain ⟨ρbχ, hbχ⟩ := (ResU.compS_defined_iff ρb χ).mpr h19.1
  -- *"By lemma 6.55, `ρᵢ # ρ_P̂(v)`."*
  have hvi : ResU.Valid (ResU.single l (CellU.immOf s v' σ hs)) := (hash_valid hbi).2
  have h55self : ResU.Hash χ (ResU.single l (CellU.immOf s v' σ hs)) :=
    ResU.six55_self hreb hEI hagχ (ResU.hash_self_single_imm hvi)
  -- H20: *"therefore by lemma 6.15 with H2, `ρ_P̂(v′) # ρᵢ ● ρ_b ● ρ_f`."*
  have hiρbf : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρbf := ResU.hash_symm hbfi
  have h20 : ResU.Hash χ fρ := ResU.hash_of_pairwise h55self hiρbf (ResU.hash_symm h19') hWcell
  -- *"setting `ρ_f = ρᵢ ● ρ_f`, with the compatibility constraint from H20"*
  obtain ⟨ρF, hF, hFb⟩ := compS_reassoc' hbf hWcell
  have hFbχ : ResU.Hash ρF ρbχ := by
    obtain ⟨x, hx, hxh⟩ := (hash_shift ρF ρb χ).mpr ⟨fρ, hFb, ResU.hash_symm h20⟩
    rwa [ResU.CompS.functional hx hbχ] at hxh
  -- the world the inner run starts at: `ρ_f ● ρ ● χ`, typed by the chooser's entry
  obtain ⟨Win, hWin, hvWin⟩ := hFbχ.2
  have hfχ : ResU.CompS fρ χ Win := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hbχ hWin
    rwa [ResU.CompS.functional hab hFb] at hab'
  obtain ⟨hTin, htgin⟩ := hentry Win hfχ hvWin
  -- H21: by the definition of `─⋆`.
  have h21 : wpTS ls e (fun ls' v'' => box β (Q ls' v'')) ρbχ := hwand χ ρbχ hPχ hbχ
  obtain ⟨ρQ, ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', g1, g2, g3, g5, g6, g7, g8, g9, gA, gB,
    gT, gtg, gps, gls, gC⟩ := h21 ρF Win ps hFbχ hWin hTin htgin
  have g4 : ResU.CompS ρF ρbχ Win := hWin
  -- H28 and H29, by unfolding `[β]` in H27.
  obtain ⟨h28, h29⟩ := gC
  -- *"Let `ρ⁺′ = ρ⁺ ⊟ ρ_P̂(v′)|dom(ρ′|mut,own)`"* — `[TR]` 6.52 at that `⊟`.
  obtain ⟨ψ, hsubK, hsplit, hψβ⟩ :=
    ResU.six52_keep hreb (ResU.CompS.comm hbχ) g9 gA h15 h29
  -- 6.11 at the `#`s the inner `wp` produced.
  obtain ⟨hiQ, hfQ⟩ := ResU.Hash.split hF (ResU.hash_symm g1)
  obtain ⟨hFp, hQp⟩ := ResU.Hash.split g2 (ResU.hash_symm g3)
  obtain ⟨hip, hfp⟩ := ResU.Hash.split hF hFp
  obtain ⟨hψQ, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hQp)
  obtain ⟨hψi, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hip)
  have hvfp : ResU.Valid fρ'p := by obtain ⟨τ, hτ, -⟩ := g7; exact ⟨τ, hτ⟩
  -- The source memory: `⟦ρᵢ ● ρ_f ● ρ_P̂(v′) ● ρ_b⟧` regrouped as 6.58's `ρ ● ρ_b ● ρᵢ`.
  obtain ⟨t1, ht1, ht1'⟩ := compS_reassoc hF g4
  obtain ⟨u1, hu1, hu1'⟩ := compS_reassoc' hbχ ht1
  rw [ResU.CompS.functional hu1 hbf] at hu1'
  obtain ⟨Y58, hY58⟩ :=
    (ResU.compS_defined_iff ρbf (ResU.single l (CellU.immOf s v' σ hs))).mpr hbfi.1
  -- *"By rewriting in H24 with lemma 6.58"* — the first conclusion.
  have h58L := ResU.six58_left hreb hEI hagχ (ResU.hash_symm h19')
    hbfi (ResU.CompS.comm hu1') (ResU.CompS.comm ht1') hY58
  have hLY : ResU.Lower Y58 μ := (h58L μ).mp g5
  -- `ρ_b ● ρ_f ● ρᵢ = ρ_f ● ρ`, which is the source H30 names.
  obtain ⟨ac, hac, hac'⟩ := compS_exch hbf hY58
  obtain ⟨t2, ht2, ht2'⟩ := compS_reassoc hac hac'
  rw [ResU.CompS.functional ht2 hc] at ht2'
  rw [ResU.CompS.functional ht2' hcf] at hLY
  -- The target memory: `⟦ρᵢ ● ρ_f ● ρ_Q ● ρ⁺⟧` regrouped as 6.58's `ρ′ ● ρ⁺ ● ρᵢ`.
  obtain ⟨t3, ht3, ht3'⟩ := compS_reassoc hF g2
  obtain ⟨u3, hu3, hu3'⟩ := compS_reassoc ht3' g6
  have hiu3 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) u3 :=
    ⟨hu3'.1, fρ'p, hu3', hvfp⟩
  have hvu3 : ResU.Valid u3 := (ResU.Valid.split hu3' hvfp).2
  have ht3p : ResU.Hash t3 ρp := ⟨hu3.1, u3, hu3, hvu3⟩
  obtain ⟨hψt3, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm ht3p)
  obtain ⟨ρ'χ, hρ'χ⟩ := (ResU.compS_defined_iff t3 ψ).mpr (ResU.hash_symm hψt3).1
  obtain ⟨ht3i, -⟩ := ResU.Hash.split hu3 (ResU.hash_symm hiu3)
  have hiρ'χ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρ'χ :=
    ResU.hash_of_pairwise (ResU.hash_symm ht3i) (ResU.hash_symm hψt3)
      (ResU.hash_symm hψi) hρ'χ
  obtain ⟨Q58, hQ58⟩ :=
    (ResU.compS_defined_iff ρ'χ (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiρ'χ).1
  -- *"…with lemma 6.58"* — the second conclusion.
  have h58R := ResU.six58_right hreb hEI hagχ (ResU.hash_symm hiu3)
    hu3 hsubK.toSub hsplit hρ'χ (ResU.CompS.comm hu3') hQ58
  have hLQ : ResU.Lower Q58 μ' := (h58R μ').mp g7
  -- `ρ′ ● ρ⁺′ ● ρᵢ = (ρ_f ● ρ_Q) ● (ρᵢ ● ρ⁺′)`, the shape the goal's row takes.
  obtain ⟨bc, hbc, hbc'⟩ := compS_exch hρ'χ hQ58
  obtain ⟨ρpG, hρpG, hρpG'⟩ := compS_reassoc hbc hbc'
  -- H33, by lemma 6.59.
  have hiπ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) π :=
    ResU.hash_of_pairwise hiQ hQp hip g9
  obtain ⟨w59, hw59⟩ := (ResU.compS_defined_iff ρQ ψ).mpr (ResU.hash_symm hψQ).1
  have hiw59 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) w59 :=
    ResU.hash_of_pairwise hiQ (ResU.hash_symm hψQ) (ResU.hash_symm hψi) hw59
  obtain ⟨Y59, hY59⟩ :=
    (ResU.compS_defined_iff w59 (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiw59).1
  have hvY59 : ResU.Valid Y59 := hash_valid_comp (ResU.hash_symm hiw59) hY59
  obtain ⟨σX, hσX⟩ := id hvρ
  obtain ⟨σY, hσY⟩ := id hvY59
  have h59 : ResU.Upd ρ Y59 :=
    ResU.six59 hreb (ResU.CompS.comm hbχ) g9 gA h15 h29 (ResU.hash_symm h18)
      (ResU.hash_symm hiπ) hsubK hc ⟨w59, hw59, hY59⟩ hσX hσY
  -- `ρ_Q ● ρᵢ ● ρ⁺′` is `ρ_Q ● (ρᵢ ● ρ⁺′)` — 6.59's `Y` at the goal's bracketing.
  obtain ⟨bc59, hbc59, hbc59'⟩ := compS_reassoc hw59 hY59
  rw [ResU.CompS.functional (ResU.CompS.comm hbc59) hρpG] at hbc59'
  -- The final world, typed by the chooser's exit: `W″ ● ρ_P̂(v′)|dom(ρ′|mut,own)` is the inner
  -- run's final world.
  have hexW : ResU.CompS Q58 (χ.restrictDom σ.exclPart) fρ'p := by
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' hsplit hu3
    rw [ResU.CompS.functional hab hρ'χ] at hab'
    obtain ⟨ab', hab₂, hab₂'⟩ := compS_reassoc' hab' hu3'
    rwa [ResU.CompS.functional hab₂ (ResU.CompS.comm hQ58)] at hab₂'
  have hcellQ : ∃ (s' : LSet) (hs' : σ.InStratum s'.join),
      Q58.get l = some (CellU.immOf s' v' σ hs') := cell_of_compS_single (ResU.CompS.comm hQ58)
  have hQβ : Q58.InStratum β := by
    have hfβ : ρf.InStratum β := ResU.CompS.inStratum_left hcf hβW
    have hρβ : ρ.InStratum β := ResU.CompS.inStratum_right hcf hβW
    have hiβ : (ResU.single l (CellU.immOf s v' σ hs)).InStratum β :=
      ResU.CompS.inStratum_left hc hρβ
    exact ResU.CompS.inStratum hQ58
      (ResU.CompS.inStratum hρ'χ (ResU.CompS.inStratum ht3 hfβ h29) hψβ) hiβ
  obtain ⟨hTout, htgout⟩ := hexit ps' ls' fρ'p Q58 gps gls gT gtg hcellQ hexW hQβ
  -- G2–G7.
  refine ⟨ρQ, ρpG, t3, Q58, Y59, v, μ, μ', ps', ls', ResU.hash_symm hfQ, ht3, ?_, hLY,
    hρpG', hLQ, g8, hbc59', ⟨h59, hvρ, hvY59⟩, ?_, hTout, htgout, gps, gls, h28⟩
  · exact ResU.hash_symm
      (ResU.hash_of_pairwise ht3i (ResU.hash_symm hψi) (ResU.hash_symm hψt3) hρpG)
  · exact noOwn_compS hρpG (noOwn_single_imm l s v' σ hs) (noOwn_subKeep hsubK gB)

end BoCa.Fig16.LogRel.Typed

end
