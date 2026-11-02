import DtorUnwind.CoreC.Reborrow
import DtorUnwind.SI.RebChooseC
import DtorUnwind.SI.RebStopD

/-!
# `[TR]` 6.150's two choosers at canonical images, at the copy's relation

The library's `rebChooseTW_top` and `rebChooseTW_deep` (`Core/Reborrow.lean`) with the same
statements over `TWNC`: `RebChooseTW` is the copy's (`DtorUnwind.SI.TWNC` in place of `TW`) and
the payloads are at the copy's `vCc`. These are the only two places the library constructs a
`TW.reb`/`TW.rebDeep` world, so they are the only places a reborrow's image is chosen. Every
other rule receives the image through `RebChooseTW`'s existential.

The proofs are the library's choosers' (`rebChooseO_top_tw`, `rebChooseO_deep_tw`) with the
image re-taken from the record's template (`tmpl r`, `tmplD r S₀ u₀ w₀`) where the library
re-takes the world's joint image (`TI`'s joint-image clauses) or keeps the handed one. The template
is itself one of those two (`tmpl_exists`, `tmplD_exists`): the joint image when a position has a
view, the handed image otherwise, exactly the library's two branches. The re-taken image is typed
by `relabel_obs` as in the library; the agreement `[TR]` 6.55 asks for comes from the template
invariant (`canon_escrowAgree`, `canonD_agree_split`) where the library reads it off the joint
image.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.C
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open DtorUnwind.SI (TWNC TmplSpec TmplSpecD tmpl tmplD canon canonD tmpl_spec tmplD_spec
  tmpl_exists canon_escrowAgree canonD_reb canonD_agree_split tags_aboveN rebRecLe_of_tags
  tagged_rebN tagged_rebDeepN tagged_rebEndN rebEndRec_of_inStratum coh_mutI)

/-- `canon_obs` (`SI/RebChooseC.lean`) at the copy's `vCc`: `canon r β` is an image at `β`, typed
at `vCc true⟦Imm̲ 'x T⟧`, with `ag` defined, agreeing with the frame and the cell. -/
theorem canon_obsC {W F : WRes} {ps : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {hs : r.R.InStratum s.join} {x : LifeVar} {β : Life} {δ' : LSub}
    (hT : TWNC W ps (rsOf ls)) (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W)
    (hx : ¬ VFree x r.T) (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hRobs : vCc false r.T ls δ' r.v r.R)
    (hLB : WitLB ls r.R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) :
    ResU.Reb β r.R (canon r β) ∧
      vCc true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v (canon r β) ∧
      (∃ A, AgW (canon r β) A) ∧ (∀ a, AgW F a → EscrowAgree r.R (canon r β) a) ∧
      (∀ a, AgW (ResU.single le (CellU.immOf s r.v r.R hs)) a →
        EscrowAgree r.R (canon r β) a) := by
  have hTI := hT.inv
  obtain ⟨-, e, aW, -, haW, -⟩ := hT.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  have hS' := hS
  obtain ⟨β₀, x₀, hx₀, hreb₀, hden₀, ⟨A₀, hA₀⟩⟩ := hS'
  have agreeCoh : ∀ {S : VTy}, (∀ y, VFree y S → VFree y r.T) → ∀ m,
      Coh (rsOf ls) m S (r.δ.extend x β) → Coh (rsOf ls) m S (δ'.extend x β) := by
    intro S hfree m h
    refine (coh_congr (fun y hy => ?_)).mp h
    by_cases hxy : x = y
    · subst hxy; rw [find?_extend_self, find?_extend_self]
    · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
      exact (hag y (hfree y hy)).symm
  have hden₀' : vShape (r.T.immReborrow (.var x₀)) (δ'.extend x₀ β₀) r.v (tmpl r) := by
    rw [vShape_immReb_agree hag]; exact hden₀
  have hW_agree := canon_escrowAgree hT hr hS β
  have liftG : ∀ G, (G = F ∨ G = ResU.single le (CellU.immOf s r.v r.R hs)) →
      ∀ a, AgW G a → EscrowAgree r.R (canon r β) a := by
    rintro G hG a ha l v ψ ψf hown hψ hψf hk hkf
    have hlift : ∃ ψ', aW.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ'.wit = ψf.wit := by
      rcases hG with rfl | rfl
      · rw [AgW.functional ha h₂] at hψf; exact lift_view hc.comm hψf hkf
      · rw [AgW.functional ha h₁] at hψf; exact lift_view hc hψf hkf
    obtain ⟨ψ', e', k', w'⟩ := hlift
    exact w'.symm.trans (hW_agree aW haW l v ψ ψ' hown hψ e' hk k')
  refine ⟨relabel_reb hRβ hreb₀, ?_, agW_relRes (fun m ψ e => (reb_cell hreb₀ e).1) hA₀,
    liftG F (Or.inl rfl), liftG _ (Or.inr rfl)⟩
  exact relabel_obs hLB hβls r.T hx hx₀ hden₀' hRobs
    (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
    (fun m ψ e => reb_cell_match hreb₀ e) (reb_wit_stratum hRβ hreb₀)
    (fun m S u hpos hown => agreeCoh (fun y => hpos.free) m (coh_root hr hx hpos hown))
    (fun m S hpos => agreeCoh (fun y => hpos.free) m (coh_mutI hTI hr hx hpos))

/-- **`rebChooseTW_top` at canonical images**: the library's statement, at `TWNC` and the copy's
relation. The chosen image is `canon r β`. -/
theorem rebChooseTW_top {ls : List SRec} {r : FrameRec} {x : LifeVar} {δ' : LSub}
    (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ) (hx : ¬ VFree x r.T) :
    RebChooseTW ls r.le (fun w σ => vCc false r.T ls δ' w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vCc true (r.T.immReborrow (.var x)) ls (δ'.extend x β) w χ) := by
  intro W F χ₀ σ ps β w s hs hT htag hβ hW hR hreb₀ hP₀
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨φ₁, eφ₁, -, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  obtain ⟨φ, eφ, -, rφ, wφ⟩ := hT.inv.leInvW r hr aW haW
  rw [eφ₁] at eφ; cases Option.some.inj eφ
  simp only [CellU.erase_immOf, CellU.wit_immOf] at rφ₁ wφ₁
  have hw : w = r.v := rφ₁.symm.trans rφ
  have hσ : σ = r.R := wφ₁.symm.trans wφ
  subst hw; subst hσ
  have hP₀s : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ₀ := by
    rw [← vShape_immReb_agree hag]; exact hP₀
  have hS := tmpl_spec (tmpl_exists hT hr hW hx hreb₀ hP₀s)
  have hβls := tags_aboveN hT.toN htag hβ
  obtain ⟨hreb, hPχ, hagχ, hEF, hEI⟩ :=
    canon_obsC hT hr hag hW hx hS hreb₀.1 hR (witLB_of hT.valid htag hle) hβls
  refine ⟨canon r β, hreb, hPχ, hagχ, hEF, hEI, fun W' hWc hv' => ?_, ?_⟩
  · have hsh : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β) := by
      rw [← vShape_immReb_agree hag]; exact vC_vShape true _ hPχ
    have hrebLe := rebRecLe_of_tags hT.toN htag hβls r.R
    exact ⟨TWNC.reb r x hT hr hle hx hreb hsh hrebLe rfl hWc hv',
      tagged_rebN hT.toN hr hle hreb hrebLe hWc htag⟩
  · rintro ps' ls' Wp W'' - hls hTp htgp ⟨s'', hs'', hc''⟩ hcomp hβ''
    have hr' : r ∈ rsOf ls' := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (hls _).mpr ht⟩
    exact ⟨TWNC.rebEnd r hTp hr' hc'' hreb hcomp (rebEndRec_of_inStratum hβ''),
      tagged_rebEndN hTp.toN hcomp htgp⟩

/-- **A chain view's template exists** once a reborrow of the view is handed an image: the
world's joint image at the view if a child position has a view (`TI`'s chain joint-image clause),
the handed image otherwise. `tmpl_exists` one level down; the two branches of
`rebChooseO_deep_tw`. -/
theorem tmplD_exists {W F χ₀ : WRes} {ps rs : List FrameRec} {r : FrameRec} {p₀ : Option Loc}
    {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    {x : LifeVar} {β : Life}
    (hT : TWNC W ps rs) (hr : r ∈ rs) (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀)
    (hW : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) F W)
    (hx : ¬ VFree x S₀) (hreb₀ : ResU.Reb β w₀ χ₀)
    (hsh₀ : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ χ₀) :
    ∃ c, TmplSpecD r S₀ u₀ w₀ c := by
  have hTI := hT.inv.1
  obtain ⟨h1, -, -, -, -, h6⟩ := hTI
  obtain ⟨-, e, aW, -, haW, -⟩ := hT.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨χl, eχl, kχl, -, wχl⟩ := AgW.get_imm h₁ (ResU.single_get_self _ _)
    (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχl
  obtain ⟨χ₀', eχ₀', kχ₀', wχ₀'⟩ := lift_view hc eχl (by rw [kχl]; simp)
  have hχ₀w : χ₀'.wit = w₀ := wχ₀'.trans wχl
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ := h1 r hr p₀ l₀ S₀ u₀ hch aW haW χ₀' eχ₀' kχ₀'
  rw [hχ₀w] at hw₀den hw₀own
  by_cases hv : ∃ l S u, Chain r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgW W a ∧
      ∃ ψ : CellU Loc Val, a.get l = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨w₁, hw₁, β₀, x₀, c₀, hx₀, hreb₁, hden₁, hA₁, -⟩ := h6 r hr p₀ l₀ S₀ u₀ hch hv
    have hw₁₀ : w₁ = w₀ := by
      obtain ⟨ψ₁, e₁, -, w₁'⟩ := hw₁ aW haW
      rw [eχ₀'] at e₁; cases Option.some.inj e₁
      exact w₁'.symm.trans hχ₀w
    subst hw₁₀
    exact ⟨c₀, β₀, x₀, hx₀, hreb₁, hden₁, hA₁⟩
  · refine ⟨χ₀, β, x, hx, hreb₀, hsh₀, agW_image_noview haW hle hreb₀
      (fun y ψ u hψ hu ζ hζ => ?_)⟩
    obtain ⟨ζ', eζ', hpos⟩ := image_dom S₀ hsh₀ hw₀den hψ
    rw [hu] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    by_contra hk
    exact hv ⟨y, S, u, hch.snoc hS (hw₀own y u hu), aW, haW, ζ, hζ, hk⟩

/-- **`rebChooseTW_deep` at canonical images**: the library's statement, at `TWNC` and the copy's
relation. The chosen image is `canonD r S₀ u₀ w β`. -/
theorem rebChooseTW_deep {ls : List SRec} {r : FrameRec} {p₀ : Option Loc} {l₀ : Loc}
    {S₀ : VTy} {u₀ : Val} {x : LifeVar} {δ' : LSub}
    (hr : r ∈ rsOf ls) (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀) (hag : AgreeOn S₀ δ' r.δ)
    (hx : ¬ VFree x S₀) :
    RebChooseTW ls l₀ (fun w σ => vCc false S₀ ls δ' w σ)
      (fun β w χ => vShape (S₀.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vCc true (S₀.immReborrow (.var x)) ls (δ'.extend x β) w χ) := by
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
  have hP₀s : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) w χ₀ := by
    rw [← vShape_immReb_agree hag]; exact hP₀
  -- the template and its canonical image at `β`
  have hS := tmplD_spec (tmplD_exists hT hr hch hW hx hreb₀ hP₀s)
  have hβls := tags_aboveN hT.toN htag hβ
  have hRβ : σ.InStratum β := hreb₀.1
  have hreb : ResU.Reb β σ (canonD r S₀ w σ β) := canonD_reb hS hRβ
  obtain ⟨hEF, hEI⟩ := canonD_agree_split hT hr hch hS β hW
  have hS' := hS
  obtain ⟨β₀, x₀, hx₀, hrebT, hdenT, ⟨A₀, hA₀⟩⟩ := hS'
  have hdenT' : vShape (S₀.immReborrow (.var x₀)) (δ'.extend x₀ β₀) w (tmplD r S₀ w σ) := by
    rw [vShape_immReb_agree hag]; exact hdenT
  have hPχ : vCc true (S₀.immReborrow (.var x)) ls (δ'.extend x β) w (canonD r S₀ w σ β) :=
    relabel_obs (witLB_of hT.valid htag hle) hβls S₀ hx hx₀ hdenT' hR
      (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
      (fun m ψ e => reb_cell_match hrebT e) (reb_wit_stratum hRβ hrebT)
      (fun m S u hpos hown => coh_child hr hch hag hx hpos (hw₀own m u hown))
      (fun m S hpos => coh_mut_child hT hr hch hag hx hpos)
  refine ⟨canonD r S₀ w σ β, hreb, hPχ, agW_relRes (fun m ψ e => (reb_cell hrebT e).1) hA₀,
    hEF, hEI, fun W' hWc hv' => ?_, ?_⟩
  · have hsh : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) w (canonD r S₀ w σ β) := by
      rw [← vShape_immReb_agree hag]; exact vC_vShape true _ hPχ
    have hrebLe := rebRecLe_of_tags hT.toN htag hβls σ
    have hcellLe : DtorUnwind.SI.RebCellLe W l₀ β := by
      intro a ha
      obtain ⟨ξ, t, eξ, ht, hy⟩ :=
        (icpAt_agW ha _ _ hle).ls (CellU.lsOf_immOf _ _ _ _) (LSet.meet_mem _)
      exact ⟨ξ, t, _, eξ, ht, hy,
        CellU.sqsupset_of_lsOf (CellU.lsOf_immOf _ _ _ _) (hβ _ _ hle)⟩
    exact ⟨TWNC.rebDeep r x hT hr hch hle hx hreb hsh hcellLe hrebLe rfl hWc hv',
      tagged_rebDeepN hT.toN hr hch hle hreb hrebLe hWc htag⟩
  · rintro ps' ls' Wp W'' - hls hTp htgp ⟨s'', hs'', hc''⟩ hcomp hβ''
    have hr' : r ∈ rsOf ls' := by
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (hls _).mpr ht⟩
    exact ⟨TWNC.rebEndDeep r hTp hr' hch hc'' hreb hcomp (rebEndRec_of_inStratum hβ''),
      tagged_rebEndN hTp.toN hcomp htgp⟩

end BoCa.Fig16.LogRel.Core.C

end
