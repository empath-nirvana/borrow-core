import Core.Chain.SI.RebAgreeCex

/-!
# `[TR]` 6.150's chooser at canonical images

`rebChooseC_top` is `rebChooseTW_top` (`Core/Reborrow.lean`) at `TWNC`: the image it returns is
`canon r β`, the record's template re-taken at `β`, rather than the world's joint image or the
handed one. The steps are `rebChooseO_top`'s first branch with `c₀ := tmpl r`:

* the template exists (`tmpl_exists`): the world's joint image if a root has a view
  (`JointAt`), the handed image otherwise (`agW_image_noview`), as in `rebChooseO_top`'s two
  branches;
* `canon r β` is typed at the program's relation by `relabel_obs` from the template's shape and
  the escrow's observable payload, as the joint image is in `rebChooseO_top`;
* the agreement `[TR]` 6.55 asks for is `canon_escrowAgree` at the world, carried to the frame and
  to the cell by `lift_view`, where `rebChooseO_top` reads it off `JointAt`;
* entry `TWNC.reb` (its image premise is `rfl`), exit `TWNC.rebEnd`.

`RebChooseTWN` (`SI/RebRuleN.lean`, now at `TWNC`) is the chooser `rwp_reborrow` takes;
`rebChooseC_tw` discharges it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeVar)

/-- `coh_mut` from `TI`. -/
theorem coh_mutI {W : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) {r₀ : FrameRec}
    (hr₀ : r₀ ∈ rs) {x : LifeVar} {β : Life} (hx : ¬ VFree x r₀.T) {m : Loc} {S : VTy}
    (hS : MutPos r₀.T r₀.v m S) : Coh rs m S (r₀.δ.extend x β) := by
  have hR₀ := (hTI.1.2.2.2.1 r₀ hr₀).1
  obtain ⟨ζ, eζ, kζ, -⟩ := mut_split_den hS hR₀
  have hd : SubRec r₀ ⟨m, ζ.erase, ζ.wit, S, r₀.δ⟩ := ⟨rfl, GPos.here hS, ζ, eζ, kζ, rfl, rfl⟩
  refine Or.inl ⟨_, hTI.sub hr₀ hd, rfl, rfl, fun y hy => ?_⟩
  have hxy : x ≠ y := fun e => hx (e ▸ hS.free hy)
  exact find?_extend_ne _ _ hxy

/-- `tagged_rebEnd` at `TWN`. -/
theorem tagged_rebEndN {W W' D : WRes} {ps rs : List FrameRec} {ls : List SRec}
    (hW₀ : TWN W ps rs) (hW : ResU.CompS W' D W) (htag : Tagged W ps ls) : Tagged W' ps ls := by
  obtain ⟨aW, haW⟩ := agW_of_valid hW₀.valid
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  refine ⟨p, hp, hd, frameLife_back hα (fun a' ha' => ?_)⟩
  obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
  rw [AgW.functional ha'' ha'] at hcomp
  exact ⟨aW, haW, icpAt_left hcomp _, fun m _ => icpAt_left hcomp m⟩

/-- **The template exists** once a reborrow of the record is handed an image: the world's joint
image if a root of the record has a view (`JointAt`), the handed image otherwise. -/
theorem tmpl_exists {W F χ₀ : WRes} {ps rs : List FrameRec} {r : FrameRec} {le : Loc}
    {s : LSet} {hs : r.R.InStratum s.join} {x : LifeVar} {β : Life}
    (hT : TWNC W ps rs) (hr : r ∈ rs)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W)
    (hx : ¬ VFree x r.T) (hreb₀ : ResU.Reb β r.R χ₀)
    (hsh₀ : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ₀) :
    ∃ c, TmplSpec r c := by
  have hTI := hT.inv
  obtain ⟨hRden, -⟩ := hTI.1.2.2.2.1 r hr
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  by_cases hv : ∃ S l u, Root r S l u ∧ ∃ a, AgW W a ∧ ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨β₀, x₀, c₀, hx₀, hreb₀', hden₀, hA, -⟩ := hTI.1.2.2.2.2.1 r hr hv
    exact ⟨c₀, β₀, x₀, hx₀, hreb₀', hden₀, hA⟩
  · refine ⟨χ₀, β, x, hx, hreb₀, hsh₀, agW_image_noview haW hle hreb₀
      (fun y ψ u hψ hu ζ hζ => ?_)⟩
    obtain ⟨ζ', eζ', hpos⟩ := image_dom r.T hsh₀ hRden hψ
    rw [hu] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    by_contra hk
    exact hv ⟨S, y, u, ⟨hS, hu⟩, aW, haW, ζ, hζ, hk⟩

/-- **The canonical image at the program's relation.** At a typed world holding the record's
cell, from the escrow's observable payload, `WitLB` and the tag bound: `canon r β` is an image at
`β` typed at `vC true⟦Imm̲ 'x T⟧`, its `ag` is defined, and it agrees with the frame and with the
cell. `rebChooseO_top`'s first branch with `c₀ := tmpl r`. -/
theorem canon_obs {W F : WRes} {ps : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {hs : r.R.InStratum s.join} {x : LifeVar} {β : Life} {δ' : LSub}
    (hT : TWNC W ps (rsOf ls)) (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W)
    (hx : ¬ VFree x r.T) (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β)
    (hRobs : vC false r.T ls δ' r.v r.R)
    (hLB : WitLB ls r.R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) :
    ResU.Reb β r.R (canon r β) ∧
      vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v (canon r β) ∧
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

/-- **`[TR]` 6.150's chooser at canonical images**, at a record's cell, at the program's relation:
`RebChooseTWN` (at `TWNC`), with the chosen image `canon r β`. -/
theorem rebChooseC_tw {ls : List SRec} {r : FrameRec} {x : LifeVar} {δ' : LSub}
    (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ) (hx : ¬ VFree x r.T) :
    RebChooseTWN ls r.le (fun w σ => vC false r.T ls δ' w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) w χ) := by
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
    canon_obs hT hr hag hW hx hS hreb₀.1 hR (witLB_of hT.valid htag hle) hβls
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

end BoCa.Fig16.LogRel.Core.Chain.SI

end
