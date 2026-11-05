import Core.Chain.SI.TWNC

/-!
# Canonical images at chain views: the template invariant extends

`TWNC.rebDeep` takes the image `canonD r S₀ u₀ w₀ β`: the template of the chain view
(`tmplD`, one typed image of the view's escrow `w₀`, fixed for the record, the position's type
and value, and the escrow) re-taken at `β`. The invariant it buys is `TemplAt`'s one level down,
and it is global, not pointwise: at every chain position `m` of a record whose parent is `ℓ₀`,
every view of `ag(W)` at `m` carries the witness the parent's template gives at `m`, the parent's
template being read at the witness of the view at `ℓ₀` in the same `ag(W)` (`TemplDAt`,
`TWNC.templD`).

Proved by induction on `TWNC`: a step whose world grows (`reb`, `rebDeep`) brings the child's
view back from the old world (`reb_like_back`) and lifts the old parent view forward
(`lift_view`), so the parent's witness is the old one; a new view at a child is a cell of the
canonical image, whose witness is the template's (`canonD_get`). A step whose world shrinks or
changes cells (`immFrame`, `immEnd`, `rebEnd`, `rebEndDeep`) brings both views back
(`frame_transfer`, `end_back`, `lift_view`).

From it, the canonical image of a chain view agrees with every typed world holding the view
(`canonD_escrowAgree`): the input `[TR]` 6.55 asks at a re-entry after a stop.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-- **The template invariant at chain views.** At a chain position `m` of `r` whose parent is
`ℓ₀`, every view of `ag(W)` at `m` carries the witness the template of the view at `ℓ₀` gives. -/
def TemplDAt (W : WRes) (r : FrameRec) : Prop :=
  ∀ p₀ l₀ S₀ u₀, Chain r.R r.T r.v p₀ l₀ S₀ u₀ → ∀ m S u, Chain r.R r.T r.v (some l₀) m S u →
    ∀ a, AgW W a → ∀ ψ₀ ψ : CellU Loc Val, a.get l₀ = some ψ₀ → ψ₀.kind ≠ Kind.own →
      a.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ, (tmplD r S₀ u₀ ψ₀.wit).get m = some ζ ∧ ψ.wit = ζ.wit

/-- `TemplDAt` passes along a step whose views at the record's chain positions come back from
the old world with their witnesses. -/
theorem templDAt_of_back {W W' : WRes} {r : FrameRec} (h : TemplDAt W r) {aW : WRes}
    (haW : AgW W aW)
    (back : ∀ a', AgW W' a' → ∀ p m S u, Chain r.R r.T r.v p m S u →
      ∀ ψ : CellU Loc Val, a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) :
    TemplDAt W' r := by
  intro p₀ l₀ S₀ u₀ hpar m S u hch a' ha' ψ₀ ψ e₀ k₀ e k
  obtain ⟨φ₀, f₀, kf₀, w₀⟩ := back a' ha' p₀ l₀ S₀ u₀ hpar ψ₀ e₀ k₀
  obtain ⟨φ, f, kf, w⟩ := back a' ha' (some l₀) m S u hch ψ e k
  obtain ⟨ζ, eζ, wζ⟩ := h p₀ l₀ S₀ u₀ hpar m S u hch aW haW φ₀ φ f₀ kf₀ f kf
  rw [w₀]
  exact ⟨ζ, eζ, w.trans wζ⟩

theorem templDAt_of_ag {W W' : WRes} {r : FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (h : TemplDAt W r) : TemplDAt W' r := by
  intro p₀ l₀ S₀ u₀ hpar m S u hch a' ha'
  exact h p₀ l₀ S₀ u₀ hpar m S u hch a' (t a' ha')

/-- At a step `W′ = W ● c` whose new views are cells of `c` at positions `c` covers: the parent's
view is the old one lifted (`lift_view`); the child's comes back (`back`) or is new (`new`). -/
theorem templDAt_grow {W W' c : WRes} {ps rs : List FrameRec} {r : FrameRec}
    (hTI : TI W ps rs) (hr : r ∈ rs) (h : TemplDAt W r) {aW : WRes} (haW : AgW W aW)
    (hW : ResU.CompS W c W')
    (back : ∀ a', AgW W' a' → ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ∀ ψ : CellU Loc Val, a'.get m = some ψ → ψ.kind ≠ Kind.own →
      (∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) ∨
      ∀ p₀ S₀ u₀, Chain r.R r.T r.v p₀ l₀ S₀ u₀ → ∀ ψ₀ : CellU Loc Val, a'.get l₀ = some ψ₀ →
        ψ₀.kind ≠ Kind.own → ∃ ζ, (tmplD r S₀ u₀ ψ₀.wit).get m = some ζ ∧ ψ.wit = ζ.wit) :
    TemplDAt W' r := by
  intro p₀ l₀ S₀ u₀ hpar m S u hch a' ha' ψ₀ ψ e₀ k₀ e k
  rcases back a' ha' l₀ m S u hch ψ e k with ⟨φ, f, kf, w⟩ | hnew
  · -- the child is old: its parent's old view, lifted, is the parent's view now
    obtain ⟨-, -, -, -, hpv⟩ := hTI.1.1 r hr (some l₀) m S u hch aW haW φ f kf
    obtain ⟨φ₀, f₀, kf₀, -⟩ := hpv l₀ rfl
    obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha'
    rw [AgW.functional haW' haW] at hcomp
    obtain ⟨ψ₀', e₀', -, w₀'⟩ := lift_view hcomp f₀ kf₀
    rw [e₀] at e₀'; cases Option.some.inj e₀'
    obtain ⟨ζ, eζ, wζ⟩ := h p₀ l₀ S₀ u₀ hpar m S u hch aW haW φ₀ φ f₀ kf₀ f kf
    rw [w₀']
    exact ⟨ζ, eζ, w.trans wζ⟩
  · exact hnew p₀ S₀ u₀ hpar ψ₀ e₀ k₀

/-- **`TWNC` keeps the template invariant at chain views, at every record.** -/
theorem TWNC.templD {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) :
    ∀ r ∈ rs, TemplDAt W r := by
  induction h with
  | empty => intro r hr; exact absurd hr (by simp)
  | alloc _ _ _ hW _ ih => exact fun r hr => templDAt_of_ag (fun a ha => alloc_ag hW ha) (ih r hr)
  | @immFrame W X Z R W' ps rs ds l v α T δ hα hW₀ hadm hX hW hden hW' hv hds ih =>
      have hvW := hW₀.toN.valid
      have hTI := hW₀.toN.inv
      obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
      obtain ⟨eR, heR, -, hRl⟩ := frame_ex hX hW heW
      intro x hx
      have hcases : DescR ⟨l, v, R, T, δ⟩ x ∨ x ∈ rs := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl (DescR.refl _)
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨p, -, hp⟩ := (hds x).mp hx; exact Or.inl ⟨p, hp⟩
          · exact Or.inr hx
      rcases hcases with ⟨p, hp⟩ | hx
      · -- a record of the new frame: no chain position has a view
        intro p₀ l₀ S₀ u₀ hpar m S u hch a' ha' ψ₀ ψ e₀ k₀ e k
        have hex : ∀ eR', ExS R eR' → eR'.get m = some (CellU.ownOf u) := fun eR' heR' =>
          xpath_ex heR' hp.xpath hch.own (by simp)
        have hml : m ≠ l := by
          rintro rfl; rw [hex eR heR] at hRl; cases hRl
        exact ((frame_new_root' hX hW hW' hvW hex hml ha').2.1 ψ e k).elim
      · obtain ⟨aW₁, haW₁⟩ := agW_of_valid hvW
        refine templDAt_of_back (ih x hx) haW₁ fun a' ha' p m S u hc ψ e k => ?_
        obtain ⟨aW₂, haW₂, ψ₀, e₀, k₀, w₀⟩ :=
          frame_transfer hX hW hW' hvW (hTI.1.2.1 x hx m u hc.own) ha' e k
        rw [AgW.functional haW₂ haW₁] at e₀
        exact ⟨ψ₀, e₀, k₀, w₀⟩
  | @reb W W' c ps rs r₀ le s β hs x hW₀ hr₀ hle hx hreb hden hβ hc hW hv ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      have hR := (hTI.1.2.2.2.1 r hr).1
      refine templDAt_grow hTI hr (ih r hr) haW hW fun a' ha' l₀ m S u hch ψ e k => ?_
      rcases reb_like_back hle hreb hW haW ha' e k with hold | ⟨u₁, q, hq, hown, hcl, -⟩
      · exact Or.inl hold
      · -- a cell of the image is at a root of `r₀`, and a root is no chain child
        exfalso
        have e₁ : r = r₀ := hTI.1.2.2.1 r hr r₀ hr₀ m u u₁ hch.own hown
        subst e₁
        obtain ⟨ζ, eζ, hpos⟩ := image_dom r.T hden (hTI.1.2.2.2.1 r hr).1 hcl
        rw [hown] at eζ; cases Option.some.inj eζ
        obtain ⟨S', hS'⟩ := hpos rfl
        exact absurd (chain_unique_rec hR hch (Chain.one hS' hown)).1 (by simp)
  | @rebDeep W W' c ps rs r₀ p₁ l₁ S₁ u₁ s w₀ hs β x hW₀ hr₀ hch₀ hcell hx hreb hden hβc hrec
      hc hW hv ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      have hR := (hTI.1.2.2.2.1 r hr).1
      obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
      rw [CellU.wit_immOf] at wχ
      obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
        hTI.1.1 r₀ hr₀ p₁ l₁ S₁ u₁ hch₀ aW haW χ eχ (by rw [kχ]; simp)
      rw [wχ] at hw₀den hw₀own
      refine templDAt_grow hTI hr (ih r hr) haW hW fun a' ha' l₀ m S u hch ψ e k => ?_
      rcases reb_like_back hcell hreb hW haW ha' e k with hold | ⟨u', q, hq, hown, hcl, hw⟩
      · exact Or.inl hold
      · -- a cell of the canonical image, at a child of `ℓ₁`
        refine Or.inr fun p₀ S₀ u₀ hpar ψ₀ e₀ k₀ => ?_
        have e₁ : r = r₀ := hTI.1.2.2.1 r hr r₀ hr₀ m u u' hch.own (hw₀own m u' hown)
        subst e₁
        obtain ⟨ζ, eζ, hpos⟩ := image_dom S₁ hden hw₀den hcl
        rw [hown] at eζ; cases Option.some.inj eζ
        obtain ⟨S', hS'⟩ := hpos rfl
        have hcS := hch₀.snoc hS' (hw₀own m u' hown)
        have hl : l₀ = l₁ := Option.some.inj (chain_unique_rec hR hch hcS).1
        subst hl
        obtain ⟨-, hSS⟩ := chain_unique_rec hR hpar hch₀
        have huu := chain_val hpar hch₀
        subst hSS huu
        -- the parent's view is the view at `ℓ₁`, its witness `w₀`
        obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha'
        rw [AgW.functional haW' haW] at hcomp
        obtain ⟨ψ₁, e₁', -, w₁⟩ := lift_view hcomp eχ (by rw [kχ]; simp)
        rw [e₀] at e₁'; cases Option.some.inj e₁'
        rw [w₁, wχ]
        subst hc
        obtain ⟨ζ', eζ', wζ'⟩ := canonD_get hcl
        rw [CellU.wit_immOf] at wζ'
        exact ⟨ζ', eζ', hw.trans wζ'⟩
  | mutFold hW₀ hX hW hW' _ ih =>
      exact fun r hr => templDAt_of_ag (fun a ha => (mut_fold_ag hX hW hW' a).mpr ha) (ih r hr)
  | mutUnfold hW₀ hW hX hW' _ ih =>
      exact fun r hr => templDAt_of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) (ih r hr)
  | free hW₀ hW _ ih =>
      exact fun r hr => templDAt_of_ag (fun a ha => (own_cell_ag hW a).mpr ha) (ih r hr)
  | store hW₀ hW hW' _ ih =>
      exact fun r hr => templDAt_of_ag
        (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha)) (ih r hr)
  | @immEnd W Y X' W' ps rs ps' rs' r₀ s hs hW₀ hr₀ hc hX' hW' hv hps hrs ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      have hrR : r ∈ rs := by
        obtain ⟨p, hp, hpd⟩ := (hrs r).mp hr
        exact (hTI.2.2.2.2.2.2.1 r).mpr ⟨p, ((hps p).mp hp).1, hpd⟩
      exact templDAt_of_back (ih r hrR) haW fun a' ha' _ m _ _ _ ψ e k =>
        end_back hc hX' hW' haW ha' e k
  | rebEnd r₀ hW₀ hr₀ hle hreb hW hβ ih =>
      intro r hr
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      refine templDAt_of_back (ih r hr) haW fun a' ha' _ m _ _ _ ψ e k => ?_
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := lift_view hcomp e k
      exact ⟨ψ₀, e₀, k₀, w₀.symm⟩
  | rebEndDeep r₀ hW₀ hr₀ hch hle hreb hW hβ ih =>
      intro r hr
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      refine templDAt_of_back (ih r hr) haW fun a' ha' _ m _ _ _ ψ e k => ?_
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := lift_view hcomp e k
      exact ⟨ψ₀, e₀, k₀, w₀.symm⟩

/-- **The canonical image of a chain view agrees with every typed world holding the view.** At
every `β`, the views of `ag(W)` at the own cells of the view's escrow carry the canonical
image's witnesses (the input `[TR]` 6.55 asks for). -/
theorem canonD_escrowAgree {W : WRes} {ps rs : List FrameRec} {r : FrameRec} (hT : TWNC W ps rs)
    (hr : r ∈ rs) {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val}
    (hch₀ : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    (hcell : W.get l₀ = some (CellU.immOf s u₀ w₀ hs))
    (hS : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀)) (β : Life) :
    ∀ a, AgW W a → EscrowAgree w₀ (canonD r S₀ u₀ w₀ β) a := by
  intro a ha m v ψ ψf hown hψ hψf _ hkf
  have hTI := hT.toN.inv
  have hR := (hTI.1.2.2.2.1 r hr).1
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm ha hcell (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ := hTI.1.1 r hr p₀ l₀ S₀ u₀ hch₀ a ha χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  obtain ⟨ζ, eζ, wζ⟩ := canonD_get hψ
  obtain ⟨β₀, x₀, -, -, hden₀, -⟩ := hS
  obtain ⟨ζ', eζ', hpos⟩ := image_dom S₀ hden₀ hw₀den eζ
  rw [hown] at eζ'; cases Option.some.inj eζ'
  obtain ⟨S, hS'⟩ := hpos rfl
  have hch := hch₀.snoc hS' (hw₀own m v hown)
  obtain ⟨ζ'', eζ'', w''⟩ :=
    hT.templD r hr p₀ l₀ S₀ u₀ hch₀ m S v hch a ha χ ψf eχ (by rw [kχ]; simp) hψf hkf
  rw [wχ, eζ] at eζ''
  cases Option.some.inj eζ''
  exact w''.trans wζ.symm

end BoCa.Fig16.LogRel.Core.Chain.SI

end
