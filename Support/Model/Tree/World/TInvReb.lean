import Support.Model.Tree.World.InvReb

/-!
# `TIT` across a reborrow

`[spec §62]`. `Core/Invariant.lean`'s `ti_reb` and `ti_rebDeepN` over `TWNT`: a root reborrow and a
deep one keep `TIT` (`tit_reb`, `tit_rebDeep`), the record-read premises (`RebRecLeT`) in place
of `StratumLe`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus} {Θ : CodeTy}

theorem ClassT.congr {rs : List (FrameRecT K)} {m : BoCa.Loc} {ψ ψ' : TCell K}
    (he : ψ'.erase = ψ.erase) (hw : ψ'.wit = ψ.wit) (h : ClassT rs m ψ) : ClassT rs m ψ' := by
  rcases h with ⟨r, hr, h₁, h₂, h₃⟩ | h
  · exact Or.inl ⟨r, hr, h₁, he.trans h₂, hw.trans h₃⟩
  · exact Or.inr h

theorem coverage_of_icp {W W' aW : TRes K} {rs : List (FrameRecT K)} (haW : AgWT W aW)
    (hC : CoverageT W rs) (t : ∀ a', AgWT W' a' → ∀ m, ICpAt aW a' m) : CoverageT W' rs := by
  intro a' ha' m ψ e hk
  obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := t a' ha' m ψ e hk
  exact (hC aW haW m ζ eζ kζ).congr rζ.symm wζ.symm

/-- A lineage member's `LeInvW` and `ExIn` from `LeInv` at the records proper. -/
theorem leInvW_of {W : TRes K} {ps rs : List (FrameRecT K)} (hl : LeInvT W ps)
    (hmem : ∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescRT p x) : LeInvW W rs := by
  intro r hr
  obtain ⟨p, hp, hd⟩ := (hmem r).mp hr
  exact (lineage_of_leInv hl hp hd).2

theorem exIn_of {W : TRes K} {ps rs : List (FrameRecT K)} (hl : LeInvT W ps)
    (hmem : ∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescRT p x) {r : FrameRecT K} (hr : r ∈ rs) : ExIn W r.R := by
  obtain ⟨p, hp, hd⟩ := (hmem r).mp hr
  exact (lineage_of_leInv hl hp hd).1

/-- A reborrow keeps `NestLife` and `NoMut`. -/
theorem nm_reb_like {W W' c w₀ : TRes K} {ps rs : List (FrameRecT K)} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life}
    (hvW : ResUT.Valid W) (hle : W.get le = some (CellUT.immOf s v w₀ hs))
    (hreb : ResUT.Reb β w₀ c) (hW : ResUT.CompS W c W')
    (hN : ∀ r ∈ rs, NestLifeT K W r) (hM : NoMutT W ps rs)
    (newOwn : ∀ aW, AgWT W aW → ∀ a', AgWT W' a' → ∀ r ∈ rs, ∀ l₀ m S u,
      ChainT r.R r.T r.v (some l₀) m S u → ∀ u', w₀.get m = some (CellUT.ownOf u') →
      (∃ φ, c.get m = some φ) →
      ∃ (ζ : TCell K) (t : TSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOfI = some t ∧
        y ∈ t.set ∧ K.lt β y) :
    (∀ r ∈ rs, NestLifeT K W' r) ∧ NoMutT W' ps rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have tm : ∀ x, MutAtT W' x → MutAtT W x := by
    intro x hm
    rcases MutAtT.split hW hm with h₁ | h₂
    · exact h₁
    · exact mutAt_of_cell hle (mutAt_image hreb h₂)
  refine ⟨fun r hr => ?_, ⟨fun r hr hm => hM.1 r hr (tm _ hm),
    fun r hr l u hl hm => hM.2 r hr l u hl (tm _ hm)⟩⟩
  refine nestLife_of_maps (hN r hr) haW (fun a' ha' l₀ m S u hc ψ s' x e hs' hx => ?_)
    (fun a' ha' l₀ m S u hc ζ t y e ht hy => ?_)
  · obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgWT.split hW).mp ha'
    rw [AgWT.functional haW' haW] at hcomp
    rcases ResUT.CompR.lsOf_inv hcomp e hs' hx with ⟨ξ, t₁, e₁, ht₁, hx₁⟩ |
        ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · exact Or.inl ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · rcases img_ls haW hle hreb (fun _ _ e => e) hac e₁ ht₁ hx₁ with hl | ⟨rfl, hφ, ζ, eζ, kζ⟩
      · exact Or.inl hl
      · right
        rcases CellUT.rep' ζ with ⟨u', rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, _, v₁, χ₁, h₁, P, hw, rfl⟩
        · exact newOwn aW haW a' ha' r hr l₀ m S u hc u' eζ hφ
        · exact absurd (CellUT.kind_immOf _ _ _ _) kζ
        · exact (hM.2 r hr m u hc.own
            (mutAt_of_cell hle (MutAtT.top eζ (by simp)))).elim
  · obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgWT.split hW).mp ha'
    rw [AgWT.functional haW' haW] at hcomp
    exact (icpAt_left hcomp l₀ ζ e).ls ht hy

/-- A reborrow's coverage: a view over an `imm` cell of the escrow copies a classified
cell; one over an `own` cell is at a chain position (`newOwn`); one over a `mut` cell is at a
sub-record's location (`newMut`), where `ag(W′)` holds the sub-record's value and witness. -/
theorem cov_reb_like {W W' c w₀ : TRes K} {rs : List (FrameRecT K)} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life} (hvW : ResUT.Valid W)
    (hle : W.get le = some (CellUT.immOf s v w₀ hs)) (hreb : ResUT.Reb β w₀ c)
    (hW : ResUT.CompS W c W') (hC : CoverageT W rs) (hLW : LeInvW W' rs)
    (newOwn : ∀ m u, w₀.get m = some (CellUT.ownOf u) → (∃ ψ, c.get m = some ψ) →
      ∃ r ∈ rs, ∃ p S u', ChainT r.R r.T r.v p m S u')
    (newMut : ∀ m (ζ : TCell K), w₀.get m = some ζ → ζ.kind = Kind.mut →
      (∃ ψ, c.get m = some ψ) → ∃ d ∈ rs, d.le = m) : CoverageT W' rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  intro a' ha' m ψ e hk
  obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgWT.split hW).mp ha'
  rw [AgWT.functional haW' haW] at hcomp
  rcases imm_back_full hcomp e hk with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · exact (hC aW haW m ψ₁ e₁ k₁).congr r₁.symm w₁.symm
  · obtain ⟨d', bi, hdb, hbi, hd'⟩ := img_walk haW hle hreb (fun _ _ e => e) hac
    rcases imm_back_full hdb e₁ k₁ with ⟨ψ₂, e₂, k₂, r₂, w₂⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
    · have ec := hd' m ψ₂ e₂
      rcases img_cell haW hle hreb ec with hi | ⟨⟨ζ, eζ, kζ⟩, -⟩
      · obtain ⟨ξ, eξ, kξ, rξ, wξ, -⟩ := hi k₂
        exact (hC aW haW m ξ eξ kξ).congr (r₁.symm.trans (r₂.symm.trans rξ.symm))
          (w₁.symm.trans (w₂.symm.trans wξ.symm))
      · rcases CellUT.rep' ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, _, v₁, χ₁, h₁, P, hw, rfl⟩
        · exact Or.inr (newOwn m u eζ ⟨_, ec⟩)
        · exact absurd (CellUT.kind_immOf _ _ _ _) kζ
        · obtain ⟨d, hd, hdm⟩ := newMut m _ eζ (by simp) ⟨_, ec⟩
          obtain ⟨ψ', e', -, r', w'⟩ := hLW d hd a' ha'
          rw [hdm, e] at e'; cases Option.some.inj e'
          exact Or.inl ⟨d, hd, hdm.symm, r', w'⟩
    · obtain ⟨ξ, eξ, kξ, rξ, wξ, -⟩ := hbi m ψ₂ e₂ k₂
      exact (hC aW haW m ξ eξ kξ).congr (r₁.symm.trans (r₂.symm.trans rξ.symm))
        (w₁.symm.trans (w₂.symm.trans wξ.symm))

/-- A reborrow at any record keeps `TI`. -/
theorem tit_reb {W W' c : TRes K} {ps rs : List (FrameRecT K)} {r₀ : FrameRecT K} {le : BoCa.Loc} {s : TSet}
    {β : Life} {hs : r₀.R.InStratum s}
    (hvW : ResUT.Valid W) (hr₀ : r₀ ∈ rs) (hle : W.get le = some (CellUT.immOf s r₀.v r₀.R hs)) (hreb : ResUT.Reb β r₀.R c)
    (hden : ((r₀.T.immReborrow β).interp Θ).P K r₀.v c)
    (hW : ResUT.CompS W c W') (hv : ResUT.Valid W') (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  have hR₀ := (h3.2.2.2.1 r₀ hr₀)
  have hl' := leInv_of_reb hvW hW hl
  obtain ⟨hN', hM'⟩ := nm_reb_like hvW hle hreb hW hN hM
    (fun aW haW a' ha' r hr l₀ m S u hc u' hown hφ => by
      have e₁ : r = r₀ := h3.2.2.1 r hr r₀ hr₀ m u u' hc.own hown
      subst e₁
      obtain ⟨φ, eφ⟩ := hφ
      obtain ⟨ζ, eζ, hpos⟩ := image_domT Θ β r.T hden hR₀ eφ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S', hS'⟩ := hpos rfl
      exact absurd (chain_unique_recT hR₀ hc (ChainT.one hS' hown)).1 (by simp))
  refine ⟨chainInv_reb hvW hr₀ hle hreb hden hW hv h3, hl', hid, hio, hN', hM', hmem, ?_⟩
  refine cov_reb_like hvW hle hreb hW hC (leInvW_of hl' hmem) (fun m u eζ ⟨ψ, ec⟩ => ?_)
    (fun m ζ eζ kζ ⟨ψ, ec⟩ => ?_)
  · obtain ⟨ζ', eζ', hpos⟩ := image_domT Θ β r₀.T hden hR₀ ec
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨r₀, hr₀, none, S, u, ChainT.one hS eζ⟩
  · obtain ⟨S, hS⟩ := image_dom_mutT Θ β r₀.T hden hR₀ ec eζ kζ
    obtain ⟨p, hp, hpr⟩ := (hmem r₀).mp hr₀
    refine ⟨⟨m, ζ.erase, ζ.wit, S⟩, (hmem _).mpr ⟨p, hp, hpr.sub ?_⟩, rfl⟩
    exact ⟨GPosT.here hS, ζ, eζ, kζ, rfl, rfl⟩

/-- `ti_rebDeep` with `W ∈ Res_β` read where it is used: at the view's own cell, which is longer
than `β`. -/
theorem tit_rebDeep {W W' c : TRes K} {ps rs : List (FrameRecT K)} {r₀ : FrameRecT K} {p₀ : Option BoCa.Loc}
    {l₁ : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val} {s : TSet} {w₀ : TRes K} {hs : w₀.InStratum s}
    {β : Life}
    (hvW : ResUT.Valid W) (hr₀ : r₀ ∈ rs) (hch₀ : ChainT r₀.R r₀.T r₀.v p₀ l₁ S₀ u₀)
    (hcell : W.get l₁ = some (CellUT.immOf s u₀ w₀ hs))
    (hreb : ResUT.Reb β w₀ c) (hden : ((S₀.immReborrow β).interp Θ).P K u₀ c)
    (hβc : RebCellLeT K W l₁ β) (hW : ResUT.CompS W c W') (hv : ResUT.Valid W') (h : TIT K Θ W ps rs) :
    TIT K Θ W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  have hR₀ := (h3.2.2.2.1 r₀ hr₀)
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgWT.get_imm haW hcell (CellUT.kind_immOf _ _ _ _)
  rw [CellUT.wit_immOf] at wχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
    h3.1 r₀ hr₀ p₀ l₁ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  have hl' := leInv_of_reb hvW hW hl
  obtain ⟨hN', hM'⟩ := nm_reb_like hvW hcell hreb hW hN hM
    (fun aW₁ haW₁ a' ha' r hr l₀ m S u hc u' hown hφ => by
      rw [AgWT.functional haW₁ haW] at *
      have e₁ : r = r₀ := h3.2.2.1 r hr r₀ hr₀ m u u' hc.own (hw₀own m u' hown)
      subst e₁
      obtain ⟨φ, eφ⟩ := hφ
      obtain ⟨ζ, eζ, hpos⟩ := image_domT Θ β S₀ hden hw₀den eφ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S', hS'⟩ := hpos rfl
      have hl := (chain_unique_recT hR₀ hc (hch₀.snoc hS' (hw₀own m u' hown))).1
      have hl' : l₀ = l₁ := Option.some.inj hl
      subst hl'
      obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgWT.split hW).mp ha'
      rw [AgWT.functional haW' haW] at hcomp
      obtain ⟨ψ₁, t₁, y, e₁, ht₁, hy₁, hβy⟩ := hβc aW haW
      obtain ⟨ξ, t, eξ, ht, hy⟩ := (icpAt_left hcomp l₀ ψ₁ e₁).ls ht₁ hy₁
      exact ⟨ξ, t, y, eξ, ht, hy, hβy⟩)
  refine ⟨chainInv_rebDeep hvW hr₀ hch₀ hcell hreb hden hW hv h3, hl', hid, hio, hN', hM', hmem,
    ?_⟩
  refine cov_reb_like hvW hcell hreb hW hC (leInvW_of hl' hmem) (fun m u eζ ⟨ψ, ec⟩ => ?_)
    (fun m ζ eζ kζ ⟨ψ, ec⟩ => ?_)
  · obtain ⟨ζ', eζ', hpos⟩ := image_domT Θ β S₀ hden hw₀den ec
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨r₀, hr₀, some l₁, S, u, hch₀.snoc hS (hw₀own m u eζ)⟩
  · obtain ⟨S, hS⟩ := image_dom_mutT Θ β S₀ hden hw₀den ec eζ kζ
    have hg : GPosT r₀.R r₀.T r₀.v m S := GPosT.of_chain hch₀ hS
    obtain ⟨ζ', eζ', kζ', -⟩ := gpos_mut_cellT Θ hg hR₀ (fun _ _ e => e)
    obtain ⟨p, hp, hpr⟩ := (hmem r₀).mp hr₀
    refine ⟨⟨m, ζ'.erase, ζ'.wit, S⟩, (hmem _).mpr ⟨p, hp, hpr.sub ?_⟩, rfl⟩
    exact ⟨hg, ζ', eζ', kζ', rfl, rfl⟩

end BoCa.Fig16.Tree.Wp

end
