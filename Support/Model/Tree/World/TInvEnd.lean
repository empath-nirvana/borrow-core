import Support.Model.Tree.World.TInvFrame

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus} {Θ : CodeTy}

theorem le_of_compS_left {a b c : TRes K} (h : ResUT.CompS a b c) : ResUT.Le a c := ⟨b, h⟩
/-- The walks of the two configurations of the end of a borrow, named once:
`W = ℓ ↦ imm(s, v, R) ● Y`, `W′ = (ℓ ↦ own(v) ● R) ● Y`. -/
theorem end_walks {W W' Y X' R : TRes K} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : R.InStratum s}
    (hc : ResUT.CompS (ResUT.single l (CellUT.immOf s v R hs)) Y W)
    (hX' : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hW' : ResUT.CompS X' Y W')
    {aW a' : TRes K} (haW : AgWT W aW) (ha' : AgWT W' a') :
    ∃ aσ aY eR aR pR, ExRT R eR ∧ AgWT R aR ∧ ResUT.CompR eR aR pR ∧
      ResUT.CompR (ResUT.single l (CellUT.immOf s v R hs)) pR aσ ∧
      ResUT.CompR aσ aY aW ∧ ResUT.CompR aR aY a' := by
  obtain ⟨aσ, aY, hσ, hY, hσY⟩ := (AgWT.split hc).mp haW
  obtain ⟨eR, aR, pR, heR, haR, hpR, hcp⟩ := AgWT.single_imm_inv hσ
  obtain ⟨x', y', hx', hy', hxy'⟩ := (AgWT.split hW').mp ha'
  have hx'' : AgWT R x' := (own_cell_ag hX' x').mp hx'
  rw [AgWT.functional hx'' haR, AgWT.functional hy' hY] at hxy'
  exact ⟨aσ, aY, eR, aR, pR, heR, haR, hpR, hcp, hσY, hxy'⟩

/-- A view of `ag(W′)` after the end of a borrow is a view of `ag(W)` over the same witness. -/
theorem end_back {W W' Y X' R : TRes K} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : R.InStratum s}
    (hc : ResUT.CompS (ResUT.single l (CellUT.immOf s v R hs)) Y W)
    (hX' : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hW' : ResUT.CompS X' Y W')
    {aW a' : TRes K} (haW : AgWT W aW) (ha' : AgWT W' a') {m : BoCa.Loc} {ψ : TCell K}
    (e : a'.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀ : TCell K, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨aσ, aY, eR, aR, pR, -, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  rcases back_view hRY e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r hpR e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hcp e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hσY e₃ k₃
    exact ⟨ψ₄, e₄, k₄, by rw [w₁, ← w₂, ← w₃, ← w₄]⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hσY e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₁.trans w₄.symm⟩

/-- An `imm` view of `ag(W)` away from `ℓ` survives the end of the borrow at `ℓ`, over the same
value and witness: the only views that go are `ℓ`'s own and `ex(R)_○`'s, which has none. -/
theorem end_fwd_imm {W W' Y X' R : TRes K} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : R.InStratum s}
    (hc : ResUT.CompS (ResUT.single l (CellUT.immOf s v R hs)) Y W)
    (hX' : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hW' : ResUT.CompS X' Y W')
    {aW a' : TRes K} (haW : AgWT W aW) (ha' : AgWT W' a') {m : BoCa.Loc} (hm : m ≠ l)
    {ψ₀ : TCell K} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨aσ, aY, eR, aR, pR, heR, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  rcases imm_back_full hσY e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · rcases imm_back_full hcp e₁ k₁ with ⟨ψ₂, e₂, -, -, -⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
    · exact absurd (ResUT.single_get_eq_some e₂).1 hm
    · rcases imm_back_full hpR e₂ k₂ with ⟨ψ₃, e₃, k₃, -, -⟩ | ⟨ψ₃, e₃, k₃, r₃, w₃⟩
      · exact absurd k₃ (ExRT.immFree heR m ψ₃ e₃)
      · obtain ⟨ψ, e, k, r, w⟩ := imm_fwd_full_l hRY e₃ k₃
        exact ⟨ψ, e, k, r.trans (r₃.trans (r₂.trans r₁)), w.trans (w₃.trans (w₂.trans w₁))⟩
  · obtain ⟨ψ, e, k, r, w⟩ := imm_fwd_full_r hRY e₁ k₁
    exact ⟨ψ, e, k, r.trans r₁, w.trans w₁⟩

/-- A non-`imm` cell reached through `mut` witnesses from a `●`-part of `C` is in `ex(C)_●`. -/
theorem xpath_ex_part {A C e : TRes K} (hle : ResUT.Le A C) (he : ExST C e) {p : List BoCa.Loc}
    {σ : TRes K} (hp : XPath A p σ) {x : BoCa.Loc} {ζ : TCell K} (ex : σ.get x = some ζ)
    (k : ζ.kind ≠ Kind.imm) : e.get x = some ζ := by
  obtain ⟨τ, hτ⟩ := hle
  cases hp with
  | nil => exact ExST.get_of_ne_imm he (ResUT.CompS.get_left_of_ne_imm hτ ex k).2 k
  | cons em km hq =>
      have eC := (ResUT.CompS.get_left_of_ne_imm hτ em (by rw [km]; simp)).2
      exact xpath_ex he (XPath.cons eC km hq) ex k

/-- `immEnd` keeps `TI`. -/
theorem tit_end {W Y X' W' : TRes K} {ps rs ps' rs' : List (FrameRecT K)} {r : FrameRecT K} {s : TSet}
    {hs : r.R.InStratum s} (hvW : ResUT.Valid W) (hr : r ∈ ps)
    (hc : ResUT.CompS (ResUT.single r.le (CellUT.immOf s r.v r.R hs)) Y W)
    (hX' : ResUT.CompS (ResUT.single r.le (CellUT.ownOf r.v)) r.R X') (hW' : ResUT.CompS X' Y W')
    (hv : ResUT.Valid W') (hps : ∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r))
    (hrs : ∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescRT p d) (h : TIT K Θ W ps rs) : TIT K Θ W' ps' rs' := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hled, hio, hN, hM, hmem, hC⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  have hrR : r ∈ rs := (hmem r).mpr ⟨r, hr, DescRT.refl r⟩
  have sub : ∀ d, d ∈ rs' → d ∈ rs := by
    intro d hd
    obtain ⟨p, hp, hpd⟩ := (hrs d).mp hd
    exact (hmem d).mpr ⟨p, ((hps p).mp hp).1, hpd⟩
  -- a record of `rs` not in `rs'` is in `r`'s lineage
  have gone_desc : ∀ d, d ∈ rs → d ∉ rs' → DescRT r d := by
    intro d hd hd'
    obtain ⟨p, hp, hpd⟩ := (hmem d).mp hd
    by_cases hpr : p = r
    · subst hpr; exact hpd
    · exact absurd ((hrs d).mpr ⟨p, (hps p).mpr ⟨hp, hpr⟩, hpd⟩) hd'
  -- the lineage's non-`imm` cells are out of `ag(W′)`
  have hleR : ResUT.Le r.R W' := (le_of_compS_right hX').trans (le_of_compS_left hW')
  obtain ⟨σ', eW', aW', heW', haW', -⟩ := id hv
  have gone : ∀ d, DescRT r d → ∀ x (ζ : TCell K), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → ∀ a, AgWT W' a → a.get x = none := by
    rintro d ⟨p, hp⟩ x ζ e k a ha
    have ex := xpath_ex_part hleR heW' hp.xpath e k
    cases ea : a.get x with
    | none => rfl
    | some ξ =>
        rw [AgWT.functional ha haW'] at ea
        exact (ex_ag_disjoint hv heW' haW' ex ea).elim
  have ne : ∀ r' ∈ rs', ∀ m u, r'.R.get m = some (CellUT.ownOf u) → m ≠ r.le := by
    intro r' hr' m u hm e
    subst e
    exact hio r hrR r' (sub r' hr') u hm
  have back : ∀ a', AgWT W' a' → ∀ m (ψ : TCell K), a'.get m = some ψ →
      ψ.kind ≠ Kind.own →
      ∃ ψ₀ : TCell K, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit :=
    fun a' ha' m ψ e hk => end_back hc hX' hW' haW ha' e hk
  have fwd : ∀ a', AgWT W' a' → ∀ m, m ≠ r.le → ∀ (ψ₀ : TCell K), aW.get m = some ψ₀ →
      ψ₀.kind = Kind.imm →
      ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit :=
    fun a' ha' m hm ψ₀ e₀ k₀ => end_fwd_imm hc hX' hW' haW ha' hm e₀ k₀
  have hleI : LeInvT W' ps' := by
    intro r' hr' a₁ ha₁
    have hr'' := (hps r').mp hr'
    have hne : r'.le ≠ r.le := fun e => hr''.2 (hled r' hr''.1 r hr e)
    obtain ⟨ψ₀, e₀, k₀, r₀', w₀⟩ := hle r' hr''.1 aW haW
    obtain ⟨ψ, e, k, r₁, w₁⟩ := fwd a₁ ha₁ r'.le hne ψ₀ e₀ k₀
    exact ⟨ψ, e, k, r₁.trans r₀', w₁.trans w₀⟩
  have chainFwd : ∀ r' ∈ rs', ∀ p m S u, ChainT r'.R r'.T r'.v p m S u → ∀ a', AgWT W' a' →
      ∀ (ψ₀ : TCell K), aW.get m = some ψ₀ → ψ₀.kind ≠ Kind.own →
      ∃ ψ, a'.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro r' hr' p m S u hch a' ha' ψ₀ e₀ k₀
    obtain ⟨kk, -⟩ := h1 r' (sub r' hr') p m S u hch aW haW ψ₀ e₀ k₀
    obtain ⟨ψ, e, k, -, w⟩ := fwd a' ha' m (ne r' hr' m u hch.own) ψ₀ e₀ kk
    exact ⟨ψ, e, by rw [k]; simp, w⟩
  obtain ⟨aσ, aY, eR, aR, pR, heR, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  have backI : ∀ m, ICpAt aW a' m := fun m =>
    icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have fwdI : ∀ m, m ≠ r.le → ICpAt a' aW m := fun m hm =>
    icpAt_comp hσY (icpAt_comp hcp (icpAt_none (single_ne _ hm))
      (icpAt_comp hpR (icpAt_of_immFree (ExRT.immFree heR) m) (icpAt_left hRY m)))
      (icpAt_right hRY m)
  have tm : ∀ x, MutAtT W' x → MutAtT W x := by
    intro x hm
    rcases MutAtT.split hW' hm with h₁ | h₂
    · rcases MutAtT.split hX' h₁ with h₃ | h₃
      · exact (not_mutAt_single_own _ _ _ h₃).elim
      · exact MutAtT.of_compS_left hc
          (MutAtT.nest (ResUT.single_get_self _ _) (by simp) (by rw [CellUT.wit_immOf]; exact h₃))
    · exact MutAtT.of_compS_right hc h₂
  refine ⟨⟨fun r' hr' => ?_, fun r' hr' m u hm a₁ ha₁ => ?_,
    fun r₁ hr₁ r₂ hr₂ => h3 r₁ (sub r₁ hr₁) r₂ (sub r₂ hr₂),
    fun r' hr' => h4 r' (sub r' hr'), fun r' hr' => ?_, fun r' hr' => ?_⟩, hleI,
    fun r₁ hr₁ r₂ hr₂ => hled r₁ ((hps r₁).mp hr₁).1 r₂ ((hps r₂).mp hr₂).1,
    fun r₁ hr₁ r₂ hr₂ => hio r₁ (sub r₁ hr₁) r₂ (sub r₂ hr₂), fun r' hr' => ?_,
    ⟨fun r' hr' hm => hM.1 r' ((hps r').mp hr').1 (tm _ hm),
     fun r' hr' l u hl hm => hM.2 r' (sub r' hr') l u hl (tm _ hm)⟩, hrs, ?_⟩
  -- DeepInv
  · have hr'' := sub r' hr'
    intro p m S u hch a₁ ha₁ ψ e hk
    obtain ⟨ψ₀, e₀, k₀, w₀⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨kk, d, o, b₁, b₂⟩ := h1 r' hr'' p m S u hch aW haW ψ₀ e₀ k₀
    obtain ⟨ψ', e', k', -, -⟩ := fwd a₁ ha₁ m (ne r' hr' m u hch.own) ψ₀ e₀ kk
    rw [e] at e'; cases Option.some.inj e'
    refine ⟨k', w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
    obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
    obtain ⟨p₀, S₀, u₀, hch₀, -⟩ := chain_lastT hch l₀ hp
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := chainFwd r' hr' p₀ l₀ S₀ u₀ hch₀ a₁ ha₁ ψ₁ e₁ k₁
    exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩
  -- support, from the lineage
  · exact exIn_support (exIn_of hleI hrs hr') hm (by simp) a₁ ha₁
  -- JointAt
  · have hr'' := sub r' hr'
    rintro ⟨S, m, u, hR, a₁, ha₁, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨β₀, c₀, q2, q3, q4, q5⟩ := h5 r' hr'' ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, c₀, q2, q3, q4, fun S' m' u' hR' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back a₂ ha₂ m' ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- JointDeep
  · have hr'' := sub r' hr'
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hch, a₁, ha₁, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨w₀, hw₀, β₀, c₀, q2, q3, q4, q5⟩ :=
      h6 r' hr'' p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hch, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨w₀, fun a₂ ha₂ => ?_, β₀, c₀, q2, q3, q4,
      fun m' S' u' hc' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
      obtain ⟨ψ₃, e₃, k₃, w₃⟩ := chainFwd r' hr' p₀ l₀ S₀ u₀ hc₀ a₂ ha₂ ψ₂ e₂ k₂
      exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back a₂ ha₂ m' ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- NestLife
  · have hr'' := sub r' hr'
    refine nestLife_of_icp (hN r' hr'') haW
      (fun a₁ ha₁ l₀ m S u hc => by rw [AgWT.functional ha₁ ha']; exact backI m)
      (fun a₁ ha₁ l₀ m S u hcm => ?_)
    rw [AgWT.functional ha₁ ha']
    refine fwdI l₀ (fun hl₀ => ?_)
    obtain ⟨p₀, S₀, u₀, hch₀, -⟩ := chain_lastT hcm l₀ rfl
    have hown := hch₀.own
    rw [hl₀] at hown
    exact hio r hrR r' hr'' u₀ hown
  -- coverage
  · intro a₁ ha₁ m ψ e hk
    obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := backI m ψ (by rw [← AgWT.functional ha₁ ha']; exact e) hk
    rcases hC aW haW m ζ eζ kζ with ⟨r', hr', h₁, h₂, h₃⟩ | ⟨r', hr', p, S, u, hch⟩
    · by_cases hin : r' ∈ rs'
      · exact Or.inl ⟨r', hin, h₁, rζ.symm.trans h₂, wζ.symm.trans h₃⟩
      · exfalso
        have hd := gone_desc r' hr' hin
        rcases hd.cases with rfl | ⟨q, hq, hqq⟩
        · have e₁ := (ResUT.CompS.get_left_of_ne_imm hW'
            (ResUT.CompS.get_left_of_ne_imm hX' (ResUT.single_get_self _ _) (by simp)).2
            (by simp)).2
          rw [← h₁] at e₁
          rw [ag_none_of_top hv ha₁ e₁ (by simp)] at e; cases e
        · obtain ⟨d', hd', -, ξ, eξ, kξ, -⟩ := hqq.last hq
          rw [h₁, gone d' hd' _ ξ eξ (by rw [kξ]; simp) a₁ ha₁] at e; cases e
    · by_cases hin : r' ∈ rs'
      · exact Or.inr ⟨r', hin, p, S, u, hch⟩
      · exfalso
        have hd := gone_desc r' hr' hin
        rw [gone r' hd _ _ hch.own (by simp) a₁ ha₁] at e; cases e

/-- `ti_endReb` with `RebEndRec` in place of `W′ ∈ Res_β`. -/
theorem tit_endReb {W W' c w₀ : TRes K} {ps rs : List (FrameRecT K)} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life}
    (hvW : ResUT.Valid W) (hle : W'.get le = some (CellUT.immOf s v w₀ hs))
    (hreb : ResUT.Reb β w₀ c) (hW : ResUT.CompS W' (c.restrictDom w₀.exclPart) W)
    (hβ : RebEndRecT K W' rs w₀ β)
    (hexcl : ∀ r ∈ rs, ∀ u, w₀.get r.le ≠ some (CellUT.ownOf u))
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle4, hid, hio, hN, hM, hmem, hC⟩ := h
  have hv : ResUT.Valid W' := (ResUT.Valid.split hW hvW).1
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  obtain ⟨a'', acr, ha'', hacr, hcomp⟩ := (AgWT.split hW).mp haW
  rw [AgWT.functional ha'' ha'] at hcomp
  have crSrc : ∀ x (ψ : TCell K), (c.restrictDom w₀.exclPart).get x = some ψ →
      c.get x = some ψ ∧ ∃ ζ : TCell K, w₀.get x = some ζ ∧ ζ.kind ≠ Kind.imm := by
    intro x ψ e
    cases ex : w₀.exclPart.get x with
    | none => rw [ResUT.restrictDom_get_of_none ex] at e; cases e
    | some ζ =>
        rw [ResUT.restrictDom_get_of_some ex] at e
        exact ⟨e, ζ, (ResUT.exclPart_eq_some.mp ex).1, (ResUT.exclPart_eq_some.mp ex).2⟩
  obtain ⟨d', bi, hdb, hbi, hd'⟩ :=
    img_walk ha' hle hreb (fun x ψ e => (crSrc x ψ e).1) hacr
  have R1 : ∀ m (ψ : TCell K), a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : TCell K, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro m ψ e hk
    obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp e hk
    exact ⟨ψ₀, e₀, k₀, w₀'.symm⟩
  have R3 : ∀ m (ψ₀ : TCell K), (c.restrictDom w₀.exclPart).get m = none →
      aW.get m = some ψ₀ → ψ₀.kind = Kind.imm →
      ∃ ψ : TCell K, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧
        ψ.wit = ψ₀.wit := by
    intro m ψ₀ hn e₀ k₀
    rcases imm_back_full hcomp e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · exact ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · rcases imm_back_full hdb e₁ k₁ with ⟨ψ₂, e₂, -, -, -⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
      · have := hd' m ψ₂ e₂; rw [hn] at this; cases this
      · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := hbi m ψ₂ e₂ k₂
        exact ⟨ζ, eζ, kζ, rζ.trans (r₂.trans r₁), wζ.trans (w₂.trans w₁)⟩
  have R4 : ∀ m (ζ : TCell K) t y, aW.get m = some ζ → ζ.lsOfI = some t → y ∈ t.set →
      (∃ (ζ' : TCell K) (t' : TSet), a'.get m = some ζ' ∧ ζ'.lsOfI = some t' ∧ y ∈ t'.set) ∨
      (y = β ∧ ∃ ζ : TCell K, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
    intro m ζ t y e ht hy
    rcases ResUT.CompR.lsOf_inv hcomp e ht hy with h' | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
    · exact Or.inl h'
    · rcases ResUT.CompR.lsOf_inv hdb e₁ ht₁ hy₁ with ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩ |
          ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩
      · obtain ⟨ec, ζw, eζw, kζw⟩ := crSrc m ξ₂ (hd' m ξ₂ e₂)
        rcases reb_cell_ls hreb ec with ⟨-, hl⟩ | ⟨ζ₃, eζ₃, kζ₃, -⟩
        · rw [hl] at ht₂; cases Option.some.inj ht₂; exact Or.inr ⟨by simpa [TSet.single_set] using hy₂, ζw, eζw, kζw⟩
        · rw [eζ₃] at eζw; cases Option.some.inj eζw; exact absurd kζ₃ kζw
      · exact Or.inl ((hbi m ξ₂ e₂).ls ht₂ hy₂)
  have tm : ∀ x, MutAtT W' x → MutAtT W x := fun x hm => MutAtT.of_compS_left hW hm
  have kimm : ∀ r ∈ rs, ∀ p m S u, ChainT r.R r.T r.v p m S u → ∀ ψ : TCell K,
      a'.get m = some ψ → ψ.kind ≠ Kind.own → ψ.kind = Kind.imm := by
    intro r hr p m S u hc ψ e hk
    cases hkk : ψ.kind with
    | own => exact absurd hkk hk
    | imm => rfl
    | «mut» => exact (hM.2 r hr m u hc.own (tm _ (agW_mut ha' m ψ e hkk))).elim
  have hN' : ∀ r ∈ rs, NestLifeT K W' r := by
    intro r hr l₀ m S u hc a₁ ha₁ ψ s' e hs' x hx
    rw [AgWT.functional ha₁ ha'] at e ⊢
    obtain ⟨ζ, t, eζ, ht, hxt⟩ := (icpAt_left hcomp m ψ e).ls hs' hx
    obtain ⟨ζ₀, t₀, y, e₀, ht₀, hy, hxy⟩ := hN r hr l₀ m S u hc aW haW ζ t eζ ht x hxt
    rcases R4 l₀ ζ₀ t₀ y e₀ ht₀ hy with ⟨ζ', t', e', ht', hy'⟩ | hβy
    · exact ⟨ζ', t', y, e', ht', hy', hxy⟩
    · obtain ⟨rfl, hex⟩ := hβy
      exact hβ r hr l₀ m S u hc hex a' ha' ψ s' e hs' x hx hxy
  have parent : ∀ r ∈ rs, ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
      ∀ ψ : TCell K, a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ : TCell K, a'.get l₀ = some ζ ∧ ζ.kind ≠ Kind.own := by
    intro r hr l₀ m S u hc ψ e hk
    obtain ⟨s', hs'⟩ := lsOf_of_imm (kimm r hr _ m S u hc ψ e hk)
    obtain ⟨ζ, t, y, eζ, ht, -, -⟩ := hN' r hr l₀ m S u hc a' ha' ψ s' e hs' s'.ne.choose s'.ne.choose_spec
    exact ⟨ζ, eζ, by rw [CellUT.kind_of_lsOf ht]; simp⟩
  have hD' : ∀ r ∈ rs, DeepInvT K Θ W' r := by
    intro r hr p m S u hc a₁ ha₁ ψ e hk
    rw [AgWT.functional ha₁ ha'] at e ⊢
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
  have hle' : LeInvT W' ps := by
    intro r hr a₁ ha₁
    rw [AgWT.functional ha₁ ha']
    obtain ⟨ψ₀, e₀, k₀, r₀, w₀''⟩ := hle4 r hr aW haW
    have hrR : r ∈ rs := (hmem r).mpr ⟨r, hr, DescRT.refl r⟩
    have hn : (c.restrictDom w₀.exclPart).get r.le = none := by
      cases ecr : (c.restrictDom w₀.exclPart).get r.le with
      | none => rfl
      | some φ =>
          exfalso
          obtain ⟨-, ζ, eζ, kζ⟩ := crSrc _ _ ecr
          rcases CellUT.rep' ζ with ⟨u', rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ |
              ⟨b₁, _, v₁, χ₁, h₁, P, hw, rfl⟩
          · exact hexcl r hrR u' eζ
          · exact kζ (CellUT.kind_immOf _ _ _ _)
          · exact hM.1 r hr (tm _ (mutAt_of_cell hle (MutAtT.top eζ (by simp))))
    obtain ⟨ψ, e, k, rr, ww⟩ := R3 r.le ψ₀ hn e₀ k₀
    exact ⟨ψ, e, k, rr.trans r₀, ww.trans w₀''⟩
  have h5' : ∀ r ∈ rs, JointAtT K Θ W' r := by
    intro r hr
    rintro ⟨S, m, u, hR, a₁, ha₁, ψ, e, hk⟩
    rw [AgWT.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨β₀, c₀, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, c₀, q2, q3, q4, fun S' m' u' hR' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgWT.functional ha₂ ha'] at e₁
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  have h6' : ∀ r ∈ rs, JointDeepT K Θ W' r := by
    intro r hr
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a₁, ha₁, ψ, e, hk⟩
    rw [AgWT.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨w₁, hw₁, β₀, c₀, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
    obtain ⟨ζ, eζ, kζ⟩ := parent r hr l₀ m S u hc ψ e hk
    obtain ⟨ζ₀, eζ₀, -, wζ⟩ := R1 l₀ ζ eζ kζ
    obtain ⟨ψ₂, e₂, -, w₂⟩ := hw₁ aW haW
    rw [eζ₀] at e₂; cases Option.some.inj e₂
    refine ⟨w₁, fun a₂ ha₂ => ⟨ζ, by rw [AgWT.functional ha₂ ha']; exact eζ, kζ, wζ.trans w₂⟩,
      β₀, c₀, q2, q3, q4, fun m' S' u' hc' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgWT.functional ha₂ ha'] at e₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ', eζ', wζ'⟩ := q5 m' S' u' hc' aW haW ψ₃ e₃ k₃
    exact ⟨ζ', eζ', w₃.trans wζ'⟩
  have h2' : ∀ r ∈ rs, ∀ m u, r.R.get m = some (CellUT.ownOf u) → ∀ a, AgWT W' a →
      ∃ ζ, a.get m = some ζ :=
    fun r hr m u hm => exIn_support (exIn_of hle' hmem hr) hm (by simp)
  refine ⟨⟨hD', h2', h3, h4, h5', h6'⟩, hle', hid, hio, hN',
    ⟨fun r hr hm => hM.1 r hr (tm _ hm), fun r hr l u hl hm => hM.2 r hr l u hl (tm _ hm)⟩,
    hmem, coverage_of_icp haW hC (fun a₁ ha₁ m => ?_)⟩
  rw [AgWT.functional ha₁ ha']
  exact icpAt_left hcomp m

end BoCa.Fig16.Tree.Wp

end
