import Support.Model.Tree.World.ShapeMutT

/-!
# A reborrow step's transfer lemmas over the tree carrier

`[spec §62]`. `Core/Invariant.lean`'s reborrow transfer (`reb_like_back`, `reb_like_fwd`,
`reb_like_new`), `ChainInv` and `DeepInv` across a root and a deep reborrow (`chainInv_reb`,
`chainInv_rebDeep`, `deepInv_back`), at the codes.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus} {Θ : CodeTy}

theorem chain_unique_recT {r : FrameRecT K} (hR : (r.T.interp Θ).P K r.v r.R)
    {p₁ p₂ : Option BoCa.Loc} {l : BoCa.Loc} {S₁ S₂ : KTy} {u₁ u₂ : BoCa.Val}
    (h₁ : ChainT r.R r.T r.v p₁ l S₁ u₁) (h₂ : ChainT r.R r.T r.v p₂ l S₂ u₂) :
    p₁ = p₂ ∧ S₁ = S₂ :=
  chain_uniqueT Θ h₁ hR (fun _ _ e => e) h₂

theorem own_del {q : TRes K} {l m : BoCa.Loc} {w : BoCa.Val}
    (e : (q.del l).get m = some (CellUT.ownOf w)) : q.get m = some (CellUT.ownOf w) := by
  by_cases hm : m = l
  · subst hm; rw [ResUT.del_get_self] at e; cases e
  · rwa [ResUT.del_get_ne _ hm] at e

theorem chain_val {R : TRes K} {T : KTy} {v : BoCa.Val} {p₁ p₂ : Option BoCa.Loc} {l : BoCa.Loc}
    {S₁ S₂ : KTy} {u₁ u₂ : BoCa.Val} (h₁ : ChainT R T v p₁ l S₁ u₁) (h₂ : ChainT R T v p₂ l S₂ u₂) :
    u₁ = u₂ := by
  have e₁ := h₁.own; have e₂ := h₂.own
  rw [e₁] at e₂; injection Option.some.inj e₂

/-- The transferred half of a reborrow step, at every clause: a view of `ag(W′)` that
`reb_transfer_gen` sends back to `ag(W)` keeps what `ChainInv` says of it there. -/
theorem reb_like_back {W W' c σ₀ aW : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : σ₀.InStratum s} {β : Life}
    (hle : W.get le = some (CellUT.immOf s v σ₀ hs)) (hr : ResUT.Reb β σ₀ c)
    (hW : ResUT.CompS W c W') (haW : AgWT W aW) {a : TRes K} (ha : AgWT W' a) {m : BoCa.Loc}
    {ψ : TCell K} (e : a.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₀ : TCell K, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) ∨
    (∃ (u : BoCa.Val) (q : TRes K) (h : (q.del m).InStratum (TSet.single β)),
      σ₀.get m = some (CellUT.ownOf u) ∧
      c.get m = some (CellUT.immOf (TSet.single β) u (q.del m) h) ∧ ψ.wit = q.del m) := by
  rcases reb_transfer_gen hle hr hW ha e hk with ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩ | hb
  · rw [AgWT.functional haW₁ haW] at e₀; exact Or.inl ⟨ψ₀, e₀, k₀, w₀⟩
  · exact Or.inr hb

/-- In a reborrow step, a view of `ag(W)` reaches `ag(W′)`, and an `imm` one stays `imm`. -/
theorem reb_like_fwd {W W' c aW : TRes K} (hW : ResUT.CompS W c W') (haW : AgWT W aW) {a : TRes K}
    (ha : AgWT W' a) {m : BoCa.Loc} {ψ₀ : TCell K} (e₀ : aW.get m = some ψ₀)
    (k₀ : ψ₀.kind ≠ Kind.own) :
    ∃ ψ, a.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit ∧
      (ψ₀.kind = Kind.imm → ψ.kind = Kind.imm) := by
  obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgWT.split hW).mp ha
  rw [AgWT.functional haW' haW] at hcomp
  obtain ⟨ψ, e, k, w⟩ := lift_view hcomp e₀ k₀
  refine ⟨ψ, e, k, w, fun hk => ?_⟩
  obtain ⟨ψ', e', k'⟩ := imm_fwd_l hcomp e₀ hk
  rw [e] at e'; cases Option.some.inj e'; exact k'

/-- In a reborrow step, a cell of the image reaches `ag(W′)` as an `imm` view over its
witness. -/
theorem reb_like_new {W W' c : TRes K} (hW : ResUT.CompS W c W') {a : TRes K} (ha : AgWT W' a)
    {m : BoCa.Loc} {ζ : TCell K} (eζ : c.get m = some ζ) (kζ : ζ.kind = Kind.imm) :
    ∃ ψ, a.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.wit = ζ.wit := by
  obtain ⟨aW', ac, -, hac, hcomp⟩ := (AgWT.split hW).mp ha
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgWT.get_imm hac eζ kζ
  obtain ⟨ψ, e, -, w⟩ := lift_view_r hcomp eχ (by rw [kχ]; simp)
  obtain ⟨ψ', e', k'⟩ := imm_fwd_r hcomp eχ kχ
  rw [e] at e'; cases Option.some.inj e'
  exact ⟨ψ, e, k', w.trans wχ⟩

/-- The `DeepInv` conclusion for a transferred view. -/
theorem deepInv_back {W W' c aW : TRes K} {r : FrameRecT K} (hW : ResUT.CompS W c W')
    (haW : AgWT W aW) (hI : DeepInvT K Θ W r) {p : Option BoCa.Loc} {m : BoCa.Loc} {S : KTy} {u : BoCa.Val}
    (hc : ChainT r.R r.T r.v p m S u) {a : TRes K} (ha : AgWT W' a) {ψ ψ₀ : TCell K}
    (e : a.get m = some ψ) (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind ≠ Kind.own)
    (w₀ : ψ.wit = ψ₀.wit) :
    ψ.kind = Kind.imm ∧ (S.interp Θ).P K u ψ.wit ∧
    (∀ m' w, ψ.wit.get m' = some (CellUT.ownOf w) → r.R.get m' = some (CellUT.ownOf w)) ∧
    (p = none → ∃ q, ResUT.Le q r.R ∧ (∃ ζ, q.get m = some ζ) ∧ ψ.wit = q.del m) ∧
    (∀ l₀, p = some l₀ → ∃ ψ₁ : TCell K, a.get l₀ = some ψ₁ ∧ ψ₁.kind ≠ Kind.own ∧
       ∃ q, ResUT.Le q ψ₁.wit ∧ (∃ ζ, q.get m = some ζ) ∧ ψ.wit = q.del m) := by
  obtain ⟨kk, d, o, b₁, b₂⟩ := hI p m S u hc aW haW ψ₀ e₀ k₀
  obtain ⟨ψ', e', -, -, hi⟩ := reb_like_fwd hW haW ha e₀ k₀
  rw [e] at e'; cases Option.some.inj e'
  refine ⟨hi kk, w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
  obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
  obtain ⟨ψ₂, e₂, k₂, w₂, -⟩ := reb_like_fwd hW haW ha e₁ k₁
  exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩

theorem chainInv_reb {W W' c : TRes K} {rs : List (FrameRecT K)} {r₀ : FrameRecT K} {le : BoCa.Loc} {s : TSet}
    {β : Life} {hs : r₀.R.InStratum s}
    (hvW : ResUT.Valid W) (hr₀ : r₀ ∈ rs) (hle : W.get le = some (CellUT.immOf s r₀.v r₀.R hs)) (hreb : ResUT.Reb β r₀.R c)
    (hden : ((r₀.T.immReborrow β).interp Θ).P K r₀.v c)
    (hW : ResUT.CompS W c W') (hv : ResUT.Valid W') (h : ChainInvT K Θ W rs) : ChainInvT K Θ W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have hR₀ := (h4 r₀ hr₀)
  -- a new view sits at a first-step root of `r₀`
  have newRoot : ∀ m (u₀ : BoCa.Val) (q : TRes K) (hq : (q.del m).InStratum (TSet.single β)),
      r₀.R.get m = some (CellUT.ownOf u₀) →
      c.get m = some (CellUT.immOf (TSet.single β) u₀ (q.del m) hq) →
      ∃ S₀, RefPosT r₀.T r₀.v m S₀ := by
    intro m u₀ q hq hown hcl
    obtain ⟨ζ, eζ, hpos⟩ := image_domT Θ β r₀.T hden hR₀ hcl
    rw [hown] at eζ; cases Option.some.inj eζ
    exact hpos rfl
  refine ⟨fun r hr => ?_, fun r hr m u hm a ha => ?_, h3, h4, fun r hr => ?_, fun r hr => ?_⟩
  · intro p m S u hc a ha ψ e hk
    rcases reb_like_back hle hreb hW haW ha e hk with ⟨ψ₀, e₀, k₀, w₀⟩ |
        ⟨u₀, q, hq, hown, hcl, hw⟩
    · exact deepInv_back hW haW (h1 r hr) hc ha e e₀ k₀ w₀
    · have e₁ : r = r₀ := h3 r hr r₀ hr₀ m u u₀ hc.own hown
      subst e₁
      obtain ⟨S₀, hpos⟩ := newRoot m u₀ q hq hown hcl
      obtain ⟨hp, hS⟩ := chain_unique_recT hR₀ hc (ChainT.one hpos hown)
      subst hp; subst hS
      have hu : u = u₀ := chain_val hc (ChainT.one hpos hown)
      subst hu
      obtain ⟨q', hq', hc', hle', hql', hty⟩ := typed_image_posT Θ hpos hown hreb hden
      rw [hcl] at hc'
      obtain ⟨-, -, hqq⟩ := CellUT.immOf_inj (Option.some.inj hc')
      obtain ⟨ψ', e', k', w'⟩ := reb_like_new hW ha hcl rfl
      rw [e] at e'; cases Option.some.inj e'
      rw [CellUT.wit_immOf] at w'
      refine ⟨k', by rw [w', hqq]; exact hty, fun m' w e'' => ?_, fun _ => ⟨q', hle', hql',
        by rw [w', hqq]⟩, fun l₀ hp => by cases hp⟩
      rw [w', hqq] at e''
      exact own_of_le hle' (own_del e'')
  · obtain ⟨ζ, hζ⟩ := h2 r hr m u hm aW haW
    exact reb_support hW haW ha hζ
  · rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
    by_cases hrr : r = r₀
    · subst hrr
      obtain ⟨a', ha'⟩ := agW_of_valid hv
      obtain ⟨-, ac₀, -, hac₀, -⟩ := (AgWT.split hW).mp ha'
      refine ⟨β, c, hreb, hden, ⟨ac₀, hac₀⟩, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ζ, eζ, kζ, -⟩ := image_at_posT Θ hR'.1 hden
      obtain ⟨ψ₂, e₂, -, w₂⟩ := reb_like_new hW ha₁ eζ kζ
      rw [e₁] at e₂; cases Option.some.inj e₂
      exact ⟨ζ, eζ, w₂⟩
    · have back : ∀ S' m' u', RootT r S' m' u' → ∀ a₁, AgWT W' a₁ → ∀ ψ₁ : TCell K,
          a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
          ∃ ψ₀ : TCell K, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
        intro S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
        rcases reb_like_back hle hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u₀, q, hq, hown, -, -⟩
        · exact hb
        · exact absurd (h3 r hr r₀ hr₀ m' u' u₀ hR'.2 hown) hrr
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back S m u hR a ha ψ e hk
      obtain ⟨β₀, c₀, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨β₀, c₀, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  · have back : ∀ l₀ m' S' u', ChainT r.R r.T r.v (some l₀) m' S' u' → ∀ a₁, AgWT W' a₁ →
        ∀ ψ₁ : TCell K, a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
        ∃ ψ₀ : TCell K, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
      intro l₀ m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
      rcases reb_like_back hle hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u₀, q, hq, hown, hcl, -⟩
      · exact hb
      · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' u' u₀ hc'.own hown
        subst e₂
        obtain ⟨S₀, hpos⟩ := newRoot m' u₀ q hq hown hcl
        exact absurd (chain_unique_recT hR₀ hc' (ChainT.one hpos hown)).1 (by simp)
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back l₀ m S u hc a ha ψ e hk
    obtain ⟨w₀, hw₀, β₀, c₀, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨w₀, fun a₁ ha₁ => ?_, β₀, c₀, q2, q3, q4,
      fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
      obtain ⟨ψ₃, e₃, k₃, w₃, -⟩ := reb_like_fwd hW haW ha₁ e₂ k₂
      exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back l₀ m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩

theorem chainInv_rebDeep {W W' c : TRes K} {rs : List (FrameRecT K)} {r₀ : FrameRecT K} {p₀ : Option BoCa.Loc}
    {l₀ : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val} {s : TSet} {w₀ : TRes K} {hs : w₀.InStratum s}
    {β : Life}
    (hvW : ResUT.Valid W) (hr₀ : r₀ ∈ rs) (hch₀ : ChainT r₀.R r₀.T r₀.v p₀ l₀ S₀ u₀)
    (hcell : W.get l₀ = some (CellUT.immOf s u₀ w₀ hs))
    (hreb : ResUT.Reb β w₀ c) (hden : ((S₀.immReborrow β).interp Θ).P K u₀ c)
    (hW : ResUT.CompS W c W') (hv : ResUT.Valid W') (h : ChainInvT K Θ W rs) : ChainInvT K Θ W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have hR₀ := (h4 r₀ hr₀)
  -- the view at `ℓ₀` in `ag(W)`, and what `DeepInv` says of it
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgWT.get_imm haW hcell (CellUT.kind_immOf _ _ _ _)
  rw [CellUT.wit_immOf] at wχ
  rw [CellUT.erase_immOf] at rχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ := h1 r₀ hr₀ p₀ l₀ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  -- a new view sits at a child of `ℓ₀`
  have newChild : ∀ m (u : BoCa.Val) (q : TRes K) (hq : (q.del m).InStratum (TSet.single β)),
      w₀.get m = some (CellUT.ownOf u) →
      c.get m = some (CellUT.immOf (TSet.single β) u (q.del m) hq) →
      ∃ S', RefPosT S₀ u₀ m S' ∧ ChainT r₀.R r₀.T r₀.v (some l₀) m S' u := by
    intro m u q hq hown hcl
    obtain ⟨ζ, eζ, hpos⟩ := image_domT Θ β S₀ hden hw₀den hcl
    rw [hown] at eζ; cases Option.some.inj eζ
    obtain ⟨S', hS'⟩ := hpos rfl
    exact ⟨S', hS', hch₀.snoc hS' (hw₀own m u hown)⟩
  have viewAt : ∀ a, AgWT W' a → ∃ ψ₀ : TCell K, a.get l₀ = some ψ₀ ∧
      ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = w₀ := by
    intro a ha
    obtain ⟨ψ₀, e₀, k₀, w₀', -⟩ := reb_like_fwd hW haW ha eχ (by rw [kχ]; simp)
    exact ⟨ψ₀, e₀, k₀, w₀'.trans wχ⟩
  refine ⟨fun r hr => ?_, fun r hr m u hm a ha => ?_, h3, h4, fun r hr => ?_, fun r hr => ?_⟩
  · intro p m S u hc a ha ψ e hk
    rcases reb_like_back hcell hreb hW haW ha e hk with ⟨ψ₀, e₀, k₀, w₀'⟩ |
        ⟨u', q, hq, hown, hcl, hw⟩
    · exact deepInv_back hW haW (h1 r hr) hc ha e e₀ k₀ w₀'
    · have e₁ : r = r₀ := h3 r hr r₀ hr₀ m u u' hc.own (hw₀own m u' hown)
      subst e₁
      obtain ⟨S', hpos, hcS⟩ := newChild m u' q hq hown hcl
      obtain ⟨hp, hS⟩ := chain_unique_recT hR₀ hc hcS
      subst hp; subst hS
      have hu : u = u' := chain_val hc hcS
      subst hu
      obtain ⟨q', hq', hc', hle', hql', hty⟩ := typed_image_posT Θ hpos hown hreb hden
      rw [hcl] at hc'
      obtain ⟨-, -, hqq⟩ := CellUT.immOf_inj (Option.some.inj hc')
      obtain ⟨ψ', e', k', w'⟩ := reb_like_new hW ha hcl rfl
      rw [e] at e'; cases Option.some.inj e'
      rw [CellUT.wit_immOf] at w'
      refine ⟨k', by rw [w', hqq]; exact hty, fun m' w e'' => ?_, fun hp => (by cases hp),
        fun l₁ hp => ?_⟩
      · rw [w', hqq] at e''
        exact hw₀own m' w (own_of_le hle' (own_del e''))
      · cases hp
        obtain ⟨ψ₀, e₀, k₀, hw₀⟩ := viewAt a ha
        exact ⟨ψ₀, e₀, k₀, q', hw₀ ▸ hle', hql', by rw [w', hqq]⟩
  · obtain ⟨ζ, hζ⟩ := h2 r hr m u hm aW haW
    exact reb_support hW haW ha hζ
  · have back : ∀ S' m' u', RootT r S' m' u' → ∀ a₁, AgWT W' a₁ → ∀ ψ₁ : TCell K,
        a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
        ∃ ψ₀ : TCell K, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
      intro S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
      rcases reb_like_back hcell hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u', q, hq, hown, hcl, -⟩
      · exact hb
      · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' _ _ hR'.2 (hw₀own m' _ hown)
        subst e₂
        obtain ⟨S'', -, hcS⟩ := newChild m' _ q hq hown hcl
        exact absurd (chain_unique_recT hR₀ (ChainT.one hR'.1 hR'.2) hcS).1 (by simp)
    rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back S m u hR a ha ψ e hk
    obtain ⟨β₀, c₀, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, c₀, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  · rintro p₁ l₁ S₁ u₁ hc₁ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
    by_cases hrl : r = r₀ ∧ l₁ = l₀
    · obtain ⟨rfl, rfl⟩ := hrl
      obtain ⟨-, hS⟩ := chain_unique_recT hR₀ hc₁ hch₀
      subst hS
      have hu : u₁ = u₀ := chain_val hc₁ hch₀
      subst hu
      obtain ⟨a', ha'⟩ := agW_of_valid hv
      obtain ⟨-, ac₀, -, hac₀, -⟩ := (AgWT.split hW).mp ha'
      refine ⟨w₀, viewAt, β, c, hreb, hden, ⟨ac₀, hac₀⟩,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨p', S₀', u₀', hcl', hpos⟩ := chain_lastT hc' l₁ rfl
      obtain ⟨-, hS'⟩ := chain_unique_recT hR₀ hcl' hch₀
      subst hS'
      have hu' : u₀' = u₁ := chain_val hcl' hch₀
      subst hu'
      obtain ⟨ζ, eζ, kζ, -⟩ := image_at_posT Θ hpos hden
      obtain ⟨ψ₂, e₂, -, w₂⟩ := reb_like_new hW ha₁ eζ kζ
      rw [e₁] at e₂; cases Option.some.inj e₂
      exact ⟨ζ, eζ, w₂⟩
    · have back : ∀ m' S' u', ChainT r.R r.T r.v (some l₁) m' S' u' → ∀ a₁, AgWT W' a₁ →
          ∀ ψ₁ : TCell K, a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
          ∃ ψ₀ : TCell K, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧
            ψ₁.wit = ψ₀.wit := by
        intro m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
        rcases reb_like_back hcell hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u'', q, hq, hown, hcl, -⟩
        · exact hb
        · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' _ _ hc'.own (hw₀own m' _ hown)
          subst e₂
          obtain ⟨S'', -, hcS⟩ := newChild m' _ q hq hown hcl
          have := (chain_unique_recT hR₀ hc' hcS).1
          simp only [Option.some.injEq] at this
          exact absurd ⟨rfl, this⟩ hrl
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back m S u hc a ha ψ e hk
      obtain ⟨w₁, hw₁, β₀, c₀, q2, q3, q4, q5⟩ :=
        h6 r hr p₁ l₁ S₁ u₁ hc₁ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨w₁, fun a₁ ha₁ => ?_, β₀, c₀, q2, q3, q4,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₁ aW haW
        obtain ⟨ψ₃, e₃, k₃, w₃, -⟩ := reb_like_fwd hW haW ha₁ e₂ k₂
        exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
        obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
        exact ⟨ζ, eζ, w₂.trans wζ⟩

end BoCa.Fig16.Tree.Wp

end
