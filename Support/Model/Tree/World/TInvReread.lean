import Support.Model.Tree.World.RebRR

/-!
# `TIT` across a re-reading

`[spec §62]`. `TWNT.reread` grows the tree to `K'` and re-types to `Θ'` where no `mut` cell is held, re-reading
the world (`RR`) and every record (`RecRR`). `tit_reread`: `TIT` at `K`, `Θ` gives it at `K'`,
`Θ'`.

Every clause of `TIT` reads the world through its aliasable walk, its `mut` cells at depth, the
records' escrows and their chains; each is carried cell by cell:

* the walks: a walk of `W'` is the re-reading of a walk of `W`, keeping each cell's tag, value,
  `imm` lifetimes, and re-reading its witness (`agW_simL`, `walk_back`);
* chains and lineages: the `own` cells of a re-read escrow are the old ones
  (`RR.own_back`, `RR.own_fwd`), so chains are kept (`ChainT.rr_back`, `ChainT.rr_fwd`); a
  sub-record's `mut` cell is re-read with its witness, so lineages are re-read
  (`LinPathT.rr_fwd`, `LinPathT.rr_back`);
* the typings: a code's meaning is carried along the re-reading where the typings agree
  (`interp_retype`); every typed resource `TIT` names sits at depth of `W`, where `Θ'` agrees
  with `Θ` (`TIT.agree_recs`, `walk_agree`);
* the reborrows of `JointAt`/`JointDeep`: carried by `reb_rr_exists`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### Lists -/

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hxy _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hr⟩ := ih hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

/-! ### Records -/

/-- A record's re-reading is single-valued. -/
theorem RecRR.func {Θ' : CodeTy} {r : FrameRecT K} {r₁ r₂ : FrameRecT K'} (h₁ : RecRR Θ' r r₁)
    (h₂ : RecRR Θ' r r₂) : r₁ = r₂ := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  have := RR.func d₁ d₂
  cases r₁; cases r₂
  simp_all

/-! ### `own` cells, chains, lineages -/

theorem RR.own_fwd {Θ : LocTy} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') {l : BoCa.Loc}
    {u : BoCa.Val} (e : ρ.get l = some (CellUT.ownOf u)) : ρ'.get l = some (CellUT.ownOf u) := by
  obtain ⟨ψ', e', hr⟩ := h.get_some e
  cases hr; exact e'

theorem ChainT.rr_fwd {Θ : LocTy} {R : TRes K} {R' : TRes K'} (h : RR Θ R R') {T : KTy}
    {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val}
    (hc : ChainT R T v p l S u) : ChainT R' T v p l S u := by
  induction hc with
  | one hp e => exact .one hp (RR.own_fwd h e)
  | step hp e _ ih => exact .step hp (RR.own_fwd h e) ih

theorem GPosT.rr_fwd {Θ : LocTy} {R : TRes K} {R' : TRes K'} (h : RR Θ R R') {T : KTy}
    {v : BoCa.Val} {m : BoCa.Loc} {S : KTy} (hg : GPosT R T v m S) : GPosT R' T v m S := by
  induction hg with
  | here hm => exact .here hm
  | step hp e _ ih => exact .step hp (RR.own_fwd h e) ih

theorem GPosT.rr_back {Θ : LocTy} {R : TRes K} {R' : TRes K'} (h : RR Θ R R') {T : KTy}
    {v : BoCa.Val} {m : BoCa.Loc} {S : KTy} (hg : GPosT R' T v m S) : GPosT R T v m S := by
  induction hg with
  | here hm => exact .here hm
  | step hp e _ ih => exact .step hp (RR.own_back h e) ih

/-- A record's chains are its re-reading's. -/
theorem chain_recRR_fwd {Θ' : CodeTy} {r : FrameRecT K} {r' : FrameRecT K'} (h : RecRR Θ' r r')
    {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val}
    (hc : ChainT r.R r.T r.v p l S u) : ChainT r'.R r'.T r'.v p l S u := by
  obtain ⟨-, hv, hT, hR⟩ := h
  rw [hv, hT]; exact ChainT.rr_fwd hR hc

theorem chain_recRR_back {Θ' : CodeTy} {r : FrameRecT K} {r' : FrameRecT K'} (h : RecRR Θ' r r')
    {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val}
    (hc : ChainT r'.R r'.T r'.v p l S u) : ChainT r.R r.T r.v p l S u := by
  obtain ⟨-, hv, hT, hR⟩ := h
  rw [hv, hT] at hc; exact ChainT.rr_back hR hc

/-- **A lineage path is re-read.** -/
theorem LinPathT.rr_fwd {Θ' : CodeTy} {r d : FrameRecT K} {p : List BoCa.Loc}
    (h : LinPathT r p d) : ∀ {r' : FrameRecT K'}, RecRR Θ' r r' →
      ∃ d', RecRR Θ' d d' ∧ LinPathT r' p d' := by
  induction h with
  | nil r => intro r' hr; exact ⟨r', hr, .nil r'⟩
  | @cons r d e p hs _ ih =>
      intro r' hr
      obtain ⟨hl, hv, hT, hR⟩ := hr
      obtain ⟨hg, ζ, eζ, kζ, vζ, wζ⟩ := hs
      obtain ⟨ζ', eζ', hrc⟩ := hR.get_some eζ
      let d' : FrameRecT K' := ⟨d.le, d.v, ζ'.wit, d.T⟩
      have hd : RecRR Θ' d d' := ⟨rfl, rfl, rfl, wζ ▸ hrc.wit⟩
      obtain ⟨e', he, hp⟩ := ih hd
      refine ⟨e', he, LinPathT.cons ⟨?_, ζ', eζ', hrc.kind.trans kζ, hrc.erase.trans vζ, rfl⟩ hp⟩
      rw [hv, hT]; exact GPosT.rr_fwd hR hg

theorem LinPathT.rr_back {Θ' : CodeTy} {r' d' : FrameRecT K'} {p : List BoCa.Loc}
    (h : LinPathT r' p d') : ∀ {r : FrameRecT K}, RecRR Θ' r r' →
      ∃ d, RecRR Θ' d d' ∧ LinPathT r p d := by
  induction h with
  | nil r' => intro r hr; exact ⟨r, hr, .nil r⟩
  | @cons r' d' e' p hs _ ih =>
      intro r hr
      obtain ⟨hl, hv, hT, hR⟩ := hr
      obtain ⟨hg, ζ', eζ', kζ', vζ', wζ'⟩ := hs
      obtain ⟨ζ, eζ, hrc⟩ := hR.get_some' eζ'
      let d : FrameRecT K := ⟨d'.le, d'.v, ζ.wit, d'.T⟩
      have hd : RecRR Θ' d d' := ⟨rfl, rfl, rfl, wζ' ▸ hrc.wit⟩
      obtain ⟨e, he, hp⟩ := ih hd
      refine ⟨e, he, LinPathT.cons (d := d) ⟨?_, ζ, eζ, hrc.kind.symm.trans kζ',
        hrc.erase.symm.trans vζ', rfl⟩ hp⟩
      rw [← hv, ← hT]; exact GPosT.rr_back hR hg

/-! ### The walks -/

/-- **A walk of the re-read world is the re-reading of the walk.** -/
theorem walk_back {Θ : LocTy} {W : TRes K} {W' : TRes K'} (hv : ResUT.Valid W) (hW : RR Θ W W')
    {a' : TRes K'} (ha' : AgWT W' a') : ∃ a, AgWT W a ∧ LRSim Θ a' a := by
  obtain ⟨a, ha⟩ := agW_of_valid hv
  obtain ⟨a'', ha'', hs⟩ := agW_simL ha W' (lrsim_of_RR hW)
  obtain rfl := AgWT.functional ha'' ha'
  exact ⟨a, ha, hs⟩

theorem walk_fwd {Θ : LocTy} {W : TRes K} {W' : TRes K'} (hW : RR Θ W W') {a : TRes K}
    (ha : AgWT W a) : ∃ a', AgWT W' a' ∧ LRSim Θ a' a :=
  agW_simL ha W' (lrsim_of_RR hW)

theorem LRSim.back {Θ : LocTy} {a : TRes K} {a' : TRes K'} (h : LRSim Θ a' a) {l : BoCa.Loc}
    {ψ' : TCell K'} (e : a'.get l = some ψ') : ∃ ψ, a.get l = some ψ ∧ LSim Θ ψ' ψ := by
  have hl := h l
  rw [e] at hl
  cases ea : a.get l with
  | none => rw [ea] at hl; cases hl
  | some ψ => rw [ea] at hl; cases hl with | some hs => exact ⟨ψ, rfl, hs⟩

theorem LRSim.fwd {Θ : LocTy} {a : TRes K} {a' : TRes K'} (h : LRSim Θ a' a) {l : BoCa.Loc}
    {ψ : TCell K} (e : a.get l = some ψ) : ∃ ψ', a'.get l = some ψ' ∧ LSim Θ ψ' ψ := by
  have hl := h l
  rw [e] at hl
  cases ea : a'.get l with
  | none => rw [ea] at hl; cases hl
  | some ψ' => rw [ea] at hl; cases hl with | some hs => exact ⟨ψ', rfl, hs⟩

/-! ### `mut` cells held -/

theorem CellAt.holdsMut {W : TRes K} {y : BoCa.Loc} {ψ : TCell K} (h : CellAt W y ψ) :
    (ψ.kind = Kind.mut → HoldsMut W y) ∧ (∀ l, HoldsMut ψ.wit l → HoldsMut W l) := by
  induction h with
  | top e =>
      refine ⟨fun hk => ?_, fun l hm => .deep e hm⟩
      rename_i ψ
      cases ψ with
      | «mut» m => exact .top e
      | own => cases hk
      | imm => cases hk
  | nest e _ ih => exact ⟨fun hk => .deep e (ih.1 hk), fun l hm => .deep e (ih.2 l hm)⟩

/-- A resource whose cells sit at depth of `W` holds `mut` cells only where `W` does. -/
theorem holdsMut_of_cellAt {W R : TRes K} (hR : ∀ y ψ, R.get y = some ψ → CellAt W y ψ)
    {l : BoCa.Loc} (hm : HoldsMut R l) : HoldsMut W l := by
  cases hm with
  | top e => exact (hR _ _ e).holdsMut.1 rfl
  | deep e h => exact (hR _ _ e).holdsMut.2 _ h

/-- A view's witness holds `mut` cells only where the world does. -/
theorem walk_holdsMut {W a : TRes K} (ha : AgWT W a) {x : BoCa.Loc} {ψ : TCell K}
    (e : a.get x = some ψ) (hk : ψ.kind ≠ Kind.own) {l : BoCa.Loc} (hm : HoldsMut ψ.wit l) :
    HoldsMut W l := by
  obtain ⟨ψ₀, c₀, w₀⟩ := agW_cellAt ha x ψ e hk
  exact c₀.holdsMut.2 l (w₀ ▸ hm)

theorem walk_agree {Θ Θ' : CodeTy} {W a : TRes K} (hag : AgreeOn Θ Θ' W) (ha : AgWT W a)
    {x : BoCa.Loc} {ψ : TCell K} (e : a.get x = some ψ) (hk : ψ.kind ≠ Kind.own) :
    AgreeOn Θ Θ' ψ.wit :=
  fun l hm => hag l (walk_holdsMut ha e hk hm)

/-- **Every record's escrow sits at depth of the world**: a record proper's is the witness of its
view (`LeInv`), a sub-record's the witness of a `mut` cell of its parent's escrow. -/
theorem TIT.recs_cellAt {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hv : ResUT.Valid W) (h : TIT K Θ W ps rs) {r : FrameRecT K} (hr : r ∈ rs) :
    ∀ y ψ, r.R.get y = some ψ → CellAt W y ψ := by
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨p, hp, q, hq⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  obtain ⟨ψ, eψ, kψ, -, wψ⟩ := h.2.1 p hp aW haW
  obtain ⟨ψ', cψ', wψ'⟩ := agW_cellAt haW _ ψ eψ (by rw [kψ]; simp)
  refine hq.cellAt fun y φ e => cψ'.wit_trans ?_
  rw [wψ', wψ]; exact e

theorem TIT.agree_recs {Θ Θ' : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hv : ResUT.Valid W) (h : TIT K Θ W ps rs) (hag : AgreeOn Θ Θ' W) {r : FrameRecT K}
    (hr : r ∈ rs) : AgreeOn Θ Θ' r.R :=
  fun l hm => hag l (holdsMut_of_cellAt (h.recs_cellAt hv hr) hm)

/-- `MutAt` read back along a re-reading. -/
theorem MutAtT.rr_back {Θ : LocTy} {ρ' : TRes K'} {x : BoCa.Loc} (h : MutAtT ρ' x) :
    ∀ {ρ : TRes K}, RR Θ ρ ρ' → MutAtT ρ x := by
  induction h with
  | top e hk =>
      intro ρ hr
      obtain ⟨ψ, eψ, hrc⟩ := hr.get_some' e
      exact .top eψ (hrc.kind.symm.trans hk)
  | nest e hk _ ih =>
      intro ρ hr
      obtain ⟨ψ, eψ, hrc⟩ := hr.get_some' e
      exact .nest eψ (by rw [← hrc.kind]; exact hk) (ih hrc.wit)

/-- A chain one step from its end extends a chain to its parent. -/
theorem chain_parent {R : TRes K} {T : KTy} {v : BoCa.Val} {l₀ l : BoCa.Loc} {S : KTy}
    {u : BoCa.Val} (h : ChainT R T v (some l₀) l S u) :
    ∃ p₀ S₀ u₀, ChainT R T v p₀ l₀ S₀ u₀ := by
  obtain ⟨p₀, S₀, u₀, hc, -⟩ := chain_lastT h l₀ rfl
  exact ⟨p₀, S₀, u₀, hc⟩

/-! ### The re-reading of a part of a typed resource -/

/-- A part of a covered, agreeing resource re-reads to a part of the re-reading, and a resource
the part's re-reading deletes from is the deletion's re-reading. -/
theorem part_rr {Θ Θ' : CodeTy} (hE : K.Ext K') {q ρ : TRes K} {ρ' : TRes K'}
    (h : ResUT.Le q ρ) (hc : CovR (sem Θ) K ρ) (hag : AgreeOn Θ Θ' ρ) (hr : RR (sem Θ') ρ ρ') :
    ∃ q', RR (sem Θ') q q' ∧ ResUT.Le q' ρ' := by
  obtain ⟨q', hq, -⟩ := RR.exists_retype hE (le_cov h hc) (le_agree h hag)
  exact ⟨q', hq, RR.le hE h hc hag hr hq⟩

/-! ### The theorem -/

/-- **`TIT` across a re-reading.** -/
theorem tit_reread {Θ Θ' : CodeTy} {W : TRes K} {W' : TRes K'}
    {ps rs : List (FrameRecT K)} {ps' rs' : List (FrameRecT K')} (hv : ResUT.Valid W)
    (hE : K.Ext K') (hag : AgreeOn Θ Θ' W) (hW : RR (sem Θ') W W')
    (hps : List.Forall₂ (RecRR Θ') ps ps') (hrs : List.Forall₂ (RecRR Θ') rs rs')
    (h : TIT K Θ W ps rs) : TIT K' Θ' W' ps' rs' := by
  obtain ⟨⟨hDeep, hOwn, hUniq, hTyped, hJAt, hJDeep⟩, hLe, hPsU, hNotR, hNest, ⟨hNM₁, hNM₂⟩,
    hDesc, hCov⟩ := h
  have hTIT : TIT K Θ W ps rs := ⟨⟨hDeep, hOwn, hUniq, hTyped, hJAt, hJDeep⟩, hLe, hPsU, hNotR,
    hNest, ⟨hNM₁, hNM₂⟩, hDesc, hCov⟩
  have hps_rs : ∀ p ∈ ps, p ∈ rs := fun p hp => (hDesc p).mpr ⟨p, hp, [], .nil p⟩
  have hagR : ∀ r ∈ rs, AgreeOn Θ Θ' r.R := fun r hr => hTIT.agree_recs hv hag hr
  have hcR : ∀ r ∈ rs, CovR (sem Θ) K r.R := fun r hr => interp_cov r.T (hTyped r hr)
  have back : ∀ r' ∈ rs', ∃ r ∈ rs, RecRR Θ' r r' := fun r' hr' => forall₂_mem_right hrs hr'
  have fwd : ∀ r ∈ rs, ∃ r' ∈ rs', RecRR Θ' r r' := fun r hr => forall₂_mem_left hrs hr
  have backP : ∀ r' ∈ ps', ∃ r ∈ ps, RecRR Θ' r r' := fun r' hr' => forall₂_mem_right hps hr'
  have fwdP : ∀ r ∈ ps, ∃ r' ∈ ps', RecRR Θ' r r' := fun r hr => forall₂_mem_left hps hr
  -- the view at a chain position: typed, covered and agreeing
  have chainView : ∀ r ∈ rs, ∀ p l S u, ChainT r.R r.T r.v p l S u → ∀ a, AgWT W a →
      ∀ ψ : TCell K, a.get l = some ψ → ψ.kind ≠ Kind.own →
      (S.interp Θ).P K u ψ.wit ∧ CovR (sem Θ) K ψ.wit ∧ AgreeOn Θ Θ' ψ.wit :=
    fun r hr p l S u hc a ha ψ e hk =>
      have hP := (hDeep r hr p l S u hc a ha ψ e hk).2.1
      ⟨hP, interp_cov S hP, walk_agree hag ha e hk⟩
  refine ⟨⟨?deep, ?own, ?uniq, ?typed, ?jat, ?jdeep⟩, ?le, ?psu, ?notR, ?nest, ⟨?nm₁, ?nm₂⟩,
    ?desc, ?cov⟩
  case deep =>
    intro r' hr' p l S u hc a' ha' ψ' e' hk'
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    have hc₀ := chain_recRR_back hrr hc
    obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
    obtain ⟨ψ, e, ⟨⟨kk, -, hwit⟩, -⟩⟩ := hs.back e'
    have hk : ψ.kind ≠ Kind.own := by rw [← kk]; exact hk'
    obtain ⟨k₁, hP, hown, hnone, hsome⟩ := hDeep r hr p l S u hc₀ a ha ψ e hk
    obtain ⟨-, hcw, hagw⟩ := chainView r hr p l S u hc₀ a ha ψ e hk
    refine ⟨kk.trans k₁, interp_retype S hE u _ _ hcw hwit hagw hP, ?_, ?_, ?_⟩
    · intro m w ew
      exact RR.own_fwd hrr.2.2.2 (hown m w (RR.own_back hwit ew))
    · intro hp
      obtain ⟨q, hq, ⟨ζ, eζ⟩, hqw⟩ := hnone hp
      obtain ⟨q', hq', hle'⟩ := part_rr hE hq (hcR r hr) (hagR r hr) hrr.2.2.2
      obtain ⟨ζ', eζ', -⟩ := hq'.get_some eζ
      refine ⟨q', hle', ⟨ζ', eζ'⟩, ?_⟩
      exact RR.func hwit (hqw ▸ RR.del hq' l)
    · intro l₀ hp
      obtain ⟨ψ₀, e₀, k₀, q, hq, ⟨ζ, eζ⟩, hqw⟩ := hsome l₀ hp
      obtain ⟨ψ₀', e₀', ⟨⟨kk₀, -, hwit₀⟩, -⟩⟩ := hs.fwd e₀
      subst hp
      obtain ⟨p₀, S₀, u₀, hc₀'⟩ := chain_parent hc₀
      obtain ⟨-, hcw₀, hagw₀⟩ := chainView r hr p₀ l₀ S₀ u₀ hc₀' a ha ψ₀ e₀ k₀
      obtain ⟨q', hq', hle'⟩ := part_rr hE hq hcw₀ hagw₀ hwit₀
      obtain ⟨ζ', eζ', -⟩ := hq'.get_some eζ
      refine ⟨ψ₀', e₀', by rw [kk₀]; exact k₀, q', hle', ⟨ζ', eζ'⟩, ?_⟩
      exact RR.func hwit (hqw ▸ RR.del hq' l)
  case own =>
    intro r' hr' l u e a' ha'
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
    obtain ⟨ζ, eζ⟩ := hOwn r hr l u (RR.own_back hrr.2.2.2 e) a ha
    obtain ⟨ζ', eζ', -⟩ := hs.fwd eζ
    exact ⟨ζ', eζ'⟩
  case uniq =>
    intro r₁' h₁ r₂' h₂ l u₁ u₂ e₁ e₂
    obtain ⟨r₁, hr₁, rr₁⟩ := back r₁' h₁
    obtain ⟨r₂, hr₂, rr₂⟩ := back r₂' h₂
    obtain rfl := hUniq r₁ hr₁ r₂ hr₂ l u₁ u₂ (RR.own_back rr₁.2.2.2 e₁) (RR.own_back rr₂.2.2.2 e₂)
    exact RecRR.func rr₁ rr₂
  case typed =>
    intro r' hr'
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    obtain ⟨-, hv', hT, hR⟩ := hrr
    rw [hv', hT]
    exact interp_retype r.T hE r.v _ _ (hcR r hr) hR (hagR r hr) (hTyped r hr)
  case jat =>
    intro r' hr' hex
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    have hex₀ : ∃ S l u, RootT r S l u ∧ ∃ a, AgWT W a ∧ ∃ ψ : TCell K, a.get l = some ψ ∧
        ψ.kind ≠ Kind.own := by
      obtain ⟨S, l, u, hroot, a', ha', ψ', e', hk'⟩ := hex
      obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
      obtain ⟨ψ, e, ⟨⟨kk, -, -⟩, -⟩⟩ := hs.back e'
      exact ⟨S, l, u, RootT.rr_back hrr hroot, a, ha, ψ, e, by rw [← kk]; exact hk'⟩
    obtain ⟨β₀, c₀, hreb, hP, ⟨A, hA⟩, hviews⟩ := hJAt r hr hex₀
    obtain ⟨c₀', hc₀', hreb'⟩ := reb_rr_exists hE hreb (hcR r hr) (hagR r hr) hrr.2.2.2
    obtain ⟨hcc, hcag⟩ := reb_cov_agree hreb (hcR r hr) (hagR r hr)
    obtain ⟨A', hA', -⟩ := walk_fwd hc₀' hA
    refine ⟨β₀, c₀', hreb', ?_, ⟨A', hA'⟩, ?_⟩
    · obtain ⟨-, hv', hT, -⟩ := hrr
      rw [hv', hT]
      exact interp_retype _ hE r.v _ _ hcc hc₀' hcag hP
    · intro S l u hroot a' ha' ψ' e' hk'
      obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
      obtain ⟨ψ, e, ⟨⟨kk, -, hwit⟩, -⟩⟩ := hs.back e'
      obtain ⟨ζ, eζ, hw⟩ := hviews S l u (RootT.rr_back hrr hroot) a ha ψ e
        (by rw [← kk]; exact hk')
      obtain ⟨ζ', eζ', hrc⟩ := hc₀'.get_some eζ
      exact ⟨ζ', eζ', RR.func hwit (hw ▸ hrc.wit)⟩
  case jdeep =>
    intro r' hr' p₀ l₀ S₀ u₀ hc' hex
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    have hc := chain_recRR_back hrr hc'
    have hex₀ : ∃ l S u, ChainT r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgWT W a ∧
        ∃ ψ : TCell K, a.get l = some ψ ∧ ψ.kind ≠ Kind.own := by
      obtain ⟨l, S, u, hcl, a', ha', ψ', e', hk'⟩ := hex
      obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
      obtain ⟨ψ, e, ⟨⟨kk, -, -⟩, -⟩⟩ := hs.back e'
      exact ⟨l, S, u, chain_recRR_back hrr hcl, a, ha, ψ, e, by rw [← kk]; exact hk'⟩
    obtain ⟨w₀, hw₀, β₀, c₀, hreb, hP, ⟨A, hA⟩, hviews⟩ := hJDeep r hr p₀ l₀ S₀ u₀ hc hex₀
    obtain ⟨aW, haW⟩ := agW_of_valid hv
    obtain ⟨ψ₀, e₀, k₀, rfl⟩ := hw₀ aW haW
    obtain ⟨-, hcw, hagw⟩ := chainView r hr p₀ l₀ S₀ u₀ hc aW haW ψ₀ e₀ k₀
    obtain ⟨w₀', hw₀', -⟩ := RR.exists_retype hE hcw hagw
    obtain ⟨c₀', hc₀', hreb'⟩ := reb_rr_exists hE hreb hcw hagw hw₀'
    obtain ⟨hcc, hcag⟩ := reb_cov_agree hreb hcw hagw
    obtain ⟨A', hA', -⟩ := walk_fwd hc₀' hA
    refine ⟨w₀', fun a' ha' => ?_, β₀, c₀', hreb', interp_retype _ hE u₀ _ _ hcc hc₀' hcag hP,
      ⟨A', hA'⟩, ?_⟩
    · obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
      obtain rfl := AgWT.functional ha haW
      obtain ⟨ψ₀', e₀', ⟨⟨kk, -, hwit⟩, -⟩⟩ := hs.fwd e₀
      exact ⟨ψ₀', e₀', by rw [kk]; exact k₀, RR.func hwit hw₀'⟩
    · intro l S u hcl a' ha' ψ' e' hk'
      obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
      obtain ⟨ψ, e, ⟨⟨kk, -, hwit⟩, -⟩⟩ := hs.back e'
      obtain ⟨ζ, eζ, hw⟩ := hviews l S u (chain_recRR_back hrr hcl) a ha ψ e
        (by rw [← kk]; exact hk')
      obtain ⟨ζ', eζ', hrc⟩ := hc₀'.get_some eζ
      exact ⟨ζ', eζ', RR.func hwit (hw ▸ hrc.wit)⟩
  case le =>
    intro r' hr' a' ha'
    obtain ⟨r, hr, hrr⟩ := backP r' hr'
    obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
    obtain ⟨ψ, e, k, er, wr⟩ := hLe r hr a ha
    obtain ⟨ψ', e', ⟨⟨kk, ee, hwit⟩, -⟩⟩ := hs.fwd e
    obtain ⟨hl, hv', -, hR⟩ := hrr
    refine ⟨ψ', by rw [hl]; exact e', kk.trans k, by rw [ee, er, hv'], ?_⟩
    exact RR.func hwit (wr ▸ hR)
  case psu =>
    intro r₁' h₁ r₂' h₂ hle
    obtain ⟨r₁, hr₁, rr₁⟩ := backP r₁' h₁
    obtain ⟨r₂, hr₂, rr₂⟩ := backP r₂' h₂
    obtain rfl := hPsU r₁ hr₁ r₂ hr₂ (by rw [← rr₁.1, ← rr₂.1]; exact hle)
    exact RecRR.func rr₁ rr₂
  case notR =>
    intro r₁' h₁ r₂' h₂ u e
    obtain ⟨r₁, hr₁, rr₁⟩ := back r₁' h₁
    obtain ⟨r₂, hr₂, rr₂⟩ := back r₂' h₂
    rw [rr₁.1] at e
    exact hNotR r₁ hr₁ r₂ hr₂ u (RR.own_back rr₂.2.2.2 e)
  case nest =>
    intro r' hr' l₀ l S u hc a' ha' ψ' s e' hs' x hx
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
    obtain ⟨ψ, e, ⟨-, hls⟩⟩ := hs.back e'
    obtain ⟨ζ, t, y, eζ, ht, hy, hxy⟩ :=
      hNest r hr l₀ l S u (chain_recRR_back hrr hc) a ha ψ s e (hls ▸ hs') x hx
    obtain ⟨ζ', eζ', ⟨-, hls'⟩⟩ := hs.fwd eζ
    exact ⟨ζ', t, y, eζ', hls'.trans ht, hy, hE hxy⟩
  case nm₁ =>
    intro r' hr' hm
    obtain ⟨r, hr, hrr⟩ := backP r' hr'
    rw [hrr.1] at hm
    exact hNM₁ r hr (hm.rr_back hW)
  case nm₂ =>
    intro r' hr' l u e hm
    obtain ⟨r, hr, hrr⟩ := back r' hr'
    exact hNM₂ r hr l u (RR.own_back hrr.2.2.2 e) (hm.rr_back hW)
  case desc =>
    intro x'
    constructor
    · intro hx'
      obtain ⟨x, hx, hxx⟩ := back x' hx'
      obtain ⟨p, hp, q, hq⟩ := (hDesc x).mp hx
      obtain ⟨p', hp', hpp⟩ := fwdP p hp
      obtain ⟨d', hd', hq'⟩ := hq.rr_fwd hpp
      obtain rfl := RecRR.func hxx hd'
      exact ⟨p', hp', q, hq'⟩
    · rintro ⟨p', hp', q, hq'⟩
      obtain ⟨p, hp, hpp⟩ := backP p' hp'
      obtain ⟨d, hd, hq⟩ := hq'.rr_back hpp
      obtain ⟨x'', hx'', hxx⟩ := fwd d ((hDesc d).mpr ⟨p, hp, q, hq⟩)
      obtain rfl := RecRR.func hd hxx
      exact hx''
  case cov =>
    intro a' ha' m ψ' e' hk'
    obtain ⟨a, ha, hs⟩ := walk_back hv hW ha'
    obtain ⟨ψ, e, ⟨⟨kk, ee, hwit⟩, -⟩⟩ := hs.back e'
    rcases hCov a ha m ψ e (kk.symm.trans hk') with ⟨r, hr, rfl, er, wr⟩ | ⟨r, hr, p, S, u, hc⟩
    · obtain ⟨r', hr', hrr⟩ := fwd r hr
      refine .inl ⟨r', hr', hrr.1.symm, by rw [ee, er, hrr.2.1], RR.func hwit (wr ▸ hrr.2.2.2)⟩
    · obtain ⟨r', hr', hrr⟩ := fwd r hr
      exact .inr ⟨r', hr', p, S, u, chain_recRR_fwd hrr hc⟩

end BoCa.Fig16.Tree.Wp

end
