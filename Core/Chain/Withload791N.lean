import Core.Chain.Inst791N
import Core.Chain.ImmImage791N
import Core.Chain.ImmTie791N
import Core.Chain.SI.RebRaiseC

/-!
# `withload` at a suspending row: the witness and the image  `[spec §62]`

Core's `withload_compatX` (`Core/Compatibility.lean:252`), step by step (`chain-interpretation.md`
§6.3), at a `Row.Suspend` callback row, is `withloadS_compat` (`WithloadSKW835N`), over
`withload_rebT` (`WithloadKW835N`). The callback's table is the constant's
(`tabN_extend_suspendC`): the row's layers do not mention `'x`. It may be stopped at under a
reborrow at `β ⊏ @bnd` (`tabNK_rebOKR_K`), and its cancel obligations are closed under the
reborrow (`tabNK_rebCanK`, by induction on how deep cancel rows nest, `erwp_rebGen_cancelRun` at
each level).

This file holds the facts those read that do not read the relation: the witness read at the run's
first entry (`desc_mem_of_tie`, `cohE_of_immWitW`), the witnesses of an image's new cells
(`immWitW_root`, `immWitW_rootMut`, `immWitW_child`, `immWitW_childMut`), a chain view's template
(`tmplD_exists`), the image's lifetimes from the run's tags (`lifeBoundW_of_entry`,
`lifeBoundOn_reb`, `lifeBoundWit_reb`), the reborrow's type (`tyEq_immReb`), and `wl`'s
antecedent at the hardest case's row (`wl_ok`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 defines_meetOfDom_empty ansC_of_suspend)
open BoCa.BoLo (Heap Kont Head performE raiseE cancelVal opPayload)

/-! ### The callback's table -/

/-- `entN` reads its cancel obligation only at a capturable entry. -/
theorem entN_fin_congr {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop}
    {f f' : Option (Nat → List SRec → Expr → WProp)} (h : capB q B = true → f = f') :
    entN q B PA PB f = entN q B PA PB f' := by
  unfold entN
  by_cases hc : capB q B = true
  · rw [h hc]
  · simp only [hc]
    congr 1

/-! ### The witness, read at the run's first entry -/

theorem _root_.BoCa.Fig16.LogRel.Core.LinPath.append {r d e : FrameRec} {p q : List Loc} (h₁ : LinPath r p d)
    (h₂ : LinPath d q e) : LinPath r (p ++ q) e := by
  induction h₁ with
  | nil r => exact h₂
  | cons hs _ ih => exact LinPath.cons hs (ih h₂)

theorem _root_.BoCa.Fig16.LogRel.Core.DescR.trans {r d e : FrameRec} (h₁ : DescR r d) (h₂ : DescR d e) : DescR r e := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨_, hp.append hq⟩

/-- **The tie puts a witness's record on the run's list**: at a typed world at the list's records,
a descendant of a record of the location typing's `imm` list is a record of the list (the typed
world's records are the lineages of its records proper, `TI`). -/
theorem desc_mem_of_tie {W : WRes} {ps : List FrameRec} {ls : List SRec} {I : List SRec}
    (hT : TWNC W ps (rsOf ls)) (hI : ImmTieL I ls) {x : SRec} (hx : x ∈ I) {d : FrameRec}
    (hd : DescR x.1 d) : d ∈ rsOf ls := by
  have hTI := hT.inv
  obtain ⟨p, hp, hpx⟩ := (hTI.2.2.2.2.2.2.1 x.1).mp (hI.rsOf hx)
  exact (hTI.2.2.2.2.2.2.1 d).mpr ⟨p, hp, hpx.trans hd⟩

/-- **The witness at the run's first entry is Core's `CohE` at the run's list.** -/
theorem cohE_of_immWitW {W : WRes} {ps : List FrameRec} {ls : List SRec} {I : List SRec}
    (hT : TWNC W ps (rsOf ls)) (hI : ImmTieL I ls) {l : Loc} {A : VTy} {δ : LSub}
    {s : LSet} (hw : ImmWitW I l s A δ) :
    ∃ x ∈ I, s.meet ≤ x.2 ∧ ∃ d, DescR x.1 d ∧ d ∈ rsOf ls ∧ ∃ S₀ δ₀, TyEq A δ S₀ δ₀ ∧
      ((l = d.le ∧ S₀ = d.T ∧ AgreeOn d.T δ₀ d.δ) ∨
        (∃ p u, Chain d.R d.T d.v p l S₀ u ∧ AgreeOn S₀ δ₀ d.δ)) := by
  obtain ⟨x, hx, hxs, d, hd, S₀, δ₀, he, hc⟩ := hw
  refine ⟨x, hx, hxs, d, hd, desc_mem_of_tie hT hI hx hd, S₀, δ₀, he, ?_⟩
  rcases hc with ⟨r, hr, h₁, h₂, h₃⟩ | ⟨r, hr, p, u, h₁, h₂⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨h₁, h₂, h₃⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨p, u, h₁, h₂⟩

/-! ### The witnesses of an image's new cells -/

/-- The witness of an image cell at a `Ref` position of a record's own cell. -/
theorem immWitW_root {I : List SRec} {x : SRec} (hx : x ∈ I) {d : FrameRec} (hd : DescR x.1 d)
    {A : VTy} {δ δ₀ : LSub} (he : TyEq A δ d.T δ₀) (hag : AgreeOn d.T δ₀ d.δ) {y : LifeVar}
    (hy : ¬ VFree y A) {β : Life} (hβ : β ≤ x.2) {m : Loc} {S : VTy} {u : Val}
    (hpos : RefPos A d.v m S) (hown : d.R.get m = some (CellU.ownOf u)) :
    ImmWitW I m (LSet.singleton β) S (δ.extend y β) := by
  obtain ⟨S', hpos', heS⟩ := hpos.tyEq he
  have hyS : ¬ VFree y S := RefPos.not_free hpos hy
  refine ⟨x, hx, hβ, d, hd, S', d.δ, TyEq.extend_left hyS β
    (heS.trans (TyEq.of_agree S' fun z hz => hag z (hpos'.free hz))),
    Or.inr ⟨d, List.mem_singleton_self _, none, u, Chain.one hpos' hown, fun _ _ => rfl⟩⟩

/-- The witness of an image cell at a `Mut` position of a record's own cell: the sub-record
there. -/
theorem immWitW_rootMut {I : List SRec} {x : SRec} (hx : x ∈ I) {d : FrameRec}
    (hd : DescR x.1 d) (hR : vShape d.T d.δ d.v d.R) {A : VTy} {δ δ₀ : LSub}
    (he : TyEq A δ d.T δ₀) (hag : AgreeOn d.T δ₀ d.δ) {y : LifeVar} (hy : ¬ VFree y A)
    {β : Life} (hβ : β ≤ x.2) {m : Loc} {S : VTy} (hpos : MutPos A d.v m S) :
    ImmWitW I m (LSet.singleton β) S (δ.extend y β) := by
  obtain ⟨S', hpos', heS⟩ := hpos.tyEq he
  have hyS : ¬ VFree y S := fun h => hy (hpos.free h)
  obtain ⟨ζ, eζ, kζ, -⟩ := mut_split_den hpos' hR
  have hsub : SubRec d ⟨m, ζ.erase, ζ.wit, S', d.δ⟩ := ⟨rfl, GPos.here hpos', ζ, eζ, kζ, rfl, rfl⟩
  refine ⟨x, hx, hβ, _, hd.sub hsub, S', d.δ, TyEq.extend_left hyS β
    (heS.trans (TyEq.of_agree S' fun z hz => hag z (hpos'.free hz))),
    Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

/-- The witness of an image cell at a `Ref` position of a chain view. -/
theorem immWitW_child {I : List SRec} {x : SRec} (hx : x ∈ I) {d : FrameRec} (hd : DescR x.1 d)
    {p : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} (hch : Chain d.R d.T d.v p l₀ S₀ u₀)
    {A : VTy} {δ δ₀ : LSub} (he : TyEq A δ S₀ δ₀) (hag : AgreeOn S₀ δ₀ d.δ) {y : LifeVar}
    (hy : ¬ VFree y A) {β : Life} (hβ : β ≤ x.2) {m : Loc} {S : VTy} {u : Val}
    (hpos : RefPos A u₀ m S) (hown : d.R.get m = some (CellU.ownOf u)) :
    ImmWitW I m (LSet.singleton β) S (δ.extend y β) := by
  obtain ⟨S', hpos', heS⟩ := hpos.tyEq he
  have hyS : ¬ VFree y S := RefPos.not_free hpos hy
  refine ⟨x, hx, hβ, d, hd, S', d.δ, TyEq.extend_left hyS β
    (heS.trans (TyEq.of_agree S' fun z hz => hag z (hpos'.free hz))),
    Or.inr ⟨d, List.mem_singleton_self _, some l₀, u, hch.snoc hpos' hown, fun _ _ => rfl⟩⟩

/-- The witness of an image cell at a `Mut` position of a chain view: the sub-record there. -/
theorem immWitW_childMut {I : List SRec} {x : SRec} (hx : x ∈ I) {d : FrameRec}
    (hd : DescR x.1 d) (hR : vShape d.T d.δ d.v d.R) {p : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (hch : Chain d.R d.T d.v p l₀ S₀ u₀) {A : VTy} {δ δ₀ : LSub}
    (he : TyEq A δ S₀ δ₀) (hag : AgreeOn S₀ δ₀ d.δ) {y : LifeVar} (hy : ¬ VFree y A)
    {β : Life} (hβ : β ≤ x.2) {m : Loc} {S : VTy} (hpos : MutPos A u₀ m S) :
    ImmWitW I m (LSet.singleton β) S (δ.extend y β) := by
  obtain ⟨S', hpos', heS⟩ := hpos.tyEq he
  have hyS : ¬ VFree y S := fun h => hy (hpos.free h)
  have hg : GPos d.R d.T d.v m S' := GPos.of_chain hch hpos'
  obtain ⟨ζ, eζ, kζ, -⟩ := gpos_mut_cell hg hR (fun _ _ e => e)
  have hsub : SubRec d ⟨m, ζ.erase, ζ.wit, S', d.δ⟩ := ⟨rfl, hg, ζ, eζ, kζ, rfl, rfl⟩
  refine ⟨x, hx, hβ, _, hd.sub hsub, S', d.δ, TyEq.extend_left hyS β
    (heS.trans (TyEq.of_agree S' fun z hz => hag z (hpos'.free hz))),
    Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

/-! ### Small facts -/

/-- An image's cells are `imm` cells. -/
theorem reb_allImm {β : Life} {R c : WRes} (hr : ResU.Reb β R c) :
    ∀ m (ψ : CellU Loc Val), c.get m = some ψ → ψ.kind = Kind.imm :=
  fun _ _ e => (reb_cell hr e).1

/-- **A resource of `imm` cells is consistent with every view**: its exclusive walk is empty. -/
theorem consistentX_allImm {ρ : WRes} (h : ∀ m (ψ : CellU Loc Val), ρ.get m = some ψ →
    ψ.kind = Kind.imm) (c : Loc → Option Life) : ConsistentX c ρ := by
  intro e he l ψ hg _
  obtain rfl : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm h)
  cases hg

/-! ### A chain view's template exists -/

/-- **A chain view's template exists** once a reborrow of the view is handed a shaped image: the
world's joint image of the view if a child of the position has a view (`JointDeep`), the handed
image otherwise (`tmpl_exists` at a chain view). -/
theorem tmplD_exists {W F χ₀ : WRes} {ps rs : List FrameRec} {r : FrameRec} {p₀ : Option Loc}
    {l₀ : Loc} {S₀ : VTy} {u₀ : Val} (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀) {s : LSet}
    {w₀ : WRes} {hs : w₀.InStratum s.join} {x : LifeVar} {β : Life}
    (hT : TWNC W ps rs) (hr : r ∈ rs)
    (hW : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) F W)
    (hx : ¬ VFree x S₀) (hreb₀ : ResU.Reb β w₀ χ₀)
    (hsh₀ : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ χ₀) :
    ∃ c, TmplSpecD r S₀ u₀ w₀ c := by
  have hTI := hT.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨φ, eφ, kφ, -, wφ⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wφ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
    hTI.1.1 r hr p₀ l₀ S₀ u₀ hch aW haW φ eφ (by rw [kφ]; simp)
  rw [wφ] at hw₀den hw₀own
  by_cases hv : ∃ l S u, Chain r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgW W a ∧
      ∃ ψ : CellU Loc Val, a.get l = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨w₀', hw₀', β₀, x₀, c₀, hx₀, hreb₀', hden₀, hA, -⟩ :=
      hTI.1.2.2.2.2.2 r hr p₀ l₀ S₀ u₀ hch hv
    obtain ⟨ψ₀, eψ₀, -, wψ₀⟩ := hw₀' aW haW
    rw [eφ] at eψ₀; cases Option.some.inj eψ₀
    rw [wφ] at wψ₀
    subst wψ₀
    exact ⟨c₀, β₀, x₀, hx₀, hreb₀', hden₀, hA⟩
  · refine ⟨χ₀, β, x, hx, hreb₀, hsh₀, agW_image_noview haW hle hreb₀
      (fun y ψ u hψ hu ζ hζ => ?_)⟩
    obtain ⟨ζ', eζ', hpos⟩ := image_dom S₀ hsh₀ hw₀den hψ
    rw [hu] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    by_contra hk
    exact hv ⟨y, S, u, hch.snoc hS (hw₀own y u hu), aW, haW, ζ, hζ, hk⟩

/-! ### The image's lifetimes, from the run's tags -/

/-- **A reborrow keeps a subset of an `imm` cell's lifetimes** (`RebAt`'s `imm` clause). -/
theorem reb_imm_sub {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc} {t : LSet} {u : Val}
    {w : WRes} {h : w.InStratum t.join} (e : c.get m = some (CellU.immOf t u w h)) {s : LSet}
    {u' : Val} {w' : WRes} {h' : w'.InStratum s.join}
    (eσ : σ.get m = some (CellU.immOf s u' w' h')) : ∀ y, t.mem y → s.mem y := by
  obtain ⟨-, π, b, hdom, -, -, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  obtain ⟨⟨t', ht', hsub, he⟩, -⟩ := (hbody l₀ q hpm).2.2.2 s u' w' h' eσ
  rw [e] at he
  obtain ⟨rfl, -, -⟩ := CellU.immOf_inj (Option.some.inj he)
  exact hsub

/-- **A reborrow's cell at an `own` location of the source has a part of the source as its
witness** (`RebAt`'s `own` clause). -/
theorem reb_own_wit {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc} {ψ : CellU Loc Val}
    (e : c.get m = some ψ) {u : Val} (eσ : σ.get m = some (CellU.ownOf u)) :
    ∃ q, ResU.Le q σ ∧ ψ.wit = q.del m := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  obtain ⟨hh, he⟩ := (hbody l₀ q hpm).2.1 u eσ
  rw [e] at he
  cases Option.some.inj he
  exact ⟨q, hle'.trans hle, by rw [CellU.wit_immOf]⟩

/-- **The source's payload is bounded by the run's tags** (Core's `lifeBound_of_tagged`, at the
cells of an `imm` cell's witness and at the world's records): an `imm` cell beneath a top-level
`imm` cell of the run's typed world sits, with its lifetimes, in `ag(W)` (`AgW.imm_wit_le`); a
world record coherent at its location is on the list with its lifetime (`ImmTieL`), tagged by a
record proper whose lineage holds the location (`linLoc_of_rel`), whose views are no
longer-lived than the tag (`FrameLife`). -/
theorem lifeBoundW_of_entry {W : WRes} {ps : List FrameRec} {ls I : List SRec}
    (hv : ResU.Valid W) (htg : Tagged W ps ls) (hI : ImmTieL I ls) {l : Loc} {s : LSet}
    {v : Val} {σ : WRes} {h : σ.InStratum s.join} (e : W.get l = some (CellU.immOf s v σ h)) :
    LifeBoundW I σ := by
  intro m t u σ' h' eσ _ x hx d hd S δ₀ hco y hy
  obtain ⟨p, -, hpx, hFL⟩ := htg x (hI x hx)
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨ev, av, q, z, -, hav, hq, hz⟩ := AgW.imm_wit_le haW e (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at hav
  have hicp : ICp aW m (CellU.immOf t u σ' h') :=
    icp_trans (icp_trans (icpAt_agW hav m _ eσ) (icpAt_right hq m)) (icpAt_left hz m)
  obtain ⟨ζ, t', eζ, ht', hyt⟩ := hicp.ls (CellU.lsOf_immOf _ _ _ _) hy
  obtain ⟨S₀, δ₁, -, hc⟩ := hco
  have hm : m = d.le ∨ ∃ q S u, Chain d.R d.T d.v q m S u := by
    rcases hc with ⟨r, hr, h₁, -, -⟩ | ⟨r, hr, q', u', h₁, -⟩
    · rw [List.mem_singleton] at hr; subst hr; exact .inl h₁
    · rw [List.mem_singleton] at hr; subst hr; exact .inr ⟨q', _, u', h₁⟩
  rcases linLoc_of_rel (hpx.trans hd) hm with ⟨-, rfl⟩ | hL
  · exact le_of_eq (hFL.1 aW haW ζ t' eζ ht' y hyt)
  · exact hFL.2 aW haW m hL ζ t' eζ ht' y hyt

/-- **A reborrow's kept cells are bounded where the source is**. -/
theorem lifeBoundOn_reb {I : List SRec} {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c)
    (hσ : LifeBoundW I σ) :
    LifeBoundOn I (fun m => ∃ ζ, σ.get m = some ζ ∧ ζ.kind = Kind.imm) c := by
  intro m t u w h e ⟨ζ, eζ, kζ⟩ x hx d hd S δ₀ hco y hy
  obtain ⟨s', h', hζe⟩ := CellU.imm_eta kζ
  rw [hζe] at eζ
  exact hσ m s' _ _ h' eζ trivial x hx d hd S δ₀ hco y (reb_imm_sub hr e eζ y hy)

/-- **A reborrow's witnesses at the source's `own` locations are bounded where the source is.** -/
theorem lifeBoundWit_reb {I : List SRec} {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c)
    (hσ : LifeBoundW I σ) : LifeBoundWit I σ c := by
  intro m ψ e ⟨u, eσ⟩
  obtain ⟨q, ⟨τ, hτ⟩, hw⟩ := reb_own_wit hr e eσ
  rw [hw]
  intro m' t u' w h e' _ x hx d hd S δ₀ hco y hy
  have hne : m' ≠ m := fun h => by subst h; rw [ResU.del_get_self] at e'; cases e'
  rw [ResU.del_get_ne _ hne] at e'
  obtain ⟨t'', h'', e'', ht⟩ := imm_piece_left hτ e'
  exact hσ m' t'' u' w h'' e'' trivial x hx d hd S δ₀ hco y (ht y hy)

/-! ### The reborrow at the loaded cell -/

/-- `Imm̲` at `δ['x ↦ β]` against a record's type at its own substitution. -/
theorem tyEq_immReb {A T : VTy} {δ δ' : LSub} (he : TyEq A δ T δ') {x y : LifeVar}
    (hx : ¬ VFree x A) (hy : ¬ VFree y T) (β : Life) :
    TyEq (A.immReborrow (.var x)) (δ.extend x β) (T.immReborrow (.var y)) (δ'.extend y β) :=
  TyEq.immReborrow (by rw [interp_ext_self, interp_ext_self])
    (TyEq.extend_left hy β (TyEq.extend_left hx β he).symm).symm

/-! ### `wl`'s antecedent -/

/-- **`wl`'s antecedent holds** at the hardest case's row. -/
theorem wl_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend _ x _⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
