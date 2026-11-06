import Core.Chain.Inst791N
import Core.Chain.ImmImage791N
import Core.Chain.ImmTie791N
import Core.Chain.SI.RebRaiseC

/-!
# `withload` at a suspending row  `[spec §62]`

Core's `withload_compatX` (`Core/Compatibility.lean:252`), step by step (`chain-interpretation.md`
§6.3), at a `Row.Suspend` callback row:

* **The tables.** The callback's table is the constant's (`tabN_extend_suspendC`): the row's
  layers do not mention `'x`. It may be stopped at under a reborrow at `β ⊏ @bnd`
  (`tabN_rebOKR`), and its cancel obligations are closed under the reborrow (`tab_rebClosed`,
  by induction on how deep cancel rows nest, `erwp_rebGen_cancelRun` at each level: the
  `tabR_canA` pattern).
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
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 defines_meetOfDom_empty)
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

/-- A row's cancel obligation reads `δ` only through its table. -/
theorem finN_of_tabN : ∀ (F : CTy) {δ₁ δ₂ : LSub} {Θ : LocTy} {c : Loc → Option Life},
    tabN (ℍ := ℍ) F δ₁ Θ c = tabN (ℍ := ℍ) F δ₂ Θ c →
      finN (ℍ := ℍ) F δ₁ Θ c = finN (ℍ := ℍ) F δ₂ Θ c
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, h => by
      simp only [tabN] at h
      simp only [finN, h]
  | .ret _, _, _, _, _, _ => rfl
  | .arr _ _, _, _, _, _, _ => rfl
  | .amp _ _, _, _, _, _, _ => rfl
  | .top, _, _, _, _, _ => rfl
  | .all _ _ _, _, _, _, _, _ => rfl
  | .nu _, _, _, _, _, _ => rfl

/-- **A row whose layers do not mention `'x` has one table at `δ` and `δ['x ↦ α]`.** -/
theorem tabN_extend_suspendC {x : LifeVar} {bnd : Lifetime.Life} (α : Life) :
    ∀ (F : CTy), F.SuspendC x bnd → ∀ (δ : LSub) (Θ : LocTy) (c : Loc → Option Life),
      tabN (ℍ := ℍ) F (δ.extend x α) Θ c = tabN (ℍ := ℍ) F δ Θ c
  | .eff m i q A B fin rc C, hF, δ, Θ, c => by
      obtain ⟨⟨_, hA, hB, _, _, hfin⟩, hC⟩ := hF
      simp only [tabN]
      rw [vN_extend_of_not_free hA, vN_extend_of_not_free hB,
        tabN_extend_suspendC α C hC δ Θ c,
        entN_fin_congr (f := finN (ℍ := ℍ) fin (δ.extend x α) Θ c) (f' := finN (ℍ := ℍ) fin δ Θ c)
          (fun hcap => finN_of_tabN fin (tabN_extend_suspendC α fin (hfin hcap) δ Θ c))]
  | .ret _, _, _, _, _ => rfl
  | .arr _ _, _, _, _, _ => rfl
  | .amp _ _, _, _, _, _ => rfl
  | .top, _, _, _, _ => rfl
  | .all _ _ _, _, _, _, _ => rfl
  | .nu _, _, _, _, _ => rfl

/-- **A cancel row meeting `CTy.SuspendC` may be stopped at under a reborrow at `β ⊏ @bnd`**:
its layers' payload and answer types outlive the bound, so their values lie in `Res_β`. -/
theorem tabN_rebOKR {x : LifeVar} {bnd : Lifetime.Life} {β : Life} {F : CTy}
    (hF : F.SuspendC x bnd) (δ : LSub) (hLt : LtLife δ bnd β) (Θ : LocTy)
    (c : Loc → Option Life) : (tabN (ℍ := ℍ) F δ Θ c).RebOKR β where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    obtain ⟨-, -, -, hOA, -⟩ := layer_suspend F hF hL
    exact vN_inStratum_bnd hOA hLt hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    obtain ⟨-, -, -, -, hOB, -⟩ := layer_suspend F hF hL
    exact vN_inStratum_bnd hOB hLt hp.1

/-- **The cancel obligations of a row meeting `CTy.SuspendC` are closed under a reborrow at
`β ⊏ @bnd`**, by induction on how deep cancel rows nest: each is a cancel run at its cancel row's
table, closed by `erwp_rebGen_cancelRun`, whose own cancel obligations are closed by the
induction. -/
theorem tab_rebClosed {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {β : Life} (hLt : LtLife δ bnd β) {le : Loc} {s : LSet} {v : Val}
    {R : WRes} {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop}
    (hE : RebEntryG (ℍ := ℍ) (Θ.view c) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok)
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
      RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok (tabN (ℍ := ℍ) F δ Θ c) := by
  intro d
  induction d with
  | zero =>
      intro F hd hF m i en h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupN F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hFs m i en h ha hql P hP
  obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hFs hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  simp only [entN, hcap, if_true] at hP
  by_cases htop : fin = .top
  · subst htop; simp [finN] at hP
  rw [finN_eq htop] at hP
  cases Option.some.inj hP
  refine ⟨fun k ls e ρb ρ hc hb hr hA => ?_, fun k ls e ρ g ρg hc hg h => erwp_garbage hc hg h⟩
  exact erwp_rebGen_cancelRun hE hreb hOk (tabN_rebOKR hfin δ hLt Θ c) (ih fin hfd hfin)
    k ls e ρb ρ hc hb hr hA

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

theorem vO_le {A : VTy} {δ : LSub} {Θ : LocTy} {k n : Nat} (hkn : k ≤ n) {v : Val} {ρ : WRes}
    (h : vO (ℍ := ℍ) A δ Θ n v ρ) : vO (ℍ := ℍ) A δ Θ k v ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (vO_down A δ Θ _ v ρ (by rwa [← Nat.add_assoc] at h))

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

/-- **The callback at the image**: the callback, at `β ⊏ @bnd`, applied to the image `χ` of the
loaded payload, typed at `Imm̲ 'x A`, runs at the constant's table with `[β]𝒱⟦B⟧` as its post. -/
theorem callback_at_image {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    (hB : ¬ VFree x B) (hS : S.Suspend x bnd) {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {f u : Val} {ρf χ Bχ : WRes} {β : Life}
    (hLt : LtLife δ bnd β)
    (hf : vN (ℍ := ℍ) (cbUTy x bnd (A.immReborrow (.var x)) B S) δ Θ n f ρf)
    (hcf : ConsistentX c ρf) (hχ : ∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm)
    (himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ)
    (hBχ : ResU.CompS ρf χ Bχ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
      (RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)) n ls
      (.app (.app (.val f) (.val .unit)) (.val u)) Bχ := by
  have h1 := (hf Θ (LocTy.extR_refl _ _) hΘ c hcf ls) β hLt
  have hcon : ConsistentX c Bχ := consistentX_compS hBχ hcf (consistentX_allImm hχ c)
  have h2 := h1 c n le_rfl u χ Bχ hBχ himg hcon
  rw [cN_effOf, tabN_extend_suspendC β _ (suspendC_effOf hS _) δ Θ c,
    tabN_effOf_base S (.box (.var x) B) B δ Θ c] at h2
  refine erwp_mono (fun k _ w ρ hb => ?_) (opTableN_local _) n ls _ Bχ h2
  obtain ⟨α', hα', hbB, hst⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  rw [vN_extend_of_not_free hB] at hbB
  exact ⟨hbB, hst⟩

/-- **Step 8 at the run's first entry** (`withload_compatX`'s steps 6–11): the loaded cell
`ℓ ↦ imm(s, v, σ)`, its payload observable at `A`, its location witnessed in the world's `imm`
records, and the callback. At the run's first entry the tie puts the witness's record on the
run's list (`cohE_of_immWitW`); the cell is that record's own cell (`TI`'s `leInvW`) or one of
its chain views (`exIn`); the image re-taken at a `β` below the cell, the callback's stratum and
the bound is a value of `Imm̲ 'x A` (`relabel_vN`), and 6.150 across the callback's stops, raises
and layered cancel runs (`erwp_rebGen`) gives the run. The table's premises are `hTab` (the
table may be stopped at under the reborrow) and `hClo` (its cancel obligations are closed under
it). The callback's run at the image is the premise `hcb`: at a suspending row
`callback_at_image`, at an unwinding row `callback_at_imageU`, at the pure row its `F (U …)`
form. -/
theorem withload_rebT {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {δ : LSub} (hbnd : ∃ γ, bnd.interp δ = some γ) (hA : ¬ VFree x A)
    {Θ : LocTy} {c : Loc → Option Life}
    (hTab : ∀ β, LtLife δ bnd β → (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c).RebOKR β)
    (hClo : ∀ β, LtLife δ bnd β → ∀ {le : Loc} {s : LSet} {v : Val} {R : WRes}
      {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop},
      RebEntryG (ℍ := ℍ) (Θ.view c) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok →
      ResU.Reb β R χ →
      (∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
        ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO) →
      RebClosed β (ResU.single le (CellU.immOf s v R hs)) χ Ok
        (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
    {n : Nat} {ls : List SRec} {f v : Val} {l : Loc} {s : LSet} {σ : WRes}
    {h : σ.InStratum s.join} {ρf X : WRes}
    (hpay : vO (ℍ := ℍ) A δ Θ n v σ) (hwit : ImmWitW Θ.imm l s A δ)
    (hcb : ∀ β, LtLife δ bnd β → ∀ (u : Val) (χ Bχ : WRes),
      (∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm) →
      vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ → ResU.CompS ρf χ Bχ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
        (RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)) n ls
        (.app (.app (.val f) (.val .unit)) (.val u)) Bχ)
    (hX : ResU.CompS (ResU.single l (CellU.immOf s v σ h)) ρf X) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
      (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) X := by
  rw [erwp_eq]
  intro ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin
  -- the cell is a top-level piece of the run's typed world
  obtain ⟨Fr, -, hcell⟩ := compS_lcomm hX hcF
  have hTI := hT.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨s'', hs'', hle⟩ := cell_of_compS_single hcell
  obtain ⟨φ₁, eφ₁, kφ₁, rφ₁, wφ₁⟩ := AgW.get_imm haW hle (CellU.kind_immOf _ _ _ _)
  simp only [CellU.erase_immOf, CellU.wit_immOf] at rφ₁ wφ₁
  -- step 6: the tie puts the witness's record on the run's list
  have hI' : ImmTieL Θ.imm ls := hI
  obtain ⟨xr, hxr, hxrs, d, hd, hdmem, S₀, δ₀, he, hcoh⟩ := cohE_of_immWitW hT hI' hwit
  -- the source's payload is bounded by the run's tags
  have hLσ : LifeBoundW Θ.imm σ := lifeBoundW_of_entry (hash_valid_comp hF hcF) htg hI' hle
  have hR₀ : vShape d.T d.δ d.v d.R := (hTI.1.2.2.2.1 d hdmem).1
  -- step 9: the fresh `β`, below the cell, the callback's stratum and the bound
  obtain ⟨γb, hγb⟩ := hbnd
  obtain ⟨g, hg⟩ := ResU.exists_stratum ρf
  set β : Life := ↓(s.meet ⊓ g ⊓ γb) with hβdef
  have hβlt : β < s.meet ⊓ g ⊓ γb := Life.down_sqsubset _
  have hβs : β < s.meet := lt_of_lt_of_le hβlt (inf_le_left.trans inf_le_left)
  have hβx : β ≤ xr.2 := hβs.le.trans hxrs
  have hβg : β ≤ g := (lt_of_lt_of_le hβlt (inf_le_left.trans inf_le_right)).le
  have hLt : LtLife δ bnd β := ⟨γb, hγb, lt_of_lt_of_le hβlt inf_le_right⟩
  have hσβ : σ.InStratum β := h.mono (hβs.le.trans (LSet.meet_le_join s))
  have hbβ : ρf.InStratum β := hg.mono hβg
  have hT' := hTab β hLt
  rcases hcoh with ⟨rfl, rfl, hag⟩ | ⟨p, u₀, hch, hag⟩
  · -- the record's own cell: `v = d.v`, `σ = d.R`
    obtain ⟨φ, eφ, -, rφ, wφ⟩ := hTI.leInvW d hdmem aW haW
    rw [eφ₁] at eφ; cases Option.some.inj eφ
    have hv : v = d.v := rφ₁.symm.trans rφ
    have hσ : σ = d.R := wφ₁.symm.trans wφ
    subst hv hσ
    -- step 7: the template, from 6.132 at the record's shape
    set y := d.T.lifeBound with hydef
    have hy : ¬ VFree y d.T := fun hf' => lt_irrefl _ (lt_vLifeBound hf')
    obtain ⟨γ, hγ⟩ := six132_shape_fresh hy d.δ d.v d.R hR₀
    obtain ⟨⟨χ₀, hreb₀, hsh₀⟩, -⟩ := hγ (↓γ) (Life.down_sqsubset γ)
    have hSt : TmplSpec d (tmpl d) := tmpl_spec (tmpl_exists hT hdmem hcell hy hreb₀ hsh₀)
    have hheA : TyEq A δ d.T d.δ := he.trans (TyEq.of_agree d.T hag)
    -- step 8: the image re-taken at `β`, typed at `Imm̲ 'x A`
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n d.v (canon d β) := by
      obtain ⟨β₁, x₁, hx₁, hreb₁, hden₁, -⟩ := hSt
      have hden₁' : vShape (A.immReborrow (.var x)) (δ.extend x β₁) d.v (tmpl d) := by
        rw [vShape_tyEq (tyEq_immReb hheA hA hx₁ β₁)]; exact hden₁
      exact relabel_vN A hA hA hden₁' hpay (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
        (fun m ψ e => reb_cell_match hreb₁ e) (reb_wit_stratum hσβ hreb₁)
        (lifeBoundOn_reb hreb₁ hLσ) (lifeBoundWit_reb hreb₁ hLσ)
        (fun m S u hpos hown => immWitW_root hxr hd he hag hA hβx hpos hown)
        (fun m S hpos => immWitW_rootMut hxr hd hR₀ he hag hA hβx hpos)
    have hshape : vShape (d.T.immReborrow (.var y)) (d.δ.extend y β) d.v (canon d β) := by
      rw [← vShape_tyEq (tyEq_immReb hheA hA hy β)]
      exact vN_vShape _ _ _ _ _ _ himg
    have hreb := canon_reb hSt hσβ
    have hE := rebEntryG_top (ℍ := ℍ) (Φ := Θ.view c) (hs := h) d y hy hSt hσβ hshape
      (fun z hz => hβs.le.trans (s.meet_least z hz))
    have hcan := hClo β hLt hE hreb okKept_top
    have hrun' := erwp_rebGen hE hreb okKept_top hT' hcan
      (Q := fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val d.v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) himg hBχ)
    rw [erwp_eq] at hrun'
    exact hrun' ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin
  · -- a chain view: the cell's value is the chain's (`ex(R)_○` lifts into `ag(W)`)
    obtain ⟨e₀, he₀, hlift⟩ := hTI.exIn hdmem aW haW
    obtain ⟨ζ, eζ, rζ, -⟩ := exR_cell he₀ hch.own (by simp)
    obtain ⟨ζ', eζ', rζ', -⟩ := hlift l ζ eζ
    rw [eφ₁] at eζ'; cases Option.some.inj eζ'
    simp only [CellU.erase_ownOf] at rζ
    have hv : v = u₀ := rφ₁.symm.trans (rζ'.trans rζ)
    subst hv
    -- the view's owned cells are the record's, and its witness is shaped (`DeepInv`)
    obtain ⟨-, hσden, hσown, -, -⟩ :=
      hTI.1.1 d hdmem p l S₀ v hch aW haW φ₁ eφ₁ (by rw [kφ₁]; simp)
    rw [wφ₁] at hσden hσown
    -- step 7: the view's template, from 6.132 at the view's shape
    set y := S₀.lifeBound with hydef
    have hy : ¬ VFree y S₀ := fun hf' => lt_irrefl _ (lt_vLifeBound hf')
    obtain ⟨γ, hγ⟩ := six132_shape_fresh hy d.δ v σ hσden
    obtain ⟨⟨χ₀, hreb₀, hsh₀⟩, -⟩ := hγ (↓γ) (Life.down_sqsubset γ)
    have hSt : TmplSpecD d S₀ v σ (tmplD d S₀ v σ) :=
      tmplD_spec (tmplD_exists hch hT hdmem hcell hy hreb₀ hsh₀)
    have hheA : TyEq A δ S₀ d.δ := he.trans (TyEq.of_agree S₀ hag)
    -- step 8: the view's image re-taken at `β`, typed at `Imm̲ 'x A`
    have himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n v
        (canonD d S₀ v σ β) := by
      obtain ⟨β₁, x₁, hx₁, hreb₁, hden₁, -⟩ := hSt
      have hden₁' : vShape (A.immReborrow (.var x)) (δ.extend x β₁) v (tmplD d S₀ v σ) := by
        rw [vShape_tyEq (tyEq_immReb hheA hA hx₁ β₁)]; exact hden₁
      exact relabel_vN A hA hA hden₁' hpay (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
        (fun m ψ e => reb_cell_match hreb₁ e) (reb_wit_stratum hσβ hreb₁)
        (lifeBoundOn_reb hreb₁ hLσ) (lifeBoundWit_reb hreb₁ hLσ)
        (fun m S u hpos hown => immWitW_child hxr hd hch he hag hA hβx hpos (hσown m u hown))
        (fun m S hpos => immWitW_childMut hxr hd hR₀ hch he hag hA hβx hpos)
    have hshape : vShape (S₀.immReborrow (.var y)) (d.δ.extend y β) v (canonD d S₀ v σ β) := by
      rw [← vShape_tyEq (tyEq_immReb hheA hA hy β)]
      exact vN_vShape _ _ _ _ _ _ himg
    have hreb := canonD_reb hSt hσβ
    have hβc : (CellU.immOf s v σ h).InStratum β := (CellU.inStratum_immOf β s v σ h).mpr hβs
    have hE := rebEntryG_deep (ℍ := ℍ) (Φ := Θ.view c) d hch y hy hSt hσβ hβc hshape
    have hcan := hClo β hLt hE hreb (okKept_deep hch)
    have hrun' := erwp_rebGen hE hreb (okKept_deep hch) hT' hcan
      (Q := fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) ρf X hX hbβ hdmem
      (fun Bχ hBχ => hcb β hLt _ _ Bχ (reb_allImm hreb) himg hBχ)
    rw [erwp_eq] at hrun'
    exact hrun' ρF fρ ps μ hF hcF hT htg hI hl hfd j μ' e' hj hrun hfin

/-- **`withload_rebT` at a suspending row**: the row's table may be stopped at under the
reborrow (`tabN_rebOKR`), and its cancel obligations are closed under it (`tab_rebClosed`). -/
theorem withload_reb {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {δ : LSub} (hbnd : ∃ γ, bnd.interp δ = some γ) (hA : ¬ VFree x A)
    (hS : S.Suspend x bnd) {Θ : LocTy} {c : Loc → Option Life}
    {n : Nat} {ls : List SRec} {f v : Val} {l : Loc} {s : LSet} {σ : WRes}
    {h : σ.InStratum s.join} {ρf X : WRes}
    (hpay : vO (ℍ := ℍ) A δ Θ n v σ) (hwit : ImmWitW Θ.imm l s A δ)
    (hcb : ∀ β, LtLife δ bnd β → ∀ (u : Val) (χ Bχ : WRes),
      (∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm) →
      vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ → ResU.CompS ρf χ Bχ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
        (RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)) n ls
        (.app (.app (.val f) (.val .unit)) (.val u)) Bχ)
    (hX : ResU.CompS (ResU.single l (CellU.immOf s v σ h)) ρf X) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
      (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) n ls
      (.app (.app (.val f) (.val .unit)) (.val v)) X :=
  withload_rebT hbnd hA (fun _ hLt => tabN_rebOKR (ℍ := ℍ) (suspendC_effOf hS B) δ hLt Θ c)
    (fun _ hLt _ _ _ _ _ _ _ hE hreb hOk => tab_rebClosed (ℍ := ℍ) (x := x) (δ := δ) (Θ := Θ)
      (c := c) hLt hE hreb hOk _ _ le_rfl (suspendC_effOf hS B)) hpay hwit hcb hX

/-! ### `withload` at a suspending row -/

/-- **`withload` at a suspending row is a value of `!` its type**: at
`Imm @a A ⊸ (∀'x ⊏ @bnd. Imm̲ 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ B` with `Σ` a `Row.Suspend x bnd` row.
Core's `withload_compatX`, step by step (`chain-interpretation.md` §6.3):

1. the context owns nothing: the constant at `PMap.empty`;
2. the `Imm` argument is `loc ℓ` (`vN`'s `Imm` clause);
3. the callback, at the same world: `⊸` is a plain wand;
4. both are at the world `Θ` the run is at, which the thunk's `U` reached;
5. the load: its payload observable at `A` (`rwp_load_I` under `erwp_bindR`);
6.–11. at the run's first entry (`withload_reb`): the record whose cell or chain view the source
   is, at the source's type (the tie and `TI`); its template (6.132, `tmpl_exists`,
   `tmplD_exists`); the image typed at `Imm̲ 'x A` (`relabel_vN`); the fresh `β`; 6.150 across the
   callback's stops, raises and layered cancel runs (`erwp_rebGen`); the callback at `δ['x ↦ β]`
   (`callback_at_image`);
12.–13. the result `['x] B` read at `B` (`vN_extend_of_not_free`).

Premises, and the rule that supplies each: `hbnd` is the bound's definedness (`Const791.OK`'s
first conjunct); `hA`, `hB`, `hS` are `withloadU`'s with `Row.Suspend` for `Row.Unwind`
(`Const791.OK`). -/
theorem withloadS_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Suspend x bnd) (δ : LSub) (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withloadUTy a x bnd A B S)) δ Θ₀ n withloadV PMap.empty := by
  -- step 1
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  -- steps 2–4
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨α₀, hα₀, ⟨l, s, w, σ, hσs, rfl, rfl, hα₀s, hpay⟩, hwit⟩ :=
    vN_le hk' hu
  rw [cN_effOf]
  refine erwp_of_valid fun hv'' => ?_
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  have hTd := opTableN_down (tabN_down (ℍ := ℍ) (CTy.effOf S B) δ Θ hΘ.1 c)
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  refine erwp_det hΦ hTd hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ hTd hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (.app (.app v0 unit') (.app load' v1)))) =
      (Kont.appR (.app (.val f) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, Val.shift, Val.loc, Expr.val, Val.prim, v0, v1,
      unit', load', Val.unit]
  rw [e₃]
  -- step 5: the load
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load_cell ls l s w σ hσs _ hc' ?_
  -- steps 6–13
  simp only [Kont.plug]
  exact withload_reb (hbnd δ (models_empty_any _)) hA hS (vO_le (Nat.sub_le k' 1) hpay)
    (hwit l s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ himg hBχ =>
      callback_at_image hB hS hΘ hLt (vN_le (Nat.sub_le k' 1) hf) hcf hχ himg hBχ) hc' 

/-- **`ConstN` for `withload` at a suspending row**, from its rule's premises. -/
theorem constN_wl {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} : ConstN (ℍ := ℍ) (.wl a x bnd A B S) := by
  rintro ⟨hbnd, hA, hB, hS⟩ δ Θ n _
  exact withloadS_compat hbnd hA hB hS δ Θ n

/-- **`withload` at the hardest case's row**, every hypothesis of `withloadS_compat` discharged:
an `Imm @a 1` source at the bound `LifeCtx.empty.meetOfDom`. -/
theorem withloadS_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withloadUTy a x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      withloadV PMap.empty :=
  withloadS_compat defines_meetOfDom_empty id id (hardestRow_suspend x _) δ Θ n

/-- **`wl`'s antecedent holds** at the hardest case's row. -/
theorem wl_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend x _⟩

/-- **`ConstN` at the hardest case's `withload`**, its antecedent discharged (`wl_ok`). -/
theorem constN_wl_inst (a : Lifetime.Life) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat)
    (hΘ : Θ.OK) :
    vN (ℍ := ℍ) (.bang (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).ty) δ Θ n
      (Const791.wl a x LifeCtx.empty.meetOfDom .unit .unit hardestRow).val PMap.empty :=
  constN_wl (wl_ok a x) δ Θ n hΘ

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
