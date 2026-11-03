import PoolSpike.Machine

/-!
# Pool spike: the invariant over the pool

* **`CInv`** is `CactusInvT` without its points (`AtPoints`): the branches compose to the world,
  the records proper are theirs, apart by location, and `RecInv`, `WInv` hold. The points are
  not kept by a run whose postcondition names no point (`cactusT_step`'s `hpt`), and a parked
  share holding views at two incomparable lifetimes sits at none. Nothing below reads them.
* **`PoolEsc`**: for every two branches, neither holds anything of a lend of the other's records
  (`FdEsc`). It is the join condition in location form, which the scheduler spike found crosses
  `twp`'s extension where the points do not; here it is what keeps the relevant records of a
  parked share alive.

The facts about the carrier: a location frozen in a resource is in each of its flattenings
(`FrzT.flat`); so a branch the share of which a record of `p`'s lineage is relevant to holds part
of `p`'s lend (`relFT_not_fdEsc`); `FdEsc` is carried along re-reading (`fdEsc_rr`) and read off
the masks of a run's own records (`noneAt_recMask`, `fdEsc_of_noneAt`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp.Pool
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap)

variable {K : WCactus}

/-! ### Frozen locations are in every flattening -/

theorem _root_.BoCa.Fig16.Tree.Wp.InDomT.cellAt {σ : TRes K} {m : BoCa.Loc} (h : InDomT σ m) : ∃ χ, CellAt σ m χ := by
  induction h with
  | top e => exact ⟨_, .top e⟩
  | wit e _ _ ih =>
      obtain ⟨χ, hχ⟩ := ih
      exact ⟨χ, .nest e hχ⟩

/-- A frozen location is an `imm` cell at depth, or beneath one. -/
theorem _root_.BoCa.Fig16.Tree.Wp.FrzT.immCell {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) :
    ∃ (y : BoCa.Loc) (ψ₀ : TCell K), CellAt ρ y ψ₀ ∧ ψ₀.kind = Kind.imm ∧
      (m = y ∨ ∃ χ, CellAt ψ₀.wit m χ) := by
  induction h with
  | imm e k => exact ⟨_, _, .top e, k, .inl rfl⟩
  | inImm e k hd =>
      obtain ⟨χ, hχ⟩ := hd.cellAt
      exact ⟨_, _, .top e, k, .inr ⟨χ, hχ⟩⟩
  | inMut e _ _ ih =>
      obtain ⟨y, ψ₀, hc, hk, hm⟩ := ih
      exact ⟨y, ψ₀, .nest e hc, hk, hm⟩

/-- **A frozen location is in every flattening.** -/
theorem _root_.BoCa.Fig16.Tree.Wp.FrzT.flat {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) {τ : TRes K}
    (hτ : ResUT.Flat ρ τ) : τ.get m ≠ none := by
  obtain ⟨y, ψ₀, hc, hk, hm⟩ := h.immCell
  obtain ⟨er, ar, -, har, hcr⟩ := hτ
  have : ∃ ζ, ar.get m = some ζ := by
    rcases hm with rfl | ⟨χ, hχ⟩
    · obtain ⟨ζ, e, -⟩ := cellAt_imm_icp hc har hk
      exact ⟨ζ, e⟩
    · exact cellAt_beneath_imm_ag hc hk hχ har
  obtain ⟨ζ, eζ⟩ := this
  obtain ⟨ξ, eξ⟩ := comp_some_r hcr eζ
  rw [eξ]; simp

/-- **A share a record of `p`'s lineage is relevant to holds part of `p`'s lend.** -/
theorem relFT_not_fdEsc {p r : FrameRecT K} (hd : DescRT p r) {ρ : TRes K} (hrel : RelFT r ρ)
    (hv : ResUT.Valid ρ) (hpv : ResUT.Valid p.R) (hF : FdEsc p.le p.R ρ) : False := by
  obtain ⟨m, hf, hm⟩ := hrel
  obtain ⟨τ, hτ⟩ := hv
  have hne := hf.flat hτ
  rcases linLoc_of_relAt hd hm with rfl | hl
  · exact hne (hF τ hτ).1
  · obtain ⟨σR, eR, aR, heR, -, -⟩ := hpv
    exact hne ((hF τ hτ).2 eR heR m (hl.exDom.exST heR))

/-! ### `FdEsc` and the masks -/

theorem noneAt_recMask {O : List (FrameRecT K)} {ρ : TRes K} (hv : ∀ q ∈ O, ResUT.Valid q.R)
    (h : ∀ q ∈ O, FdEsc q.le q.R ρ) : NoneAt (recMask O) ρ := by
  rintro τ hτ x ⟨q, hq, hx⟩
  rcases hx with rfl | hx
  · exact (h q hq τ hτ).1
  · obtain ⟨σR, eR, aR, heR, -, -⟩ := hv q hq
    exact (h q hq τ hτ).2 eR heR x (hx.exST heR)

/-- `FdEsc` of a typed record proper read off the masks of a list holding it. -/
theorem fdEsc_of_noneAt {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) {O : List (FrameRecT K)}
    {p : FrameRecT K} (hp : p ∈ O) (hpps : p ∈ ps) {ρ : TRes K} (h : NoneAt (recMask O) ρ) :
    FdEsc p.le p.R ρ := by
  have hTI := hT.inv
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hpps, [], .nil p⟩
  intro τ hτ
  refine ⟨h τ hτ _ ⟨p, hp, .inl rfl⟩, fun eR heR x hxs => ?_⟩
  obtain ⟨ψx, eψx⟩ := Option.isSome_iff_exists.mp hxs
  obtain ⟨d, hd, ζ, eζ, kζ⟩ := exST_lineage Θ heR p rfl (hTI.1.2.2.2.1 p hprs) x ψx eψx
  exact h τ hτ x ⟨p, hp, .inr (LinLocT.exDom ⟨d, hd, ζ, eζ, kζ⟩)⟩

/-- **`FdEsc` is carried along re-reading**, of the resource and of the record. -/
theorem fdEsc_rr {K' : WCactus} (hE : K.Ext K') {Θ' : CodeTy} {tc' : TChoice K'}
    {W' : TRes K'} {ps' rs' : List (FrameRecT K')} (hT : TWNT K' Θ' tc' W' ps' rs')
    {p : FrameRecT K} {p' : FrameRecT K'} (hpp : RecRR Θ' p p') (hp' : p' ∈ ps')
    (hpv : ResUT.Valid p.R) {ρ : TRes K} {ρ' : TRes K'} (hv : ResUT.Valid ρ)
    (hr : RR (sem Θ') ρ ρ') (h : FdEsc p.le p.R ρ) : FdEsc p'.le p'.R ρ' := by
  have h₀ : NoneAt (recMask [p]) ρ := noneAt_recMask (by simpa using hpv) (by simpa using h)
  have h₁ : NoneAt (recMask [p]) ρ' := h₀.rr hE hv hr
  have h₂ : NoneAt (recMask [p']) ρ' :=
    h₁.mono fun x hx => (recMask_rr (List.Forall₂.cons hpp .nil) x).mpr hx
  exact fdEsc_of_noneAt hT (List.mem_singleton_self _) hp' h₂

/-! ### The invariant without points -/

/-- `CactusInvT` without its points. -/
def CInv (w : TWd) (bs : List (TBranch w.K)) (W : TRes w.K) (ps : List (FrameRecT w.K))
    (ls : List (SRecT w.K)) (μ : Heap) : Prop :=
  CompAllT (bs.map Prod.fst) W ∧ (∀ p, p ∈ ps ↔ p ∈ (bs.map Prod.snd).flatten) ∧
    Apart (bs.map Prod.snd) ∧ RecInv w W ps ls ∧ WInv w W μ

theorem CInv.of_cactus {w : TWd} {bs : List (TBranch w.K)} {ns : List Life} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (h : CactusInvT w bs ns W ps ls μ) : CInv w bs W ps ls μ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- **Neither of two branches holds anything of a lend of the other's records.** -/
def EscApart {K : WCactus} (a b : TBranch K) : Prop :=
  (∀ p ∈ a.2, FdEsc p.le p.R b.1) ∧ (∀ p ∈ b.2, FdEsc p.le p.R a.1)

abbrev PoolEsc {K : WCactus} (bs : List (TBranch K)) : Prop := List.Pairwise EscApart bs

theorem escApart_symm {K : WCactus} : Symmetric (EscApart (K := K)) :=
  fun _ _ h => ⟨h.2, h.1⟩

theorem compAllT_perm {ρs ρs' : List (TRes K)} (hp : ρs.Perm ρs') :
    ∀ {W : TRes K}, CompAllT ρs W → CompAllT ρs' W := by
  induction hp with
  | nil => exact id
  | cons x _ ih =>
      intro W h
      cases h with
      | cons hr hc => exact .cons (ih hr) hc
  | swap x y l =>
      intro W h
      cases h with
      | cons hr hc =>
      cases hr with
      | cons hr' hc' =>
      rename_i W₁ W₂
      obtain ⟨x', hx', hx'W⟩ := (ResUT.CompS.assoc y x W₂ W).mp ⟨W₁, hc', hc⟩
      obtain ⟨V, hV, hVW⟩ := (ResUT.CompS.assoc x y W₂ W).mpr ⟨x', ResUT.CompS.comm hx', hx'W⟩
      exact .cons (.cons hr' hV) hVW
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

theorem apart_symm {K : WCactus} :
    Symmetric (fun (O₁ O₂ : List (FrameRecT K)) => ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) :=
  fun _ _ h p hp q hq e => h q hq p hp e.symm

/-- **The invariant does not read the order of the branches.** -/
theorem CInv.perm {w : TWd} {bs bs' : List (TBranch w.K)} (hp : bs.Perm bs') {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (h : CInv w bs W ps ls μ) : CInv w bs' W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI⟩ := h
  refine ⟨compAllT_perm (hp.map _) hC, fun p => ?_, ((hp.map _).pairwise_iff fun {_ _} h => apart_symm h).mp hA,
    hR, hI⟩
  rw [hps p]
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩; exact ⟨_, ⟨b, hp.mem_iff.mp hb, rfl⟩, h⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, h⟩; exact ⟨_, ⟨b, hp.mem_iff.mpr hb, rfl⟩, h⟩

/-- An empty branch owning nothing leaves the invariant. -/
theorem CInv.drop {w : TWd} {rest : List (TBranch w.K)} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (h : CInv w ((PMap.empty, []) :: rest) W ps ls μ) : CInv w rest W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI⟩ := h
  simp only [List.map_cons] at hC hA
  cases hC with
  | cons hr hc =>
  obtain rfl := ResUT.CompS.functional (ResUT.CompS.comm hc) (ResUT.compS_empty_right _)
  exact ⟨hr, fun p => by simpa using hps p, (List.pairwise_cons.mp hA).2, hR, hI⟩

/-- A part of a composite of branches. -/
theorem compAllT_part {ρs : List (TRes K)} {W : TRes K} (h : CompAllT ρs W) {ρ : TRes K}
    (hρ : ρ ∈ ρs) : ∃ y, ResUT.CompS ρ y W := by
  induction h with
  | nil => cases hρ
  | @cons a W₀ W₁ ρs hr hc ih =>
      rcases List.mem_cons.mp hρ with rfl | hρ
      · exact ⟨_, hc⟩
      · obtain ⟨y, hy⟩ := ih hρ
        obtain ⟨z, hz, hzW⟩ := (ResUT.CompS.assoc ρ y a W₀).mpr ⟨W₁, hy, ResUT.CompS.comm hc⟩
        exact ⟨z, hzW⟩

/-! ### Lists along a relation -/

theorem forall₂_and_mem {α β : Type} {R : α → β → Prop} {P : α → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → (∀ x ∈ xs, P x) →
      List.Forall₂ (fun x y => R x y ∧ P x) xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hP => .cons ⟨h, hP _ List.mem_cons_self⟩
      (forall₂_and_mem t fun x hx => hP x (List.mem_cons_of_mem _ hx))

theorem pairwise_forall₂ {α β : Type} {R : α → β → Prop} {P : α → α → Prop}
    {P' : β → β → Prop} (hP : ∀ a b a' b', R a a' → R b b' → P a b → P' a' b') :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → List.Pairwise P xs →
      List.Pairwise P' ys
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hp => by
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hp
      refine List.pairwise_cons.mpr ⟨fun b' hb' => ?_, pairwise_forall₂ hP t htl⟩
      obtain ⟨b, hb, hbb⟩ := forall₂_mem_right t hb'
      exact hP _ _ _ _ h hbb (hhd b hb)

theorem forall₂_split_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {x : α} {ys : List β}, List.Forall₂ R (xs₁ ++ x :: xs₂) ys →
      ∃ ys₁ y ys₂, ys = ys₁ ++ y :: ys₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ R x y ∧
        List.Forall₂ R xs₂ ys₂
  | [], _, _, _ :: _, .cons h t => ⟨[], _, _, rfl, .nil, h, t⟩
  | _ :: _, _, _, _ :: _, .cons h t =>
      let ⟨ys₁, y, ys₂, e, h₁, h₂, h₃⟩ := forall₂_split_right t
      ⟨_ :: ys₁, y, ys₂, by rw [e]; rfl, .cons h h₁, h₂, h₃⟩

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}, List.Forall₂ R xs₁ ys₁ →
      List.Forall₂ R xs₂ ys₂ → List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h₂ => .cons h (forall₂_append t h₂)

end BoCa.Fig16.Tree.Wp.Pool

end
