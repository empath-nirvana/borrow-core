import ProbeD1.BinderJ

/-!
# ProbeD1 — the `U` introductions at the revised W (`BINDER.md` §5, item 4; §11)

`Statement0UThawFreeJ binder0` (`statement0UThawFreeJ`): the four `U` introductions, the context's
thaw and `ThawInstJ`, at `binder0`, at the relation `BinderJ.lean` defines, at the contexts
`CtxThawFree` admits.

* **The clause across `⋆`** (`relendJ_sep`): GhostEnd's `relendableS_sep` at W's views. A `mut`
  view is in at most one part (`GhostEnd.vwE_disj`); two `imm` views are one cell, and a view
  handed at an instantiation is split back between the parts by [TR] 6.116 (`I-dup`,
  `compS_self_single_imm`).
* **The composite instantiation** (`ext_inst_comp`; `instComp`, `keepsSComp`): the retained
  part's records, tags and all, along two instantiations. It is what `ThawInstJ` needs
  (`relendJ_thunk`).
* **The leaves** (`relendJ_mut`, `relendJ_imm`). At a place no entry lends, the cell lies above the
  outermost lend (the table), so the records it reads are fixed (`mem_above_cell`) and its payload
  type is read at external lifetimes (`PayExt`, `agree_of_payExt`). At a bound place, the cell is
  the innermost entry's view (the guard's `PlaceViewsL`), dropped and handed back; the leaf's
  payload type is the view's up to the reading (`CohS`), and `tyEq_inst` keeps that at a type Core
  reads without a thunk. Coherence moves with the record it reads (`cohE_inst`, `rec1_δ`, which
  uses `RecsOutside` and `OuterBelowTop`).
* **A box** keeps its bound: each handed view is at its entry's instantiated lifetime, above the
  instantiated bound (`vwSW_outlives_inst`).
* **The rows** (`thunkF_U_J`, `thunkV_U_J`): the context's thaw, and at each instantiation the
  body by the premise there, the index's facts carried by the instantiation (`StackOK.inst`,
  `outerBelowTop_inst`, `stackJInst`, `subDom_inst`, `instModels`, `subOutsideInst`) and the
  table and views by `guardInst`.

What the result does not cover: slots `CtxThawFree` excludes (`μ`, `fam`; `ThawFreeScope` shows
typing reaches one); and the obligations the revision puts on rows outside this file —
`RetainedPay` at every row that introduces a `Mut` or `Imm` value, `KeepsT` at every consumer of
the `U` clause, `OuterBelowTop` at every row that pushes a lend (`BINDER.md` §11).
-/
noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS MutDisj jdgCty)
open BoCa.BoLo (Step1N Head)

/-! ### W's views across `⋆` -/

theorem atExactly_compS {α : Life} {ψ₁ ψ₂ ψ : CellU BoCa.Loc Val} (h₁ : AtExactly α ψ₁)
    (h₂ : AtExactly α ψ₂) (hc : CellU.CompS ψ₁ ψ₂ ψ) : AtExactly α ψ := by
  obtain ⟨s₁, s₂, v, χ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hc
  have hm : ∀ x, (s₁ ∪ s₂).mem x → x = α := by
    rintro x (hx | hx)
    · exact h₁.2 s₁ rfl x hx
    · exact h₂.2 s₂ rfl x hx
  exact ⟨hm _ (s₁ ∪ s₂).meet_mem, fun t ht y hy => by
    simp only [CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht; exact hm y hy⟩

/-- **The views of one entry join** (GhostEnd's `vwE_join`, the cell exact). -/
theorem vwEW_join {s : LSub} {e : LEnt} {d₁ d₂ : Bool} {α : Life} {ls : List SRec}
    {a₁ a₂ a : WRes} (h₁ : vwEW s e d₁ α ls a₁) (h₂ : vwEW s e d₂ α ls a₂)
    (hc : ResU.CompS a₁ a₂ a) : vwEW s e (d₁ || d₂) α ls a := by
  refine ⟨GhostEnd.vwE_join h₁.1 h₂.1 hc, fun ψ hψ => ?_⟩
  rcases top_split hc hψ with e₁ | e₂ | ⟨ψ₁, ψ₂, f₁, f₂, hC⟩
  · exact h₁.2 ψ e₁
  · exact h₂.2 ψ e₂
  · exact atExactly_compS (h₁.2 ψ₁ f₁) (h₂.2 ψ₂ f₂) hC

theorem compS_self_single_imm (l : BoCa.Loc) (S : LSet) (v : Val) (χ : WRes)
    (h : χ.InStratum S.join) :
    ResU.CompS (ResU.single l (CellU.immOf S v χ h)) (ResU.single l (CellU.immOf S v χ h))
      (ResU.single l (CellU.immOf S v χ h)) := by
  have h₃ : χ.InStratum (S ∪ S).join := ResU.InStratum.sup h h
  have e : CellU.immOf (S ∪ S) v χ h₃ = CellU.immOf S v χ h :=
    CellU.immOf_congr (LSet.union_self S) rfl rfl h₃ h
  have hc := ResU.compS_single_imm l S S v χ h h h₃
  rwa [e] at hc

/-- **A view handed at an instantiation splits between two parts**: a `mut` view goes to the one
part that dropped it, an `imm` view is duplicated ([TR] 6.116). -/
theorem vwEW_split {s : LSub} {e : LEnt} {d₁ d₂ : Bool}
    (hd : e.k = .mut → ¬ (d₁ = true ∧ d₂ = true)) {α : Life} {ls : List SRec} {a : WRes}
    (h : vwEW s e (d₁ || d₂) α ls a) :
    ∃ a₁ a₂, ResU.CompS a₁ a₂ a ∧ vwEW s e d₁ α ls a₁ ∧ vwEW s e d₂ α ls a₂ := by
  cases d₁ with
  | false =>
      exact ⟨PMap.empty, a, compS_empty_left a, ⟨⟨rfl, trivial⟩, fun _ hψ => absurd hψ (by simp)⟩,
        by simpa using h⟩
  | true =>
      cases d₂ with
      | false =>
          exact ⟨a, PMap.empty, ResU.comp_empty_right a, by simpa using h,
            ⟨⟨rfl, trivial⟩, fun _ hψ => absurd hψ (by simp)⟩⟩
      | true =>
          obtain ⟨el, ex, eT, ek, ecr⟩ := e
          cases ek with
          | «mut» => exact (hd rfl ⟨rfl, rfl⟩).elim
          | imm u₀ =>
              have h' : vwEW s ⟨el, ex, eT, .imm u₀, ecr⟩ true α ls a := by simpa using h
              obtain ⟨⟨S, v, χ, hS, ls₀, hρ, -⟩, -⟩ := h'
              refine ⟨a, a, ?_, by simpa using h, by simpa using h⟩
              rw [hρ]
              exact compS_self_single_imm _ S v χ hS

theorem vwSW_join {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds₁ ds₂ : List Bool}
    {αs : List Life} {ls : List SRec} {ρ₁ ρ₂ ρ : WRes}, vwSW s seen σ ds₁ αs ls ρ₁ →
    vwSW s seen σ ds₂ αs ls ρ₂ → ResU.CompS ρ₁ ρ₂ ρ →
    vwSW s seen σ (List.zipWith (· || ·) ds₁ ds₂) αs ls ρ ∧ MutDisj seen σ ds₁ ds₂
  | _, [], [], [], [], _, _, _, _, h₁, h₂, hc => by
      obtain ⟨rfl, -⟩ := h₁; obtain ⟨rfl, -⟩ := h₂
      rw [eq_of_compS_empty_left hc]; exact ⟨⟨rfl, trivial⟩, trivial⟩
  | seen, e :: σ, d₁ :: ds₁, d₂ :: ds₂, α :: αs, ls, _, _, _,
      ⟨a₁, r₁, hc₁, ha₁, hr₁⟩, ⟨a₂, r₂, hc₂, ha₂, hr₂⟩, hc => by
      obtain ⟨ac, bd, hac, hbd, hρ⟩ := GhostEnd.compS_four hc₁ hc₂ hc
      obtain ⟨hv, hdisj⟩ := vwSW_join hr₁ hr₂ hbd
      refine ⟨⟨ac, bd, hρ, ?_, hv⟩, fun hk => GhostEnd.vwE_disj hk ha₁.1 ha₂.1 hac, hdisj⟩
      rw [GhostEnd.vis_or]; exact vwEW_join ha₁ ha₂ hac
  | _, [], [], _ :: _, αs, _, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, [], _ :: _, _, αs, _, _, _, _, h, _, _ => by cases αs <;> exact h.elim
  | _, _ :: _, [], _, αs, _, _, _, _, h, _, _ => by cases αs <;> exact h.elim
  | _, _ :: _, _ :: _, [], αs, _, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, [], [], [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h, _, _ => h.elim

theorem vwSW_split {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds₁ ds₂ : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, MutDisj seen σ ds₁ ds₂ →
    ds₁.length = σ.length → ds₂.length = σ.length →
    vwSW s seen σ (List.zipWith (· || ·) ds₁ ds₂) αs ls ρ →
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vwSW s seen σ ds₁ αs ls ρ₁ ∧ vwSW s seen σ ds₂ αs ls ρ₂
  | _, [], [], [], [], _, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩
  | seen, e :: σ, d₁ :: ds₁, d₂ :: ds₂, α :: αs, ls, _, ⟨hd, hdisj⟩, hl₁, hl₂,
      ⟨a, r, hc, ha, hr⟩ => by
      rw [GhostEnd.vis_or] at ha
      obtain ⟨a₁, a₂, hca, ha₁, ha₂⟩ := vwEW_split hd ha
      obtain ⟨r₁, r₂, hcr, hr₁, hr₂⟩ :=
        vwSW_split hdisj (by simpa using hl₁) (by simpa using hl₂) hr
      obtain ⟨x, y, hx, hy, hxy⟩ := GhostEnd.compS_four hca hcr hc
      exact ⟨x, y, hxy, ⟨a₁, r₁, hx, ha₁, hr₁⟩, ⟨a₂, r₂, hy, ha₂, hr₂⟩⟩
  | _, [], [], [], _ :: _, _, _, _, _, _, h => h.elim
  | _, [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _, [], [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | _, _ :: _, _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h => h.elim

/-! ### Records along a part and a composite -/

theorem rel_of_compS_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {r : FrameRec}
    (h : Core.Rel r ρ₁) : Core.Rel r ρ := by
  obtain ⟨m, ψ, hg, hk, hm⟩ := h
  obtain ⟨ψ', hg', hk', -⟩ := ResU.CompS.get_left hc hg
  exact ⟨m, ψ', hg', hk'.trans hk, hm⟩

theorem rel_of_compS_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {r : FrameRec}
    (h : Core.Rel r ρ₂) : Core.Rel r ρ := rel_of_compS_left (ResU.CompS.comm hc) h

theorem KeepsT.left {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : KeepsT ls ls' ρ) : KeepsT ls ls' ρ₁ := fun x hx hr => h x hx (rel_of_compS_left hc hr)

theorem KeepsT.right {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : KeepsT ls ls' ρ) : KeepsT ls ls' ρ₂ := fun x hx hr => h x hx (rel_of_compS_right hc hr)

theorem KeepsS.left {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : KeepsS ls ls' ρ) : KeepsS ls ls' ρ₁ := fun x hx hr => h x hx (rel_of_compS_left hc hr)

theorem KeepsS.right {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : KeepsS ls ls' ρ) : KeepsS ls ls' ρ₂ := fun x hx hr => h x hx (rel_of_compS_right hc hr)

/-- A record strictly longer-lived than the outermost lend is fixed by the stack's
instantiation: it is a member of the instantiated list exactly when of the list. -/
theorem mem_recs_iff_of_lt {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {x : SRec}
    (hx : ∀ o ∈ αs.getLast?, o < x.2) {L : List SRec} : x ∈ ι.recs L ↔ x ∈ L := by
  rcases ι with _ | ⟨c, θ⟩
  · exact Iff.rfl
  · obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp (hat c θ rfl)
    have hcx : OrderDual.toDual (OrderDual.ofDual o - 1) ≤ x.2 := cut_le_of_lt (hx o ho)
    rw [Inst.mem_recs]
    constructor
    · rintro ⟨y, hy, hyx⟩
      by_cases hyc : y.2 < OrderDual.toDual (OrderDual.ofDual o - 1)
      · rw [Inst.rec1_moved _ hyc] at hyx
        have : θ y.2 = x.2 := congrArg Prod.snd hyx
        exact absurd (this ▸ θ.lt_cut hyc) (not_lt.mpr hcx)
      · rw [Inst.rec1_fixed _ (not_lt.mp hyc)] at hyx
        exact hyx ▸ hy
    · intro hxL
      exact ⟨x, hxL, Inst.rec1_fixed _ hcx⟩

theorem lt_of_cellIn {αs : List Life} {ρ : WRes} (hz : stratS αs ρ) {b : Life} (hb : CellIn ρ b)
    {o : Life} (ho : αs.getLast? = some o) : o < b := by
  obtain ⟨m, ψ, hg, hk, hle⟩ := hb
  have hin := hz o ho m ψ hg
  have : o < ψ.at := by
    cases ψ with
    | own v => exact absurd rfl hk
    | imm i => exact hin
    | «mut» mm => exact hin
  exact lt_of_lt_of_le this hle

/-- **The retained part's extension along a composite instantiation.** -/
theorem ext_inst_comp {αs : List Life} {ι₁ ι₂ : Inst}
    (h₂ : InstAt (ι₁.life αs) ι₂) {ls ls₁ ls₂ : List SRec} {ρz : WRes} (hz : stratS αs ρz)
    (he₁ : Ext (ι₁.recs ls) ls₁ ρz) (hk₁ : KeepsT (ι₁.recs ls) ls₁ ρz)
    (he₂ : Ext (ι₂.recs ls₁) ls₂ ρz) (hk₂ : KeepsT (ι₂.recs ls₁) ls₂ ρz) :
    Ext (ι₂.recs (ι₁.recs ls)) ls₂ ρz ∧ KeepsT (ι₂.recs (ι₁.recs ls)) ls₂ ρz := by
  have hkt : KeepsT (ι₂.recs (ι₁.recs ls)) ls₂ ρz := by
    intro x hx hr
    obtain ⟨y, hy, rfl⟩ := Inst.mem_recs.mp hx
    have hry : Core.Rel y.1 ρz := (rel_rec1 ι₂ y ρz).mp hr
    exact hk₂ _ (Inst.mem_recs.mpr ⟨y, hk₁ y hy hry, rfl⟩) hr
  refine ⟨⟨fun r hr hrel => ?_, fun b hb x hx => ?_⟩, hkt⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map_of_mem (hkt x hx hrel)
  · have hlast : ∀ o ∈ αs.getLast?, o < x.2 := fun o ho =>
      lt_trans (lt_of_cellIn hz hb ho) hx
    have hlast₂ : ∀ o ∈ (ι₁.life αs).getLast?, o < x.2 := by
      intro o ho
      rw [Inst.life_getLast?] at ho
      obtain ⟨o₀, ho₀, rfl⟩ := Option.mem_map.mp ho
      exact lt_of_le_of_lt (ι₁.life1_le o₀) (hlast o₀ ho₀)
    exact (mem_recs_iff_of_lt h₂ hlast₂).trans ((he₁.2 b hb x hx).trans
      ((mem_recs_iff_of_lt h₂ hlast₂).symm.trans (he₂.2 b hb x hx)))

/-! ### The clause across `⋆` -/

theorem relendJ_mono {δ : LSub} {σ : LStack} {P Q : LSub → List Life → List SRec → WProp}
    (hPQ : ∀ δ' αs' ls' ρ, P δ' αs' ls' ρ → Q δ' αs' ls' ρ) {αs : List Life} {ls : List SRec}
    {ρ : WRes} (h : RelendJ δ σ P αs ls ρ) : RelendJ δ σ Q αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h
  exact ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro ρv τ hv hcv =>
    hPQ _ _ _ _ (H ι hat ls' he hkt hks hro ρv τ hv hcv)⟩

/-- **The clause is closed under `⋆`**: the retained parts compose and stay above the outermost
lend; the dropped views join entry by entry (a `mut` view in at most one part, two `imm` views
one cell); at an instantiation the views handed split back, each part thawed by its own. -/
theorem relendJ_sep {δ : LSub} {σ : LStack} {P Q : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} {ρ : WRes}
    (h : (RelendJ δ σ P αs ls ⋆ RelendJ δ σ Q αs ls) ρ) :
    RelendJ δ σ (fun δ' αs' ls' => P δ' αs' ls' ⋆ Q δ' αs' ls') αs ls ρ := by
  obtain ⟨ρ₁, ρ₂, hc, ⟨ds₁, ρz₁, ρn₁, hc₁, hn₁, hz₁, hth₁⟩,
    ⟨ds₂, ρz₂, ρn₂, hc₂, hn₂, hz₂, hth₂⟩⟩ := h
  obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := GhostEnd.compS_four hc₁ hc₂ hc
  obtain ⟨hn, hdisj⟩ := vwSW_join hn₁.1 hn₂.1 hcn
  refine ⟨_, ρz, ρn, hcρ, ⟨hn, placeViewsL_join hcn hn₁.2 hn₂.2⟩,
    fun a ha => (outlives_comp hcz a).mpr ⟨hz₁ a ha, hz₂ a ha⟩,
    fun ι hat ls' he hkt hks hro ρv τ hv hcv => ?_⟩
  obtain ⟨ρv₁, ρv₂, hcv₁₂, hv₁, hv₂⟩ :=
    vwSW_split hdisj (vwSW_length hn₁.1).1 (vwSW_length hn₂.1).1 hv.1
  obtain ⟨x, y, hx, hy, hxy⟩ := GhostEnd.compS_four hcz hcv₁₂ hcv
  exact ⟨x, y, hxy,
    hth₁ ι hat ls' (he.left hcz) (hkt.left hcz) (hks.left hcn) hro ρv₁ x
      ⟨hv₁, placeViewsL_left hcv₁₂ hv.2⟩ hx,
    hth₂ ι hat ls' (he.right hcz) (hkt.right hcz) (hks.right hcn) hro ρv₂ y
      ⟨hv₂, placeViewsL_right hcv₁₂ hv.2⟩ hy⟩

/-! ### Bookkeeping at an instantiation -/

theorem stratS_inst {αs : List Life} {ρ : WRes} (ι : Inst) (h : stratS αs ρ) :
    stratS (ι.life αs) ρ := by
  intro a ha
  rw [Inst.life_getLast?] at ha
  obtain ⟨o, ho, rfl⟩ := Option.mem_map.mp ha
  exact ResU.InStratum.mono (ι.life1_le o) (h o ho)

theorem outerBelowTop_inst {αs : List Life} (ι : Inst) (h : OuterBelowTop αs) :
    OuterBelowTop (ι.life αs) := by
  intro a ha
  rw [Inst.life_getLast?] at ha
  obtain ⟨o, ho, rfl⟩ := Option.mem_map.mp ha
  exact lt_of_le_of_lt (ι.life1_le o) (h o ho)

theorem innerAt_life (σ : LStack) (ι : Inst) (l : BoCa.Loc) : ∀ (αs : List Life),
    innerAt σ (ι.life αs) l = (innerAt σ αs l).map (fun p => (p.1, ι.life1 p.2)) := by
  induction σ with
  | nil => intro αs; simp [innerAt]
  | cons e σ ih =>
      intro αs
      cases αs with
      | nil => simp [innerAt, Inst.life]
      | cons α αs =>
          show innerAt (e :: σ) (ι.life1 α :: ι.life αs) l = _
          rw [innerAt_cons, innerAt_cons]
          by_cases h : e.l = l
          · simp [h]
          · simp only [h, if_false]; exact ih αs

/-- An instantiation fixes a lifetime that is not internal to the stack. -/
theorem fix_of_not_internal {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {a : Life}
    (h : ¬ Internal αs a) : ι.life1 a = a := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · exact θ.fix a (not_lt.mp fun hlt => h ⟨c, hat c θ rfl, hlt⟩)

/-- **A payload type read at external lifetimes reads the same at an instantiation.** -/
theorem agree_of_payExt {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {s : LSub} {T : VTy}
    (h : PayExt αs s T) : ∀ y, VFree y T → (ι.sub s).find? y = s.find? y := by
  intro y hy
  rw [Inst.find?_sub]
  cases hm : s.find? y with
  | none => rfl
  | some m =>
      show some (OrderDual.ofDual (ι.life1 (OrderDual.toDual m))) = some m
      rw [fix_of_not_internal hat (h y hy m hm)]
      rfl

theorem payExt_inst {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {s : LSub} {T : VTy}
    (h : PayExt αs s T) : PayExt (ι.life αs) (ι.sub s) T := by
  intro y hy m hm hint
  rw [agree_of_payExt hat h y hy] at hm
  obtain ⟨c₂, hc₂, hlt⟩ := hint
  have hc₂' : cutOf (ι.life αs) = some c₂ := hc₂
  obtain ⟨o₂, ho₂, -⟩ := cutOf_eq.mp hc₂'
  rw [Inst.life_getLast?] at ho₂
  obtain ⟨o, ho, -⟩ := Option.map_eq_some_iff.mp ho₂
  have hc : cutOf αs = some (OrderDual.toDual (OrderDual.ofDual o - 1)) := by
    simp [cutOf, ho]
  exact h y hy m hm ⟨_, hc, lt_of_lt_of_le hlt (cutOf_inst_le hc hc₂')⟩

/-- **A record's reading at an instantiation**: moved with the record below the cut, and fixed
with it above, since it outlives the outermost lend and so reads only lifetimes above it. -/
theorem rec1_δ {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {ls : List SRec} (hro : RecsOutside αs ls) {y : SRec} (hy : y ∈ ls) :
    (ι.rec1 y).1.δ = ι.sub y.1.δ := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp (hat c θ rfl)
    by_cases hlt : y.2 < OrderDual.toDual (OrderDual.ofDual o - 1)
    · rw [Inst.rec1_moved θ hlt]; rfl
    · rw [Inst.rec1_fixed θ (not_lt.mp hlt)]
      have hoy : o < y.2 := lt_of_lt_of_le (lt_cut_self (hob o ho)) (not_lt.mp hlt)
      have hmem : o ∈ αs := List.mem_of_getLast? ho
      symm
      refine mapN_eq_self fun p hp => ?_
      have hop : o < OrderDual.toDual p.2 := hro o hmem y hy hoy p hp
      show OrderDual.ofDual (θ (OrderDual.toDual p.2)) = p.2
      rw [θ.fix _ (cut_le_of_lt hop)]
      rfl

theorem subDom_inst {δ : LSub} {Δ : LifeCtx} (ι : Inst) (h : SubDom δ Δ) : SubDom (ι.sub δ) Δ := by
  intro y hy
  refine h y fun hn => hy ?_
  rw [Inst.find?_sub, hn]
  rfl

/-! ### The parts of a resource -/

theorem ImmSub.inStratum {ψ ψ' : CellU BoCa.Loc Val} (h : ImmSub ψ ψ') {a : Life}
    (h' : ψ'.InStratum a) : ψ.InStratum a := by
  rcases h with rfl | ⟨S, S', v, χ, hS, hS', rfl, rfl, hsub⟩
  · exact h'
  · exact lt_of_lt_of_le h' (LSet.meet_mono_of_subset hsub)

theorem tabAtS_left {σ : LStack} {αs : List Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ) : TabAtS σ αs ρ₁ :=
  ⟨fun a ha => ((outlives_comp hc _).mp (h.1 a ha)).1, fun a ha k ψ hk e => by
    obtain ⟨ψ', e', hs⟩ := top_of_compS_left hc e
    exact hs.inStratum (h.2 a ha k ψ' hk e')⟩

theorem tabAtS_right {σ : LStack} {αs : List Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : TabAtS σ αs ρ) : TabAtS σ αs ρ₂ := tabAtS_left (ResU.CompS.comm hc) h

theorem eq_empty_of_compS_left {a b : WRes} (h : ResU.CompS a b PMap.empty) : a = PMap.empty := by
  apply PMap.ext
  intro l
  rw [PMap.empty_get]
  cases e : a.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨ψ', e', -⟩ := ResU.CompS.get_left h e
      rw [PMap.empty_get] at e'
      exact absurd e' (by simp)

theorem eq_empty_of_compS_right {a b : WRes} (h : ResU.CompS a b PMap.empty) : b = PMap.empty :=
  eq_empty_of_compS_left (ResU.CompS.comm h)

theorem not_deepAt_empty {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} : ¬ DeepAt PMap.empty l ψ := by
  intro h
  cases h with
  | top e => rw [PMap.empty_get] at e; exact absurd e (by simp)
  | wit e _ => rw [PMap.empty_get] at e; exact absurd e (by simp)

theorem placeViewsL_empty {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} :
    PlaceViewsL s σ αs ls PMap.empty :=
  placeViewsL_of_noBound fun _ _ hd _ _ => not_deepAt_empty hd

theorem stratS_empty (αs : List Life) : stratS αs PMap.empty := fun a _ => ResU.inStratum_empty a

/-! ### The views of one place -/

/-- The drop flags of the innermost entry lending `l`. -/
def dsPlace : LStack → BoCa.Loc → List Bool
  | [], _ => []
  | e :: σ, l => if e.l = l then true :: σ.map (fun _ => false) else false :: dsPlace σ l

theorem vwSW_false {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life}
    {ls : List SRec}, αs.length = σ.length → vwSW s seen σ (σ.map fun _ => false) αs ls PMap.empty
  | _, [], [], _, _ => ⟨rfl, trivial⟩
  | seen, e :: σ, α :: αs, ls, hl => by
      refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ?_, vwSW_false (by simpa using hl)⟩
      have : vis seen e false = false := by simp [vis]
      rw [this]; exact vwEW_off _ _ _ _
  | _, [], _ :: _, _, hl => by simp at hl
  | _, _ :: _, [], _, hl => by simp at hl

theorem vwSW_false_inv {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, vwSW s seen σ (σ.map fun _ => false) αs ls ρ → ρ = PMap.empty
  | _, [], [], _, _, h => h.1
  | seen, e :: σ, α :: αs, ls, ρ, ⟨a, r, hc, ha, hr⟩ => by
      have hv : vis seen e false = false := by simp [vis]
      rw [hv] at ha
      rw [vwEW_off_eq ha, vwSW_false_inv hr] at hc
      exact eq_empty_of_compS_empty hc
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim

theorem vwSW_dsAt {s : LSub} {l : BoCa.Loc} {e : LEnt} {α : Life} {ls : List SRec} {ρ : WRes}
    (hv : vwEW s e true α ls ρ) : ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life},
    αs.length = σ.length → l ∉ seen → innerAt σ αs l = some (e, α) →
    vwSW s seen σ (dsPlace σ l) αs ls ρ
  | _, [], [], _, _, hi => by simp [innerAt] at hi
  | seen, e' :: σ, α' :: αs, hl, hs, hi => by
      rw [innerAt_cons] at hi
      by_cases he : e'.l = l
      · rw [if_pos he] at hi
        obtain ⟨rfl, rfl⟩ : e' = e ∧ α' = α := by simpa using hi
        simp only [dsPlace, if_pos he]
        refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ?_, vwSW_false (by simpa using hl)⟩
        have : vis seen e' true = true := by simp [vis, he, hs]
        rw [this]; exact hv
      · rw [if_neg he] at hi
        simp only [dsPlace, if_neg he]
        refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_,
          vwSW_dsAt hv (by simpa using hl) ?_ hi⟩
        · have : vis seen e' false = false := by simp [vis]
          rw [this]; exact vwEW_off _ _ _ _
        · simp only [List.mem_cons, not_or]; exact ⟨Ne.symm he, hs⟩
  | _, [], _ :: _, hl, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _ => by simp at hl

theorem vwSW_dsAt_inv {s : LSub} {l : BoCa.Loc} {e : LEnt} {α : Life} {ls : List SRec} :
    ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life} {ρ : WRes},
    l ∉ seen → innerAt σ αs l = some (e, α) → vwSW s seen σ (dsPlace σ l) αs ls ρ →
    vwEW s e true α ls ρ
  | _, [], [], _, _, hi, _ => by simp [innerAt] at hi
  | seen, e' :: σ, α' :: αs, ρ, hs, hi, h => by
      rw [innerAt_cons] at hi
      by_cases he : e'.l = l
      · rw [if_pos he] at hi
        obtain ⟨rfl, rfl⟩ : e' = e ∧ α' = α := by simpa using hi
        simp only [dsPlace, if_pos he] at h
        obtain ⟨a, r, hc, ha, hr⟩ := h
        have : vis seen e' true = true := by simp [vis, he, hs]
        rw [this] at ha
        rw [vwSW_false_inv hr] at hc
        rw [eq_of_compS_empty_left (ResU.CompS.comm hc)]
        exact ha
      · rw [if_neg he] at hi
        simp only [dsPlace, if_neg he] at h
        obtain ⟨a, r, hc, ha, hr⟩ := h
        have : vis seen e' false = false := by simp [vis]
        rw [this] at ha
        rw [vwEW_off_eq ha] at hc
        rw [eq_of_compS_empty_left hc]
        exact vwSW_dsAt_inv (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm he, hs⟩) hi hr
  | _, [], _ :: _, _, _, hi, _ => by simp [innerAt] at hi
  | _, _ :: _, [], _, _, hi, _ => by simp [innerAt] at hi

/-- **The clause at an empty resource**: no views dropped, nothing retained. -/
theorem relendJ_emp {δ : LSub} {σ : LStack} {P : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} (hl : αs.length = σ.length)
    (hP : ∀ δ' αs' ls', P δ' αs' ls' PMap.empty) : RelendJ δ σ P αs ls PMap.empty := by
  refine ⟨σ.map fun _ => false, PMap.empty, PMap.empty, ResU.comp_empty_right _,
    ⟨vwSW_false hl, placeViewsL_empty⟩, stratS_empty αs,
    fun ι _ ls' _ _ _ _ ρv τ hv hcv => ?_⟩
  rw [vwSW_false_inv hv.1] at hcv
  rw [eq_empty_of_compS_empty hcv]
  exact hP _ _ _

/-! ### The types the leaves read -/

/-- **`TyEqInst` at a type Core reads without a thunk**: each clause compares readings by an
equality of lifetimes, which one map on both sides keeps. -/
theorem tyEq_inst (ι : Inst) : ∀ (A : VTy), CoreStable A → ∀ {B : VTy} {s s' : LSub},
    TyEq A s B s' → TyEq A (ι.sub s) B (ι.sub s')
  | .unit, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .zero, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .unk, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .int _, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .opq _, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .tvar _, _, B, _, _, h => by cases B <;> simp_all [TyEq]
  | .tensor A₁ A₂, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_inst ι A₁ hc.1 h.1, tyEq_inst ι A₂ hc.2 h.2⟩
  | .sum A₁ A₂, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_inst ι A₁ hc.1 h.1, tyEq_inst ι A₂ hc.2 h.2⟩
  | .ref A, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact tyEq_inst ι A hc h
  | .bang A, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact tyEq_inst ι A hc h
  | .box a A, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact ⟨by rw [Inst.interp_sub, Inst.interp_sub, h.1], tyEq_inst ι A hc h.2⟩
  | .imm a A, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact ⟨by rw [Inst.interp_sub, Inst.interp_sub, h.1], tyEq_inst ι A hc h.2⟩
  | .mut a A, hc, B, _, _, h => by
      cases B <;> simp only [TyEq] at h ⊢
      exact ⟨by rw [Inst.interp_sub, Inst.interp_sub, h.1], tyEq_inst ι A hc h.2⟩
  | .thunk _, hc, _, _, _, _ => hc.elim
  | .mu _, hc, _, _, _, _ => hc.elim
  | .fam _, hc, _, _, _, _ => hc.elim

/-- At a type Core reads without a thunk, the program's relation is the observable view. -/
theorem vC_true_eq_false : ∀ (A : VTy), CoreStable A → ∀ (ls : List SRec) (s : LSub),
    vC true A ls s = vC false A ls s
  | .unit, _, _, _ => rfl
  | .zero, _, _, _ => rfl
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .tensor A B, h, ls, s => by
      have h₁ := vC_true_eq_false A h.1 ls s
      have h₂ := vC_true_eq_false B h.2 ls s
      funext v; simp only [vCE, h₁, h₂]
  | .sum A B, h, ls, s => by
      have h₁ := vC_true_eq_false A h.1 ls s
      have h₂ := vC_true_eq_false B h.2 ls s
      funext v; simp only [vCE, h₁, h₂]
  | .bang _, _, _, _ => rfl
  | .box a A, h, ls, s => by
      have ih := vC_true_eq_false A h ls s
      funext v; simp only [vCE, ih]
  | .ref A, h, ls, s => by
      have ih := vC_true_eq_false A h ls s
      funext v; simp only [vCE, ih]
  | .imm _ _, _, _, _ => rfl
  | .mut _ _, _, _, _ => rfl
  | .thunk _, h, _, _ => h.elim
  | .mu _, h, _, _ => h.elim
  | .fam _, h, _, _ => h.elim

theorem keepsS_of_keepsT {ls ls' : List SRec} {ρ : WRes} (h : KeepsT ls ls' ρ) : KeepsS ls ls' ρ :=
  fun x hx hr => ⟨x, h x hx hr, RecUpTo.refl x⟩

/-- **Coherence at an instantiation** (`CohEInst` at the stack's own index): the record the cell is
coherent with is kept, moved with its reading when below the cut and read above the outermost
lend when not (`rec1_δ`); the comparison moves with it (`tyEq_inst`). -/
theorem cohE_inst {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {ls ls' : List SRec} (hro : RecsOutside αs ls) {T : VTy} (hT : CoreStable T) {s : LSub}
    {l : BoCa.Loc} {R : WRes} (hR : ∃ ψ, R.get l = some ψ ∧ ψ.kind = Kind.imm)
    (hks : KeepsS (ι.recs ls) ls' R) (h : CohE (rsOf ls) l T s) :
    CohE (rsOf ls') l T (ι.sub s) := by
  obtain ⟨S₀, δ₀, hTy, hCoh⟩ := h
  obtain ⟨ψ, hψ, hk⟩ := hR
  have key : ∀ y ∈ ls, AgreeOn S₀ δ₀ y.1.δ →
      (l = y.1.le ∧ S₀ = y.1.T ∨ ∃ p u, Chain y.1.R y.1.T y.1.v p l S₀ u) →
      CohE (rsOf ls') l T (ι.sub s) := by
    intro y hy hag hpos
    have hrel : Core.Rel y.1 R := by
      refine ⟨l, ψ, hψ, hk, ?_⟩
      rcases hpos with ⟨h1, -⟩ | ⟨p, u, hch⟩
      · exact Or.inl h1
      · exact Or.inr ⟨p, S₀, u, hch⟩
    obtain ⟨x', hx', hup⟩ :=
      hks (ι.rec1 y) (Inst.mem_recs.mpr ⟨y, hy, rfl⟩) ((rel_rec1 ι y R).mpr hrel)
    obtain ⟨hle, hv, hTT, hδ, -, hR'⟩ := hup
    have hδ' : x'.1.δ = ι.sub y.1.δ := hδ.trans (rec1_δ hat hob hro hy)
    have hmem : x'.1 ∈ rsOf ls' := List.mem_map_of_mem hx'
    refine ⟨S₀, x'.1.δ, ?_, ?_⟩
    · rw [hδ']
      exact tyEq_inst ι T hT (hTy.trans (TyEq.of_agree S₀ hag))
    · rcases hpos with ⟨h1, h2⟩ | ⟨p, u, hch⟩
      · left
        refine ⟨x'.1, hmem, ?_, ?_, fun _ _ => rfl⟩
        · rw [hle, Inst.rec1_le]; exact h1
        · rw [hTT, Inst.rec1_T]; exact h2
      · right
        refine ⟨x'.1, hmem, p, u, ?_, fun _ _ => rfl⟩
        rw [hTT, Inst.rec1_T, hv, Inst.rec1_v]
        exact Chain.of_own_iff (fun l' u' => by rw [hR' l' u', Inst.rec1_R]) hch
  rcases hCoh with ⟨r, hr, h1, h2, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact key y hy (h2 ▸ hag) (Or.inl ⟨h1, h2⟩)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact key y hy hag (Or.inr ⟨p, u, hch⟩)

/-! ### The leaves at an instantiation -/

theorem cell_above_of_stratS {αs : List Life} {ρ : WRes} (hz : stratS αs ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∀ o ∈ αs.getLast?, o < ψ.at := by
  intro o ho
  have h := hz o ho l ψ hg
  cases ψ with
  | own v => exact absurd rfl hk
  | imm i => exact h
  | «mut» m => exact h

/-- **The records a retained cell reads are fixed**: above a cell of the retained part, the
instantiated list is the list, and the extension keeps it. -/
theorem mem_above_cell {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {ls ls' : List SRec}
    {ρ : WRes} (hz : stratS αs ρ) (he : Ext (ι.recs ls) ls' ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hg : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) (x : SRec)
    (hx : ψ.at < x.2) : x ∈ ls ↔ x ∈ ls' :=
  (mem_recs_iff_of_lt hat fun o ho => lt_trans (cell_above_of_stratS hz hg hk o ho) hx).symm.trans
    (he.2 ψ.at ⟨l, ψ, hg, hk, le_rfl⟩ x hx)

/-- **A retained `Mut` leaf at an instantiation**: its cell lies above the outermost lend, so the
records it reads are fixed; its payload type is read at external lifetimes, so the stored
predicate and its support read the same. -/
theorem vC_mut_retained {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {a : Lifetime.Life}
    {T : VTy} {ls ls' : List SRec} {s : LSub} {v : Val} {ρ : WRes} (hpay : PayExt αs s T)
    (hz : stratS αs ρ) (he : Ext (ι.recs ls) ls' ρ) (h : vC true (.mut a T) ls s v ρ) :
    vC true (.mut a T) ls' (ι.sub s) v ρ := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hv, b, u, σ', hσ', Q, hw, ls₀, hαb, hρ, hQ, hmem, hsupp⟩ := pure_sep_iff.mp hsep
  have hP : ∀ ls₀, vC true T ls₀ (ι.sub s) = vC true T ls₀ s :=
    fun ls₀ => vC_congr T (agree_of_payExt hat hpay) true ls₀
  have hg : ρ.get ℓ = some (CellU.mutOf b u σ' hσ' Q hw) := by rw [hρ]; simp
  refine ⟨ι.life1 α, ?_, ℓ, pure_sep_mk hv ?_⟩
  · rw [Inst.interp_sub, hα]; rfl
  · refine ⟨b, u, σ', hσ', Q, hw, ls₀, le_trans (ι.life1_le α) hαb, hρ, ?_, fun x => ?_,
      fun ls'' u'' σ'' hP' => hsupp ls'' u'' σ'' (by
        show vC true T ls'' s u'' σ''; rw [← hP ls'']; exact hP')⟩
    · show ofS Q = vC true T ls₀ (ι.sub s)
      rw [hP]; exact hQ
    · rw [hmem x]
      exact and_congr_left fun hxb =>
        mem_above_cell hat hz he hg CellU.kind_mutOf_ne_own x hxb

/-- **A retained `Imm` leaf at an instantiation**: as a `Mut` leaf, its coherence kept by
`cohE_inst`. -/
theorem vC_imm_retained {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {a : Lifetime.Life} {T : VTy} (hT : CoreStable T) {ls ls' : List SRec}
    (hro : RecsOutside αs ls) {s : LSub} {v : Val} {ρ : WRes} (hpay : PayExt αs s T)
    (hz : stratS αs ρ) (he : Ext (ι.recs ls) ls' ρ) (hkt : KeepsT (ι.recs ls) ls' ρ)
    (h : vC true (.imm a T) ls s v ρ) : vC true (.imm a T) ls' (ι.sub s) v ρ := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨⟨hv, hcoh⟩, S, u, χ, hχ, ls₀, hρ, hP, hαS, hmem⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  refine ⟨ι.life1 α, ?_, ℓ, pure_sep_mk ⟨hv, ?_⟩ ?_⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact cohE_inst hat hob hro hT ⟨_, hg, rfl⟩ (keepsS_of_keepsT hkt) hcoh
  · refine ⟨S, u, χ, hχ, ls₀, hρ, ?_, le_trans (ι.life1_le α) hαS, fun x => ?_⟩
    · show vC false T ls₀ (ι.sub s) u χ
      rw [vC_congr T (agree_of_payExt hat hpay) false ls₀]; exact hP
    · rw [hmem x]
      exact and_congr_left fun hxb =>
        mem_above_cell hat hz he hg (by simp [CellU.immOf, CellU.kind]) x hxb

/-- **A `Mut` leaf at a bound place at an instantiation**: the instantiated view, whose payload
type is the leaf's up to the reading (`CohS`, kept by `tyEq_inst`), at a lifetime the leaf's
index reaches by the instantiation's monotonicity. -/
theorem vC_mut_bound (ι : Inst) {a : Lifetime.Life} {T : VTy} (hT : CoreStable T) {e : LEnt}
    {s : LSub} {ls ls' : List SRec} {l : BoCa.Loc} {αe : Life} {ρ ρv : WRes} (hel : e.l = l)
    (hk : e.k = .mut) (hTy : TyEq T s e.T s) (h : vC true (.mut a T) ls s (.loc l) ρ)
    (hatl : ∀ ψ, ρ.get l = some ψ → ψ.at = αe)
    (hv : vwEW (ι.sub s) e true (ι.life1 αe) ls' ρv) :
    vC true (.mut a T) ls' (ι.sub s) (.loc l) ρv := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hel hk hTy
  subst hel hk
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hvl, b, u, σ', hσ', Q, hw, ls₀, hαb, hρ, -, -, -⟩ := pure_sep_iff.mp hsep
  cases hvl
  have hb : b = αe := hatl (CellU.mutOf b u σ' hσ' Q hw) (by rw [hρ]; simp)
  obtain ⟨⟨b', u', σ'', hσ'', Q', hw', ls₀', hαb', hρv, hQ', hmem', hsupp'⟩, -⟩ := hv
  have hTy' : TyEq T (ι.sub s) eT (ι.sub s) := tyEq_inst ι T hT hTy
  have hP : ∀ ls₀, vC true T ls₀ (ι.sub s) = vC true eT ls₀ (ι.sub s) :=
    fun ls₀ => vC_tyEq hTy' true ls₀
  refine ⟨ι.life1 α, ?_, el, pure_sep_mk rfl
    ⟨b', u', σ'', hσ'', Q', hw', ls₀', ?_, hρv, ?_, hmem', ?_⟩⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact le_trans (ι.life1_le_iff.mpr (hb ▸ hαb)) hαb'
  · show ofS Q' = vC true T ls₀' (ι.sub s)
    rw [hP]; exact hQ'
  · intro ls₂ u₂ σ₂ hP₂
    exact hsupp' ls₂ u₂ σ₂ (by
      show vC true eT ls₂ (ι.sub s) u₂ σ₂; rw [← hP ls₂]; exact hP₂)

/-- **An `Imm` leaf at a bound place at an instantiation**: the instantiated view, its payload in
the observable view (`vC_true_eq_false`), its coherence kept by `cohE_inst` at the records the
dropped view is coherent with (`KeepsS`). -/
theorem vC_imm_bound {αs : List Life} {ι : Inst} (hat : InstAt αs ι) (hob : OuterBelowTop αs)
    {a : Lifetime.Life} {T : VTy} (hT : CoreStable T) {e : LEnt} {s : LSub} {ls ls' : List SRec}
    (hro : RecsOutside αs ls) {l : BoCa.Loc} {αe : Life} {ρ ρv : WRes} (hel : e.l = l)
    {u₀ : Val} (hk : e.k = .imm u₀) (hTy : TyEq T s e.T s)
    (h : vC true (.imm a T) ls s (.loc l) ρ) (hatl : ∀ ψ, ρ.get l = some ψ → ψ.at = αe)
    (hks : KeepsS (ι.recs ls) ls' ρ) (hv : vwEW (ι.sub s) e true (ι.life1 αe) ls' ρv) :
    vC true (.imm a T) ls' (ι.sub s) (.loc l) ρv := by
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  simp only at hel hk hTy
  subst hel hk
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨⟨hvl, hcoh⟩, S, u, χ, hχ, ls₀, hρ, -, hαS, -⟩ := pure_sep_iff.mp hsep
  cases hvl
  have hg : ρ.get el = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  have hS : S.meet = αe := hatl _ hg
  obtain ⟨⟨S', u', χ', hχ', ls₀', hρv, hP', hαS', hmem'⟩, -⟩ := hv
  have hTy' : TyEq T (ι.sub s) eT (ι.sub s) := tyEq_inst ι T hT hTy
  refine ⟨ι.life1 α, ?_, el, pure_sep_mk ⟨rfl, ?_⟩ ⟨S', u', χ', hχ', ls₀', hρv, ?_, ?_, hmem'⟩⟩
  · rw [Inst.interp_sub, hα]; rfl
  · exact cohE_inst hat hob hro hT ⟨_, hg, rfl⟩ hks hcoh
  · show vC false T ls₀' (ι.sub s) u' χ'
    rw [← vC_true_eq_false T hT, vC_tyEq hTy' true]; exact hP'
  · exact le_trans (ι.life1_le_iff.mpr (hS ▸ hαS)) hαS'

/-! ### The leaves' clause -/

theorem vRLJ_mut_eq (p : Placement) (σ : LStack) (δ : LSub) (a : Lifetime.Life) (T : VTy)
    (αs : List Life) (ls : List SRec) (v : Val) :
    vRLJ p σ δ (.mut a T) αs ls v = fun ρ => vC true (.mut a T) ls (extS δ σ αs) v ρ ∧
      CohS σ αs (extS δ σ αs) (.mut a T) v ρ ∧ RetainedPay σ αs (extS δ σ αs) T v := by
  rw [vRLJ]

theorem vRLJ_imm_eq (p : Placement) (σ : LStack) (δ : LSub) (a : Lifetime.Life) (T : VTy)
    (αs : List Life) (ls : List SRec) (v : Val) :
    vRLJ p σ δ (.imm a T) αs ls v = fun ρ => vC true (.imm a T) ls (extS δ σ αs) v ρ ∧
      CohS σ αs (extS δ σ αs) (.imm a T) v ρ ∧ RetainedPay σ αs (extS δ σ αs) T v := by
  rw [vRLJ]

theorem vRLJ_thunk0 (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec)
    (f : Val) :
    vRLJ .binder0 σ δ (.thunk C) αs ls f = guardPV (extS δ σ αs) σ αs ls
      (RelendJ δ σ (fun δ' αs' ls' => cRLJ .binder0 σ δ' C αs' ls' (forceE C (.val f))) αs ls) := by
  rw [vRLJ]; rfl

theorem not_mem_of_innerAt_none {σ : LStack} {αs : List Life} (hl : αs.length = σ.length)
    {l : BoCa.Loc} (h : innerAt σ αs l = none) : l ∉ σ.map LEnt.l := fun hm => by
  obtain ⟨e, α, he⟩ := innerAt_isSome hl hm
  rw [h] at he; exact absurd he (by simp)

theorem innerAt_inst_some {σ : LStack} {αs : List Life} (ι : Inst) {l : BoCa.Loc} {e : LEnt}
    {α : Life} (h : innerAt σ αs l = some (e, α)) :
    innerAt σ (ι.life αs) l = some (e, ι.life1 α) := by
  rw [innerAt_life, h]; rfl

theorem innerAt_inst_none {σ : LStack} {αs : List Life} (ι : Inst) {l : BoCa.Loc}
    (h : innerAt σ αs l = none) : innerAt σ (ι.life αs) l = none := by
  rw [innerAt_life, h]; rfl

/-- A leaf at a place no entry lends lies above the outermost lend (the table). -/
theorem stratS_single_unbound {σ : LStack} {αs : List Life} {ρ : WRes}
    (hl : αs.length = σ.length) (ht : TabAtS σ αs ρ) {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hρ : ρ = ResU.single l ψ) (hi : innerAt σ αs l = none) : stratS αs ρ := by
  intro o ho
  have hψ := ht.2 o ho l ψ (not_mem_of_innerAt_none hl hi) (by rw [hρ]; simp)
  rw [hρ]
  exact ResU.inStratum_single l hψ

/-- **The thaw of a `Mut` leaf**: at a place no entry lends, retained (`vC_mut_retained`); at a
bound place, the innermost entry's view (the guard), dropped and handed back
(`vC_mut_bound`). -/
theorem relendJ_mut {a : Lifetime.Life} {T : VTy} (hT : CoreStable T) {δ : LSub} {σ : LStack}
    {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes} (hok : StackOK σ αs)
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (h : vRLJ .binder0 σ δ (.mut a T) αs ls v ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' (.mut a T) αs' ls' v) αs ls ρ := by
  rw [vRLJ_mut_eq] at h
  obtain ⟨hvc, hcoh, hpay⟩ := h
  obtain ⟨α, -, ℓ, hsep⟩ := id hvc
  obtain ⟨rfl, b, u, σ', hσ', Q, hw, ls₀, -, hρ, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.mutOf b u σ' hσ' Q hw) := by rw [hρ]; simp
  cases hi : innerAt σ αs ℓ with
  | none =>
      have hz : stratS αs ρ := stratS_single_unbound hok.1 ht hρ hi
      have hp := hpay ℓ rfl hi
      refine ⟨σ.map fun _ => false, ρ, PMap.empty, ResU.comp_empty_right ρ,
        ⟨vwSW_false hok.1, placeViewsL_empty⟩, hz, fun ι hat ls' he _ _ _ ρv τ hv hcv => ?_⟩
      rw [vwSW_false_inv hv.1] at hcv
      rw [eq_of_compS_empty_left (ResU.CompS.comm hcv)]
      rw [vRLJ_mut_eq, extS_inst]
      refine ⟨vC_mut_retained hat hp hz he hvc, fun l' e' α' hl' hi' => ?_, fun l' hl' _ => ?_⟩
      · cases hl'
        rw [innerAt_inst_none ι hi] at hi'; exact absurd hi' (by simp)
      · cases hl'; exact payExt_inst hat hp
  | some p =>
      obtain ⟨e, αe⟩ := p
      have hview : vwEW (extS δ σ αs) e true αe ls ρ := by
        have := hpv.1 ℓ _ (ExAt.top hg) CellU.kind_mutOf_ne_own e αe hi
        rwa [← hρ] at this
      obtain ⟨hkind, hTy⟩ := (hcoh ℓ e αe rfl hi).1
      have hatl := (hcoh ℓ e αe rfl hi).2
      have hk : e.k = .mut := by
        cases hek : e.k with
        | «mut» => rfl
        | imm u₀ => rw [hek] at hkind; exact hkind.elim
      have hel : e.l = ℓ := (innerAt_mem hi).2
      refine ⟨dsPlace σ ℓ, PMap.empty, ρ, compS_empty_left ρ,
        ⟨vwSW_dsAt hview hok.1 List.not_mem_nil hi, hpv⟩, stratS_empty αs,
        fun ι hat ls' _ _ _ _ ρv τ hv hcv => ?_⟩
      rw [eq_of_compS_empty_left hcv]
      have hv' : vwEW (ι.sub (extS δ σ αs)) e true (ι.life1 αe) ls' ρv := by
        have := vwSW_dsAt_inv List.not_mem_nil (innerAt_inst_some ι hi) hv.1
        rwa [extS_inst] at this
      beta_reduce
      rw [vRLJ_mut_eq, extS_inst]
      refine ⟨vC_mut_bound ι hT hel hk hTy hvc hatl hv', fun l' e' α' hl' hi' => ?_,
        fun l' hl' hn => ?_⟩
      · cases hl'
        rw [innerAt_inst_some ι hi] at hi'
        obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 αe = α' := by simpa using hi'
        refine ⟨⟨by rw [hk]; trivial, tyEq_inst ι T hT hTy⟩, fun ψ hψ => ?_⟩
        exact (hv'.2 ψ (by rw [hel]; exact hψ)).1
      · cases hl'
        rw [innerAt_inst_some ι hi] at hn; exact absurd hn (by simp)

/-- **The thaw of an `Imm` leaf**: as a `Mut` leaf, its coherence kept at the records the retained
part (`KeepsT`) or the dropped view (`KeepsS`) is coherent with. -/
theorem relendJ_imm {a : Lifetime.Life} {T : VTy} (hT : CoreStable T) {δ : LSub} {σ : LStack}
    {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes} (hok : StackOK σ αs)
    (hob : OuterBelowTop αs) (hro : RecsOutside αs ls) (ht : TabAtS σ αs ρ)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) (h : vRLJ .binder0 σ δ (.imm a T) αs ls v ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' (.imm a T) αs' ls' v) αs ls ρ := by
  rw [vRLJ_imm_eq] at h
  obtain ⟨hvc, hcoh, hpay⟩ := h
  obtain ⟨α, -, ℓ, hsep⟩ := id hvc
  obtain ⟨⟨rfl, -⟩, S, u, χ, hχ, ls₀, hρ, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ.get ℓ = some (CellU.immOf S u χ hχ) := by rw [hρ]; simp
  have hko : (CellU.immOf S u χ hχ).kind ≠ Kind.own := by simp [CellU.immOf, CellU.kind]
  cases hi : innerAt σ αs ℓ with
  | none =>
      have hz : stratS αs ρ := stratS_single_unbound hok.1 ht hρ hi
      have hp := hpay ℓ rfl hi
      refine ⟨σ.map fun _ => false, ρ, PMap.empty, ResU.comp_empty_right ρ,
        ⟨vwSW_false hok.1, placeViewsL_empty⟩, hz,
        fun ι hat ls' he hkt _ _ ρv τ hv hcv => ?_⟩
      rw [vwSW_false_inv hv.1] at hcv
      rw [eq_of_compS_empty_left (ResU.CompS.comm hcv)]
      rw [vRLJ_imm_eq, extS_inst]
      refine ⟨vC_imm_retained hat hob hT hro hp hz he hkt hvc, fun l' e' α' hl' hi' => ?_,
        fun l' hl' _ => ?_⟩
      · cases hl'
        rw [innerAt_inst_none ι hi] at hi'; exact absurd hi' (by simp)
      · cases hl'; exact payExt_inst hat hp
  | some p =>
      obtain ⟨e, αe⟩ := p
      have hview : vwEW (extS δ σ αs) e true αe ls ρ := by
        have := hpv.1 ℓ _ (ExAt.top hg) hko e αe hi
        rwa [← hρ] at this
      obtain ⟨hkind, hTy⟩ := (hcoh ℓ e αe rfl hi).1
      have hatl := (hcoh ℓ e αe rfl hi).2
      obtain ⟨u₀, hk⟩ : ∃ u₀, e.k = .imm u₀ := by
        cases hek : e.k with
        | «mut» => rw [hek] at hkind; exact hkind.elim
        | imm u₀ => exact ⟨u₀, rfl⟩
      have hel : e.l = ℓ := (innerAt_mem hi).2
      refine ⟨dsPlace σ ℓ, PMap.empty, ρ, compS_empty_left ρ,
        ⟨vwSW_dsAt hview hok.1 List.not_mem_nil hi, hpv⟩, stratS_empty αs,
        fun ι hat ls' _ _ hks _ ρv τ hv hcv => ?_⟩
      rw [eq_of_compS_empty_left hcv]
      have hv' : vwEW (ι.sub (extS δ σ αs)) e true (ι.life1 αe) ls' ρv := by
        have := vwSW_dsAt_inv List.not_mem_nil (innerAt_inst_some ι hi) hv.1
        rwa [extS_inst] at this
      beta_reduce
      rw [vRLJ_imm_eq, extS_inst]
      refine ⟨vC_imm_bound hat hob hT hro hel hk hTy hvc hatl hks hv',
        fun l' e' α' hl' hi' => ?_, fun l' hl' hn => ?_⟩
      · cases hl'
        rw [innerAt_inst_some ι hi] at hi'
        obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 αe = α' := by simpa using hi'
        refine ⟨⟨by rw [hk]; trivial, tyEq_inst ι T hT hTy⟩, fun ψ hψ => ?_⟩
        exact (hv'.2 ψ (by rw [hel]; exact hψ)).1
      · cases hl'
        rw [innerAt_inst_some ι hi] at hn; exact absurd hn (by simp)

/-! ### The views handed under a box -/

theorem vwE_single {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {a : WRes}
    (h : vwE s e true α ls a) : ∃ ψ, a = ResU.single e.l ψ ∧ ψ.kind ≠ Kind.own := by
  obtain ⟨l, x, T, kd, cr⟩ := e
  cases kd with
  | «mut» =>
      obtain ⟨_, _, _, _, _, _, _, -, rfl, -⟩ := h
      exact ⟨_, rfl, CellU.kind_mutOf_ne_own⟩
  | imm v =>
      obtain ⟨_, _, _, _, _, rfl, -⟩ := h
      exact ⟨_, rfl, by simp [CellU.immOf, CellU.kind]⟩

theorem lt_at_of_inStratum {ψ : CellU BoCa.Loc Val} {a : Life} (h : ψ.InStratum a)
    (hk : ψ.kind ≠ Kind.own) : a < ψ.at := by
  cases ψ with
  | own v => exact absurd rfl hk
  | imm i => exact h
  | «mut» m => exact h

/-- **The views handed at an instantiation stay above an instantiated bound**: each dropped view is
at its entry's lifetime, above the bound when dropped, and the instantiation keeps the order. -/
theorem vwSW_outlives_inst {s s' : LSub} (ι : Inst) {α : Life} : ∀ {seen : List BoCa.Loc}
    {σ : LStack} {ds : List Bool} {αs : List Life} {ls ls' : List SRec} {ρn ρv : WRes},
    vwSW s seen σ ds αs ls ρn → vwSW s' seen σ ds (ι.life αs) ls' ρv → Outlives ρn α →
    Outlives ρv (ι.life1 α)
  | _, [], [], [], _, _, _, _, _, h₂, _ => by
      obtain ⟨rfl, -⟩ := h₂; exact ResU.inStratum_empty _
  | seen, e :: σ, d :: ds, αi :: αs, ls, ls', _, _, ⟨a, r, hc, ha, hr⟩,
      ⟨a', r', hc', ha', hr'⟩, ho => by
      have ho' := (outlives_comp hc α).mp ho
      refine (outlives_comp hc' _).mpr ⟨?_, vwSW_outlives_inst ι hr hr' ho'.2⟩
      cases hvis : vis seen e d
      · rw [hvis] at ha'; rw [vwEW_off_eq ha']; exact ResU.inStratum_empty _
      · rw [hvis] at ha ha'
        obtain ⟨ψ, rfl, hk⟩ := vwE_single ha.1
        obtain ⟨ψ', rfl, -⟩ := vwE_single ha'.1
        have hat : AtExactly αi ψ := ha.2 ψ (by simp)
        have hat' : AtExactly (ι.life1 αi) ψ' := ha'.2 ψ' (by simp)
        have hlt : α < αi := by
          have := lt_at_of_inStratum (ho'.1 e.l ψ (by simp)) hk
          rwa [hat.1] at this
        refine ResU.inStratum_single _ (CellU.inStratum_of_lt_at ?_)
        rw [hat'.1]; exact ι.life1_lt_iff.mpr hlt
  | _, [], [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, [], _ :: _, [], _, _, _, _, h, _, _ => h.elim
  | _, [], _ :: _, _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, [], [], _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h, _, _ => h.elim

/-- **No view dropped, none handed**: views at the empty resource are all off, and so are the
views handed with the same flags. -/
theorem vwSW_eq_empty_inst {s s' : LSub} (ι : Inst) : ∀ {seen : List BoCa.Loc} {σ : LStack}
    {ds : List Bool} {αs : List Life} {ls ls' : List SRec} {ρ : WRes},
    vwSW s seen σ ds αs ls PMap.empty → vwSW s' seen σ ds (ι.life αs) ls' ρ → ρ = PMap.empty
  | _, [], [], [], _, _, _, _, h₂ => h₂.1
  | seen, e :: σ, d :: ds, αi :: αs, ls, ls', _, ⟨a, r, hc, ha, hr⟩, ⟨a', r', hc', ha', hr'⟩ => by
      have ha0 := eq_empty_of_compS_left hc
      have hr0 := eq_empty_of_compS_right hc
      subst ha0 hr0
      have hr'0 := vwSW_eq_empty_inst ι hr hr'
      cases hvis : vis seen e d
      · rw [hvis] at ha'
        rw [vwEW_off_eq ha', hr'0] at hc'
        exact eq_empty_of_compS_empty hc'
      · rw [hvis] at ha
        obtain ⟨ψ, hψ, -⟩ := vwE_single ha.1
        have hget : (PMap.empty : WRes).get e.l = some ψ := by rw [hψ]; simp
        rw [PMap.empty_get] at hget; exact absurd hget (by simp)
  | _, [], [], _ :: _, _, _, _, h, _ => h.elim
  | _, [], _ :: _, [], _, _, _, h, _ => h.elim
  | _, [], _ :: _, _ :: _, _, _, _, h, _ => h.elim
  | _, _ :: _, [], [], _, _, _, h, _ => h.elim
  | _, _ :: _, [], _ :: _, _, _, _, h, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, h, _ => h.elim

/-! ### The thaw at every slot type `ThawFree` admits -/

/-- **A `U` value instantiated is a `U` value at the instantiation** (`ThawInstJ`): its clause at
the stack, re-read at an instantiation, is its clause there, every instantiation of the
instantiated stack composing with the first (`instComp`), the retained part's records along both
(`ext_inst_comp`), the dropped views' along both (`keepsSComp`). -/
theorem relendJ_thunk {C : CTy} {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {f : Val} {ρ : WRes} (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (h : vRLJ .binder0 σ δ (.thunk C) αs ls f ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' (.thunk C) αs' ls' f) αs ls ρ := by
  rw [vRLJ_thunk0] at h
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h ht hpv
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks _ ρv τ hv hcv => ?_⟩
  beta_reduce
  rw [vRLJ_thunk0]
  intro _ _
  refine ⟨ds, ρz, ρv, hcv, hv, stratS_inst ι hz,
    fun ι₂ hat₂ ls₂ he₂ hkt₂ hks₂ hro₂ ρv₂ τ₂ hv₂ hcv₂ => ?_⟩
  obtain ⟨ι₃, hat₃, hsub, hlife, hrecs⟩ := instComp αs ι ι₂ hat hat₂
  have hl₃ : ι₃.life αs = ι₂.life (ι.life αs) := by
    simp only [Inst.life, List.map_map]
    exact List.map_congr_left fun a _ => hlife a
  obtain ⟨he₃, hkt₃⟩ := ext_inst_comp hat₂ hz he hkt he₂ hkt₂
  have hks₃ := keepsSComp _ _ σ ds αs (ι.life αs) ls ls' ls' ls₂ ρn ρv ι ι₂ hn hv hks hks₂
  rw [← hrecs] at he₃ hkt₃ hks₃
  have := H ι₃ hat₃ ls₂ he₃ hkt₃ hks₃ (by rw [hl₃]; exact hro₂) ρv₂ τ₂
    (by rw [hl₃, hsub]; exact hv₂) hcv₂
  rw [hl₃, hsub] at this
  exact this

/-- **The thaw of a slot**, at every type `ThawFree` admits: W's formers by the clause's closure
(`relendJ_sep`, `relendJ_mono`), the box bound moved with the views (`vwSW_outlives_inst`), the
borrow leaves (`relendJ_mut`, `relendJ_imm`), the data leaves holding nothing. -/
theorem relendJ_value : ∀ (A : VTy), ThawFree A →
    ∀ {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLJ .binder0 σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' A αs' ls' v) αs ls ρ
  | .thunk _, _, _, _, _, _, _, _, _, _, _, ht, hpv, h => relendJ_thunk ht hpv h
  | .tensor A B, hAB, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      have R₁ := relendJ_value A hAB.1 hok hob hro (tabAtS_left hc ht) (placeViewsL_left hc hpv) h₁
      have R₂ := relendJ_value B hAB.2 hok hob hro (tabAtS_right hc ht)
        (placeViewsL_right hc hpv) h₂
      exact relendJ_mono (fun _ _ _ τ hτ => ⟨v₁, v₂, pure_sep_mk rfl hτ⟩)
        (relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩)
  | .sum A B, hAB, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inl ⟨v₁, pure_sep_mk rfl hτ⟩)
          (relendJ_value A hAB.1 hok hob hro ht hpv h₁)
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inr ⟨v₂, pure_sep_mk rfl hτ⟩)
          (relendJ_value B hAB.2 hok hob hro ht hpv h₂)
  | .bang A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨rfl, h₁⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := relendJ_value A hA hok hob hro ht hpv h₁
      have hz0 := eq_empty_of_compS_left hc
      have hn0 := eq_empty_of_compS_right hc
      subst hz0 hn0
      refine ⟨ds, PMap.empty, PMap.empty, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      have hv0 : ρv = PMap.empty := vwSW_eq_empty_inst ι hn.1 hv.1
      subst hv0
      exact ⟨eq_empty_of_compS_empty hcv, H ι hat ls' he hkt hks hro' PMap.empty τ hv hcv⟩
  | .box a A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨α, hα, hv, hout⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := relendJ_value A hA hok hob hro ht hpv hv
      have hzo := (outlives_comp hc α).mp hout
      refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv' hcv => ?_⟩
      refine ⟨ι.life1 α, ?_, H ι hat ls' he hkt hks hro' ρv τ hv' hcv, ?_⟩
      · rw [extS_inst, Inst.interp_sub, hα]; rfl
      · exact (outlives_comp hcv _).mpr ⟨ResU.InStratum.mono (ι.life1_le α) hzo.1,
          vwSW_outlives_inst ι hn.1 hv'.1 hzo.2⟩
  | .ref A, hA, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      obtain ⟨ds, ρz, ρn, hc', hn, hz, H⟩ :=
        relendJ_value A hA hok hob hro (tabAtS_right hc ht) (placeViewsL_right hc hpv) ha
      obtain ⟨ρz', hcz, hc''⟩ := compS_reassoc' hc' hc
      refine ⟨ds, ρz', ρn, hc'', hn, fun o ho => (outlives_comp hcz o).mpr
        ⟨by rw [hown]; exact ResU.inStratum_single_own o ℓ v', hz o ho⟩,
        fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      obtain ⟨τa, hτa, hτ⟩ := compS_reassoc hcz hcv
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, τa, hτ, hown,
        H ι hat ls' (he.right hcz) (hkt.right hcz) hks hro' ρv τa hv hτa⟩⟩
  | .mut _ T, hT, _, _, _, _, _, _, hok, _, _, ht, hpv, h =>
      relendJ_mut (T := T) (show CoreStable T from hT) hok ht hpv h
  | .imm _ T, hT, _, _, _, _, _, _, hok, hob, hro, ht, hpv, h =>
      relendJ_imm (T := T) (show CoreStable T from hT) hok hob hro ht hpv h
  | .unit, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .int _, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .opq _, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .unk, _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | .zero, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .tvar _, _, _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .mu _, hA, _, _, _, _, _, _, _, _, _, _, _, _ => hA.elim
  | .fam _, hA, _, _, _, _, _, _, _, _, _, _, _, _ => hA.elim

/-- **The thaw of a context's slots.** -/
theorem relendJ_gSep : ∀ (Γ : Ctx VTy) (γ : List Val), CtxThawFree Γ →
    ∀ {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {ρ : WRes},
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gSepRLJ .binder0 σ δ αs ls Γ γ ρ →
    RelendJ δ σ (fun δ' αs' ls' => gSepRLJ .binder0 σ δ' αs' ls' Γ γ) αs ls ρ
  | [], _, _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | _ :: _, [], _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | s :: Γ, v :: γ, hTF, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      have hTF' : CtxThawFree Γ := fun s' hs' hl => hTF s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLJ, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have R₁ := relendJ_value s.ty (hTF s List.mem_cons_self hl) hok hob hro
          (tabAtS_left hc ht) (placeViewsL_left hc hpv) h₁
        have R₂ := relendJ_gSep Γ γ hTF' hok hob hro (tabAtS_right hc ht)
          (placeViewsL_right hc hpv) h₂
        exact relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩
      · simp only [gSepRLJ, hl] at h ⊢
        exact relendJ_gSep Γ γ hTF' hok hob hro ht hpv h

/-- **`CtxRelendsThawFreeJ binder0`**: the thaw at every context `CtxThawFree` admits, at the
revised W. -/
theorem ctxRelendsThawFreeJ : CtxRelendsThawFreeJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ hTF δ σ αs ls γ ρ hok hob _ _ hro _ ht hpv hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  exact relendJ_mono (fun _ _ _ τ hτ => pure_sep_mk hlw hτ)
    (relendJ_gSep Γ γ hTF hok hob hro ht hpv hgs)

/-- **`ThawInstJ binder0`.** -/
theorem thawInstJ : ThawInstJ (ℍ := ℍ) .binder0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ ht hpv h => relendJ_thunk ht hpv h

/-! ### The `U` introductions at `binder0`, at the revised W -/

theorem gRLJ_dead_cons {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} {S : VTy}
    {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes} (h : gRLJ .binder0 σ δ αs ls Γ γ ρ) :
    gRLJ .binder0 σ δ αs ls (⟨S, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp h
  exact pure_sep_mk (by simpa using hlw) (by simpa [gSepRLJ] using hgs)

/-- A persistent context holds nothing, at the revised W. -/
theorem gSepRLJ_persistent {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes), Persistent Γ →
    gSepRLJ .binder0 σ δ αs ls Γ γ ρ → ρ = PMap.empty
  | [], [], _, _, h => h.1
  | [], _ :: _, _, _, h => h.1
  | _ :: _, [], _, _, h => h.1
  | s :: Γ, v :: γ, ρ, hP, h => by
      have hP' : Persistent Γ := fun s' hs' hl => hP s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLJ, hl, if_true] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        obtain ⟨A, hA⟩ := hP s List.mem_cons_self hl
        rw [hA] at h₁
        have e₁ : ρ₁ = PMap.empty := h₁.1
        rw [e₁, gSepRLJ_persistent Γ γ ρ₂ hP' h₂] at hc
        exact eq_empty_of_compS_empty hc
      · simp only [gSepRLJ, hl] at h
        exact gSepRLJ_persistent Γ γ ρ hP' h

/-- **The `U` clause of `thunk M : U (F A)` at `binder0`, at the revised W**: the context's thaw
(`ctxRelendsThawFreeJ`), and at each instantiation the body by the premise there: the stack in
shape, its outermost lend below `⊤`, the judgement's entries, the models and the readings kept
by the instantiation, the table and the guard's views by `guardInst`. -/
theorem thunkF_U_J {Δ : LifeCtx} {Γ : Ctx VTy} (hTF : CtxThawFree Γ) {M : Expr} {A : VTy}
    (hM : SemSJ (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)))
    (hBL : BindersLow (⟨.unit, false⟩ :: Γ) (.ret A))
    (hSc : Scoped Δ (⟨.unit, false⟩ :: Γ) (.ret A))
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hJ : StackJ σ αs δ Δ (⟨.unit, false⟩ :: Γ) (.ret A)) (hSD : SubDom δ Δ)
    (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls) (hso : SubOutside σ αs δ)
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLJ .binder0 σ δ αs ls Γ γ ρ) :
    vRLJ (ℍ := ℍ) .binder0 σ δ (.thunk (.ret A)) αs ls (.lam (Expr.psub 1 γ M)) ρ := by
  rw [vRLJ_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    ctxRelendsThawFreeJ Δ Γ hTF δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  have hg' := H ι hat ls' he hkt hks hro' ρv τ hv hcv
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← GhostEnd.substAll_cons_l]
  exact hM hBL hSc (ι.sub δ) σ (ι.life αs) ls' (Val.unit :: γ) τ (hok.inst ι)
    (outerBelowTop_inst ι hob) (stackJInst σ αs δ Δ _ _ ι hok.1 hJ) (subDom_inst ι hSD)
    (instModels Δ δ σ αs ι hMod) hro' (subOutsideInst σ αs δ ι hso) ht' hpv'
    (gRLJ_dead_cons hg')

/-- **The `U` clause of `thunk V : U C` at `binder0`, at the revised W**: as `thunkF_U_J`, the thunk
the λ-value itself. -/
theorem thunkV_U_J {Δ : LifeCtx} {Γ : Ctx VTy} (hTF : CtxThawFree Γ) {N : Expr} {C : CTy}
    (hC : C.isRet = false) (hN : SemSJ (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C))
    (hBL : BindersLow Γ C) (hSc : Scoped Δ Γ C)
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs) (hJ : StackJ σ αs δ Δ Γ C)
    (hSD : SubDom δ Δ) (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls)
    (hso : SubOutside σ αs δ) (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLJ .binder0 σ δ αs ls Γ γ ρ) :
    vRLJ (ℍ := ℍ) .binder0 σ δ (.thunk C) αs ls (.lam (Expr.psub 1 γ N)) ρ := by
  rw [vRLJ_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    ctxRelendsThawFreeJ Δ Γ hTF δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  rw [forceE_of_not_ret hC]
  exact hN hBL hSc (ι.sub δ) σ (ι.life αs) ls' γ τ (hok.inst ι) (outerBelowTop_inst ι hob)
    (stackJInst σ αs δ Δ Γ C ι hok.1 hJ) (subDom_inst ι hSD) (instModels Δ δ σ αs ι hMod) hro'
    (subOutsideInst σ αs δ ι hso) ht' hpv' (H ι hat ls' he hkt hks hro' ρv τ hv hcv)

/-- **`ThunkFRow` at `binder0`, at the revised W, at the contexts `CtxThawFree` admits.** -/
theorem thunkFRowTFJ : ThunkFRowTFJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hTF hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ (thunkF_U_J hTF hM ⟨hBL.1, fun s hs hl => ?_⟩
    ⟨hSc.1, fun s hs hl => ?_⟩ hok hob (stackJ_body hJ (fun _ _ _ h => by cases h)
      (fun _ h => h) fun _ => ctxAvoids_dead) hSD hMod hro hso ht hpv hg)
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`ThunkVRow` at `binder0`, at the revised W, at the contexts `CtxThawFree` admits.** -/
theorem thunkVRowTFJ : ThunkVRowTFJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hTF hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ (thunkV_U_J hTF hC hN hBL hSc hok hob
    (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hro hso ht hpv hg)

/-- **`BangThunkFRow` at `binder0`, at the revised W, at the contexts `CtxThawFree` admits**: the
context is persistent, so it, and the thunk with it, hold nothing. -/
theorem bangThunkFRowTFJ : BangThunkFRowTFJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hTF hP hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLJ_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨hρ, thunkF_U_J hTF hM ⟨hBL.1, fun s hs hl => ?_⟩
    ⟨hSc.1, fun s hs hl => ?_⟩ hok hob (stackJ_body hJ (fun _ _ _ h => by cases h)
      (fun _ h => h) fun _ => ctxAvoids_dead) hSD hMod hro hso ht hpv hg⟩
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`BangThunkVRow` at `binder0`, at the revised W, at the contexts `CtxThawFree` admits.** -/
theorem bangThunkVRowTFJ : BangThunkVRowTFJ (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hTF hP hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLJ_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ ⟨hρ, thunkV_U_J hTF hC hN hBL hSc hok hob
    (stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hro hso ht hpv hg⟩

/-- **The `U` side of statement 0 at `binder0`, at the revised W, at the contexts `CtxThawFree`
admits.** -/
theorem statement0UThawFreeJ : Statement0UThawFreeJ (ℍ := ℍ) .binder0 :=
  ⟨thawInstJ, ctxRelendsThawFreeJ, thunkFRowTFJ, thunkVRowTFJ, bangThunkFRowTFJ,
    bangThunkVRowTFJ⟩

end ProbeD1

end
