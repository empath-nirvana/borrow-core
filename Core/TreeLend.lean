import Core.TreePool
import Support.Model.Tree.Port.Six43to46

/-!
# Opening and ending a lend at `twp` over the tree world  `[spec §62]`

A lend of an `own` cell `ℓ ↦ own(())` with the empty escrow, as two `twp_update` instances:

* **open** (`twp_lendOpen`): `ℓ ↦ own(())` becomes the lend cell `ℓ ↦ imm({α}, (), ∅)`
  (`viewRes α ℓ`), the run owns the record `lendRec ℓ` (`TWNT.immFrame`), and the list carries it
  tagged `α`. Nothing is asked of `α`;
* **end** (`twp_lendEnd`): the lend cell goes back to `ℓ ↦ own(())` (`TWNT.immEnd`), the record
  leaves the run's records and the list. The frame and the rest of the run's resource hold nothing
  at `ℓ` at any depth (`FdEsc ℓ ∅`, which is `immEnd_valid_of_fdEsc`'s condition at the empty
  escrow).

The lend cell is an `imm` cell, so it splits into copies (`viewRes_dup`): a copy is a shared view
of `ℓ` another branch may hold across a stop. The end needs every copy back: the condition at the
end is that no other part holds anything at `ℓ`.

Both rules rest on one fact about the carrier (`flat_compS_view`, `ag_compS_view`): beside a
resource whose flattening misses `ℓ`, the lend cell adds itself and nothing else to the
flattening and to the aliasable walk, as `ℓ ↦ own(())` adds itself to the exclusive walk
(`flat_compS_ownT`). The lowering is the same either way (`()` at `ℓ`).

**Scope.** The escrow is empty, so the record has no lineage (`emptyRec_no_desc`) and the end's
membership conditions reduce to "the record and nothing else leaves". Escrows that hand out views
of their contents (`TWNT.reb`) are not covered here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

section Carrier
variable {K K' : WCactus}

/-! ### The lend cell beside a resource -/

theorem exST_view (β : Life) (m : BoCa.Loc) : ExST (viewRes (K := K) β m) PMap.empty :=
  exST_all_imm fun x ψ e => by
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact CellUT.kind_immOf _ _ _ _

theorem agWT_view (β : Life) (m : BoCa.Loc) : AgWT (viewRes (K := K) β m) (viewRes β m) := by
  obtain ⟨τ, e, a, -, ha, -⟩ := valid_view (K := K) β m
  obtain rfl := ag_view ha
  exact ha

/-- The right part of a composite misses what the composite misses. -/
theorem get_none_of_compS_right {a b c : TRes K} (h : ResUT.CompS a b c) {l : BoCa.Loc}
    (hl : c.get l = none) : b.get l = none := by
  cases e : b.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨χ, eχ, -⟩ := compS_get_right' h e
      rw [hl] at eχ; cases eχ

theorem get_none_of_compS_left {a b c : TRes K} (h : ResUT.CompS a b c) {l : BoCa.Loc}
    (hl : c.get l = none) : a.get l = none :=
  get_none_of_compS_right (ResUT.CompS.comm h) hl

/-- **The lend cell beside a resource whose flattening misses `ℓ`** adds itself to the
flattening. -/
theorem flat_compS_view {ρ ρ' σ : TRes K} {β : Life} {l : BoCa.Loc}
    (hc : ResUT.CompS ρ (viewRes β l) ρ') (hσ : ResUT.Flat ρ σ) (hl : σ.get l = none) :
    ∃ τ, ResUT.Flat ρ' τ ∧ ResUT.CompS σ (viewRes β l) τ := by
  classical
  obtain ⟨e₁, a₁, he₁, ha₁, hσc⟩ := hσ
  obtain ⟨τ, hτ⟩ := (ResUT.compS_defined_iff σ (viewRes β l)).mpr
    (compatS_single_of_get_noneT hl)
  obtain ⟨a, hav, heτ⟩ := (ResUT.CompS.assoc e₁ a₁ (viewRes β l) τ).mpr ⟨σ, hσc, hτ⟩
  have hR : ResUT.CompR a₁ (viewRes β l) a := (ResUT.compR_iff_compS hav.1 a).mpr hav
  exact ⟨τ, (ResUT.Flat.split hc).mpr ⟨e₁, PMap.empty, e₁, a₁, viewRes β l, a, he₁,
    exST_view β l, ResUT.compS_empty_right e₁, ha₁, agWT_view β l, hR, heτ⟩, hτ⟩

/-- **The lend cell beside a resource whose flattening misses `ℓ`** adds itself to the
aliasable walk, and the walk of the rest misses `ℓ`. -/
theorem ag_compS_view {ρ ρ' σ a' : TRes K} {β : Life} {l : BoCa.Loc}
    (hc : ResUT.CompS ρ (viewRes β l) ρ') (hσ : ResUT.Flat ρ σ) (hl : σ.get l = none)
    (ha' : AgWT ρ' a') :
    ∃ a, AgWT ρ a ∧ a.get l = none ∧ a'.get l = some (viewCell β) ∧
      ∀ m, m ≠ l → a'.get m = a.get m := by
  obtain ⟨σ₁, σ₂, h₁, h₂, h₁₂⟩ := (AgWT.split hc).mp ha'
  obtain rfl := AgWT.functional h₂ (agWT_view β l)
  obtain ⟨e₁, a₁, -, ha₁, hσc⟩ := hσ
  have e₀ : a₁ = σ₁ := AgWT.functional ha₁ h₁
  subst e₀
  have hσ₁l : a₁.get l = none := get_none_of_compS_right hσc hl
  refine ⟨a₁, h₁, hσ₁l, ?_, fun m hm => ?_⟩
  · rw [ResUT.Comp.get_of_left_none h₁₂ hσ₁l]; exact ResUT.single_get_self _ _
  · exact ResUT.Comp.get_of_right_none h₁₂ (ResUT.single_get_ne _ hm)

/-- The aliasable walk beside an `own` cell is the walk of the rest. -/
theorem ag_compS_own {ρ ρ' a : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ') (ha : AgWT ρ a) : AgWT ρ' a :=
  (AgWT.split hc).mpr ⟨a, PMap.empty, ha, AgWT.single_own l v, ResUT.comp_empty_right a⟩

/-- The lend cell's copies compose to the lend cell. -/
theorem viewRes_dup (β : Life) (l : BoCa.Loc) :
    ResUT.CompS (viewRes (K := K) β l) (viewRes β l) (viewRes β l) := by
  have h := ResUT.compS_single_imm (K := K) l (TSet.single β) (TSet.single β) BoCa.Val.unit
    PMap.empty (emptyT_inStratum _) (emptyT_inStratum _) (emptyT_inStratum _)
  have hu : TSet.single β ∪ TSet.single β = TSet.single β := TSet.ext (by simp)
  rw [hu] at h
  exact h

/-! ### The lend cell under re-reading -/

theorem rr_view {Θ : LocTy} {β : Life} {l : BoCa.Loc} :
    RR Θ (viewRes (K := K) β l) (viewRes (K := K') β l) := by
  classical
  refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
  · by_cases hm : m = l
    · subst hm; simp [viewRes]
    · simp [viewRes, ResUT.single_get_ne _ hm]
  · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
    exact RC.immOf_of _ _ RR.empty

/-- A re-read lend cell is the lend cell. -/
theorem rr_view_eq {Θ : LocTy} {β : Life} {l : BoCa.Loc} {ρ' : TRes K'}
    (h : RR Θ (viewRes (K := K) β l) ρ') : ρ' = viewRes β l := by
  obtain ⟨ψ', rfl, hr⟩ := RR.of_sng h
  obtain ⟨χ', h', rfl, hχ⟩ := RC.immOf_inv hr
  obtain rfl := RR.of_empty hχ
  rfl

theorem holdsMut_of_compS_view {a y : TRes K} {β : Life} {l' : BoCa.Loc}
    (hc : ResUT.CompS a (viewRes β l') y) {l : BoCa.Loc} (h : HoldsMut y l) : HoldsMut a l := by
  classical
  have hview : ∀ k ψ, (viewRes (K := K) β l').get k = some ψ → ψ = viewCell β := fun k ψ e => by
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; rfl
  cases h with
  | @top _ _ m e =>
      rcases ResUT.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
      · rw [e] at f; cases f
      · rw [e] at f; cases f; exact .top f₁
      · rw [e] at f; cases f
        exact absurd (hview _ _ f₂) (by simp [viewCell, CellUT.immOf])
      · rw [e] at f; cases f
        exact absurd (CellUT.CompS.kind hC) (by simp [CellUT.kind])
  | @deep _ k _ ψ e hm =>
      rcases ResUT.Comp.get hc k with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
      · rw [e] at f; cases f
      · rw [e] at f; cases f; exact .deep f₁ hm
      · rw [e] at f; cases f
        obtain rfl := hview _ _ f₂
        have hw : (viewCell (K := K) β).wit = PMap.empty := by simp [viewCell, CellUT.wit_immOf]
        rw [hw] at hm
        cases hm with
        | top e₀ => simp at e₀
        | deep e₀ _ => simp at e₀
      · rw [e] at f; cases f
        have hw := (CellUT.CompS.wit hC).1
        exact .deep f₁ (hw ▸ hm)

theorem rr_own {Θ : LocTy} {l : BoCa.Loc} {v : BoCa.Val} :
    RR Θ (ResUT.single l (CellUT.ownOf (K := K) v)) (ResUT.single l (CellUT.ownOf (K := K') v)) := by
  classical
  refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
  · by_cases hm : m = l
    · subst hm; simp
    · simp [ResUT.single_get_ne _ hm]
  · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
    exact RC.own _ _

/-- A re-read resource holding the lend cell at `ℓ` holds it there. -/
theorem rr_view_get {Θ : LocTy} {β : Life} {l : BoCa.Loc} {ρ : TRes K} {ρ' : TRes K'}
    (h : RR Θ ρ ρ') (e : ρ.get l = some (viewCell β)) : ρ'.get l = some (viewCell β) := by
  obtain ⟨ψ', e', hr⟩ := h.get_some e
  obtain ⟨χ', h', rfl, hχ⟩ := RC.immOf_inv hr
  obtain rfl := RR.of_empty hχ
  exact e'

/-- A part beside a singleton, missing its location, is the composite without it. -/
theorem eq_del_of_compS_single' {ρ ρ₂ : TRes K} {l : BoCa.Loc} {ψ : TCell K}
    (hc : ResUT.CompS ρ₂ (ResUT.single l ψ) ρ) (hl : ρ₂.get l = none) : ρ₂ = ρ.del l := by
  classical
  refine PMap.ext fun x => ?_
  by_cases ex : x = l
  · subst ex; rw [ResUT.del_get_self]; exact hl
  · rw [ResUT.del_get_ne _ ex, ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ ex)]

/-- **A sub-list of a re-read list has a re-reading** inside the re-read list. -/
theorem forall₂_sub {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    ∀ {zs : List α}, (∀ z ∈ zs, z ∈ xs) → ∃ ws, List.Forall₂ R zs ws ∧ ∀ y ∈ ws, y ∈ ys
  | [], _ => ⟨[], .nil, fun _ h => by cases h⟩
  | z :: zs, hz => by
      obtain ⟨y, hy, hzy⟩ := forall₂_mem_left h (hz z List.mem_cons_self)
      obtain ⟨ws, hws, hin⟩ := forall₂_sub h (zs := zs) fun z' h' => hz z' (List.mem_cons_of_mem _ h')
      exact ⟨y :: ws, .cons hzy hws, fun y' h' => by
        rcases List.mem_cons.mp h' with rfl | h'
        · exact hy
        · exact hin y' h'⟩

/-! ### The record of a lend -/

/-- **The record of a lend of `ℓ ↦ own(())`**: lent location `ℓ`, value `()`, the empty escrow,
code `unit`. -/
def lendRec {K : WCactus} (l : BoCa.Loc) : FrameRecT K := ⟨l, BoCa.Val.unit, PMap.empty, KTy.unit⟩

theorem lendRec_rr {Θ' : CodeTy} (l : BoCa.Loc) :
    RecRR Θ' (lendRec (K := K) l) (lendRec (K := K') l) :=
  ⟨rfl, rfl, rfl, RR.empty⟩

/-- A record re-read to the lend's record is the lend's record. -/
theorem lendRec_rr_eq {Θ' : CodeTy} {l : BoCa.Loc} {r : FrameRecT K}
    (h : RecRR Θ' r (lendRec (K := K') l)) : r = lendRec l := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hR : r.R = PMap.empty := PMap.ext fun m => by
    simpa [lendRec] using (h₄.1 m).mpr (by simp [lendRec])
  obtain ⟨le, v, R, T⟩ := r
  simp only [lendRec] at h₁ h₂ h₃ hR
  subst h₁; subst h₂; subst h₃; subst hR
  rfl

theorem exDom_empty {x : BoCa.Loc} : ¬ ExDom (PMap.empty : TRes K) x := by
  intro h
  cases h with
  | top e _ => simp at e
  | deep e _ _ => simp at e

theorem recMask_lendRec {O : List (FrameRecT K)} {l x : BoCa.Loc} :
    recMask (lendRec l :: O) x ↔ x = l ∨ recMask O x := by
  simp only [recMask, List.mem_cons, exists_eq_or_imp]
  constructor
  · rintro (h | h)
    · exact Or.inl (h.resolve_right exDom_empty)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

theorem descRT_lendRec {l : BoCa.Loc} {d : FrameRecT K} (h : DescRT (lendRec l) d) :
    d = lendRec l := by
  obtain ⟨p, hp⟩ := h
  cases hp with
  | nil => rfl
  | cons hs _ =>
      obtain ⟨-, ζ, eζ, -⟩ := hs
      simp [lendRec] at eζ

theorem linLoc_lendRec {l m : BoCa.Loc} : ¬ LinLocT (lendRec (K := K) l) m := by
  rintro ⟨d, hd, ζ, eζ, -⟩
  obtain rfl := descRT_lendRec hd
  simp [lendRec] at eζ

end Carrier

/-! ### Open -/

/-- **Open a lend at `twp`.** The run holds `ℓ ↦ own(())` beside `Z`; from there on it holds the
lend cell `ℓ ↦ imm({α}, (), ∅)` beside `Z`, owns the lend's record `lendRec ℓ`, and the list
carries it tagged `α`. An instance of `twp_update`: `TWNT.immFrame` at the world's records, the
record's frame lifetime `α` read off the lend cell (the only view at `ℓ`), the other records'
frame lifetimes kept (`ℓ` is no lineage location of theirs, `le_not_linLoc`), `UpdX` masked at
`ℓ` (the record's mask), and the frame holds nothing at `ℓ` (the world held `own` there). -/
theorem twp_lendOpen {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ : TRes w.K} {l : BoCa.Loc} (α : Life)
    (hρ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ)
    (hρ₁ : ResUT.CompS Z (viewRes α l) ρ₁)
    (h : twp (ℍ := ℍ) F Q n w ((lendRec l, α) :: ls) (lendRec l :: O) e ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  classical
  refine twp_update (fun w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO _ _ hc hS hR hI => ?_) h
  have hZl : Z.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hρ.1)
  have hρ₀l : ρ₀.get l = some (CellUT.ownOf BoCa.Val.unit) :=
    RR.own_fwd hr (by rw [ResUT.Comp.get_of_left_none hρ hZl, ResUT.single_get_self])
  have hρ₀ : ResUT.CompS (ρ₀.del l) (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₀ :=
    ResUT.CompS.comm (compS_single_del hρ₀l)
  have hZ : Z = ρ.del l := eq_del_of_compS_single (ResUT.CompS.comm hρ)
  have hrZ : RRw (w := w) (w' := w₀) Z (ρ₀.del l) := hZ ▸ RR.del hr l
  obtain ⟨ρ₁₀, hρ₁₀, hr₁⟩ := RR.compS hrZ rr_view hρ₁
  -- the rest of the world, `Y = ρf ● Z₀`, and its flattening, which misses `ℓ`
  obtain ⟨Y, hY, hYf⟩ := (ResUT.CompS.assoc ρf (ρ₀.del l) _ fρ).mp ⟨ρ₀, hρ₀, hc⟩
  obtain ⟨τ, hτ⟩ := hI.valid
  obtain ⟨σ, hσ, hστ⟩ := (flat_compS_ownT hYf).mp hτ
  have hσl : σ.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hστ.1)
  obtain ⟨fρ₁, hY₁⟩ := (ResUT.compS_defined_iff Y (viewRes α l)).mpr
    (compatS_single_of_get_noneT (get_eq_none_of_flatT hσ hσl))
  obtain ⟨τ₁, hτ₁, hστ₁⟩ := flat_compS_view hY₁ hσ hσl
  have hv₁ : ResUT.Valid fρ₁ := ⟨τ₁, hτ₁⟩
  obtain ⟨ρ', hρ', hfρ₁⟩ := (ResUT.CompS.assoc ρf (ρ₀.del l) (viewRes α l) fρ₁).mpr ⟨Y, hY, hY₁⟩
  rw [ResUT.CompS.functional hρ' hρ₁₀] at hfρ₁
  -- the records
  have hTW := hR.1
  have hTin : TWNT w₀.K w₀.Θ w₀.tc fρ₁ (lendRec l :: ps) (lendRec l :: ([] ++ rsOfT ls₀)) :=
    TWNT.immFrame (ds := []) KTy.unit (emptyT_inStratum _) hTW (ResUT.compS_empty_right _)
      (ResUT.CompS.comm hYf) ⟨rfl, rfl⟩ (ResUT.CompS.comm hY₁) hv₁
      (fun d => ⟨fun h => by simp at h, fun h => (emptyRec_no_desc l _ _ d h).elim⟩)
  have hpsl : ∀ q ∈ ps, q.le ≠ l := by
    intro q hq hql
    obtain ⟨a, ha⟩ := agW_of_valid ⟨τ, hτ⟩
    obtain ⟨ψ, eψ⟩ := leInv_view hTW hq a ha
    obtain ⟨eY, aY, -, haY, hσc⟩ := hσ
    have ea : aY = a := AgWT.functional haY (alloc_agT hYf ha)
    subst ea
    rw [hql, get_none_of_compS_right hσc hσl] at eψ
    cases eψ
  have hFLold : ∀ p ∈ ps, ∀ t, FrameLifeT w₀.K fρ p t → FrameLifeT w₀.K fρ₁ p t := by
    intro p hp t ⟨h₁, h₂⟩
    refine ⟨fun a₁ ha₁ ζ s eζ hs y hy => ?_, fun a₁ ha₁ m hm ψ s eψ hs y hy => ?_⟩
    · obtain ⟨a, ha, -, -, hm⟩ := ag_compS_view hY₁ hσ hσl ha₁
      exact h₁ a (ag_compS_own hYf ha) ζ s (by rw [← hm _ (hpsl p hp)]; exact eζ) hs y hy
    · obtain ⟨a, ha, -, -, hm'⟩ := ag_compS_view hY₁ hσ hσl ha₁
      by_cases hml : m = l
      · subst hml
        exact (le_not_linLoc hTin (List.mem_cons_of_mem _ hp) List.mem_cons_self hm).elim
      · exact h₂ a (ag_compS_own hYf ha) m hm ψ s (by rw [← hm' m hml]; exact eψ) hs y hy
  have hFLnew : FrameLifeT w₀.K fρ₁ (lendRec l) α := by
    refine ⟨fun a₁ ha₁ ζ s eζ hs y hy => ?_, fun a₁ _ m hm => (linLoc_lendRec hm).elim⟩
    obtain ⟨a, -, -, hl₁, -⟩ := ag_compS_view hY₁ hσ hσl ha₁
    have eζ' : a₁.get l = some ζ := eζ
    rw [hl₁] at eζ'
    cases eζ'
    simp only [viewCell, CellUT.lsOfI_immOf, Option.some.injEq] at hs
    subst hs
    simpa using hy
  have htg : TaggedT w₀.K fρ₁ (lendRec l :: ps) ((lendRec l, α) :: ls₀) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨lendRec l, List.mem_cons_self, DescRT.refl _, hFLnew⟩
    · obtain ⟨p, hp, hd, hf⟩ := hR.2 x hx
      exact ⟨p, List.mem_cons_of_mem _ hp, hd, hFLold p hp x.2 hf⟩
  -- the run's part, flattened, and the update masked at `ℓ`
  have hvρ₀ : ResUT.Valid ρ₀ := (ResUT.Valid.split hc ⟨τ, hτ⟩).2
  obtain ⟨σ₀, hσ₀⟩ := hvρ₀
  obtain ⟨σZ, hσZ, hσZ₀⟩ := (flat_compS_ownT hρ₀).mp hσ₀
  have hσZl : σZ.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hσZ₀.1)
  obtain ⟨σ₁', hσ₁', hσZ₁⟩ := flat_compS_view hρ₁₀ hσZ hσZl
  have hcovY : CovR (sem w₀.Θ) w₀.K Y := CovR.of_compS_left hYf hI.1
  have hcovZ : CovR (sem w₀.Θ) w₀.K (ρ₀.del l) :=
    CovR.of_compS_left (ResUT.CompS.comm hY) hcovY
  obtain ⟨τa, τb, ha, hb, hx⟩ :=
    UpdX.of_rr (Θ := sem w₀.Θ) (WCactus.Ext.refl _) (recMask O₀) ⟨σZ, hσZ⟩ (RR.refl hcovZ)
  obtain rfl := ResUT.Flat.functional hσZ ha
  obtain rfl := ResUT.Flat.functional hσZ hb
  have hmask : ∀ k, k ≠ l → recMask (lendRec l :: O₀) k = recMask O₀ k := fun k hk =>
    propext (by rw [recMask_lendRec]; exact ⟨fun h => h.resolve_left hk, Or.inr⟩)
  have hupd : UpdX (sem w₀.Θ) (recMask O₀) (recMask (lendRec l :: O₀)) ρ₀ ρ₁₀ := by
    refine ⟨σ₀, σ₁', hσ₀, hσ₁', fun k => ?_⟩
    by_cases hk : k = l
    · subst hk
      refine ⟨fun ψ e hk' _ => ?_, fun ψ' _ _ hE' => absurd (recMask_lendRec.mpr (Or.inl rfl)) hE'⟩
      rw [ResUT.Comp.get_of_left_none hσZ₀ hσZl, ResUT.single_get_self] at e
      cases e; exact absurd rfl hk'
    · rw [hmask k hk, ResUT.Comp.get_of_right_none hσZ₀ (ResUT.single_get_ne _ hk),
        ResUT.Comp.get_of_right_none hσZ₁ (ResUT.single_get_ne _ hk)]
      exact hx k
  have hnone : NoneAt (MaskDiff (recMask O₀) (recMask (lendRec l :: O₀))) ρf := by
    refine NoneAt.of_compS_left hY ⟨σ, hσ⟩ fun τY hτY x hx => ?_
    obtain rfl := ResUT.Flat.functional hσ hτY
    by_cases hxl : x = l
    · subst hxl; exact hσl
    · unfold MaskDiff at hx
      rw [hmask x hxl] at hx
      tauto
  refine ⟨ρ₁₀, fρ₁, (lendRec l, α) :: ls₀, lendRec l :: O₀, lendRec l :: ps,
    ⟨hE.1, fun x hx => (AgreeOn.of_compS_left hρ hE.2) x (holdsMut_of_compS_view hρ₁ hx)⟩,
    hr₁, .cons ⟨lendRec_rr l, rfl⟩ hl, .cons (lendRec_rr l) hO,
    ⟨hfρ₁.1, fρ₁, hfρ₁, hv₁⟩, hfρ₁, ⟨fun p => ?_, fun p hp q hq => ?_⟩, ⟨hTin, htg⟩,
    ⟨fun m ψ e => ?_, ?_⟩, hupd, hnone⟩
  · simp only [List.mem_cons]; rw [hS.1 p]; tauto
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact fun e => hpsl q ((hS.1 q).mpr (Or.inr hq)) e.symm
    · exact hS.2 p hp q hq
  · by_cases hm : m = l
    · subst hm
      rw [ResUT.Comp.get_of_left_none hY₁ (get_eq_none_of_flatT hσ hσl), viewRes,
        ResUT.single_get_self] at e
      cases e
      exact Cov.immOf_iff.mpr fun x ψ e => by simp at e
    · rw [ResUT.Comp.get_of_right_none hY₁ (ResUT.single_get_ne _ hm)] at e
      exact hcovY m ψ e
  · obtain ⟨τ', hτ', hval⟩ := hI.2
    obtain rfl := ResUT.Flat.functional hτ hτ'
    refine ⟨τ₁, hτ₁, fun x => ?_⟩
    rw [hval x]
    by_cases hx : x = l
    · subst hx
      rw [ResUT.Comp.get_of_left_none hστ hσl, ResUT.Comp.get_of_left_none hστ₁ hσl, viewRes,
        ResUT.single_get_self, ResUT.single_get_self]
      rfl
    · rw [ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ hx),
        ResUT.Comp.get_of_right_none hστ₁ (ResUT.single_get_ne _ hx)]

/-! ### End -/

/-- **End a lend at `twp`.** The run holds the lend cell `ℓ ↦ imm({α}, (), ∅)` beside `Z` and owns
`lendRec ℓ`; from there on it holds `ℓ ↦ own(())` beside `Z`, owns the records `O₁` (`O` without
the lend's), and the list is `ls₁` (`ls` without the lend's entries). The end needs every copy of
the lend cell back: `Z` and the frame hold nothing at `ℓ` at any depth, which is `FdEsc ℓ ∅`
against the rest of the world. An instance of `twp_update`: `TWNT.immEnd`, the records' frame
lifetimes kept (the aliasable walk loses `ℓ` and nothing else), `UpdX` masked at `ℓ`. -/
theorem twp_lendEnd {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls ls₁ : List (SRecT w.K)}
    {O O₁ : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ : TRes w.K} {l : BoCa.Loc} {α : Life}
    (hρ : ResUT.CompS Z (viewRes α l) ρ)
    (hρ₁ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₁)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf)
    (hO : ∀ x, x ∈ O ↔ x = lendRec l ∨ x ∈ O₁) (hO₁ : lendRec l ∉ O₁)
    (hls : ∀ x, x ∈ ls ↔ x.1 = lendRec l ∨ x ∈ ls₁) (hls₁ : ∀ x ∈ ls₁, x.1 ≠ lendRec l)
    (h : twp (ℍ := ℍ) F Q n w ls₁ O₁ e ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  classical
  refine twp_update (fun w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ _ hc hS hR hI => ?_) h
  obtain ⟨σZw, hσZw⟩ := hvZ
  have hZl : Z.get l = none := get_eq_none_of_flatT hσZw (hZ σZw hσZw l rfl)
  have hρl : ρ.get l = some (viewCell α) := by
    rw [ResUT.Comp.get_of_left_none hρ hZl, viewRes, ResUT.single_get_self]
  have hρ₀ : ResUT.CompS (ρ₀.del l) (viewRes α l) ρ₀ := ResUT.del_compS (rr_view_get hr hρl)
  have hZd : Z = ρ.del l := eq_del_of_compS_single' hρ hZl
  have hrZ : RRw (w := w) (w' := w₀) Z (ρ₀.del l) := hZd ▸ RR.del hr l
  obtain ⟨ρ₁₀, hρ₁₀, hr₁⟩ := RR.compS hrZ rr_own hρ₁
  have hZ₀ : NoneAt (· = l) (ρ₀.del l) := NoneAt.rr hE.1 ⟨σZw, hσZw⟩ hrZ hZ
  -- the rest of the world, `Y = ρf ● Z₀`; it holds nothing at `ℓ`
  obtain ⟨Y, hY, hYf⟩ := (ResUT.CompS.assoc ρf (ρ₀.del l) _ fρ).mp ⟨ρ₀, hρ₀, hc⟩
  have hvf : ResUT.Valid fρ := hI.valid
  have hvY : ResUT.Valid Y := (ResUT.Valid.split hYf hvf).1
  have hvYp := ResUT.Valid.split hY hvY
  have hYl : NoneAt (· = l) Y := NoneAt.compS hY hvYp.1 hvYp.2 (hF w₀ ρf hFρ) hZ₀
  obtain ⟨σ, hσ⟩ := hvY
  have hσl : σ.get l = none := hYl σ hσ l rfl
  obtain ⟨τ, hτ, hστ⟩ := flat_compS_view hYf hσ hσl
  obtain ⟨fρ₁, hY₁⟩ := (ResUT.compS_defined_iff Y (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT (get_eq_none_of_flatT hσ hσl))
  obtain ⟨τ₁, hστ₁⟩ := (ResUT.compS_defined_iff σ (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT hσl)
  have hτ₁ : ResUT.Flat fρ₁ τ₁ := (flat_compS_ownT hY₁).mpr ⟨σ, hσ, hστ₁⟩
  have hv₁ : ResUT.Valid fρ₁ := ⟨τ₁, hτ₁⟩
  obtain ⟨ρ', hρ', hfρ₁⟩ := (ResUT.CompS.assoc ρf (ρ₀.del l) _ fρ₁).mpr ⟨Y, hY, hY₁⟩
  rw [ResUT.CompS.functional hρ' hρ₁₀] at hfρ₁
  -- the records: `O₁` and `ls₁` re-read inside `O₀` and `ls₀`
  have hTW := hR.1
  have hTI := hTW.inv
  obtain ⟨O₁₀, hO₁₀, hO₁₀in⟩ := forall₂_sub hOr (zs := O₁) fun z hz => (hO z).mpr (Or.inr hz)
  obtain ⟨ls₁₀, hls₁₀, hls₁₀in⟩ := forall₂_sub hl (zs := ls₁) fun z hz => (hls z).mpr (Or.inr hz)
  have hr₀O : lendRec l ∈ O₀ := by
    obtain ⟨y, hy, hry⟩ := forall₂_mem_left hOr ((hO _).mpr (Or.inl rfl))
    rwa [RecRR.func hry (lendRec_rr l)] at hy
  have hr₀ps : lendRec l ∈ ps := (hS.1 _).mpr (Or.inl hr₀O)
  have hr₀O₁ : lendRec l ∉ O₁₀ := fun hm => by
    obtain ⟨x, hx, hxr⟩ := forall₂_mem_right hO₁₀ hm
    exact hO₁ (lendRec_rr_eq hxr ▸ hx)
  have hr₀ls₁ : ∀ y ∈ ls₁₀, y.1 ≠ lendRec l := fun y hy hyr => by
    obtain ⟨x, hx, hxy, -⟩ := forall₂_mem_right hls₁₀ hy
    rw [hyr] at hxy
    exact hls₁ x hx (lendRec_rr_eq hxy)
  have hO₀mem : ∀ x, x ∈ O₀ ↔ x = lendRec l ∨ x ∈ O₁₀ := by
    intro x
    refine ⟨fun hx => ?_, fun hx => hx.elim (fun e => e ▸ hr₀O) (hO₁₀in x)⟩
    obtain ⟨y, hy, hyx⟩ := forall₂_mem_right hOr hx
    rcases (hO y).mp hy with rfl | hy₁
    · exact Or.inl (RecRR.func hyx (lendRec_rr l))
    · obtain ⟨x', hx', hyx'⟩ := forall₂_mem_left hO₁₀ hy₁
      exact Or.inr (RecRR.func hyx hyx' ▸ hx')
  have hls₀mem : ∀ y ∈ ls₀, y.1 ≠ lendRec l → y ∈ ls₁₀ := by
    intro y hy hyr
    obtain ⟨x, hx, hxy, hxt⟩ := forall₂_mem_right hl hy
    rcases (hls x).mp hx with hx₁ | hx₁
    · exact absurd (RecRR.func hxy (hx₁ ▸ lendRec_rr l)) hyr
    · obtain ⟨y', hy', hxy', hxt'⟩ := forall₂_mem_left hls₁₀ hx₁
      have : y' = y := Prod.ext (RecRR.func hxy' hxy) (hxt'.trans hxt.symm)
      exact this ▸ hy'
  have hpsF : lendRec l ∉ psF := fun hm => hS.2 _ hr₀O _ hm rfl
  have hps₁ : ∀ p, p ∈ O₁₀ ++ psF ↔ p ∈ ps ∧ p ≠ lendRec l := by
    intro p
    rw [List.mem_append, hS.1 p, hO₀mem p]
    constructor
    · rintro (h | h)
      · exact ⟨Or.inl (Or.inr h), fun e => hr₀O₁ (e ▸ h)⟩
      · exact ⟨Or.inr h, fun e => hpsF (e ▸ h)⟩
    · rintro ⟨(h | h) | h, hne⟩
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h
  have hrs₁ : ∀ d, d ∈ rsOfT ls₁₀ ↔ ∃ p ∈ O₁₀ ++ psF, DescRT p d := by
    intro d
    simp only [rsOfT, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hd⟩ := (hTI.2.2.2.2.2.2.1 y.1).mp
        (List.mem_map.mpr ⟨y, hls₁₀in y hy, rfl⟩)
      refine ⟨p, (hps₁ p).mpr ⟨hp, fun e => ?_⟩, hd⟩
      subst e
      exact hr₀ls₁ y hy (descRT_lendRec hd)
    · rintro ⟨p, hp, hd⟩
      obtain ⟨hpps, hpne⟩ := (hps₁ p).mp hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ((hTI.2.2.2.2.2.2.1 d).mpr ⟨p, hpps, hd⟩)
      refine ⟨y, hls₀mem y hy fun e => ?_, rfl⟩
      rw [e] at hd
      obtain ⟨q, hq⟩ := hd
      cases hq with
      | nil => exact hpne rfl
      | cons hs t =>
          have hprs : p ∈ rsOfT ls₀ := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hpps, [], .nil p⟩
          exact not_desc_proper hTW hr₀ps hprs ⟨_, List.cons_ne_nil _ _, .cons hs t⟩
  have hTout : TWNT w₀.K w₀.Θ w₀.tc fρ₁ (O₁₀ ++ psF) (rsOfT ls₁₀) :=
    TWNT.immEnd (lendRec l) (s := TSet.single α) (hs := emptyT_inStratum _) hTW hr₀ps
      (ResUT.CompS.comm hYf) (ResUT.compS_empty_right _) (ResUT.CompS.comm hY₁) hv₁ hps₁ hrs₁
  -- the frame lifetimes: the aliasable walk loses `ℓ`
  have hag : ∀ a₁, AgWT fρ₁ a₁ → ∃ a, AgWT fρ a ∧ a₁.get l = none ∧
      ∀ m, m ≠ l → a₁.get m = a.get m := by
    intro a₁ ha₁
    have haY : AgWT Y a₁ := alloc_agT hY₁ ha₁
    obtain ⟨a, ha⟩ := agW_of_valid hvf
    obtain ⟨aY, haY', haYl, -, hm⟩ := ag_compS_view hYf hσ hσl ha
    obtain rfl := AgWT.functional haY' haY
    exact ⟨a, ha, haYl, fun m hm' => (hm m hm').symm⟩
  have htg : TaggedT w₀.K fρ₁ (O₁₀ ++ psF) ls₁₀ := by
    intro x hx
    obtain ⟨p, hp, hd, hf₁, hf₂⟩ := hR.2 x (hls₁₀in x hx)
    have hpne : p ≠ lendRec l := fun e => hr₀ls₁ x hx (descRT_lendRec (e ▸ hd))
    refine ⟨p, (hps₁ p).mpr ⟨hp, hpne⟩, hd, fun a₁ ha₁ ζ s eζ hs y hy => ?_,
      fun a₁ ha₁ m hm ψ s eψ hs y hy => ?_⟩
    · obtain ⟨a, ha, hl₁, hm⟩ := hag a₁ ha₁
      have hpl : p.le ≠ l := fun e => by rw [e, hl₁] at eζ; cases eζ
      exact hf₁ a ha ζ s (by rw [← hm _ hpl]; exact eζ) hs y hy
    · obtain ⟨a, ha, hl₁, hm'⟩ := hag a₁ ha₁
      have hml : m ≠ l := fun e => by rw [e, hl₁] at eψ; cases eψ
      exact hf₂ a ha m hm ψ s (by rw [← hm' m hml]; exact eψ) hs y hy
  -- the run's part, flattened, and the update masked at `ℓ`
  have hvρ₀ : ResUT.Valid ρ₀ := (ResUT.Valid.split hc hvf).2
  have hvZ₀ : ResUT.Valid (ρ₀.del l) := (ResUT.Valid.split hρ₀ hvρ₀).1
  obtain ⟨σZ, hσZ⟩ := hvZ₀
  have hσZl : σZ.get l = none := hZ₀ σZ hσZ l rfl
  obtain ⟨σ₀, hσ₀, hσZ₀⟩ := flat_compS_view hρ₀ hσZ hσZl
  obtain ⟨σ₁', hσZ₁⟩ := (ResUT.compS_defined_iff σZ (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT hσZl)
  have hσ₁' : ResUT.Flat ρ₁₀ σ₁' := (flat_compS_ownT hρ₁₀).mpr ⟨σZ, hσZ, hσZ₁⟩
  have hcovY : CovR (sem w₀.Θ) w₀.K Y := CovR.of_compS_left hYf hI.1
  have hcovZ : CovR (sem w₀.Θ) w₀.K (ρ₀.del l) :=
    CovR.of_compS_left (ResUT.CompS.comm hY) hcovY
  obtain ⟨τa, τb, ha, hb, hx⟩ :=
    UpdX.of_rr (Θ := sem w₀.Θ) (WCactus.Ext.refl _) (recMask O₀) ⟨σZ, hσZ⟩ (RR.refl hcovZ)
  obtain rfl := ResUT.Flat.functional hσZ ha
  obtain rfl := ResUT.Flat.functional hσZ hb
  have hlm : recMask O₀ l := ⟨lendRec l, hr₀O, Or.inl rfl⟩
  have hmask : ∀ k, k ≠ l → recMask O₁₀ k = recMask O₀ k := fun k hk => by
    apply propext
    simp only [recMask]
    constructor
    · rintro ⟨p, hp, hpk⟩; exact ⟨p, hO₁₀in p hp, hpk⟩
    · rintro ⟨p, hp, hpk⟩
      rcases (hO₀mem p).mp hp with rfl | hp
      · rcases hpk with hpk | hpk
        · exact absurd hpk hk
        · exact absurd hpk exDom_empty
      · exact ⟨p, hp, hpk⟩
  have hupd : UpdX (sem w₀.Θ) (recMask O₀) (recMask O₁₀) ρ₀ ρ₁₀ := by
    refine ⟨σ₀, σ₁', hσ₀, hσ₁', fun k => ?_⟩
    by_cases hk : k = l
    · subst hk
      refine ⟨fun _ _ _ hE => absurd hlm hE, fun ψ' e hk' _ => ?_⟩
      rw [ResUT.Comp.get_of_left_none hσZ₁ hσZl, ResUT.single_get_self] at e
      cases e; exact absurd rfl hk'
    · rw [hmask k hk, ResUT.Comp.get_of_right_none hσZ₀ (ResUT.single_get_ne _ hk),
        ResUT.Comp.get_of_right_none hσZ₁ (ResUT.single_get_ne _ hk)]
      exact hx k
  have hnone : NoneAt (MaskDiff (recMask O₀) (recMask O₁₀)) ρf := by
    intro τf hτf x hx
    by_cases hxl : x = l
    · subst hxl; exact hF w₀ ρf hFρ τf hτf x rfl
    · unfold MaskDiff at hx
      rw [hmask x hxl] at hx
      tauto
  refine ⟨ρ₁₀, fρ₁, ls₁₀, O₁₀, O₁₀ ++ psF,
    ⟨hE.1, fun x hx => (AgreeOn.of_compS_left hρ hE.2) x (holdsMut_of_compS_own hρ₁ hx)⟩,
    hr₁, hls₁₀, hO₁₀, ⟨hfρ₁.1, fρ₁, hfρ₁, hv₁⟩, hfρ₁,
    ⟨fun p => by rw [List.mem_append], fun p hp q hq => hS.2 p (hO₁₀in p hp) q hq⟩,
    ⟨hTout, htg⟩, ⟨covR_compS_own hY₁ hcovY, ?_⟩, hupd, hnone⟩
  obtain ⟨τ', hτ', hval⟩ := hI.2
  obtain rfl := ResUT.Flat.functional hτ hτ'
  refine ⟨τ₁, hτ₁, fun x => ?_⟩
  rw [hval x]
  by_cases hx : x = l
  · subst hx
    rw [ResUT.Comp.get_of_left_none hστ hσl, ResUT.Comp.get_of_left_none hστ₁ hσl, viewRes,
      ResUT.single_get_self, ResUT.single_get_self]
    rfl
  · rw [ResUT.Comp.get_of_right_none hστ (ResUT.single_get_ne _ hx),
      ResUT.Comp.get_of_right_none hστ₁ (ResUT.single_get_ne _ hx)]

end BoCa.Fig16.Tree.Wp

end
