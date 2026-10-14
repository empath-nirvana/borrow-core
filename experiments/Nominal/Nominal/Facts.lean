import Nominal.Relation

/-!
# Nominal — facts about small resources

Composition with `∅` and of two cells at distinct locations, the walks of a resource with one
`mut` cell, and validity of a borrow of a borrow; separating conjunction with `⌜−⌝`; the two
readings of `[α]P` on a chain. Used by `Package.lean` and `Witnesses.lean` to build concrete
configurations and to check that they are valid.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-! ### Composition with `∅` and of two cells -/

theorem comp_empty_left (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop)
    (ρ : ResU L) : Comp R C PMap.empty ρ ρ := by
  refine ⟨fun l ψ₁ ψ₂ e _ => absurd e (by simp), fun l => ?_⟩
  show OptComp C none (ρ.get l) (ρ.get l)
  cases ρ.get l <;> rfl

theorem comp_empty_right (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop)
    (ρ : ResU L) : Comp R C ρ PMap.empty ρ := by
  refine ⟨fun l ψ₁ ψ₂ _ e => absurd e (by simp), fun l => ?_⟩
  show OptComp C (ρ.get l) none (ρ.get l)
  cases ρ.get l <;> rfl

theorem comp_empty_left_eq {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    {ρ σ : ResU L} (h : Comp R C PMap.empty ρ σ) : σ = ρ := by
  refine PMap.ext fun l => ?_
  have := h.2 l
  change OptComp C none (ρ.get l) (σ.get l) at this
  cases e : ρ.get l <;> rw [e] at this <;> exact this

theorem comp_empty_right_eq {R : CellU L → CellU L → Prop}
    {C : CellU L → CellU L → CellU L → Prop} {ρ σ : ResU L} (h : Comp R C ρ PMap.empty σ) :
    σ = ρ := by
  refine PMap.ext fun l => ?_
  have := h.2 l
  change OptComp C (ρ.get l) none (σ.get l) at this
  cases e : ρ.get l <;> rw [e] at this <;> exact this

/-- `ℓ ↦ ψ, ℓ′ ↦ ψ′`. -/
def ResU.pair (l : Loc) (ψ : CellU L) (l' : Loc) (ψ' : CellU L) : ResU L where
  get := fun k => if k = l then some ψ else if k = l' then some ψ' else none
  finite := by
    refine ⟨[l, l'], fun k h => ?_⟩
    by_cases e : k = l
    · simp [e]
    · by_cases e' : k = l'
      · simp [e']
      · simp [e, e'] at h

theorem ResU.single_get_ne {l l' : Loc} (ψ : CellU L) (h : l' ≠ l) :
    (ResU.single l ψ).get l' = none := by
  rw [ResU.single_get, if_neg h]

theorem ResU.pair_get_left (l : Loc) (ψ : CellU L) (l' : Loc) (ψ' : CellU L) :
    (ResU.pair l ψ l' ψ').get l = some ψ := if_pos rfl

theorem ResU.pair_get_right {l l' : Loc} (ψ ψ' : CellU L) (h : l' ≠ l) :
    (ResU.pair l ψ l' ψ').get l' = some ψ' := by
  show (if l' = l then some ψ else if l' = l' then some ψ' else none) = some ψ'
  rw [if_neg h, if_pos rfl]

theorem ResU.pair_get_ne {l l' k : Loc} (ψ ψ' : CellU L) (h₁ : k ≠ l) (h₂ : k ≠ l') :
    (ResU.pair l ψ l' ψ').get k = none := by
  show (if k = l then some ψ else if k = l' then some ψ' else none) = none
  rw [if_neg h₁, if_neg h₂]

theorem comp_single_single (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop)
    {l l' : Loc} (hl : l ≠ l') (ψ ψ' : CellU L) :
    Comp R C (ResU.single l ψ) (ResU.single l' ψ') (ResU.pair l ψ l' ψ') := by
  refine ⟨fun k ψ₁ ψ₂ e₁ e₂ => ?_, fun k => ?_⟩
  · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₁
    obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₂
    exact absurd rfl hl
  · by_cases e : k = l
    · subst e
      rw [ResU.single_get_self, ResU.single_get_ne ψ' hl, ResU.pair_get_left]
      rfl
    · by_cases e' : k = l'
      · subst e'
        rw [ResU.single_get_ne ψ e, ResU.single_get_self, ResU.pair_get_right ψ ψ' e]
        rfl
      · rw [ResU.single_get_ne ψ e, ResU.single_get_ne ψ' e', ResU.pair_get_ne ψ ψ' e e']
        rfl

theorem CellU.CompatS.symm {ψ₁ ψ₂ : CellU L} (h : CellU.CompatS ψ₁ ψ₂) :
    CellU.CompatS ψ₂ ψ₁ :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

theorem CellU.CompS.symm {ψ₁ ψ₂ ψ : CellU L} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS ψ₂ ψ₁ ψ := by
  obtain ⟨hc, hk, he, hw, hl⟩ := h
  exact ⟨hc.symm, hk, he.trans hc.2.2.1, hw.trans hc.2.2.2, hl.trans (Finset.union_comm _ _)⟩

/-- `●` is commutative. -/
theorem ResU.CompS.symm {ρ₁ ρ₂ ρ : ResU L} (h : ResU.CompS ρ₁ ρ₂ ρ) : ResU.CompS ρ₂ ρ₁ ρ := by
  refine ⟨fun l ψ₂ ψ₁ e₂ e₁ => (h.1 l ψ₁ ψ₂ e₁ e₂).symm, fun l => ?_⟩
  have hl := h.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at hl
  · exact hl
  · exact hl
  · exact hl
  · obtain ⟨ψ, hψ, hc⟩ := hl
    exact ⟨ψ, hψ, hc.symm⟩

theorem ResU.Hash.symm {ρ₁ ρ₂ : ResU L} (h : ρ₁.Hash ρ₂) : ρ₂.Hash ρ₁ := by
  obtain ⟨hc, ρ, hρ, hv⟩ := h
  exact ⟨fun l ψ₂ ψ₁ e₂ e₁ => (hc l ψ₁ ψ₂ e₁ e₂).symm, ρ, hρ.symm, hv⟩

/-! ### Restriction and sites -/

theorem restrict_empty (k : Kind) : ResU.restrict (PMap.empty : ResU L) k = PMap.empty :=
  PMap.ext fun _ => rfl

theorem restrict_single_of (l : Loc) (ψ : CellU L) (k : Kind) (h : ψ.kind = k) :
    (ResU.single l ψ).restrict k = ResU.single l ψ := by
  refine PMap.ext fun l' => ?_
  show ((ResU.single l ψ).get l').bind _ = (ResU.single l ψ).get l'
  rw [ResU.single_get]
  split_ifs <;> simp [h]

theorem restrict_single_of_ne (l : Loc) (ψ : CellU L) (k : Kind) (h : ψ.kind ≠ k) :
    (ResU.single l ψ).restrict k = PMap.empty := by
  refine PMap.ext fun l' => ?_
  show ((ResU.single l ψ).get l').bind _ = none
  rw [ResU.single_get]
  split_ifs <;> simp [h]

theorem sites_empty (k : Kind) : ResU.Sites (PMap.empty : ResU L) k [] :=
  ⟨List.nodup_nil, fun l => ⟨fun h => (by cases h), fun ⟨_, e, _⟩ => absurd e (by simp)⟩⟩

theorem sites_single (l : Loc) (ψ : CellU L) : ResU.Sites (ResU.single l ψ) ψ.kind [l] := by
  refine ⟨List.nodup_singleton l, fun l' => ⟨fun h => ?_, fun ⟨ψ', e, _⟩ => ?_⟩⟩
  · rw [List.mem_singleton.mp h]
    exact ⟨ψ, ResU.single_get_self _ _, rfl⟩
  · exact List.mem_singleton.mpr (ResU.single_get_eq_some e).1

theorem sites_single_ne (l : Loc) (ψ : CellU L) (k : Kind) (h : ψ.kind ≠ k) :
    ResU.Sites (ResU.single l ψ) k [] := by
  refine ⟨List.nodup_nil, fun l' => ⟨fun h' => (by cases h'), fun ⟨ψ', e, hk⟩ => ?_⟩⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact absurd hk h

/-! ### Walks -/

theorem exW_empty (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop) :
    ExW R C PMap.empty PMap.empty := by
  refine .mk (w := []) (nm := PMap.empty) (b := PMap.empty) (sites_empty _) .nil .nil ?_ ?_
  · rw [restrict_empty, restrict_empty]; exact comp_empty_left R C _
  · exact comp_empty_left R C _

theorem agW_empty : AgW (PMap.empty : ResU L) PMap.empty := by
  refine .mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty) (bi := PMap.empty)
    (sites_empty _) (sites_empty _) .nil .nil .nil .nil ?_ ?_
  · rw [restrict_empty]; exact comp_empty_left _ _ _
  · exact comp_empty_left _ _ _

/-- The exclusive walk of one `mut` cell: its witness's walk composed with it. -/
theorem exW_single_mut {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    {l : Loc} {ψ : CellU L} (hk : ψ.kind = .mut) {e₁ σ : ResU L} (h₁ : ExW R C ψ.wit e₁)
    (hσ : Comp R C (ResU.single l ψ) e₁ σ) : ExW R C (ResU.single l ψ) σ := by
  refine .mk (w := [(l, e₁)]) (nm := ResU.single l ψ) (b := e₁) ?_
    (.cons ψ (ResU.single_get_self _ _) hk h₁ .nil) (.cons .nil (comp_empty_right R C e₁)) ?_ hσ
  · have := sites_single l ψ
    rwa [hk] at this
  · rw [restrict_single_of_ne l ψ _ (by rw [hk]; decide), restrict_single_of l ψ _ hk]
    exact comp_empty_left R C _

/-- The aliasable walk of one `mut` cell: its witness's. -/
theorem agW_single_mut {l : Loc} {ψ : CellU L} (hk : ψ.kind = .mut) {a₁ : ResU L}
    (h₁ : AgW ψ.wit a₁) : AgW (ResU.single l ψ) a₁ := by
  refine .mk (wm := [(l, a₁)]) (wi := []) (a := a₁) (bm := a₁) (bi := PMap.empty) ?_
    (sites_single_ne l ψ _ (by rw [hk]; decide)) (.cons ψ (ResU.single_get_self _ _) hk h₁ .nil)
    .nil (.cons .nil (comp_empty_right _ _ a₁)) .nil ?_ (comp_empty_right _ _ a₁)
  · have := sites_single l ψ
    rwa [hk] at this
  · rw [restrict_single_of_ne l ψ _ (by rw [hk]; decide)]
    exact comp_empty_left _ _ _

theorem flat_empty : ResU.Flat (PMap.empty : ResU L) PMap.empty :=
  ⟨PMap.empty, PMap.empty, exW_empty _ _, agW_empty, comp_empty_left _ _ _⟩

theorem valid_empty : ResU.Valid (PMap.empty : ResU L) := ⟨_, flat_empty⟩

/-- A `mut` cell whose witness is `∅` is valid on its own. -/
theorem valid_single_mut_empty {l : Loc} {ψ : CellU L} (hk : ψ.kind = .mut)
    (hw : ψ.wit = PMap.empty) : (ResU.single l ψ).Valid := by
  refine ⟨ResU.single l ψ, ResU.single l ψ, PMap.empty, ?_, ?_, comp_empty_right _ _ _⟩
  · refine exW_single_mut hk (e₁ := PMap.empty) (by rw [hw]; exact exW_empty _ _) ?_
    exact comp_empty_right _ _ _
  · exact agW_single_mut hk (by rw [hw]; exact agW_empty)

/-- **A borrow of a borrow is valid**: `ℓ ↦ mut(_, _, ℓ′ ↦ ψ′, _)` with `ψ′` a `mut` cell whose
witness is `∅`, `ℓ ≠ ℓ′`. -/
theorem valid_mut_mut {l l' : Loc} (hl : l ≠ l') {ψ ψ' : CellU L} (hk : ψ.kind = .mut)
    (hk' : ψ'.kind = .mut) (hw : ψ.wit = ResU.single l' ψ') (hw' : ψ'.wit = PMap.empty) :
    (ResU.single l ψ).Valid := by
  have hexI : ExS (ResU.single l' ψ') (ResU.single l' ψ') :=
    exW_single_mut hk' (e₁ := PMap.empty) (by rw [hw']; exact exW_empty _ _)
      (comp_empty_right _ _ _)
  have hagI : AgW (ResU.single l' ψ') PMap.empty :=
    agW_single_mut hk' (by rw [hw']; exact agW_empty)
  refine ⟨ResU.pair l ψ l' ψ', ResU.pair l ψ l' ψ', PMap.empty, ?_, ?_, comp_empty_right _ _ _⟩
  · exact exW_single_mut hk (by rw [hw]; exact hexI) (comp_single_single _ _ hl ψ ψ')
  · exact agW_single_mut hk (by rw [hw]; exact hagI)

/-- The exclusive walk of one `imm` cell is `∅`. -/
theorem exW_single_imm (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop)
    {l : Loc} {ψ : CellU L} (hk : ψ.kind = .imm) : ExW R C (ResU.single l ψ) PMap.empty := by
  refine .mk (w := []) (nm := PMap.empty) (b := PMap.empty)
    (sites_single_ne l ψ _ (by rw [hk]; decide)) .nil .nil ?_ (comp_empty_left R C _)
  rw [restrict_single_of_ne l ψ _ (by rw [hk]; decide),
    restrict_single_of_ne l ψ _ (by rw [hk]; decide)]
  exact comp_empty_left R C _

/-- The aliasable walk of one `imm` cell: the cell, beside its witness's walks. -/
theorem agW_single_imm {l : Loc} {ψ : CellU L} (hk : ψ.kind = .imm) {e a p σ : ResU L}
    (hex : ExR ψ.wit e) (hag : AgW ψ.wit a) (hp : ResU.CompR e a p)
    (hσ : ResU.CompR (ResU.single l ψ) p σ) : AgW (ResU.single l ψ) σ := by
  refine .mk (wm := []) (wi := [(l, p)]) (a := ResU.single l ψ) (bm := PMap.empty) (bi := p)
    (sites_single_ne l ψ _ (by rw [hk]; decide)) ?_ .nil
    (.cons ψ (ResU.single_get_self _ _) hk e a hex hag hp .nil) .nil
    (.cons .nil (comp_empty_right _ _ p)) ?_ hσ
  · have := sites_single l ψ
    rwa [hk] at this
  · rw [restrict_single_of l ψ _ hk]
    exact comp_empty_right _ _ _

/-- **An `imm` borrow of an `imm` borrow is valid**: `ℓ ↦ imm(_, _, ℓ′ ↦ ψ′)` with `ψ′` an `imm`
cell whose witness is `∅`, `ℓ ≠ ℓ′`. -/
theorem valid_imm_imm {l l' : Loc} (hl : l ≠ l') {ψ ψ' : CellU L} (hk : ψ.kind = .imm)
    (hk' : ψ'.kind = .imm) (hw : ψ.wit = ResU.single l' ψ') (hw' : ψ'.wit = PMap.empty) :
    (ResU.single l ψ).Valid := by
  have hagI : AgW (ResU.single l' ψ') (ResU.single l' ψ') :=
    agW_single_imm hk' (e := PMap.empty) (a := PMap.empty) (p := PMap.empty)
      (by rw [hw']; exact exW_empty _ _) (by rw [hw']; exact agW_empty)
      (comp_empty_left _ _ _) (comp_empty_right _ _ _)
  refine ⟨ResU.pair l ψ l' ψ', PMap.empty, ResU.pair l ψ l' ψ', exW_single_imm _ _ hk, ?_,
    comp_empty_left _ _ _⟩
  exact agW_single_imm hk (e := PMap.empty) (a := ResU.single l' ψ') (p := ResU.single l' ψ')
    (by rw [hw]; exact exW_single_imm _ _ hk') (by rw [hw]; exact hagI)
    (comp_empty_left _ _ _) (comp_single_single _ _ hl ψ ψ')

theorem hash_empty_of_valid {ρ : ResU L} (h : ρ.Valid) : ResU.Hash (PMap.empty : ResU L) ρ :=
  ⟨fun _ _ _ e _ => absurd e (by simp), ρ, comp_empty_left _ _ _, h⟩

/-! ### Propositions -/

theorem sepN_pure_iff {p : Prop} {Q : WPropN L} {ρ : ResU L} :
    sepN (pureN p) Q ρ ↔ p ∧ Q ρ := by
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, hp⟩, hQ⟩
    rw [comp_empty_left_eq hc]
    exact ⟨hp, hQ⟩
  · rintro ⟨hp, hQ⟩
    exact ⟨PMap.empty, ρ, comp_empty_left _ _ _, ⟨rfl, hp⟩, hQ⟩

theorem wandN_pure_iff {p : Prop} {Q : WPropN L} {ρ : ResU L} :
    wandN (pureN p) Q ρ ↔ (p → Q ρ) := by
  constructor
  · intro h hp
    exact h PMap.empty ρ ⟨rfl, hp⟩ (comp_empty_right _ _ _)
  · rintro h ρ₁ ρ₂ ⟨rfl, hp⟩ hc
    rw [comp_empty_right_eq hc]
    exact h hp

/-- Every cell of `ρ` is `own`. -/
def OwnOnly (ρ : ResU L) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind = .own

theorem CellU.inStratum_of_own {ψ : CellU L} (h : ψ.kind = .own) (S : Finset L) :
    ψ.InStratum S := by
  cases ψ with
  | own v => trivial
  | imm i => cases h
  | «mut» m => cases h

/-- **An owned resource is in every stratum.** -/
theorem OwnOnly.inStratum {ρ : ResU L} (h : OwnOnly ρ) (S : Finset L) : ρ.InStratum S :=
  fun l ψ e => CellU.inStratum_of_own (h l ψ e) S

/-- An owned resource is fixed by every automorphism. -/
theorem OwnOnly.relRU_eq {ρ : ResU L} (h : OwnOnly ρ) (π : L ≃o L) : relRU π ρ = ρ := by
  refine PMap.ext fun l => ?_
  rw [relRU_get]
  cases e : ρ.get l with
  | none => rfl
  | some ψ =>
      have hk := h l ψ e
      cases ψ with
      | own v => rfl
      | imm i => cases hk
      | «mut» m => cases hk

/-- A `mut` cell whose lifetime, witness and stored predicate are fixed is fixed. -/
theorem relU_mutOf_fix (π : L ≃o L) {b : L} {u : Val} {σ : ResU L} {h : σ.InStratum {b}}
    {P : Val → ResU L → Prop} {hw : P u σ} (hb : π b = b) (hσ : relRU π σ = σ)
    (hP : img π P = P) : relU π (CellU.mutOf b u σ h P hw) = CellU.mutOf b u σ h P hw := by
  rw [relU_mutOf]
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · simp only [CellU.wit_mutOf]; exact hσ
  · simp only [CellU.lts_mutOf]; rw [hb]
  · rw [CellU.pu_mutOf, CellU.pu_mutOf, hP, hb]

/-! ### The two readings of `[α]P` -/

/-- On a chain the two readings agree. -/
theorem survives_iff_inStratum_of_chain {α : L} (hchain : ∀ a b : L, a ≤ b ∨ b ≤ a)
    (ρ : ResU L) : ρ.Survives α ↔ ρ.InStratum {α} :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    CellU.survives_iff_inStratum (fun m _ => hchain m α)

theorem boxE_eq_boxS_of_chain (hchain : ∀ a b : L, a ≤ b ∨ b ≤ a) (α : L) (P : WPropN L) :
    boxE α P = boxS α P := by
  funext ρ
  exact propext (and_congr_right fun _ => survives_iff_inStratum_of_chain hchain ρ)

end Nominal

end
