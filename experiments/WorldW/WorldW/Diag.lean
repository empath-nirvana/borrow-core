import WorldW.Between

/-!
# WorldW — the frozen-list diagnostic (DESIGN §3.4, checkpoint 3)

**World: the W-draft, at Core's `ptoMutS`.** A diagnostic; it draws no conclusion alone. Its
distinguishing input need not arise, so a refutation of it measures our `ptoMutS`'s predicate
equality, not OQ-9 (a).

* `mutViewSurvives_stable`: at the list-stable payload type `1 ⊕ 1` the view survives an older
  frame's close.
* `not_mutViewSurvives_reads`: at the list-reading payload type `1 ⊕ Imm 'x₁ 1` it does not. The
  stored predicate was frozen at a list holding the older frame's record, and `ptoMutS` asks it to
  *equal* the payload relation at the shorter list; `CohE` makes the two differ at a view of the
  older frame's place. The input is not built from a `TW` history.

The input is not built from a `TW` history. So this predicts nothing about where the
list-reading between-lenders probes stop, and does not say whether a failure there belongs to our
`ptoMutS` or to (a).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- After an older 6.64 frame closes, a younger `Mut` view of another place is still the view
`ptoMutS` reads at the shorter list. -/
def MutViewSurvivesOlderClose (T₃ : LifeVar → VTy) : Prop :=
  ∀ (ℓ₃ : BoCa.Loc) (α₃ : Life) (x₁ : LifeVar) (δ : LSub) (p₂ : FrameRec) (α₂ : Life)
    (ls ls' : List SRec) (ρ : WRes),
    (∀ x, x ∈ ls' ↔ (x ∈ ls ∧ ¬ LinOf (.imm (p₂, α₂)) x)) →
    ptoMutS ℓ₃ α₃ ls (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ →
    ptoMutS ℓ₃ α₃ ls' (fun ls₀ => vC true (T₃ x₁) ls₀ δ) ρ

/-- `𝒱⟦1 ⊕ 1⟧` reads no record list. -/
theorem vC_T3Stable_listFree (x₁ : LifeVar) (δ : LSub) (ls ls' : List SRec) :
    vC true (T3Stable x₁) ls δ = vC true (T3Stable x₁) ls' δ := rfl

/-- **At the list-stable payload type the view survives an older frame's close.** -/
theorem mutViewSurvives_stable : MutViewSurvivesOlderClose T3Stable := by
  intro ℓ₃ α₃ x₁ δ p₂ α₂ ls ls' ρ _ h
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, -, hunif⟩ := h
  refine ⟨b, u, σ, hσ, Q, hw, ls'.filter (fun x => decide (b < x.2)), hab, hρ, ?_, fun x => ?_,
    hunif⟩
  · rw [hQ]; exact vC_T3Stable_listFree x₁ δ ls₀ _
  · simp [List.mem_filter]

section reads

/-- The distinguishing input: `x₁ ↦ 1`, the older frame's record at `ℓ₂ = 0` tagged `2`, the
younger `Mut` view at `ℓ₃ = 1` and lifetime `5` (so `5 ⊏ 2 ⊏ 1`). -/
abbrev dδ : LSub := ⟨[(0, 1)]⟩
abbrev dα₁ : Life := OrderDual.toDual 1
abbrev dα₂ : Life := OrderDual.toDual 2
abbrev dα₃ : Life := OrderDual.toDual 5
def dp₂ : FrameRec := ⟨0, Val.unit, PMap.empty, .unit, dδ⟩
def dls : List SRec := [(dp₂, dα₂)]
abbrev dP : List SRec → Val → WProp := fun ls₀ => vC true (T3Reads 0) ls₀ dδ

/-- Every resource the payload relation holds of lies in `Res_5`: its only borrow is an `imm`
cell at a lifetime `⊒ 1`. -/
theorem dP_support (ls₀ : List SRec) (v : Val) (ρ : WRes) (h : dP ls₀ v ρ) :
    ρ.InStratum dα₃ := by
  rcases h with ⟨v₁, h⟩ | ⟨v₂, h⟩
  · obtain ⟨-, hu⟩ := pure_sep_iff.mp h
    obtain ⟨hρ, -⟩ := hu
    subst hρ; exact ResU.inStratum_empty _
  · obtain ⟨-, α, hα, ℓ, h⟩ := pure_sep_iff.mp h
    obtain ⟨-, s, u, σ, hσ, ls₁, hρ, -, hle, -⟩ := pure_sep_iff.mp h
    have hα' : α = dα₁ := Option.some.inj (hα.symm.trans rfl)
    subst hρ hα'
    intro k ψ e
    by_cases hk : k = ℓ
    · subst hk; rw [ResU.single_get_self] at e; cases Option.some.inj e
      exact lt_of_lt_of_le (show dα₃ < dα₁ by decide) hle
    · rw [single_get_none _ hk] at e; exact absurd e (by simp)

/-- The stored predicate, stratified at `5`. -/
def dQ : Val → SPropS BoCa.Loc Val dα₃ := fun v => SPropU.toS dα₃ (dP dls v)

theorem dQ_ofS : ofS dQ = dP dls :=
  funext fun _ => funext fun _ => propext ((SPropU.toU_toS_iff _ _ _).trans
    ⟨fun h => h.1, fun h => ⟨h, dP_support _ _ _ h⟩⟩)

theorem dQ_unit : dQ (Val.inj₁ Val.unit) ⟨PMap.empty, ResU.inStratum_empty dα₃⟩ :=
  Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-- The view of the older frame's place, at `1`. -/
def dView : WRes :=
  ResU.single 0 (CellU.immOf (LSet.singleton dα₁) Val.unit PMap.empty (ResU.inStratum_empty _))

/-- At the list holding the older record, the payload relation holds of `inj₂ ℓ₂` and its view:
`CohE` finds the record. -/
theorem dP_in : dP dls (Val.inj₂ (Val.loc 0)) dView := by
  refine Or.inr ⟨Val.loc 0, pure_sep_mk rfl ⟨dα₁, rfl, 0, pure_sep_mk ⟨rfl, ?_⟩ ?_⟩⟩
  · exact ⟨.unit, dδ, trivial, Or.inl ⟨dp₂, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩
  · refine ⟨LSet.singleton dα₁, Val.unit, PMap.empty, ResU.inStratum_empty _, [], rfl,
      ⟨rfl, rfl⟩, le_refl _, fun x => ?_⟩
    simp only [dls, List.mem_singleton, List.not_mem_nil, false_iff, not_and]
    rintro rfl
    show ¬ (dα₁ < dα₂)
    decide

/-- At the shorter list it does not: `CohE` finds no record. -/
theorem dP_out : ¬ dP [] (Val.inj₂ (Val.loc 0)) dView := by
  rintro (⟨v₁, h⟩ | ⟨v₂, h⟩)
  · obtain ⟨hv, -⟩ := pure_sep_iff.mp h
    exact absurd (congrArg Subtype.val hv) (by simp [Val.inj₁, Val.inj₂])
  · obtain ⟨-, α, -, ℓ, h⟩ := pure_sep_iff.mp h
    obtain ⟨⟨-, S₀, δ₀, -, hcoh⟩, -⟩ := pure_sep_iff.mp h
    rcases hcoh with ⟨r, hr, -⟩ | ⟨r, hr, -⟩ <;> exact absurd hr List.not_mem_nil

/-- **At the list-reading payload type the view does not survive an older frame's close.** -/
theorem not_mutViewSurvives_reads : ¬ MutViewSurvivesOlderClose T3Reads := by
  intro h
  let ρ : WRes := ResU.single 1 (CellU.mutOf dα₃ (Val.inj₁ Val.unit) PMap.empty
    (ResU.inStratum_empty dα₃) dQ dQ_unit)
  have hpt : ptoMutS 1 dα₃ dls (fun ls₀ => vC true (T3Reads 0) ls₀ dδ) ρ := by
    refine ⟨dα₃, _, _, _, dQ, dQ_unit, dls, le_refl _, rfl, dQ_ofS, fun x => ?_,
      fun ls' u' σ' hp => dP_support ls' u' σ' hp⟩
    simp only [dls, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, show dα₃ < dα₂ by decide⟩
    · exact fun h => h.1
  have hls' : ∀ x, x ∈ ([] : List SRec) ↔ (x ∈ dls ∧ ¬ LinOf (.imm (dp₂, dα₂)) x) := by
    intro x
    simp only [List.not_mem_nil, false_iff, not_and, not_not, dls, List.mem_singleton]
    rintro rfl
    exact ⟨⟨[], LinPath.nil dp₂⟩, rfl⟩
  obtain ⟨b', u', σ', h', Q', hw', ls₀', -, hρ', hQ', hls₀', -⟩ :=
    h 1 dα₃ 0 dδ dp₂ dα₂ dls [] ρ hls' hpt
  have hnil : ls₀' = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun x hx => absurd ((hls₀' x).mp hx).1 List.not_mem_nil
  have hcell := congrArg (fun r : WRes => r.get 1) hρ'
  simp only [ρ, ResU.single_get_self, Option.some.injEq] at hcell
  obtain rfl : dα₃ = b' := CellU.mutOf_at hcell
  obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj hcell
  rw [hnil] at hQ'
  have hPP : dP dls = dP [] := dQ_ofS.symm.trans hQ'
  exact dP_out (hPP ▸ dP_in)

end reads

end WorldW

end
