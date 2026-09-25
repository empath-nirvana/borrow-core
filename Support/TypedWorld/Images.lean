import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.ClosingSentence
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Empty
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.UpdateFrame
import Support.Model.WalkSplitting
import Support.Model.Walks
import Support.TypedWorld.Records
import Support.TypedWorld.World

/-!
# Support — TypedWorld — Images

`[about ours]`.  The typed world's first layer: composition read cell by cell, walks through an escrow, the `immFrame` and `alloc` steps, roots and `Ref` chains, and typed reborrow images.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {R : CellU Loc Val → CellU Loc Val → Prop}

theorem comp_get_l {ρ₁ ρ₂ ρ : WRes} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ) (e₂ : ρ₂.get l = none) : ρ.get l = some ψ := by
  have := h.2 l; rw [e₁, e₂] at this; exact this

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem single_ne {l l' : Loc} (ψ : CellU Loc Val) (h : l' ≠ l) : (ResU.single l ψ).get l' = none :=
  ResU.single_get_ne ψ h

theorem flat_empty : ResU.Flat (PMap.empty : WRes) PMap.empty :=
  ⟨_, _, ExW.empty_of_all_imm (fun l ψ e => absurd e (by simp)), DeepReborrow.agW_empty,
    ResU.comp_empty_left _⟩

theorem comp_some {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : WRes} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellU Loc Val}
    (e : ρ₁.get l = some ψ) : ∃ ζ, ρ.get l = some ζ := by
  have := h.2 l
  rw [e] at this
  cases e2 : ρ₂.get l <;> rw [e2] at this
  · exact ⟨_, this⟩
  · obtain ⟨ζ, hz, -⟩ := this; exact ⟨ζ, hz⟩

/-- A non-`own` cell of an operand of `○` reaches the composite as a non-`own` cell over the
same witness. -/
theorem lift_view {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ₁ : CellU Loc Val}
    (e : a₁.get l = some ψ₁) (hk : ψ₁.kind ≠ Kind.own) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit := by
  have := h.2 l
  rw [e] at this
  cases e2 : a₂.get l <;> rw [e2] at this
  · exact ⟨_, this, hk, rfl⟩
  · obtain ⟨ψ, hψ, hC⟩ := this
    refine ⟨ψ, hψ, ?_⟩
    cases hC with
    | same => exact ⟨hk, rfl⟩
    | strict k =>
        have hc := CellU.compS_spec _ _ k
        exact ⟨by rw [CellU.CompS.kind hc]; exact fun c => Kind.noConfusion c,
          (CellU.CompS.wit hc).1⟩
    | mutMut => exact ⟨by simp, by simp⟩
    | mutOwn => exact ⟨hk, rfl⟩
    | ownMut => exact absurd (CellU.kind_ownOf _) hk
    | immOwn => exact ⟨hk, rfl⟩
    | ownImm => exact absurd (CellU.kind_ownOf _) hk
    | immMut => exact ⟨hk, rfl⟩
    | mutImm => exact ⟨by rw [CellU.kind_immOf]; exact fun c => Kind.noConfusion c,
        by rw [CellU.wit_immOf]; simp⟩

/-- A non-`own` cell of `ψ₁ ○ ψ₂` has the witness of a non-`own` operand. -/
theorem CellU.CompR.back_view {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind ≠ Kind.own) :
    (ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨ (ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  cases h with
  | same => exact Or.inl ⟨hk, rfl⟩
  | strict k =>
      have hc := CellU.compS_spec _ _ k
      exact Or.inl ⟨by rw [(CellU.CompatS.kinds k).1]; exact fun c => Kind.noConfusion c,
        (CellU.CompS.wit hc).1⟩
  | mutMut => exact Or.inl ⟨by simp, by simp⟩
  | mutOwn => exact Or.inl ⟨hk, rfl⟩
  | ownMut => exact Or.inr ⟨hk, rfl⟩
  | immOwn => exact Or.inl ⟨hk, rfl⟩
  | ownImm => exact Or.inr ⟨hk, rfl⟩
  | immMut => exact Or.inl ⟨hk, rfl⟩
  | mutImm => exact Or.inr ⟨hk, rfl⟩

/-- …and at the resource level. -/
theorem back_view {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ : CellU Loc Val}
    (e : a.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  rcases ResU.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk, rfl⟩
  · rw [e'] at e; cases e
    rcases CellU.CompR.back_view hC hk with ⟨k, w⟩ | ⟨k, w⟩
    · exact Or.inl ⟨_, e₁, k, w⟩
    · exact Or.inr ⟨_, e₂, k, w⟩

theorem back_some {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {a₁ a₂ a : WRes} (h : ResU.Comp R C a₁ a₂ a) {l : Loc} {ψ : CellU Loc Val}
    (e : a.get l = some ψ) : (∃ ψ₁, a₁.get l = some ψ₁) ∨ (∃ ψ₂, a₂.get l = some ψ₂) := by
  rcases ResU.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, -⟩ | ⟨ζ, -, e₂, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, -, -, -⟩
  · rw [e'] at e; cases e
  · exact Or.inl ⟨_, e₁⟩
  · exact Or.inr ⟨_, e₂⟩
  · exact Or.inl ⟨_, e₁⟩

/-- Forward lift of a non-`own` cell through the right operand. -/
theorem lift_view_r {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ₂ : CellU Loc Val}
    (e : a₂.get l = some ψ₂) (hk : ψ₂.kind ≠ Kind.own) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit :=
  lift_view (ResU.CompR.comm h) e hk

theorem comp_some_r {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : WRes} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellU Loc Val}
    (e : ρ₂.get l = some ψ) : ∃ ζ, ρ.get l = some ζ := by
  rcases ResU.Comp.get h l with ⟨-, e₂, -⟩ | ⟨ζ, -, e₂, -⟩ | ⟨ζ, -, -, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, -, -, e', -⟩
  · rw [e₂] at e; cases e
  · rw [e₂] at e; cases e
  · exact ⟨_, e'⟩
  · exact ⟨_, e'⟩

/-- At a valid resource, the exclusive and aliasable walks have disjoint domains:
`⦇ρ⦈ = ex(ρ)_● ● ag(ρ)` is strict, `●` relates `imm` cells only, and `ex(ρ)_●` has
none (`ExS.immFree`, `[TR]` 6.36). -/
theorem ex_ag_disjoint {W e a : WRes} (hv : ResU.Valid W) (he : ExS W e) (ha : AgW W a)
    {l : Loc} {ψ₁ ψ₂ : CellU Loc Val} (e₁ : e.get l = some ψ₁) (e₂ : a.get l = some ψ₂) :
    False := by
  obtain ⟨σ, e', a', he', ha', hc⟩ := hv
  rw [ExS.functional he' he] at hc
  rw [AgW.functional ha' ha] at hc
  rcases ResU.Comp.get hc l with ⟨e₁', -, -⟩ | ⟨ζ, -, e₂', -⟩ | ⟨ζ, e₁', -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁', -, -, hC⟩
  · rw [e₁'] at e₁; cases e₁
  · rw [e₂'] at e₂; cases e₂
  · rw [e₁'] at e₁; cases e₁
  · rw [e₁'] at e₁; cases e₁
    obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
    exact ExS.immFree he l _ e₁' (by rw [h₁]; rfl)

theorem lift_part {W σ₀ t aW et at' pt : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} (hle : W.get le = some (CellU.immOf s v σ₀ hs))
    (ht : ResU.Le t σ₀) (haW : AgW W aW) (het : ExR t et) (hat : AgW t at')
    (hpt : ResU.CompR et at' pt) {l : Loc} {ψ : CellU Loc Val} (e : pt.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ.wit := by
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨a₁, a₂, -, h₂, h12⟩ := (AgW.split (ResU.del_compS hle)).mp haW
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, hcp₀⟩ := AgW.single_imm_inv h₂
  have up : ∀ ψ', p₀.get l = some ψ' → ψ'.kind ≠ Kind.own →
      ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ'.wit := by
    intro ψ' e' k'
    obtain ⟨ψ₁, e₁, k₁, w₁⟩ := lift_view_r hcp₀ e' k'
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r h12 e₁ k₁
    exact ⟨ψ₂, e₂, k₂, w₂.trans w₁⟩
  rcases back_view hpt e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨x₁, x₂, hx₁, -, hx⟩ := (ExR.split_of_compS hτ).mp he₀
    rw [ExR.functional hx₁ het] at hx
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view hx e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view hp₀ e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := up ψ₃ e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩
  · obtain ⟨y₁, y₂, hy₁, -, hy⟩ := (AgW.split hτ).mp ha₀
    rw [AgW.functional hy₁ hat] at hy
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view hy e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hp₀ e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := up ψ₃ e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩

theorem reb_support {W W' c aW a' : WRes} (hW : ResU.CompS W c W') (haW : AgW W aW)
    (ha' : AgW W' a') {l : Loc} {ψ : CellU Loc Val} (e : aW.get l = some ψ) :
    ∃ ζ, a'.get l = some ζ := by
  obtain ⟨σw, σc, hw, -, hcomp⟩ := (AgW.split hW).mp ha'
  rw [AgW.functional hw haW] at hcomp
  exact comp_some hcomp e

/-- The walks of the three configurations of an `immFrame` step, named once.
`W = (ℓ ↦ own(v) ● R) ● Z`, `W' = ℓ ↦ imm({α}, v, R) ● Z`. -/
theorem frame_walks {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) (ha' : AgW W' a') :
    ∃ eW aW r z eR σc pc, ExS W eW ∧ AgW W aW ∧ AgW R r ∧ ResU.CompR r z aW ∧
      ExS R eR ∧ (∀ m ζ, eR.get m = some ζ → ∃ ζ', eW.get m = some ζ') ∧
      eW.get l = some (CellU.ownOf v) ∧
      ResU.CompR eR r pc ∧
      ResU.CompR (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) pc σc ∧
      ResU.CompR σc z a' := by
  obtain ⟨σ, eW, aW, heW, haW, -⟩ := hv
  obtain ⟨x, z, hx, hz, hxz⟩ := (AgW.split hW).mp haW
  obtain ⟨o, r, ho, hr, hor⟩ := (AgW.split hX).mp hx
  rw [AgW.functional ho (AgW.single_own l v)] at hor
  rw [ResU.CompR.functional hor (ResU.comp_empty_left r)] at hxz
  obtain ⟨σc, σz, hc, hz', hcz⟩ := (AgW.split hW').mp ha'
  rw [AgW.functional hz' hz] at hcz
  obtain ⟨ec, ac, pc, hec, hac, hpc, hcp⟩ := AgW.single_imm_inv hc
  rw [AgW.functional hac hr] at hpc
  obtain ⟨eX, eZ, heX, -, heXZ⟩ := (ExS.split hW).mp heW
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExS.split hX).mp heX
  rw [ExR.functional hec (ExS.toExR heR)] at hpc
  rw [ExS.functional heo (ExW.single_own l v)] at heoR
  refine ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hxz, heR,
    fun m ζ e => ?_, ?_, hpc, hcp, hcz⟩
  · obtain ⟨ζ₁, e₁⟩ := comp_some_r heoR e
    exact comp_some heXZ e₁
  · have e₁ := comp_get_l heoR (ResU.single_get_self l _) (by
      rcases ResU.Comp.get heoR l with ⟨e₁, -, -⟩ | ⟨ζ, -, e₂, -⟩ | ⟨ζ, e₁, -, -⟩ |
          ⟨ζ₁, ζ₂, ζ, e₁, e₂, -, hC⟩
      · rw [ResU.single_get_self] at e₁; cases e₁
      · exact e₂
      · rw [ResU.single_get_self] at e₁; cases e₁
      · rw [ResU.single_get_self] at e₁; cases e₁
        obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
        exact absurd h₁ CellU.ownOf_ne_immOf)
    have hne : (CellU.ownOf (Loc := Loc) v).kind ≠ Kind.imm := by simp
    rcases ResU.Comp.get heXZ l with ⟨e₃, -, -⟩ | ⟨ζ, e₃, -, e₄⟩ | ⟨ζ, e₃, -, -⟩ |
        ⟨ζ₁, ζ₂, ζ, e₃, -, -, hC⟩
    · rw [e₁] at e₃; cases e₃
    · rw [e₁] at e₃; cases e₃; exact e₄
    · rw [e₁] at e₃; cases e₃
    · rw [e₁] at e₃; cases e₃
      obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
      exact absurd h₁ CellU.ownOf_ne_immOf

/-- `immFrame` transfers every view at a supported location. -/
theorem frame_transfer {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) {m : Loc} (hsupp : ∀ aW, AgW W aW → ∃ ζ, aW.get m = some ζ)
    (ha' : AgW W' a') {ψ : CellU Loc Val} (e : a'.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ aW, AgW W aW ∧ ∃ ψ₀, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  obtain ⟨ζs, hζs⟩ := hsupp aW haW
  refine ⟨aW, haW, ?_⟩
  rcases back_view hcz e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · rcases back_view hcp e₁ k₁ with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
    · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₂
      exact (ex_ag_disjoint hv heW haW hl hζs).elim
    · rcases back_view hpc e₂ k₂ with ⟨ψ₃, e₃, -, -⟩ | ⟨ψ₃, e₃, k₃, w₃⟩
      · obtain ⟨ζ', e'⟩ := hup m ψ₃ e₃
        exact (ex_ag_disjoint hv heW haW e' hζs).elim
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hrz e₃ k₃
        exact ⟨ψ₄, e₄, k₄, w₁.trans (w₂.trans (w₃.trans w₄.symm))⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hrz e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₁.trans w₄.symm⟩

/-- …support is kept. -/
theorem frame_support {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) {m : Loc} (hsupp : ∀ aW, AgW W aW → ∃ ζ, aW.get m = some ζ)
    (ha' : AgW W' a') : ∃ ζ, a'.get m = some ζ := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  obtain ⟨ζs, hζs⟩ := hsupp aW haW
  rcases back_some hrz hζs with ⟨ψ₁, e₁⟩ | ⟨ψ₁, e₁⟩
  · obtain ⟨_, e₂⟩ := comp_some_r hpc e₁
    obtain ⟨_, e₃⟩ := comp_some_r hcp e₂
    exact comp_some hcz e₃
  · exact comp_some_r hcz e₁

/-- `ag(W ● ℓ ↦ own(v)) = ag(W)`. -/
theorem alloc_ag {W W' a' : WRes} {l : Loc} {v : Val}
    (hW : ResU.CompS W (ResU.single l (CellU.ownOf v)) W') (ha' : AgW W' a') : AgW W a' := by
  obtain ⟨σw, σo, hw, ho, hc⟩ := (AgW.split hW).mp ha'
  rw [AgW.functional ho (AgW.single_own l v)] at hc
  rw [ResU.CompR.functional hc (ResU.comp_empty_right σw)]
  exact hw

theorem agW_of_valid {W : WRes} (h : ResU.Valid W) : ∃ a, AgW W a := by
  obtain ⟨σ, e, a, -, ha, -⟩ := h; exact ⟨a, ha⟩

/-- `p ≤ σ` and `σ ∈ Res_β` give `p/ℓ ∈ Res_β`. -/
theorem del_stratum_of_le {p σ : WRes} {l : Loc} {β : Life} (hp : ResU.Le p σ)
    (hσ : σ.InStratum β) : (p.del l).InStratum (LSet.singleton β).join := by
  obtain ⟨τ, hτ⟩ := hp
  have h1 : p.InStratum β := ResU.CompS.inStratum_left hτ hσ
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e; exact h1 m ψ e

theorem vShape_congr : ∀ (T : Ty) {δ₁ δ₂ : LSub},
    (∀ y, LFree y T → δ₁.find? y = δ₂.find? y) → vShape T δ₁ = vShape T δ₂
  | .unit, _, _, _ => rfl
  | .unk, _, _, _ => rfl
  | .lolli _ _, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .tensor T₁ T₂, δ₁, δ₂, h => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vShape T₁ δ₁ v₁ ⋆ vShape T₂ δ₁ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vShape T₁ δ₂ v₁ ⋆ vShape T₂ δ₂ v₂)
      rw [vShape_congr T₁ (fun y hy => h y (Or.inl hy)), vShape_congr T₂ (fun y hy => h y (Or.inr hy))]
  | .sum T₁ T₂, δ₁, δ₂, h => by
      funext v
      show BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vShape T₁ δ₁ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vShape T₂ δ₁ v₂) =
        BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vShape T₁ δ₂ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vShape T₂ δ₂ v₂)
      rw [vShape_congr T₁ (fun y hy => h y (Or.inl hy)), vShape_congr T₂ (fun y hy => h y (Or.inr hy))]
  | .ref T, δ₁, δ₂, h => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vShape T δ₁ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vShape T δ₂ v')
      rw [vShape_congr T h]
  | .bang T, δ₁, δ₂, h => rfl
  | .box a T, δ₁, δ₂, h => by
      funext v
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw)))
        (by rw [vShape_congr T (fun y hy => h y (Or.inr hy))])
  | .imm a T, δ₁, δ₂, h => by
      funext v
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw)))
        (by rw [vShape_congr T (fun y hy => h y (Or.inr hy))])
  | .mut a T, δ₁, δ₂, h => by
      funext v
      exact atLife_congr (interp_congr a (fun w hw => h w (Or.inl hw)))
        (by rw [vShape_congr T (fun y hy => h y (Or.inr hy))])

theorem vShape_extend_of_not_free {x : LifeVar} {T : Ty} (h : ¬ LFree x T)
    (δ : LSub) (α : Life) : vShape T (δ.extend x α) = vShape T δ :=
  vShape_congr T (fun _ hy => find?_extend_ne δ α (fun e => h (e ▸ hy)))

theorem RefPos.not_free {T : Ty} {v : Val} {l : Loc} {S : Ty} (h : RefPos T v l S)
    {x : LifeVar} (hx : ¬ LFree x T) : ¬ LFree x S := by
  induction h with
  | ref S l => exact hx
  | tensorL _ ih => exact ih (fun h => hx (Or.inl h))
  | tensorR _ ih => exact ih (fun h => hx (Or.inr h))
  | sumL _ ih => exact ih (fun h => hx (Or.inl h))
  | sumR _ ih => exact ih (fun h => hx (Or.inr h))
  | box _ ih => exact ih (fun h => hx (Or.inr h))

theorem Val.pair_inj' {a b c d : Val} (h : Val.pair a b = Val.pair c d) : a = c ∧ b = d := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_pair] at hv
  obtain ⟨h₁, h₂⟩ := Expr.pair.inj hv
  exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩

theorem Val.inj₁_inj' {a c : Val} (h : Val.inj₁ a = Val.inj₁ c) : a = c := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₁] at hv
  exact Subtype.ext (Expr.inj₁.inj hv)

theorem Val.inj₂_inj' {a c : Val} (h : Val.inj₂ a = Val.inj₂ c) : a = c := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₂] at hv
  exact Subtype.ext (Expr.inj₂.inj hv)

theorem Val.inj₁_ne_inj₂ {a c : Val} (h : Val.inj₁ a = Val.inj₂ c) : False := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₁, Val.val_inj₂] at hv
  exact Expr.noConfusion hv

/-- A cell of a `●`-operand reaches the composite with its kind, witness and value. -/
theorem compS_get_left' {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ₁ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ₁) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit ∧ ψ.erase = ψ₁.erase := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact ⟨_, f, rfl, rfl, rfl⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁
    refine ⟨χ, f, ?_, (CellU.CompS.wit hC).1, (CellU.CompS.erase hC).1⟩
    rw [CellU.CompS.kind hC]
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    rw [h₁]; rfl

theorem compS_get_right' {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ₂ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₂.kind ∧ ψ.wit = ψ₂.wit ∧ ψ.erase = ψ₂.erase :=
  compS_get_left' (ResU.CompS.comm h) e₂

/-- The typed reborrow's cell at every root.  At a `RefPos T v ℓ S`, a resource
`c ∈ 𝒱⟦Imm̲ 'x T⟧_{δ['x↦β]}(v)` has an `imm` cell at `ℓ` whose witness is
`𝒱⟦S⟧δ`-typed at its value — `[TR]` 6.131's `Ref T′` case (*"`↺α 𝒱⟦Imm 'a T′⟧δ(v)`"*),
carried up through the `⊗`/`⊕`/`[@a]` cases the induction passes. -/
theorem image_at_pos {T : Ty} {v : Val} {l : Loc} {S : Ty} (hp : RefPos T v l S)
    {δ : LSub} {x : LifeVar} {β : Life} (hx : ¬ LFree x T) :
    ∀ {c : WRes}, vShape (T.immReborrow (.var x)) (δ.extend x β) v c →
      ∃ ψ, c.get l = some ψ ∧ ψ.kind = Kind.imm ∧ vShape S δ ψ.erase ψ.wit := by
  induction hp with
  | ref S l =>
      intro c hc
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, hWd, -⟩ := pure_sep_iff.mp hk
      have hl' : l = l' := by
        have := congrArg Subtype.val hl; simpa using this
      subst hl'
      rw [vShape_extend_of_not_free (T := S) hx] at hWd
      exact ⟨_, ResU.single_get_self _ _, rfl, by simpa using hWd⟩
  | @tensorL T₁ T₂ v₁ v₂ l S _ ih =>
      intro c hc
      obtain ⟨a, b, hk⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨ψ, e, k, d⟩ := ih (fun h => hx (Or.inl h)) h₁
      obtain ⟨ψ', e', k', w', r'⟩ := compS_get_left' hcc e
      exact ⟨ψ', e', k'.trans k, by rw [w', r']; exact d⟩
  | @tensorR T₁ T₂ v₁ v₂ l S _ ih =>
      intro c hc
      obtain ⟨a, b, hk⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, -, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨ψ, e, k, d⟩ := ih (fun h => hx (Or.inr h)) h₂
      obtain ⟨ψ', e', k', w', r'⟩ := compS_get_right' hcc e
      exact ⟨ψ', e', k'.trans k, by rw [w', r']; exact d⟩
  | @sumL T₁ T₂ v₁ l S _ ih =>
      intro c hc
      rcases hc with ⟨a, hk⟩ | ⟨a, hk⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk
        cases Val.inj₁_inj' he
        exact ih (fun h => hx (Or.inl h)) h₁
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        exact (Val.inj₁_ne_inj₂ he).elim
  | @sumR T₁ T₂ v₂ l S _ ih =>
      intro c hc
      rcases hc with ⟨a, hk⟩ | ⟨a, hk⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        exact (Val.inj₁_ne_inj₂ he.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk
        cases Val.inj₂_inj' he
        exact ih (fun h => hx (Or.inr h)) h₂
  | @box a T v l S _ ih =>
      intro c hc
      exact ih (fun h => hx (Or.inr h)) hc

/-- `typed_image_pos`: 6.131's `Ref T′` case against `reb_β`'s `own` clause.  At a root
`ℓ ↦ own(u)` of `σ` (`RefPos T v ℓ S`), a typed reborrow `c ∈ reb_β(σ) ∩ 𝒱⟦Imm̲ 'x T⟧` has
`c(ℓ) = imm({β}, u, q/ℓ)` for a piece `q ≤ σ` holding `ℓ` (`[TR]` p. 5, `reb_α`'s `own`
clause), and `q/ℓ ∈ 𝒱⟦S⟧δ(u)`. -/
theorem typed_image_pos {T S : Ty} {δ : LSub} {x : LifeVar} {σ c : WRes} {v : Val} {l : Loc}
    {u : Val} {β : Life} (hx : ¬ LFree x T) (hp : RefPos T v l S)
    (hown : σ.get l = some (CellU.ownOf u)) (hr : ResU.Reb β σ c)
    (ht : vShape (T.immReborrow (.var x)) (δ.extend x β) v c) :
    ∃ (q : WRes) (h : (q.del l).InStratum (LSet.singleton β).join),
      c.get l = some (CellU.immOf (LSet.singleton β) u (q.del l) h) ∧
      ResU.Le q σ ∧ (∃ ψ, q.get l = some ψ) ∧ vShape S δ u (q.del l) := by
  obtain ⟨ψ, eψ, -, hd⟩ := image_at_pos hp hx ht
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨_, eψ⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  obtain ⟨hh, he⟩ := hq.2.1 u hown
  rw [eψ] at he
  cases Option.some.inj he
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  refine ⟨q, hh, eψ, hle'.trans hle, hq.1, ?_⟩
  simpa using hd

/-- A non-`own` cell of an iterated `○` comes from a member, over the same witness. -/
theorem bigComp_back {xs : List WRes} {b : WRes}
    (h : BigComp CellU.CompatR CellU.CompR xs b) {l : Loc} {ψ : CellU Loc Val}
    (e : b.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ x ∈ xs, ∃ ψ', x.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit := by
  induction h generalizing ψ with
  | nil => rw [PMap.empty_get] at e; cases e
  | @cons σ τ ρ σs _ hc ih =>
      rcases back_view hc e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · exact ⟨σ, List.mem_cons_self .., ψ₁, e₁, k₁, w₁⟩
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := ih e₁ k₁
        exact ⟨x, List.mem_cons_of_mem _ hx, ψ', e', k', w₁.trans w'⟩

/-- `[TR]` p. 5's `ag` row read backwards at a view.  A non-`own` cell of `ag(ρ)` at `ℓ`
comes from one of the row's three factors, over the same witness: `ρ|imm` (then `ρ(ℓ)` is
`imm`), the `mut` family `{ag(ρ′) | ρ(m) = mut(_,_,ρ′,_)}`, or the `imm` family
`{ex(ρ′)_○ ○ ag(ρ′) | ρ(m) = imm(_,_,ρ′)}`. -/
theorem agW_source {ρ σ : WRes} (h : AgW ρ σ) {l : Loc} {ψ : CellU Loc Val}
    (e : σ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₀, ρ.get l = some ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ.wit = ψ₀.wit) ∨
    (∃ m ψm a, ρ.get m = some ψm ∧ ψm.kind = Kind.mut ∧ AgW ψm.wit a ∧
      ∃ ψ', a.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit) ∨
    (∃ m ψm ev av p, ρ.get m = some ψm ∧ ψm.kind = Kind.imm ∧ ExR ψm.wit ev ∧
      AgW ψm.wit av ∧ ResU.CompR ev av p ∧
      ∃ ψ', p.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit) := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      rcases back_view hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · rcases back_view ha e₁ k₁ with ⟨ψ₂, e₂, -, w₂⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
        · obtain ⟨e₃, k₃⟩ := ResU.restrict_eq_some.mp e₂
          exact Or.inl ⟨ψ₂, e₃, k₃, w₁.trans w₂⟩
        · obtain ⟨x, hx, ψ', e', k', w'⟩ := bigComp_back hbm e₂ k₂
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          obtain ⟨χ, hχ, hag⟩ := AgWitsM.mem hwm p hp
          obtain ⟨χ', hχ', kχ'⟩ := (hsm.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
          rw [hχ] at hχ'; cases Option.some.inj hχ'
          exact Or.inr (Or.inl ⟨p.1, χ, p.2, hχ, kχ', hag, ψ', e', k',
            w₁.trans (w₂.trans w')⟩)
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := bigComp_back hbi e₁ k₁
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨χ, ev, av, hχ, hex, hag, hc⟩ := AgWitsI.mem hwi p hp
        obtain ⟨χ', hχ', kχ'⟩ := (hsi.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [hχ] at hχ'; cases Option.some.inj hχ'
        exact Or.inr (Or.inr ⟨p.1, χ, ev, av, p.2, hχ, kχ', hex, hag, hc, ψ', e', k',
          w₁.trans w'⟩)

/-- Every cell of `c ∈ reb_β(σ)` is `imm`, and is `reb_β`'s image of `σ`'s cell there
(`[TR]` p. 5's three clauses): an `own` cell becomes `imm({β}, u, q/ℓ)` for a piece `q ≤ σ`
holding `ℓ`; a `mut` cell's witness is kept; an `imm` cell's witness is kept. -/
theorem reb_cell {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc}
    {ψ : CellU Loc Val} (e : c.get m = some ψ) :
    ψ.kind = Kind.imm ∧
    ((∃ u q h, σ.get m = some (CellU.ownOf u) ∧
        ψ = CellU.immOf (LSet.singleton β) u (q.del m) h ∧ ResU.Le q σ ∧
        (∃ ζ, q.get m = some ζ)) ∨
     (∃ ζ, σ.get m = some ζ ∧ ζ.kind = Kind.mut ∧ ψ.wit = ζ.wit) ∨
     (∃ ζ, σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧ ψ.wit = ζ.wit)) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  have hqσ : ResU.Le q σ := hle'.trans hle
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hqσ
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨rfl, Or.inl ⟨u, q, hh, hζ, rfl, ⟨τ, hτ⟩, ζq, hζq⟩⟩
  · obtain ⟨⟨t, ht, -, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨rfl, Or.inr (Or.inr ⟨_, hζ, rfl, ?_⟩)⟩
    rw [CellU.wit_immOf, CellU.wit_immOf]
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨rfl, Or.inr (Or.inl ⟨_, hζ, rfl, ?_⟩)⟩
    rw [CellU.wit_immOf, CellU.wit_mutOf]

/-- The walks of an escrow `σ₀` held at `W(ℓₑ) = imm(s, v, σ₀)`: `ex(σ₀)_○ ○ ag(σ₀)` is
defined (the third factor of `ag(W)`'s row). -/
theorem escrow_walks {W σ₀ aW : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} (hle : W.get le = some (CellU.immOf s v σ₀ hs))
    (haW : AgW W aW) : ∃ e₀ a₀ p₀, ExR σ₀ e₀ ∧ AgW σ₀ a₀ ∧ ResU.CompR e₀ a₀ p₀ := by
  obtain ⟨a₁, a₂, -, h₂, -⟩ := (AgW.split (ResU.del_compS hle)).mp haW
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, -⟩ := AgW.single_imm_inv h₂
  exact ⟨e₀, a₀, p₀, he₀, ha₀, hp₀⟩

/-- A view of `ex(σ₀)_○ ○ ag(σ₀)` reaches `ag(W)` (`lift_part` at `t = σ₀`). -/
theorem lift_escrow {W σ₀ aW e₀ a₀ p₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} (hle : W.get le = some (CellU.immOf s v σ₀ hs))
    (haW : AgW W aW) (he₀ : ExR σ₀ e₀) (ha₀ : AgW σ₀ a₀) (hp₀ : ResU.CompR e₀ a₀ p₀)
    {l : Loc} {ψ : CellU Loc Val} (e : p₀.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ.wit :=
  lift_part hle (ResU.Le.refl _) haW he₀ ha₀ hp₀ e hk

theorem hRR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
  fun _ _ ψ hc => ⟨ψ, hc⟩

/-- The `reb` step's view transfer, at every root.  At `W′ = W ● c` with
`c ∈ reb_β(σ₀)` and `σ₀` the escrow of an `imm` cell of `W`: every non-`own` cell of
`ag(W′)` either carries the witness of a non-`own` cell of `ag(W)` at the same location, or
sits at an owned cell `ℓ ↦ own(u)` of `σ₀` where `c(ℓ) = imm({β}, u, q/ℓ)` and carries
`q/ℓ`.  `reb_β`'s `mut` and `imm` clauses keep a
witness `ag(W)` already holds (`AgW.mut_wit_le`, `AgW.imm_wit_le`, `ExW.wit_le`), and its
`own` clause's `q/ℓ ≤ σ₀` is `lift_part`'s. -/
theorem reb_transfer_gen {W W' c σ₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} {β : Life}
    (hle : W.get le = some (CellU.immOf s v σ₀ hs)) (hr : ResU.Reb β σ₀ c)
    (hW : ResU.CompS W c W') {a' : WRes} (ha' : AgW W' a') {l : Loc} {ψ : CellU Loc Val}
    (e : a'.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ aW, AgW W aW ∧ ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) ∨
    (∃ (u : Val) (q : WRes) (h : (q.del l).InStratum (LSet.singleton β).join),
      σ₀.get l = some (CellU.ownOf u) ∧
      c.get l = some (CellU.immOf (LSet.singleton β) u (q.del l) h) ∧ ψ.wit = q.del l) := by
  obtain ⟨aW, ac, haW, hac, hcomp⟩ := (AgW.split hW).mp ha'
  rcases back_view hcomp e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
  · exact Or.inl ⟨aW, haW, ψ₁, e₁, k₁, w₁⟩
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀⟩ := escrow_walks hle haW
  have up : ∀ ψ', p₀.get l = some ψ' → ψ'.kind ≠ Kind.own → ψ.wit = ψ'.wit →
      (∃ aW, AgW W aW ∧ ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) :=
    fun ψ' e' k' w' => by
      obtain ⟨ψ₀, e₀', k₀, w₀⟩ := lift_escrow hle haW he₀ ha₀ hp₀ e' k'
      exact ⟨aW, haW, ψ₀, e₀', k₀, w'.trans w₀.symm⟩
  rcases agW_source hac e₂ k₂ with ⟨ψ₀, eψ₀, kψ₀, wψ₀⟩ | ⟨m, ψm, a, eψm, kψm, -⟩ |
      ⟨m, ψm, ev, av, p, eψm, kψm, hev, hav, hp, ψ', e', k', w'⟩
  · -- `c|imm` at `ℓ` itself
    obtain ⟨-, hcase⟩ := reb_cell hr eψ₀
    rcases hcase with ⟨u, q, h, hown, rfl, -, -⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · exact Or.inr ⟨u, q, h, hown, eψ₀, by rw [w₂, wψ₀, CellU.wit_immOf]⟩
    · obtain ⟨χ, eχ, -, hχ⟩ := ExR.get_of_ne_imm he₀ eζ (by rw [kζ]; exact fun c => Kind.noConfusion c)
      obtain ⟨wχ, kχ⟩ := hχ (by rw [kζ]; exact fun c => Kind.noConfusion c)
      obtain ⟨ψ', e', k', w'⟩ := lift_view hp₀ eχ kχ
      exact Or.inl <| up ψ' e' k' (by rw [w₂, wψ₀, wζ, w', wχ])
    · obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm ha₀ eζ kζ
      obtain ⟨ψ', e', k', w'⟩ := lift_view_r hp₀ eχ (by rw [kχ]; exact fun c => Kind.noConfusion c)
      exact Or.inl <| up ψ' e' k' (by rw [w₂, wψ₀, wζ, w', wχ])
  · -- the `mut` family of `c`: `c` has no `mut` cell
    exact absurd (reb_cell hr eψm).1 (by rw [kψm]; exact fun c => Kind.noConfusion c)
  · -- the `imm` family of `c`: `ex(w)_○ ○ ag(w)` of one of `c`'s cells
    obtain ⟨-, hcase⟩ := reb_cell hr eψm
    rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · have ht : ResU.Le (q.del m) σ₀ := ResU.Le.trans ⟨_, ResU.del_compS hζq⟩ hqσ
      rw [CellU.wit_immOf] at hev hav
      obtain ⟨ψ₀, e₀', k₀, w₀⟩ := lift_part hle ht haW hev hav hp e' k'
      exact Or.inl ⟨aW, haW, ψ₀, e₀', k₀, w₂.trans (w'.trans w₀.symm)⟩
    · obtain ⟨ev', z, hev', hz⟩ := ExW.wit_le hRR ResU.compLawsR he₀ eζ kζ
      obtain ⟨av', z', hav', hz'⟩ := AgW.mut_wit_le ha₀ eζ kζ
      rw [wζ] at hev hav
      rw [ExR.functional hev hev'] at hp
      rw [AgW.functional hav hav'] at hp
      rcases back_view hp e' k' with ⟨ψ₃, e₃, k₃, w₃⟩ | ⟨ψ₃, e₃, k₃, w₃⟩
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz e₃ k₃
        obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view hp₀ e₄ k₄
        exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₃, w₅, w₄])
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz' e₃ k₃
        obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view_r hp₀ e₄ k₄
        exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₃, w₅, w₄])
    · obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ := AgW.imm_wit_le ha₀ eζ kζ
      rw [wζ] at hev hav
      rw [ExR.functional hev hev', AgW.functional hav hav'] at hp
      rw [ResU.CompR.functional hp hp'] at e'
      obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz e' k'
      obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view_r hp₀ e₄ k₄
      exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₅, w₄])

/-- An `imm` cell of a `○`-composite comes from an `imm` operand. -/
theorem imm_back {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ : CellU Loc Val}
    (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = Kind.imm) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = Kind.imm) := by
  rcases ResU.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk⟩
  · rw [e'] at e; cases Option.some.inj e
    obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
    rcases CellU.CompR.imm_source hC hψ with ⟨s₁, h₁, e₁'⟩ | ⟨s₂, h₂, e₂'⟩
    · exact Or.inl ⟨_, e₁, by rw [e₁']; rfl⟩
    · exact Or.inr ⟨_, e₂, by rw [e₂']; rfl⟩

theorem imm_fwd_l {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ₁ : CellU Loc Val}
    (e : a₁.get l = some ψ₁) (hk : ψ₁.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨χ, eχ, kχ, -, -⟩ := ResU.CompR.get_imm_left h e hk
  exact ⟨χ, eχ, kχ⟩

theorem imm_fwd_r {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc} {ψ₂ : CellU Loc Val}
    (e : a₂.get l = some ψ₂) (hk : ψ₂.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨χ, eχ, kχ, -, -⟩ := ResU.CompR.get_imm_right h e hk
  exact ⟨χ, eχ, kχ⟩

/-- Under `immFrame` (`[TR]` 6.64), an `imm` cell of `ag(W)` stays `imm` in `ag(W′)`. -/
theorem frame_imm {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) (ha' : AgW W' a') {aW : WRes} (haW : AgW W aW) {m : Loc}
    {ψ₀ : CellU Loc Val} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgW.functional haW' haW] at hrz
  rcases imm_back hrz e₀ k₀ with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₁, e₁, k₁⟩
  · obtain ⟨ψ₂, e₂, k₂⟩ := imm_fwd_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃⟩ := imm_fwd_r hcp e₂ k₂
    exact imm_fwd_l hcz e₃ k₃
  · exact imm_fwd_r hcz e₁ k₁

/-- A root of a record: `ℓ ↦ own(u)` in the escrow at a `RefPos` of the recorded `(T, v)`.
`[about ours: our record, read at 6.131's positions]` -/
def Root (r : FrameRec) (S : Ty) (l : Loc) (u : Val) : Prop :=
  RefPos r.T r.v l S ∧ r.R.get l = some (CellU.ownOf u)

theorem empty_of_pure {p : Prop} {ρ : WRes} (h : (⌜p⌝ : WProp) ρ) : ρ = PMap.empty := h.1

/-- Every cell of a typed reborrow sits over a cell of the typed escrow, and over an
`own` cell only at a root.  By induction on `T`, the clauses of `𝒱⟦Imm̲ 'x T⟧` against
those of `𝒱⟦T⟧`: `⊸`, `∀` and `Unk` give `emp`; `Ref S` a single cell over `ℓ ↦ own(u)`;
`Imm @a S` a single cell over the `imm` cell; `Mut @a S` a single cell over the `mut` cell. -/
theorem image_dom {x : LifeVar} {δ δ' : LSub} :
    ∀ (T : Ty) {v : Val} {c R : WRes}, vShape (T.immReborrow (.var x)) δ' v c →
      vShape T δ v R → ∀ {m : Loc} {ψ : CellU Loc Val}, c.get m = some ψ →
      ∃ ζ, R.get m = some ζ ∧ (ζ.kind = Kind.own → ∃ S, RefPos T v m S) := by
  intro T
  induction T with
  | unit =>
      intro v c R hc _ m ψ e
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | sum T₁ T₂ ih₁ ih₂ =>
      intro v c R hc hR m ψ e
      rcases hc with ⟨a, hk⟩ | ⟨a, hk⟩ <;> rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk'
        subst he; cases Val.inj₁_inj' he'
        obtain ⟨ζ, eζ, hζ⟩ := ih₁ h₁ h₁' e
        exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPos.sumL hS⟩⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        subst he; exact (Val.inj₁_ne_inj₂ he').elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        subst he; exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk'
        subst he; cases Val.inj₂_inj' he'
        obtain ⟨ζ, eζ, hζ⟩ := ih₂ h₂ h₂' e
        exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPos.sumR hS⟩⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v c R hc hR m ψ e
      obtain ⟨a, b, hk⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', h₂'⟩ := pure_sep_iff.mp hk'
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases back_some hcc e with ⟨ψ₁, e₁⟩ | ⟨ψ₂, e₂⟩
      · obtain ⟨ζ₁, eζ₁, hζ₁⟩ := ih₁ h₁ h₁' e₁
        obtain ⟨ζ, eζ, kζ, -, -⟩ := compS_get_left' hRR eζ₁
        exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ₁ (kζ ▸ k); ⟨S, RefPos.tensorL hS⟩⟩
      · obtain ⟨ζ₂, eζ₂, hζ₂⟩ := ih₂ h₂ h₂' e₂
        obtain ⟨ζ, eζ, kζ, -, -⟩ := compS_get_right' hRR eζ₂
        exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ₂ (kζ ▸ k); ⟨S, RefPos.tensorR hS⟩⟩
  | lolli T₁ T₂ _ _ =>
      intro v c R hc _ m ψ e
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | ref S _ =>
      intro v c R hc hR m ψ e
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      subst hl
      obtain ⟨l'', u, hk'⟩ := hR
      obtain ⟨hl', ρa, ρb, hab, hown, -⟩ := pure_sep_iff.mp hk'
      have hl'' : m = l'' := by have := congrArg Subtype.val hl'; simpa using this
      subst hl''
      rw [show ρa = ResU.single m (CellU.ownOf u) from hown] at hab
      have := (ResU.CompS.get_left_of_ne_imm hab (ResU.single_get_self _ _) (by simp)).2
      exact ⟨_, this, fun _ => ⟨S, RefPos.ref S m⟩⟩
  | bang S _ =>
    intro v c R hc _ m ψ e
    rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | imm a S _ =>
      intro v c R hc hR m ψ e
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      obtain ⟨α', -, l'', hk'⟩ := hR
      obtain ⟨hl', s', w', W', hW', rfl, -, -⟩ := pure_sep_iff.mp hk'
      have : m = l'' := by
        have := congrArg Subtype.val (hl.symm.trans hl'); simpa using this
      subst this
      exact ⟨_, ResU.single_get_self _ _, fun k => absurd k (by simp)⟩
  | «mut» a S _ =>
      intro v c R hc hR m ψ e
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      obtain ⟨α', -, l'', hk'⟩ := hR
      obtain ⟨hl', -, ⟨b, w', W', hW', Q, hQ, -, rfl, -⟩, -⟩ := pure_sep_iff.mp hk'
      have : m = l'' := by
        have := congrArg Subtype.val (hl.symm.trans hl'); simpa using this
      subst this
      exact ⟨_, ResU.single_get_self _ _, fun k => absurd k (by simp)⟩
  | box a T ih =>
      intro v c R hc hR m ψ e
      obtain ⟨α, -, hb, -⟩ := hR
      obtain ⟨ζ, eζ, hζ⟩ := ih hc hb e
      exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPos.box hS⟩⟩
  | all y b T _ =>
      intro v c R hc _ m ψ e
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | unk =>
      intro v c R hc _ m ψ e
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e

open Classical in
/-- The cell `reb_β`'s `own`/`mut` clauses would put at `m` over the same value and witness,
where `R(m)` is not `imm`; otherwise the cell unchanged. -/
def relCell (R : WRes) (β : Life) (m : Loc) (ψ : CellU Loc Val) : CellU Loc Val :=
  if h : ψ.kind = Kind.imm ∧ (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
      ψ.wit.InStratum (LSet.singleton β).join then
    CellU.immOf (LSet.singleton β) ψ.erase ψ.wit h.2.2
  else ψ

/-- `c` with each cell passed through `relCell`. -/
def relRes (R : WRes) (β : Life) (c : WRes) : WRes where
  get m := (c.get m).map (relCell R β m)
  finite := by
    obtain ⟨d, hd⟩ := c.finite
    exact ⟨d, fun l hl => hd l (fun e => hl (by simp [e]))⟩

theorem relRes_get (R : WRes) (β : Life) (c : WRes) (m : Loc) :
    (relRes R β c).get m = (c.get m).map (relCell R β m) := rfl

theorem relCell_props (R : WRes) (β : Life) (m : Loc) (ψ : CellU Loc Val) :
    (relCell R β m ψ).erase = ψ.erase ∧ (relCell R β m ψ).wit = ψ.wit ∧
    (relCell R β m ψ).kind = ψ.kind := by
  unfold relCell
  split
  · rename_i h
    exact ⟨by simp, by simp, by simp [h.1]⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem relCell_fire {R : WRes} {β : Life} {m : Loc} {s : LSet} {v : Val} {w : WRes}
    {hw : w.InStratum s.join} {ζ : CellU Loc Val} (eζ : R.get m = some ζ)
    (kζ : ζ.kind ≠ Kind.imm) (hβ : w.InStratum (LSet.singleton β).join) :
    relCell R β m (CellU.immOf s v w hw) = CellU.immOf (LSet.singleton β) v w hβ := by
  unfold relCell
  rw [dif_pos ⟨rfl, ⟨ζ, eζ, kζ⟩, by simpa using hβ⟩]
  exact CellU.immOf_congr rfl (by simp) (by simp) _ _

theorem relCell_keep {R : WRes} {β : Life} {m : Loc} {ψ ζ : CellU Loc Val}
    (eζ : R.get m = some ζ) (kζ : ζ.kind = Kind.imm) : relCell R β m ψ = ψ := by
  unfold relCell
  rw [dif_neg]
  rintro ⟨-, ⟨ζ', e', k'⟩, -⟩
  rw [eζ] at e'; cases Option.some.inj e'; exact k' kζ

theorem relCell_compS {R : WRes} {β : Life} {m : Loc} {ψ₁ ψ₂ ψ : CellU Loc Val}
    (hC : CellU.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS (relCell R β m ψ₁) (relCell R β m ψ₂) (relCell R β m ψ) := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := hC
  by_cases hc : (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
      ρ.InStratum (LSet.singleton β).join
  · obtain ⟨⟨ζ, eζ, kζ⟩, hβ⟩ := hc
    rw [relCell_fire eζ kζ hβ, relCell_fire eζ kζ hβ, relCell_fire eζ kζ hβ]
    refine ⟨_, _, v, ρ, hβ, hβ, by rw [LSet.union_self]; exact hβ, rfl, rfl, ?_⟩
    exact CellU.immOf_congr (LSet.union_self _).symm rfl rfl _ _
  · have keep : ∀ (t : LSet) (ht : ρ.InStratum t.join),
        relCell R β m (CellU.immOf t v ρ ht) = CellU.immOf t v ρ ht := by
      intro t ht
      unfold relCell
      rw [dif_neg]
      rintro ⟨-, hz, hw⟩
      exact hc ⟨hz, by simpa using hw⟩
    rw [keep, keep, keep]
    exact ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩

theorem relRes_compS {R : WRes} {β : Life} {c₁ c₂ c : WRes} (h : ResU.CompS c₁ c₂ c) :
    ResU.CompS (relRes R β c₁) (relRes R β c₂) (relRes R β c) := by
  refine ⟨fun m ψ₁' ψ₂' e₁ e₂ => ?_, fun m => ?_⟩
  · rw [relRes_get] at e₁ e₂
    obtain ⟨ψ₁, f₁, rfl⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨ψ₂, f₂, rfl⟩ := Option.map_eq_some_iff.mp e₂
    obtain ⟨k₁, k₂, hv, hw⟩ := CellU.compatS_iff.mp (h.1 m ψ₁ ψ₂ f₁ f₂)
    obtain ⟨r₁, w₁, q₁⟩ := relCell_props R β m ψ₁
    obtain ⟨r₂, w₂, q₂⟩ := relCell_props R β m ψ₂
    exact CellU.compatS_iff.mpr ⟨q₁.trans k₁, q₂.trans k₂, by rw [r₁, r₂, hv],
      by rw [w₁, w₂, hw]⟩
  · rcases ResU.Comp.get h m with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;>
      rw [relRes_get, relRes_get, relRes_get, e₁, e₂, e] <;> simp only [Option.map_none, Option.map_some]
    · exact rfl
    · exact rfl
    · exact rfl
    · exact ⟨_, rfl, relCell_compS hC⟩

theorem relRes_empty (R : WRes) (β : Life) : relRes R β PMap.empty = PMap.empty :=
  PMap.ext fun m => by rw [relRes_get]; rfl

theorem relRes_single (R : WRes) (β : Life) (l : Loc) (ψ : CellU Loc Val) :
    relRes R β (ResU.single l ψ) = ResU.single l (relCell R β l ψ) := by
  refine PMap.ext fun m => ?_
  rw [relRes_get]
  by_cases e : m = l
  · subst e; rw [ResU.single_get_self, ResU.single_get_self]; rfl
  · rw [ResU.single_get_ne _ e, ResU.single_get_ne _ e]; rfl

theorem interp_ext_self (δ : LSub) (x : LifeVar) (β : Life) :
    (Lifetime.Life.var x).interp (δ.extend x β) = some β := by
  rw [Lifetime.Life.interp_var, find?_extend_self]

/-- …and it is in `reb_β(R)`, by the same `π`. -/
theorem relabel_reb {R c₀ : WRes} {β β₀ : Life} (hRβ : R.InStratum β)
    (hr : ResU.Reb β₀ R c₀) : ResU.Reb β R (relRes R β c₀) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  refine ⟨hRβ, π, b, ⟨hdom.1, fun m => ?_⟩, hbig, hle, fun m p hp => ?_⟩
  · rw [hdom.2 m, relRes_get]
    constructor
    · rintro ⟨ψ, e⟩; exact ⟨_, by rw [e]; rfl⟩
    · rintro ⟨ψ, e⟩
      obtain ⟨ψ₀, e₀, -⟩ := Option.map_eq_some_iff.mp e
      exact ⟨ψ₀, e₀⟩
  have hq := hbody m p hp
  have hmem : p ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hp, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  have hpR : ResU.Le p R := hle'.trans hle
  refine ⟨hq.1, fun u hown => ?_, fun b₀ v χ hb P hw hmut => ?_, fun s v χ h himm => ?_⟩
  · obtain ⟨h₀, e₀⟩ := hq.2.1 u hown
    have hβ := del_stratum_of_le (l := m) hpR hRβ
    refine ⟨hβ, ?_⟩
    rw [relRes_get, e₀]
    simp only [Option.map_some]
    rw [relCell_fire hown (by simp) hβ]
  · obtain ⟨⟨h₀, e₀⟩, hd⟩ := hq.2.2.1 b₀ v χ hb P hw hmut
    have hcell := hRβ m _ hmut
    have hβ : χ.InStratum (LSet.singleton β).join :=
      ResU.InStratum.mono (le_of_lt hcell) hb
    refine ⟨⟨hβ, ?_⟩, hd⟩
    rw [relRes_get, e₀]
    simp only [Option.map_some]
    rw [relCell_fire hmut (by simp) hβ]
  · obtain ⟨⟨t, ht, hsub, e₀⟩, hd⟩ := hq.2.2.2 s v χ h himm
    refine ⟨⟨t, ht, hsub, ?_⟩, hd⟩
    rw [relRes_get, e₀]
    simp only [Option.map_some]
    rw [relCell_keep himm rfl]

/-- `○` against an `imm` cell reads only its value and witness. -/
theorem compatR_imm_congr' {s' : LSet} {v' : Val} {ρ' : WRes} {hs' : ρ'.InStratum s'.join}
    {ψ ζ : CellU Loc Val} (k : ψ.kind = Kind.imm) (he : v' = ψ.erase) (hw : ρ' = ψ.wit)
    (h : CellU.CompatR ψ ζ) : CellU.CompatR (CellU.immOf s' v' ρ' hs') ζ := by
  obtain ⟨χ, hc⟩ := h
  cases hc with
  | same =>
      exact ⟨_, CellU.CompR.strict (CellU.compatS_iff.mpr ⟨rfl, k, by simpa using he,
        by simpa using hw⟩)⟩
  | strict kk =>
      obtain ⟨-, k₂, e₂, w₂⟩ := CellU.compatS_iff.mp kk
      exact ⟨_, CellU.CompR.strict (CellU.compatS_iff.mpr ⟨rfl, k₂,
        by rw [← e₂]; simpa using he, by rw [← w₂]; simpa using hw⟩)⟩
  | mutMut => exact absurd k (by simp)
  | mutOwn => exact absurd k (by simp)
  | ownMut => exact absurd k (by simp)
  | immOwn s v ρ h =>
      simp only [CellU.erase_immOf, CellU.wit_immOf] at he hw
      subst he; subst hw
      exact ⟨_, CellU.CompR.immOwn s' _ _ hs'⟩
  | ownImm => exact absurd k (by simp)
  | immMut s v ρ h b hb P hP =>
      simp only [CellU.erase_immOf, CellU.wit_immOf] at he hw
      subst he; subst hw
      exact ⟨_, CellU.CompR.immMut s' _ _ hs' b hb P hP⟩
  | mutImm => exact absurd k (by simp)

theorem compatR_imm_congr {ψ ψ' ζ : CellU Loc Val} (k : ψ.kind = Kind.imm)
    (k' : ψ'.kind = Kind.imm) (he : ψ'.erase = ψ.erase) (hw : ψ'.wit = ψ.wit)
    (h : CellU.CompatR ψ ζ) : CellU.CompatR ψ' ζ := by
  obtain ⟨s', hs', e'⟩ := CellU.imm_eta k'
  rw [e']
  exact compatR_imm_congr' k he hw h

theorem agWitsI_congr {ρ ρ' : WRes}
    (hc : ∀ l ψ, ρ.get l = some ψ → ∃ ψ', ρ'.get l = some ψ' ∧ ψ'.kind = ψ.kind ∧
      ψ'.wit = ψ.wit) :
    ∀ (wi : List (Loc × WRes)), AgWitsI ρ wi → AgWitsI ρ' wi := by
  intro wi
  induction wi with
  | nil => intro _; exact AgWitsI.nil
  | cons q wi ih =>
      intro h
      cases h with
      | cons ψ hψ hk e a hex hag hp hw =>
          obtain ⟨ψ', e', k', w'⟩ := hc _ ψ hψ
          exact AgWitsI.cons ψ' e' (k'.trans hk) e a (w' ▸ hex) (w' ▸ hag) hp (ih hw)

/-- `ag` of a re-taken image is defined when the original's is: every cell is `imm`,
and the walk reads an `imm` cell only at its value and witness. -/
theorem agW_relRes {R ρ A : WRes} {β : Life}
    (hall : ∀ m ψ, ρ.get m = some ψ → ψ.kind = Kind.imm) (h : AgW ρ A) :
    ∃ A', AgW (relRes R β ρ) A' := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      have hwm0 : wm.map Prod.fst = [] :=
        ResU.sites_nil_of_none hsm (fun l ψ e => by rw [hall l ψ e]; simp)
      have hwm1 : wm = [] := List.map_eq_nil_iff.mp hwm0
      subst hwm1
      have hbm0 : bm = PMap.empty := BigComp.nil_inv hbm
      subst hbm0
      have ha0 : a = ρ.restrict Kind.imm := ResU.CompR.functional ha (ResU.comp_empty_right _)
      subst ha0
      have hget : ∀ l ψ', (relRes R β ρ).get l = some ψ' →
          ∃ ψ, ρ.get l = some ψ ∧ ψ' = relCell R β l ψ := by
        intro l ψ' e
        rw [relRes_get] at e
        obtain ⟨ψ, e₀, rfl⟩ := Option.map_eq_some_iff.mp e
        exact ⟨ψ, e₀, rfl⟩
      have hkind : ∀ l ψ', (relRes R β ρ).get l = some ψ' → ψ'.kind = Kind.imm := by
        intro l ψ' e
        obtain ⟨ψ, e₀, rfl⟩ := hget l ψ' e
        rw [(relCell_props R β l ψ).2.2]; exact hall l ψ e₀
      have hsm' : ResU.Sites (relRes R β ρ) Kind.mut (([] : List (Loc × WRes)).map Prod.fst) :=
        ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), fun ⟨ψ', e, k⟩ => by
          rw [hkind l ψ' e] at k; cases k⟩⟩
      have hsi' : ResU.Sites (relRes R β ρ) Kind.imm (wi.map Prod.fst) := by
        refine ⟨hsi.1, fun l => (hsi.2 l).trans ⟨fun ⟨ψ, e, k⟩ => ?_, fun ⟨ψ', e, k⟩ => ?_⟩⟩
        · exact ⟨relCell R β l ψ, by rw [relRes_get, e]; rfl, by
            rw [(relCell_props R β l ψ).2.2]; exact k⟩
        · obtain ⟨ψ, e₀, rfl⟩ := hget l ψ' e
          exact ⟨ψ, e₀, hall l ψ e₀⟩
      have hwi' : AgWitsI (relRes R β ρ) wi := agWitsI_congr (fun l ψ e =>
        ⟨relCell R β l ψ, by rw [relRes_get, e]; rfl, (relCell_props R β l ψ).2.2,
          (relCell_props R β l ψ).2.1⟩) wi hwi
      obtain ⟨σ', hσ'⟩ := (ResU.compR_defined_iff ((relRes R β ρ).restrict Kind.imm) bi).mpr
        (by
          intro l ψ₁ ψ₂ e₁ e₂
          obtain ⟨e₁', -⟩ := ResU.restrict_eq_some.mp e₁
          obtain ⟨ψ, e₀, rfl⟩ := hget l ψ₁ e₁'
          have hk₀ := hall l ψ e₀
          have hc₀ := hσ.1 l ψ ψ₂ (ResU.restrict_eq_some.mpr ⟨e₀, hk₀⟩) e₂
          obtain ⟨r₁, w₁, q₁⟩ := relCell_props R β l ψ
          exact compatR_imm_congr hk₀ (q₁.trans hk₀) r₁ w₁ hc₀)
      exact ⟨σ', AgW.mk hsm' hsi' AgWitsM.nil hwi' BigComp.nil hbi
        (ResU.comp_empty_right _) hσ'⟩

/-- The views at a record's roots come from one typed reborrow.  If any root of `r` has a
view in `ag(W)`, there is a typed image `c₀ ∈ reb_β₀(R) ∩ 𝒱⟦Imm̲ 'x₀ T⟧` with `ag(c₀)`
defined whose cell at every root carries the witness of the view there.  A reborrow of `R`
puts a view at every root at once (`image_at_pos`), and `✓` makes later views agree with it
(*"immutable cells ψ₁, ψ₂ at the same location must all have the same witness"*, `[CONF]`
415:19), so the most recent image realises them all.
`[about ours: an invariant of the typed world]` -/
def JointAt (W : WRes) (r : FrameRec) : Prop :=
  (∃ S l u, Root r S l u ∧ ∃ a, AgW W a ∧ ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own) →
  ∃ (β₀ : Life) (x₀ : LifeVar) (c₀ : WRes), ¬ LFree x₀ r.T ∧ ResU.Reb β₀ r.R c₀ ∧
    vShape (r.T.immReborrow (.var x₀)) (r.δ.extend x₀ β₀) r.v c₀ ∧ (∃ A, AgW c₀ A) ∧
    ∀ S l u, Root r S l u → ∀ a, AgW W a → ∀ ψ, a.get l = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ, c₀.get l = some ζ ∧ ψ.wit = ζ.wit

/-- The stratum a re-taken image's `own`/`mut`-sourced witnesses need: `q/ℓ ≤ R` and a
`mut` cell's witness both lie in `Res_β` when `R` does (H13, `@ρ′ ⊐ β`). -/
theorem reb_wit_stratum {β β₀ : Life} {R c₀ : WRes} (hRβ : R.InStratum β)
    (hr : ResU.Reb β₀ R c₀) :
    ∀ m ψ, c₀.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      ψ.wit.InStratum (LSet.singleton β).join := by
  intro m ψ e ⟨ζ, eζ, kζ⟩
  obtain ⟨-, hcase⟩ := reb_cell hr e
  rcases hcase with ⟨u, q, h, hown, rfl, hq, -⟩ | ⟨ζ', eζ', kζ', wζ'⟩ | ⟨ζ', eζ', kζ', -⟩
  · rw [CellU.wit_immOf]; exact del_stratum_of_le hq hRβ
  · rw [eζ] at eζ'; cases Option.some.inj eζ'
    rw [wζ']
    rcases CellU.rep ζ with ⟨v, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, v, χ, hb, P, hw, rfl⟩
    · exact absurd kζ' (by simp)
    · exact absurd kζ' (by simp)
    · rw [CellU.wit_mutOf]
      exact ResU.InStratum.mono (le_of_lt (hRβ m _ eζ)) hb
  · rw [eζ] at eζ'; cases Option.some.inj eζ'; exact absurd kζ' kζ

theorem RefPos.inv_ref {S₀ S : Ty} {v : Val} {l : Loc} (h : RefPos (.ref S₀) v l S) :
    v = Val.loc l ∧ S = S₀ := by
  cases h; exact ⟨rfl, rfl⟩

theorem RefPos.inv_tensor {T₁ T₂ S : Ty} {v : Val} {l : Loc}
    (h : RefPos (.tensor T₁ T₂) v l S) :
    ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ (RefPos T₁ v₁ l S ∨ RefPos T₂ v₂ l S) := by
  cases h with
  | tensorL h => exact ⟨_, _, rfl, Or.inl h⟩
  | tensorR h => exact ⟨_, _, rfl, Or.inr h⟩

theorem RefPos.inv_sum {T₁ T₂ S : Ty} {v : Val} {l : Loc} (h : RefPos (.sum T₁ T₂) v l S) :
    (∃ v₁, v = Val.inj₁ v₁ ∧ RefPos T₁ v₁ l S) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ RefPos T₂ v₂ l S) := by
  cases h with
  | sumL h => exact Or.inl ⟨_, rfl, h⟩
  | sumR h => exact Or.inr ⟨_, rfl, h⟩

theorem RefPos.inv_box {a : Lifetime.Life} {T S : Ty} {v : Val} {l : Loc}
    (h : RefPos (.box a T) v l S) : RefPos T v l S := by
  cases h with
  | box h => exact h

theorem own_of_le {B R : WRes} (h : ResU.Le B R) {l : Loc} {u : Val}
    (e : B.get l = some (CellU.ownOf u)) : R.get l = some (CellU.ownOf u) := by
  obtain ⟨τ, hτ⟩ := h
  exact (ResU.CompS.get_left_of_ne_imm hτ e (by simp)).2

theorem not_own_both {B₁ B₂ X : WRes} (h : ResU.CompS B₁ B₂ X) {l : Loc} {u₁ u₂ : Val}
    (e₁ : B₁.get l = some (CellU.ownOf u₁)) (e₂ : B₂.get l = some (CellU.ownOf u₂)) : False := by
  have := ResU.CompatS.right_eq_none h.1 e₁ (by simp)
  rw [e₂] at this; cases this

/-- Parts of the two operands of a `●` compose, and their composite is a part of the whole. -/
theorem sub_comp {B₁ Y₁ R₁ B₂ Y₂ R₂ R : WRes} (h₁ : ResU.CompS B₁ Y₁ R₁)
    (h₂ : ResU.CompS B₂ Y₂ R₂) (h : ResU.CompS R₁ R₂ R) :
    ∃ X, ResU.CompS B₁ B₂ X ∧ ResU.Le X R := by
  obtain ⟨bc, hbc, hB₁⟩ := compS_reassoc h₁ h
  obtain ⟨yb, hyb, hbc'⟩ := compS_reassoc' h₂ hbc
  obtain ⟨z, hz, hbc''⟩ := compS_reassoc (ResU.CompS.comm hyb) hbc'
  obtain ⟨X, hX, hR⟩ := compS_reassoc' hbc'' hB₁
  exact ⟨X, hX, z, hR⟩

theorem le_of_compS_left {a b c : WRes} (h : ResU.CompS a b c) : ResU.Le a c := ⟨b, h⟩

theorem le_of_compS_right {a b c : WRes} (h : ResU.CompS a b c) : ResU.Le b c :=
  ⟨a, ResU.CompS.comm h⟩

/-- At a root, a typed escrow holds `ℓ ↦ own(u′) ● P` with `P ∈ 𝒱⟦S⟧δ(u′)` — the `Ref`
clause of `[TR]` p. 4 (`∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)`), reached through the `⊗`,
`⊕` and `[@a]` clauses. -/
theorem own_split {δ : LSub} :
    ∀ (T : Ty) {v : Val} {R : WRes} {l : Loc} {S : Ty}, vShape T δ v R → RefPos T v l S →
      ∃ u P B, ResU.CompS (ResU.single l (CellU.ownOf u)) P B ∧ vShape S δ u P ∧ ResU.Le B R := by
  intro T
  induction T with
  | ref S₀ _ =>
      intro v R l S hR hp
      obtain ⟨rfl, rfl⟩ := RefPos.inv_ref hp
      obtain ⟨l', u, hk⟩ := hR
      obtain ⟨hl, ρa, ρb, hab, hown, hden⟩ := pure_sep_iff.mp hk
      have e : l = l' := by have := congrArg Subtype.val hl; simpa using this
      subst e
      rw [show ρa = ResU.single l (CellU.ownOf u) from hown] at hab
      exact ⟨u, ρb, R, hab, hden, ResU.Le.refl _⟩
  | bang S₀ _ => intro v R l S hR hp; cases hp
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v R l S hR hp
      obtain ⟨v₁, v₂, rfl, hp'⟩ := RefPos.inv_tensor hp
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he, R₁, R₂, hRR, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      rcases hp' with hp' | hp'
      · obtain ⟨u, P, B, hB, hP, hle⟩ := ih₁ h₁ hp'
        exact ⟨u, P, B, hB, hP, hle.trans (le_of_compS_left hRR)⟩
      · obtain ⟨u, P, B, hB, hP, hle⟩ := ih₂ h₂ hp'
        exact ⟨u, P, B, hB, hP, hle.trans (le_of_compS_right hRR)⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      intro v R l S hR hp
      rcases RefPos.inv_sum hp with ⟨v₁, rfl, hp'⟩ | ⟨v₂, rfl, hp'⟩
      · rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk
          cases Val.inj₁_inj' he
          exact ih₁ h₁ hp'
        · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he).elim
      · rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he.symm).elim
        · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk
          cases Val.inj₂_inj' he
          exact ih₂ h₂ hp'
  | box a T ih =>
      intro v R l S hR hp
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb (RefPos.inv_box hp)
  | unit => intro v R l S _ hp; cases hp
  | lolli _ _ _ _ => intro v R l S _ hp; cases hp
  | imm _ _ _ => intro v R l S _ hp; cases hp
  | «mut» _ _ _ => intro v R l S _ hp; cases hp
  | all _ _ _ _ => intro v R l S _ hp; cases hp
  | unk => intro v R l S _ hp; cases hp

/-- Two roots of a typed escrow are one position, or their blocks compose strictly.
The `⊗` clause's `⋆` is `●` (`[TR]` p. 6), and `●` composes no two `own` cells. -/
theorem refPos_blocks {δ : LSub} :
    ∀ (T : Ty) {v : Val} {R : WRes} {l₁ l₂ : Loc} {S₁ S₂ : Ty}, vShape T δ v R →
      RefPos T v l₁ S₁ → RefPos T v l₂ S₂ →
      (l₁ = l₂ ∧ S₁ = S₂) ∨
      ∃ u₁ u₂ P₁ P₂ B₁ B₂ X, ResU.CompS (ResU.single l₁ (CellU.ownOf u₁)) P₁ B₁ ∧
        vShape S₁ δ u₁ P₁ ∧ ResU.CompS (ResU.single l₂ (CellU.ownOf u₂)) P₂ B₂ ∧
        vShape S₂ δ u₂ P₂ ∧ ResU.CompS B₁ B₂ X ∧ ResU.Le X R := by
  intro T
  induction T with
  | ref S₀ _ =>
      intro v R l₁ l₂ S₁ S₂ _ h₁ h₂
      obtain ⟨e₁, rfl⟩ := RefPos.inv_ref h₁
      obtain ⟨e₂, rfl⟩ := RefPos.inv_ref h₂
      refine Or.inl ⟨?_, rfl⟩
      have := congrArg Subtype.val (e₁.symm.trans e₂); simpa using this
  | bang S₀ _ => intro v R l₁ l₂ S₁ S₂ _ h₁ h₂; cases h₁
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v R l₁ l₂ S₁ S₂ hR h₁ h₂
      obtain ⟨v₁, v₂, rfl, h₁'⟩ := RefPos.inv_tensor h₁
      obtain ⟨v₁', v₂', he, h₂'⟩ := RefPos.inv_tensor h₂
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, hR₁, hR₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases h₁' with h₁' | h₁' <;> rcases h₂' with h₂' | h₂'
      · rcases ih₁ hR₁ h₁' h₂' with h | ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, hX, hle⟩
        · exact Or.inl h
        · exact Or.inr ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, hX,
            hle.trans (le_of_compS_left hRR)⟩
      · obtain ⟨u₁, P₁, B₁, a₁, b₁, ⟨Y₁, hY₁⟩⟩ := own_split T₁ hR₁ h₁'
        obtain ⟨u₂, P₂, B₂, a₂, b₂, ⟨Y₂, hY₂⟩⟩ := own_split T₂ hR₂ h₂'
        obtain ⟨X, hX, hle⟩ := sub_comp hY₁ hY₂ hRR
        exact Or.inr ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, hX, hle⟩
      · obtain ⟨u₁, P₁, B₁, a₁, b₁, ⟨Y₁, hY₁⟩⟩ := own_split T₂ hR₂ h₁'
        obtain ⟨u₂, P₂, B₂, a₂, b₂, ⟨Y₂, hY₂⟩⟩ := own_split T₁ hR₁ h₂'
        obtain ⟨X, hX, hle⟩ := sub_comp hY₂ hY₁ hRR
        exact Or.inr ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, ResU.CompS.comm hX, hle⟩
      · rcases ih₂ hR₂ h₁' h₂' with h | ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, hX, hle⟩
        · exact Or.inl h
        · exact Or.inr ⟨u₁, u₂, P₁, P₂, B₁, B₂, X, a₁, b₁, a₂, b₂, hX,
            hle.trans (le_of_compS_right hRR)⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      intro v R l₁ l₂ S₁ S₂ hR h₁ h₂
      rcases RefPos.inv_sum h₁ with ⟨v₁, rfl, h₁'⟩ | ⟨v₁, rfl, h₁'⟩ <;>
        rcases RefPos.inv_sum h₂ with ⟨v₂, he, h₂'⟩ | ⟨v₂, he, h₂'⟩
      · cases Val.inj₁_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₁_inj' he'
          exact ih₁ hR' h₁' h₂'
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he').elim
      · exact (Val.inj₁_ne_inj₂ he).elim
      · exact (Val.inj₁_ne_inj₂ he.symm).elim
      · cases Val.inj₂_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he'.symm).elim
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₂_inj' he'
          exact ih₂ hR' h₁' h₂'
  | box a T ih =>
      intro v R l₁ l₂ S₁ S₂ hR h₁ h₂
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb (RefPos.inv_box h₁) (RefPos.inv_box h₂)
  | unit => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp
  | lolli _ _ _ _ => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp
  | imm _ _ _ => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp
  | «mut» _ _ _ => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp
  | all _ _ _ _ => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp
  | unk => intro v R l₁ l₂ S₁ S₂ _ hp; cases hp

theorem Chain.own {R : WRes} {T : Ty} {v : Val} {p : Option Loc} {l : Loc} {S : Ty} {u : Val}
    (h : Chain R T v p l S u) : R.get l = some (CellU.ownOf u) := by
  induction h with
  | one _ e => exact e
  | step _ _ _ ih => exact ih

/-- Extending a chain by one `RefPos` step of its last pointee. -/
theorem Chain.snoc {R : WRes} {T : Ty} {v : Val} {p : Option Loc} {l₀ : Loc} {S₀ : Ty}
    {u₀ : Val} (h : Chain R T v p l₀ S₀ u₀) {l : Loc} {S : Ty} {u : Val}
    (hp : RefPos S₀ u₀ l S) (e : R.get l = some (CellU.ownOf u)) :
    Chain R T v (some l₀) l S u := by
  induction h with
  | one h₁ e₁ => exact Chain.step h₁ e₁ (Chain.one hp e)
  | step h₁ e₁ _ ih => exact Chain.step h₁ e₁ (ih hp)

/-- A chain stays inside every typed piece of its source.  If `P ∈ 𝒱⟦T⟧δ(v)` and `P`'s
owned cells are `R`'s, every location a chain from `(T, v)` reaches is an owned cell of `P`. -/
theorem chain_own {δ : LSub} {R : WRes} {T : Ty} {v : Val} {p : Option Loc} {l : Loc}
    {S : Ty} {u : Val} (h : Chain R T v p l S u) :
    ∀ {P : WRes}, vShape T δ v P →
      (∀ m w, P.get m = some (CellU.ownOf w) → R.get m = some (CellU.ownOf w)) →
      P.get l = some (CellU.ownOf u) := by
  induction h with
  | @one T v l S u hp e =>
      intro P hP hag
      obtain ⟨u', P₀, B, hB, -, hle⟩ := own_split T hP hp
      have eB := (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag l u' eP] at e
      cases Option.some.inj e
      exact eP
  | @step T v l₁ S₁ u₁ p l S u hp e₁ _ ih =>
      intro P hP hag
      obtain ⟨u', P₁, B, hB, hP₁, hle⟩ := own_split T hP hp
      have eB := (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag l₁ u' eP] at e₁
      cases Option.some.inj e₁
      have hle₁ : ResU.Le P₁ P := (le_of_compS_right hB).trans hle
      exact own_of_le hle₁ (ih hP₁ (fun m w e => hag m w (own_of_le hle₁ e)))

/-- A location is reached by at most one chain: one parent, one pointee type.  Two first
steps are one position or have strictly composable blocks (`refPos_blocks`), and a chain
through a first step stays inside that step's block (`chain_own`). -/
theorem chain_unique {δ : LSub} {R : WRes} {T : Ty} {v : Val} {p₁ : Option Loc} {l : Loc}
    {S₁ : Ty} {u₁ : Val} (h₁ : Chain R T v p₁ l S₁ u₁) :
    ∀ {P : WRes}, vShape T δ v P →
      (∀ m w, P.get m = some (CellU.ownOf w) → R.get m = some (CellU.ownOf w)) →
      ∀ {p₂ : Option Loc} {S₂ : Ty} {u₂ : Val}, Chain R T v p₂ l S₂ u₂ → p₁ = p₂ ∧ S₁ = S₂ := by
  induction h₁ with
  | @one T v l S₁ u₁ hp₁ e₁ =>
      intro P hP hag p₂ S₂ u₂ h₂
      cases h₂ with
      | one hp₂ e₂ =>
          rcases refPos_blocks T hP hp₁ hp₂ with ⟨-, hS⟩ | ⟨a₁, a₂, Q₁, Q₂, B₁, B₂, X, hB₁, -, hB₂, -, hX, -⟩
          · exact ⟨rfl, hS⟩
          · exact (not_own_both hX
              (ResU.CompS.get_left_of_ne_imm hB₁ (ResU.single_get_self _ _) (by simp)).2
              (ResU.CompS.get_left_of_ne_imm hB₂ (ResU.single_get_self _ _) (by simp)).2).elim
      | @step _ _ l₁' S₁' u₁' p' _ _ _ hp₂ e₂ t₂ =>
          rcases refPos_blocks T hP hp₁ hp₂ with ⟨rfl, rfl⟩ | ⟨a₁, a₂, Q₁, Q₂, B₁, B₂, X, hB₁, _, hB₂, hQ₂, hX, hle⟩
          · obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_split T hP hp₁
            have eP := own_of_le hle
              (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
            rw [hag l w eP] at e₂; cases Option.some.inj e₂
            have hleQ : ResU.Le Q P := (le_of_compS_right hB).trans hle
            have eQ := chain_own t₂ hQ (fun m w e => hag m w (own_of_le hleQ e))
            have := ResU.CompatS.right_eq_none hB.1 (ResU.single_get_self _ _) (by simp)
            rw [eQ] at this; cases this
          · have eX₂ := (ResU.CompS.get_left_of_ne_imm hB₂ (ResU.single_get_self _ _) (by simp)).2
            have hXP : ResU.Le B₂ P := (le_of_compS_right hX).trans hle
            rw [hag _ _ (own_of_le hXP eX₂)] at e₂; cases Option.some.inj e₂
            have hleQ : ResU.Le Q₂ P := (le_of_compS_right hB₂).trans hXP
            have eQ := chain_own t₂ hQ₂ (fun m w e => hag m w (own_of_le hleQ e))
            exact (not_own_both hX
              (ResU.CompS.get_left_of_ne_imm hB₁ (ResU.single_get_self _ _) (by simp)).2
              (own_of_le (le_of_compS_right hB₂) eQ)).elim
  | @step T v l₁ S₁ u₁ p l S u hp₁ e₁ t₁ ih =>
      intro P hP hag p₂ S₂ u₂ h₂
      cases h₂ with
      | one hp₂ e₂ =>
          rcases refPos_blocks T hP hp₂ hp₁ with ⟨rfl, rfl⟩ | ⟨a₁, a₂, Q₁, Q₂, B₁, B₂, X, hB₁, _, hB₂, hQ₂, hX, hle⟩
          · obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_split T hP hp₂
            have eP := own_of_le hle
              (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
            rw [hag l w eP] at e₁; cases Option.some.inj e₁
            have hleQ : ResU.Le Q P := (le_of_compS_right hB).trans hle
            have eQ := chain_own t₁ hQ (fun m w e => hag m w (own_of_le hleQ e))
            have := ResU.CompatS.right_eq_none hB.1 (ResU.single_get_self _ _) (by simp)
            rw [eQ] at this; cases this
          · have eX₂ := (ResU.CompS.get_left_of_ne_imm hB₂ (ResU.single_get_self _ _) (by simp)).2
            have hXP : ResU.Le B₂ P := (le_of_compS_right hX).trans hle
            rw [hag _ _ (own_of_le hXP eX₂)] at e₁; cases Option.some.inj e₁
            have hleQ : ResU.Le Q₂ P := (le_of_compS_right hB₂).trans hXP
            have eQ := chain_own t₁ hQ₂ (fun m w e => hag m w (own_of_le hleQ e))
            exact (not_own_both hX
              (ResU.CompS.get_left_of_ne_imm hB₁ (ResU.single_get_self _ _) (by simp)).2
              (own_of_le (le_of_compS_right hB₂) eQ)).elim
      | @step _ _ l₁' S₁' u₁' p' _ _ _ hp₂ e₂ t₂ =>
          rcases refPos_blocks T hP hp₁ hp₂ with ⟨rfl, rfl⟩ | ⟨a₁, a₂, Q₁, Q₂, B₁, B₂, X, hB₁, hQ₁, hB₂, hQ₂, hX, hle⟩
          · rw [e₁] at e₂; cases Option.some.inj e₂
            obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_split T hP hp₁
            have eP := own_of_le hle
              (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
            rw [hag l₁ w eP] at e₁; cases Option.some.inj e₁
            have hleQ : ResU.Le Q P := (le_of_compS_right hB).trans hle
            obtain ⟨hp, hS⟩ := ih hQ (fun m w e => hag m w (own_of_le hleQ e)) t₂
            subst hp; exact ⟨rfl, hS⟩
          · have hX₁ : ResU.Le B₁ P := (le_of_compS_left hX).trans hle
            have hX₂ : ResU.Le B₂ P := (le_of_compS_right hX).trans hle
            have eX₁ := (ResU.CompS.get_left_of_ne_imm hB₁ (ResU.single_get_self _ _) (by simp)).2
            have eX₂ := (ResU.CompS.get_left_of_ne_imm hB₂ (ResU.single_get_self _ _) (by simp)).2
            rw [hag _ _ (own_of_le hX₁ eX₁)] at e₁; cases Option.some.inj e₁
            rw [hag _ _ (own_of_le hX₂ eX₂)] at e₂; cases Option.some.inj e₂
            have hleQ₁ : ResU.Le Q₁ P := (le_of_compS_right hB₁).trans hX₁
            have hleQ₂ : ResU.Le Q₂ P := (le_of_compS_right hB₂).trans hX₂
            have eQ₁ := chain_own t₁ hQ₁ (fun m w e => hag m w (own_of_le hleQ₁ e))
            have eQ₂ := chain_own t₂ hQ₂ (fun m w e => hag m w (own_of_le hleQ₂ e))
            exact (not_own_both hX (own_of_le (le_of_compS_right hB₁) eQ₁)
              (own_of_le (le_of_compS_right hB₂) eQ₂)).elim

/-- The last step of a chain with a parent. -/
theorem chain_last {R : WRes} {T : Ty} {v : Val} {p : Option Loc} {l : Loc} {S : Ty} {u : Val}
    (h : Chain R T v p l S u) :
    ∀ l₀, p = some l₀ → ∃ p₀ S₀ u₀, Chain R T v p₀ l₀ S₀ u₀ ∧ RefPos S₀ u₀ l S := by
  induction h with
  | one _ _ => intro l₀ e; cases e
  | @step T v l₁ S₁ u₁ p l S u hp e₁ t ih =>
      intro l₀ e
      cases p with
      | none =>
          simp only [Option.getD_none, Option.some.injEq] at e
          subst e
          cases t with
          | one hp' _ => exact ⟨none, S₁, u₁, Chain.one hp e₁, hp'⟩
      | some l₀' =>
          simp only [Option.getD_some, Option.some.injEq] at e
          subst e
          obtain ⟨p₀, S₀, u₀, hc, hr⟩ := ih l₀' rfl
          exact ⟨_, S₀, u₀, Chain.step hp e₁ hc, hr⟩

theorem own_del {q : WRes} {l m : Loc} {w : Val}
    (e : (q.del l).get m = some (CellU.ownOf w)) : q.get m = some (CellU.ownOf w) := by
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rwa [ResU.del_get_ne _ hm] at e

/-- Under `immFrame`, a view of `ag(W)` reaches `ag(W′)` over the same witness. -/
theorem frame_fwd {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) (ha' : AgW W' a') {aW : WRes} (haW : AgW W aW) {m : Loc}
    {ψ₀ : CellU Loc Val} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind ≠ Kind.own) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgW.functional haW' haW] at hrz
  rcases back_view hrz e₀ k₀ with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hcp e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hcz e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hcz e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₄.trans w₁.symm⟩

/-- The invariant at every chain position of a frame.  Every non-`own` cell of `ag(W)` at
a chain position `ℓ` (pointee `S`, value `u`, parent `p`) is an `imm` view, `𝒱⟦S⟧δ(u)`-typed,
whose owned cells are the frame escrow's, and whose witness is `q/ℓ` for a piece `q` of the
parent's escrow: the frame's `R` at a first step, the parent view's witness otherwise — the
escrow a `withload` at the parent reborrows.
`[about ours: an invariant of the typed world]` -/
def DeepInv (W : WRes) (r : FrameRec) : Prop :=
  ∀ p l S u, Chain r.R r.T r.v p l S u → ∀ a, AgW W a → ∀ ψ : CellU Loc Val,
    a.get l = some ψ → ψ.kind ≠ Kind.own →
    ψ.kind = Kind.imm ∧ vShape S r.δ u ψ.wit ∧
    (∀ m w, ψ.wit.get m = some (CellU.ownOf w) → r.R.get m = some (CellU.ownOf w)) ∧
    (p = none → ∃ q, ResU.Le q r.R ∧ (∃ ζ, q.get l = some ζ) ∧ ψ.wit = q.del l) ∧
    (∀ l₀, p = some l₀ → ∃ ψ₀ : CellU Loc Val, a.get l₀ = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧
       ∃ q, ResU.Le q ψ₀.wit ∧ (∃ ζ, q.get l = some ζ) ∧ ψ.wit = q.del l)

/-- The joint clause at a chain position: the views at `ℓ₀`'s children come from one
typed reborrow of the view at `ℓ₀`.
`[about ours: an invariant of the typed world]` -/
def JointDeep (W : WRes) (r : FrameRec) : Prop :=
  ∀ p₀ l₀ S₀ u₀, Chain r.R r.T r.v p₀ l₀ S₀ u₀ →
  (∃ l S u, Chain r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgW W a ∧ ∃ ψ : CellU Loc Val,
      a.get l = some ψ ∧ ψ.kind ≠ Kind.own) →
  ∃ w₀ : WRes, (∀ a, AgW W a → ∃ ψ₀ : CellU Loc Val, a.get l₀ = some ψ₀ ∧
      ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = w₀) ∧
    ∃ (β₀ : Life) (x₀ : LifeVar) (c₀ : WRes), ¬ LFree x₀ S₀ ∧ ResU.Reb β₀ w₀ c₀ ∧
      vShape (S₀.immReborrow (.var x₀)) (r.δ.extend x₀ β₀) u₀ c₀ ∧ (∃ A, AgW c₀ A) ∧
      ∀ l S u, Chain r.R r.T r.v (some l₀) l S u → ∀ a, AgW W a → ∀ ψ : CellU Loc Val,
        a.get l = some ψ → ψ.kind ≠ Kind.own → ∃ ζ, c₀.get l = some ζ ∧ ψ.wit = ζ.wit

/-- The invariant of the nested typed world.
`[about ours: an invariant of the typed world]` -/
def ChainInv (W : WRes) (rs : List FrameRec) : Prop :=
  (∀ r ∈ rs, DeepInv W r) ∧
  (∀ r ∈ rs, ∀ l u, r.R.get l = some (CellU.ownOf u) → ∀ a, AgW W a → ∃ ζ, a.get l = some ζ) ∧
  (∀ r₁ ∈ rs, ∀ r₂ ∈ rs, ∀ l u₁ u₂, r₁.R.get l = some (CellU.ownOf u₁) →
     r₂.R.get l = some (CellU.ownOf u₂) → r₁ = r₂) ∧
  (∀ r ∈ rs, vShape r.T r.δ r.v r.R ∧ AdmWf r.T r.δ) ∧
  (∀ r ∈ rs, JointAt W r) ∧
  (∀ r ∈ rs, JointDeep W r)

theorem chain_unique_rec {r : FrameRec} (hR : vShape r.T r.δ r.v r.R) {p₁ p₂ : Option Loc}
    {l : Loc} {S₁ S₂ : Ty} {u₁ u₂ : Val} (h₁ : Chain r.R r.T r.v p₁ l S₁ u₁)
    (h₂ : Chain r.R r.T r.v p₂ l S₂ u₂) : p₁ = p₂ ∧ S₁ = S₂ :=
  chain_unique h₁ hR (fun _ _ e => e) h₂

theorem chain_val {R : WRes} {T : Ty} {v : Val} {p₁ p₂ : Option Loc} {l : Loc}
    {S₁ S₂ : Ty} {u₁ u₂ : Val} (h₁ : Chain R T v p₁ l S₁ u₁) (h₂ : Chain R T v p₂ l S₂ u₂) :
    u₁ = u₂ := by
  have e₁ := h₁.own; have e₂ := h₂.own
  rw [e₁] at e₂; injection Option.some.inj e₂

/-- The transferred half of a reborrow step, at every clause: a view of `ag(W′)` that
`reb_transfer_gen` sends back to `ag(W)` keeps what `ChainInv` says of it there. -/
theorem reb_like_back {W W' c σ₀ aW : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} {β : Life}
    (hle : W.get le = some (CellU.immOf s v σ₀ hs)) (hr : ResU.Reb β σ₀ c)
    (hW : ResU.CompS W c W') (haW : AgW W aW) {a : WRes} (ha : AgW W' a) {m : Loc}
    {ψ : CellU Loc Val} (e : a.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) ∨
    (∃ (u : Val) (q : WRes) (h : (q.del m).InStratum (LSet.singleton β).join),
      σ₀.get m = some (CellU.ownOf u) ∧
      c.get m = some (CellU.immOf (LSet.singleton β) u (q.del m) h) ∧ ψ.wit = q.del m) := by
  rcases reb_transfer_gen hle hr hW ha e hk with ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩ | hb
  · rw [AgW.functional haW₁ haW] at e₀; exact Or.inl ⟨ψ₀, e₀, k₀, w₀⟩
  · exact Or.inr hb

/-- In a reborrow step, a view of `ag(W)` reaches `ag(W′)`, and an `imm` one stays `imm`. -/
theorem reb_like_fwd {W W' c aW : WRes} (hW : ResU.CompS W c W') (haW : AgW W aW) {a : WRes}
    (ha : AgW W' a) {m : Loc} {ψ₀ : CellU Loc Val} (e₀ : aW.get m = some ψ₀)
    (k₀ : ψ₀.kind ≠ Kind.own) :
    ∃ ψ, a.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit ∧
      (ψ₀.kind = Kind.imm → ψ.kind = Kind.imm) := by
  obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgW.split hW).mp ha
  rw [AgW.functional haW' haW] at hcomp
  obtain ⟨ψ, e, k, w⟩ := lift_view hcomp e₀ k₀
  refine ⟨ψ, e, k, w, fun hk => ?_⟩
  obtain ⟨ψ', e', k'⟩ := imm_fwd_l hcomp e₀ hk
  rw [e] at e'; cases Option.some.inj e'; exact k'

/-- In a reborrow step, a cell of the image reaches `ag(W′)` as an `imm` view over its
witness. -/
theorem reb_like_new {W W' c : WRes} (hW : ResU.CompS W c W') {a : WRes} (ha : AgW W' a)
    {m : Loc} {ζ : CellU Loc Val} (eζ : c.get m = some ζ) (kζ : ζ.kind = Kind.imm) :
    ∃ ψ, a.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.wit = ζ.wit := by
  obtain ⟨aW', ac, -, hac, hcomp⟩ := (AgW.split hW).mp ha
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm hac eζ kζ
  obtain ⟨ψ, e, -, w⟩ := lift_view_r hcomp eχ (by rw [kχ]; simp)
  obtain ⟨ψ', e', k'⟩ := imm_fwd_r hcomp eχ kχ
  rw [e] at e'; cases Option.some.inj e'
  exact ⟨ψ, e, k', w.trans wχ⟩

/-- The `DeepInv` conclusion for a transferred view. -/
theorem deepInv_back {W W' c aW : WRes} {r : FrameRec} (hW : ResU.CompS W c W')
    (haW : AgW W aW) (hI : DeepInv W r) {p : Option Loc} {m : Loc} {S : Ty} {u : Val}
    (hc : Chain r.R r.T r.v p m S u) {a : WRes} (ha : AgW W' a) {ψ ψ₀ : CellU Loc Val}
    (e : a.get m = some ψ) (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind ≠ Kind.own)
    (w₀ : ψ.wit = ψ₀.wit) :
    ψ.kind = Kind.imm ∧ vShape S r.δ u ψ.wit ∧
    (∀ m' w, ψ.wit.get m' = some (CellU.ownOf w) → r.R.get m' = some (CellU.ownOf w)) ∧
    (p = none → ∃ q, ResU.Le q r.R ∧ (∃ ζ, q.get m = some ζ) ∧ ψ.wit = q.del m) ∧
    (∀ l₀, p = some l₀ → ∃ ψ₁ : CellU Loc Val, a.get l₀ = some ψ₁ ∧ ψ₁.kind ≠ Kind.own ∧
       ∃ q, ResU.Le q ψ₁.wit ∧ (∃ ζ, q.get m = some ζ) ∧ ψ.wit = q.del m) := by
  obtain ⟨kk, d, o, b₁, b₂⟩ := hI p m S u hc aW haW ψ₀ e₀ k₀
  obtain ⟨ψ', e', -, -, hi⟩ := reb_like_fwd hW haW ha e₀ k₀
  rw [e] at e'; cases Option.some.inj e'
  refine ⟨hi kk, w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
  obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
  obtain ⟨ψ₂, e₂, k₂, w₂, -⟩ := reb_like_fwd hW haW ha e₁ k₁
  exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩

theorem chainInv_reb {W W' c : WRes} {rs : List FrameRec} {r₀ : FrameRec} {le : Loc} {s : LSet}
    {β : Life} {hs : r₀.R.InStratum s.join} {x : LifeVar}
    (hvW : ResU.Valid W) (hr₀ : r₀ ∈ rs) (hle : W.get le = some (CellU.immOf s r₀.v r₀.R hs))
    (hx : ¬ LFree x r₀.T) (hreb : ResU.Reb β r₀.R c)
    (hden : vShape (r₀.T.immReborrow (.var x)) (r₀.δ.extend x β) r₀.v c)
    (hW : ResU.CompS W c W') (hv : ResU.Valid W') (h : ChainInv W rs) : ChainInv W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have hR₀ := (h4 r₀ hr₀).1
  -- a new view sits at a first-step root of `r₀`
  have newRoot : ∀ m (u₀ : Val) (q : WRes) (hq : (q.del m).InStratum (LSet.singleton β).join),
      r₀.R.get m = some (CellU.ownOf u₀) →
      c.get m = some (CellU.immOf (LSet.singleton β) u₀ (q.del m) hq) →
      ∃ S₀, RefPos r₀.T r₀.v m S₀ := by
    intro m u₀ q hq hown hcl
    obtain ⟨ζ, eζ, hpos⟩ := image_dom r₀.T hden hR₀ hcl
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
      obtain ⟨hp, hS⟩ := chain_unique_rec hR₀ hc (Chain.one hpos hown)
      subst hp; subst hS
      have hu : u = u₀ := chain_val hc (Chain.one hpos hown)
      subst hu
      obtain ⟨q', hq', hc', hle', hql', hty⟩ := typed_image_pos hx hpos hown hreb hden
      rw [hcl] at hc'
      obtain ⟨-, -, hqq⟩ := CellU.immOf_inj (Option.some.inj hc')
      obtain ⟨ψ', e', k', w'⟩ := reb_like_new hW ha hcl rfl
      rw [e] at e'; cases Option.some.inj e'
      rw [CellU.wit_immOf] at w'
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
      obtain ⟨-, ac₀, -, hac₀, -⟩ := (AgW.split hW).mp ha'
      refine ⟨β, x, c, hx, hreb, hden, ⟨ac₀, hac₀⟩, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ζ, eζ, kζ, -⟩ := image_at_pos hR'.1 hx hden
      obtain ⟨ψ₂, e₂, -, w₂⟩ := reb_like_new hW ha₁ eζ kζ
      rw [e₁] at e₂; cases Option.some.inj e₂
      exact ⟨ζ, eζ, w₂⟩
    · have back : ∀ S' m' u', Root r S' m' u' → ∀ a₁, AgW W' a₁ → ∀ ψ₁ : CellU Loc Val,
          a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
          ∃ ψ₀ : CellU Loc Val, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
        intro S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
        rcases reb_like_back hle hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u₀, q, hq, hown, -, -⟩
        · exact hb
        · exact absurd (h3 r hr r₀ hr₀ m' u' u₀ hR'.2 hown) hrr
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back S m u hR a ha ψ e hk
      obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  · have back : ∀ l₀ m' S' u', Chain r.R r.T r.v (some l₀) m' S' u' → ∀ a₁, AgW W' a₁ →
        ∀ ψ₁ : CellU Loc Val, a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
        ∃ ψ₀ : CellU Loc Val, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
      intro l₀ m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
      rcases reb_like_back hle hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u₀, q, hq, hown, hcl, -⟩
      · exact hb
      · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' u' u₀ hc'.own hown
        subst e₂
        obtain ⟨S₀, hpos⟩ := newRoot m' u₀ q hq hown hcl
        exact absurd (chain_unique_rec hR₀ hc' (Chain.one hpos hown)).1 (by simp)
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back l₀ m S u hc a ha ψ e hk
    obtain ⟨w₀, hw₀, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨w₀, fun a₁ ha₁ => ?_, β₀, x₀, c₀, q1, q2, q3, q4,
      fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
      obtain ⟨ψ₃, e₃, k₃, w₃, -⟩ := reb_like_fwd hW haW ha₁ e₂ k₂
      exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back l₀ m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩

theorem chainInv_rebDeep {W W' c : WRes} {rs : List FrameRec} {r₀ : FrameRec} {p₀ : Option Loc}
    {l₀ : Loc} {S₀ : Ty} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    {β : Life} {x : LifeVar}
    (hvW : ResU.Valid W) (hr₀ : r₀ ∈ rs) (hch₀ : Chain r₀.R r₀.T r₀.v p₀ l₀ S₀ u₀)
    (hcell : W.get l₀ = some (CellU.immOf s u₀ w₀ hs)) (hx : ¬ LFree x S₀)
    (hreb : ResU.Reb β w₀ c) (hden : vShape (S₀.immReborrow (.var x)) (r₀.δ.extend x β) u₀ c)
    (hW : ResU.CompS W c W') (hv : ResU.Valid W') (h : ChainInv W rs) : ChainInv W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have hR₀ := (h4 r₀ hr₀).1
  -- the view at `ℓ₀` in `ag(W)`, and what `DeepInv` says of it
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  rw [CellU.erase_immOf] at rχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ := h1 r₀ hr₀ p₀ l₀ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  -- a new view sits at a child of `ℓ₀`
  have newChild : ∀ m (u : Val) (q : WRes) (hq : (q.del m).InStratum (LSet.singleton β).join),
      w₀.get m = some (CellU.ownOf u) →
      c.get m = some (CellU.immOf (LSet.singleton β) u (q.del m) hq) →
      ∃ S', RefPos S₀ u₀ m S' ∧ Chain r₀.R r₀.T r₀.v (some l₀) m S' u := by
    intro m u q hq hown hcl
    obtain ⟨ζ, eζ, hpos⟩ := image_dom S₀ hden hw₀den hcl
    rw [hown] at eζ; cases Option.some.inj eζ
    obtain ⟨S', hS'⟩ := hpos rfl
    exact ⟨S', hS', hch₀.snoc hS' (hw₀own m u hown)⟩
  have viewAt : ∀ a, AgW W' a → ∃ ψ₀ : CellU Loc Val, a.get l₀ = some ψ₀ ∧
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
      obtain ⟨hp, hS⟩ := chain_unique_rec hR₀ hc hcS
      subst hp; subst hS
      have hu : u = u' := chain_val hc hcS
      subst hu
      obtain ⟨q', hq', hc', hle', hql', hty⟩ := typed_image_pos hx hpos hown hreb hden
      rw [hcl] at hc'
      obtain ⟨-, -, hqq⟩ := CellU.immOf_inj (Option.some.inj hc')
      obtain ⟨ψ', e', k', w'⟩ := reb_like_new hW ha hcl rfl
      rw [e] at e'; cases Option.some.inj e'
      rw [CellU.wit_immOf] at w'
      refine ⟨k', by rw [w', hqq]; exact hty, fun m' w e'' => ?_, fun hp => (by cases hp),
        fun l₁ hp => ?_⟩
      · rw [w', hqq] at e''
        exact hw₀own m' w (own_of_le hle' (own_del e''))
      · cases hp
        obtain ⟨ψ₀, e₀, k₀, hw₀⟩ := viewAt a ha
        exact ⟨ψ₀, e₀, k₀, q', hw₀ ▸ hle', hql', by rw [w', hqq]⟩
  · obtain ⟨ζ, hζ⟩ := h2 r hr m u hm aW haW
    exact reb_support hW haW ha hζ
  · have back : ∀ S' m' u', Root r S' m' u' → ∀ a₁, AgW W' a₁ → ∀ ψ₁ : CellU Loc Val,
        a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
        ∃ ψ₀ : CellU Loc Val, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₁.wit = ψ₀.wit := by
      intro S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
      rcases reb_like_back hcell hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u', q, hq, hown, hcl, -⟩
      · exact hb
      · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' _ _ hR'.2 (hw₀own m' _ hown)
        subst e₂
        obtain ⟨S'', -, hcS⟩ := newChild m' _ q hq hown hcl
        exact absurd (chain_unique_rec hR₀ (Chain.one hR'.1 hR'.2) hcS).1 (by simp)
    rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back S m u hR a ha ψ e hk
    obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  · rintro p₁ l₁ S₁ u₁ hc₁ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
    by_cases hrl : r = r₀ ∧ l₁ = l₀
    · obtain ⟨rfl, rfl⟩ := hrl
      obtain ⟨-, hS⟩ := chain_unique_rec hR₀ hc₁ hch₀
      subst hS
      have hu : u₁ = u₀ := chain_val hc₁ hch₀
      subst hu
      obtain ⟨a', ha'⟩ := agW_of_valid hv
      obtain ⟨-, ac₀, -, hac₀, -⟩ := (AgW.split hW).mp ha'
      refine ⟨w₀, viewAt, β, x, c, hx, hreb, hden, ⟨ac₀, hac₀⟩,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨p', S₀', u₀', hcl', hpos⟩ := chain_last hc' l₁ rfl
      obtain ⟨-, hS'⟩ := chain_unique_rec hR₀ hcl' hch₀
      subst hS'
      have hu' : u₀' = u₁ := chain_val hcl' hch₀
      subst hu'
      obtain ⟨ζ, eζ, kζ, -⟩ := image_at_pos hpos hx hden
      obtain ⟨ψ₂, e₂, -, w₂⟩ := reb_like_new hW ha₁ eζ kζ
      rw [e₁] at e₂; cases Option.some.inj e₂
      exact ⟨ζ, eζ, w₂⟩
    · have back : ∀ m' S' u', Chain r.R r.T r.v (some l₁) m' S' u' → ∀ a₁, AgW W' a₁ →
          ∀ ψ₁ : CellU Loc Val, a₁.get m' = some ψ₁ → ψ₁.kind ≠ Kind.own →
          ∃ ψ₀ : CellU Loc Val, aW.get m' = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧
            ψ₁.wit = ψ₀.wit := by
        intro m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
        rcases reb_like_back hcell hreb hW haW ha₁ e₁ hk₁ with hb | ⟨u'', q, hq, hown, hcl, -⟩
        · exact hb
        · have e₂ : r = r₀ := h3 r hr r₀ hr₀ m' _ _ hc'.own (hw₀own m' _ hown)
          subst e₂
          obtain ⟨S'', -, hcS⟩ := newChild m' _ q hq hown hcl
          have := (chain_unique_rec hR₀ hc' hcS).1
          simp only [Option.some.injEq] at this
          exact absurd ⟨rfl, this⟩ hrl
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back m S u hc a ha ψ e hk
      obtain ⟨w₁, hw₁, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
        h6 r hr p₁ l₁ S₁ u₁ hc₁ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨w₁, fun a₁ ha₁ => ?_, β₀, x₀, c₀, q1, q2, q3, q4,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₁ aW haW
        obtain ⟨ψ₃, e₃, k₃, w₃, -⟩ := reb_like_fwd hW haW ha₁ e₂ k₂
        exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁
        obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
        exact ⟨ζ, eζ, w₂.trans wζ⟩

/-- `ψ` at `x` has a counterpart in `a`: a cell over the same value, non-`own` over the same
witness when `ψ` is not `own`. -/
def Cp (a : WRes) (x : Loc) (ψ : CellU Loc Val) : Prop :=
  ∃ ζ : CellU Loc Val, a.get x = some ζ ∧ ζ.erase = ψ.erase ∧
    (ψ.kind ≠ Kind.own → ζ.kind ≠ Kind.own ∧ ζ.wit = ψ.wit)

/-- Every cell of `ρ` has a counterpart in `a`. -/
def AllCp (a ρ : WRes) : Prop := ∀ x ψ, ρ.get x = some ψ → Cp a x ψ

theorem cp_compat {a : WRes} {x : Loc} {ψ₁ ψ₂ : CellU Loc Val} (h₁ : Cp a x ψ₁)
    (h₂ : Cp a x ψ₂) : CellU.CompatR ψ₁ ψ₂ := by
  obtain ⟨ζ₁, e₁, r₁, w₁⟩ := h₁
  obtain ⟨ζ₂, e₂, r₂, w₂⟩ := h₂
  rw [e₁] at e₂; cases Option.some.inj e₂
  exact CellU.compatR_iff.mpr ⟨r₁.symm.trans r₂, fun k₁ k₂ => (w₁ k₁).2.symm.trans (w₂ k₂).2⟩

theorem cp_comp {a : WRes} {x : Loc} {ψ₁ ψ₂ ψ : CellU Loc Val} (hC : CellU.CompR ψ₁ ψ₂ ψ)
    (h₁ : Cp a x ψ₁) (h₂ : Cp a x ψ₂) : Cp a x ψ := by
  obtain ⟨ζ₁, e₁, r₁, w₁⟩ := h₁
  refine ⟨ζ₁, e₁, r₁.trans (CellU.CompR.erase hC).2.symm, fun hk => ?_⟩
  rcases CellU.CompR.back_view hC hk with ⟨k, w⟩ | ⟨k, w⟩
  · obtain ⟨kz, wz⟩ := w₁ k; exact ⟨kz, wz.trans w.symm⟩
  · obtain ⟨ζ₂, e₂, r₂, w₂⟩ := h₂
    rw [e₁] at e₂; cases Option.some.inj e₂
    obtain ⟨kz, wz⟩ := w₂ k; exact ⟨kz, wz.trans w.symm⟩

theorem comp_allCp {a ρ₁ ρ₂ : WRes} (h₁ : AllCp a ρ₁) (h₂ : AllCp a ρ₂) :
    ∃ ρ, ResU.CompR ρ₁ ρ₂ ρ ∧ AllCp a ρ := by
  obtain ⟨ρ, hρ⟩ := (ResU.compR_defined_iff ρ₁ ρ₂).mpr
    (fun x ψ₁ ψ₂ e₁ e₂ => cp_compat (h₁ x ψ₁ e₁) (h₂ x ψ₂ e₂))
  refine ⟨ρ, hρ, fun x ψ e => ?_⟩
  rcases ResU.Comp.get hρ x with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact h₁ x _ e₁
  · rw [e'] at e; cases e; exact h₂ x _ e₂
  · rw [e'] at e; cases e; exact cp_comp hC (h₁ x _ e₁) (h₂ x _ e₂)

theorem bigComp_allCp {a : WRes} :
    ∀ (xs : List WRes), (∀ ρ ∈ xs, AllCp a ρ) →
      ∃ b, BigComp CellU.CompatR CellU.CompR xs b ∧ AllCp a b
  | [], _ => ⟨PMap.empty, BigComp.nil, fun x ψ e => by cases e⟩
  | ρ :: xs, h => by
      obtain ⟨b, hb, hab⟩ := bigComp_allCp xs (fun σ hσ => h σ (List.mem_cons_of_mem _ hσ))
      obtain ⟨c, hc, hac⟩ := comp_allCp (h ρ List.mem_cons_self) hab
      exact ⟨c, BigComp.cons hb hc, hac⟩

theorem allCp_left {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) : AllCp a a₁ := by
  intro x ψ e
  rcases ResU.Comp.get h x with ⟨e₁, -, -⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, e₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e₁] at e; cases e
  · rw [e₁] at e; cases e; exact ⟨_, e', rfl, fun k => ⟨k, rfl⟩⟩
  · rw [e₁] at e; cases e
  · rw [e₁] at e; cases e
    refine ⟨ζ, e', (CellU.CompR.erase hC).2, fun hk => ?_⟩
    obtain ⟨ψ', e'', k', w'⟩ := lift_view h e₁ hk
    rw [e'] at e''; cases Option.some.inj e''
    exact ⟨k', w'⟩

theorem allCp_right {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) : AllCp a a₂ :=
  allCp_left (ResU.CompR.comm h)

theorem allCp_trans {a b c : WRes} (h₁ : AllCp b a) (h₂ : AllCp c b) : AllCp c a := by
  intro x ψ e
  obtain ⟨ζ, e₁, r₁, w₁⟩ := h₁ x ψ e
  obtain ⟨ξ, e₂, r₂, w₂⟩ := h₂ x ζ e₁
  refine ⟨ξ, e₂, r₂.trans r₁, fun hk => ?_⟩
  obtain ⟨k₁, wz⟩ := w₁ hk
  obtain ⟨k₂, wx⟩ := w₂ k₁
  exact ⟨k₂, wx.trans wz⟩

theorem reb_cell_erase {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc}
    {ψ : CellU Loc Val} (e : c.get m = some ψ) :
    ∃ ζ : CellU Loc Val, σ.get m = some ζ ∧ ζ.erase = ψ.erase := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hle'.trans hle
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  refine ⟨ζ, hζ, ?_⟩
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he; simp
  · obtain ⟨⟨t, ht, -, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he; simp
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he; simp

open Classical in
/-- `ag(W)` with the image's cells put in at the image's `own`-sourced locations. -/
def plusRes (aW c σ₀ : WRes) : WRes where
  get x := if (∃ ψ u, c.get x = some ψ ∧ σ₀.get x = some (CellU.ownOf u)) then c.get x
    else aW.get x
  finite := by
    obtain ⟨d₁, h₁⟩ := c.finite
    obtain ⟨d₂, h₂⟩ := aW.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    dsimp only at hl
    by_cases hc : ∃ ψ u, c.get l = some ψ ∧ σ₀.get l = some (CellU.ownOf u)
    · rw [if_pos hc] at hl; exact List.mem_append_left _ (h₁ l hl)
    · rw [if_neg hc] at hl; exact List.mem_append_right _ (h₂ l hl)

open Classical in
theorem plusRes_own {aW c σ₀ : WRes} {x : Loc} {ψ : CellU Loc Val} {u : Val}
    (e : c.get x = some ψ) (hu : σ₀.get x = some (CellU.ownOf u)) :
    (plusRes aW c σ₀).get x = some ψ := by
  show (if _ then _ else _) = _
  rw [if_pos ⟨ψ, u, e, hu⟩, e]

open Classical in
theorem plusRes_other {aW c σ₀ : WRes} {x : Loc}
    (h : ¬ ∃ ψ u, c.get x = some ψ ∧ σ₀.get x = some (CellU.ownOf u)) :
    (plusRes aW c σ₀).get x = aW.get x := by
  show (if _ then _ else _) = _
  rw [if_neg h]

/-- `ag` of a reborrow image is defined when none of its `own`-sourced locations carries a
view in `ag(W)`.  `c ∈ reb_β(σ₀)`, `σ₀` the escrow of an `imm` cell of `W`. -/
theorem agW_image_noview {W aW σ₀ c : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : σ₀.InStratum s.join} {β : Life} (haW : AgW W aW)
    (hle : W.get le = some (CellU.immOf s v σ₀ hs)) (hr : ResU.Reb β σ₀ c)
    (hroot : ∀ x (ψ : CellU Loc Val) (u : Val), c.get x = some ψ →
      σ₀.get x = some (CellU.ownOf u) → ∀ ζ : CellU Loc Val, aW.get x = some ζ →
      ζ.kind = Kind.own) :
    ∃ A, AgW c A := by
  -- the escrow's walks, and their counterparts in `ag(W)`
  obtain ⟨a₁, a₂, -, h₂, h12⟩ := (AgW.split (ResU.del_compS hle)).mp haW
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, hcp₀⟩ := AgW.single_imm_inv h₂
  have cp₀ : AllCp aW p₀ := allCp_trans (allCp_right hcp₀) (allCp_right h12)
  have cpe : AllCp aW e₀ := allCp_trans (allCp_left hp₀) cp₀
  have cpa : AllCp aW a₀ := allCp_trans (allCp_right hp₀) cp₀
  set aP := plusRes aW c σ₀ with haP
  -- the value `ag(W)` carries at an owned cell of the escrow
  have ownVal : ∀ x u, σ₀.get x = some (CellU.ownOf u) → ∀ ζ : CellU Loc Val,
      aW.get x = some ζ → ζ.erase = u := by
    intro x u hu ζ hζ
    obtain ⟨χ, eχ, rχ, -⟩ := ExR.get_of_ne_imm he₀ hu (by simp)
    obtain ⟨ξ, eξ, rξ, -⟩ := cpe x χ eχ
    rw [hζ] at eξ; cases Option.some.inj eξ
    rw [rξ, rχ]; rfl
  -- counterparts in `ag(W)` are counterparts in `aP`
  have plus : ∀ ρ, AllCp aW ρ → AllCp aP ρ := by
    intro ρ hρ x ψ e
    obtain ⟨ζ, eζ, rζ, wζ⟩ := hρ x ψ e
    by_cases hc : ∃ ψ' u, c.get x = some ψ' ∧ σ₀.get x = some (CellU.ownOf u)
    · obtain ⟨ψ', u, e', hu⟩ := hc
      have kζ := hroot x ψ' u e' hu ζ eζ
      refine ⟨ψ', plusRes_own e' hu, ?_, fun hk => absurd kζ (wζ hk).1⟩
      obtain ⟨ζ', eζ', rζ'⟩ := reb_cell_erase hr e'
      rw [hu] at eζ'; cases Option.some.inj eζ'
      rw [← rζ', ← rζ, ownVal x u hu ζ eζ]; rfl
    · exact ⟨ζ, (plusRes_other hc).trans eζ, rζ, wζ⟩
  -- the image's own cells have counterparts in `aP`
  have cpc : AllCp aP c := by
    intro x ψ e
    obtain ⟨-, hcase⟩ := reb_cell hr e
    obtain ⟨ζ₀, eζ₀, rζ₀⟩ := reb_cell_erase hr e
    rcases hcase with ⟨u, q, h, hown, rfl, -, -⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · exact ⟨_, plusRes_own e hown, rfl, fun k => ⟨k, rfl⟩⟩
    · rw [eζ] at eζ₀; cases Option.some.inj eζ₀
      obtain ⟨χ, eχ, rχ, hχ⟩ := ExR.get_of_ne_imm he₀ eζ (by rw [kζ]; simp)
      obtain ⟨wχ, kχ⟩ := hχ (by rw [kζ]; simp)
      obtain ⟨ξ, eξ, rξ, wξ⟩ := cpe x χ eχ
      obtain ⟨kξ, wξ'⟩ := wξ kχ
      refine plus _ (fun y φ ey => ?_) x ψ (ResU.single_get_self x ψ)
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some ey
      exact ⟨ξ, eξ, by rw [rξ, rχ, rζ₀], fun _ => ⟨kξ, by rw [wξ', wχ, wζ]⟩⟩
    · rw [eζ] at eζ₀; cases Option.some.inj eζ₀
      obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm ha₀ eζ kζ
      obtain ⟨ξ, eξ, rξ, wξ⟩ := cpa x χ eχ
      obtain ⟨kξ, wξ'⟩ := wξ (by rw [kχ]; simp)
      refine plus _ (fun y φ ey => ?_) x ψ (ResU.single_get_self x ψ)
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some ey
      exact ⟨ξ, eξ, by rw [rξ, rχ, rζ₀], fun _ => ⟨kξ, by rw [wξ', wχ, wζ]⟩⟩
  -- each witness's `ex(w)_○ ○ ag(w)` is defined, with counterparts in `aP`
  have piece : ∀ x (ψ : CellU Loc Val), c.get x = some ψ →
      ∃ e a p, ExR ψ.wit e ∧ AgW ψ.wit a ∧ ResU.CompR e a p ∧ AllCp aP p := by
    intro x ψ e
    obtain ⟨-, hcase⟩ := reb_cell hr e
    rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · rw [CellU.wit_immOf]
      obtain ⟨τ, hτ⟩ : ResU.Le (q.del x) σ₀ := ResU.Le.trans ⟨_, ResU.del_compS hζq⟩ hqσ
      obtain ⟨et, _, het, -, hce⟩ := (ExR.split_of_compS hτ).mp he₀
      obtain ⟨at', _, hat, -, hca⟩ := (AgW.split hτ).mp ha₀
      obtain ⟨p, hp, cpp⟩ := comp_allCp (allCp_trans (allCp_left hce) cpe)
        (allCp_trans (allCp_left hca) cpa)
      exact ⟨et, at', p, het, hat, hp, plus p cpp⟩
    · obtain ⟨ev', z, hev', hz⟩ := ExW.wit_le hRR ResU.compLawsR he₀ eζ kζ
      obtain ⟨av', z', hav', hz'⟩ := AgW.mut_wit_le ha₀ eζ kζ
      rw [← wζ] at hev' hav'
      obtain ⟨p, hp, cpp⟩ := comp_allCp (allCp_trans (allCp_left hz) cpe)
        (allCp_trans (allCp_left hz') cpa)
      exact ⟨ev', av', p, hev', hav', hp, plus p cpp⟩
    · obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ := AgW.imm_wit_le ha₀ eζ kζ
      rw [← wζ] at hev' hav'
      exact ⟨ev', av', p', hev', hav', hp', plus p' (allCp_trans (allCp_left hz) cpa)⟩
  -- the `imm` family, along `c`'s domain
  have hkind : ∀ x (ψ : CellU Loc Val), c.get x = some ψ → ψ.kind = Kind.imm :=
    fun x ψ e => (reb_cell hr e).1
  obtain ⟨-, π, b, hdom, -, -, -⟩ := hr
  have fam : ∀ d : List Loc, (∀ x ∈ d, ∃ ψ, c.get x = some ψ) →
      ∃ wi : List (Loc × WRes), wi.map Prod.fst = d ∧ AgWitsI c wi ∧
        ∀ q ∈ wi, AllCp aP q.2 := by
    intro d
    induction d with
    | nil => intro _; exact ⟨[], rfl, AgWitsI.nil, fun q hq => absurd hq (by simp)⟩
    | cons x d ih =>
        intro hd
        obtain ⟨wi, hwi, hag, hcp⟩ := ih (fun y hy => hd y (List.mem_cons_of_mem _ hy))
        obtain ⟨ψ, eψ⟩ := hd x List.mem_cons_self
        obtain ⟨e, a, p, he, ha, hp, cpp⟩ := piece x ψ eψ
        refine ⟨(x, p) :: wi, by simp [hwi], AgWitsI.cons ψ eψ (hkind x ψ eψ) e a he ha hp hag,
          fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact cpp
        · exact hcp q hq
  obtain ⟨wi, hwi, hagi, hcpi⟩ :=
    fam (π.map Prod.fst) (fun x hx => (hdom.2 x).mp hx)
  obtain ⟨bi, hbi, cpbi⟩ := bigComp_allCp (wi.map Prod.snd) (fun ρ hρ => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hρ; exact hcpi q hq)
  have cpr : AllCp aP (c.restrict Kind.imm) := fun x ψ e =>
    cpc x ψ (ResU.restrict_eq_some.mp e).1
  obtain ⟨σ, hσ, -⟩ := comp_allCp cpr cpbi
  have hsm : ResU.Sites c Kind.mut (([] : List (Loc × WRes)).map Prod.fst) :=
    ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), fun ⟨ψ, e, k⟩ => by
      rw [hkind l ψ e] at k; cases k⟩⟩
  have hsi : ResU.Sites c Kind.imm (wi.map Prod.fst) := by
    rw [hwi]
    exact ⟨hdom.1, fun l => (hdom.2 l).trans ⟨fun ⟨ψ, e⟩ => ⟨ψ, e, hkind l ψ e⟩,
      fun ⟨ψ, e, _⟩ => ⟨ψ, e⟩⟩⟩
  exact ⟨σ, AgW.mk hsm hsi AgWitsM.nil hagi BigComp.nil hbi (ResU.comp_empty_right _) hσ⟩

/-- The cell of `W` at `ℓ` when `ℓ ↦ imm(s, v, σ) ● F = W`: an `imm` cell over `v` and `σ`. -/
theorem cell_of_compS_single {W F σ : WRes} {l : Loc} {s : LSet} {v : Val}
    {hs : σ.InStratum s.join} (hW : ResU.CompS (ResU.single l (CellU.immOf s v σ hs)) F W) :
    ∃ (s' : LSet) (hs' : σ.InStratum s'.join), W.get l = some (CellU.immOf s' v σ hs') := by
  obtain ⟨ψ, e, k, w, r⟩ := compS_get_left' hW (ResU.single_get_self _ _)
  obtain ⟨s', hs', hψ⟩ := CellU.imm_eta (k.trans (CellU.kind_immOf _ _ _ _))
  simp only [CellU.wit_immOf, CellU.erase_immOf] at w r
  rw [w] at hs'
  refine ⟨s', hs', by rw [e, hψ]; exact congrArg some (CellU.immOf_congr rfl r w _ _)⟩

end BoCa.Fig16.LogRel.Typed

end
