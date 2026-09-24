import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Singletons
import Support.Model.Walks

/-!
# Support — Model — Update

`[about ours]`.  The update relation `↭` at both printed readings, `reb_α` read at one location, and the form `[TR]` §6 unfolds `↭` to.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Once a flattening is in hand, the lookup is a lookup in it. -/
theorem ResU.flatAt_iff {ρ σ : ResU Loc Val} (h : ρ.Flat σ) (l : Loc)
    (ψ : CellU Loc Val) : ρ.FlatAt l ψ ↔ σ.get l = some ψ :=
  ⟨fun ⟨_, hf, hg⟩ => by cases ResU.Flat.functional hf h; exact hg, fun hg => ⟨σ, h, hg⟩⟩

/-- `↭` read off a pair of flattenings. -/
theorem ResU.upd_of_flat {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val} (h₁ : ρ₁.Flat σ₁)
    (h₂ : ρ₂.Flat σ₂)
    (himm : ∀ (l : Loc) (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
        σ₁.get l = some (CellU.immOf s v χ h) ↔ σ₂.get l = some (CellU.immOf s v χ h))
    (hmut : ∀ (l : Loc) (b : Life) (P : Val → SPropS Loc Val b),
        (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
            σ₁.get l = some (CellU.mutOf b v χ h P hw)) ↔
        (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
            σ₂.get l = some (CellU.mutOf b v χ h P hw))) :
    ρ₁.Upd ρ₂ := by
  refine ⟨fun l s v χ h => ?_, fun l b P => ?_⟩
  · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]; exact himm l s v χ h
  · constructor
    · rintro ⟨v, χ, h, hw, hg⟩
      obtain ⟨v', χ', h', hw', hg'⟩ :=
        (hmut l b P).mp ⟨v, χ, h, hw, (ResU.flatAt_iff h₁ _ _).mp hg⟩
      exact ⟨v', χ', h', hw', (ResU.flatAt_iff h₂ _ _).mpr hg'⟩
    · rintro ⟨v, χ, h, hw, hg⟩
      obtain ⟨v', χ', h', hw', hg'⟩ :=
        (hmut l b P).mpr ⟨v, χ, h, hw, (ResU.flatAt_iff h₂ _ _).mp hg⟩
      exact ⟨v', χ', h', hw', (ResU.flatAt_iff h₁ _ _).mpr hg'⟩

theorem ResU.Upd.symm {ρ₁ ρ₂ : ResU Loc Val} (h : ρ₁.Upd ρ₂) : ρ₂.Upd ρ₁ :=
  ⟨fun l s v χ hs => (h.1 l s v χ hs).symm, fun l b P => (h.2 l b P).symm⟩

theorem ResU.dom_single (l : Loc) (ψ : CellU Loc Val) :
    ResU.Dom (ResU.single l ψ) [l] := by
  classical
  refine ⟨by simp, fun l' => ⟨fun hm => ?_, fun ⟨χ, hg⟩ => ?_⟩⟩
  · cases List.mem_singleton.mp hm
    exact ⟨ψ, ResU.single_get_self _ _⟩
  · exact List.mem_singleton.mpr (ResU.single_get_eq_some hg).1

open Classical in
theorem ResU.del_get_ne (ρ : ResU Loc Val) {l l' : Loc} (h : l' ≠ l) :
    (ρ.del l).get l' = ρ.get l' := if_neg h

/-- `ρ ≤ ρ`.
`[about ours: reflexivity of the printed order]` -/
theorem ResU.Le.refl (ρ : ResU Loc Val) : ResU.Le ρ ρ :=
  ⟨PMap.empty, ResU.comp_empty_right ρ⟩

/-- `≤` is transitive, as `[TR]` 6.127's second bullet (p. 33) chains it:
*"`ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ≥ ⨀_{ℓ∈dom(π′)} π′(ℓ)`."*
`[about ours: transitivity of the printed order]` -/
theorem ResU.Le.trans {ρ σ τ : ResU Loc Val} (h₁ : ResU.Le ρ σ) (h₂ : ResU.Le σ τ) :
    ResU.Le ρ τ :=
  ResU.Comp.factor_trans (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS
    h₁.choose_spec h₂.choose_spec

/-- `∅ ≤ ρ`.
`[about ours: the least element of the printed order]` -/
theorem ResU.Le.empty (ρ : ResU Loc Val) : ResU.Le (PMap.empty : ResU Loc Val) ρ := by
  refine ⟨ρ, ResU.Compat.of_disjoint (fun _ => Or.inl rfl), fun l => ?_⟩
  show OptComp CellU.CompS none (ρ.get l) (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

/-- `⨀{ρ} = ρ`.
`[about ours: the fold at one element]` -/
theorem BigComp.single {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    BigComp R C [ρ] ρ := BigComp.cons BigComp.nil (ResU.comp_empty_right ρ)

theorem CellU.Sim.symm {ψ ψ' : CellU Loc Val} (h : CellU.Sim ψ ψ') :
    CellU.Sim ψ' ψ := by
  rcases h with ⟨a, P, h₁, h₂⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · exact Or.inl ⟨a, P, h₂, h₁⟩
  · exact Or.inr ⟨s, v, χ, hh, e₂, e₁⟩

theorem ResU.borrowPart_eq_some {ρ : ResU Loc Val} {l : Loc} {ψ : CellU Loc Val} :
    ρ.borrowPart.get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind ≠ Kind.own) := by
  rw [show ρ.borrowPart = ρ.restrictOn (fun k => !(k == Kind.own)) from rfl,
    ResU.restrictOn_eq_some]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩

/-- One direction, at one location: `↭` sends a borrow cell of `⦇ρ₁⦈` to a
`∼`-related cell of `⦇ρ₂⦈`. -/
theorem ResU.sim_of_upd {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val} (h : ResU.Upd ρ₁ ρ₂)
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂)
    {l : Loc} {ψ : CellU Loc Val} (hg : σ₁.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) : ∃ ψ', σ₂.get l = some ψ' ∧ CellU.Sim ψ ψ' := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellU.ownOf (Loc := Loc) v).kind = Kind.own) hk
  · refine ⟨CellU.immOf s v χ hh, ?_, Or.inr ⟨s, v, χ, hh, rfl, rfl⟩⟩
    exact (ResU.flatAt_iff h₂ l _).mp ((h.1 l s v χ hh).mp ⟨σ₁, h₁, hg⟩)
  · obtain ⟨v', χ', h', hw', hfa⟩ := (h.2 l b P).mp ⟨v, χ, hh, hw, ⟨σ₁, h₁, hg⟩⟩
    exact ⟨CellU.mutOf b v' χ' h' P hw', (ResU.flatAt_iff h₂ l _).mp hfa,
      Or.inl ⟨b, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v', χ', h', hw', rfl⟩⟩⟩

/-- An `imm` cell composed at `○` with a non-`imm` one is itself. -/
theorem CellU.CompR.imm_nonimm_left {ψ φ ζ : CellU Loc Val}
    (h : CellU.CompR ψ φ ζ) (hk : ψ.kind = Kind.imm) (hf : φ.kind ≠ Kind.imm) :
    ζ = ψ := by
  cases h with
  | same χ => exact absurd hk hf
  | strict k => exact absurd (CellU.CompatS.kinds k).2 hf
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd hk (by simp)
  | mutOwn a v ρ ha P hP => exact absurd hk (by simp)
  | ownMut a v ρ ha P hP => exact absurd hk (by simp)
  | immOwn s v ρ hh => rfl
  | ownImm s v ρ hh => exact absurd hk (by simp)
  | immMut s v ρ hh b hb P hP => rfl
  | mutImm s v ρ hh b hb P hP => exact absurd hk (by simp)

/-- `ResU.SimForm` at one location: the domain clause and `∼`, guarded by
`−∣imm,mut` as `[TR]` p. 20 guards it (an `own` cell is `∼`-related to nothing). -/
def ResU.SimFormAt (σL σR : ResU BoCa.Loc BoCa.Val) (l : BoCa.Loc) : Prop :=
  ((∃ ψ, σL.borrowPart.get l = some ψ) ↔ (∃ ψ, σR.borrowPart.get l = some ψ)) ∧
  (∀ ψ, σL.borrowPart.get l = some ψ →
    ∃ φ, σR.get l = some φ ∧ CellU.Sim ψ φ)

/-- `↭`'s printed unfolding is `ResU.SimFormAt` at every location. -/
theorem ResU.simForm_iff_at {σL σR : ResU BoCa.Loc BoCa.Val} :
    ResU.SimForm σL σR ↔ ∀ l, ResU.SimFormAt σL σR l :=
  ⟨fun h l => ⟨h.1 l, h.2 l⟩, fun h => ⟨fun l => (h l).1, fun l => (h l).2⟩⟩

end BoCa.Fig16

end
