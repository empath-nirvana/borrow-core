import Support.Model.Tree.Port.RelaxedWalks
import Support.Model.Tree.Port.Cells

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Update.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — Update

`[about ours]`.  The update relation `↭` at both printed readings, `reb_α` read at one location, and the form `[TR]` §6 unfolds `↭` to.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- Once a flattening is in hand, the lookup is a lookup in it. -/
theorem ResUT.flatAt_iff {ρ σ : ResUT Loc Val K} (h : ρ.Flat σ) (l : Loc)
    (ψ : CellUT Loc Val K) : ρ.FlatAt l ψ ↔ σ.get l = some ψ :=
  ⟨fun ⟨_, hf, hg⟩ => by cases ResUT.Flat.functional hf h; exact hg, fun hg => ⟨σ, h, hg⟩⟩

/-- `↭` read off a pair of flattenings. -/
theorem ResUT.upd_of_flat {ρ₁ ρ₂ σ₁ σ₂ : ResUT Loc Val K} (h₁ : ρ₁.Flat σ₁)
    (h₂ : ρ₂.Flat σ₂)
    (himm : ∀ (l : Loc) (s : TSet) (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum s),
        σ₁.get l = some (CellUT.immOf s v χ h) ↔ σ₂.get l = some (CellUT.immOf s v χ h))
    (hmut : ∀ (l : Loc) (b : TSet) [Fact (K.Anti b)] (P : Val → SPropST Loc Val K b),
        (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
            σ₁.get l = some (CellUT.mutOf b v χ h P hw)) ↔
        (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
            σ₂.get l = some (CellUT.mutOf b v χ h P hw))) :
    ρ₁.Upd ρ₂ := by
  refine ⟨fun l s v χ h => ?_, fun l b _ P => ?_⟩
  · rw [ResUT.flatAt_iff h₁, ResUT.flatAt_iff h₂]; exact himm l s v χ h
  · constructor
    · rintro ⟨v, χ, h, hw, hg⟩
      obtain ⟨v', χ', h', hw', hg'⟩ :=
        (hmut l b P).mp ⟨v, χ, h, hw, (ResUT.flatAt_iff h₁ _ _).mp hg⟩
      exact ⟨v', χ', h', hw', (ResUT.flatAt_iff h₂ _ _).mpr hg'⟩
    · rintro ⟨v, χ, h, hw, hg⟩
      obtain ⟨v', χ', h', hw', hg'⟩ :=
        (hmut l b P).mpr ⟨v, χ, h, hw, (ResUT.flatAt_iff h₂ _ _).mp hg⟩
      exact ⟨v', χ', h', hw', (ResUT.flatAt_iff h₁ _ _).mpr hg'⟩

theorem ResUT.Upd.symm {ρ₁ ρ₂ : ResUT Loc Val K} (h : ρ₁.Upd ρ₂) : ρ₂.Upd ρ₁ :=
  ⟨fun l s v χ hs => (h.1 l s v χ hs).symm, fun l b _ P => (h.2 l b P).symm⟩

theorem ResUT.dom_single (l : Loc) (ψ : CellUT Loc Val K) :
    ResUT.Dom (ResUT.single l ψ) [l] := by
  classical
  refine ⟨by simp, fun l' => ⟨fun hm => ?_, fun ⟨χ, hg⟩ => ?_⟩⟩
  · cases List.mem_singleton.mp hm
    exact ⟨ψ, ResUT.single_get_self _ _⟩
  · exact List.mem_singleton.mpr (ResUT.single_get_eq_some hg).1

open Classical in
theorem ResUT.del_get_ne (ρ : ResUT Loc Val K) {l l' : Loc} (h : l' ≠ l) :
    (ρ.del l).get l' = ρ.get l' := if_neg h

/-- `ρ ≤ ρ`.
`[about ours: reflexivity of the printed order]` -/
theorem ResUT.Le.refl (ρ : ResUT Loc Val K) : ResUT.Le ρ ρ :=
  ⟨PMap.empty, ResUT.comp_empty_right ρ⟩

/-- `≤` is transitive, as `[TR]` 6.127's second bullet (p. 33) chains it:
*"`ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ≥ ⨀_{ℓ∈dom(π′)} π′(ℓ)`."*
`[about ours: transitivity of the printed order]` -/
theorem ResUT.Le.trans {ρ σ τ : ResUT Loc Val K} (h₁ : ResUT.Le ρ σ) (h₂ : ResUT.Le σ τ) :
    ResUT.Le ρ τ :=
  ResUT.Comp.factor_trans (fun _ _ _ hc => CellUT.CompS.compat hc) ResUT.compLawsS
    h₁.choose_spec h₂.choose_spec

/-- `∅ ≤ ρ`.
`[about ours: the least element of the printed order]` -/
theorem ResUT.Le.empty (ρ : ResUT Loc Val K) : ResUT.Le (PMap.empty : ResUT Loc Val K) ρ := by
  refine ⟨ρ, ResUT.Compat.of_disjoint (fun _ => Or.inl rfl), fun l => ?_⟩
  show OptCompT CellUT.CompS none (ρ.get l) (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

/-- `⨀{ρ} = ρ`.
`[about ours: the fold at one element]` -/
theorem BigCompT.single {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} (ρ : ResUT Loc Val K) :
    BigCompT R C [ρ] ρ := G.BigComp.cons G.BigComp.nil (ResUT.comp_empty_right ρ)

theorem CellUT.Sim.symm {ψ ψ' : CellUT Loc Val K} (h : CellUT.Sim ψ ψ') :
    CellUT.Sim ψ' ψ := by
  rcases h with ⟨a, i, P, h₁, h₂⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · exact Or.inl ⟨a, i, P, h₂, h₁⟩
  · exact Or.inr ⟨s, v, χ, hh, e₂, e₁⟩

theorem ResUT.borrowPart_eq_some {ρ : ResUT Loc Val K} {l : Loc} {ψ : CellUT Loc Val K} :
    ρ.borrowPart.get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind ≠ Kind.own) := by
  rw [show ρ.borrowPart = ρ.restrictOn (fun k => !(k == Kind.own)) from rfl,
    ResUT.restrictOn_eq_some]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩

/-- One direction, at one location: `↭` sends a borrow cell of `⦇ρ₁⦈` to a
`∼`-related cell of `⦇ρ₂⦈`. -/
theorem ResUT.sim_of_upd {ρ₁ ρ₂ σ₁ σ₂ : ResUT Loc Val K} (h : ResUT.Upd ρ₁ ρ₂)
    (h₁ : ResUT.Flat ρ₁ σ₁) (h₂ : ResUT.Flat ρ₂ σ₂)
    {l : Loc} {ψ : CellUT Loc Val K} (hg : σ₁.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) : ∃ ψ', σ₂.get l = some ψ' ∧ CellUT.Sim ψ ψ' := by
  rcases CellUT.rep' ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, _, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellUT.ownOf (K := K) (Loc := Loc) v).kind = Kind.own) hk
  · refine ⟨CellUT.immOf s v χ hh, ?_, Or.inr ⟨s, v, χ, hh, rfl, rfl⟩⟩
    exact (ResUT.flatAt_iff h₂ l _).mp ((h.1 l s v χ hh).mp ⟨σ₁, h₁, hg⟩)
  · obtain ⟨v', χ', h', hw', hfa⟩ := (h.2 l b P).mp ⟨v, χ, hh, hw, ⟨σ₁, h₁, hg⟩⟩
    exact ⟨CellUT.mutOf b v' χ' h' P hw', (ResUT.flatAt_iff h₂ l _).mp hfa,
      Or.inl ⟨b, inferInstance, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v', χ', h', hw', rfl⟩⟩⟩

/-- An `imm` cell composed at `○` with a non-`imm` one is itself. -/
theorem CellUT.CompR.imm_nonimm_left {ψ φ ζ : CellUT Loc Val K}
    (h : CellUT.CompR ψ φ ζ) (hk : ψ.kind = Kind.imm) (hf : φ.kind ≠ Kind.imm) :
    ζ = ψ := by
  cases h with
  | same χ => exact absurd hk hf
  | strict k => exact absurd (CellUT.CompatS.kinds k).2 hf
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd hk (by simp)
  | mutOwn a v ρ ha P hP => exact absurd hk (by simp)
  | ownMut a v ρ ha P hP => exact absurd hk (by simp)
  | immOwn s v ρ hh => rfl
  | ownImm s v ρ hh => exact absurd hk (by simp)
  | immMut s v ρ hh b hb P hP => rfl
  | mutImm s v ρ hh b hb P hP => exact absurd hk (by simp)

/-- `ResUT.SimForm` at one location: the domain clause and `∼`, guarded by
`−∣imm,mut` as `[TR]` p. 20 guards it (an `own` cell is `∼`-related to nothing). -/
def ResUT.SimFormAt (σL σR : ResUT BoCa.Loc BoCa.Val K) (l : BoCa.Loc) : Prop :=
  ((∃ ψ, σL.borrowPart.get l = some ψ) ↔ (∃ ψ, σR.borrowPart.get l = some ψ)) ∧
  (∀ ψ, σL.borrowPart.get l = some ψ →
    ∃ φ, σR.get l = some φ ∧ CellUT.Sim ψ φ)

/-- `↭`'s printed unfolding is `ResUT.SimFormAt` at every location. -/
theorem ResUT.simForm_iff_at {σL σR : ResUT BoCa.Loc BoCa.Val K} :
    ResUT.SimForm σL σR ↔ ∀ l, ResUT.SimFormAt σL σR l :=
  ⟨fun h l => ⟨h.1 l, h.2 l⟩, fun h => ⟨fun l => (h l).1, fun l => (h l).2⟩⟩

end BoCa.Fig16.Tree

end
