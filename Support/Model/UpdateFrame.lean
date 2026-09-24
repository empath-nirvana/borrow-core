import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Flattening
import Support.Model.Update
import Support.Model.Walks

/-!
# Support — Model — UpdateFrame

`[about ours]`.  The pointwise route through Lemma 6.48: `⦇−⦈` of a `○`-composite and the cell-level update.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem optComp_left_none
    {C C' : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val →
      CellU BoCa.Loc BoCa.Val → Prop}
    {o₂ o : Option (CellU BoCa.Loc BoCa.Val)} (h : OptComp C none o₂ o) :
    OptComp C' none o₂ o := by
  cases o₂ <;> exact h

theorem optComp_right_none
    {C C' : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val →
      CellU BoCa.Loc BoCa.Val → Prop}
    {o₁ o : Option (CellU BoCa.Loc BoCa.Val)} (h : OptComp C o₁ none o) :
    OptComp C' o₁ none o := by
  cases o₁ <;> exact h

/-- `⦇ρ₁ ● ρ₂⦈ = ⦇ρ₁⦈ ○ ⦇ρ₂⦈`.
`[about ours: the factorisation `[TR]` 6.48's proof performs, as an equation
between flattenings]` -/
theorem flat_compR {ρ₁ ρ₂ ρ₁₂ σ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (hσ : ResU.Flat ρ₁₂ σ) :
    ∃ σ₁ σ₂, ResU.Flat ρ₁ σ₁ ∧ ResU.Flat ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ σ := by
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  have hdisj := ResU.CompatS.disjoint_of_immFree himm hc.1
  have hd12 := ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec.1
  have key : ∀ l, (σ₁.get l = e₁.get l ∧ σ₂.get l = e₂.get l ∧ σ.get l = e.get l)
      ∨ (σ₁.get l = a₁.get l ∧ σ₂.get l = a₂.get l ∧ σ.get l = a.get l) := by
    intro l
    rcases hdisj l with hnoE | hnoA
    · obtain ⟨f₁, f₂⟩ := (ResU.Comp.eq_none_iff hec l).mp hnoE
      exact Or.inr ⟨ResU.Comp.get_of_left_none hσ₁ f₁,
        ResU.Comp.get_of_left_none hσ₂ f₂, ResU.Comp.get_of_left_none hc hnoE⟩
    · obtain ⟨g₁, g₂⟩ := (ResU.Comp.eq_none_iff hac l).mp hnoA
      exact Or.inl ⟨ResU.Comp.get_of_right_none hσ₁ g₁,
        ResU.Comp.get_of_right_none hσ₂ g₂, ResU.Comp.get_of_right_none hc hnoA⟩
  refine ⟨σ₁, σ₂, ⟨e₁, a₁, he₁, ha₁, hσ₁⟩, ⟨e₂, a₂, he₂, ha₂, hσ₂⟩, ?_, ?_⟩
  · intro l ψ₁ ψ₂ f₁ f₂
    rcases key l with ⟨k₁, k₂, -⟩ | ⟨k₁, k₂, -⟩
    · rw [k₁] at f₁; rw [k₂] at f₂
      rcases hd12 l with hn | hn
      · rw [hn] at f₁; exact absurd f₁ (by simp)
      · rw [hn] at f₂; exact absurd f₂ (by simp)
    · rw [k₁] at f₁; rw [k₂] at f₂; exact hac.1 l ψ₁ ψ₂ f₁ f₂
  · intro l
    rcases key l with ⟨k₁, k₂, k⟩ | ⟨k₁, k₂, k⟩
    · rw [k₁, k₂, k]
      have hp := hec.2 l
      rcases hd12 l with hn | hn
      · rw [hn] at hp ⊢; exact optComp_left_none hp
      · rw [hn] at hp ⊢; exact optComp_right_none hp
    · rw [k₁, k₂, k]; exact hac.2 l

/-- `ψ` is a `mut` cell of lifetime `b` and invariant `P̂`, value and witness
free: the data `↭`'s second clause fixes. -/
def IsMutSig (ψ : CellU BoCa.Loc BoCa.Val) (b : Life)
    (P : Val → SPropS BoCa.Loc BoCa.Val b) : Prop :=
  ∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
    ψ = CellU.mutOf b v χ h P hw

/-- `↭`'s two clauses at one location of the two flattenings.
`[about ours: `[TR]` p. 5's `↭`, at one location of the flattenings]` -/
def CellUpd (o o' : Option (CellU BoCa.Loc BoCa.Val)) : Prop :=
  (∀ (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
      o = some (CellU.immOf s v χ h) ↔ o' = some (CellU.immOf s v χ h)) ∧
  (∀ (b : Life) (P : Val → SPropS BoCa.Loc BoCa.Val b),
      (∃ ψ, o = some ψ ∧ IsMutSig ψ b P) ↔ (∃ ψ, o' = some ψ ∧ IsMutSig ψ b P))

/-- `↭` read at one location of the two flattenings. -/
theorem cellUpd_of_upd {ρ₁ ρ₂ σ₁ σ₂ : WRes} (h : ResU.Upd ρ₁ ρ₂)
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) (l : BoCa.Loc) :
    CellUpd (σ₁.get l) (σ₂.get l) := by
  refine ⟨fun s v χ hh => ?_, fun b P => ?_⟩
  · rw [← ResU.flatAt_iff h₁, ← ResU.flatAt_iff h₂]
    exact h.1 l s v χ hh
  · constructor
    · rintro ⟨ψ, hψ, v, χ, hh, hw, rfl⟩
      obtain ⟨v', χ', hh', hw', hg⟩ :=
        (h.2 l b P).mp ⟨v, χ, hh, hw, (ResU.flatAt_iff h₁ _ _).mpr hψ⟩
      exact ⟨_, (ResU.flatAt_iff h₂ _ _).mp hg, ⟨v', χ', hh', hw', rfl⟩⟩
    · rintro ⟨ψ, hψ, v, χ, hh, hw, rfl⟩
      obtain ⟨v', χ', hh', hw', hg⟩ :=
        (h.2 l b P).mpr ⟨v, χ, hh, hw, (ResU.flatAt_iff h₂ _ _).mpr hψ⟩
      exact ⟨_, (ResU.flatAt_iff h₁ _ _).mp hg, ⟨v', χ', hh', hw', rfl⟩⟩

/-- `CellUpd` is reflexive. -/
theorem CellUpd.refl (o : Option (CellU BoCa.Loc BoCa.Val)) : CellUpd o o :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- `(ρ₁ ● ρ₂) ● ρ₃` regrouped as `ρ₁ ● (ρ₂ ● ρ₃)`. -/
theorem compS_reassoc {a b c ab x : WRes} (h₁ : ResU.CompS a b ab)
    (h₂ : ResU.CompS ab c x) : ∃ bc, ResU.CompS b c bc ∧ ResU.CompS a bc x :=
  (ResU.CompS.assoc a b c x).mpr ⟨ab, h₁, h₂⟩

/-- `ρ₁ ● (ρ₂ ● ρ₃)` regrouped as `(ρ₁ ● ρ₂) ● ρ₃`. -/
theorem compS_reassoc' {a b c bc x : WRes} (h₁ : ResU.CompS b c bc)
    (h₂ : ResU.CompS a bc x) : ∃ ab, ResU.CompS a b ab ∧ ResU.CompS ab c x :=
  (ResU.CompS.assoc a b c x).mp ⟨bc, h₁, h₂⟩

/-- `(ρ₁ ● ρ₂) ● ρ₃ = (ρ₁ ● ρ₃) ● ρ₂`. -/
theorem compS_exch {a b c ab x : WRes} (h₁ : ResU.CompS a b ab)
    (h₂ : ResU.CompS ab c x) : ∃ ac, ResU.CompS a c ac ∧ ResU.CompS ac b x := by
  obtain ⟨bc, hbc, hx⟩ := compS_reassoc h₁ h₂
  exact compS_reassoc' (ResU.CompS.comm hbc) hx

/-- `ρ₁ ● (ρ₂ ● ρ₃) = ρ₂ ● (ρ₁ ● ρ₃)`. -/
theorem compS_lcomm {a b c bc x : WRes} (h₁ : ResU.CompS b c bc)
    (h₂ : ResU.CompS a bc x) : ∃ ac, ResU.CompS a c ac ∧ ResU.CompS b ac x := by
  obtain ⟨ab, hab, hx⟩ := compS_reassoc' h₁ h₂
  obtain ⟨ac, hac, hx'⟩ := compS_exch hab hx
  exact ⟨ac, hac, ResU.CompS.comm hx'⟩

/-- `∀v. P̂(v) ─⋆ Q̂(v)`, the ramification wand: `[TR]` 6.146 prints `(P̂ –⋆ Q̂)`
and H2 of its proof reads `(∀ (P̂ –⋆ Q̂))(ρ₂)`. -/
def wandAll (P Q : Val → WProp) : WProp := all fun v => wand (P v) (Q v)

end BoCa.Fig16.BoLo

end
