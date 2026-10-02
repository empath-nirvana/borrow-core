import Restrat.Composition

/-!
# Restrat — a re-stratification fixes everything above its cut

`relRU_of_inStratum`: if `ρ ∈ Res_c` (every borrow cell of `ρ` is strictly longer than the cut,
at every depth), then `e·ρ = ρ`.  This includes the stored invariants: a `mut` cell above the
cut stores `P̂ : Val → SProp_β` with `β ⊐ c`, and the image of `P̂` along a map that is the
identity on `Res_β` is `P̂`.

This is what L14.2 (`docs/effects-tr/14-stored-continuations.md`) needs of a frozen segment's
external footprint: it lies in `Res_c` at the cut `c`, so moving the internal lifetimes leaves it
unchanged, cell for cell, invariant for invariant.
-/

noncomputable section

namespace Restrat
open BoCa.Fig16

namespace Emb
variable {c : Life} (e : Emb c) {Loc Val : Type}

theorem mapL_of_lt {s : LSet} (h : c < s.meet) : e.mapL s = s := by
  refine lset_ext (fun y => ?_) (e.fix _ (le_of_lt (lt_of_lt_of_le h s.meet_le_join)))
    (e.fix _ (le_of_lt h))
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [e.fix x (le_of_lt (lt_of_lt_of_le h (s.meet_least x hx)))]
  · intro hy
    exact ⟨y, hy, e.fix y (le_of_lt (lt_of_lt_of_le h (s.meet_least y hy)))⟩

omit e in
theorem mutOf_congr' {b b' : Life} {v : Val} {ρ ρ' : ResU Loc Val}
    {h : ρ.InStratum b} {h' : ρ'.InStratum b'}
    {P : Val → SPropS Loc Val b} {P' : Val → SPropS Loc Val b'}
    {hP : P v ⟨ρ, h⟩} {hP' : P' v ⟨ρ', h'⟩} (eb : b = b') (eρ : ρ = ρ')
    (eP : ∀ (r : ResU Loc Val) (hr : r.InStratum b) (hr' : r.InStratum b') (w : Val),
        P w ⟨r, hr⟩ ↔ P' w ⟨r, hr'⟩) :
    CellU.mutOf b v ρ h P hP = CellU.mutOf b' v ρ' h' P' hP' := by
  subst eρ
  exact CellU.mutOf_congr eb v ρ h h' P P' hP hP' eP

/-- Above the cut, the action is the identity. -/
theorem relU_of_inStratum_aux : ∀ α : Life, c ≤ α →
    ∀ ψ : CellU Loc Val, ψ.InStratum α → e.relU ψ = ψ := by
  intro α
  induction α using (invImage OrderDual.ofDual Nat.lt_wfRel).wf.induction with
  | _ α ih =>
    intro hcα ψ hψ
    have resFix : ∀ β, α < β → c ≤ β → ∀ χ : ResU Loc Val, χ.InStratum β → e.relRU χ = χ := by
      intro β hβ hcβ χ hχ
      refine PMap.ext fun l => ?_
      rw [relRU_get]
      cases hl : χ.get l with
      | none => rfl
      | some φ => exact congrArg some (ih β hβ hcβ φ (hχ l φ hl))
    rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, h, rfl⟩ | ⟨b, v, χ, h, P, hw, rfl⟩
    · rfl
    · have hs : α < s.meet := hψ
      have hj : α < s.join := lt_of_lt_of_le hs s.meet_le_join
      have hχ : e.relRU χ = χ := resFix s.join hj (le_trans hcα (le_of_lt hj)) χ h
      rw [e.relU_immOf]
      exact CellU.immOf_congr (e.mapL_of_lt (lt_of_le_of_lt hcα hs)) rfl hχ _ _
    · have hb : α < b := hψ
      have hcb : c ≤ b := le_trans hcα (le_of_lt hb)
      have hχ : e.relRU χ = χ := resFix b hb hcb χ h
      rw [e.relU_mutOf]
      refine mutOf_congr' (e.fix b hcb) hχ fun r hr hr' w => ⟨?_, ?_⟩
      · rintro ⟨r₀, h₀, hP⟩
        have h₀' : e.relRU r₀.val = r := h₀
        rw [resFix b hb hcb r₀.val r₀.property] at h₀'
        have : r₀ = ⟨r, hr'⟩ := Subtype.ext h₀'
        rwa [← this]
      · intro hP
        exact ⟨⟨r, hr'⟩, resFix b hb hcb r hr', hP⟩

/-- A cell in `Cell_c` is fixed. -/
theorem relU_of_inStratum {ψ : CellU Loc Val} (h : ψ.InStratum c) : e.relU ψ = ψ :=
  e.relU_of_inStratum_aux c le_rfl ψ h

/-- `ρ ∈ Res_c ⇒ e·ρ = ρ`. -/
theorem relRU_of_inStratum {ρ : ResU Loc Val} (h : ρ.InStratum c) : e.relRU ρ = ρ := by
  refine PMap.ext fun l => ?_
  rw [relRU_get]
  cases hl : ρ.get l with
  | none => rfl
  | some φ => exact congrArg some (e.relU_of_inStratum (h l φ hl))

end Emb

end Restrat
