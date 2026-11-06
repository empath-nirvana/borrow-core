import Core.Chain.SI.LocTy

/-!
# `perLocShape_not_reborrow`'s configuration at the per-lend world  `[spec §62]`

The world is `Core/Chain/SI/LocTy.lean`; the design is `docs/new-core/scope-791-loctype.md`.
`Shape791N.perLocShape_not_reborrow` is a value of the per-location reading of `Mut` that is not
one after a reborrow of an unrelated location. Here the same value is one of the interpretation's
`Mut` (`mutL`, over the per-lend world) before and after the reborrow
(`perLocShape_lend_reborrow`, L2 (c)).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.PerLendShape791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI

/-- `𝒱⟦1⟧`'s family at any lifetime. -/
def famUnit (β : Life) : Nat → Val → SPropS Loc Val β := fun _ u r => u = Val.unit ∧ r.1 = PMap.empty

/-- The inner cell `ℓ₂ ↦ mut(β, (), ∅, 𝒱⟦1⟧)`. -/
def innerCell (l₂ : Loc) (β : Life) : WRes :=
  ResU.single l₂ (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) (famUnit β 0)
    ⟨rfl, rfl⟩)

theorem innerCell_inStratum (l₂ : Loc) {b β : Life} (hbβ : b < β) :
    (innerCell l₂ β).InStratum b :=
  ResU.inStratum_single l₂ ((CellU.inStratum_mutOf b β _ _ _ _ _).mpr hbβ)

/-! ### L2 (c): `perLocShape_not_reborrow`'s configuration, per lend -/

/-- `𝒱⟦1⟧`. -/
def unitL : CPredL := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty

theorem famL_unit (b : Life) (Θ : LocTy) : famL b unitL Θ = famUnit b := rfl

/-- `ℓ` and `ℓ₂` lent at `β` with `𝒱⟦1⟧`'s family. -/
def W₁ (l l₂ : Loc) (β : Life) : LocTy :=
  ⟨fun x b => if (x = l ∨ x = l₂) ∧ b = β then some (famUnit b) else none, []⟩

/-- …and `ℓ_b` lent at `b` with `𝒱⟦Mut @β 1⟧`'s, read above `b`. -/
def Wc (l l₂ lb : Loc) (b β : Life) : LocTy :=
  ⟨fun x a => if x = lb ∧ a = b then some (famL a (mutL β unitL) (W₁ l l₂ β)) else W₁ l l₂ β x a,
    []⟩

theorem Wc_above (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) (b β : Life) :
    (Wc l l₂ lb b β).above b = (W₁ l l₂ β).above b := by
  refine LocTy.ext' (fun x a => ?_) rfl
  simp only [LocTy.above_apply, Wc, LocTy.mk_apply]
  by_cases h : x = lb ∧ a = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

theorem Wc_fresh (l l₂ lb : Loc) {α b β : Life} (hαb : α < b) (hbβ : b < β) :
    (Wc l l₂ lb b β).Fresh α := by
  intro x a ha
  simp only [Wc, W₁, LocTy.mk_apply] at ha
  by_cases h : x = lb ∧ a = b
  · rw [h.2]; exact hαb
  · rw [if_neg h] at ha
    by_cases h' : (x = l ∨ x = l₂) ∧ a = β
    · rw [h'.2]; exact lt_trans hαb hbβ
    · exact absurd (if_neg h') ha

/-- **`perLocShape_not_reborrow`'s configuration holds per lend.** The same value (a `Mut @b
(Mut @β 1)` at `ℓ_b`, its content a `Mut @β 1` at `ℓ₂`, holding nothing at `ℓ`) is one of Core's
shape at `Wc` and at `Wc` with `ℓ` lent at any `α < b < β` with any family: the per-location
typing loses `ℓ` above `b` (`Shape791N.perLocShape_not_reborrow`), the per-lend typing keeps it. -/
theorem perLocShape_lend_reborrow (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) {α b β : Life}
    (hαb : α < b) (hbβ : b < β) (F : Nat → Val → SPropS Loc Val α) :
    ∃ (v : Val) (ρ : WRes),
      (∀ x ψ, ρ.get x = some ψ → x ≠ l) ∧
      mutL b (mutL β unitL) (Wc l l₂ lb b β) 0 v ρ ∧
      mutL b (mutL β unitL) ((Wc l l₂ lb b β).add l α F) 0 v ρ := by
  have hfam : famL b (mutL β unitL) (Wc l l₂ lb b β) = famL b (mutL β unitL) (W₁ l l₂ β) := by
    funext j u r
    simp only [famL, Wc_above l l₂ lb hl hl₂ b β]
  -- the content: `ℓ₂ ↦ mut(β, (), ∅, 𝒱⟦1⟧)`, typed at `W₁` above `b`
  have hin : mutL β unitL ((W₁ l l₂ β).above b) 0 (Val.loc l₂) (innerCell l₂ β) := by
    refine ⟨l₂, Val.unit, PMap.empty, ResU.inStratum_empty β, 0, ⟨rfl, rfl⟩, le_rfl, rfl, ?_, rfl⟩
    simp [LocTy.above_apply, W₁, hbβ, famL_unit]
  have hw : famL b (mutL β unitL) (Wc l l₂ lb b β) 0 (Val.loc l₂)
      ⟨innerCell l₂ β, innerCell_inStratum l₂ hbβ⟩ := by
    rw [hfam]; exact hin
  have hv : mutL b (mutL β unitL) (Wc l l₂ lb b β) 0 (Val.loc lb)
      (ResU.single lb (CellU.mutOf b (Val.loc l₂) (innerCell l₂ β)
        (innerCell_inStratum l₂ hbβ) _ hw)) := by
    refine ⟨lb, _, _, _, 0, hw, le_rfl, rfl, ?_, rfl⟩
    rw [hfam]
    simp only [Wc, LocTy.mk_apply, and_self, if_true]
  refine ⟨_, _, fun x ψ hx => ?_, hv, mutL_add (Wc_fresh l l₂ lb hαb hbβ) l F hv⟩
  by_cases h : x = lb
  · rw [h]; exact hl
  · rw [ResU.single_get_ne _ h] at hx; exact absurd hx (by simp)

end BoCa.Fig16.LogRel.Core.Chain.SI.PerLendShape791

end
