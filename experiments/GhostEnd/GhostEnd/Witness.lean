import Restrat.MutCounterexample
import Restrat.Reborrow

/-!
# GhostEnd — `mut_not_natural`'s witness under freeze and re-lend

`Restrat.MutCounterexample` moves the cell `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧_δ)`
by `e = shift ⊤ 1`. The moved cell stores the image of `𝒱⟦Imm 'b 1⟧_δ`, which rejects the gap
resource `ℓ′ ↦ imm({1}, (), ∅)`, so `𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}` fails there.

Freeze never moves that cell. Its lifetime `2` is below the cut, so it is internal, and freezing
leaves `ℓ ↦ own(ℓ′) ● ℓ′ ↦ imm({1}, (), ∅)`, the shape 6.65's exit hands back. The move then
reaches only the payload: `e·(ℓ′ ↦ imm({1}, (), ∅)) = ℓ′ ↦ imm({2}, (), ∅)` (`moved_payload`). The
re-lend builds a **new** cell over that payload whose stored predicate is `𝒱⟦Imm 'b 1⟧_{e∘δ}`
itself, so `P̂` is never moved.

* `relent_holds`: the re-lent cell is in `𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}`. This is `fails`'s
  conclusion, now holding.
* `gap_accepted`: the gap resource that defeats the moved cell satisfies the re-lent cell's
  predicate.

Whether `ρ₀` with these numerals arises in a run is not checked here. The route never asks: a cell
below the cut is ghost-ended before any move, and a cell above it is fixed (`relRU_of_inStratum`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd.Witness
open BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel
open BoCa.Lifetime (LSub LifeVar)
open Restrat Restrat.MutCounterexample

/-- The frozen payload, moved: `e·(ℓ′ ↦ imm({1}, (), ∅)) = ℓ′ ↦ imm({2}, (), ∅)`. -/
theorem moved_payload : e.relRU (ResU.single ℓ' (immCell 1)) = ResU.single ℓ' (immCell 2) := by
  have key : ∀ (s s' : LSet) (ρ ρ' : WRes) (h : ρ.InStratum s.join)
      (h' : ρ'.InStratum s'.join), s = s' → ρ = ρ' →
      CellU.immOf s BoCa.Val.unit ρ h = CellU.immOf s' BoCa.Val.unit ρ' h' := by
    rintro s _ ρ _ h h' rfl rfl; rfl
  rw [e.relRU_single]
  congr 1
  unfold immCell
  rw [e.relU_immOf]
  exact key _ _ _ _ _ _ (by rw [e.mapL_singleton]; rfl) e.relRU_empty

/-- `𝒱⟦Imm 'b 1⟧_{e∘δ}` lies in `Res_3`. -/
theorem vS'_supported (w : BoCa.Val) (r : WRes) (h : vDen S (LSub.mapN e.toNat δ) w r) :
    r.InStratum (L 3) := by
  obtain ⟨α, hα, ℓ₀, hk⟩ := h
  have hα' : α = L 2 := Option.some.inj hα.symm
  obtain ⟨-, s, u, σ, hσ, rfl, -, hle⟩ := pure_sep_iff.mp hk
  refine ResU.inStratum_single _ ?_
  show L 3 < s.meet
  rw [hα'] at hle
  exact lt_of_lt_of_le (L_lt (by norm_num)) hle

/-- The re-lent cell's predicate: `𝒱⟦Imm 'b 1⟧_{e∘δ}`, not the image of `𝒱⟦Imm 'b 1⟧_δ`. -/
def Q' : BoCa.Val → SPropS BoCa.Loc BoCa.Val (L 3) :=
  fun v => SPropU.toS (L 3) (vDen S (LSub.mapN e.toNat δ) v)

theorem ofS_Q' : ofS Q' = vDen S (LSub.mapN e.toNat δ) := by
  funext v r
  apply propext
  constructor
  · rintro ⟨_, hS⟩; exact hS
  · intro hS; exact ⟨vS'_supported v r hS, hS⟩

theorem σ'_in : (ResU.single ℓ' (immCell 2) : WRes).InStratum (L 3) :=
  ResU.inStratum_single _ (show L 3 < L 2 from L_lt (by norm_num))

theorem hw' : Q' (.loc ℓ') ⟨ResU.single ℓ' (immCell 2), σ'_in⟩ :=
  vS_holds (θ := LSub.mapN e.toNat δ) (m := 2) rfl le_rfl

/-- The re-lent cell: `ℓ ↦ mut(3, ℓ′, e·(ℓ′ ↦ imm({1}, (), ∅)), 𝒱⟦Imm 'b 1⟧_{e∘δ})`. -/
def ρ₁ : WRes :=
  ResU.single ℓ (CellU.mutOf (L 3) (.loc ℓ') (ResU.single ℓ' (immCell 2)) σ'_in Q' hw')

/-- **Freeze, move, re-lend** repairs the witness: the re-lent cell is in
`𝒱⟦Mut 'a (Imm 'b 1)⟧_{e∘δ}`, where the moved cell is not (`fails`). -/
theorem relent_holds : vDen T (LSub.mapN e.toNat δ) (.loc ℓ) ρ₁ := by
  refine ⟨L 4, rfl, ℓ, pure_sep_mk rfl ?_⟩
  exact ⟨L 3, .loc ℓ', _, σ'_in, Q', hw', L_le (by norm_num), rfl, ofS_Q'⟩

/-- The gap resource that defeats the moved cell satisfies the re-lent cell's predicate. -/
theorem gap_accepted : ofS Q' (.loc ℓ') (ResU.single ℓ' (immCell 1)) := by
  rw [ofS_Q']
  exact vS_holds (θ := LSub.mapN e.toNat δ) (m := 2) rfl (by norm_num)

end GhostEnd.Witness
