import Restrat.Composition

/-!
# Restrat — naturality of `@ρ`

`@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ` (row 5.11, `ResU.AtLife`, a greatest lower bound) moves to `e(@ρ)`:
`AtLife (e·ρ) (e a) ↔ AtLife ρ a` (`atLife_iff`), so `@(e·ρ) = e(@ρ)` (`at_relRU`).  The
greatest-lower-bound clause quantifies over every lifetime, not only moved ones; it holds at an
unmoved bound because a non-empty finite meet is attained (`atLife_attained`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16

namespace Emb
variable {c : Life} (e : Emb c) {Loc Val : Type}

/-- The meet of a non-empty resource is the lifetime of one of its cells; of the empty one, `⊤`. -/
theorem atLife_attained {ρ : ResU Loc Val} {a : Life} (h : ρ.AtLife a) :
    a = ⊤ ∨ ∃ l ψ, ρ.get l = some ψ ∧ ψ.at = a := by
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  -- every cell is strictly longer than `a`, so the next longer lifetime is a lower bound
  have hlt : ∀ l ψ, ρ.get l = some ψ → a < ψ.at := fun l ψ hl =>
    lt_of_le_of_ne (h.1 l ψ hl) (fun k => hne2 l ψ hl k.symm)
  have ha : 0 < OrderDual.ofDual a := by
    rcases Nat.eq_zero_or_pos (OrderDual.ofDual a) with h0 | h0
    · exact absurd (OrderDual.ofDual.injective (h0.trans rfl)) hne1
    · exact h0
  have hb := h.2 (OrderDual.toDual (OrderDual.ofDual a - 1)) fun l ψ hl => by
    have := hlt l ψ hl
    show OrderDual.ofDual ψ.at ≤ OrderDual.ofDual a - 1
    have : OrderDual.ofDual ψ.at < OrderDual.ofDual a := this
    omega
  have : OrderDual.ofDual a ≤ OrderDual.ofDual a - 1 := hb
  omega

theorem atLife_iff (ρ : ResU Loc Val) (a : Life) :
    (e.relRU ρ).AtLife (e a) ↔ ρ.AtLife a := by
  constructor
  · rintro ⟨hlb, hglb⟩
    refine ⟨fun l ψ hl => ?_, fun b hb => ?_⟩
    · have := hlb l (e.relU ψ) (by rw [relRU_get, hl]; rfl)
      rw [at_relU] at this
      exact e.le_iff.mp this
    · refine e.le_iff.mp (hglb (e b) fun l χ hχ => ?_)
      rw [relRU_get] at hχ
      obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hχ
      rw [at_relU]; exact e.le_iff.mpr (hb l ψ hψ)
  · intro h
    refine ⟨fun l χ hχ => ?_, fun b hb => ?_⟩
    · rw [relRU_get] at hχ
      obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hχ
      rw [at_relU]; exact e.le_iff.mpr (h.1 l ψ hψ)
    · rcases atLife_attained h with rfl | ⟨l, ψ, hψ, hat⟩
      · rw [e.map_top]; exact le_top
      · have := hb l (e.relU ψ) (by rw [relRU_get, hψ]; rfl)
        rwa [at_relU, hat] at this

theorem atLife_unique {ρ : ResU Loc Val} {a b : Life} (ha : ρ.AtLife a) (hb : ρ.AtLife b) :
    a = b :=
  le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

/-- `@(e·ρ) = e(@ρ)`. -/
theorem at_relRU (ρ : ResU Loc Val) : (e.relRU ρ).at = e ρ.at :=
  atLife_unique (Classical.choose_spec (e.relRU ρ).exists_atLife)
    ((e.atLife_iff ρ ρ.at).mpr (Classical.choose_spec ρ.exists_atLife))

end Emb

end Restrat
