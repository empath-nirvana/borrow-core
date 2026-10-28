import Lowering.BigStep
import Lowering.Obligations

/-!
# Lowering — a run under the LIR's allocator  `[spec §56]`

The relation's `wp` asks for a run under every allocator (`Core/Alloc.lean`, SPEC §13). The print
keeps the source's memory (`Lowering/LIRPrint.lean`), and its allocations are the LIR's: the
`c`-th at the region base `16 + c · regionSize` (`Op.cellNew`, `Op.cellsNew`). `bumpAlloc` is
the allocator that answers that base wherever it is free, so a run under it is one the LIR
follows at the same locations. `arun_of_sem`: a closed `F 1` term in the relation has a run under
it from the empty memory to `()` at the empty memory.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Alloc ARun)
open BoCa.Lifetime (LSub LifeCtx)

/-- The base of the `c`-th region: the LIR's `next` after `c` allocations. -/
@[irreducible] def regionBase (c : Nat) : Nat := 16 + c * Backend2.regionSize

open Classical in
/-- **The LIR's allocator**: the `c`-th allocation at the base of the `c`-th region, wherever that
block is free, else the least free block. -/
def bumpAlloc : Alloc where
  pick c μ n := if ∀ i, i < n → μ (regionBase c + i) = none then regionBase c
    else Alloc.leastFree.pick c μ n
  fresh c μ n hfin i hi := by
    split
    · next h => exact h i hi
    · exact Alloc.leastFree.fresh c μ n hfin i hi

theorem bumpAlloc_pick {c : Nat} {μ : Heap} {n : Nat}
    (h : ∀ i, i < n → μ (regionBase c + i) = none) : bumpAlloc.pick c μ n = regionBase c := by
  simp only [bumpAlloc, if_pos h]

/-- A term whose `wp` at the empty resource lands in `P` has, under any allocator, a run from the
empty memory to a value at which `P` holds, at the empty memory (as `theorem32D`). -/
theorem arun_of_wp (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes)) (A : Alloc) :
    ∃ c' v, ARun (ℍ := ℍ) A 0 Adequacy.emptyMem e c' Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', -, -, h1, h2, h3, hlow, h6, h7, ⟨c', hrun⟩, h9, h10, h11,
    -, -, -, -, h12⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg A 0
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional hlow Fig16.BoLo.lower_empty
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨c', v, hrun, hPv⟩

/-- **A closed `F 1` term in the relation runs under every allocator** from the empty memory to
`()` at the empty memory. -/
theorem arun_of_sem {e : Expr} (hsem : SemC (ℍ := ℍ) LifeCtx.empty [] e (.ret .unit))
    (A : Alloc) : ∃ c', ARun (ℍ := ℍ) A 0 Adequacy.emptyMem e c' Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have he : substAll [] e = e := Adequacy.psub_nil 0 _
  rw [he] at hwp
  obtain ⟨c', v, h, rfl⟩ := arun_of_wp (ℍ := ℍ) e (· = Val.unit) hwp A
  exact ⟨c', h⟩

end Lowering
