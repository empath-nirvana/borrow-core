import Paper.S6_1_StandardLemmas.Lemmas
import Support.LogicalRelation.Facts
import Support.Model.Singletons
/-!
# Check: an existentially packed environment does not link image to escrow

A closure's typed reborrow image needs every cell of it to sit over a cell of the
escrow, from the two shapes alone.  If an `unr` closure's shape packs its environment
existentially, `∃ E w, S E δ w ρ`, the image and the escrow choose `E` and `w`
independently.  For any shape family agreeing with `vShape` at `1` and `Ref`, there are an
image and an escrow both of that shape with a cell in the image over nothing in the escrow.
-/

namespace BoCa.Fig16.LogRel
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub)

theorem envShape_unlinked (S : Ty → LSub → Val → WProp)
    (hu : ∀ δ v, S .unit δ v = ⌜v = .unit⌝)
    (hr : ∀ δ v T, S (.ref T) δ v =
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ S T δ v')
    (δ : LSub) :
    ∃ (c R : WRes) (m : BoCa.Loc) (ψ : CellU BoCa.Loc BoCa.Val),
      (∃ E w, S E δ w c) ∧ (∃ E w, S E δ w R) ∧ c.get m = some ψ ∧ R.get m = none := by
  refine ⟨ResU.single 0 (CellU.ownOf .unit), PMap.empty, 0, CellU.ownOf .unit,
    ⟨.ref .unit, .loc 0, ?_⟩, ⟨.unit, .unit, ?_⟩, ResU.single_get_self _ _, PMap.empty_get _⟩
  · rw [hr]
    refine ⟨0, .unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩⟩
    rw [hu]; exact ⟨rfl, rfl⟩
  · rw [hu]; exact ⟨rfl, rfl⟩

/-- Fixing the environment's type in the arrow does not link them either: the environment
*value* is still chosen independently. -/
theorem envValue_unlinked (S : Ty → LSub → Val → WProp)
    (hu : ∀ δ v, S .unit δ v = ⌜v = .unit⌝)
    (hr : ∀ δ v T, S (.ref T) δ v =
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ S T δ v')
    (δ : LSub) :
    ∃ (c R : WRes) (m : BoCa.Loc) (ψ : CellU BoCa.Loc BoCa.Val),
      (∃ w, S (.ref .unit) δ w c) ∧ (∃ w, S (.ref .unit) δ w R) ∧
        c.get m = some ψ ∧ R.get m = none := by
  have mk : ∀ n : BoCa.Loc, S (.ref .unit) δ (.loc n) (ResU.single n (CellU.ownOf .unit)) := by
    intro n
    rw [hr]
    refine ⟨n, .unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩⟩
    rw [hu]; exact ⟨rfl, rfl⟩
  exact ⟨_, _, 0, _, ⟨_, mk 0⟩, ⟨_, mk 1⟩, ResU.single_get_self _ _,
    ResU.single_get_ne _ (by decide)⟩

end BoCa.Fig16.LogRel
