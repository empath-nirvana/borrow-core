import Targets.B.Adequacy
import Targets.Base.Data

/-!
# System B — a closed program in Core's relation runs from every finite memory

B2 reads a closed program from the empty memory.  A program in Core's relation at the pure row, at
the empty resource, also runs from any memory with finitely many cells, under any allocator: the
frame of `wpG` is any world that lowers to the memory, and the world that owns every cell of the
memory is one (`ownWorld`).  It is built by `TW.alloc`, one cell at a time, at the frame `∅`
(`alloc_world`), so it is a `TW` world at no frame record.

* **`ownWorld`**: a memory with finitely many cells is the lowering of a `TW` world, valid, at no
  frame record.
* **`runs_of_rel`**: every run of a program in the relation at `F A` (the pure row, the empty
  resource), from a memory with finitely many cells, continues to a value in the relation at `A`;
  at `A = 1` that value is `()` (`runs_of_rel_unit`).

The memory the program runs from is the one a run of a whole program has reached, so the program's
own run reads only the cells it allocates: the world owning the rest is the frame, and `wpG`'s run
under the allocator that replays the given run continues it (`wpG_seg`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub)

/-! ### The world that owns a memory -/

/-- **A memory with finitely many cells is the lowering of a `TW` world** at no frame record:
the world that owns each cell, built by `TW.alloc` from `∅`. -/
theorem ownWorld_of_list :
    ∀ (d : List Loc) (μ : Heap), (∀ ℓ, μ ℓ ≠ none → ℓ ∈ d) →
      ∃ W : WRes, TW W [] [] ∧ ResU.Lower W μ ∧ ResU.Hash PMap.empty W
  | [], μ, hd => by
      have hμ : μ = fun _ => none := by
        funext ℓ
        by_contra h
        exact absurd (hd ℓ h) List.not_mem_nil
      subst hμ
      exact ⟨PMap.empty, TW.empty, lower_empty, hash_empty⟩
  | a :: d, μ, hd => by
      have hd' : ∀ ℓ, μ.del a ℓ ≠ none → ℓ ∈ d := by
        intro ℓ h
        by_cases hℓ : ℓ = a
        · subst hℓ; rw [Heap.del_same] at h; exact absurd rfl h
        · rw [Heap.del_other hℓ] at h
          rcases List.mem_cons.1 (hd ℓ h) with h' | h'
          · exact absurd h' hℓ
          · exact h'
      obtain ⟨W', hT', hlow', hh'⟩ := ownWorld_of_list d (μ.del a) hd'
      cases hμa : μ a with
      | none =>
          have : μ.del a = μ := by
            funext ℓ
            by_cases hℓ : ℓ = a
            · subst hℓ; rw [Heap.del_same, hμa]
            · rw [Heap.del_other hℓ]
          rw [this] at hlow'
          exact ⟨W', hT', hlow', hh'⟩
      | some v =>
          obtain ⟨x, σ', -, hfx, hσ', hT, hlow, -, -⟩ :=
            alloc_world (ρf := PMap.empty) (ps := []) (rs := []) v hh' (compS_empty_left W') hT'
              hlow' (Heap.del_same _ _)
          obtain rfl := eq_of_compS_empty_left hσ'
          have hup : (μ.del a).upd a v = μ := by
            funext ℓ
            by_cases hℓ : ℓ = a
            · subst hℓ; rw [Heap.upd_same, hμa]
            · rw [Heap.upd_other hℓ, Heap.del_other hℓ]
          rw [hup] at hlow
          exact ⟨σ', hT, hlow, hfx⟩

/-- **The world that owns a memory with finitely many cells.** -/
theorem ownWorld {μ : Heap} (h : FinDom μ) :
    ∃ W : WRes, TW W [] [] ∧ ResU.Lower W μ ∧ ResU.Hash PMap.empty W := by
  obtain ⟨d, hd⟩ := h
  exact ownWorld_of_list d μ hd

/-! ### Runs from a memory with finitely many cells -/

/-- **A program in the relation at `F A` runs to a value from every finite memory**: every run of
it, from a memory with finitely many cells, continues to a value in the relation at `A`.  The
memory's cells are `wpG`'s frame (`ownWorld`); the run is a prefix of `wpG`'s run under the
allocator that replays it (`wpG_seg`); the pure row allows no stop, so that run ends at a value. -/
theorem runs_of_rel {A : VTy} {e : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf [] A) [] LSub.empty e PMap.empty) {μ : Heap} (hfin : FinDom μ)
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) μ e μ₁ e₁) :
    ∃ (μ' : Heap) (v : Val), Steps (ℍ := ℍ) μ₁ e₁ μ' v.1 ∧
      ∃ (ls : List SRec) (ρ : WRes), vC true A ls LSub.empty v ρ := by
  obtain ⟨W, hT, hlow, hh⟩ := ownWorld hfin
  have hw := ewp_unfold (opTable_mono _) ((cC_effOf [] A [] LSub.empty e PMap.empty).mp h)
  have hirr : ∀ ls' t ρ', (valPost (fun ls v => vC true A ls LSub.empty v) ls' t ρ' ∨
      opTable (Row.tab [] LSub.empty) ls' t
        (fun ls e => ewpTS ls e (opTable (Row.tab [] LSub.empty))
          (fun ls v => vC true A ls LSub.empty v)) ρ') →
      ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂ := fun _ _ _ hp => post_irr hp
  obtain ⟨ρ', -, -, -, -, t, μ', -, ls', -, -, -, -, -, hrest, -, -, -, -, -, -, -, hΦ⟩ :=
    wpG_seg hw hirr (ResU.hash_symm hh) (ResU.comp_empty_right W) hT
      (fun x hx => absurd hx List.not_mem_nil) hlow hs
  rcases hΦ with ⟨v, rfl, hv⟩ | ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · exact ⟨μ', v, hrest, ls', ρ', hv⟩
  · obtain ⟨⟨-, -, hT', -⟩, -⟩ := pure_sep_iff.mp hp
    simp [Row.tab, Row.find] at hT'
  · obtain ⟨⟨-, -, hT', -⟩, -⟩ := pure_sep_iff.mp hp
    simp [Row.tab, Row.find] at hT'

/-- **At `F 1`, every run from a finite memory continues to `()`.** -/
theorem runs_of_rel_unit {e : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf [] .unit) [] LSub.empty e PMap.empty) {μ : Heap} (hfin : FinDom μ)
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) μ e μ₁ e₁) :
    ∃ μ' : Heap, Steps (ℍ := ℍ) μ₁ e₁ μ' Val.unit.1 := by
  obtain ⟨μ', v, hrest, ls, ρ, hv⟩ := runs_of_rel h hfin hs
  obtain ⟨-, hd⟩ := (vC_data (VTy.DataB.unit 0)).mp hv
  cases hd
  exact ⟨μ', hrest⟩

end Targets

end
