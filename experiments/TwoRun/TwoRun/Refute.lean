import TwoRun.Sim

/-!
# TwoRun — the forms of the every-run footprint that do not hold

`wpTS` exhibits one run.  `Sim.lean` carries its footprint to every *fresh* run, along an
injective renaming of the final heap.  Neither restriction can be dropped for every `wpTS`
term.  Both witnesses below mention a location literal and are not typed by `CDerives`; they
bound what follows from `wpTS` alone, not what holds of well-typed programs.

* **Without the renaming** (`not_everyRunFootprint`).  `alloc (free 0)`, lent the cell `0` as a
  `mut` cell, frees it and allocates a cell holding `()`.  The exhibited run allocates `0` again
  and ends where it started.  A fresh run that allocates `1` ends with `0` unallocated, and
  `Footprint`'s third clause fails.  So `EveryRunFootprint` (`FrameTheorems/EveryRun.lean`) does
  not hold, even at fresh runs; its image under the renaming `1 ↦ 0` does.
* **Without freshness** (`not_everyRunFootprintRen`).  `staleE` allocates `x`, frees it, allocates
  `y` and `z`, and branches on `load x`.  A run that reuses `x`'s location for `y` reads
  `inj₁ ()` and leaves the lent cell alone; one that reuses it for `z` reads `inj₂ ()` and frees
  the lent cell.  Both reach values.  The second run's final heap is empty, and no renaming of it
  keeps the lent cell allocated.  Both runs are stale: each allocates a location its
  configuration still names.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.TwoRun
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Core.FrameTheorems (Footprint EveryRunFootprint unitMutCell unitInv
  lent_unit_world flat_single_mut_empty lower_of_flat_factor)

/-! ### `wpTS` of a run that restores the heap -/

/-- A term that runs from every heap of every world completing `ρ` back to that heap satisfies
`wpTS` at every post-condition holding of `ρ`. -/
theorem wpTS_restore {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    {v : Val}
    (hrun : ∀ ρf fρ μ, ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
      Steps μ e μ (.val v))
    (hQ : Q ls v ρ) : wpTS ls e Q ρ := by
  intro ρf fρ ps hf hc hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  exact ⟨ρ, PMap.empty, fρ, fρ, ρ, v, μ, μ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), hμ,
    ResU.comp_empty_right fρ, hμ, hrun ρf fρ μ hf hc hμ, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-- The heap of a world is finite. -/
theorem lower_finite {Z : WRes} {μ : Heap} (hμ : ResU.Lower Z μ) :
    ∃ d : List Loc, ∀ l, μ l ≠ none → l ∈ d := by
  obtain ⟨σ, -, hval⟩ := hμ
  obtain ⟨d, hd⟩ := σ.finite
  exact ⟨d, fun l hl => hd l fun h => hl (by rw [hval l, h]; rfl)⟩

/-! ### The world lending cell `0` -/

/-- The resource `0 ↦ mut(α, (), ∅, 𝒱⟦1⟧)`. -/
abbrev lentRes (α : Life) : WRes := ResU.single 0 (unitMutCell α)

/-- The heap `0 ↦ ()`. -/
abbrev heap0 : Heap := BoLo.Heap.upd (fun _ => none) 0 .unit

theorem lentRes_flat (α : Life) : ResU.Flat (lentRes α) (lentRes α) :=
  flat_single_mut_empty 0 α .unit (ResU.inStratum_empty α) (unitInv α) ⟨rfl, rfl⟩

theorem lentRes_mut (α : Life) : ∃ ψ, (lentRes α).FlatAt 0 ψ ∧ ψ.kind = Kind.mut :=
  ⟨unitMutCell α, ⟨lentRes α, lentRes_flat α, ResU.single_get_self _ _⟩, rfl⟩

/-- Every heap of a world completing `lentRes α` holds `()` at `0`. -/
theorem lentRes_heap {α : Life} {ρf fρ : WRes} {μ : Heap} (hc : ResU.CompS ρf (lentRes α) fρ)
    (hμ : ResU.Lower fρ μ) : μ 0 = some .unit :=
  lower_of_flat_factor (ResU.CompS.comm hc) hμ (lentRes_flat α) (ResU.single_get_self _ _)

theorem lent_world (α : Life) : ∃ ps,
    ResU.Hash PMap.empty (lentRes α) ∧ ResU.CompS PMap.empty (lentRes α) (lentRes α) ∧
      TW (lentRes α) ps (rsOf []) ∧ Tagged (lentRes α) ps [] ∧ ResU.Lower (lentRes α) heap0 := by
  have : HostIs wasmHost := ⟨⟩
  obtain ⟨hf, fρ, ps, hc, hT, htg, hμ⟩ := (lent_unit_world (ℍ := wasmHost) default 0 α 0).2
  cases ResU.CompS.functional hc (ResU.comp_empty_left _)
  exact ⟨ps, hf, hc, hT, htg, hμ⟩

/-! ### `alloc (free 0)` -/

def allocE (e : Expr) : Expr := .app (.val (.prim .alloc)) e
def freeE (e : Expr) : Expr := .app (.val (.prim .free)) e
def loadE (e : Expr) : Expr := .app (.val (.prim .load)) e

/-- `alloc (free 0)`. -/
def reallocE : Expr := allocE (freeE (.val (.loc 0)))

theorem reallocE_runs {μ : Heap} (h0 : μ 0 = some .unit) {ℓ : Loc} (hℓ : BoLo.Heap.del μ 0 ℓ = none) :
    Steps μ reallocE (BoLo.Heap.upd (BoLo.Heap.del μ 0) ℓ .unit) (.val (.loc ℓ)) :=
  .more ⟨.appR (.val (.prim .alloc)) .hole, _, _, rfl, rfl, Head.free μ 0 .unit h0⟩
    (.one (Step1.head (Head.alloc _ .unit ℓ hℓ)))

theorem reallocE_wp (α : Life) (ls : List SRec) :
    wpTS ls reallocE (fun _ _ ρ' => ρ' = lentRes α) (lentRes α) := by
  refine wpTS_restore (v := .loc 0) (fun ρf fρ μ _ hc hμ => ?_) rfl
  have h0 := lentRes_heap hc hμ
  have e : BoLo.Heap.upd (BoLo.Heap.del μ 0) 0 .unit = μ := by
    funext k
    by_cases hk : k = 0
    · subst hk; rw [BoLo.Heap.upd_same, h0]
    · rw [BoLo.Heap.upd_other hk, BoLo.Heap.del_other hk]
  have := reallocE_runs h0 (ℓ := 0) (BoLo.Heap.del_same _ _)
  rwa [e] at this

/-- The run of `alloc (free 0)` from `0 ↦ ()` that allocates `1`.  It is fresh. -/
theorem reallocE_fresh1 :
    FreshRun heap0 reallocE (BoLo.Heap.upd (BoLo.Heap.del heap0 0) 1 .unit) (.val (.loc 1)) := by
  refine .more ⟨⟨.appR (.val (.prim .alloc)) .hole, _, _, rfl, rfl,
    Head.free heap0 0 .unit (BoLo.Heap.upd_same _ _ _),
      BoLo.not_arrRedex_prim (by decide) _⟩, fun ℓ h₁ h₂ => ?_⟩ (.more
      ⟨⟨.hole, _, _, rfl, rfl, Head.alloc _ .unit 1 (by simp [BoLo.Heap.del]),
        BoLo.not_arrRedex_prim (by decide) _⟩, fun ℓ h₁ h₂ => ?_⟩ (.refl _ _))
  · exact absurd h₂ (by
      by_cases hk : ℓ = 0
      · subst hk; simp at h₁
      · rw [BoLo.Heap.del_other hk] at h₁; exact h₁)
  · rintro (h | h | ⟨k, w, hk, hw⟩)
    · exact h h₂
    · simp [Expr.Occ, BoLo.Kont.plug, Val.unit, Val.prim] at h
    · by_cases hk0 : k = 0
      · subst hk0; simp at hk
      · simp [BoLo.Heap.del, hk0] at hk

/-- **`EveryRunFootprint` does not hold**, at a fresh run of a term outside the calculus. -/
theorem not_everyRunFootprint : ¬ EveryRunFootprint := by
  intro h
  obtain ⟨ps, hf, hc, hT, htg, hμ⟩ := lent_world (OrderDual.toDual 0)
  have := h [] reallocE _ _ _ _ _ _ _ _ (reallocE_wp _ []) hf hc hT htg hμ
    reallocE_fresh1.toSteps
  obtain ⟨ψ, hψ, hk⟩ := lentRes_mut (OrderDual.toDual 0)
  exact this.2.2 0 ψ hψ hk (by simp [BoLo.Heap.upd, BoLo.Heap.del])

/-! ### A stale run -/

/-- `let x = alloc () in let _ = free x in let y = alloc (inj₁ ()) in let z = alloc (inj₂ ()) in
let _ = case (load x) {inj₁ _. () | inj₂ _. free 0} in let _ = free y in free z`. -/
def staleE : Expr :=
  elet (allocE unit')
    (elet (freeE (.var 0))
      (elet (allocE (.val (.inj₁ .unit)))
        (elet (allocE (.val (.inj₂ .unit)))
          (elet (.case (loadE (.var 3)) unit' (freeE (.val (.loc 0))))
            (elet (freeE (.var 2)) (freeE (.var 2)))))))

theorem steps_elet {μ μ₁ μ₂ : Heap} {e body e' : Expr} {v : Val} (h₁ : Steps μ e μ₁ (.val v))
    (h₂ : Steps μ₁ (body.subst 0 v) μ₂ e') : Steps μ (elet e body) μ₂ e' :=
  (Steps.plug (.appR (.val (.lam body)) .hole) h₁).trans (.more (Step1.head (.beta _ body v)) h₂)

theorem steps_head {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a') : Steps μ a μ' a' :=
  .one (Step1.head h)

/-- The run of `staleE` that allocates `x` at `ℓx`, `y` at `ℓy` and `z` at `ℓz`, when `load x`
reads `r` and the branch it selects runs to `()`. -/
theorem staleE_runs {μ μc : Heap} {ℓx ℓy ℓz : Loc} {r : Val} (hx : μ ℓx = none)
    (hy : BoLo.Heap.del (BoLo.Heap.upd μ ℓx .unit) ℓx ℓy = none)
    (hz : BoLo.Heap.upd (BoLo.Heap.del (BoLo.Heap.upd μ ℓx .unit) ℓx) ℓy (.inj₁ .unit) ℓz = none)
    (hr : BoLo.Heap.upd (BoLo.Heap.upd (BoLo.Heap.del (BoLo.Heap.upd μ ℓx .unit) ℓx) ℓy
      (.inj₁ .unit)) ℓz (.inj₂ .unit) ℓx = some r)
    (hc : Steps (BoLo.Heap.upd (BoLo.Heap.upd (BoLo.Heap.del (BoLo.Heap.upd μ ℓx .unit) ℓx) ℓy
      (.inj₁ .unit)) ℓz (.inj₂ .unit)) (.case (.val r) unit' (freeE (.val (.loc 0)))) μc unit')
    {μy w : Val} (hμy : μc ℓy = some μy) (hμz : BoLo.Heap.del μc ℓy ℓz = some w) :
    Steps μ staleE (BoLo.Heap.del (BoLo.Heap.del μc ℓy) ℓz) (.val w) := by
  refine steps_elet (steps_head (.alloc _ .unit ℓx hx)) ?_
  refine steps_elet (steps_head (.free _ ℓx .unit (BoLo.Heap.upd_same _ _ _))) ?_
  refine steps_elet (steps_head (.alloc _ (.inj₁ .unit) ℓy hy)) ?_
  refine steps_elet (steps_head (.alloc _ (.inj₂ .unit) ℓz hz)) ?_
  refine steps_elet (v := .unit) ((Steps.plug (.case .hole unit' (freeE (.val (.loc 0))))
    (steps_head (.load _ ℓx r hr))).trans hc) ?_
  refine steps_elet (steps_head (.free _ ℓy μy hμy)) ?_
  exact steps_head (.free _ ℓz w hμz)

/-- From a heap holding `()` at `0`, `staleE` runs back to the heap when `y` reuses `x`'s
location: `load x` reads `inj₁ ()`. -/
theorem staleE_restores {μ : Heap} {ℓ ℓ' : Loc} (hℓ : μ ℓ = none) (hℓ' : μ ℓ' = none)
    (hne : ℓ' ≠ ℓ) : Steps μ staleE μ (.val (.inj₂ .unit)) := by
  have e := staleE_runs (μ := μ) (ℓx := ℓ) (ℓy := ℓ) (ℓz := ℓ') (r := .inj₁ .unit) hℓ
    (by simp) (by simp [BoLo.Heap.upd, BoLo.Heap.del, hne, hℓ'])
    (by simp [BoLo.Heap.upd, hne.symm]) (steps_head (.case₁ _ .unit unit' _))
    (μy := .inj₁ .unit) (w := .inj₂ .unit) (by simp [BoLo.Heap.upd, hne.symm])
    (by simp [BoLo.Heap.upd, BoLo.Heap.del, hne])
  convert e using 1
  funext k
  by_cases h₁ : k = ℓ
  · subst h₁; simp [BoLo.Heap.del, hℓ, hne.symm]
  by_cases h₂ : k = ℓ'
  · subst h₂; simp [BoLo.Heap.del, hℓ']
  simp [BoLo.Heap.upd, BoLo.Heap.del, h₁, h₂]

theorem staleE_wp (α : Life) (ls : List SRec) :
    wpTS ls staleE (fun _ _ ρ' => ρ' = lentRes α) (lentRes α) := by
  refine wpTS_restore (v := .inj₂ .unit) (fun ρf fρ μ _ _ hμ => ?_) rfl
  obtain ⟨d, hd⟩ := lower_finite hμ
  obtain ⟨ℓ, hℓ⟩ := loc_infinite d
  obtain ⟨ℓ', hℓ'⟩ := loc_infinite (ℓ :: d)
  have fresh : ∀ {k}, k ∉ d → μ k = none := fun {k} hk => by
    by_contra h; exact hk (hd k h)
  exact staleE_restores (fresh hℓ) (fresh fun h => hℓ' (List.mem_cons_of_mem _ h))
    (fun h => hℓ' (h ▸ List.mem_cons_self))

/-- From `0 ↦ ()`, the run of `staleE` that allocates `x` at `1`, `y` at `2` and `z` at `1`:
`load x` reads `inj₂ ()`, and the run frees `0`. -/
theorem staleE_frees :
    ∃ μR : Heap, Steps heap0 staleE μR (.val (.inj₂ .unit)) ∧ ∀ k, μR k = none := by
  refine ⟨_, staleE_runs (μ := heap0) (ℓx := 1) (ℓy := 2) (ℓz := 1) (r := .inj₂ .unit)
    (by simp) (by simp [BoLo.Heap.upd, BoLo.Heap.del])
    (by simp [BoLo.Heap.upd, BoLo.Heap.del]) (by simp [BoLo.Heap.upd])
    ((steps_head (.case₂ _ .unit unit' _)).trans (steps_head (.free _ 0 .unit
      (by simp [BoLo.Heap.upd]))))
    (μy := .inj₁ .unit) (w := .inj₂ .unit) (by simp [BoLo.Heap.upd, BoLo.Heap.del])
    (by simp [BoLo.Heap.upd, BoLo.Heap.del]), fun k => ?_⟩
  by_cases h₀ : k = 0
  · subst h₀; simp [BoLo.Heap.del]
  by_cases h₁ : k = 1
  · subst h₁; simp [BoLo.Heap.del]
  by_cases h₂ : k = 2
  · subst h₂; simp [BoLo.Heap.del]
  simp [BoLo.Heap.upd, BoLo.Heap.del, h₀, h₁, h₂]

/-- The footprint on every run, up to an injective renaming of the final heap: the form
`everyFreshRunFootprint` proves for fresh runs. -/
def EveryRunFootprintRen : Prop :=
  ∀ (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ ρf fρ : WRes)
    (ps : List FrameRec) (μ μR : Heap) (w : Val),
    wpTS ls e Q ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Lower fρ μ → Steps μ e μR w.1 →
    ∃ g : Loc → Loc, Set.InjOn g {x | μR x ≠ none} ∧ Footprint ρf ρ μ (Heap.push g μR)

/-- **`EveryRunFootprintRen` does not hold**, at a stale run of a term outside the calculus. -/
theorem not_everyRunFootprintRen : ¬ EveryRunFootprintRen := by
  intro h
  obtain ⟨ps, hf, hc, hT, htg, hμ⟩ := lent_world (OrderDual.toDual 0)
  obtain ⟨μR, hrun, hnone⟩ := staleE_frees
  obtain ⟨g, -, hfp⟩ := h [] staleE _ _ _ _ _ _ _ (.inj₂ .unit) (staleE_wp _ []) hf hc hT htg hμ
    hrun
  obtain ⟨ψ, hψ, hk⟩ := lentRes_mut (OrderDual.toDual 0)
  refine hfp.2.2 0 ψ hψ hk ?_
  simp only [Heap.push]
  rw [dif_neg]
  rintro ⟨x, hx, -⟩
  exact hx (hnone x)

end BoCa.Fig16.LogRel.Core.TwoRun

end
