import ProbeD1.Gap

/-!
# ProbeD1 — Core's `∀` reads the room between lifetimes (`GAP.md` §3c)

Core's `∀` clause (`Core/Relation.lean`, `cC` at `.all`) is the printed one ([TR] p. 4, row 4.5;
[CONF] p. 415:12), over the printed `Life = ℕᵒᵈ`: it quantifies over every lifetime strictly
below the bound. Its body may compare the bound variable non-strictly with a cell (`ptoMutS`'s
`α ⊑ b`). So the clause can hold because no lifetime lies strictly between two lifetimes in play,
and fail at a configuration of the same order type that leaves room there.

The witness, at `∀'0 ⊏ ⊤. F (Mut '0 1)` and the value `Λ. return ℓ₀`:

* at the resource `ℓ₀ ↦ mut(1, (), ∅, 𝒱⟦1⟧)` the clause holds (`adj_holds`): every `α ⊏ ⊤` is
  `⊑ 1`, since `1` is adjacent to `⊤ = 0`;
* at any single `mut` cell at `2` with an empty witness it fails (`adj_fails`): `α = 1` is below
  `⊤` and not `⊑ 2`, and a run's `↭` keeps the cell's lifetime (`pvLocal`, `ResU.UpdMut`);
* the two resources have the same order type, `⊤ ⊐ 1` and `⊤ ⊐ 2`; the re-stratification
  `shift ⊤ 1` carries the first to a cell of the second shape (`adj_relRU`), so Core's relation is
  not invariant under it (`coreAllNotNatural`);
* hence Core's `∀` does not imply the full position-`∀` (`CutAllC`: the clause at every renaming
  of the configuration by an embedding fixing `⊤`) at `σ = []` (`not_coreAllImpCutAll`).

The value is not claimed to be derivable, and no target of the probe is refuted here: the witness
is the reason the design (`GAP.md`) does not rely on Core's relation being invariant under an
embedding that opens a gap.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (innerView unitQ unitQ_holds innerView_ptoMutS)

/-! ### The clause holds at the cell adjacent to `⊤` -/

/-- The inner view stores `𝒱⟦1⟧` for every index at or below its lifetime. -/
theorem ptoMutS_innerView_le {k : BoCa.Loc} {αy α : Life} (h : α ≤ αy) (ls : List SRec)
    (δ' : LSub) : ptoMutS k α ls (fun ls₀ => vC true .unit ls₀ δ') (innerView k αy) := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hle, hρ, hQ, hmem, hsupp⟩ := innerView_ptoMutS k αy ls δ'
  exact ⟨b, u, σ, hσ, Q, hw, ls₀, le_trans h hle, hρ, hQ, hmem, hsupp⟩

theorem adj_subst : Expr.subst 0 Val.unit (.val (Val.loc 0) : Expr) = .val (Val.loc 0) := by
  simp [Expr.subst]

/-- Every lifetime strictly below `⊤` is at or below `1`. -/
theorem le_one_of_lt_top {α : Life} (h : α < OrderDual.toDual (0 : ℕ)) : α ≤ lifeN 1 := by
  have h' : 0 < OrderDual.ofDual α := h
  show 1 ≤ OrderDual.ofDual α
  omega

/-- **At `ℓ₀ ↦ mut(1, (), ∅, 𝒱⟦1⟧)` the clause holds**: `1` is adjacent to `⊤`. -/
theorem adj_holds : cC (ℍ := ℍ) adjC [] adjδ adjE (innerView 0 (lifeN 1)) := by
  intro α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β, hβ, hlt⟩ := hp
  obtain rfl : β = Lifetime.SLife.top := Option.some.inj hβ.symm
  have hρ₂ : ρ₂ = innerView 0 (lifeN 1) := ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine wpTS_lolli [] (.val (Val.loc 0)) Val.unit _ _ ?_
  rw [adj_subst]
  refine wpTS_val [] (Val.loc 0) _ _ ?_
  exact ⟨α, rfl, 0, pure_sep_mk rfl (ptoMutS_innerView_le (le_one_of_lt_top hlt) [] _)⟩

/-! ### The clause fails at a cell at `2` -/

/-- A single `mut` cell with an empty witness is its own flattening. -/
theorem flat_single_mut_empty {k : BoCa.Loc} {b : Life} {u : Val}
    {h : ResU.InStratum b (PMap.empty : WRes)} {Q : Val → SPropS BoCa.Loc Val b}
    {hw : Q u ⟨PMap.empty, h⟩} :
    ResU.Flat (ResU.single k (CellU.mutOf b u PMap.empty h Q hw))
      (ResU.single k (CellU.mutOf b u PMap.empty h Q hw)) :=
  ⟨_, PMap.empty, ExW.single_mut BoLo.exW_empty (ResU.comp_empty_right _),
    AgW.single_mut BoLo.agW_empty, ResU.comp_empty_right _⟩

/-- Its world: `alloc` the place, then `mutFold` it. -/
theorem tw_single_mut_empty {b : Life} {h : ResU.InStratum b (PMap.empty : WRes)}
    {Q : Val → SPropS BoCa.Loc Val b} (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    TW (ResU.single 0 (CellU.mutOf b Val.unit PMap.empty h Q hw)) [] [] := by
  have h₁ : TW (ResU.single 0 (CellU.ownOf Val.unit)) [] [] :=
    TW.alloc TW.empty lower_empty rfl (ResU.comp_empty_left _) (ResU.valid_single_own _ _)
  exact TW.mutFold (ρ := PMap.empty) (Z := PMap.empty) (hw := hw) h₁
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (ResU.valid_single_mut_of_wit (ResU.comp_empty_left _) (ResU.valid_single_own _ _))

/-- **At any single `mut` cell at `2` with an empty witness, the clause fails**: at `α = 1`, below
`⊤`, the answer's cell must be at a lifetime `⊒ 1`, and a run's `↭` keeps the lifetime `2` of the
only `mut` cell of the flattening. -/
theorem adj_fails {h : ResU.InStratum (lifeN 2) (PMap.empty : WRes)}
    {Q : Val → SPropS BoCa.Loc Val (lifeN 2)} (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ cC (ℍ := ℍ) adjC [] adjδ adjE
      (ResU.single 0 (CellU.mutOf (lifeN 2) Val.unit PMap.empty h Q hw)) := by
  intro hC
  have hflat := flat_single_mut_empty (k := 0) (u := Val.unit) (hw := hw)
  have hval : ResU.Valid (ResU.single 0 (CellU.mutOf (lifeN 2) Val.unit PMap.empty h Q hw)) :=
    ⟨_, hflat⟩
  have hlt : LtLife adjδ .top (lifeN 1) :=
    ⟨Lifetime.SLife.top, rfl, show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide⟩
  have hwp := hC (lifeN 1) PMap.empty _ ⟨rfl, hlt⟩ (ResU.comp_empty_right _)
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) (tw_single_mut_empty hw) (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α, hα, ℓ, hsep⟩ := hQ
  obtain rfl : α = lifeN 1 := (Option.some.inj hα).symm
  obtain ⟨-, b, u, χ, hχ, Q', hw', -, hαb, hρ', -, -, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ'.get ℓ = some (CellU.mutOf b u χ hχ Q' hw') := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b u χ hχ Q' hw') :=
    pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, σ₀, hσ₀, hg₀⟩ := (hU.1.2 ℓ b Q').mpr ⟨u, χ, hχ, hw', hf⟩
  rw [ResU.Flat.functional hσ₀ hflat] at hg₀
  obtain ⟨-, he⟩ := ResU.single_get_eq_some hg₀
  have hb : b = lifeN 2 := CellU.mutOf_at he
  rw [hb] at hαb
  exact absurd hαb (by decide)

/-- `adj_fails` at a witness equal to `∅` and a lifetime equal to `2`. -/
theorem adj_fails' {b : Life} (hb : b = lifeN 2) {χ : WRes} (hχe : χ = PMap.empty)
    {h : χ.InStratum b} {Q : Val → SPropS BoCa.Loc Val b} (hw : Q Val.unit ⟨χ, h⟩) :
    ¬ cC (ℍ := ℍ) adjC [] adjδ adjE (ResU.single 0 (CellU.mutOf b Val.unit χ h Q hw)) := by
  subst hb hχe
  exact adj_fails hw

/-- **Core's `∀` distinguishes the two configurations.** -/
theorem coreAllAdjacent : CoreAllAdjacent (ℍ := ℍ) :=
  ⟨adj_holds, adj_fails (h := ResU.inStratum_empty _) (unitQ_holds (lifeN 2))⟩

/-! ### The image under `shift ⊤ 1` -/

theorem adjθ_one : adjθ (lifeN 1) = lifeN 2 := rfl

/-- `shift ⊤ 1` carries the cell at `1` to a cell at `2` with an empty witness. -/
theorem adj_relRU :
    adjθ.relRU (innerView 0 (lifeN 1)) =
      ResU.single 0 (CellU.mutOf (adjθ (lifeN 1)) Val.unit (adjθ.relRU PMap.empty)
        ((adjθ.inStratum_relRU (lifeN 1) PMap.empty).mpr (ResU.inStratum_empty _))
        (adjθ.relS (lifeN 1) (unitQ (lifeN 1)))
        (adjθ.relS_holds (ResU.inStratum_empty _) (unitQ_holds (lifeN 1)))) := by
  rw [innerView, Restrat.Emb.relRU_single, Restrat.Emb.relU_mutOf]

/-- At the image of the cell at `1` under `shift ⊤ 1` the clause fails. -/
theorem adj_fails_relRU :
    ¬ cC (ℍ := ℍ) adjC [] adjδ adjE (adjθ.relRU (innerView 0 (lifeN 1))) := by
  rw [adj_relRU]
  exact adj_fails' adjθ_one (Restrat.Emb.relRU_empty (e := adjθ)) _

/-- **Core's relation is not invariant under `shift ⊤ 1`.** -/
theorem coreAllNotNatural : CoreAllNotNatural (ℍ := ℍ) :=
  ⟨adjC, [], adjδ, adjE, innerView 0 (lifeN 1), adj_holds, adj_fails_relRU⟩

/-- **Core's `∀` does not imply the full position-`∀` at `σ = []`**: at the cell adjacent to `⊤`
the clause holds, and at the renaming `shift ⊤ 1`, which opens the cut between `⊤` and the cell,
it fails. -/
theorem not_coreAllImpCutAll : NotCoreAllImpCutAll (ℍ := ℍ) := fun h =>
  adj_fails_relRU (h adjC [] adjδ adjE (innerView 0 (lifeN 1)) adj_holds adjθ)

end ProbeD1

end
