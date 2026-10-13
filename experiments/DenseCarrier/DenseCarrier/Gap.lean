import DenseCarrier.Faithful
import DenseCarrier.Equivariance
import ProbeD1.GapWitness

/-!
# DenseCarrier — the gap test

`GapWitness.lean`'s configuration, at a general lifetime order: the type
`∀'0 ⊏ @c. F (Mut '0 1)`, the value `Λ. return ℓ₀`, and a single `mut` cell at a slot `b` below
the bound `m = @cδ`. Its fate is decided by the room between the cell and the bound **in `L`**:

* `holdsD`: if every `α ⊏ m` is `⊑ ι b` (no lifetime of `L` strictly between `ι b` and `m`), the
  clause holds at the inner view `ℓ₀ ↦ mut(b, (), ∅, 𝒱⟦1⟧)`;
* `failsD`: if some `α` of `L` lies strictly between `ι b` and `m`, the clause fails at every
  single `mut` cell at `b` with an empty witness: a run's `↭` keeps the cell's slot, and
  `α ⊑ ι b` is false.

At `L = Life` with the identity slots (Core, by `Faithful.lean`) the cell at `1` has no room below
`⊤` and the cell at `2` has room, so the clause holds at one and fails at the other
(`coreAllAdjacentD`, which is `ProbeD1.coreAllAdjacent` read through `cD_id`). At a densely
ordered `L` there is room below the bound at every slot below it, so the clause fails at every such
slot (`dense_fails`), and the adjacency witness cannot be built (`not_denseCoreAllAdjacent`): the
clause does not tell two configurations of one order type apart (`dense_same_order_type`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open GhostEnd (innerView unitQ unitQ_holds)
open ProbeD1 (adjE adj_subst flat_single_mut_empty tw_single_mut_empty)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-- `∀'0 ⊏ @c. F (Mut '0 1)`. -/
abbrev gapC (c : Lifetime.Life) : CTy := .all 0 c (.ret (.mut (.var 0) .unit))

theorem fragC_gapC (c : Lifetime.Life) : FragC (gapC c) := trivial

/-- The inner view stores `𝒱⟦1⟧` for every `L`-lifetime at or below its slot. -/
theorem ptoMutD_innerView_le (ι : Slots L) {k : Loc} {b : Life} {α : L} (h : α ≤ ι b)
    (ls : List SRec) (δ' : LSubD L) :
    ptoMutD ι k α ls (fun ls₀ => vD ι .unit ls₀ δ') (innerView k b) := by
  refine ⟨b, Val.unit, PMap.empty, ResU.inStratum_empty b, unitQ b, unitQ_holds b,
    ls.filter (fun r => decide (r.2 ⊐ b)), h, rfl, ?_, ?_, ?_⟩
  · funext v ρ
    apply propext
    constructor
    · rintro ⟨_, h'⟩; exact h'
    · intro h'
      exact ⟨by obtain ⟨rfl, -⟩ := h'; exact ResU.inStratum_empty b, h'⟩
  · intro r; simp [List.mem_filter]
  · rintro ls' u' σ' ⟨rfl, -⟩; exact ResU.inStratum_empty b

/-- **No room between the cell and the bound: the clause holds.** -/
theorem holdsD (ι : Slots L) (c : Lifetime.Life) (δ : LSubD L) {m : L}
    (hm : interpD δ c = some m) (b : Life) (hroom : ∀ α, α < m → α ≤ ι b) :
    cD (ℍ := ℍ) ι (gapC c) [] δ adjE (innerView 0 b) := by
  intro α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β, hβ, hlt⟩ := hp
  rw [hm] at hβ
  obtain rfl := Option.some.inj hβ
  have hρ₂ : ρ₂ = innerView 0 b := ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine wpTS_lolli [] (.val (Val.loc 0)) Val.unit _ _ ?_
  rw [adj_subst]
  refine wpTS_val [] (Val.loc 0) _ _ ?_
  exact ⟨α, LSubD.find?_extend_self δ 0 α, 0,
    pure_sep_mk rfl (ptoMutD_innerView_le ι (hroom α hlt) [] _)⟩

/-- **Room between the cell and the bound: the clause fails** at every single `mut` cell at `b`
with an empty witness. -/
theorem failsD (ι : Slots L) (c : Lifetime.Life) (δ : LSubD L) {m : L}
    (hm : interpD δ c = some m) {b : Life} {α : L} (hbα : ι b < α) (hαm : α < m)
    {h : ResU.InStratum b (PMap.empty : WRes)} {Q : Val → SPropS Loc Val b}
    (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ cD (ℍ := ℍ) ι (gapC c) [] δ adjE
      (ResU.single 0 (CellU.mutOf b Val.unit PMap.empty h Q hw)) := by
  intro hC
  have hflat := flat_single_mut_empty (k := 0) (u := Val.unit) (hw := hw)
  have hval : ResU.Valid (ResU.single 0 (CellU.mutOf b Val.unit PMap.empty h Q hw)) :=
    ⟨_, hflat⟩
  have hlt : LtLifeD δ c α := ⟨m, hm, hαm⟩
  have hwp := hC α PMap.empty _ ⟨rfl, hlt⟩ (ResU.comp_empty_right _)
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) (tw_single_mut_empty hw) (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α', hα', ℓ, hsep⟩ := hQ
  change (δ.extend 0 α).find? 0 = some α' at hα'
  rw [LSubD.find?_extend_self] at hα'
  obtain rfl := Option.some.inj hα'
  obtain ⟨-, b', u, χ, hχ, Q', hw', -, hαb, hρ', -, -, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ'.get ℓ = some (CellU.mutOf b' u χ hχ Q' hw') := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b' u χ hχ Q' hw') :=
    ProbeD1.pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, σ₀, hσ₀, hg₀⟩ := (hU.1.2 ℓ b' Q').mpr ⟨u, χ, hχ, hw', hf⟩
  rw [ResU.Flat.functional hσ₀ hflat] at hg₀
  obtain ⟨-, he⟩ := ResU.single_get_eq_some hg₀
  have hb : b' = b := CellU.mutOf_at he
  rw [hb] at hαb
  exact absurd hαb (not_le.mpr hbα)

/-- The empty reading. -/
abbrev δ₀ : LSubD L := ⟨[]⟩

theorem interpD_top (δ : LSubD L) : interpD δ .top = some ⊤ := rfl

/-! ### At `L = Life` and the identity slots: Core -/

/-- The cell at `1` has no room below `⊤`. -/
theorem room_one (α : Life) (h : α < ⊤) : α ≤ Slots.id (OrderDual.toDual 1) := by
  have h' : 0 < OrderDual.ofDual α := h
  show 1 ≤ OrderDual.ofDual α
  omega

/-- **Core's `∀` distinguishes the cells at `1` and `2`** (`ProbeD1.CoreAllAdjacent`, through
`cD_id`). -/
theorem coreAllAdjacentD :
    cD (ℍ := ℍ) Slots.id (gapC .top) [] δ₀ adjE (innerView 0 (OrderDual.toDual 1)) ∧
      ¬ cD (ℍ := ℍ) Slots.id (gapC .top) [] δ₀ adjE (innerView 0 (OrderDual.toDual 2)) :=
  ⟨holdsD Slots.id .top δ₀ (interpD_top _) _ room_one,
    failsD Slots.id .top δ₀ (interpD_top _) (α := OrderDual.toDual 1)
      (show OrderDual.toDual (2 : ℕ) < OrderDual.toDual 1 from by decide)
      (show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide) (unitQ_holds _)⟩

/-- The same, read in Core's own relation. -/
theorem coreAllAdjacent_via_cD : ProbeD1.CoreAllAdjacent (ℍ := ℍ) := by
  have h := coreAllAdjacentD (ℍ := ℍ)
  rw [cD_id _ (fragC_gapC _)] at h
  exact h

/-! ### At a dense `L`: no adjacency -/

/-- **At a dense `L` the clause fails at every slot below the bound.** -/
theorem dense_fails [DenselyOrdered L] (ι : Slots L) (c : Lifetime.Life) (δ : LSubD L) {m : L}
    (hm : interpD δ c = some m) {b : Life} (hb : ι b < m)
    {h : ResU.InStratum b (PMap.empty : WRes)} {Q : Val → SPropS Loc Val b}
    (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ cD (ℍ := ℍ) ι (gapC c) [] δ adjE
      (ResU.single 0 (CellU.mutOf b Val.unit PMap.empty h Q hw)) := by
  obtain ⟨α, h₁, h₂⟩ := exists_between hb
  exact failsD ι c δ hm h₁ h₂ hw

/-- At the inner view. -/
theorem dense_fails_innerView [DenselyOrdered L] (ι : Slots L) (c : Lifetime.Life) (δ : LSubD L)
    {m : L} (hm : interpD δ c = some m) {b : Life} (hb : ι b < m) :
    ¬ cD (ℍ := ℍ) ι (gapC c) [] δ adjE (innerView 0 b) :=
  dense_fails ι c δ hm hb (unitQ_holds b)

/-- **The dense analogue of `CoreAllAdjacent`**: the clause at `∀'0 ⊏ ⊤. F (Mut '0 1)` holds at
the cell at slot `b₁` and fails at the cell at slot `b₂`, both below `⊤` in `L`. -/
def DenseCoreAllAdjacent (ι : Slots L) : Prop :=
  ∃ b₁ b₂ : Life, ι b₁ < ⊤ ∧ ι b₂ < ⊤ ∧
    cD (ℍ := ℍ) ι (gapC .top) [] δ₀ adjE (innerView 0 b₁) ∧
    ¬ cD (ℍ := ℍ) ι (gapC .top) [] δ₀ adjE (innerView 0 b₂)

/-- **At a dense `L` the adjacency witness cannot be built**, at any slots. -/
theorem not_denseCoreAllAdjacent [DenselyOrdered L] (ι : Slots L) :
    ¬ DenseCoreAllAdjacent (ℍ := ℍ) ι := by
  rintro ⟨b₁, -, h₁, -, hC, -⟩
  exact dense_fails_innerView ι .top δ₀ (interpD_top _) h₁ hC

/-- At Core's slots `1` and `2`, wherever a dense `L` puts them. -/
theorem not_denseCoreAllAdjacent_one_two [DenselyOrdered L] (ι : Slots L) :
    ¬ (cD (ℍ := ℍ) ι (gapC .top) [] δ₀ adjE (innerView 0 (OrderDual.toDual 1)) ∧
      ¬ cD (ℍ := ℍ) ι (gapC .top) [] δ₀ adjE (innerView 0 (OrderDual.toDual 2))) := by
  rintro ⟨hC, -⟩
  have h₁ : ι (OrderDual.toDual 1) < ⊤ := by
    rw [← ι.map_top]
    exact ι.strictMono (show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide)
  exact dense_fails_innerView ι .top δ₀ (interpD_top _) h₁ hC

/-- **At a dense `L` the clause does not tell two cells of one order type apart**: below the
bound it fails at both. -/
theorem dense_same_order_type [DenselyOrdered L] (ι : Slots L) (c : Lifetime.Life)
    (δ : LSubD L) {m : L} (hm : interpD δ c = some m) {b₁ b₂ : Life} (h₁ : ι b₁ < m)
    (h₂ : ι b₂ < m) :
    cD (ℍ := ℍ) ι (gapC c) [] δ adjE (innerView 0 b₁) ↔
      cD (ℍ := ℍ) ι (gapC c) [] δ adjE (innerView 0 b₂) :=
  ⟨fun h => absurd h (dense_fails_innerView ι c δ hm h₁),
    fun h => absurd h (dense_fails_innerView ι c δ hm h₂)⟩

end DenseCarrier

end
