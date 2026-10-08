import ProbeD1.Nx

/-!
# ProbeD1 — the two-cell guard gap (`NEXT.md` item 1a): the proofs

* **The guard lemmas.** `pairRebCells`: [TR] p. 5's `reb_β` at a payload owning two places, with
  the reborrowed type's shape, holds an `imm` cell exactly at `β` at both. `pairCallbackGuardFails`:
  beside any resource, two such cells at places the stack does not lend fail the table at the stack
  when `β` is below its innermost lend, and at every own push at `β` (`loadGuardFails2`).
  `pairCallbackGuardFailsLe`: any two borrow cells no longer-lived than the outermost lend fail it.
  `sliceCallbackGuardFails`: the same at a family. `pairBoundBelow`: `withload`'s bound `⊓Δ` reads
  below the lend. `pairNilOldGuardHolds`: at the empty stack the guard holds of every resource.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### Small facts -/

/-- A cell of the right part is a cell of the composite. -/
theorem compS_get_some_right {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hl : ρ₂.get l = some ψ) : ∃ ψ', ρ.get l = some ψ' := by
  rcases ResU.Comp.get h l with ⟨-, e₂, -⟩ | ⟨_, -, e₂, -⟩ | ⟨_, -, -, e⟩ |
      ⟨_, _, _, -, -, e, -⟩
  · rw [e₂] at hl; exact absurd hl (by simp)
  · rw [e₂] at hl; exact absurd hl (by simp)
  · exact ⟨_, e⟩
  · exact ⟨_, e⟩

/-- A cell of the left part is a cell of the composite. -/
theorem compS_get_some_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hl : ρ₁.get l = some ψ) : ∃ ψ', ρ.get l = some ψ' :=
  compS_get_some_right (ResU.CompS.comm h) hl

/-- **A cell at a lifetime below the innermost lend fails the table's first conjunct.** -/
theorem not_tabAtS_head {σ : LStack} {αs : List Life} {h β : Life} {ρ : WRes} {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hh : αs.head? = some h) (hβ : β < h) (hl : ρ.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) (hat : ψ.at = β) : ¬ TabAtS σ αs ρ := by
  intro ht
  have hin : ψ.InStratum (↓h) := ht.1 h hh l ψ hl
  have hlt : (↓h) < ψ.at := lt_at_of_inStratum hin hk
  rw [hat] at hlt
  exact Life.not_lt_of_down_lt hlt hβ

/-- **A borrow cell no longer-lived than the outermost lend, at a place the stack does not lend,
fails the table's second conjunct.** -/
theorem not_tabAtS_last {σ : LStack} {αs : List Life} {o : Life} {ρ : WRes} {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (ho : αs.getLast? = some o) (hσ : l ∉ σ.map LEnt.l)
    (hl : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) (hat : ψ.at ≤ o) : ¬ TabAtS σ αs ρ := by
  intro ht
  have hlt : o < ψ.at := lt_at_of_inStratum (ht.2 o ho l ψ hσ hl) hk
  exact absurd hat (not_le.mpr hlt)

/-! ### The reborrow's two cells -/

/-- `Imm̲ 'x (Ref 1 ⊗ Ref 1) = Imm 'x 1 ⊗ Imm 'x 1`. -/
theorem pairTy_immReborrow (x : LifeVar) :
    pairTy.immReborrow (.var x) = .tensor (.imm (.var x) .unit) (.imm (.var x) .unit) := rfl

/-- **The shape of `Imm 'x 1` at a location holds a cell there.** -/
theorem vShape_immUnit_get {s : LSub} {x : LifeVar} {l : BoCa.Loc} {ρ : WRes}
    (h : vShape (.imm (.var x) .unit) s (.loc l) ρ) : ∃ ψ, ρ.get l = some ψ := by
  obtain ⟨α, -, ℓ, hsep⟩ := h
  obtain ⟨hl, s', u, χ, hχ, rfl, -, -⟩ := pure_sep_iff.mp hsep
  cases hl
  exact ⟨_, ResU.single_get_self _ _⟩

/-- **`PairRebCells`**: the shape puts a cell of the reborrow at each place (`ptoImm` at each leaf),
and `reb_β`'s `own` clause makes it `imm({β}, (), _)` (`ResU.reb_src`). -/
theorem pairRebCells : PairRebCells := by
  intro R cb β l₁ l₂ x s h₁ h₂ hreb hsh
  rw [pairTy_immReborrow] at hsh
  obtain ⟨v₁, v₂, hsep⟩ := hsh
  obtain ⟨hv, hrest⟩ := pure_sep_iff.mp hsep
  obtain ⟨ρ₁, ρ₂, hc, hs₁, hs₂⟩ := hrest
  obtain ⟨rfl, rfl⟩ := Val.pair_inj' hv
  obtain ⟨ψ₁, hψ₁⟩ := vShape_immUnit_get hs₁
  obtain ⟨ψ₂, hψ₂⟩ := vShape_immUnit_get hs₂
  obtain ⟨φ₁, e₁⟩ := compS_get_some_left hc hψ₁
  obtain ⟨φ₂, e₂⟩ := compS_get_some_right hc hψ₂
  obtain ⟨v₁, χ₁, k₁, rfl, hv₁, -⟩ := ResU.reb_src hreb e₁ h₁ (by simp)
  obtain ⟨v₂, χ₂, k₂, rfl, hv₂, -⟩ := ResU.reb_src hreb e₂ h₂ (by simp)
  simp only [CellU.erase_ownOf] at hv₁ hv₂
  subst hv₁; subst hv₂
  exact ⟨⟨χ₁, k₁, e₁⟩, ⟨χ₂, k₂, e₂⟩⟩

/-! ### The guard at the reborrowed argument -/

/-- **`PairCallbackGuardFails`**: at the old stack the cell at `l₁` is below the innermost lend,
which the table's first conjunct forbids; at a push, `loadGuardFails2` at the reborrow, a part of
the composite (`tabAtS_comp`). -/
theorem pairCallbackGuardFails : PairCallbackGuardFails := by
  intro σ αs β cb ρc ρ l₁ l₂ hne h₁ h₂ ⟨v₁, χ₁, k₁, e₁⟩ ⟨v₂, χ₂, k₂, e₂⟩ hc
  refine ⟨fun h hh hβ ht => ?_, fun en hok ht => ?_⟩
  · exact not_tabAtS_head hh hβ e₁ CellU.kind_immOf_ne_own rfl ((GhostEnd.tabAtS_comp hc).mp ht).2
  · exact loadGuardFails2 σ αs en β cb l₁ l₂ v₁ v₂ χ₁ χ₂ k₁ k₂ hok hne h₁ h₂ e₁ e₂
      ((GhostEnd.tabAtS_comp hc).mp ht).2

/-- **`PairCallbackGuardFailsLe`**: the table's second conjunct at a cell at a place the stack does
not lend, at the old stack and, at a push, at whichever of the two places the pushed entry does
not lend. -/
theorem pairCallbackGuardFailsLe : PairCallbackGuardFailsLe := by
  intro σ αs o cb ρk ρ l₁ l₂ ψ₁ ψ₂ hne h₁ h₂ e₁ e₂ k₁ k₂ a₁ a₂ hc
  refine ⟨fun ho ht => ?_, fun en β _ ho ht => ?_⟩
  · exact not_tabAtS_last ho h₁ e₁ k₁ a₁ ((GhostEnd.tabAtS_comp hc).mp ht).2
  · have hcb := ((GhostEnd.tabAtS_comp hc).mp ht).2
    by_cases he : en.l = l₁
    · refine not_tabAtS_last ho ?_ e₂ k₂ a₂ hcb
      rw [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h => hne (he.symm.trans h.symm), h₂⟩
    · refine not_tabAtS_last ho ?_ e₁ k₁ a₁ hcb
      rw [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h => he h.symm, h₁⟩

/-- **`SliceCallbackGuardFails`**: at the old stack the element at `ℓ` is below the innermost
lend; at a push, `sliceGuardFails` at two elements, at the family, a part of the composite. -/
theorem sliceCallbackGuardFails : SliceCallbackGuardFails := by
  intro σ αs β ρs ρc ρ ℓ hσ hcells hc
  refine ⟨fun h hh hβ ht => ?_, fun en hok ht => ?_⟩
  · obtain ⟨ψ, hψ, hk, hat⟩ := hcells 0 (by decide)
    exact not_tabAtS_head hh hβ hψ hk hat ((GhostEnd.tabAtS_comp hc).mp ht).2
  · exact sliceGuardFails σ αs en β ρs ℓ 2 hok le_rfl hσ hcells
      ((GhostEnd.tabAtS_comp hc).mp ht).2

/-! ### The bound, the empty stack -/

/-- **`PairBoundBelow`**: `⊓Δ` at `Δ = '0 ⊏ ⊤` is `'0 ⊓ ⊤`, read at `α` at the stack's reading. -/
theorem pairBoundBelow : PairBoundBelow := by
  intro δ e α β he ⟨γ, hγ, hlt⟩
  have h0 : (extS δ [e] [α]).find? 0 = some (OrderDual.ofDual α) := by
    show (LSub.extend (extS δ [] []) e.x α).find? 0 = _
    rw [he]; exact find?_extend_self _ _ _
  have hb : (pairΔ.meetOfDom).interp (extS δ [e] [α]) = some (OrderDual.ofDual α) := by
    simp [LifeCtx.meetOfDom, LifeCtx.empty, LifeCtx.extend, Lifetime.meetOfDomL,
      Lifetime.Life.interp, h0, Lifetime.SLife.meet, Lifetime.SLife.top]
  rw [hb] at hγ
  cases hγ
  exact hlt

/-- **`PairNilOldGuardHolds`**: the table at `[]` has no head and no last lend, and no place is
bound (`pvlNil`). -/
theorem pairNilOldGuardHolds : PairNilOldGuardHolds := fun s ls ρ =>
  ⟨⟨fun a ha => absurd ha (by simp), fun a ha => absurd ha (by simp)⟩, pvlNil s ls ρ⟩

end ProbeD1

end
