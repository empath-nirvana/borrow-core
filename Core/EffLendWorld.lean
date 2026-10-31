import Core.EffDefs

/-!
# Core — the lend's re-lend at a bounded world: what `Owed (some r)` carries  `[spec §63]`

`lendM_frame` (`Core/EffLend.lean`) re-lends at a resumption with the cell the stop held. That cell
is `ℓ ↦ mut(α, v, ρ_P, QsAt T δ ls α)`, whose predicate is `𝒱⟦T⟧` at the stop's list `ls` for
every resource of `Res_α`. Resumed at a list `ls′` with `Owed (some r) ls ls′` (M1's world), the
same predicate at `ls′` follows from locality (`vC_local`) when `Ext` holds between the two lists,
both ways, at every resource of `Res_α`.

This file records what the bound gives towards that:

* `owedBound_stratum_config`: a configuration, every hypothesis discharged, where
  `Owed (some r) ls ls′ ρ` holds at a stop's share with `α ⊏ r`, a resource `ρ′ ∈ Res_α` exists,
  and `Ext ls ls′ ρ′` does not hold. `Res_α` admits a borrow cell at any lifetime longer than `α`,
  and `Ext` at it keeps the records longer-lived than that cell; the bound keeps only those
  strictly inside `r`.
* `OwedKeepsAbove α en`: the property that would carry `Ext` to every resource of `Res_α`, a
  premise on the resumer: every record longer-lived than `α` kept. It names no depth.
* `owed_same_of_keepsAbove`: with that property and `α ⊏ r`, a list the bounded stop is owed at
  has the stop's members, so the bound adds nothing over keeping every record.
-/

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Every record longer-lived than `α` is kept** at every list a stop at `en` is owed at: what
carries `Ext` from a stop's share to every resource of `Res_α`.  A premise on the resumer; it
names no depth.  `[spec §63]` -/
def OwedKeepsAbove (α : Life) (en : OpEnt) : Prop :=
  ∀ ls ls' ρ, Owed en ls ls' ρ → ∀ x : SRec, x.2 ⊐ α → (x ∈ ls ↔ x ∈ ls')

/-- **With every record longer-lived than `α` kept, a bound outliving `α` keeps every record**:
the records it does not keep inside it are the ones `OwedKeepsAbove` keeps.  `[spec §63]` -/
theorem owed_same_of_keepsAbove {α r : Life} {en : OpEnt} (hk : OwedKeepsAbove α en)
    (hw : en.wld = some r) (hrα : r ⊐ α) {ls ls' : List SRec} {ρ : WRes}
    (h : Owed en ls ls' ρ) : ∀ x, x ∈ ls ↔ x ∈ ls' := by
  intro x
  rcases lt_trichotomy x.2 α with hx | hx | hx
  · exact h.2 r hw x (lt_trans hx hrα)
  · exact h.2 r hw x (hx ▸ hrα)
  · exact hk ls ls' ρ h x hx

/-- The entry of the configuration: must-resume, at the world `some r`. -/
def cfgEnt (r : Life) : OpEnt :=
  ⟨.lin, false, fun _ _ _ => True, fun _ _ _ => True, none, some r⟩

/-- A frame record, tagged `β`. -/
def cfgRec (β : Life) : SRec :=
  (⟨0, .unit, PMap.empty, .unit, LSub.empty⟩, β)

/-- The resource of the configuration: one `mut` cell at `b`, holding nothing. -/
noncomputable def cfgCell (b : Life) : WRes :=
  ResU.single 0 (CellU.mutOf b .unit PMap.empty (ResU.inStratum_empty b) (fun _ _ => True) trivial)

/-- **`Owed (some r)` at a stop's share does not give `Ext` at every resource of `Res_α`.**
The lifetimes, longest first: `β = 1`, `b = r = 2`, `α = 3`.  The lists differ in one record
tagged `β`, outside the bound, longer-lived than the cell at `b ∈ Res_α`; the share is empty.
`[spec §63]` -/
theorem owedBound_stratum_config :
    ∃ (en : OpEnt) (r α : Life) (ls ls' : List SRec) (ρ ρ' : WRes),
      en.wld = some r ∧ r ⊐ α ∧ Owed en ls ls' ρ ∧ ρ'.InStratum α ∧ ¬ Ext ls ls' ρ' := by
  let β : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  let α : Life := OrderDual.toDual 3
  refine ⟨cfgEnt b, b, α, [cfgRec β], [], PMap.empty, cfgCell b, rfl, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · show OrderDual.toDual 3 < OrderDual.toDual 2
    exact OrderDual.toDual_lt_toDual.mpr (by decide)
  · intro rec _ hR
    obtain ⟨m, ψ, hg, -⟩ := hR
    exact absurd hg (by simp)
  · intro c hc
    obtain ⟨m, ψ, hg, -⟩ := hc
    exact absurd hg (by simp)
  · intro r' hr' x hx
    cases hr'
    simp only [List.mem_singleton, List.not_mem_nil, iff_false]
    rintro rfl
    exact absurd hx (by
      show ¬ (OrderDual.toDual 1 < OrderDual.toDual 2)
      exact fun h => absurd (OrderDual.toDual_lt_toDual.mp h) (by decide))
  · intro l ψ hg
    unfold cfgCell at hg
    by_cases hl : l = 0
    · subst hl
      rw [ResU.single_get_self] at hg
      cases hg
      show OrderDual.toDual 3 < OrderDual.toDual 2
      exact OrderDual.toDual_lt_toDual.mpr (by decide)
    · exact absurd hg (by simp [ResU.single, hl])
  · intro hE
    have hcell : CellIn (cfgCell b) b :=
      ⟨0, _, ResU.single_get_self _ _, CellU.kind_mutOf_ne_own, le_refl _⟩
    have := (hE.2 b hcell (cfgRec β)
      (show OrderDual.toDual 2 < OrderDual.toDual 1 from
        OrderDual.toDual_lt_toDual.mpr (by decide))).mp (List.mem_singleton_self _)
    exact absurd this (by simp)

end BoCa.Fig16.LogRel.Core
