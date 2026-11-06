import Core.Chain.Cancel791N

/-!
# Core's `Mut` on the chain, at a reborrow: a configuration  `[spec §62]`

Core's `Mut` clause (`ptoMutS`, `Core/Relation.lean`) stores `𝒱⟦A⟧` read at the records strictly
longer-lived than the cell (`ofS Q = P ls₀`), and Core's Kripke order `Ext` keeps exactly the
records above every borrow of the resource. On the chain the families live in the location
typing `Φ` (`UpdN` changes a cell's predicate only along `Φ ℓ`), so Core's shape there is: a
`Mut` value at `ℓ` whose cell is at `α`, with `Φ ℓ = (α, 𝒱⟦A⟧ read at Φ above α)` (`mutC`).

A reborrow runs its callback at `Φ.set ℓ α Fi` where `Φ ℓ = (β, Fo)`, `α < β` (`erwp_withbor3`,
the frame `withbor3U` and the field reborrow `withborFE` run). The configuration: a value of
Core's shape at a location `ℓ_b ≠ ℓ`, its cell at `b` with `α < b < β`, holding a `Mut @β 1` at
a location `ℓ₂ ≠ ℓ` (`coreShape_not_reborrow`). It is a value at `Φ` and is not one at
`Φ.set ℓ α F`, for every `F`: re-typing `ℓ` below `b` takes `ℓ` out of `Φ` above `b`, so the
family `Φ ℓ_b` stores is no longer `𝒱⟦Mut @β 1⟧` read at `Φ` above `b`, though the value holds
nothing at `ℓ`. A callback holding such a borrow (one shorter than the source's, longer than the
reborrow's) is valid at `Φ`; Core's Kripke order would have to reach `Φ.set ℓ α Fi` for the
callback to run there, and no order along which Core's `Mut` values are stable reaches it.

The reason is structural: Core's records are one per lend (a reborrow adds a record and keeps
the source's), and the chain's location typing is one family per location (a reborrow overwrites
the source's). Nothing here changes a definition the relation reads.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Shape791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI

/-- `Φ` above `α`: the entries whose lifetime is strictly longer than `α` (Core's `ls₀`). -/
def LocFam.above (Φ : LocFam) (α : Life) : LocFam := fun l =>
  match Φ l with
  | some x => if α < x.1 then some x else none
  | none => none

/-- A content predicate read at a location typing: the semantic payload of a type. -/
abbrev CPredN := LocFam → Nat → Val → WRes → Prop

/-- The family Core's shape stores at a cell at `α`: the payload read at `Φ` above `α`. -/
def famC (α : Life) (P : CPredN) (Φ : LocFam) : Nat → Val → SPropS Loc Val α :=
  fun j u r => P (LocFam.above Φ α) j u r.1

/-- **Core's `Mut` clause on the chain**: a location whose cell at `α` holds the member `j ≥ n`
of `famC α P Φ`, the family `Φ ℓ` gives. -/
def mutC (α : Life) (P : CPredN) : CPredN := fun Φ n v ρ =>
  ∃ (l : Loc) (w : Val) (χ : WRes) (hχ : χ.InStratum α) (j : Nat) (hw : famC α P Φ j w ⟨χ, hχ⟩),
    n ≤ j ∧ v = Val.loc l ∧ Φ l = some ⟨α, famC α P Φ⟩ ∧
      ρ = ResU.single l (CellU.mutOf α w χ hχ (famC α P Φ j) hw)

/-- `𝒱⟦1⟧`. -/
def unitP : CPredN := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty

/-- `𝒱⟦1⟧`'s family at any lifetime, read at any `Φ`. -/
def famUnit (β : Life) : Nat → Val → SPropS Loc Val β := fun _ u r => u = Val.unit ∧ r.1 = PMap.empty

theorem famC_unit (β : Life) (Φ : LocFam) : famC β unitP Φ = famUnit β := rfl

theorem above_set_lt {Φ : LocFam} {l : Loc} {α b : Life} (hαb : ¬ b < α)
    {F : Nat → Val → SPropS Loc Val α} : LocFam.above (Φ.set l α F) b l = none := by
  simp only [LocFam.above, LocFam.set, if_true]
  exact if_neg hαb

/-- The location typing of the configuration: `ℓ` and `ℓ₂` at `β` with `𝒱⟦1⟧`'s family, `ℓ_b`
at `b` with `𝒱⟦Mut @β 1⟧`'s, read at the entries above `b`. -/
def Φ₁ (l l₂ : Loc) (β : Life) : LocFam := fun x =>
  if x = l ∨ x = l₂ then some ⟨β, famUnit β⟩ else none

def Φc (l l₂ lb : Loc) (b β : Life) : LocFam := fun x =>
  if x = lb then some ⟨b, famC b (mutC β unitP) (Φ₁ l l₂ β)⟩ else Φ₁ l l₂ β x

theorem Φc_above (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) {b β : Life} (hbβ : b < β) :
    LocFam.above (Φc l l₂ lb b β) b = Φ₁ l l₂ β := by
  funext x
  simp only [LocFam.above, Φc, Φ₁]
  by_cases hx : x = lb
  · subst hx
    simp [hl, hl₂]
  · by_cases h : x = l ∨ x = l₂
    · simp [hx, h, hbβ]
    · simp [hx, h]

theorem Φ₁_above (l l₂ : Loc) {b β : Life} (hbβ : b < β) :
    LocFam.above (Φ₁ l l₂ β) b = Φ₁ l l₂ β := by
  funext x
  simp only [LocFam.above, Φ₁]
  by_cases h : x = l ∨ x = l₂ <;> simp [h, hbβ]

/-- The inner cell `ℓ₂ ↦ mut(β, (), ∅, 𝒱⟦1⟧)`. -/
def innerCell (l₂ : Loc) (β : Life) : WRes :=
  ResU.single l₂ (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) (famUnit β 0)
    ⟨rfl, rfl⟩)

theorem innerCell_inStratum (l₂ : Loc) {b β : Life} (hbβ : b < β) :
    (innerCell l₂ β).InStratum b :=
  ResU.inStratum_single l₂ ((CellU.inStratum_mutOf b β _ _ _ _ _).mpr hbβ)

/-- `ℓ₂` holds a `Mut @β 1` at `Φ₁` above anything below `β`. -/
theorem inner_mutC (l l₂ : Loc) {b β : Life} (hbβ : b < β) :
    mutC β unitP (LocFam.above (Φ₁ l l₂ β) b) 0 (Val.loc l₂) (innerCell l₂ β) := by
  rw [Φ₁_above l l₂ hbβ]
  refine ⟨l₂, Val.unit, PMap.empty, ResU.inStratum_empty β, 0, ⟨rfl, rfl⟩, le_rfl, rfl, ?_, rfl⟩
  simp [Φ₁, famC_unit]

/-- **The configuration.** At `Φc`, the location `ℓ_b` holds a value of Core's shape at
`Mut @b (Mut @β 1)` (its content a `Mut @β 1` at `ℓ₂`); for every `α < b` and every family
`F`, the same value is not one at `Φc.set ℓ α F`, the location typing a reborrow of `ℓ` at `α`
runs its callback at. The value holds nothing at `ℓ`. -/
theorem coreShape_not_reborrow (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) (hll₂ : l₂ ≠ l)
    {α b β : Life} (hαb : α < b) (hbβ : b < β) (F : Nat → Val → SPropS Loc Val α) :
    ∃ (v : Val) (ρ : WRes),
      (∀ x ψ, ρ.get x = some ψ → x ≠ l) ∧
      mutC b (mutC β unitP) (Φc l l₂ lb b β) 0 v ρ ∧
      ¬ mutC b (mutC β unitP) ((Φc l l₂ lb b β).set l α F) 0 v ρ := by
  have hfam : famC b (mutC β unitP) (Φc l l₂ lb b β) =
      famC b (mutC β unitP) (Φ₁ l l₂ β) := by
    funext j u r
    simp only [famC, Φc_above l l₂ lb hl hl₂ hbβ, Φ₁_above l l₂ hbβ]
  have hw : famC b (mutC β unitP) (Φc l l₂ lb b β) 0 (Val.loc l₂)
      ⟨innerCell l₂ β, innerCell_inStratum l₂ hbβ⟩ := by
    simp only [famC, Φc_above l l₂ lb hl hl₂ hbβ]
    have h := inner_mutC l l₂ hbβ
    rwa [Φ₁_above l l₂ hbβ] at h
  refine ⟨Val.loc lb, ResU.single lb (CellU.mutOf b (Val.loc l₂) (innerCell l₂ β)
    (innerCell_inStratum l₂ hbβ) _ hw), fun x ψ hx => ?_, ?_, ?_⟩
  · by_cases h : x = lb
    · rw [h]; exact hl
    · rw [ResU.single_get_ne _ h] at hx; exact absurd hx (by simp)
  · refine ⟨lb, _, _, _, 0, hw, le_rfl, rfl, ?_, rfl⟩
    simp only [Φc, if_true, hfam]
  · rintro ⟨l', w, χ, hχ, j, hw', -, hv, hΦ, -⟩
    obtain rfl : lb = l' := by
      have := congrArg Subtype.val hv
      simpa [Val.loc] using this
    -- `Φ ℓ_b` is unchanged by the re-typing, so its family is read above `b` at both
    have hΦlb : (Φc l l₂ lb b β).set l α F lb =
        some ⟨b, famC b (mutC β unitP) (Φ₁ l l₂ β)⟩ := by
      simp [LocFam.set, hl, Φc]
    rw [hΦlb] at hΦ
    have heq : famC b (mutC β unitP) (Φ₁ l l₂ β) =
        famC b (mutC β unitP) ((Φc l l₂ lb b β).set l α F) := by
      have := (Sigma.mk.inj_iff.mp (Option.some.inj hΦ)).2
      exact eq_of_heq this
    -- at the member `ℓ ↦ mut(β, (), ∅, 𝒱⟦1⟧)`: in the family read at `Φ₁`, not in the one read
    -- at the re-typed `Φ`, where `ℓ` is not above `b`
    have hin : famC b (mutC β unitP) (Φ₁ l l₂ β) 0 (Val.loc l)
        ⟨innerCell l β, innerCell_inStratum l hbβ⟩ := by
      simp only [famC]
      rw [Φ₁_above l l₂ hbβ]
      refine ⟨l, Val.unit, PMap.empty, ResU.inStratum_empty β, 0, ⟨rfl, rfl⟩, le_rfl, rfl, ?_, rfl⟩
      simp [Φ₁, famC_unit]
    rw [heq] at hin
    obtain ⟨l'', -, -, -, -, -, -, hv'', hΦ'', -⟩ := hin
    obtain rfl : l = l'' := by
      have := congrArg Subtype.val hv''
      simpa [Val.loc] using this
    rw [above_set_lt (not_lt.mpr hαb.le)] at hΦ''
    cases hΦ''

end BoCa.Fig16.LogRel.Core.Chain.SI.Shape791N

end
