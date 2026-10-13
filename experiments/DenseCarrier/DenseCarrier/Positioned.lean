import DenseCarrier.Nominal

/-!
# DenseCarrier — cells at the positions of a dense order, stratified by a separate index

`RelendRoom.lean`'s obstruction is room: a cell sits at a stratum, and a type can need a stratum
strictly between two lifetimes. Every order that carries the layer equation and has no least
element has adjacent strata (`carrier_covBy`: it is reverse-well-founded by `carrier_iff`, and each
point is covered from below, `exists_covBy_of_wellFoundedGT`), so a carrier whose cells' lifetimes
are their strata always has such a pair.

A carrier with no room keeps the lifetime and the stratum apart: a cell carries a **position** in
`L`, any linear order, dense ones included, and a **stratum** in a reverse-well-founded index `S`
that only the recursion reads (`PCell`, `PCell_eq`: a `mut` cell of stratum `σ` stores a predicate
on the cells of a stratum `τ ⊐ σ`). It exists over every `L`: the index the recursion runs on is
`S`, so `no_fsCarrier`'s descending sequence of cardinals, which runs along an ascending chain of
lifetimes used as strata, has nothing to run along.

The order automorphisms of `L` act on it, moving positions and keeping strata (`pact`, a cell's
stored predicate moved to its image), and the action is a **bijection** (`pact_bijective`): the
image of a stored predicate is its whole transport, with no position left free. On the two-order
design the re-slotting of a region is not onto (`exists_gap`), which is what `Reslot.lean`'s and
`RelendRoom.lean`'s refutations turn on.

What this carrier does not give: the relation's `Mut` clause equates a cell's stored predicate with
`𝒱⟦A⟧`, a predicate on resources at every stratum, while a stored predicate here lives on one
stratum. The clause would store `𝒱⟦A⟧` restricted to the cell's stratum, and storing into a lent
place would then have to show the stored value's cells are in that stratum, which positions do not
determine. Whether Core's relation and the fundamental property port to this carrier is not derived.
-/

noncomputable section

namespace DenseCarrier
open BoCa.Fig16 (PMap)

/-! ### Adjacent strata -/

/-- **In a reverse-well-founded order with no least element every point is covered from below.** -/
theorem exists_covBy_of_wellFoundedGT {S : Type} [LinearOrder S] [WellFoundedGT S]
    [NoMinOrder S] (x : S) : ∃ y, y ⋖ x := by
  obtain ⟨z, hz⟩ := exists_lt x
  obtain ⟨y, hy, hmax⟩ := (wellFounded_gt (α := S)).has_min {w | w < x} ⟨z, hz⟩
  exact ⟨y, hy, fun w hyw hwx => hmax w hwx hyw⟩

/-- **Every order that carries the layer equation, with no least element, has adjacent strata**: a
lifetime just below each lifetime, with no lifetime between them. -/
theorem carrier_covBy {L Loc Val : Type} [LinearOrder L] [NoMinOrder L] [Nonempty Loc]
    [Nonempty Val] {Cell : L → Type} (hC : IsCarrier Loc Val Cell) (x : L) : ∃ y, y ⋖ x := by
  have := (carrier_iff (Loc := Loc) (Val := Val)).mp ⟨Cell, hC⟩
  exact exists_covBy_of_wellFoundedGT x

/-! ### The positioned carrier -/

section Positioned
variable (S L Loc Val : Type) [LinearOrder S]

/-- A `mut` cell of stratum `σ`, one layer: a position `p` in `L`, a stratum `τ ⊐ σ`, a value, a
witness on the cells of `τ`, and a stored predicate on them that holds at the witness. -/
structure PMutF (σ : S) (below : ∀ τ, σ < τ → Type) : Type where
  p : L
  τ : S
  hτ : σ < τ
  v : Val
  ρ : PMap Loc (below τ hτ)
  P : Val → PMap Loc (below τ hτ) → Prop
  hw : P v ρ

/-- A cell of stratum `σ`, one layer: `own(v)` or a positioned `mut` cell. -/
inductive PCellF (σ : S) (below : ∀ τ, σ < τ → Type) : Type where
  | own (v : Val)
  | mut (m : PMutF S L Loc Val σ below)

variable [WellFoundedGT S]

/-- **The positioned carrier**: the layer equation solved by recursion down the index `S`. -/
def PCell : S → Type := WellFounded.fix wellFounded_gt (PCellF S L Loc Val)

theorem PCell_eq (σ : S) :
    PCell S L Loc Val σ = PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ) :=
  WellFounded.fix_eq wellFounded_gt (PCellF S L Loc Val) σ

end Positioned

namespace PCell
variable {S L Loc Val : Type} [LinearOrder S] [WellFoundedGT S]

def toF {σ : S} (x : PCell S L Loc Val σ) : PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ) :=
  cast (PCell_eq S L Loc Val σ) x

def ofF {σ : S} (y : PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ)) : PCell S L Loc Val σ :=
  cast (PCell_eq S L Loc Val σ).symm y

@[simp] theorem toF_ofF {σ : S} (y : PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ)) :
    (ofF y).toF = y := cast_cast _ _ y

@[simp] theorem ofF_toF {σ : S} (x : PCell S L Loc Val σ) : ofF x.toF = x := cast_cast _ _ x

end PCell

/-! ### The automorphisms of `L` act -/

section Action
variable {S L Loc Val : Type} [LinearOrder S] [WellFoundedGT S] [LinearOrder L]

/-- One layer of the action: the position moved by `π`, the witness moved cell by cell, the stored
predicate moved to its image, the strata kept. -/
def pLayer (π : L ≃o L) (σ : S) (rec : ∀ τ, σ < τ → PCell S L Loc Val τ → PCell S L Loc Val τ) :
    PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ) →
      PCellF S L Loc Val σ (fun τ _ => PCell S L Loc Val τ)
  | .own v => .own v
  | .mut m => .mut ⟨π m.p, m.τ, m.hτ, m.v, m.ρ.map (rec m.τ m.hτ),
      fun v r => ∃ r₀, r₀.map (rec m.τ m.hτ) = r ∧ m.P v r₀, ⟨m.ρ, rfl, m.hw⟩⟩

/-- **`π · ψ`**: an order automorphism of `L` on the positioned carrier. -/
def pact (π : L ≃o L) : ∀ σ : S, PCell S L Loc Val σ → PCell S L Loc Val σ :=
  WellFounded.fix (wellFounded_gt (α := S))
    (C := fun σ => PCell S L Loc Val σ → PCell S L Loc Val σ)
    (fun σ rec x => PCell.ofF (pLayer π σ (fun τ h => rec τ h) x.toF))

theorem pact_eq (π : L ≃o L) (σ : S) (x : PCell S L Loc Val σ) :
    pact π σ x = PCell.ofF (pLayer π σ (fun τ _ => pact π τ) x.toF) := by
  unfold pact
  rw [WellFounded.fix_eq]

/-- **The action is undone by the inverse**, stratum by stratum. -/
theorem pact_symm_pact (π : L ≃o L) :
    ∀ (σ : S) (x : PCell S L Loc Val σ), pact π.symm σ (pact π σ x) = x := by
  intro σ
  induction σ using (wellFounded_gt (α := S)).induction with
  | _ σ ih =>
    intro x
    rw [pact_eq, pact_eq, PCell.toF_ofF]
    conv_rhs => rw [← PCell.ofF_toF x]
    congr 1
    generalize x.toF = y
    cases y with
    | own v => rfl
    | «mut» m =>
        obtain ⟨p, τ, hτ, v, ρ, P, hw⟩ := m
        have hid : ∀ c : PCell S L Loc Val τ, pact π.symm τ (pact π τ c) = c := ih τ hτ
        have hρ : (ρ.map (pact π τ)).map (pact π.symm τ) = ρ := by
          rw [pmap_map_map]; exact pmap_map_id' hid ρ
        have hP : (fun v r => ∃ r₁, r₁.map (pact π.symm τ) = r ∧
            ∃ r₀, r₀.map (pact π τ) = r₁ ∧ P v r₀) = P := by
          funext u r
          apply propext
          constructor
          · rintro ⟨r₁, rfl, r₀, rfl, h⟩
            rw [pmap_map_map, pmap_map_id' (f := pact π.symm τ ∘ pact π τ) hid]; exact h
          · intro h
            exact ⟨r.map (pact π τ), by rw [pmap_map_map]; exact pmap_map_id' hid r, r, rfl, h⟩
        simp only [pLayer]
        congr 1
        simp only [OrderIso.symm_apply_apply, PMutF.mk.injEq, true_and]
        exact ⟨heq_of_eq hρ, heq_of_eq hP⟩

/-- **The action is a bijection on every stratum**: the image of a stored predicate is its whole
transport. -/
theorem pact_bijective (π : L ≃o L) (σ : S) :
    Function.Bijective (pact (S := S) (Loc := Loc) (Val := Val) π σ) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨pact π.symm σ, pact_symm_pact π σ, fun x => ?_⟩
  have := pact_symm_pact π.symm σ x
  rwa [OrderIso.symm_symm] at this

end Action

end DenseCarrier

end
