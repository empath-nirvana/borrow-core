import Core.Chain.SI.LocTy

/-! Isolated loan-identity boundary [spec §62]. A fixed predicate member is too strong
an identity for main's indexed mutable-cell update. This uses a concrete positive-index
MutStep; it does not assert that this family arises from a particular source type. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.LoanMemberBoundary
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core

def family (β : Life) : Nat → Val → SPropS Loc Val β :=
  fun n v _ => n ≤ 1 ∨ v = Val.unit

theorem family_down (β : Life) : DownFam β (family β) := by
  intro n v r h
  rcases h with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

def before (β : Life) : CellU Loc Val :=
  CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β)
    (family β 2) (Or.inr rfl)

def after (β : Life) : CellU Loc Val :=
  CellU.mutOf β (Val.loc 0) PMap.empty (ResU.inStratum_empty β)
    (family β 1) (Or.inl le_rfl)

def view (l : Loc) (β : Life) : LocFam :=
  LocFam.set LocFam.empty l β (family β)

theorem view_down (l : Loc) (β : Life) : (view l β).Down :=
  LocFam.set_down (fun _ _ _ h => by cases h) (family_down β)

/-- The production update accepts this change at index 1, from stored member 2 to 1. -/
theorem member_write_is_legal (l : Loc) (β : Life) :
    MutStep (view l β) 1 l (before β) (after β) :=
  mutStep_write (view_down l β) (by simp [view, LocFam.set]) le_rfl

/-- The same valid indexed write changes the actual stored predicate. -/
theorem member_predicates_differ (β : Life) :
    cellPred (before β) ≠ cellPred (after β) := by
  intro he
  have ha : cellPred (after β) (Val.loc 0) PMap.empty :=
    (mpred_mutOf _ _).mpr ⟨ResU.inStratum_empty β, Or.inl le_rfl⟩
  rw [← he] at ha
  obtain ⟨h, hp⟩ := (mpred_mutOf _ _).mp ha
  rcases hp with hp | hp
  · omega
  · have hv := congrArg Subtype.val hp
    cases hv

/-- The physical part of a fixed-member return contract, as used by OwnedClaim/W1. -/
def FixedMemberReturn (l : Loc) (β : Life) (P : Val → SPropS Loc Val β) (ρ : WRes) : Prop :=
  ∃ (u : Val) (h : ResU.InStratum β (PMap.empty : WRes)) (hu : P u ⟨PMap.empty, h⟩),
    ρ = ResU.single l (CellU.mutOf β u PMap.empty h P hu)

/-- Location and lifetime are unchanged, yet the fixed old member rejects the legal return. -/
theorem fixed_member_return_rejected (l : Loc) (β : Life) :
    ¬ FixedMemberReturn l β (family β 2) (ResU.single l (after β)) := by
  rintro ⟨u, h, hu, he⟩
  have hcell := congrArg (fun r : WRes => r.get l) he
  simp only [ResU.single_get_self] at hcell
  have hv := congrArg CellU.erase (Option.some.inj hcell)
  change Val.loc 0 = u at hv
  subst u
  rcases hu with hu | hu
  · omega
  · have hx := congrArg Subtype.val hu
    cases hx

theorem fixed_member_is_not_a_general_loan_identity (l : Loc) (β : Life) :
    MutStep (view l β) 1 l (before β) (after β) ∧
      ¬ FixedMemberReturn l β (family β 2) (ResU.single l (after β)) :=
  ⟨member_write_is_legal l β, fixed_member_return_rejected l β⟩

#print axioms member_write_is_legal
#print axioms member_predicates_differ
#print axioms fixed_member_return_rejected
#print axioms fixed_member_is_not_a_general_loan_identity
end BoCa.Fig16.LogRel.Core.Chain.SI.LoanMemberBoundary
end
