import TypedCaseProof.Program

/-! Concrete positive and adversarial controls for the restricted typed scalar case. -/
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub)
open Classical

def scalarCell (l : Loc) (β : Life) : WRes :=
  ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β)
    (unitFamily β 0) ⟨rfl,rfl⟩)

theorem first_claim_positive (κ : Life) : Ownγ 0 (claim 0 [unitLoan 0 1] + GRes.life κ) :=
  ⟨0,1,by simp [claim]⟩

theorem W1_admitted (κ : Life) :
    (reg W1 + (claim 0 [unitLoan 0 1] + GRes.life κ)).Valid :=
  GRes.Valid.left (show ((reg W1 + (claim 0 [unitLoan 0 1] + GRes.life κ)) +
    permit 0 [unitLoan 0 1]).Valid by
      simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using W1_first_valid κ)

theorem W1_reply (k : Nat) (ls : List SRec) :
    RegistryReply k ls Val.unit (PMap.empty,reg W1) := ⟨rfl,rfl,W1,Θ1,W1_sat,rfl⟩

theorem W1_return (k : Nat) (ls : List SRec) :
    Returned 0 k ls (Val.loc 0) (scalarCell 0 1,reg W1 + permit 0 [unitLoan 0 1]) :=
  ⟨W1,Θ1,W1_sat,unitLoan 0 1,⟨Val.unit,ResU.inStratum_empty 1,⟨rfl,rfl⟩,rfl,rfl⟩,rfl⟩

theorem W1_return_actual_main (n : Nat) :
    vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 1) Θ1 n (Val.loc 0) (scalarCell 0 1) := by
  apply owned_return_typed_match W1_sat (first_claim_positive 0)
    (g := claim 0 [unitLoan 0 1] + GRes.life 0)
    (by simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using W1_first_valid 0)
    (show cellOf (unitLoan 0 1) (Val.loc 0) (scalarCell 0 1) from
      ⟨Val.unit,ResU.inStratum_empty 1,⟨rfl,rfl⟩,rfl,rfl⟩)
    (LSub.empty.extend 0 1) (.var 0) 1 (interp_ext_self _ _ _) le_rfl n

/-- The single case succeeds with actual main scalar types, proposed owned Ref/U, a
real capture and extra suspension. The universally quantified admitted futures include
this genuinely changed main world/registry, with an inhabited typed reply. -/
theorem complete_scalar_case (n : Nat) :
    vN (ℍ := ℍ) (.ref .unit) LSub.empty Θ0 n (Val.loc 0) (ResU.single 0 (CellU.ownOf Val.unit)) ∧
    erwpX (ℍ := ℍ) phi (mask 0 0) (opTableX (parkTab 0)) (scalarPost 0 0 0) n []
      (storedProgram 0) (ResU.single 0 (CellU.ownOf Val.unit),reg emptyRegistry + GRes.life 0) ∧
    W0 ≠ W1 ∧ Θ0 ≠ Θ1 ∧ WorldSat W1 Θ1 ∧
    (reg W1 + (claim 0 [unitLoan 0 1] + GRes.life 0)).Valid ∧
    RegistryReply n [] Val.unit (PMap.empty,reg W1) ∧
    vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 1) Θ1 n (Val.loc 0) (scalarCell 0 1) := by
  have hp := storedProgram_typed emptyRegistry Θ0 0 0 0 1 rfl W0_sat n
  exact ⟨hp.1,hp.2,W0_ne_W1,Θ0_ne_Θ1,W1_sat,W1_admitted 0,W1_reply n [],W1_return_actual_main n⟩

/-- A second legitimate scalar loan cannot masquerade as the first loan's return. -/
theorem wrong_return_rejected (k : Nat) (ls : List SRec) :
    ¬ ReturnedAt 0 W1 k ls (Val.loc 1) (scalarCell 1 2,reg W1 + permit 1 [unitLoan 1 2]) := by
  rintro ⟨d,_,hg⟩
  have hh := congrArg (fun g : GRes => g.wrF 0 [d]) hg
  simp [reg,permit] at hh

/-- The typed storage mechanism exactly specializes to current recursive Ref(U) with
zero ghost. This is a value-clause fact, not an execution equivalence to current rwp. -/
theorem zero_protocol_stored_U (δ : LSub) (Θ : LocTy) (n : Nat) (a : Loc) :
    RefX (liftVal (fun v r => vN (ℍ := ℍ) (.thunk (.ret .unit)) δ Θ n v r))
      (Val.loc a) (ResU.single a (CellU.ownOf TypedBridge.unitThunk),0) :=
  (RefX_zero_iff (.thunk (.ret .unit)) δ Θ n _ _).mpr (plain_stored_U_unit δ Θ n a)

/-- The expected slot cannot be paired with a different legitimate loan descriptor. -/
theorem forged_same_slot_rejected :
    ¬ (reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 1 2]).Valid := by
  intro hv
  have he := (List.cons.inj (match_return hv)).1
  have hh := congrArg (fun d : Loan => match d with | .mut l _ _ => l | .imm _ _ => 0) he
  simp [unitLoan] at hh

/-- Positive ownership is not inferred from a small-index execution obligation. It
remains mandatory even at index zero, and cannot be erased by wrapping κ in Ref. -/
theorem ScalarU_no_ghost_erasure (γ : Loc) (M : Mask) (Q : PostX) (k : Nat)
    (ls : List SRec) (κv : Val) (ρ : WRes) :
    ¬ ScalarU (ℍ := ℍ) γ M Q k ls κv (ρ,0) := by
  rintro ⟨⟨l,β,hpos⟩,_⟩
  simp at hpos

theorem ScalarRef_no_ghost_erasure (γ : Loc) (M : Mask) (Q : PostX) (k : Nat)
    (ls : List SRec) (p : Val) (ρ : WRes) :
    ¬ ScalarRef (ℍ := ℍ) γ M Q k ls p (ρ,0) := by
  intro h
  obtain ⟨l,β,hpos⟩ := ScalarRef_preserves_claim h
  simp at hpos

#print axioms forged_same_slot_rejected
#print axioms ScalarU_no_ghost_erasure
#print axioms ScalarRef_no_ghost_erasure
#print axioms W1_admitted
#print axioms W1_return_actual_main
#print axioms complete_scalar_case
#print axioms wrong_return_rejected
#print axioms zero_protocol_stored_U
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
