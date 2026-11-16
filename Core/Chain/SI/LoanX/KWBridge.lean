import Core.Chain.SI.LoanX.WorldSat
import Core.Chain.SI.MFrameK

/-! A concrete owned scalar reply satisfies the existing main `KW.Owed`
conditions as well as registry/world coherence [spec §62]. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge

def exampleKW₀ : KW := ⟨Θ0, fun _ => none, 1⟩
def exampleKW₁ : KW := ⟨Θ1, fun _ => none, 1⟩

/-- The additional world key lies below the stop floor. At that floor the
original key makes the `FoldInv` preservation obligation vacuous. -/
theorem exampleKW_owed_own (s : Loc) (v : Val) :
    exampleKW₀.Owed 1 exampleKW₁ (ResU.single s (CellU.ownOf v)) := by
  have hf : Θ0.Fresh 2 := LocTy.fresh_add (N := 2) (N' := 2)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)
  refine ⟨LocTy.extP_add hf (by decide) 1 (unitFamily 2) _,
    W1_sat.1, consistentX_of_top (ResU.inStratum_single_own _ s v) _, le_rfl, ?_⟩
  intro g hfg hfold
  change Θ0.FoldInv g at hfold
  have hkey : Θ0 0 1 ≠ none := by
    change (LocTy.empty.add 0 1 (unitFamily 1)) 0 1 ≠ none
    simp [LocTy.add_self]
  have hlt : g < (1 : Life) := hfold.1 0 1 hkey
  exact (not_lt_of_ge hfg hlt).elim

/-- The same changed reply also respects the outstanding registry fragments. -/
theorem W1_main_reply_admitted (s : Loc) (v : Val) (κ : Life) :
    exampleKW₀.Owed 1 exampleKW₁ (ResU.single s (CellU.ownOf v)) ∧
    WorldSat W1 Θ1 ∧
    (reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1] + GRes.life κ).Valid :=
  ⟨exampleKW_owed_own s v, W1_sat, W1_first_valid κ⟩

#print axioms exampleKW_owed_own
#print axioms W1_main_reply_admitted
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
