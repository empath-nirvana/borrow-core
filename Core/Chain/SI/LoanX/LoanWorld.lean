import Core.Chain.SI.LoanX.KWBridge

/-! A typed stop world combines main `KW` with an authoritative loan
registry and its scalar-family coherence [spec §62]. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

structure LoanKW where
  typed : KW
  registry : Registry
  sat : WorldSat registry typed.Θ

/-- An owed world keeps every existing `KW.Owed` obligation and is compatible
with the continuation's complete ghost share at the new registry. -/
def LoanKW.Owed (x : LoanKW) (f : Life) (y : LoanKW) (share : XRes) : Prop :=
  x.typed.Owed f y.typed share.1 ∧ (reg y.registry + share.2).Valid

theorem LoanKW.owed_self (x : LoanKW) (f : Life) (share : XRes)
    (hc : ConsistentX x.typed.c share.1)
    (hv : (reg x.registry + share.2).Valid) :
    x.Owed f x share :=
  ⟨KW.owed_self x.sat.1 f hc, hv⟩

theorem LoanKW.Owed.trans {x y z : LoanKW} {f : Life} {share : XRes}
    (hxy : x.Owed f y share) (hyz : y.Owed f z share) : x.Owed f z share :=
  ⟨KW.Owed.trans hxy.1 hyz.1, hyz.2⟩

def scalarWorld₀ : LoanKW := ⟨exampleKW₀, W0, W0_sat⟩
def scalarWorld₁ : LoanKW := ⟨exampleKW₁, W1, W1_sat⟩

/-- The concrete second-stop reply is admitted by both main `KW.Owed` and
the owned registry relation. -/
theorem scalarWorld_reply (s : Loc) (v : Val) (κ : Life) :
    scalarWorld₀.Owed 1 scalarWorld₁
      (ResU.single s (CellU.ownOf v), claim 0 [unitLoan 0 1] + GRes.life κ) := by
  refine ⟨exampleKW_owed_own s v, ?_⟩
  have hv := W1_first_valid κ
  have h := GRes.Valid.left (show
    ((reg W1 + (claim 0 [unitLoan 0 1] + GRes.life κ)) +
      permit 0 [unitLoan 0 1]).Valid by
      simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hv)
  exact h

#print axioms LoanKW.owed_self
#print axioms LoanKW.Owed.trans
#print axioms scalarWorld_reply
end BoCa.Fig16.LogRel.Core.Chain.SI
