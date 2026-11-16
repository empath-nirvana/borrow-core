import Core.Chain.SI.LoanX.WorldSat
import TypedCaseProof.TypedResources
import TypedCaseProof.GhostUpdate
import TypedCaseProof.GhostValidity
import TypedCaseProof.StorePark
import Core.Chain.SI.LoanX.MutLoan

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.BoLo (Kont Head hndE hndVal performE opPayload freeE)
open BoCa.Lifetime (LSub)
open Classical

def ReturnedAt (γ : Loc) (m : Registry) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  ∃ d : Loan, cellOf d w x.1 ∧ x.2 = reg m + permit γ [d]

def Returned (γ : Loc) : Nat → List SRec → Val → XProp := fun k ls w x =>
  ∃ (m : Registry) (Θ : LocTy), WorldSat m Θ ∧ ReturnedAt γ m k ls w x

def Outgoing (γ : Loc) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  ∃ (m : Registry) (Θ : LocTy) (d : Loan), WorldSat m Θ ∧ m γ = some [d] ∧
    cellOf d w x.1 ∧ x.2 = reg m + permit γ [d]

def loanEntry (γ : Loc) : OpEntX where
  q := .lin
  remask := false
  PA := Outgoing γ
  PB := Returned γ
  fin := none
  wc := fun ls ls' _ => ls' = ls

def RegistryMsg (γ : Loc) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  w = Val.unit ∧ x.1 = PMap.empty ∧ ∃ (m : Registry) (Θ : LocTy),
    WorldSat m Θ ∧ x.2 = reg m ∧ ∃ l β, m γ = some [unitLoan l β]

def RegistryReply : Nat → List SRec → Val → XProp := fun _ _ w x =>
  w = Val.unit ∧ x.1 = PMap.empty ∧ ∃ (m : Registry) (Θ : LocTy), WorldSat m Θ ∧ x.2 = reg m

def parkEntry (γ : Loc) : OpEntX where
  q := .lin
  remask := false
  PA := RegistryMsg γ
  PB := RegistryReply
  fin := none
  wc := fun ls ls' _ => ls' = ls

def parkTab (γ : Loc) : OpTabX := fun m i =>
  if m = 8 ∧ i = 0 then some (parkEntry γ) else none

def loanTab (γ : Loc) : OpTabX := fun m i =>
  if m = 7 ∧ i = 0 then some (loanEntry γ) else parkTab γ m i

def phi : LocFam := LocFam.empty
theorem phi_down : phi.Down := by intro l β F h; simp [phi] at h

def mask (l : Loc) (κ : Life) : Mask := {(l,Auth.mloan κ)}

/-- The result uses ACTUAL main vN Ref unit, plus the authoritative discharged ledger. -/
def scalarPost (γ l : Loc) (κ : Life) : PostX := fun _ k _ w x =>
  w = Val.loc l ∧ ∃ (m : Registry) (Θ : LocTy), WorldSat m Θ ∧ m γ = some [] ∧
    x.2 = reg m + GRes.life κ ∧ vN (ℍ := ℍ) (.ref .unit) LSub.empty Θ k w x.1

theorem scalarPost_down (γ l : Loc) (κ : Life) : (scalarPost γ l κ).Down := by
  rintro C k ls w x ⟨hv,m,Θ,hs,hm,hg,ht⟩
  exact ⟨hv,m,Θ,hs,hm,hg,vN_down _ _ _ _ _ _ ht⟩

/-- A proposed restricted U clause: POSITIVE owned scalar claim, admitted typed registry
futures justified by that resource, actual current-main Mut arguments, and masked execution.
This is a resource-aware branded callable slice, not unchanged Goal791N U. -/
def ScalarU (γ : Loc) (M : Mask) (Q : PostX) (k : Nat) (ls : List SRec) (κv : Val) (x : XRes) : Prop :=
  Ownγ γ x.2 ∧ ∀ (m : Registry) (Θ : LocTy), WorldSat m Θ → (reg m + x.2).Valid →
    ∀ ls', ls' = ls → ∀ j, j < k → ∀ (w : Val) (y z : XRes),
      ReturnedAt γ m j ls' w y → CompX x y z → z.2.Valid →
      (∃ β : Life, vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 β) Θ j w y.1) ∧
      erwpX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q j ls'
        (.app (.app κv.1 (.val (Val.inj₁ .unit))) (.val w)) z

abbrev ScalarRef (γ : Loc) (M : Mask) (Q : PostX) (k : Nat) (ls : List SRec) : Val → XProp :=
  RefX (ScalarU (ℍ := ℍ) γ M Q k ls)

theorem ScalarU_le {γ : Loc} {M : Mask} {Q : PostX} {k n : Nat} {ls : List SRec}
    {κv : Val} {x : XRes} (hkn : k ≤ n) (hu : ScalarU (ℍ := ℍ) γ M Q n ls κv x) :
    ScalarU (ℍ := ℍ) γ M Q k ls κv x :=
  ⟨hu.1,fun m Θ hs hv ls' hls j hj w y z hR hc hz => hu.2 m Θ hs hv ls' hls j (by omega) w y z hR hc hz⟩

/-- Capture's execution proof is strengthened into the typed future obligation using
POSITIVE J and registry/world coherence. No target typed-continuation law is assumed. -/
theorem ScalarU_of_capture {γ : Loc} {M : Mask} {Q : PostX} {k : Nat} {ls : List SRec}
    {κv : Val} {x : XRes} (ho : Ownγ γ x.2)
    (hk : KapRelX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q (loanEntry γ) k ls κv x) :
    ScalarU (ℍ := ℍ) γ M Q k ls κv x := by
  refine ⟨ho,?_⟩
  intro m Θ hs hv ls' hls j hj w y z hR hc hz
  obtain ⟨d,hcell,hg⟩ := hR
  have hvalid : (reg m + x.2 + permit γ [d]).Valid := by
    rw [hc.2,hg] at hz
    simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hz
  obtain ⟨l,β,hd,hm,htyped⟩ := owned_return_any hs ho hvalid hcell j
  refine ⟨⟨β,htyped⟩,?_⟩
  exact hk ls' hls j hj w y z ⟨m,Θ,hs,d,hcell,hg⟩ hc

theorem ScalarU_apply {γ : Loc} {M : Mask} {Q : PostX} {k j : Nat} {ls : List SRec}
    {κv w : Val} {x y z : XRes} (hu : ScalarU (ℍ := ℍ) γ M Q k ls κv x)
    (hj : j < k) {m : Registry} {Θ : LocTy} (hs : WorldSat m Θ)
    (hR : ReturnedAt γ m j ls w y) (hc : CompX x y z) (hz : z.2.Valid) :
    (∃ β : Life, vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 β) Θ j w y.1) ∧
      erwpX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q j ls
        (.app (.app κv.1 (.val (Val.inj₁ .unit))) (.val w)) z := by
  obtain ⟨d,hcell,hg⟩ := hR
  have hv : (reg m + x.2).Valid := GRes.Valid.left
    (show ((reg m + x.2) + permit γ [d]).Valid by
      rw [hc.2,hg] at hz
      simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hz)
  exact hu.2 m Θ hs hv ls rfl j hj w y z ⟨d,hcell,hg⟩ hc hz

theorem ScalarRef_preserves_claim {γ : Loc} {M : Mask} {Q : PostX} {k : Nat}
    {ls : List SRec} {p : Val} {x : XRes}
    (hr : ScalarRef (ℍ := ℍ) γ M Q k ls p x) : Ownγ γ x.2 :=
  RefX_preserves_owned (fun _ _ h => h.1) hr

#print axioms ScalarU_of_capture
#print axioms ScalarU_apply
#print axioms ScalarRef_preserves_claim
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
