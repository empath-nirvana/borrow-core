import Core.Chain.SI.LoanX.Cell

/-! The owned registry fragment connects a parked scalar loan to the actual
current-main value interpretation after unrelated registry changes. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

def unitLoan (l : Loc) (β : Life) : Loan := .mut l β (unitFamily β 0)

/-- Each active scalar descriptor names a coherent current-main location family.
Unrelated registry entries and retired entries impose no extra restriction. -/
def WorldSat (m : Registry) (Θ : LocTy) : Prop :=
  Θ.OK ∧ ∀ γ l β, m γ = some [unitLoan l β] →
    Θ l β = some (unitFamily β)

def Ownγ (γ : Loc) (g : GRes) : Prop :=
  ∃ l β, 0 < g.tokF γ [unitLoan l β]

/-- Registry validity recovers the exact descriptor carried by a parked claim. -/
theorem owned_key {m : Registry} {Θ : LocTy} {γ : Loc} {g : GRes}
    (hs : WorldSat m Θ) (hv : (reg m + g).Valid) (ho : Ownγ γ g) :
    ∃ l β, m γ = some [unitLoan l β] ∧ Θ l β = some (unitFamily β) := by
  obtain ⟨l, β, hc⟩ := ho
  have hm : m γ = some [unitLoan l β] :=
    hv.tokF_agree m γ [unitLoan l β]
      (by simp [reg]) (by simpa [reg] using hc)
  exact ⟨l, β, hm, hs.2 γ l β hm⟩

/-- Closing a slot does not disturb coherence for other active claims. -/
theorem WorldSat.close {m : Registry} {Θ : LocTy} {γ : Loc}
    (hs : WorldSat m Θ) : WorldSat (put m γ []) Θ := by
  refine ⟨hs.1, ?_⟩
  intro γ' l β hm
  by_cases he : γ' = γ
  · subst γ'
    simp [put] at hm
  · exact hs.2 γ' l β (by simp [put, he] at hm; exact hm)

/-- Opening an additional scalar registry entry preserves world coherence when its
key is already present. The algebraic allocation lemma supplies freshness. -/
theorem WorldSat.put_scalar {m : Registry} {Θ : LocTy} {γ l : Loc} {β : Life}
    (hs : WorldSat m Θ) (hk : Θ l β = some (unitFamily β)) :
    WorldSat (put m γ [unitLoan l β]) Θ := by
  refine ⟨hs.1, ?_⟩
  intro γ' l' β' hm
  by_cases he : γ' = γ
  · subst γ'
    have hloan : unitLoan l β = unitLoan l' β' := by
      have hh : [unitLoan l β] = [unitLoan l' β'] :=
        Option.some.inj (by simpa [put] using hm)
      simpa using hh
    unfold unitLoan at hloan
    cases hloan
    exact hk
  · exact hs.2 γ' l' β' (by simp [put, he] at hm; exact hm)

/-- Existing scalar claims remain coherent under an actual current-main world
extension. The new world supplies its own `OK` proof. -/
theorem WorldSat.ext {m : Registry} {Θ Θ' : LocTy}
    (hs : WorldSat m Θ) (he : Θ.Ext Θ') (hOK : Θ'.OK) :
    WorldSat m Θ' :=
  ⟨hOK, fun γ l β hm => he l β (unitFamily β) (hs.2 γ l β hm)⟩

/-- A concrete extension keeps the first live loan while admitting a second
independent scalar loan at a fresh world key. -/
def exampleWorld₀ : LocTy := LocTy.empty.add 0 1 (unitFamily 1)
def exampleWorld₁ : LocTy := exampleWorld₀.add 1 2 (unitFamily 2)
def exampleReg₀ : Registry := put (fun _ => none) 0 [unitLoan 0 1]
def exampleReg₁ : Registry := put exampleReg₀ 1 [unitLoan 1 2]

theorem unitFamily_down (β : Life) : DownFam β (unitFamily β) :=
  fun _ _ _ h => h

theorem exampleWorld₀_ok : exampleWorld₀.OK := by
  refine ⟨LocTy.down_add LocTy.empty_down 0 (unitFamily_down 1), 3, ?_⟩
  exact LocTy.fresh_add (N := 3) (N' := 3)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)

theorem exampleWorld₁_ok : exampleWorld₁.OK := by
  have hf3 : exampleWorld₀.Fresh 3 := LocTy.fresh_add (N := 3) (N' := 3)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)
  refine ⟨LocTy.down_add exampleWorld₀_ok.1 1 (unitFamily_down 2), 3, ?_⟩
  exact LocTy.fresh_add hf3 le_rfl (by decide) 1 (unitFamily 2)

theorem exampleWorld_extension : exampleWorld₀.Ext exampleWorld₁ := by
  apply LocTy.ext_add (l := 1) (F := unitFamily 2)
  exact LocTy.fresh_add (N := 2) (N' := 2)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)

theorem exampleWorldSat₀ : WorldSat exampleReg₀ exampleWorld₀ := by
  have he : WorldSat (fun _ => none) exampleWorld₀ := by
    refine ⟨exampleWorld₀_ok, ?_⟩
    intro γ l β hm
    cases hm
  exact he.put_scalar (by simp [exampleWorld₀, LocTy.add_self])

theorem exampleWorldSat₁ : WorldSat exampleReg₁ exampleWorld₁ := by
  have h0 := exampleWorldSat₀.ext exampleWorld_extension exampleWorld₁_ok
  exact h0.put_scalar (by simp [exampleWorld₁, LocTy.add_self])

abbrev emptyRegistry : Registry := fun _ => none
abbrev W0 : Registry := exampleReg₀
abbrev W1 : Registry := exampleReg₁
abbrev Θ0 : LocTy := exampleWorld₀
abbrev Θ1 : LocTy := exampleWorld₁

theorem W0_fresh_second : W0 1 = none := by
  simp [W0, exampleReg₀, put]

theorem W0_sat : WorldSat W0 Θ0 := exampleWorldSat₀
theorem W1_sat : WorldSat W1 Θ1 := exampleWorldSat₁

theorem W0_ne_W1 : W0 ≠ W1 := by
  intro he
  have hh := congrArg (fun m : Registry => m 1) he
  simp [W0, W1, exampleReg₀, exampleReg₁, put] at hh

theorem Θ0_ne_Θ1 : Θ0 ≠ Θ1 := by
  intro he
  have hh := congrArg (fun Θ : LocTy => Θ 1 2) he
  simp [Θ0, Θ1, exampleWorld₀, exampleWorld₁, LocTy.add] at hh

theorem W1_allocate : FP (reg W0)
    (reg W1 + claim 1 [unitLoan 1 2] + permit 1 [unitLoan 1 2]) := by
  simpa [W1, exampleReg₁] using
    (allocate W0 1 [unitLoan 1 2] W0_fresh_second)

theorem W1_first_valid (κ : Life) :
    (reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1] + GRes.life κ).Valid := by
  have hm : W1 0 = some [unitLoan 0 1] := by
    simp [W1, exampleReg₁, exampleReg₀, put]
  exact GRes.valid_add_life (registered_valid W1 0 [unitLoan 0 1] hm)
    (by simp [reg, claim, permit])

/-- Physical return plus the matching owned claim gives the actual main `vN Mut` fact. -/
theorem owned_return_typed {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
    {m : Registry} {Θ : LocTy} {γ : Loc} {g : GRes}
    (hs : WorldSat m Θ) (_hv : (reg m + g).Valid) (_ho : Ownγ γ g)
    {l : Loc} {β : Life} {w : Val} {ρ : WRes}
    (hm : m γ = some [unitLoan l β]) (hr : cellOf (unitLoan l β) w ρ)
    (δ : BoCa.Lifetime.LSub) (a : Lifetime.Life) (α : Life)
    (ha : a.interp δ = some α) (hab : α ≤ β) (n : Nat) :
    vN (ℍ := ℍ) (.mut a .unit) δ Θ n w ρ := by
  have hk := hs.2 γ l β hm
  obtain ⟨u, hχ, hu, rfl, rfl⟩ := hr
  exact W1_scalar_return_main a δ Θ l α β ha hab hk n u hχ hu

/-- The return permission supplies the descriptor key; registry agreement also
shows that the parked claim and this physical return refer to that same entry. -/
theorem owned_return_typed_match {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
    {m : Registry} {Θ : LocTy} {γ : Loc} {g : GRes}
    (hs : WorldSat m Θ) (ho : Ownγ γ g)
    {l : Loc} {β : Life} {w : Val} {ρ : WRes}
    (hv : (reg m + g + permit γ [unitLoan l β]).Valid)
    (hr : cellOf (unitLoan l β) w ρ)
    (δ : BoCa.Lifetime.LSub) (a : Lifetime.Life) (α : Life)
    (ha : a.interp δ = some α) (hab : α ≤ β) (n : Nat) :
    vN (ℍ := ℍ) (.mut a .unit) δ Θ n w ρ := by
  have hvg : (reg m + g).Valid := GRes.Valid.left hv
  obtain ⟨l', β', hclaim, _⟩ := owned_key hs hvg ho
  have hreturn : m γ = some [unitLoan l β] :=
    hv.wrF_agree m γ [unitLoan l β] (by simp [reg])
      (by simp [permit])
  have _ : [unitLoan l' β'] = [unitLoan l β] :=
    Option.some.inj (hclaim.symm.trans hreturn)
  exact owned_return_typed hs hvg ho hreturn hr δ a α ha hab n

/-- An arbitrary returned descriptor is identified by the owned fragment, so
the typed application need not assume a matching location or family. -/
theorem owned_return_any {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
    {m : Registry} {Θ : LocTy} {γ : Loc} {g : GRes} {d : Loan}
    {w : Val} {ρ : WRes} (hs : WorldSat m Θ) (ho : Ownγ γ g)
    (hv : (reg m + g + permit γ [d]).Valid) (hr : cellOf d w ρ)
    (n : Nat) :
    ∃ l β, d = unitLoan l β ∧ m γ = some [d] ∧
      vN (ℍ := ℍ) (.mut (.var 0) .unit)
        (BoCa.Lifetime.LSub.empty.extend 0 β) Θ n w ρ := by
  have hvg : (reg m + g).Valid := GRes.Valid.left hv
  obtain ⟨l, β, hc, hk⟩ := owned_key hs hvg ho
  have hp : m γ = some [d] :=
    hv.wrF_agree m γ [d] (by simp [reg]) (by simp [permit])
  have he : unitLoan l β = d := by
    have hh : [unitLoan l β] = [d] := Option.some.inj (hc.symm.trans hp)
    simpa using hh
  subst d
  refine ⟨l, β, rfl, hc, ?_⟩
  exact owned_return_typed hs hvg ho hc hr
    (BoCa.Lifetime.LSub.empty.extend 0 β) (.var 0) β
    (by exact interp_ext_self BoCa.Lifetime.LSub.empty 0 β) (le_refl β) n

#print axioms owned_key
#print axioms owned_return_typed
#print axioms owned_return_typed_match
#print axioms owned_return_any
#print axioms W1_sat
#print axioms W1_allocate
#print axioms W1_first_valid

end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
