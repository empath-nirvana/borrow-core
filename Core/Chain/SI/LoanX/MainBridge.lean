import Core.Chain.Goal791N
import Core.Chain.SI.AFrameK

/-! Owned-loan return facts at the current typed interpretation [spec §62].
All typing conclusions below use actual `Goal791N.vN/cN`, unchanged. `FamilyBrand`
is proof-carrying metadata extracted from that interpretation. The proposed
resource-aware callable and storage clauses are separate from this module.
-/
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub)
open BoCa.BoLo (Head Kont)

structure FamilyBrand where
  loc : Loc
  life : Life
  family : Nat → Val → SPropS Loc Val life

/-- Main mutL permits different indexed members of the SAME stable family. -/
def ReturnedCell (b : FamilyBrand) (n : Nat) (v : Val) (ρ : WRes) : Prop :=
  ∃ (u : Val) (h : ResU.InStratum b.life (PMap.empty : WRes)) (j : Nat)
    (hu : b.family j u ⟨PMap.empty,h⟩), n ≤ j ∧ v = Val.loc b.loc ∧
      ρ = ResU.single b.loc (CellU.mutOf b.life u PMap.empty h (b.family j) hu)

/-- The precise current-main semantic information an owned family claim must justify.
The last conjunct is already required by main's Mut clause. -/
def BrandAt (A : VTy) (δ : LSub) (Θ : LocTy) (b : FamilyBrand) : Prop :=
  Θ b.loc b.life = some b.family ∧
  b.family = famL b.life (fun Θ j u r => vN (ℍ := ℍ) A δ Θ j u r) Θ ∧
  ∀ Θ' j u r, vN (ℍ := ℍ) A δ Θ' j u r → r.InStratum b.life

def Shallow (ρ : WRes) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.wit = PMap.empty

theorem returned_shallow {b : FamilyBrand} {n : Nat} {v : Val} {ρ : WRes}
    (h : ReturnedCell b n v ρ) : Shallow ρ := by
  obtain ⟨u,hχ,j,hu,_,_,rfl⟩ := h
  intro l ψ hg
  obtain ⟨_,rfl⟩ := ResU.single_get_eq_some hg
  exact CellU.wit_mutOf _ _ _ _ _ _

/-- Reconstructs actual recursive vN, including payloads A containing U/μ/etc., provided
the existing Mut uniformity and family-coherence facts hold. -/
theorem returned_to_vN {A : VTy} {a : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {b : FamilyBrand} {α : Life} {n : Nat} {v : Val} {ρ : WRes}
    (ha : a.interp δ = some α) (hab : α ≤ b.life)
    (hb : BrandAt (ℍ := ℍ) A δ Θ b) (hr : ReturnedCell b n v ρ) :
    vN (ℍ := ℍ) (.mut a A) δ Θ n v ρ := by
  obtain ⟨hkey,hfam,hunif⟩ := hb
  obtain ⟨u,hχ,j,hu,hnj,hv,hρ⟩ := hr
  refine ⟨α,ha,b.life,hab,?_,hunif⟩
  unfold mutL
  rw [← hfam]
  exact ⟨b.loc,u,PMap.empty,hχ,j,hu,hnj,hv,hkey,hρ⟩

/-- Every shallow actual Mut value exposes a brand at its ACTUAL (possibly slack) lifetime. -/
theorem vN_to_returned {A : VTy} {a : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {n : Nat} {v : Val} {ρ : WRes}
    (hv : vN (ℍ := ℍ) (.mut a A) δ Θ n v ρ) (hs : Shallow ρ) :
    ∃ (α : Life) (b : FamilyBrand), a.interp δ = some α ∧ α ≤ b.life ∧
      BrandAt (ℍ := ℍ) A δ Θ b ∧ ReturnedCell b n v ρ := by
  obtain ⟨α,ha,β,hab,hm,hunif⟩ := hv
  obtain ⟨l,u,χ,hχ,j,hu,hnj,hv,hkey,hρ⟩ := hm
  have he : χ = PMap.empty := by
    have hh := hs l (CellU.mutOf β u χ hχ
      (famL β (fun Θ j u r => vN (ℍ := ℍ) A δ Θ j u r) Θ j) hu)
      (by rw [hρ]; exact ResU.single_get_self _ _)
    simpa only [CellU.wit_mutOf] using hh
  subst χ
  exact ⟨α,⟨l,β,famL β (fun Θ j u r => vN (ℍ := ℍ) A δ Θ j u r) Θ⟩,
    ha,hab,⟨hkey,rfl,hunif⟩,⟨u,hχ,j,hu,hnj,hv,hρ⟩⟩

theorem shallow_mut_iff_brand (A : VTy) (a : Lifetime.Life) (δ : LSub) (Θ : LocTy)
    (n : Nat) (v : Val) (ρ : WRes) :
    (vN (ℍ := ℍ) (.mut a A) δ Θ n v ρ ∧ Shallow ρ) ↔
    ∃ (α : Life) (b : FamilyBrand), a.interp δ = some α ∧ α ≤ b.life ∧
      BrandAt (ℍ := ℍ) A δ Θ b ∧ ReturnedCell b n v ρ := by
  constructor
  · intro h; exact vN_to_returned h.1 h.2
  · rintro ⟨α,b,ha,hab,hb,hr⟩
    exact ⟨returned_to_vN ha hab hb hr,returned_shallow hr⟩

/-- Existing ExtR supplies exact key and above-world agreement when the RETURNED
borrow is in the resource. This is derived from the current definition, not assumed. -/
theorem brandAt_extR {A : VTy} {δ : LSub} {Θ Θ' : LocTy} {b : FamilyBrand}
    {n : Nat} {v : Val} {ρ : WRes} (hb : BrandAt (ℍ := ℍ) A δ Θ b)
    (hr : ReturnedCell b n v ρ) (he : Θ.ExtR Θ' ρ) : BrandAt (ℍ := ℍ) A δ Θ' b := by
  obtain ⟨hkey,hfam,hunif⟩ := hb
  obtain ⟨u,hχ,j,hu,hnj,hv,rfl⟩ := hr
  have hc : CellIn (ResU.single b.loc (CellU.mutOf b.life u PMap.empty hχ (b.family j) hu)) b.life := by
    have hh := CellIn.single (l := b.loc)
      (ψ := CellU.mutOf b.life u PMap.empty hχ (b.family j) hu) (by simp [CellU.kind_mutOf])
    simpa only [CellU.at_mutOf] using hh
  obtain ⟨hk,ha⟩ := he.1 b.loc b.life b.family hkey hc
  refine ⟨hk,?_,hunif⟩
  rw [hfam]
  funext k w r
  simp only [famL,ha]

/-- Changes of member/content are admitted through ReturnedCell; current-main typing
is recovered at the returned resource's legitimate future world. -/
theorem returned_future_typed {A : VTy} {a : Lifetime.Life} {δ : LSub} {Θ Θ' : LocTy}
    {b : FamilyBrand} {α : Life} {n : Nat} {v : Val} {ρ : WRes}
    (ha : a.interp δ = some α) (hab : α ≤ b.life)
    (hb : BrandAt (ℍ := ℍ) A δ Θ b) (hr : ReturnedCell b n v ρ)
    (he : Θ.ExtR Θ' ρ) : vN (ℍ := ℍ) (.mut a A) δ Θ' n v ρ :=
  returned_to_vN ha hab (brandAt_extR hb hr he) hr

/-- Scalar unit family is index-independent, exactly the common case W1's fixed P can encode. -/
theorem unit_member_constant (δ : LSub) (Θ : LocTy) (β : Life) (j k : Nat) :
    famL β (fun Θ n u r => vN (ℍ := ℍ) .unit δ Θ n u r) Θ j =
    famL β (fun Θ n u r => vN (ℍ := ℍ) .unit δ Θ n u r) Θ k := rfl

/-- Physical ownership of storage/capture cells is invisible to current U's ExtR. -/
def NoBorrow (ρ : WRes) : Prop := ∀ a, ¬ CellIn ρ a

theorem own_noBorrow (l : Loc) (v : Val) : NoBorrow (ResU.single l (CellU.ownOf v)) := by
  rintro a ⟨m,ψ,hg,hkind,_⟩
  by_cases hm : m = l
  · subst m
    rw [ResU.single_get_self] at hg
    cases Option.some.inj hg
    exact hkind rfl
  · rw [ResU.single_get_ne _ hm] at hg
    cases hg

theorem noBorrow_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : NoBorrow ρ) : NoBorrow ρ₂ := fun a hi => h a (hi.of_right hc)

theorem noBorrow_comp {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : NoBorrow ρ₁) (h₂ : NoBorrow ρ₂) : NoBorrow ρ := by
  intro a hi
  rcases CellIn.split hc hi with hi | hi
  · exact h₁ a hi
  · exact h₂ a hi

theorem noBorrow_extR_any (Θ Θ' : LocTy) {ρ : WRes} (h : NoBorrow ρ) : Θ.ExtR Θ' ρ :=
  ⟨fun _ a _ _ hi => (h a hi).elim,fun x _ hi => (h x.2 hi).elim⟩

/-- ACTUAL main Ref(U C) storage still demands every OK world when its physical resources
are only owned cells. A ghost claim cannot be recovered from this current clause alone.
This is a demand theorem, not a claim that every such thunk is untypable. -/
theorem stored_U_all_worlds (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat)
    (p : Val) (ρ : WRes) (hn : NoBorrow ρ)
    (hv : vN (ℍ := ℍ) (.ref (.thunk C)) δ Θ n p ρ) :
    ∃ (l : Loc) (κ : Val) (σ : WRes), p = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf κ)) σ ρ ∧
      ∀ Θ' : LocTy, Θ'.OK → ∀ c, ConsistentX c σ → ∀ ls,
        cN (ℍ := ℍ) C δ Θ' c n ls (forceE C κ.1) σ := by
  obtain ⟨l,κ,σ,hp,hc,hU⟩ := hv
  refine ⟨l,κ,σ,hp,hc,?_⟩
  intro Θ' hOK c hview ls
  exact hU Θ' (noBorrow_extR_any Θ Θ' (noBorrow_right hc hn)) hOK c hview ls

def unitFamily (β : Life) : Nat → Val → SPropS Loc Val β :=
  fun _ u r => u = Val.unit ∧ r.1 = PMap.empty

def scalarBrand (l : Loc) (β : Life) : FamilyBrand := ⟨l,β,unitFamily β⟩

theorem unit_brandAt (δ : LSub) (Θ : LocTy) (l : Loc) (β : Life)
    (hk : Θ l β = some (unitFamily β)) : BrandAt (ℍ := ℍ) .unit δ Θ (scalarBrand l β) := by
  refine ⟨hk,rfl,?_⟩
  rintro Θ' j u r ⟨_,rfl⟩
  exact ResU.inStratum_empty β

/-- W1's scalar fixed-predicate cell has the ACTUAL current-main Mut type at every index,
provided the world's key is coherent. This is the physical-cell/value bridge, not an
execution/owned-ghost erasure theorem. -/
theorem W1_scalar_return_main (a : Lifetime.Life) (δ : LSub) (Θ : LocTy)
    (l : Loc) (α β : Life) (ha : a.interp δ = some α) (hab : α ≤ β)
    (hk : Θ l β = some (unitFamily β)) (n : Nat) (u : Val)
    (hχ : ResU.InStratum β (PMap.empty : WRes))
    (hu : unitFamily β 0 u ⟨PMap.empty,hχ⟩) :
    vN (ℍ := ℍ) (.mut a .unit) δ Θ n (Val.loc l)
      (ResU.single l (CellU.mutOf β u PMap.empty hχ (unitFamily β 0) hu)) :=
  returned_to_vN ha hab (unit_brandAt δ Θ l β hk) ⟨u,hχ,n,hu,le_rfl,rfl,rfl⟩

/-- Actual cN's ordinary Mut arrow requires ALL compatible brands at the world, not
only the brand retained by one particular κ. Therefore identity is a relational return
contract change, not merely WRes→XRes in the existing unbranded arrow clause. -/
theorem ordinary_arrow_all_brands {A : VTy} {a : Lifetime.Life} {C : CTy}
    {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (hc : cN (ℍ := ℍ) (.arr (.mut a A) C) δ Θ c n ls e ρ)
    {b : FamilyBrand} {α : Life} {k : Nat} (hkn : k ≤ n)
    (ha : a.interp δ = some α) (hab : α ≤ b.life)
    (hb : BrandAt (ℍ := ℍ) A δ Θ b) {w : Val} {ρv ρ' : WRes}
    (hr : ReturnedCell b k w ρv) (hcomp : ResU.CompS ρ ρv ρ')
    (c' : Loc → Option Life) (hview : ConsistentX c' ρ') :
    cN (ℍ := ℍ) C δ Θ c' k ls (.app e (.val w)) ρ' :=
  hc c' k hkn w ρv ρ' hcomp (returned_to_vN ha hab hb hr) hview

/-- Positive no-loan regression: current recursive U and Ref(U) are inhabited and need
no branded protocol. This does not assert X→current-main conservativity with residual ghosts. -/
def unitThunk : Val := Val.lam (.val Val.unit)

theorem plain_U_unit (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.thunk (.ret .unit)) δ Θ n unitThunk PMap.empty := by
  intro Θ' _ hOK c _ ls
  have hΦ := LocTy.view_down hOK.1 c
  refine (cN_ret_iff _ _ _ _ _ _ _ _).mpr ?_
  show erwp (ℍ := ℍ) (Θ'.view c) _ _ n ls (.app unitThunk.1 (.val Val.unit)) PMap.empty
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down)
    (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ (.val Val.unit) Val.unit) rfl .hole) ?_
  simpa [unitThunk,Expr.subst,Kont.plug] using
    (erwp_val (Φ := Θ'.view c) (Tb := opTableN OpTabN.empty)
      (Q := fun k _ v ρ => vN (ℍ := ℍ) .unit δ Θ' k v ρ)
      (n := n) (ls := ls) (v := Val.unit) (ρ := PMap.empty) ⟨rfl,rfl⟩)

theorem plain_stored_U_unit (δ : LSub) (Θ : LocTy) (n : Nat) (s : Loc) :
    vN (ℍ := ℍ) (.ref (.thunk (.ret .unit))) δ Θ n (Val.loc s)
      (ResU.single s (CellU.ownOf unitThunk)) :=
  ⟨s,unitThunk,PMap.empty,rfl,ResU.comp_empty_right _,plain_U_unit δ Θ n⟩

/-- A separate execution-boundary obstruction: even a perfectly typed matched return
cannot be closed by keeping current UpdVN unchanged on that location. This is a statement
about the exact endpoint resources, not a typed-source unsoundness claim. -/
theorem current_update_cannot_close (Φ : LocFam) (n : Nat) (l : Loc) (β : Life)
    (u w : Val) (χ : WRes) (hχ : χ.InStratum β) (P : Val → SPropS Loc Val β)
    (hu : P u ⟨χ,hχ⟩) :
    ¬ UpdVN Φ n (ResU.single l (CellU.mutOf β u χ hχ P hu))
      (ResU.single l (CellU.ownOf w)) := by
  intro hU
  obtain ⟨σ,hσ⟩ := hU.2.1
  obtain ⟨ψ,hψ,hkind,_,_⟩ := hσ.get (ResU.single_get_self l (CellU.mutOf β u χ hχ P hu))
  have hmut : ψ.kind = Kind.mut := by simpa only [CellU.kind_mutOf] using hkind
  obtain ⟨ψ',hψ',hstep⟩ := hU.1.2.1 l ψ ⟨σ,hσ,hψ⟩ hmut
  obtain ⟨τ,hτ,hget⟩ := hψ'
  rw [ResU.Flat.functional hτ (ResU.flat_single_own l w),ResU.single_get_self] at hget
  cases Option.some.inj hget
  cases hstep.2.1

#print axioms current_update_cannot_close
#print axioms W1_scalar_return_main
#print axioms ordinary_arrow_all_brands
#print axioms plain_U_unit
#print axioms plain_stored_U_unit
#print axioms returned_to_vN
#print axioms vN_to_returned
#print axioms shallow_mut_iff_brand
#print axioms brandAt_extR
#print axioms returned_future_typed
#print axioms unit_member_constant
#print axioms stored_U_all_worlds
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedBridge
