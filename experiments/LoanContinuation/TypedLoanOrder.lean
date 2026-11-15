import Core.Chain.Goal791N
import Core.Chain.LendExit835N

/-! Experimental semantic entry [spec §62].
Adds loan claims (location, actual cell lifetime), requiring the exact family at that key and
its world-above slice to survive futures of a stored continuation. Retains ordinary ExtR at
its physical resource. Empty claims recover the current U clause. This order experiment does
NOT redefine cN, claim an X/K execution bridge, or prove a fundamental/adequacy theorem.
-/
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedLoanOrderProbe
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeVar)

abbrev Claims := List (Loc × Life)

def Protect (D : Claims) (Θ Θ' : LocTy) : Prop :=
  ∀ l β, (l, β) ∈ D → Θ' l β = Θ l β ∧ Θ'.above β = Θ.above β

def Future (D : Claims) (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  Θ.ExtR Θ' ρ ∧ Protect D Θ Θ'

theorem protect_refl (D : Claims) (Θ : LocTy) : Protect D Θ Θ :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem protect_trans {D : Claims} {Θ Θ' Θ'' : LocTy}
    (h : Protect D Θ Θ') (h' : Protect D Θ' Θ'') : Protect D Θ Θ'' :=
  fun l β hm => ⟨(h' l β hm).1.trans (h l β hm).1,
    (h' l β hm).2.trans (h l β hm).2⟩

theorem future_refl (D : Claims) (Θ : LocTy) (ρ : WRes) : Future D Θ Θ ρ :=
  ⟨LocTy.extR_refl _ _, protect_refl _ _⟩

theorem future_trans {D : Claims} {Θ Θ' Θ'' : LocTy} {ρ : WRes}
    (h : Future D Θ Θ' ρ) (h' : Future D Θ' Θ'' ρ) : Future D Θ Θ'' ρ :=
  ⟨h.1.trans h'.1, protect_trans h.2 h'.2⟩

theorem future_nil (Θ Θ' : LocTy) (ρ : WRes) :
    Future [] Θ Θ' ρ ↔ Θ.ExtR Θ' ρ :=
  ⟨And.left, fun h => ⟨h, fun _ _ hm => (List.not_mem_nil hm).elim⟩⟩

/-- The changed U future clause, factored over an arbitrary computation interpretation.
For active claims the final execution relation must be X-based, not unchanged cN. -/
def UClaims (R : LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop)
    (D : Claims) (Θ : LocTy) (n : Nat) (e : Expr) (ρ : WRes) : Prop :=
  ∀ Θ', Future D Θ Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls, R Θ' c n ls e ρ

theorem UClaims_transport {R : LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop}
    {D : Claims} {Θ Θ' : LocTy} {n : Nat} {e : Expr} {ρ : WRes}
    (hf : Future D Θ Θ' ρ) (hu : UClaims R D Θ n e ρ) : UClaims R D Θ' n e ρ :=
  fun Θ'' hfuture hOK c hc ls => hu Θ'' (future_trans hf hfuture) hOK c hc ls

theorem no_loan_U (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) :
    UClaims (cN (ℍ := ℍ) C δ) [] Θ n (forceE C v.1) ρ ↔
      vN (ℍ := ℍ) (.thunk C) δ Θ n v ρ := by
  constructor
  · intro h Θ' he hOK c hc ls
    exact h Θ' ((future_nil _ _ _).mpr he) hOK c hc ls
  · intro h Θ' he hOK c hc ls
    exact h Θ' he.1 hOK c hc ls

/-- Preserves the actual stored family for arbitrary P, including higher-order payloads. -/
theorem mutL_transport {D : Claims} {Θ Θ' : LocTy} {l : Loc} {β : Life}
    (hmem : (l, β) ∈ D) (hprotect : Protect D Θ Θ') (P : CPredL)
    {n : Nat} {ρ : WRes} (hm : mutL β P Θ n (Val.loc l) ρ) :
    mutL β P Θ' n (Val.loc l) ρ := by
  obtain ⟨m, w, χ, hχ, j, hw, hnj, hv, hl, hρ⟩ := hm
  have hlm : l = m := by
    have he := congrArg Subtype.val hv
    simpa [Val.loc] using he
  subst m
  obtain ⟨hkey, habove⟩ := hprotect l β hmem
  have hfam : famL β P Θ' = famL β P Θ := by
    funext k v r
    simp only [famL, habove]
  unfold mutL
  rw [hfam]
  exact ⟨l, w, χ, hχ, j, hw, hnj, rfl, hkey.trans hl, hρ⟩

/-- Actual vN Mut payload transport at its exact loan lifetime, for arbitrary payload type A. -/
theorem typed_payload_transport {D : Claims} {Θ Θ' : LocTy} {l : Loc} {β : Life}
    (hmem : (l, β) ∈ D) (hprotect : Protect D Θ Θ') (A : VTy) (δ : LSub) (x : LifeVar)
    {n : Nat} {ρ : WRes}
    (hm : mutL β (fun Θ j v r => vN (ℍ := ℍ) A (δ.extend x β) Θ j v r)
      Θ n (Val.loc l) ρ)
    (hunif : ∀ Θ j v r, vN (ℍ := ℍ) A (δ.extend x β) Θ j v r → r.InStratum β) :
    vN (ℍ := ℍ) (.mut (.var x) A) (δ.extend x β) Θ' n (Val.loc l) ρ :=
  ⟨β, interp_ext_self _ _ _, β, le_rfl, mutL_transport hmem hprotect _ hm, hunif⟩

/-- An unrelated fresh lend is genuinely permitted, for any old world, payload family and share. -/
theorem unrelated_lend {Θ : LocTy} {α β : Life} {l m : Loc}
    (hf : Θ.Fresh α) (hlt : α < β) (hne : m ≠ l)
    (G : Nat → Val → SPropS Loc Val α) (ρ : WRes) :
    Future [(l, β)] Θ (Θ.add m α G) ρ := by
  refine ⟨(LocTy.extA_add hf _ G).extR ρ, ?_⟩
  intro q b hm
  have he : (q,b) = (l,β) := List.mem_singleton.mp hm
  cases he
  exact ⟨LocTy.add_other Θ hne.symm G β,
    LocTy.above_add Θ m (not_lt_of_gt hlt) G⟩

/-- Capture-cell ownership gives ordinary ExtR no information about the outstanding loan. -/
theorem own_no_cellIn (r : Loc) (a : Life) :
    ¬ CellIn (ResU.single r (CellU.ownOf Val.unit)) a := by
  rintro ⟨m, ψ, hg, hk, _⟩
  by_cases hmr : m = r
  · subst m
    rw [ResU.single_get_self] at hg
    cases Option.some.inj hg
    exact hk rfl
  · rw [ResU.single_get_ne _ hmr] at hg
    cases hg

theorem own_extR_any (Θ Θ' : LocTy) (r : Loc) :
    Θ.ExtR Θ' (ResU.single r (CellU.ownOf Val.unit)) :=
  ⟨fun _ a _ _ hc => (own_no_cellIn r a hc).elim,
    fun x _ hc => (own_no_cellIn r x.2 hc).elim⟩

def unitFamily (β : Life) : Nat → Val → SPropS Loc Val β := fun _ v r =>
  v = Val.unit ∧ r.1 = PMap.empty

def loanWorld (l : Loc) (β : Life) : LocTy := LocTy.empty.add l β (unitFamily β)

theorem dropping_loan_allowed_by_current_U (l r : Loc) (β : Life) :
    (loanWorld l β).ExtR LocTy.empty (ResU.single r (CellU.ownOf Val.unit)) ∧
    LocTy.empty.OK ∧
    ¬ Future [(l, β)] (loanWorld l β) LocTy.empty
      (ResU.single r (CellU.ownOf Val.unit)) := by
  refine ⟨own_extR_any _ _ _, LocTy.empty_ok, fun h => ?_⟩
  have he := (h.2 l β (List.mem_singleton_self _)).1
  simp [loanWorld, LocTy.add_self] at he

theorem own_consistent (r : Loc) (c : Loc → Option Life) :
    ConsistentX c (ResU.single r (CellU.ownOf Val.unit)) := by
  intro e he m ψ hg hk
  obtain rfl : e = ResU.single r (CellU.ownOf Val.unit) :=
    ExS.functional he (ExW.single_own r Val.unit)
  by_cases hmr : m = r
  · subst m
    rw [ResU.single_get_self] at hg
    cases Option.some.inj hg
    cases hk
  · rw [ResU.single_get_ne _ hmr] at hg
    cases hg

/-- Actual κ value, with the existing capture-cell implementation. -/
def captured (r : Loc) (H : Val) (K : BoLo.Kont) : Val :=
  ⟨BoLo.kappaC false r H K, isVal_kappaC false r H K⟩

/-- The current stored-U clause, at an actual captured κ, demands the world that has
forgotten the outstanding key. This is a demand, not an assumption that κ meets it. -/
theorem current_U_captured_demands_drop (C : CTy) (δ : LSub) (l r : Loc) (β : Life)
    (H : Val) (K : BoLo.Kont) (n : Nat)
    (hu : vN (ℍ := ℍ) (.thunk C) δ (loanWorld l β) n (captured r H K)
      (ResU.single r (CellU.ownOf Val.unit)))
    (c : Loc → Option Life) (ls : List SRec) :
    cN (ℍ := ℍ) C δ LocTy.empty c n ls (forceE C (captured r H K).1)
      (ResU.single r (CellU.ownOf Val.unit)) :=
  hu LocTy.empty (own_extR_any _ _ _) LocTy.empty_ok c (own_consistent r c) ls

theorem unitFamily_down (β : Life) : DownFam β (unitFamily β) :=
  fun _ _ _ h => h

theorem loanWorld_ok (l : Loc) : (loanWorld l 1).OK := by
  refine ⟨LocTy.down_add LocTy.empty_down l (unitFamily_down 1), 3, ?_⟩
  exact LocTy.fresh_add (N := 3) (N' := 3)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) l (unitFamily 1)

theorem concrete_allowed_change (r : Loc) :
    let Θ := loanWorld 0 1
    let Θ' := Θ.add 1 2 (unitFamily 2)
    Θ.OK ∧ Θ'.OK ∧ Θ' ≠ Θ ∧
      Future [(0, 1)] Θ Θ' (ResU.single r (CellU.ownOf Val.unit)) := by
  intro Θ Θ'
  have hf : Θ.Fresh 2 := LocTy.fresh_add (N := 2) (N' := 2)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)
  have hf3 : Θ.Fresh 3 := LocTy.fresh_add (N := 3) (N' := 3)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)
  refine ⟨loanWorld_ok 0, ⟨LocTy.down_add (loanWorld_ok 0).1 1 (unitFamily_down 2),
    3, LocTy.fresh_add hf3 le_rfl (by decide) 1 (unitFamily 2)⟩, ?_,
    unrelated_lend hf (by decide) (by decide) _ _⟩
  intro he
  have hget := congrArg (fun W : LocTy => W 1 2) he
  simp [Θ', Θ, loanWorld, LocTy.add] at hget

/-- A fully inhabited mutable answer in the old world. -/
def typedBorrow (l : Loc) (β : Life) (n : Nat) : WRes :=
  ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β)
    (unitFamily β n) ⟨rfl, rfl⟩)

theorem typedBorrow_at_source (l : Loc) (β : Life) (n : Nat) :
    vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 β)
      (loanWorld l β) n (Val.loc l) (typedBorrow l β n) := by
  refine ⟨β, interp_ext_self _ _ _, β, le_rfl, ?_, ?_⟩
  · exact lend_mutL LocTy.empty l β
      (fun Θ j v r => vN (ℍ := ℍ) .unit (LSub.empty.extend 0 β) Θ j v r)
      le_rfl (ResU.inStratum_empty β) ⟨rfl, rfl⟩
  · rintro Θ j v r ⟨_, rfl⟩
    exact ResU.inStratum_empty β

theorem typedBorrow_not_at_dropped_world (l : Loc) (β : Life) (n : Nat) :
    ¬ vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 β)
      LocTy.empty n (Val.loc l) (typedBorrow l β n) := by
  rintro ⟨_, _, b, _, hm, _⟩
  obtain ⟨m, w, χ, hχ, j, hw, hnj, hv, hl, hρ⟩ := hm
  simp at hl

theorem typedBorrow_survives_allowed_change (r : Loc) (n : Nat) :
    vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 1)
      ((loanWorld 0 1).add 1 2 (unitFamily 2)) n (Val.loc 0) (typedBorrow 0 1 n) := by
  have hp := (concrete_allowed_change r).2.2.2.2
  refine typed_payload_transport (List.mem_singleton_self (0, (1 : Life))) hp .unit
    LSub.empty 0 ?_ ?_
  · exact lend_mutL LocTy.empty 0 1
      (fun Θ j v r => vN (ℍ := ℍ) .unit (LSub.empty.extend 0 1) Θ j v r)
      le_rfl (ResU.inStratum_empty 1) ⟨rfl, rfl⟩
  · rintro Θ j v r ⟨_, rfl⟩
    exact ResU.inStratum_empty 1

/-- Protection of one loan does not make ordinary Mut answers identify that loan.
A new key at the SAME lifetime admits a different-location answer, compatible with κ's cell. -/
theorem same_lifetime_wrong_answer (n : Nat) :
    let Θ := loanWorld 0 1
    let Θ' := Θ.add 1 1 (unitFamily 1)
    Future [(0, 1)] Θ Θ' (ResU.single 2 (CellU.ownOf Val.unit)) ∧
    Θ.OK ∧ Θ'.OK ∧
    vN (ℍ := ℍ) (.mut (.var 0) .unit) (LSub.empty.extend 0 1)
      Θ' n (Val.loc 1) (typedBorrow 1 1 n) ∧
    (typedBorrow 1 1 n).get 0 = none ∧
    ∃ ρ, ResU.CompS (ResU.single 2 (CellU.ownOf Val.unit)) (typedBorrow 1 1 n) ρ := by
  intro Θ Θ'
  have hf3 : Θ.Fresh 3 := LocTy.fresh_add (N := 3) (N' := 3)
    (fun _ _ h => absurd rfl h) le_rfl (by decide) 0 (unitFamily 1)
  refine ⟨⟨own_extR_any _ _ _, ?_⟩, loanWorld_ok 0,
    ⟨LocTy.down_add (loanWorld_ok 0).1 1 (unitFamily_down 1),
      3, LocTy.fresh_add hf3 le_rfl (by decide) 1 (unitFamily 1)⟩, ?_, ?_, ?_⟩
  · intro l β hm
    have he : (l,β) = (0, (1 : Life)) := List.mem_singleton.mp hm
    cases he
    exact ⟨LocTy.add_other Θ (by decide) (unitFamily 1) 1,
      LocTy.above_add Θ 1 (lt_irrefl 1) (unitFamily 1)⟩
  · refine ⟨1, interp_ext_self _ _ _, 1, le_rfl, ?_, ?_⟩
    · exact lend_mutL Θ 1 1
        (fun Θ j v r => vN (ℍ := ℍ) .unit (LSub.empty.extend 0 1) Θ j v r)
        le_rfl (ResU.inStratum_empty 1) ⟨rfl, rfl⟩
    · rintro Θ j v r ⟨_, rfl⟩
      exact ResU.inStratum_empty 1
  · exact ResU.single_get_ne _ (by decide)
  · obtain ⟨ρ, hρ⟩ := (ResU.compS_defined_iff (typedBorrow 1 1 n)
        (ResU.single 2 (CellU.ownOf Val.unit))).mpr
      (compatS_single_of_get_none (ResU.single_get_ne _ (by decide)))
    exact ⟨ρ, ResU.CompS.comm hρ⟩

#print axioms same_lifetime_wrong_answer
#print axioms typedBorrow_survives_allowed_change
#print axioms current_U_captured_demands_drop
#print axioms concrete_allowed_change
#print axioms typedBorrow_at_source
#print axioms typedBorrow_not_at_dropped_world
#print axioms no_loan_U
#print axioms UClaims_transport
#print axioms mutL_transport
#print axioms typed_payload_transport
#print axioms unrelated_lend
#print axioms dropping_loan_allowed_by_current_U
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedLoanOrderProbe
