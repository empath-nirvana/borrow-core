import FnMut.Core.Dtor

/-!
# FnMut — the affine closure as codata

`FnMut^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`: an object with two observations, `call`, which
takes an `A`, answers a `B` and hands back the rest, and `close`, which ends it.  A closure
value is `U(FnMut^c A B)`; one that outlives `@c` is `[@c] U(FnMut^c A B)` (`FnBox`), and the
rest every call hands back is again of that type.  `@c` is the bound Rust writes as
`dyn FnMut(A) -> B + 'c`.

The type is an abbreviation over `νX. C` in the fork `FnMut.Core`, whose positivity admits an
observation with a closed argument (`A ⊸ D`) and a boxed rest (`[@c] U X`).  The relation
clause is the unrolling (`cC_fnMut_iff`); the paper's `Unk` clause and the observable view
are untouched (`immReborrow_fnBox`, `vC_obs_fnMut`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The type -/

/-- The body of `FnMut^c A B`: `(A ⊸ F(B ⊗ [@c] U X)) & F 1`, `U X` the variable `0`. -/
abbrev fnBody (c : Lifetime.Life) (A B : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (.ret .unit)

/-- `FnMut^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`. -/
abbrev fnMutC (c : Lifetime.Life) (A B : VTy) : CTy := .nu (fnBody c A B)

/-- `U(FnMut^c A B)`: an affine closure. -/
abbrev fnMutT (c : Lifetime.Life) (A B : VTy) : VTy := .thunk (fnMutC c A B)

/-- `[@c] U(FnMut^c A B)`: an affine closure that outlives `@c`, the type stored, lent and
handed back by a call. -/
abbrev fnBox (c : Lifetime.Life) (A B : VTy) : VTy := .box c (fnMutT c A B)

/-- The body at the state `S`: `(A ⊸ F(B ⊗ [@c] S)) & F 1`. -/
abbrev fnStepC (c : Lifetime.Life) (A B S : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor B (.box c S)))) (.ret .unit)

/-- The unrolling, `(A ⊸ F(B ⊗ [@c] U(FnMut^c A B))) & F 1`. -/
abbrev fnUnroll (c : Lifetime.Life) (A B : VTy) : CTy := fnStepC c A B (fnMutT c A B)

/-- **Positivity**: at a closed argument type, `FnMut`'s body is an observation tree. -/
theorem fnBody_nuOk {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    (fnBody c A B).NuOk :=
  ⟨⟨hA, VTy.poly_of_not_occ (VTy.not_occ_rename_succ B), trivial⟩, fun h => h⟩

theorem fnBody_instT (c : Lifetime.Life) (A B S : VTy) :
    (fnBody c A B).instT S = fnStepC c A B S := by
  simp only [CTy.instT, VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, VTy.inst_rename_succ]

theorem fnBody_unroll (c : Lifetime.Life) (A B : VTy) :
    (fnBody c A B).unroll = fnUnroll c A B :=
  fnBody_instT c A B _

/-! ### The relation clause -/

/-- **The relation at the affine arrow.**  `𝒞⟦FnMut^c A B⟧` is its unrolling: a computation
is an affine closure when, at every argument, `call` answers a `B` and a rest that is again an
affine closure outliving `@c` (`[@c]`, the resource condition `@ρ ⊐ c`), and `close` runs to
`()`.  The greatest fixed point of that clause (`NuRel.lean`), read off at the unrolling. -/
theorem cC_fnMut_iff {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) (ls : List SRec)
    (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (fnMutC c A B) ls δ e ρ ↔
      (∀ v, (vC true A ls δ v ─⋆
          wpTS ls (.app (.app e (.val (.inj₁ .unit))) (.val v))
            (fun ls' => vC true (.tensor B (fnBox c A B)) ls' δ)) ρ) ∧
      wpTS ls (.app e (.val (.inj₂ .unit))) (fun ls' => vC true .unit ls' δ) ρ := by
  rw [cC_nu_iff (fnBody_nuOk hA c B), fnBody_unroll]
  rfl

/-- Coinduction at the affine arrow: a candidate closed under the clause is in the relation. -/
theorem fnMut_coind {A : VTy} (hA : A.Cl 0) {c : Lifetime.Life} {B : VTy} {δ : LSub}
    {R : CPred} (hR : R.Le (nuF (fnBody c A B) δ R)) :
    ∀ ls e ρ, R ls e ρ → cC (fnMutC c A B) ls δ e ρ :=
  fun ls e ρ h _ => nuRel_coind (C := fnBody c A B) hR ls e ρ h

/-! ### The observable view and the paper's `Unk` clause

An affine closure is a `U C`.  The observable view, at which an `Imm` payload is held
(§12.69), relaxes `U` to `True`, and `Imm̲` takes `U C` to `Unk`: a closure behind an `Imm`
borrow can only be forgotten, as the paper's clause (4) says of `⊸`.  A `Mut` payload is held
at the program's view.  So no access path reads an affine closure at the observable view, and
`obs_transfer` is not asked to move one. -/

theorem vC_obs_fnMut (c : Lifetime.Life) (A B : VTy) (ls : List SRec) (δ : LSub) (v : Val) :
    vC false (fnMutT c A B) ls δ v = fun _ => True := rfl

theorem immReborrow_fnMut (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (fnMutT c A B) = .unk := rfl

theorem immReborrow_fnBox (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (fnBox c A B) = .unk := rfl

/-! ### Structure: affine, not unrestricted -/

/-- An affine closure has a destructor, `close` (SPEC §12, class 2). -/
theorem hasDtor_fnMut {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (fnMutT c A B) :=
  .nu (C := .arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (R := .unit)
    (fnBody_nuOk hA c B) trivial .unit

theorem hasDtor_fnBox {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (fnBox c A B) :=
  .box (hasDtor_fnMut hA c B)

/-- An affine closure is not persistent: no split duplicates it and no promotion takes it. -/
theorem not_persistent_fnMut (c : Lifetime.Life) (A B : VTy) :
    ¬ (fnMutT c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

theorem not_persistent_fnBox (c : Lifetime.Life) (A B : VTy) :
    ¬ (fnBox c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

end BoCa.Fig16.LogRel.Core

end
