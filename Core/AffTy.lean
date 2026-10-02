import Core.Nu

/-!
# The affine closure: the type, its relation clause, and its terms  `[spec §22, §24]`

`Aff^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`: an object with two observations, `call`, which
takes an `A`, answers a `B` and hands back the rest, and `close`, which ends it.  A closure
value is `U(Aff^c A B)`; one that outlives `@c` is `[@c] U(Aff^c A B)` (`affBox`), and the
rest every call hands back is again of that type.  `@c` is the bound (cf. Rust's
`dyn FnMut(A) -> B + 'c`).

The type is an abbreviation over `νX. C`, an instance of §7's positivity with an observation
taking a closed argument (`A ⊸ D`) and a boxed rest (`[@c] U X`).  The relation clause is the
unrolling (`cC_aff_iff`), and coinduction is `aff_coind`.  The introduction term `mkE` builds a
closure from a state and `!` code; its derivations are `AffRules.lean`'s.  This file comes
before `CDerives` (`Fundamental.lean`), whose rule `[gen]` answers at `[@c] U(Aff^c A B)`
(`Gen.lean`, SPEC §24); the closure's structure (destructor, persistence) is `Aff.lean`'s.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The type -/

/-- The body of `Aff^c A B`: `(A ⊸ F(B ⊗ [@c] U X)) & F 1`, `U X` the variable `0`. -/
abbrev affBody (c : Lifetime.Life) (A B : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (.ret .unit)

/-- `Aff^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`. -/
abbrev affC (c : Lifetime.Life) (A B : VTy) : CTy := .nu (affBody c A B)

/-- `U(Aff^c A B)`: an affine closure. -/
abbrev affT (c : Lifetime.Life) (A B : VTy) : VTy := .thunk (affC c A B)

/-- `[@c] U(Aff^c A B)`: an affine closure that outlives `@c`, the type stored, lent and
handed back by a call. -/
abbrev affBox (c : Lifetime.Life) (A B : VTy) : VTy := .box c (affT c A B)

/-- The body at the state `S`: `(A ⊸ F(B ⊗ [@c] S)) & F 1`. -/
abbrev affStepC (c : Lifetime.Life) (A B S : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor B (.box c S)))) (.ret .unit)

/-- The unrolling, `(A ⊸ F(B ⊗ [@c] U(Aff^c A B))) & F 1`. -/
abbrev affUnroll (c : Lifetime.Life) (A B : VTy) : CTy := affStepC c A B (affT c A B)

/-- **Positivity**: at a closed argument type, the affine closure's body is an observation tree. -/
theorem affBody_nuOk {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    (affBody c A B).NuOk :=
  ⟨⟨hA, VTy.poly_of_not_occ (VTy.not_occ_rename_succ B), trivial⟩, fun h => h⟩

theorem affBody_instT (c : Lifetime.Life) (A B S : VTy) :
    (affBody c A B).instT S = affStepC c A B S := by
  simp only [CTy.instT, VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, VTy.inst_rename_succ]

theorem affBody_unroll (c : Lifetime.Life) (A B : VTy) :
    (affBody c A B).unroll = affUnroll c A B :=
  affBody_instT c A B _

/-! ### The relation clause -/

/-- **The relation at the affine arrow.**  `𝒞⟦Aff^c A B⟧` is its unrolling: a computation
is an affine closure when, at every argument, `call` answers a `B` and a rest that is again an
affine closure outliving `@c` (`[@c]`, the resource condition `@ρ ⊐ c`), and `close` runs to
`()`.  The greatest fixed point of that clause (`NuRel.lean`), read off at the unrolling. -/
theorem cC_aff_iff {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) (ls : List SRec)
    (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (affC c A B) ls δ e ρ ↔
      (∀ v, (vC true A ls δ v ─⋆
          wpTS ls (.app (.app e (.val (.inj₁ .unit))) (.val v))
            (fun ls' => vC true (.tensor B (affBox c A B)) ls' δ)) ρ) ∧
      wpTS ls (.app e (.val (.inj₂ .unit))) (fun ls' => vC true .unit ls' δ) ρ := by
  rw [cC_nu_iff (affBody_nuOk hA c B), affBody_unroll]
  rfl

/-- Coinduction at the affine arrow: a candidate closed under the clause is in the relation. -/
theorem aff_coind {A : VTy} (hA : A.Cl 0) {c : Lifetime.Life} {B : VTy} {δ : LSub}
    {R : CPred} (hR : R.Le (nuF (affBody c A B) δ R)) :
    ∀ ls e ρ, R ls e ρ → cC (affC c A B) ls δ e ρ :=
  fun ls e ρ h _ => nuRel_coind (C := affBody c A B) hR ls e ρ h

/-! ### Terms -/

/-- `unfold` at `Aff^c A B`. -/
abbrev affUnfoldV (c : Lifetime.Life) (A B : VTy) : Val := unfoldV (affBody c A B)

/-- `⟨f to g. (g s) π₁, f to g. (g s) π₂⟩`, with `f : !U(S ⊸ Aff^c A B)` at `2` and `s : S`
at `3` inside `withPair`'s binders: the codata `unfold step s` as a value.  `f` stays `!` in
the context, so the value outlives whatever `s` outlives. -/
def packE : Expr :=
  withPair (bindE (.var 2) (.app (.app (.var 0) (.var 4)) (.val (.inj₁ .unit))))
    (bindE (.var 2) (.app (.app (.var 0) (.var 4)) (.val (.inj₂ .unit))))

/-- `s₀ to s. unfold step to f. pack to k. K`: `K` with the closure `unfold step s₀` at
index `0`. -/
def mkE (c : Lifetime.Life) (A B : VTy) (s₀ : Expr) (step : Val) (K : Expr) : Expr :=
  bindE s₀ (bindE (.app (.val (affUnfoldV c A B)) (.val step)) (bindE packE K))

end BoCa.Fig16.LogRel.Core

end
