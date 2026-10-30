import Core.Dtor
import Core.RelationFacts

/-!
# The closure `Clo` as codata  `[spec §22]`

`Clo^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`: an object with two observations, `call`, which
takes an `A`, answers a `B` and hands back the rest, and `close`, which ends it.  A closure
value is `U(Clo^c A B)`; one that outlives `@c` is `[@c] U(Clo^c A B)` (`cloBox`), and the
rest every call hands back is again of that type.  `@c` is the bound (cf. Rust's
`dyn FnMut(A) -> B + 'c`).

The type is an abbreviation over `νX. C`, an instance of §7's positivity with an observation
taking a closed argument (`A ⊸ D`) and a boxed rest (`[@c] U X`).  The relation clause is the
unrolling (`cC_clo_iff`); the paper's `Unk` clause and the observable view are untouched
(`immReborrow_cloBox`, `vC_obs_clo`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The type -/

/-- The body of `Clo^c A B`: `(A ⊸ F(B ⊗ [@c] U X)) & F 1`, `U X` the variable `0`. -/
abbrev cloBody (c : Lifetime.Life) (A B : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (.ret .unit)

/-- `Clo^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`. -/
abbrev cloC (c : Lifetime.Life) (A B : VTy) : CTy := .nu (cloBody c A B)

/-- `U(Clo^c A B)`: a closure. -/
abbrev cloT (c : Lifetime.Life) (A B : VTy) : VTy := .thunk (cloC c A B)

/-- `[@c] U(Clo^c A B)`: a closure that outlives `@c`, the type stored, lent and
handed back by a call. -/
abbrev cloBox (c : Lifetime.Life) (A B : VTy) : VTy := .box c (cloT c A B)

/-- The body at the state `S`: `(A ⊸ F(B ⊗ [@c] S)) & F 1`. -/
abbrev cloStepC (c : Lifetime.Life) (A B S : VTy) : CTy :=
  .amp (.arr A (.ret (.tensor B (.box c S)))) (.ret .unit)

/-- The unrolling, `(A ⊸ F(B ⊗ [@c] U(Clo^c A B))) & F 1`. -/
abbrev cloUnroll (c : Lifetime.Life) (A B : VTy) : CTy := cloStepC c A B (cloT c A B)

/-- **Positivity**: at a closed argument type, the closure's body is an observation tree. -/
theorem cloBody_nuOk {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    (cloBody c A B).NuOk :=
  ⟨⟨hA, VTy.poly_of_not_occ (VTy.not_occ_rename_succ B), trivial⟩, fun h => h⟩

theorem cloBody_instT (c : Lifetime.Life) (A B S : VTy) :
    (cloBody c A B).instT S = cloStepC c A B S := by
  simp only [CTy.instT, VTy.inst, VTy.subst, VTy.scons]
  rw [← VTy.inst, VTy.inst_rename_succ]

theorem cloBody_unroll (c : Lifetime.Life) (A B : VTy) :
    (cloBody c A B).unroll = cloUnroll c A B :=
  cloBody_instT c A B _

/-! ### The relation clause -/

/-- **The relation at the closure's type.**  `𝒞⟦Clo^c A B⟧` is its unrolling: a computation
is a closure when, at every argument, `call` answers a `B` and a rest that is again a
closure outliving `@c` (`[@c]`, the resource condition `@ρ ⊐ c`), and `close` runs to
`()`.  The greatest fixed point of that clause (`NuRel.lean`), read off at the unrolling. -/
theorem cC_clo_iff {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) (ls : List SRec)
    (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (cloC c A B) ls δ e ρ ↔
      (∀ v, (vC true A ls δ v ─⋆
          wpTS ls (.app (.app e (.val (.inj₁ .unit))) (.val v))
            (fun ls' => vC true (.tensor B (cloBox c A B)) ls' δ)) ρ) ∧
      wpTS ls (.app e (.val (.inj₂ .unit))) (fun ls' => vC true .unit ls' δ) ρ := by
  rw [cC_nu_iff (cloBody_nuOk hA c B), cloBody_unroll]
  rfl

/-- Coinduction at the closure's type: a candidate closed under the clause is in the relation. -/
theorem clo_coind {A : VTy} (hA : A.Cl 0) {c : Lifetime.Life} {B : VTy} {δ : LSub}
    {R : CPred} (hR : R.Le (nuF (cloBody c A B) δ R)) :
    ∀ ls e ρ, R ls e ρ → cC (cloC c A B) ls δ e ρ :=
  fun ls e ρ h _ => nuRel_coind (C := cloBody c A B) hR ls e ρ h

/-! ### The observable view and the paper's `Unk` clause

A closure is a `U C`.  The observable view, at which an `Imm` payload is held
(§12.69), relaxes `U` to `True`, and `Imm̲` takes `U C` to `Unk`: a closure behind an `Imm`
borrow can only be forgotten, as the paper's clause (4) says of `⊸`.  A `Mut` payload is held
at the program's view.  So no access path reads a closure at the observable view, and
`obs_transfer` is not asked to move one. -/

theorem vC_obs_clo (c : Lifetime.Life) (A B : VTy) (ls : List SRec) (δ : LSub) (v : Val) :
    vC false (cloT c A B) ls δ v = fun _ => True := rfl

theorem immReborrow_clo (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (cloT c A B) = .unk := rfl

theorem immReborrow_cloBox (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (cloBox c A B) = .unk := rfl

/-! ### Structure: linear, with a derived drop -/

/-- A closure has a destructor, `close` (SPEC §12, group 2). -/
theorem hasDtor_clo {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (cloT c A B) :=
  .nu (C := .arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (R := .unit)
    (cloBody_nuOk hA c B) trivial .unit

theorem hasDtor_cloBox {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (cloBox c A B) :=
  .box (hasDtor_clo hA c B)

/-- A closure is not persistent: no split duplicates it and no promotion takes it. -/
theorem not_persistent_clo (c : Lifetime.Life) (A B : VTy) :
    ¬ (cloT c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

theorem not_persistent_cloBox (c : Lifetime.Life) (A B : VTy) :
    ¬ (cloBox c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

/-- A closure is not forgettable (`Forgettable`, SPEC §12 group 1): dropping one runs its `close`,
so its derived drop is its destructor (group 2), not `forget`. -/
theorem not_forgettable_clo (c : Lifetime.Life) (A B : VTy) : ¬ Forgettable (cloT c A B) := by
  intro h; cases h

/-- `U(A ⊸ F B)` is linear with no derived drop (SPEC §12 group 3): it is disposed of only
by calling it, which needs an `A`.  So it cannot be the state of a closure whose `close`
must dispose of it, and there is no uniform coercion from `A ⇒ B` to `Clo`. -/
theorem not_hasDtor_lolli (A B : VTy) : ¬ HasDtor (.lolli A B) := by
  intro h; cases h

/-- `obs_transfer` at a closure: its arm at `U C`, where the observable view holds
`True`, is the arm the closure takes.  `[spec §12.69]` -/
theorem obs_transfer_cloBox {R : WRes} {ls : List SRec} (hLB : WitLB ls R) (c : Lifetime.Life)
    (A B : VTy) {δ : LSub} {v : Val} {P Q : WRes} (hP : CellMatch R P) (hQ : CellMatch R Q)
    (h : vC false (cloBox c A B) ls δ v P) (hs : vShape (cloBox c A B) δ v Q) :
    vC false (cloBox c A B) ls δ v Q :=
  obs_transfer hLB (cloBox c A B) hP hQ h hs

/-! ### Higher-order and effectful closures -/

/-- A closure whose argument is a borrowed closure is positive: the argument
type is closed. -/
theorem cloBody_nuOk_higher (a c c' : Lifetime.Life) (A' B' B : VTy) :
    (cloBody c (.mut a (cloBox c' A' B')) B).NuOk :=
  cloBody_nuOk (A := .mut a (cloBox c' A' B')) trivial c B

/-- The body of a closure whose call performs the operations of the row `Σ`:
`(A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`.  `[spec §19]` -/
abbrev cloEffBody (S : List OpSig) (c : Lifetime.Life) (A B : VTy) : CTy :=
  .amp (.arr A (CTy.effOf S (.tensor (B.rename Nat.succ) (.box c (.tvar 0)))))
    (CTy.effOf S .unit)

/-- An effectful closure is positive at closed operation types, so `nuIn`, `nuOut` and
`unfold` cover it with no further change. -/
theorem cloEffBody_nuOk {S : List OpSig} (hS : ∀ o ∈ S, o.A.Cl 0 ∧ o.B.Cl 0) {A : VTy}
    (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) : (cloEffBody S c A B).NuOk :=
  ⟨⟨hA, CTy.nuLeaf_effOf hS ⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ B), trivial⟩⟩,
   CTy.nuLeaf_effOf hS (fun h => h)⟩

end BoCa.Fig16.LogRel.Core

end
