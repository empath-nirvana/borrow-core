import Core.Dtor
import Core.RelationFacts
import Core.AffTy

/-!
# The affine closure as codata  `[spec §22]`

`Aff^c A B ≜ νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`: an object with two observations, `call`, which
takes an `A`, answers a `B` and hands back the rest, and `close`, which ends it.  A closure
value is `U(Aff^c A B)`; one that outlives `@c` is `[@c] U(Aff^c A B)` (`affBox`), and the
rest every call hands back is again of that type.  `@c` is the bound (cf. Rust's
`dyn FnMut(A) -> B + 'c`).

The type, its relation clause (`cC_aff_iff`) and coinduction (`aff_coind`) are in `AffTy.lean`,
before `CDerives`, so that a rule of the judgment may answer at the type (`[gen]`, `Gen.lean`).
This file has its structure: the paper's `Unk` clause and the observable view are untouched
(`immReborrow_affBox`, `vC_obs_aff`), and it has a destructor and is not persistent.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The observable view and the paper's `Unk` clause

An affine closure is a `U C`.  The observable view, at which an `Imm` payload is held
(§12.69), relaxes `U` to `True`, and `Imm̲` takes `U C` to `Unk`: a closure behind an `Imm`
borrow can only be forgotten, as the paper's clause (4) says of `⊸`.  A `Mut` payload is held
at the program's view.  So no access path reads an affine closure at the observable view, and
`obs_transfer` is not asked to move one. -/

theorem vC_obs_aff (c : Lifetime.Life) (A B : VTy) (ls : List SRec) (δ : LSub) (v : Val) :
    vC false (affT c A B) ls δ v = fun _ => True := rfl

theorem immReborrow_aff (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (affT c A B) = .unk := rfl

theorem immReborrow_affBox (b c : Lifetime.Life) (A B : VTy) :
    VTy.immReborrow b (affBox c A B) = .unk := rfl

/-! ### Structure: affine, not unrestricted -/

/-- An affine closure has a destructor, `close` (SPEC §12, class 2). -/
theorem hasDtor_aff {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (affT c A B) :=
  .nu (C := .arr A (.ret (.tensor (B.rename Nat.succ) (.box c (.tvar 0))))) (R := .unit)
    (affBody_nuOk hA c B) trivial .unit

theorem hasDtor_affBox {A : VTy} (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) :
    HasDtor (affBox c A B) :=
  .box (hasDtor_aff hA c B)

/-- An affine closure is not persistent: no split duplicates it and no promotion takes it. -/
theorem not_persistent_aff (c : Lifetime.Life) (A B : VTy) :
    ¬ (affT c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

theorem not_persistent_affBox (c : Lifetime.Life) (A B : VTy) :
    ¬ (affBox c A B).Persistent := by
  simp [VTy.Persistent, VTy.persistent]

/-- An affine closure is not forgettable (`Affine`, SPEC §12 class 1): dropping one runs its
`close`, so it is affine by its destructor (class 2), not by `forget`. -/
theorem not_affine_aff (c : Lifetime.Life) (A B : VTy) : ¬ Affine (affT c A B) := by
  intro h; cases h

/-- A linear closure `U(A ⊸ F B)` has no destructor (SPEC §12 class 3): it is disposed of only
by calling it, which needs an `A`.  So it cannot be the state of an affine closure whose `close`
must dispose of it, and linear ≤ affine has no uniform coercion. -/
theorem not_hasDtor_lolli (A B : VTy) : ¬ HasDtor (.lolli A B) := by
  intro h; cases h

/-- `obs_transfer` at an affine closure: its arm at `U C`, where the observable view holds
`True`, is the arm the affine closure takes.  `[spec §12.69]` -/
theorem obs_transfer_affBox {R : WRes} {ls : List SRec} (hLB : WitLB ls R) (c : Lifetime.Life)
    (A B : VTy) {δ : LSub} {v : Val} {P Q : WRes} (hP : CellMatch R P) (hQ : CellMatch R Q)
    (h : vC false (affBox c A B) ls δ v P) (hs : vShape (affBox c A B) δ v Q) :
    vC false (affBox c A B) ls δ v Q :=
  obs_transfer hLB (affBox c A B) hP hQ h hs

/-! ### Higher-order and effectful affine closures -/

/-- An affine closure whose argument is a borrowed affine closure is positive: the argument
type is closed. -/
theorem affBody_nuOk_higher (a c c' : Lifetime.Life) (A' B' B : VTy) :
    (affBody c (.mut a (affBox c' A' B')) B).NuOk :=
  affBody_nuOk (A := .mut a (affBox c' A' B')) trivial c B

/-- The body of an affine closure whose call performs the operations of the row `Σ`:
`(A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1`.  `[spec §19]` -/
abbrev affEffBody (S : List OpSig) (c : Lifetime.Life) (A B : VTy) : CTy :=
  .amp (.arr A (CTy.effOf S (.tensor (B.rename Nat.succ) (.box c (.tvar 0)))))
    (CTy.effOf S .unit)

/-- An effectful affine closure is positive at closed operation types, so `nuIn`, `nuOut` and
`unfold` cover it with no further change. -/
theorem affEffBody_nuOk {S : List OpSig} (hS : ∀ o ∈ S, o.A.Cl 0 ∧ o.B.Cl 0) {A : VTy}
    (hA : A.Cl 0) (c : Lifetime.Life) (B : VTy) : (affEffBody S c A B).NuOk :=
  ⟨⟨hA, CTy.nuLeaf_effOf hS ⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ B), trivial⟩⟩,
   CTy.nuLeaf_effOf hS (fun h => h)⟩

end BoCa.Fig16.LogRel.Core

end
