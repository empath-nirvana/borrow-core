import Targets.Base.Typing
import Targets.Base.Machine

/-!
# Base — observations and contextual approximation over Core (DESIGN §2, D12)

For the binary statements over Core (`Targets/Instance/Binary.lean`), all outside the first
pass.  `t₁ ≼ t₂` at `U C`: every well-typed closing context at a data answer
observes no more of `t₁` than of `t₂`, under the platform `P`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The values a closed program at a data answer can finish at, under the platform `P`. -/
def Obs (P : Platform) (A : VTy) (e : Expr) : Set Val :=
  {v | ∃ c, PSteps (ℍ := ℍ) P (init P e) c ∧ Final P A c ∧ c.e = .val v}

/-- The thunk `λ_. e` of a computation at an `F` type. -/
def thunkF (e : Expr) : Val := ⟨.lam (e.shift 1 0), .lam⟩

/-- `t₁ ≼ t₂` at `U C`: every well-typed closing context at a data answer observes no more of `t₁`
than of `t₂`.  `t₁`, `t₂` are closed thunks of `C`. -/
def CtxApprox (J : TypingJ) (P : Platform) (C : CTy) (t₁ t₂ : Val) : Prop :=
  ∀ (f : Expr) (S : Row) (A : VTy), A.Data → RowLe S P.ops →
    J.at LifeCtx.empty [⟨.thunk C, true⟩] f (.comp (CTy.effOf S A)) →
    Obs (ℍ := ℍ) P A (f.subst 0 t₁) ⊆ Obs (ℍ := ℍ) P A (f.subst 0 t₂)

/-- Contextual equivalence at `U C`. -/
def CtxEquiv (J : TypingJ) (P : Platform) (C : CTy) (t₁ t₂ : Val) : Prop :=
  CtxApprox (ℍ := ℍ) J P C t₁ t₂ ∧ CtxApprox (ℍ := ℍ) J P C t₂ t₁

end Targets

end
