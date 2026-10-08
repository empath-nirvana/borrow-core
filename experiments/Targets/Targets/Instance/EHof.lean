import Targets.Instance.ETyping
import Targets.Instance.Theories

/-!
# The Instance — E1's higher-order function at `J₁`: one typing serves every row

`hof = λg. g ()`, written by our instance as `λg. (λx. g x) ()`, is typed at `J₁` once, at
`U(∀ρ:any. U(1 ⊸ F_ρ bool) ⊸ F_ρ bool)` (`derV_hof_J₁`): Core types the λ-value at every instance,
each at its own row.  That one typing serves a callback at every row (`polyUse_hof_J₁`, E1's
schema): the callback `λ_. M` is SPEC §26's `[λ-dead]`, and `f`'s closing is read at the
instance of the use's row (`der_callPoly_J₁`).  `hof` calls its callback, catching nothing
(`callsThrough_hof`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont performE raiseE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt RVar RowEnv)

section Hof
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- `hof`, as our instance writes it: `λg. (λx. g x) ()`. -/
def hofE : Expr := .lam (appE (.var 0) .unit)

theorem hof_val : ((𝕁).hof).1 = hofE := rfl

/-- **`hof` at an instance**: `U(1 ⊸ F_S B) ⊸ F_S B`, at every row `S` and answer `B`. -/
theorem d_hof (S : Row) (B : VTy) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] hofE (.comp (.arr (.thunk (.arr .unit (CTy.effOf S B))) (CTy.effOf S B))) :=
  .lam (.bind (.right .nil) (.ret (.unitI (.cons .nil)))
    (.app (.right (.left .nil)) (.force (C := .arr .unit (CTy.effOf S B)) (.there (.here .nil)))
      (.here (.cons .nil))))

/-- `hof`'s polymorphic body: `U(1 ⊸ F_ρ B) ⊸ F_ρ B`. -/
def hofC (B : VTy) : OCTy := .arr (.thunk (.arr .unit (effAt [] (OVTy.ofV B)))) (effAt [] (OVTy.ofV B))

theorem hofC_den (B : VTy) (η : RowEnv) (r : Row) :
    (hofC B).den (Function.update η ρ₀ r) =
      .arr (.thunk (.arr .unit (CTy.effOf r B))) (CTy.effOf r B) := by
  simp [hofC, effAt, OCTy.den, OVTy.den, OVTy.den_ofV]

theorem hofC_rFree (B : VTy) : (hofC B).RFree :=
  ⟨OCTy.rFree_ofC (.arr .unit (.ret B)), OVTy.rFree_ofV B⟩

/-- **E1: `hof` is typed once**, at `U(∀ρ:any. U(1 ⊸ F_ρ B) ⊸ F_ρ B)`. -/
theorem derV_hof_J₁ (B : VTy) : (𝕁).derV [] (𝕁).hof (polyTy (hofC B)) :=
  derV_poly_J₁ (hofC_rFree B) trivial rfl fun r η _ _ => by
    rw [hofC_den]; exact d_hof r B

/-- `bool` at our instance. -/
theorem bool_eq : (𝕁).bool = OVTy.ofV boolT := rfl

theorem boolT_not_loop : ∀ A₀ L, boolT ≠ .sum A₀ (.thunk L) := by
  intro A₀ L h
  simp [boolT] at h

theorem unitT_not_loop : ∀ A₀ L, (VTy.unit) ≠ .sum A₀ (.thunk L) := by
  intro A₀ L h; cases h

/-- **E1's schema at `J₁`**: the one typing of `hof` serves a callback at every row. -/
theorem polyUse_hof_J₁ (hΞ : Ξ.NU) :
    (𝕁).PolyUse [polyTy (hofC boolT)] (fun g => (𝕁).call ((𝕁).var 0) g) (𝕁).bool (𝕁).bool := by
  intro ε M hM
  exact der_callPoly_J₁ hΞ (hofC_rFree boolT) trivial boolT_not_loop
    (fun η => hofC_den boolT η _) hM hM.1

end Hof

end Targets.Inst

end
