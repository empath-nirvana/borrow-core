import Targets.Instance.Types
import Targets.Instance.Rows

/-!
# The Instance — typing systems over the open types (RESTRUCTURE §4.2)

* **`OurTyping RF`**: a judgement `Θ; Δ; Γ ⊢ e : j` over the open types, with the outlives
  judgements its rules consult, how its row variables are the row form `RF`'s variables (`env`;
  at `orowRF`, whose variables are row variables, the identity), and its judgement at an effect
  context `Ξ` (`derAt`): the derivations whose inner rows are tied to `Ξ` (decision R), which our
  instance at `Ξ` reads.  A typing system that ties nothing reads `der` there.
* **The reading `J.read`** (the design's `⟦J⟧ : TypingJ`), what B and the pins see: at each
  admissible instance `η` of the row context, a derivation of `J` at the empty row context whose
  conclusion has no row `∀` and denotes the instance, `Γ η ⊢ e : j η`.  The derivation may use
  `∀` inside: a let-bound polymorphic function is internal to it, so the reading holds of every
  closed program the typing system types.  It is pointwise, as B reads judgements
  (`SemW` at every admissible instance): a syntactic conclusion at the row context would not hold
  of a family of judgements that no open type denotes, and `ExtendsNU` asks for every family of
  today's (builder's note, RESTRUCTURE §Unresolved).
* **`tier1Open`**: today's kernel over the open types — a judgement holds only at `∀`-free types,
  where it is `tier1NU` at their families.  Its reading is `tier1NU` (`tier1Open_read`).
* **`RowVarKernel J`**, recorded, not a conjunct of done: decision 62's mechanism, `J` closed under
  `[allR-I]` and `[allR-E]` at `U` and `!U` (Curry-style: no term former).  Done requires effect
  polymorphism through A's schemas; `RowVarKernel` records how `J₂` will meet it.
-/

noncomputable section

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Targets (RVar RowEnv RowCon RowCtx RowForm EffCtx TypingJ OutJ CDerivesNU tier1NU orowRF)

/-- **A typing system over the open types of the row form `RF`.** -/
structure OurTyping (RF : RowForm) where
  /-- `Θ; Δ; Γ ⊢ e : j`. -/
  der : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop
  /-- The outlives judgements its rules consult (OQ-28 open in them). -/
  out : OutJ
  /-- Its row variables as the row form's variables. -/
  env : ∀ Ξ, RowEnv → (RF.alg Ξ).Var → Row
  /-- Its judgement at the effect context `Ξ`: the derivations whose inner rows, the rows of their
  handlers and operations, are tied to `Ξ` (decision R).  Our instance at `Ξ` reads it. -/
  derAt : EffCtx → RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop

/-- The empty row context admits every environment. -/
theorem rowCtx_models_nil (η : RowEnv) : RowCtx.Models [] η := fun _ _ h => absurd h (by simp)

/-- **The reading** (`⟦J⟧`): at each admissible instance, a derivation at the empty row context
with a `∀`-free conclusion denoting the instance. -/
def OurTyping.read {RF : RowForm} (J : OurTyping RF) : TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → ∃ (Γ' : Ctx OVTy) (j' : OJdg), octxRFree Γ' ∧ j'.RFree ∧
      J.der [] Δ Γ' e j' ∧ (∀ η', octxDen η' Γ' = Γ η) ∧ (∀ η', j'.den η' = j η), J.out⟩

/-- Today's kernel over the open types: `∀`-free types, `CDerivesNU` at every admissible
instance. -/
def tier1OpenDer : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop :=
  fun Θ Δ Γ e j => octxRFree Γ ∧ j.RFree ∧
    ∀ η, Θ.Models η → CDerivesNU Δ (octxDen η Γ) e (j.den η)

/-- **`tier1Open`**: today's kernel, unr-free, over the open types at the minimal tail-variable row
form.  Its row variables are those of the row context only. -/
def tier1Open : OurTyping orowRF := ⟨tier1OpenDer, OutJ.core, fun _ η => η, fun _ => tier1OpenDer⟩

/-- **The reading of `tier1Open` is `tier1NU`.** -/
theorem tier1Open_read : tier1Open.read = tier1NU := by
  show TypingJ.mk _ _ = TypingJ.mk _ _
  congr 1
  funext Θ Δ Γ e j
  apply propext
  constructor
  · intro h η hη
    obtain ⟨Γ', j', -, -, ⟨-, -, hd⟩, hΓ, hj⟩ := h η hη
    have h' := hd η (rowCtx_models_nil η)
    rwa [hΓ η, hj η] at h'
  · intro h η hη
    refine ⟨octxOf (Γ η), OJdg.ofJ (j η), octxRFree_octxOf _, OJdg.rFree_ofJ _,
      ⟨octxRFree_octxOf _, OJdg.rFree_ofJ _, fun η' _ => ?_⟩,
      fun η' => octxDen_octxOf η' _, fun η' => OJdg.den_ofJ η' _⟩
    rw [octxDen_octxOf, OJdg.den_ofJ]
    exact h η hη

/-! ### The row `∀`, recorded -/

/-- `ρ` is admissible at the constraint `k` along the family `σ`, at every admissible instance of
`Θ`. -/
def AdmAt (Θ : RowCtx) (k : RowCon) (σ : RowEnv → Row) : Prop :=
  ∀ η, Θ.Models η → k.cls.Admits (σ η) ∧ ∀ o ∈ σ η, k.adm o

/-- `Γ` does not mention the row variable `ρ`. -/
def FreshIn (ρ : RVar) (Γ : Ctx OVTy) : Prop :=
  ∀ η r, octxDen (Function.update η ρ r) Γ = octxDen η Γ

/-- **`[allR-I]`**, at `U` and at `!U`: a λ-value typed at `U C` with `ρ` fresh for `Θ` and `Γ` is
typed at `U(∀ρ:k. C)`. -/
def RC_allRI {RF : RowForm} (J : OurTyping RF) : Prop :=
  ∀ Θ Δ Γ (b : Expr) C ρ k, ρ ∉ Θ.map Prod.fst → FreshIn ρ Γ →
    (J.der ((ρ, k) :: Θ) Δ Γ (.val (Val.lam b)) (.val (.thunk C)) →
      J.der Θ Δ Γ (.val (Val.lam b)) (.val (.thunk (.allR ρ k C)))) ∧
    (J.der ((ρ, k) :: Θ) Δ Γ (.val (Val.lam b)) (.val (.bang (.thunk C))) →
      J.der Θ Δ Γ (.val (Val.lam b)) (.val (.bang (.thunk (.allR ρ k C)))))

/-- **`[allR-E]`**, at `U` and at `!U`: a value at `U(∀ρ:k. C)` is at `U C'` for every `C'` whose
instances are `C`'s with `ρ` read as an admissible row family `σ`. -/
def RC_allRE {RF : RowForm} (J : OurTyping RF) : Prop :=
  ∀ Θ Δ Γ V C C' ρ k (σ : RowEnv → Row), AdmAt Θ k σ →
    (∀ η, OCTy.den η C' = OCTy.den (Function.update η ρ (σ η)) C) →
    (J.der Θ Δ Γ V (.val (.thunk (.allR ρ k C))) → J.der Θ Δ Γ V (.val (.thunk C'))) ∧
    (J.der Θ Δ Γ V (.val (.bang (.thunk (.allR ρ k C)))) → J.der Θ Δ Γ V (.val (.bang (.thunk C'))))

/-- **Decision 62's mechanism**, recorded: the typing system has the row `∀`. -/
def RowVarKernel {RF : RowForm} (J : OurTyping RF) : Prop := RC_allRI J ∧ RC_allRE J

end Targets.Inst

end
