import Core.Fundamental

/-!
# SecondClass — the fixed point with a passed environment, and at a record

`bounded_fix[A, C]` (SPEC §20, `Core/BoundedFix.lean`) is stated at every value type `A` and
every computation type `C`. Two restatements of a recursive group's step are therefore instances
of it, with no new rule and no new obligation:

- **`!` code with a passed environment.** The step is `!` code, and the group's environment `E`
  (an answering capability `Mut 'l S`, an owned value, a layer's state) is not captured: it is a
  component of the argument, `A = E ⊗ A₀`, handed back in the answer when the caller needs it.
  Each level receives the environment, as System Ξ's blocks do in
  `experiments/HandlersAsBorrows` (`EnvTy`), and as SPEC §2's `FnMut` row does.
  `boundedFixEnv_compatX` is `boundedFix_compatX` at `A = E ⊗ A₀`.
- **A record of functions** (Bekič). A group whose members answer different types is one fixed
  point at `C = (A₁ ⊸ C₁) & (A₂ ⊸ C₂)`, `A = 1`: the group is a recursive object, the step its
  generator, and a call of member `j` forces the self-reference and projects.
  `boundedFixRec_compatX` is `boundedFix_compatX` at that `C`.

Both are stated at the paper's judgment (`CDerives.boundedFix`) and at the relation
(`boundedFix_compatX`). The probe programs that use them are `RecLog.lean` (typed here) and
`probes/*.bc` (typed by the certifying checker).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.SecondClass
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### `!` code with a passed environment -/

/-- The self-reference of a step over the environment `E`: `1 ⊕ !U(E ⊗ A ⊸ C)`. The code is
`!`; the environment is not in it. -/
abbrev envSelfTy (E A : VTy) (C : CTy) : VTy := fixSelfTy (.tensor E A) C

/-- The step over the environment `E`: `!U((1 ⊕ !U(E ⊗ A ⊸ C)) ⊗ (E ⊗ A) ⊸ C)`. -/
abbrev envStepTy (E A : VTy) (C : CTy) : VTy := fixStepTy (.tensor E A) C

/-- `bounded_fix` at a passed environment. -/
abbrev boundedFixEnvTy (E A : VTy) (C : CTy) : VTy := boundedFixTy (.tensor E A) C

/-- The restated rule at the judgment: `bounded_fix[E ⊗ A, C]`. -/
theorem CDerives.boundedFixEnv {Δ : LifeCtx} {Γ : Ctx VTy} (E A : VTy) (C : CTy)
    (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixEnvTy E A C)) :=
  .boundedFix (.tensor E A) C hΓ

/-- **The restated rule is sound**, at every environment, argument and computation type: it is
`boundedFix_compatX` at `E ⊗ A`. -/
theorem boundedFixEnv_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {E A : VTy} {C : CTy}
    (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .boundedFix)) (boundedFixEnvTy E A C) :=
  boundedFix_compatX hΓ

/-- The step's code is persistent, whatever the environment: its type is a `!`, so it may be
copied into every level and held by the self-reference. The environment's type `E` is
unconstrained. -/
theorem envStepTy_persistent (E A : VTy) (C : CTy) : (envStepTy E A C).Persistent := rfl

/-! ### A record of functions -/

/-- The record of two members' functions, `(A₁ ⊸ C₁) & (A₂ ⊸ C₂)`. -/
abbrev recTy (A₁ A₂ : VTy) (C₁ C₂ : CTy) : CTy := .amp (.arr A₁ C₁) (.arr A₂ C₂)

/-- The fixed point at a record, at the judgment: `bounded_fix[1, (A₁ ⊸ C₁) & (A₂ ⊸ C₂)]`. -/
theorem CDerives.boundedFixRec {Δ : LifeCtx} {Γ : Ctx VTy} (A₁ A₂ : VTy) (C₁ C₂ : CTy)
    (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy .unit (recTy A₁ A₂ C₁ C₂))) :=
  .boundedFix .unit _ hΓ

/-- **The fixed point at a record is sound**: `boundedFix_compatX` at `C = (A₁ ⊸ C₁) & (A₂ ⊸ C₂)`.
The members' answer types `C₁`, `C₂` are independent, rows included. -/
theorem boundedFixRec_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A₁ A₂ : VTy} {C₁ C₂ : CTy}
    (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .boundedFix)) (boundedFixTy .unit (recTy A₁ A₂ C₁ C₂)) :=
  boundedFix_compatX hΓ

/-- The two compose: a record whose members each take the group's environment. -/
theorem boundedFixEnvRec_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {E A₁ A₂ : VTy} {C₁ C₂ : CTy}
    (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .boundedFix))
      (boundedFixTy .unit (recTy (.tensor E A₁) (.tensor E A₂) C₁ C₂)) :=
  boundedFix_compatX hΓ

end BoCa.Fig16.LogRel.Core.SecondClass
