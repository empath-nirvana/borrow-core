import Coeffects.Imm

/-!
# Coeffects — a `needs` layer that elaborates into `CDerives`

`KDem U x Δ Γ e T`: `e` is the elaboration of a computation of `T` that **needs** `Mut U` of its
context, implicitly (its source never names the demand).  Three rules:

* `need`: any core term at the demand type `Dem U T` (a primitive use of the demand, or a call of
  a function whose result needs it: `f a : Dem U T`);
* `weaken`: a computation that needs nothing;
* `seq`: two computations that need `Mut U`, in sequence, need it once.  It elaborates to
  `seqD e₁ e₂`, the reborrow contraction (`d_seqD`).

and two **providers**, which discharge the demand for their scope:

* `provide_wf`: from an owned cell `c : Ref U`, by `withbor` form 2;
* `reprovide_wf`: from a borrow the caller holds, `m : Mut @a U`, by `withbor` form 3.  A
  function that needs `Mut U` called from another that needs it is served this way.

`KDem.elab` turns every `KDem` derivation into a `CDerives` derivation of the elaborated term, so
`fundamentalC` gives soundness (`KDem.sem`) and there is no new semantic case.  The layer adds no
rule to `CDerives` and no index to it: the demand is a callback type, and discharging it is a
borrow.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Coeffects
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)
open BoCa.Programs (app2)
open Optics

/-- The `needs Mut U` layer.  `x` is the lifetime binder the demand is served at. -/
inductive KDem (U : VTy) (x : LifeVar) : LifeCtx → Ctx VTy → Expr → VTy → Prop where
  /-- A core term at the demand type. -/
  | need {Δ Γ e T} (hT : plainV T = true) (h : CDerives Δ Γ e (.val (demTy U x Δ.meetOfDom T))) :
      KDem U x Δ Γ e T
  /-- A value that needs nothing. -/
  | weaken {Δ Γ t T} (hT : plainV T = true) (hΓ : Ctx.Dead Γ)
      (ht : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives (FD₁ Δ x) Γ' t (.val T)) :
      KDem U x Δ Γ (weakenD t) T
  /-- Sequencing: the demand is shared, and each side is served by a reborrow. -/
  | seq {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.SplitP Γ Γ₂ Γ₁)
      (h₁ : KDem U x Δ Γ₁ e₁ T₁) (h₂ : KDem U x Δ Γ₂ e₂ T₂) :
      KDem U x Δ Γ (app2 seqD e₁ e₂) (.tensor T₁ T₂)

theorem KDem.plain {U : VTy} {x : LifeVar} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T : VTy}
    (h : KDem U x Δ Γ e T) : plainV T = true := by
  induction h with
  | need hT => exact hT
  | weaken hT => exact hT
  | seq _ _ _ ih₁ ih₂ => simp [plainV, ih₁, ih₂]

/-- **Elaboration.**  A `KDem` derivation is a `CDerives` derivation of the elaborated term at
the demand type. -/
theorem KDem.elab {U : VTy} {x y : LifeVar} {Δ : LifeCtx} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hy : Δ.find? y = none) (hxy : x ≠ y) (hU : Payload U) {Γ : Ctx VTy} {e : Expr} {T : VTy}
    (h : KDem U x Δ Γ e T) : CDerives Δ Γ e (.val (demTy U x Δ.meetOfDom T)) := by
  induction h with
  | need _ h => exact h
  | weaken _ hΓ ht => exact d_weakenD hΔ hx hΓ ht
  | @seq Γ' Γ₁ Γ₂ e₁ e₂ T₁ T₂ hs h₁ h₂ ih₁ ih₂ =>
      exact .lolliE hs ih₂ (.lolliE (splitP_left_all Γ₁) ih₁
        (d_seqD hΔ hx hy hxy hU h₁.plain h₂.plain (kill_dead Γ₁)))

/-- **Soundness**, by `fundamentalC`: nothing new. -/
theorem KDem.sem {U : VTy} {x y : LifeVar} {Δ : LifeCtx} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hy : Δ.find? y = none) (hxy : x ≠ y) (hU : Payload U) {Γ : Ctx VTy} {e : Expr} {T : VTy}
    (h : KDem U x Δ Γ e T) : SemV (ℍ := ℍ) Δ Γ e (demTy U x Δ.meetOfDom T) :=
  fundamentalC (h.elab hΔ hx hy hxy hU)

/-- **The provider from an owned cell.**  `provide c { e }`, elaborated `withbor c e`:
`Ref U ⊗ T`.  The demand of `e` is discharged for its scope, and the cell comes back. -/
theorem provide_wf {U : VTy} {x y : LifeVar} {Δ : LifeCtx} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hy : Δ.find? y = none) (hxy : x ≠ y) (hU : Payload U)
    {Γ Γe Γc : Ctx VTy} {c e : Expr} {T : VTy} (hs : Ctx.SplitP Γ Γe Γc)
    (hc : CDerives Δ Γc c (.val (.ref U))) (h : KDem U x Δ Γe e T) :
    CDerives Δ Γ (app2 withbor c e) (.val (.tensor (.ref U) T)) :=
  .lolliE hs (h.elab hΔ hx hy hxy hU) (.lolliE (splitP_left_all Γc) hc
    (.withbor2 x (kill_dead Γc).toP hx
      ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, hU.outlives _ _⟩ (hU.noFree _)
      (plain_noFree h.plain)))

/-- **The provider from a borrow the caller holds.**  `withbor m e` with `m : Mut @a U`:
`Mut @a U ⊗ T`.  A computation that needs `Mut U`, run by a caller that itself holds the
demand, is served by a reborrow. -/
theorem reprovide_wf {U : VTy} {x y : LifeVar} {Δ : LifeCtx} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hy : Δ.find? y = none) (hxy : x ≠ y) (hU : Payload U) {a : Lifetime.Life}
    {Γ Γe Γc : Ctx VTy} {c e : Expr} {T : VTy} (hs : Ctx.SplitP Γ Γe Γc)
    (hc : CDerives Δ Γc c (.val (.mut a U))) (h : KDem U x Δ Γe e T) :
    CDerives Δ Γ (app2 withbor c e) (.val (.tensor (.mut a U) T)) :=
  .lolliE hs (h.elab hΔ hx hy hxy hU) (.lolliE (splitP_left_all Γc) hc
    (.withbor3 x (kill_dead Γc).toP hx (hU.noFree _) (plain_noFree h.plain)))

end BoCa.Fig16.LogRel.Core.Coeffects

end
