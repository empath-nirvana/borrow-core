import ModesLabels.Modes
/-!
# Experiment: the borrow axioms as labelled shifts

`shiftTy src view ret x bnd T₂ = src ⊸ (∀'x ⊏ bnd. view 'x ⊸ ['x] T₂) ⊸ R`, with
`R = src ⊗ T₂` when `ret` and `R = T₂` otherwise.  The four label-introducing axioms are
instances (`withbor1_shift` … `withload_shift`).  At each, the view's mode is at least the
source's, and the source comes back exactly when its mode lacks contraction.
`withswap` is not an instance: its callback is a bare `⊸` with no label.
-/

namespace Experiments.Shifts
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Typed Experiments.ModesLabels
open BoCa.Lifetime (LifeVar)

/-- A labelled shift. -/
def shiftTy (src : Ty) (view : Lifetime.Life → Ty) (ret : Bool) (x : LifeVar)
    (bnd : Lifetime.Life) (T₂ : Ty) : Ty :=
  .lolli src (.lolli (.all x bnd (.lolli (view (.var x)) (.box (.var x) T₂)))
    (if ret then .tensor src T₂ else T₂))

theorem withbor1_shift (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    axWithbor1Ty x bnd T₁ T₂ = shiftTy (.ref T₁) (fun a => .imm a T₁) true x bnd T₂ := rfl

theorem withbor2_shift (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    axWithbor2Ty x bnd T₁ T₂ = shiftTy (.ref T₁) (fun a => .mut a T₁) true x bnd T₂ := rfl

theorem withbor3_shift (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    axWithbor3Ty a x bnd T₁ T₂ = shiftTy (.mut a T₁) (fun b => .mut b T₁) true x bnd T₂ := rfl

theorem withload_shift (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    axWithloadTy a x bnd T₁ T₂ =
      shiftTy (.imm a T₁) (fun b => T₁.immReborrow b) false x bnd T₂ := rfl

/-- The (source mode, view mode, returned) triple of each instance, at any `T₁`. -/
theorem shift_modes (a b : Lifetime.Life) (T₁ : Ty) :
    (mode (.ref T₁), mode (.imm b T₁)) = (.lin, .unr) ∧
    (mode (.ref T₁), mode (.mut b T₁)) = (.lin, .aff) ∧
    (mode (.mut a T₁), mode (.mut b T₁)) = (.aff, .aff) ∧
    (mode (.imm a T₁), mode (T₁.immReborrow b)) = (.unr, .unr) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [mode_immReborrow]; rfl

/-- The source is returned exactly when its mode lacks contraction. -/
theorem ret_iff_not_C (a : Lifetime.Life) (T₁ : Ty) :
    ¬ (mode (.ref T₁)).C ∧ ¬ (mode (.mut a T₁)).C ∧ (mode (.imm a T₁)).C := by
  simp [mode, Mode.C]

/-- The one (source, view) pair with view mode ≥ source mode that the table lacks. -/
def axWithborMITy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) : Ty :=
  shiftTy (.mut a T₁) (fun b => .imm b T₁) true x bnd T₂

end Experiments.Shifts
