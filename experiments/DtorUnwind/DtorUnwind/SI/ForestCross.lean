import DtorUnwind.SI.ForestIStopN

/-!
# Stage 5, stated: a borrow handed to another task across a stop

A task spawned inside an `imm` lend that borrows from its parent hands the borrow out of the lend
at a stop: the payload of the spawn carries a view at the lend's lifetime `A`, so it is not in
`Res_A`. `OpTabN.ILendOKX` is `ILendOKK` without the payload condition, and `CrossTaskILend` is
`erwp_I_frameK`'s statement at such a table.

Not derived, and no obstruction verified. `erwp_I_frameK` reads the payload condition at one
step, 6.38 at the stop (`six38_no_borrow_in_frame`: the payload holds no view at the frame's
location), which is what lets the lender take the borrow back at the frame's end. Without it the
frame's end needs every view handed out to be gone, which is a fact about the scheduler (the
child has finished or been cancelled before the parent's lend ends), not about any one table
entry.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub)

/-- `ILendOKK` with no condition on what a stop passes out. -/
structure OpTabN.ILendOKX (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧ IWcUnfold A en.wc
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB k ls₁ w ρ → en.PB k ls₂ w ρ

/-- **The cross-task Imm Frame.** `erwp_I_frameK` at a table whose stops may pass the borrow
out. -/
def CrossTaskILend : Prop :=
  ∀ (Φ : LocFam) (l : Loc) (T : VTy) (δ : LSub) (_ : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (_ : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (_ : ∀ ls₁ ls₂ ρ, Ext ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    (A : Life) (Tb : OpTabN) (_ : Tb.ILendOKX A) (Q : PostN)
    (_ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ)
    (n : Nat) (ls : List SRec) (e : Expr) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
    ρb.InStratum A → P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP →
    ResU.CompS ρlP ρb ρ → (∀ x ∈ ls, x.2 ≠ A) → ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
    (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
      erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
        e BI) →
    erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
