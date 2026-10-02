import GhostEnd.ClosureBody
import GhostEnd.Branch

/-!
# GhostEnd — a closure capturing the lend across a yield, every hypothesis discharged

    withbor ℓ (Λ. λm. return (thunk (return forget to fg. fg m to r. return r)) to f.
                      perform yield 1 to u.
                      u; force f)

at the row `{yield : I32 ↠ 1}`, linear and resuming. Before the yield the borrower packs `m`
into a closure `f : U(F(['x] 1))`. At the stop the frame holds `f`, and the lend's cell sits
inside `f`'s environment. The cell is dropped there; at the resumption the fresh view goes back
into the environment and `f` is re-derived at the new lend from its own typing (`tv_thaw`,
`tv_sound`). After the yield `f` is forced, and it answers the box that hands the owner back.

`f`'s type does not mention `'x`, and a thunk does not outlive anything, so `StopSafe` and
`LOk` both reject this frame. `closure_spans_yield` is `withbor_of_rbodyC` with every hypothesis
discharged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd.Capture
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd.Instance (yieldOp)
open GhostEnd.Branch (mS deadOf deadPD hbx hΔx hS hT hf yieldE)

/-- The closure's type: a thunk answering the box. -/
abbrev Uf : VTy := .thunk (.ret (.box (.var 0) .unit))

/-- The closure's body, `m` at index `1` under the thunk's dead binder. -/
def body₀ : Expr := bindE forget (bindE (.app (.var 0) (.var 2)) (.var 0))

/-- `u; force f`. -/
def after : Expr := .seq (.var 0) (forceE (.ret (.box (.var 0) .unit)) (.var 1))

/-- The borrower's body. -/
def body : Expr := bindE (.val (.lam body₀)) (bindE (yieldE 1) after)

theorem d_body₀ :
    CDerives Δ₁ (⟨.unit, false⟩ :: ([] ++ [mS true])) body₀ (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.dead (.right .nil)) (.ret (.forgetMut (a := .var 0) (A := .unit) (.cons (.cons .nil))))
    (.bind (.left (.dead (.left .nil)))
      (.app (.left (.dead (.right .nil))) (.force (.here (.cons (.cons .nil))))
        (.there (.there (.here .nil))))
      (.ret (.boxI (.var (.here (.cons (.cons (.cons .nil)))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons (.cons .nil)))))))

theorem d_after :
    CDerives Δ₁ ([⟨.unit, true⟩, ⟨Uf, true⟩] ++ [mS false]) after
      (.comp (.ret (.box (.var 0) .unit))) :=
  .unitE (.left (.right (.dead .nil))) (.var (.here (.cons (.cons .nil))))
    (.force (.there (.here (.cons .nil))))

abbrev RB (Γ : Ctx VTy) (ml : Bool) (E : Expr)
    (Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp) : Prop :=
  RBodyC LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] Γ ml E Ans

theorem rb_mid : RB [⟨Uf, true⟩] false (bindE (yieldE 1) after) (ansRC 0 (.box (.var 0) .unit)) :=
  rbodyC_let hbx hΔx hT hS (Γ₁ := [⟨Uf, false⟩]) (Γ₂ := [⟨Uf, true⟩]) (ml₁ := false)
    (ml₂ := false) (A₁ := yieldOp.B) (.right (.dead .nil))
    (rbodyC_perform hbx hΔx hS hf (fundamentalC (.lit (.i32 1) (deadPD [Uf]))))
    (rbodyC_ret hbx hΔx (fundamentalC d_after))

theorem rb_body : RB [] true body (ansRC 0 (.box (.var 0) .unit)) :=
  rbodyC_let hbx hΔx hT hS (Γ₁ := []) (Γ₂ := []) (ml₁ := true) (ml₂ := false) (A₁ := Uf)
    (.left .nil) (rbodyC_thunk d_body₀) rb_mid

/-- **A closure capturing the lend across a yield.** From `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`, the program is in
`𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`, at every assignment and record list. -/
theorem closure_spans_yield (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam body), .lam⟩))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withbor_of_rbodyC hδ hβ hT (by simp [VFree]) (βP := ⊤) ?_ (by decide) rb_body l v ls
  intro ls w σ h
  rw [h.1]; exact ResU.inStratum_empty _

end GhostEnd.Capture
