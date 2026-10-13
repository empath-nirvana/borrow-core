import Core.Types
import ProbeD1.GapWitness

/-!
# ProbeD1 — probes for `BRIDGE.md`

Two facts the bridge design reads.

* **A thunk is already confined.** `U C` has no outlives derivation (`thunk_not_outlives`), so a
  context with a live `U` slot is never `CtxOutlives` (`ctxOutlives_not_of_live_thunk`), and `[]I`
  (`CDerives.boxI`, whose premise is `CtxOutlives`) cannot box any value typed in it. A value built
  from a continuation `κ : U C` therefore cannot leave a borrow callback, whose result is
  `['x] B`, nor a handler that ends a lifetime the same way. This is the "external, bounded" half
  of the bridge, and it needs no new former.
* **The unrestricted thaw of Core's relation is false.** Moving every lifetime below a cut by an
  order embedding — the instantiation a resume would apply to a frozen computation's internal
  lifetimes, here at the cut `⊤` — does not preserve Core's `cC` at every configuration
  (`not_coreThawTop`, a corollary of `coreAllNotNatural`). The witness is GAP.md §3c's; it is not
  claimed to arise from a typed program, so this is a fact about the unrestricted statement, not an
  obstruction to a thaw restricted to residuals of typed programs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1.Bridge
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `U C` outlives nothing: `VOutlivesR` has no `thunk` rule. -/
theorem thunk_not_outlives {Rb Rr : Lifetime.Life → Prop} (C : CTy) :
    ¬ VOutlivesR Rb Rr (.thunk C) := by
  intro h; cases h

/-- A context holding a live `U` slot outlives no lifetime, so `[]I` boxes nothing typed in it. -/
theorem ctxOutlives_not_of_live_thunk {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    {C : CTy} {s : Slot VTy} (hs : s ∈ Γ) (hl : s.live = true) (ht : s.ty = .thunk C) :
    ¬ CtxOutlives Δ Γ a := by
  rintro ⟨-, h⟩
  have h' := h s hs hl
  rw [ht] at h'
  exact thunk_not_outlives C h'

/-- The thaw of Core's computation relation along the internal instantiation `shift ⊤ 1`, at every
configuration: reading, records and resource moved together. -/
def CoreThawTop : Prop :=
  ∀ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    cC (ℍ := ℍ) C ls δ e ρ →
      cC (ℍ := ℍ) C (ls.map (Targets.srecRestrat adjθ)) (Restrat.LSub.mapN adjθ.toNat δ) e
        (adjθ.relRU ρ)

/-- **The unrestricted thaw is false**, by GAP.md §3c's witness. -/
theorem not_coreThawTop : ¬ CoreThawTop (ℍ := ℍ) := by
  intro h
  obtain ⟨C, ls, δ, e, ρ, h₁, h₂⟩ := coreAllNotNatural (ℍ := ℍ)
  exact h₂ (h C ls δ e ρ h₁)

end ProbeD1.Bridge

end
