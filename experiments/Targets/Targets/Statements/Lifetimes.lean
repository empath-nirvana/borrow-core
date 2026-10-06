import Targets.Defs.World
import Targets.Defs.Typing

/-!
# Targets — P9, lifetime soundness (DESIGN §6 P9)

**World:** [W].

A value of a type that outlives `@a` holds only resources that outlive `@aδ`, at every type of the
calculus, suspension types included, at every index: [TR] 6.60 at W ("If ∆ ⊢ T ⊐ @a and δ ∈ ⟦∆⟧,
and ρ ∈ 𝒱⟦T⟧δ then @ρ ⊐ @aδ").  So no capability is used outside its handler's extent, and no
continuation is resumed after a lifetime it holds a loan from has ended (the survey's A4).

The outlives judgments are the typing system's own (`J.out`), and every rule transcription reads
them, so `LifetimeSound M J.out` certifies exactly the outlives rules `J` uses.  Core's have no rule
at `U C`; whether tier 2 adds one, or a `[gen]` rule, is OQ-28.  The machine sees locations, not
lifetimes, so this property has no program-level form here; T1 covers its use-after-free
consequence.
-/

noncomputable section

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **P9**: 6.60 at W, at both of the typing system's outlives judgments, both modes, every
index. -/
def LifetimeSound (M : SemWorld) (O : OutJ) : Prop :=
  (∀ Δ δ a α T b i v ρ, LifeCtx.Models Δ δ → Lifetime.Life.interp δ a = some α → O.lt Δ a T →
     M.val b T i δ v ρ → BoLo.Outlives ρ α) ∧
  (∀ Δ δ a α T b i v ρ, LifeCtx.Models Δ δ → Lifetime.Life.interp δ a = some α → O.le Δ a T →
     M.val b T i δ v ρ → OutlivesLe ρ α)

end Targets

end
