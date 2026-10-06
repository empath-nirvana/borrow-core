import Targets.Statements.Device

/-!
# Targets — P14, well-bracketing conservativity (DESIGN §6 P14)

**World:** P14.a is [Core σ=[]]; P14.b relates [Core σ=[]] to [W].

* **P14.a** (`WBCore`): tier 1 is well-bracketed by construction: no frame or record a run opens
  is open at any of its stops (R-T1, `Core/EffDefs.lean`'s `wpG`).
* **P14.b, T7's shape** (`ConservativeWB`, a conjunct of done): a value today's Core proves valid,
  at a type whose callbacks can perform only operations in `{fn, abort}` (the row-abortive types;
  `fn` operations are answering effects, which are borrows and not rows), stays valid in W at every
  index reachable from its σ = [] index.
* **P14.b′, every type** (`Conservative`, beside done): A7 in full, open as the survey says.
* **P14.c**: what tier 2 gives up is a proof principle (R-T1), not a valid value.  Stated only as a
  machine-checked obstruction when one is built; none is claimed.

Both P14.b forms read `vCE none`, Core's relation as this branch imports it; `Targets/Audit.lean`
pins its definition, so a redefined Core cannot meet them by definition.

Literature: Timany–Guéneau–Birkedal, POPL 2024 ("A program is said to be well-bracketed if every
called function must return before its caller can resume execution"); the survey's T7 ("for every
library L proved sound against well-bracketed contexts: L remains sound in every context whose
operations, as observable from L's callbacks, are in {fn, abort}").
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

/-- **P14.a.**  `wpG`'s conjunct at `Core/EffDefs.lean:40`. -/
def WBCore : Prop :=
  ∀ ls e (Q : List SRec → Expr → WProp) ρ, wpG (ℍ := ℍ) ls e Q ρ →
    wpG (ℍ := ℍ) ls e (fun ls' t ρ' => Q ls' t ρ' ∧ ∀ x, x ∈ ls' ↔ x ∈ ls) ρ

/-- **P14.b, T7's shape**: today's Core relation embeds into W at row-abortive types, at every
index reachable from σ = [], in both modes.  A conjunct of done. -/
def ConservativeWB (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE (ℍ := ℍ) none b A ls δ v ρ →
    ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ

/-- **P14.b′, every type**: A7 in full.  Beside done. -/
def Conservative (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, vCE (ℍ := ℍ) none b A ls δ v ρ →
    ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ

end Targets

end
