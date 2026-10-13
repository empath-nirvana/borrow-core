import Targets.B.Guarantees

/-!
# System B — P14, well-bracketing conservativity (RESTRUCTURE §3.3, §3.6)

At `BWorld` (they read only `val`, `Ext` and `nil`); B's, since `SoundnessContractsOfFL` reads
`Conservative`.

* **P14.a** (`WBCore`): tier 1 is well-bracketed by construction: R-T1 (`Core/EffDefs.lean`'s
  `wpG`).  Proved (`wbCore`), independent of `J` and `M`: a companion lemma, not a conjunct.
* **P14.b** (`ConservativeWB`): today's Core relation embeds into W at row-abortive types, at every
  index reachable from σ = [].  It needs `Mono`, so it is beside done, in the device (§3.6).
* **P14.b′, every type** (`Conservative`): A7 in full, beside done.

Literature: Timany–Guéneau–Birkedal, POPL 2024 ("A program is said to be well-bracketed if every
called function must return before its caller can resume execution"); the survey's T7.
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
def ConservativeWB (M : B.BWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE (ℍ := ℍ) none b A ls δ v ρ →
    ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ

/-- **P14.b′, every type**: A7 in full.  Beside done. -/
def Conservative (M : B.BWorld) : Prop :=
  ∀ b A ls δ v ρ, vCE (ℍ := ℍ) none b A ls δ v ρ →
    ∀ i', M.Ext (ls, M.nil) i' ρ → M.val b A i' δ v ρ

end Targets

end
