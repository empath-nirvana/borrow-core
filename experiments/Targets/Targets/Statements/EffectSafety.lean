import Targets.Defs.Typing
import Targets.Defs.Runs

/-!
# Targets — P2, effect safety, and T0, the effect algebra (DESIGN §6 P2)

**World:** [prog].  T0 is about the row form and its link to the typing rules.

* **P2** (`EffSafe`): a program typed at `F_Σ A`, `Σ` unr-free, only ever stops at a value or at an
  operation of `Σ`, of the right kind, and is never stuck elsewhere.  At `Σ = []` it never stops at
  an operation: no unhandled operation.
* **T0** (`RowAlgSafe RF`, with `RowLink RF`): the row form the typing rules use, with row
  variables, is an effect algebra in Yoshioka et al.'s sense (Def. 3.5) and meets their safety
  conditions (Def. 5.1): subeffecting cannot hide a performed operation, and handling one name
  never erases another's operations.  Def. 7.1 (masking) and Def. 7.6 (dispatch ignoring type
  arguments) do not apply: there is no masking, and dispatch is by `(n, i)`.

Literature: Yoshioka–Sekiyama–Igarashi (ICFP 2024) Def. 5.1 ("(1) For any L, (L)↑ < 0 does not
hold. (2) If (L)↑ < ε and (L′)↑ ⊙ ε′ ∼ ε and L ≠ L′, then (L)↑ < ε′") and Thm 5.8 ("If ∅ ⊢ e : A | 0
and e −→∗ e′ ↛, then e′ = v"); System C Cor. 9 ("never results in an undelimited label"); Tang et
al. Thm 3.2.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Steps Step1)

/-- **P2**, at unr-free rows (a row with a resuming `unr` operation is covered at tier 1, by Core's
adequacy). -/
def EffSafe (J : TypingJ) : Prop :=
  ∀ e (S : Row) A, Row.NU S → J.closed e (CTy.effOf S A) →
    ∀ μ' e', Steps (ℍ := ℍ) Adequacy.emptyMem e μ' e' →
      IsVal e' ∨ (∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'') ∨ StopsIn S e'

/-- Yoshioka–Sekiyama–Igarashi Def. 5.1: the safety conditions of an effect algebra. -/
structure EffAlg.Safe (EA : EffAlg) : Prop where
  c1 : ∀ L, ¬ EA.Sub (EA.lift L) EA.unit
  c2 : ∀ L L' ε ε' x, EA.Sub (EA.lift L) ε → EA.comp (EA.lift L') ε' = some x → EA.eqv x ε →
         L ≠ L' → EA.Sub (EA.lift L) ε'

/-- **T0**: the row form's algebra is an effect algebra (Def. 3.5) that meets the safety conditions
(Def. 5.1), at every effect context.  In `EndStateAt` beside `RowLink RF`. -/
def RowAlgSafe (RF : RowForm) : Prop := ∀ Ξ : EffCtx, (RF.alg Ξ).Laws ∧ (RF.alg Ξ).Safe

end Targets

end
