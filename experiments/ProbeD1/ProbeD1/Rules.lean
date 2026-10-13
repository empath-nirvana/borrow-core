import ProbeD1.World

/-!
# ProbeD1 — the probe's rule set (DESIGN §11)

`ProbeRules Δ Γ e j` holds when the judgement is derivable from Core's rules without resuming `unr`
operations together with the three spanning rules the probe validates: `withbor` (1), `withbor` (2)
and `withload` at a resuming row (`SpanRule1`, `SpanRule2`, `SpanRuleLoad` at `admClosedOp`). It is
the least typing system, at Core's outlives judgements, that holds every judgement of Core's
unr-free fragment and is closed under Core's rules (`ExtendsNU`, Targets' end-state pin) and under
those three rules. A derivation is exhibited by building the judgement from the closure properties.

It is the rule set the arising check reads (`Arising.lean`): a configuration arises from runs of
terms derivable here, and a value arises as the answer of one.

A definition only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Targets (TypingJ OutJ ExtendsNU SpanRule1 SpanRule2 SpanRuleLoad admClosedOp)

/-- **The probe's rule set**: derivable in every typing system at Core's outlives judgements that
extends Core's unr-free rules, is closed under them, and is closed under the spanning rules of
`withbor` (1), `withbor` (2) and `withload` at `admClosedOp`. -/
def ProbeRules (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  ∀ J : TypingJ, J.out = OutJ.core → ExtendsNU J → SpanRule1 J admClosedOp →
    SpanRule2 J admClosedOp → SpanRuleLoad J admClosedOp → J.at Δ Γ e j

end ProbeD1

end
