import Targets.Defs.Typing

/-!
# Targets — T4, Lowering and zero cost (cross-language) (DESIGN §3 T4, notebook P13)

**World:** [prog] and the backend's IRs.  **Named-only; out of the first pass.**

* **`LoweringCorrect J`** (Ma–Ge–Jung–Zhang, OOPSLA 2025, Cor. 1: "if a closed, well-typed SL
  program terminates with a value, then its translation in TL also terminates and produces the
  expected result"): for every closed `e` with `J.closed e (.ret A)` at a data `A` that runs to a
  value from the empty memory, there is a fuel beyond which `stageRun "flat" fuel e =
  stageRun "source" fuel e`.
* **`ZeroCost J`**: for every lowering class `c`, every closed `e` of the class (`c.Of e`) with
  reference encoding `e'` (`c.ref e = some e'`), and every fuel at which both run to the end, the
  flat counts of `e` are at most those of `e'`, objects allocated and dispatched calls each.

The missing definitions:

* `stageRun stage fuel e`: a fuel-parametric copy of `Backend.interpStageExpr`;
* `flatCounts fuel e`: runs `Flat.lower p true T` by `callFn` and reads `(allocs, indirect)` from
  the final `FState`;
* `LowClass.Of` and `LowClass.ref`, over `LowClass` below: `answering` (every clause a
  `tailClause`; its reference encoding replaces every `perform (n, i) a` by `c_i a`), `abortive`
  (every operation abortive, a fact about types, so `Of` needs the handler's row; its reference
  encoding returns `inj₂ (i, v)` through each enclosing `let` by a `case`), and `control` (no
  reference encoding until OQ-23 is answered).

The source's reference interpreter must agree with `Steps` on terminating runs (`sourceRun_sound`),
an obligation of `LoweringCorrect`'s proof, not of its statement.  Whether lowering correctness is a
theorem, and the control class's cost model, are OQ-23, which needs the user.
-/

noncomputable section

namespace Targets

/-- The lowering classes: an answering operation (a direct call of its clause on the passed
state), an abortive operation (an early return through a sum, a branch per call), a control
operation (a hand-written state machine). -/
inductive LowClass
  | answering
  | abortive
  | control
  deriving DecidableEq, Repr

end Targets

end
