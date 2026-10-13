import Targets.Base.Rows

/-!
# The Instance — A₃ at the backend: the lowering classes (RESTRUCTURE §1.7, §4.5)

A₃ itself (`LoweringCorrect`, `ZeroCost`, over the fixed
target machine and the hand-written equivalents' costs) is A's (`Targets/A/Lowering.lean`).  The
backend erases handling by class: an answering operation becomes a direct call of its clause on the
passed state, an abortive operation an early return through a sum (a branch per call), a control
operation a hand-written state machine.  Named-only; out of the first pass (OQ-23).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

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
