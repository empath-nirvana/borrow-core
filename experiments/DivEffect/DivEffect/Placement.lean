import DivEffect.Plain
import Core.DelayPrograms
import Core.EffBorrow

/-!
# DivEffect — the placement of ticks  (§4.1, unknown 3), and borrows

**The placement** (§3.2): at the empty row, a move forward to a loop's head is an explicit
`tick ()`, and a move back to it is `iterate`'s own tick.  So a `while` whose state is `s₀` and
whose turn is `f` elaborates to

    tick () to n. case n { next → iterate (f, s₀) | close → (f s₀).2 to q. inr q }

and `div_fuel n` of it runs `n` turns, as today's machine (`unfold` of the same step) observed by
`driveE n` does.  `Residual.lean`'s program is this schema (its close returns the cell, which is
`(f c).2`); `Run.lean` runs it against today's machine at `n = 0, …, 6`, with the same answers.

**Not proved** (`sim_loop`, a `sorry`): the simulation, for this one schema.  The design asks for
more: joins, direct-style calls, the row (a generator, whose loops tick only at back edges), and
the same effects in order, not only the same answers.  Each of those needs today's machine for
that schema as a Lean term.  Today's machine is `Frontend/Sugar.lean`'s per-body machine, built
from string templates (`docs/pipeline-architecture.md` §9.2, defect 2), so there is no Lean term
to simulate against beyond this kernel-level schema.  B2 writes the elaboration as typed schemes;
the simulation is then stated over them.

**The programs whose observations are counted**, B2's acceptance:
* `div_fuel`: `corpus/io-fuel.bc`, `lend-lib-each.bc`, `lend-lib-loop.bc`,
  `corpus/sugar/hof-closure.bc`, `hof-local.bc`, `hof-returned.bc`, `surface-defer.bc` (and their
  `.core.bc` pairs), and `lib/div.bc`;
* a stored generator's observations (`U (pull …)`, its skips seen by the consumer):
  `corpus/for-data-div.bc` (`first_two`), `core-yield-pull.bc`, `gen-adapters.bc`,
  `gen-adapters-fail.bc`, `gen-borrowed.bc`, `gen-close.bc`, `gen-div.bc`, `gen-fib.bc`,
  `gen-pipeline.bc`, `gen-tokenize-parse.bc`, `gen-value.bc`, `lend-lib-gen.bc`,
  `lend-pipeline.bc`, `yield-callback.bc`, and the `async-r1-*.bc` programs.

**Borrows** (`tick_not_unwind`): no borrow callback's row holds `tick`.  A borrow's callback is at
an unwind-only row (`Row.Unwind`, SPEC §19), every operation of which is abortive, and `tick` is
linear.  So a tick never stands inside a borrow's scope, and no borrow frame spans a segment
boundary: the frame lemmas are used within one segment, at `ewpTS`, as today.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`tick` cannot cross a borrow**: no unwind-only row holds it. -/
theorem tick_not_unwind (d : UInt32) {S : Row} {x : LifeVar} (hU : Row.Unwind S x) :
    tickSig d ∉ S := fun h => by
  have := (hU _ h).1
  simp [OpSig.abort, tickSig, VTy.isZero] at this

/-- Today's machine for a `while`: `unfold` of the step at the state, observed by `driveE n`. -/
def oldLoop (B R : VTy) (f s₀ : Val) (n : ℕ) : Expr :=
  bindE (.app (.app (.val (unfoldV (CTy.loopBody B R))) (.val f)) (.val s₀)) (driveE n)

/-- The `Div` elaboration of the same `while`, under `div_fuel n`. -/
def newLoop (d : UInt32) (f s₀ : Val) (n : ℕ) : Expr :=
  fuelE d n (.app (.val (.lam (.case (.var 0)
      (.app (.val (iterV d)) (.val (Val.pair f s₀)))
      (.app (.val inrV) (obsC f s₀)))))
    (tickE d))

/-- **The simulation of unknown 3, at the `while` schema**: for every closed step and state and
every `n`, today's machine observed `n` times and the `Div` elaboration under `div_fuel n` reach
the same answers. -/
def SimLoop (d : UInt32) (B R : VTy) : Prop :=
  ∀ (f s₀ : Val), closedAt 0 f.1 = true → closedAt 0 s₀.1 = true → ∀ (n : ℕ) (v : Val),
    (∃ μ, Steps (ℍ := ℍ) Adequacy.emptyMem (oldLoop B R f s₀ n) μ (.val v)) ↔
      (∃ μ, Steps (ℍ := ℍ) Adequacy.emptyMem (newLoop d f s₀ n) μ (.val v))

/-- **Not proved** (`sorry`).  It needs a simulation relation between the two runs: the turn
`(f s).1` runs under different frames (today's `unfold` node and `driveE`'s bind; the `Div`
handler, `div_fuel`'s frame and `iterate`'s turn frame), the same steps at the same memory; between
turns, today's machine takes pure steps, and the `Div` side takes the tick's catch, `κ`'s cell
(allocated, then freed) and `div_fuel`'s counter.  The relation is per configuration of the turn,
as `Runtime.lean`'s invariant is for one handler.  The other schemas and the effects in order need
today's machine as Lean terms (see the module's docstring).  I have not derived this statement,
and I have not verified that any obstruction is real. -/
theorem sim_loop (d : UInt32) (B R : VTy) : SimLoop (ℍ := ℍ) d B R := by
  sorry

end BoCa.Fig16.LogRel.Core.DivEffect

end
