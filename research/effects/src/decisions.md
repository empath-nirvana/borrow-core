# Decided constraints

These bound the design space. Each is quoted at the strength the user gave it. The full register is `docs/decisions.md` and [`docs/effects-state/04-decisions.md`](../../../docs/effects-state/04-decisions.md).

- **Nothing breaks the borrow calculus** (2026-10-03). "NOTHING CAN BREAK THE BORROW CALCULUS." This concerns the guarantees, not BoLo's text: "You can't add an effect system without changing it. They interact."
- **Multi-shot is ignored as a design goal** (decision 63, 2026-10-04). "TOTALLY IGNORE MULTISHOT AS A DESIGN GOAL. If it works it works, if it doesn't, it doesn't." It never blocks or shapes anything. On friction, the `unr` qualifier is restricted or removed.
- **Effects are core**, on a literature-backed foundation.
- **Row variables are in the kernel** (decision 62).
- **Handlers are deep** (decision 62).
- **Cancellation is what SPEC §19 builds** (decision 62).
- **No step-indexing** (decision 7).
- **Effect handling is erased at runtime.** No function colouring; effects may appear in types.
- **Divergence is an effect** (codata). Totality is not a goal.
- **Errors are a control-flow effect** (`raise`). No API returns a sum for failure.
- **Binary laws are optional** unless safety needs them (2026-10-02).
- **Threads are required eventually.** Keep the door open.
- **Higher-order operations: not now** (decision 57).

## The decided algebra

These are the equations and semantic choices every unit must preserve. A unit may prove them,
restate a target to match them, or report that one does not hold. It may not change them.

- **Handler laws** (deep handlers, Plotkin–Pretnar): a handler's return clause meets `return v`;
  an operation clause meets `op(v)` with the continuation re-wrapped in the same handler; an
  operation of another name passes the handler (forwarding).
- **Algebraicity**: `op(v) to x. P = op(v; y. (k y to x. P))`; an abortive operation absorbs its
  continuation: `raise e to x. P = raise e`.
- **Static per-site names** (SPEC §19, *Names*): an operation reaches the handler site it names;
  no accidental handling.
- **Continuations are linear or affine; `unr` is tolerated, never designed for.** An affine `κ`
  is consumed by exactly one of resume or cancel; a linear `κ` has no cancel.
- **Cancel is not interceptable** (SPEC §19, *Cancels*): the cancelled region's handlers are dead
  and catch nothing; the canceller sees `()`.
- **Finalisers follow `finally`'s law**: `(raise e) then x. N unwind D = D (); raise e`. A
  finaliser's raise of a name handled outside the cancelled region propagates to the live
  handlers, and the canceller sees it as an ordinary raise. A finaliser's raise of a name handled
  only inside the region is a **type error**. Not a runtime seal, not a stuck state. Every
  finaliser runs, so the teardown completes. Which of several finaliser errors wins is a policy,
  not part of the algebra.
- **Deadness is a property of handler frames, not names** (2026-10-08). A cancel kills the
  cancelled region's frames; a dead frame catches nothing — no raise, no operation — so a
  finaliser's effects (raises and ordinary operations alike) reach the nearest *live* instance,
  even when a re-entered site has a dead instance of the same name inside the region. The machine
  never silently drops a finaliser's error; typing guarantees a live handler exists. This replaces
  SPEC §19's by-name suppression (`N`, `errNext`'s middle case) and the lowering's cancel mask.
- **Finalisers may perform ordinary operations** of live handlers, not only raise (2026-10-08).
- **Algebraicity is observed with kept errors' values**; where `unr` continuations get in the way,
  the law is proved at contexts with no `unr` operation (as E5 and E2d), never by observing less
  (2026-10-08).
- **Safety means every operation that is performed or raised has a live handler**. A stuck state
  or a silently dropped error is never a semantics.
- **Effect handling is erased**: tail-resumptive → call, abortive → branch, suspension → state
  machine; zero-size cells cost nothing.
- **Nothing breaks the borrow calculus**, as above.

### Hard stop

Before committing, a unit **stops that step and reports** if its change would:

1. change an equation or semantic choice listed above;
2. change the observable behaviour of an existing kernel or corpus program, or remove one
   (`corpus/kernel-counts.expected`, the corpus goldens), including by making it stuck;
3. add a runtime rule whose job is to block a behaviour (a seal, a stuck state, a suppression)
   instead of a typing rule that excludes it;
4. reject a program that the algebra gives a meaning to, unless a decision records that rejection
   as a deliberate restriction;
5. weaken a target beyond what the decided calculus needs, to make a proof go through.

The report names the law, the change, and the programs affected. The step's work is kept
uncommitted (stashed) and the unit moves on. Restatements that bring a target *into line with*
this algebra are not a stop.
