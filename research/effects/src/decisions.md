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
