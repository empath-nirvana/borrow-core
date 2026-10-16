# Async

**Planned: #52** (tracking).

The goal is enough to support a cooperative, tokio-like scheduler without garbage collection or
reference counting, and without WebAssembly-only features.

Already in place:

- A future is codata: polling is one observation of a `delay`, and cancelling is its `close`
  (see [Codata](../codata.md)).
- Cancellation cannot leak: `close` is mandatory, and the checker inserts it for unused futures
  (see [Implicit destructors](../implicit-destructors.md)).
- An executor's run loop is a loop over explicit state.

- `await` is a handler operation, and `lib/async.bc` is a round-robin scheduler with no function
  colouring: a function that awaits is ordinary, and one that takes a block is copied at the
  block's row (see [Effects and handlers](../effects.md), *Async tasks*; SPEC §30;
  `corpus/async-scheduler.bc`, `corpus/async-map.bc`).

Still to come: borrows across `await` (`docs/async-capabilities.md` §3), spawning from a
scheduler handle, cancellation of a task holding a lend, and wakers. Async lowers to stackless
state machines, as Rust's `async` does ([Design decisions](../../decisions.md), 25).
