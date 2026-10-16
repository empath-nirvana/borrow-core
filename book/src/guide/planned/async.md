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

- A task may lend its own cell across `await` (SPEC §29), log to the scheduler, be cancelled while
  it holds a lend, and hold an outer borrow when spawned below it (SPEC §32;
  `corpus/async-logged.bc`, `async-cancel.bc`, `async-scoped.bc`).

Still to come: segmenting a lend at an `await` (L0), an `imm` lend across one, spawning from a
scheduler handle, and wakers. Async lowers to stackless state machines, as Rust's `async` does
([Design decisions](../../decisions.md), 25).
