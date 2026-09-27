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

Still to come: externs and real I/O (#7), effects as borrowed capabilities with `await` as a
handler operation (#18), an executor corpus program, borrows across `await`, and wakers. Async
lowers to stackless state machines, as Rust's `async` does ([Design decisions](../../decisions.md),
25).
