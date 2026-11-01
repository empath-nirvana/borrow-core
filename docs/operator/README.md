# Design-down: a Kubernetes operator in the language we want

Status: a design sketch. Nothing here is built, and `operator.bc` does not parse. It is not in any
corpus directory, and no gate reads it.

The user decided that the one axis on which this language should be clearly better than Rust is
**function colouring**. Async, errors, generators and other control effects should work through
one mechanism, so that ordinary code and higher-order code (`map`, `fold`, `for`, pipelines,
codecs) work whatever effects are involved. On every other axis, "as good as Rust" is enough.

The method is to design down. We write the program we want (`operator.bc`), then ask whether the
engine can support it (§3). The program is the north star of #67: a Kubernetes operator with
logging and everything else a real one has.

| file | what |
|---|---|
| [`operator.bc`](operator.bc) | the operator in the ideal syntax, with the library interfaces it uses and its tests |
| [`memcached.rs`](memcached.rs) | the same operator in Rust with kube-rs, written for the comparison, with `// COLOR:` at every coloured spot |
| this file | the goals, a walkthrough, the side-by-side, the gap analysis and the path |

Contents:

- §0 The operator chosen, and its references
- §1 The experience goals
- §2 The one mechanism
- §3 A walkthrough of `operator.bc`
- §4 Side by side with kube-rs
- §5 Gap analysis
- §6 The minimal ordered path
- §7 Surface hypotheses and alternatives

## 0. The operator, and its references

**The operator-sdk "Memcached" tutorial operator**, extended to kube-rs's controller feature set.
It is the best-known small operator, and it has implementations in Go and Rust to compare with.

- **Behaviour.** The Go tutorial is the reference: operator-sdk,
  `testdata/go/v4/memcached-operator/internal/controller/memcached_controller.go`
  (https://github.com/operator-framework/operator-sdk). The custom resource is
  `cache.example.com/v1alpha1` `Memcached`, with `spec.size` and `spec.containerPort`. The
  operator does these things:
  - it owns a Deployment with `replicas = size`;
  - it writes `Available` and `Degraded` status conditions;
  - it keeps a finalizer, `cache.example.com/finalizer`, and on delete it records an event, sets
    `Degraded` and then removes the finalizer;
  - it reads the image from `MEMCACHED_IMAGE`.
- **Rust.** kube-rs has no Memcached example. `memcached.rs` is the same operator written with
  the kube-rs APIs of three references, each checked against kube-rs `main` (the `kube` 4.x line):
  - `examples/configmapgen_controller.rs` for the controller, `owns`, apply, concurrency and
    `shutdown_on_signal`;
  - `examples/secret_syncer.rs` and `kube-runtime/src/finalizer.rs` for the finalizer helper;
  - `kube-rs/controller-rs` for status, events, the error policy, metrics, and the mock API
    server in `src/fixtures.rs`.

  Leader election is not part of kube-runtime. `memcached.rs` uses `kube-lease-manager`, the
  commonly used crate.
- **Features covered**, and where each one is in `operator.bc`:

  | feature | where |
  |---|---|
  | list + watch with resync and reconnect | `watcher` (§1.6) |
  | reconcile creating and updating a Deployment | server-side apply (§2.4) |
  | status updates | `apply_status`, `set_condition` |
  | finalizers | `apply_memcached` step 1 and `finalize` |
  | structured logging with spans | §1.1 |
  | errors with retry and backoff | `retry`, `call`, `reconcile_key` |
  | timeouts and cancellation | `timeout`, `race` |
  | concurrent reconciles with a bound | `run_controller`, `for_each_concurrent` |
  | graceful shutdown on SIGTERM | `terminated`, `take_until`, the drain in `run_controller` |
  | configuration from env and args | `parse_config` |
  | leader election | `while_leader` |
  | metrics | `Metrics`, `serve_metrics` |
  | pipelines | `triggers`, `watch` |
  | streaming I/O | response bodies, the watch stream, log output |
  | data transformation | `desired`, `set_condition`, `diff`, `merge_patch` |
  | serialization | `derives Json`, the pull parser over any byte source |
  | tests | Part 3 |

## 1. The experience goals

Each design choice in `operator.bc` is tagged with the goals it serves. Two notes go with the tags:

- `not-think:` names what a reader may ignore;
- `types-tell:` names what the types still show.

| | goal | the reader does not think about | the types still tell |
|---|---|---|---|
| **G1** | One function for every context. | async or sync; which runtime; `.await`; `Pin`; `Send` | the inferred effect row: `Async` means it may wait |
| **G2** | Failure is handled where it is handled. | `?`, `map_err`, `From` impls at each call | `Fail<E>` in the row, with its `E` |
| **G3** | Cleanup is automatic on every exit: return, raise, timeout, cancellation, shutdown. | which exit paths close which connection; async `Drop` | which values have destructors (SPEC §12) and which must be handed back |
| **G4** | Ambient services (log, clock, metrics) reach code without being threaded through it. | passing a logger or a context struct everywhere | `Log`, `Clock` and `Metrics` in the row |
| **G5** | Tests replace the world by handlers. | mocking traits, dependency injection, paused runtimes, real time | which effects a test must handle (the row of what it calls) |
| **G6** | A stream is an iterator. | `Stream` vs `Iterator` vs `TryStream`; `StreamExt` vs `TryStreamExt`; `boxed()` | the element type, and the effects of `next` |
| **G7** | A codec is derived once per type and runs over any byte source. | `from_slice` vs `from_reader` vs an async codec; buffering whole bodies | the source's row, plus `Fail<JsonError>` |
| **G8** | Cost stays readable, as good as Rust. | nothing: see the right-hand column | `box` allocates; `{ … }` suspends; a copy per effect set; `total` promises no effect |
| **G9** | Concurrency is structured. | `Arc`, `'static`, forgotten `JoinHandle`s | lifetimes; a task cannot outlive its scope |

## 2. The one mechanism

This section is the design's thesis, stated so that it can be checked against the engine in §5.

**Every effect is declared the same way and handled the same way.** An `effect` declares
operations; a `handler` implements them; `with h { … }` installs one for a block. A function's
effects are **inferred**, as divergence is today (SPEC §14), so a signature needs no annotation.
An effect row that is written, as in `-> T / {Fail<E>}`, is a checked promise, like `total`.
Operations come in two kinds, told apart by what the handler must do.

1. **Answering operations**: `Log.emit`, `Clock.now`, `Metrics.inc`, `Http.send`. The handler
   returns a value and the caller continues.
   - They are the capabilities of decision 30, passed implicitly. This is the `needs`/`provide`
     elaboration of PR #100, `KDem`: the caller of a function provides what it needs.
   - The strict account (branch `coeffects-strict`, §2.4) shows that a threaded `Mut` capability
     *is* the algebraic effect, by Møgelberg–Staton, so no second mechanism is needed.
   - They cost a direct call.
2. **Control operations**: `raise`, `yield`, `wait`. The handler may resume the caller never,
   later, or somewhere else. They change the **computation type** of every function that
   performs them, and that is the part that colours functions in other languages. Each one is a
   shape of the one codata former the core already has:
   - `Fail<E>`: the result is `F (B + E)`. `raise` is an injection, and unwinding is the implicit
     destructors (SPEC §12).
   - `Yield<T>`: the result is `U (iter T B K)`. A generator is `unfold` (SPEC §7, decision 25).
   - `Async`: the result is `U (iter Wait B K)`. A task is an iterator of what it waits for, and a
     scheduler is its consumer. This is #52's "a future is codata", with the yield type made
     explicit.
   - Divergence, which exists today, is `U (loop B K)`, which is `iter 1 B K`.

   Combined, they sum: `Async` together with `Yield<T>` is `iter (Wait + T) B K`. That is Rust's
   `Poll<Option<T>>`, which is why no separate `Stream` type is needed.

**Nothing is written twice, because nothing is compiled once.** A higher-order function (`map`,
`retry`, `decode`, `reconcile` itself) is specialized at the computation types of its callback,
iterator and handler arguments. SPEC §14 does exactly this for divergence today, and it names the
three things each further effect must supply:

- a computation type;
- an inference rule;
- an elaboration of a body and of a call.

The copy of `map` over a pure `Vec` is a plain loop. The copy over a watch stream is a state
machine that fails and suspends. The test's copy of `reconcile` answers from an in-memory API
server. All of them come from one source. This is whole-program monomorphization (decision 8),
with the cost Rust's generics already have: one copy per instantiation. There is no effect
polymorphism in the core.

**Who handles what.**

- A function's answering effects are provided by its caller, like implicit parameters.
- A closure or an iterator captures the providers in scope where it is made.
- A control effect goes to whoever *runs or observes* the computation:
  - a `raise` goes to the `try` around the observation;
  - a `wait` goes to the scheduler, `race` or `timeout` that is driving the task.

  This is why `timeout` can cancel a read performed by a body stream that the HTTP handler made.
  It is also the codata reading: a suspension is yielded to the observer.

**Cancellation is not resuming.** A handler that does not resume its continuation abandons it.
A timeout, a lost `race`, shutdown and a raise all unwind the same way: the destructors run, the
borrows end, and whatever has no destructor goes back in the residual (SPEC §14). So G3 has one
mechanism, not four.

**Shared mutable state lives in a handler, not in a lock.** Consider the metrics registry, the
log sink and the HTTP pool:

- each is owned by the handler that implements its effect;
- tasks reach it through operations;
- the cooperative scheduler runs one answering clause at a time.

There is no interior mutability. The price is a rule for handler authors: **a clause that touches
shared state does not suspend**. So `http_client` checks a connection out of the pool in one
step, and then does the waiting on the connection, which the task owns. Whether the engine can
deliver this is obstacle O2 (§5.2).

## 3. Walkthrough of `operator.bc`

**Part 1, the library.**

- **§1.1 Effects.**
  - `Fail`, `Yield` and `Async` are built in, handled by `try`, `generate` and `block_on`/`scope`.
  - `Log`, `Clock` and `Metrics` are declared in the library. Each has a production handler:
    - `json_lines` writes one JSON object per line to `stderr`;
    - `system_clock`'s `sleep` is a `wait` on a deadline;
    - `prometheus` owns the registry.
  - Log fields are any value with a JSON codec, usually a record literal:
    `info("applying deployment", &{ change: &patch })`. The logger's structure and the codec's
    structure are therefore the same thing.
  - `span` is a handler of `Log` that forwards to the outer one.
- **§1.2 Iterators.**
  - There is one `Iter`. `map`, `filter` and `filter_map` are three-line generators, written once.
  - `merge`, `debounce`, `batch`, `take_until` and `for_each_concurrent` are interfaces.
- **§1.3 Time.** `timeout` is `race(body, { sleep(d) })`.
- **§1.4 JSON.**
  - The `Json` interface is what `derives Json` provides. The generated code for `MemcachedSpec`
    is shown: a loop over keys that pulls bytes from its source.
  - The source is an `Iter<Bytes, R>`. Decoding from a `Vec` in a test and from a chunked socket
    body mid-watch is the same function.
  - `merge_patch` (RFC 7386) and `diff` are total folds over `Value`.
- **§1.5 HTTP** is an effect with one answering operation, `send`. The response body is an
  iterator of chunks, and dropping it closes the connection. `http_client` is the real handler.
- **§1.6 The Kubernetes client.**
  - `get`, `apply`, `apply_status`, `json_patch`, `list` and `watch` are ordinary functions over
    `Http`.
  - `watch` is a generator over the body's lines. `watcher` is kube-runtime's `watcher`: list,
    watch, relist on `410 Gone`, back off on error, and emit `Resync` after each list.
- **§1.7 `retry`** takes a `fn` body, which it may call several times, and a predicate for which
  failures to retry. It sleeps between attempts with `Clock`.
- **§1.8 Tasks.** `scope` is the scheduler, `race` closes the loser, and `for_each_concurrent` is
  a bounded pool.
- **§1.9 `run_controller`** is kube-runtime's `Controller`:
  - the queue lives in one loop;
  - there is at most one reconcile per key at a time;
  - requeues are timers;
  - triggers are debounced;
  - on shutdown it drains, with a grace period.

**Part 2, the operator.**

- **§2.1 Types.** `Memcached` derives `Json` and `Resource`. `DeploymentScale` decodes only the
  replica count and ready count we read, and unknown fields are skipped.
- **§2.2 `parse_config`** reads borrowed views of `args` and `env`. Its only effect is
  `Fail<ConfigError>`.
- **§2.3 `desired`** is a `total fn` from the custom resource to a `DeploymentApply<'a>` made of
  borrowed views of the resource and the config. Building it copies no string, and it is encoded
  straight into the request. `set_condition` is `meta.SetStatusCondition`.
- **§2.4 `reconcile`** does the tutorial's steps in order:
  1. get the custom resource;
  2. validate it;
  3. branch on the deletion timestamp;
  4. add the finalizer, then apply the Deployment (logging the `diff` when it changes), then
     apply the status;
  5. or `finalize`.

  Every API call goes through `call`, which is `retry` of `timeout` of the call, with
  `KubeError` mapped once to `ReconcileError`. Its inferred row is
  `{Http, Clock, Async, Log, Metrics, Fail<ReconcileError>}`; nothing in the body names `Http`,
  `Clock` or `Async`.
- **§2.5 `reconcile_key`** holds the only `try` in the operator: log, count, and requeue with
  backoff. The failure count is an argument owned by the controller's queue. A `&mut Map` captured
  by the callback would be rejected by the borrow checker, since up to `concurrency` calls run at
  once.
- **§2.6 `triggers`** is the controller's input, as a pipeline:

  ```
  merge(from_crs, from_deps) |> take_until(stop) |> debounce(1.s, trigger_key) |> inspect(…)
  ```

  `from_deps` maps an owned Deployment's events to its owner, as `owns` does. `while_leader`
  races the controller against lease renewal. `serve_metrics` answers `/metrics` through the
  `Metrics` operation `render`.
- **§2.7 `main`.**
  - It holds the capabilities and chooses the four handlers once.
  - It runs `race(serve_metrics, controller)`. SIGTERM ends the trigger stream, the controller
    drains, and then the metrics server is abandoned and its listener closes. The shutdown order
    follows from the program's structure.

**Part 3, the tests.** Each test is the production function under other handlers:

- `fake_apiserver`, an `Http` handler over an in-memory store with fault injection;
- `simulated`, which runs virtual time: when everything waits on a deadline, time jumps to it;
- `capture_logs` and `no_metrics`.

There are five tests:

- the first reconcile adds the finalizer, and the second creates the Deployment and the status.
  The exact request sequence is asserted, and no time passes;
- two `503`s are retried with backoff. The test asserts the sleeps, `[100ms, 200ms]`, and that
  virtual time ends at 300 ms;
- a failing reconcile is requeued with a backoff that grows with the failure count;
- a slow body times out, is retried four times, and every cancelled body is closed. The test
  asserts `open == 0` and the exact virtual time;
- the watcher relists after `410 Gone`.

## 4. Side by side with kube-rs

`memcached.rs` marks each coloured spot with `// COLOR:`.

### 4.1 Async functions

**Rust.** `async fn reconcile`, `async fn apply`, `async fn cleanup`. `#[tokio::main]` fixes the
runtime, and everything under it is tied to that runtime. The context is
`Arc<Ctx>: Send + Sync`, and the reconciler future must be `Send + 'static`, so it cannot borrow
from `main`. `error_policy` is a *sync* callback, so it cannot await anything.

**Ours.**

```
fn reconcile(cfg: &Config, key: &ObjectKey) -> Action =
```

There is no marker. The same function runs in three ways:

- under the scheduler, where the copy is a state machine;
- under `block_on`, where the copy blocks in `wait`;
- in a test, where the copy's only suspensions are simulated sleeps.

The config is borrowed (`&Config`), because tasks live inside a scope (G9).

### 4.2 Error handling

**Rust.**

- `.await?` on every call. `#[from] kube::Error` and
  `.map_err(|e| Error::Finalizer(Box::new(e)))` wrap errors.
- `finalizer`'s error type wraps ours, so the result is mapped twice.
- `try_fold` and `TryStreamExt` are a second adapter family for fallible streams.

**Ours.**

- A call that may fail is just a call. The error type is converted once per region:
  `fn kube<T>(body) = map_err(ReconcileError::Kube, body)`.
- The only `try` is in `reconcile_key`. The error policy is ordinary code in the same effect
  world: it logs, counts and computes the backoff.
- The same `fold` works over a fallible iterator.

### 4.3 Retries

**Rust.**

```rust
async fn retry<T, F, Fut>(timeout: Duration, mut body: F) -> Result<T, Error>
where F: FnMut() -> Fut, Fut: Future<Output = Result<T, kube::Error>>
```

This helper serves async callers only. Each call site wraps its request in `|| deps.get_opt(&name)`.

**Ours.**

```
fn retry<T, E>(policy: Backoff, max: i32, retryable: fn(&E) -> bool,
               body: fn() -> T / {Fail<E>, ..}) -> T / {Fail<E>} =
```

One `retry` serves every caller. It sleeps through `Clock`, so in a test the sleeps are virtual
and observable.

### 4.4 Cancellation and timeouts

**Rust.**

- `tokio::time::timeout` works only for futures.
- Dropping a future at an `.await` cancels it, but there is no async `Drop`. Cleanup that needs
  I/O, such as removing a finalizer or telling the server, cannot run on cancel.
- The finalizer helper documents this: the object may be reconciled again.

**Ours.**

- `timeout(d, body)` is `race(body, { sleep(d) })`, and the loser unwinds like a raise.
- A connection is a value with a destructor. Every exit closes it: `return`, `raise`, timeout,
  shutdown.
- The fourth test asserts it (`open == 0`).
- What is still open is a destructor that must *perform* I/O and can fail (SPEC §12 Open; §5,
  N6).

### 4.5 Logging

**Rust.**

- `tracing` is ambient: a global subscriber and task-local spans (`#[instrument]`).
- It is convenient and invisible in types.
- A span does not follow a spawned future unless `.instrument(span)` is attached.

**Ours.**

- `Log` is an effect. The handler chosen in `main` is `json_lines(&mut stderr, level)`, and no
  function in between takes a logger.
- `Log` appears in the inferred row, so a function whose row lacks `Log` provably does not log.
  This is the frame theorem of decision 30.
- `span` is a handler of `Log` that adds fields and forwards. Tasks spawned inside a span are
  inside it lexically.

### 4.6 Tests

**Rust**, from controller-rs's fixtures:

- `tower_test::mock::pair`, then `Client::new(mock_service, "default")`, then a second task that
  answers requests in order;
- `#[tokio::test(start_paused = true)]` to control `tokio::time`, which does not cover anything
  that reads the system clock;
- asserting on the retry backoff means asserting on the elapsed paused time.

**Ours.**

```
simulated(&mut t, &mut slept, {
  with fake_apiserver(&mut st), capture_logs(&mut logs), no_metrics() { reconcile(&cfg, &key) }
})
```

- There is no trait, no DI and no runtime. The fake is an ordinary handler over a `Store`.
- The test asserts the exact request list, the exact sleeps and the exact virtual time.

### 4.7 Pipelines

**Rust.**

- `Controller::run(..)` returns a `Stream`, consumed by `StreamExt::for_each(|res| async move {…})`.
- A watch is `api.watch(..).await?.boxed()`, folded with `TryStreamExt::try_fold`.
- The same logic over a `Vec` uses `Iterator`, another trait with another adapter set.
- Async closures in adapters (`filter_map(|x| async move {…})`) are their own idiom.

**Ours.**

```
let events = resp.body |> chunks |> lines
  |> map(|line| map_err(KubeError::Decode, { decode_str::<WatchEvent<K>>(&line) }));
```

The stages mix effects: the body waits and fails, `lines` is pure, and the `map` fails. They are
the adapters a test runs on a `Vec<u8>`. `triggers` adds `merge`, `take_until`, `debounce` (which
waits) and `inspect` (which counts).

### 4.8 Serialization

**Rust.**

- serde has no deserializer over an async reader.
- kube's watch frames each line into a buffer and calls `serde_json::from_slice`.
- Streaming from a socket means framing first, and that is a different path from
  `serde_json::from_reader` over a blocking `Read`.
- k8s-openapi types own every field, so building a Deployment clones each string.

**Ours.**

- `derives Json` generates a pull parser over any `Iter<Bytes, R>` (shown for `MemcachedSpec`).
  The source's effects become the decoder's.
- A type that decodes only what it reads (`DeploymentScale`) skips the rest.
- The value we encode, `DeploymentApply<'a>`, is made of views into the custom resource.

### 4.9 What ours still shows

- Effects are in types, inferred.
- `box` marks allocation, and `{ … }` marks a suspended block.
- Lifetimes on views (`'a`) are written.
- `total` is written on pure helpers.
- Suspension *inside* a function is not marked at call sites. Draft 0 marks it only at the
  operation (`suspend gen.yield(x)`, `docs/surface-cbpv.md` §2.11), and `operator.bc` never
  performs `wait` outside the library. `bcc` and an editor can show where a copy became a state
  machine. §7 lists the alternative.

## 5. Gap analysis

Each feature is classified as one of:

- **(a) today**: supported now;
- **(b) planned**: a named issue or stage covers it;
- **(c) new design**: a precise open question.

Obstacles in the engine, O1 to O6, are in §5.2, each with the pending corpus program or the rule
behind it.

### 5.1 Feature by feature

| feature | used at | status | notes |
|---|---|---|---|
| ownership, `&`/`&mut` lends, `let mut`, `if`, `match` | everywhere | **(a)** | decisions 37–38 |
| div inferred; `total fn` checked | `watcher` loops forever; `total fn desired` | **(a)** | SPEC §14 |
| `for` over any iterator a function returns | `for line in …`, `for ev in watch(…)` | **(a)** | `corpus/axes/codata-effects.bc` |
| specialization of a HOF at a div callback | the model for all effects | **(a)** for div at parameter types | SPEC §14; stored callbacks excluded (O3) |
| a capability lent per step inside a loop | the sequential operator's `&cfg` per reconcile | **(a)** | `corpus/axes/scope-loop-lend.bc` |
| an iterator holding a borrow across a scope | body and parser views | **(a)** in core | `corpus/axes/scope-boxed-iter.bc` |
| `data` with named fields, constructors, patterns, `box` | every type | **(b)** stage 8 | also needed: type parameters (`Option<T>`, `Api<K>`), values without `box` (strings design Q5), lifetime parameters (`DeploymentApply<'a>`) |
| `fn f<'a>` | `desired<'a>`, `parse_config<'a>` | **(a)** surface | `corpus/fn-lifetime.bc` |
| finite `for`, total | `for (k, v) in p.iter()` in `merge_patch` | **(b)** stage 9 / strings S4 | `pending/for-finite.bc` |
| `u8`, slices, `buf`, `string`, `str 'a`, `lit`, `write_all` | text, JSON, HTTP, logs | **(b)** strings S1–S5 | `docs/strings-slices-design.md` |
| `i64`, `f64`, duration literals | `Duration`, histogram values | **(b)** i64 exists (#80); **(c)** `f64` and literal suffixes | small |
| `Vec`, ordered `Map`, `Set` | labels, JSON objects, queue | **(b)** `buf` (S5), #64 | |
| `|>` | pipelines | **(b)** #59, #17 | elaboration only |
| iterator adapters (`map`, `filter`, `merge`, `take`, …) | §1.2 | **(b)** #48 | written as generators they need `Yield` |
| closures capturing `i32`s and `imm` borrows, called many times | `retry(…, \|\| get(&api, &name))`, `for_each_concurrent` | **(b)** #9, #58; **(c)** for `imm` | O6 |
| a callback inside a fold's algebra | `diff`'s `filter_map`, `merge_patch`'s map | **(c)** | O4, `pending/map-div-fold.bc` |
| `Fail<E>`: `raise`, `try`, `map_err`, `return`, `break` | `reconcile`, `retry`, codecs | **(b)** #18; **(c)** unwinding | O5, `pending/raise-in-fold.bc` |
| `effect`/`handler`/`with` for answering operations | `Log`, `Clock`, `Metrics`, `Http` | **(b)** PR #100 (`needs`/`provide`); **(c)** handler records | O3 |
| `Yield<T>`, `generate` | `watch`, `watcher`, adapters | **(b)** #18 | `pending/generator-handler.bc`; no kernel change |
| `Async`: `wait`, `block_on` | all I/O | **(b)** #52 | `block_on` needs no state machine |
| `scope`, `spawn`, `race`, bounded concurrency | `run_controller`, `main`, `timeout` | **(b)** #52; **(c)** | O1, O2 |
| simulated time (a deterministic scheduler) | tests | **(b)** with #52 | library code once `race` exists |
| `derives Json`, `derives Resource`, `@json("…")` renames | every API type | **(c)** | N8 |
| an `interface` for `T: Json` and `K: Resource` | `decode<T: Json>` | **(c)** | N8: decision 8 re-checks generics, but has no overloading on `T` |
| `Args`, `Env`, `Clock`, `Signals`, `Net` capabilities | `main` | **(b)** SPEC §11 "Designed", #66 | `Signals` is new but follows the same pattern |
| TLS; service-account token and CA | in-cluster `http_client` | **(b)** #67 step 5 | host or FFI boundary (decision 27) |
| a destructor that performs I/O | `Conn`, `Listener`, `Body` | **(c)** | N6, SPEC §12 Open |
| multi-shot continuations | not used | none | `retry` re-runs a `fn`, not a continuation |

### 5.2 The obstacles in the engine

Each obstacle names what blocks it and how the operator meets it.

**O1. A loop inside a borrow scope** (`corpus/pending/borrow-across-loop.bc`).

- **Where it blocks.** A borrow block's body is one `F` computation. A div or async body returns
  a loop, which cannot leave the scope that holds its borrow. `withbor` is a scoped,
  non-algebraic operation (strict account §4).
- **Where the operator meets it.** Concurrent tasks borrow `&cfg` for the whole life of the
  scheduler loop (`run_controller(…, |key, n| reconcile_key(&cfg, key, n))`).
- **Where it does not.**
  - A `with h(&mut state) { … }` around a loop, if the elaborator treats the handler's state as
    *owned and handed back*: moved in, then returned in the loop's residual. That is the
    move-and-rebind lend of decision 38 and the residual of SPEC §14.
  - The sequential operator: it lends `&cfg` per reconcile, which works today
    (`scope-loop-lend.bc`).
- **Closed by decision 71** (`docs/tombstones/lends-across-suspensions.md`): no borrow block spans
  observations. The tasks are lent `&cfg` from outside a scheduler that runs inside the borrow
  (`spawn_in`/`run_in`, SPEC §32), or get copies; the sequential operator lends per reconcile.
- **The question (as asked).** Should the kernel have a borrow block at loop type, whose frame spans every
  observation? The pending file sketches its type:
  `Ref A ⊸ (∀'x. Mut 'x A ⊸ U (Loop (['x] B) R)) ⊸ U (Loop (Ref A ⊗ B) (Ref A ⊗ R))`.
  Its soundness is the frame (6.64) held across a sequence of observations, which the typed
  world does not state. The alternative is a per-step lend (O2's route).

**O2. Several interleaved tasks using one mutable capability** (`corpus/pending/two-writers.bc`).

- **Where it blocks.** `Mut ⊸ Mut ⊗ Mut` is not a rule.
- **Where the operator meets it.** Up to `concurrency` reconciles each use `Log` (the log sink),
  `Metrics` (the registry) and `Http` (the pool). They never run at the same instant, but each
  suspended task would hold the borrow.
- **Two routes.** Both need one kernel item, **issue #96, codata observations that take input.**
  - **(i) Per-step lend.** A task's `next` takes the shared capabilities for one step:
    `νX. ∀'x. Mut 'x Caps ⊸ F (['x] (Wait ⊗ U X ⊕ B))`.
  - **(ii) Operation forwarding.** A task yields the operation as data to the scope, and the
    scope's handler runs it and resumes the task *with the result*. Unit-result operations
    (`emit`, `inc`) need no input. `Http`'s pool checkout returns a connection and does.
- **Kept small by two choices.**
  - `wait` returns nothing: a woken task retries its read, as a Rust future re-polls. So plain
    suspension needs no input.
  - Handler clauses that touch shared state do not suspend (§2).
- **The question.** Is #96's input observation sound at a lifetime-polymorphic input? The
  question is `∀'x` in an observation of `ν`. SPEC §7 restricts `ν`'s body to observations
  ending in `F A`, with `U X` only under `⊗`/`⊕`. A `∀'x. Mut 'x Caps ⊸ …` observation is outside
  that class.

**O3. Effects of callbacks stored in data** (`corpus/pending/callbacks-in-data.bc`; typed
elaboration decision 6).

- **Where it blocks.** Specialization instantiates effects only at *parameter* types. A callback
  stored in a record keeps its written effect.
- **Where the operator meets it.** A handler value is such a record: `http_client`'s `send`
  performs `Async` and `Fail<HttpError>`, and `fake_apiserver`'s does neither. `reconcile` must
  be specialized at the effects of the handler record's fields, and an iterator's `next` at its
  producer's effects. The `Body` that `send` returns is codata whose effect the *handler* chooses.
- **The questions.**
  - Does specialization extend to the fields of a *known* record argument, and to the
    observations of an iterator argument, by the same keying by (function, instantiation)?
  - Must an effect signature whose operation returns codata (`send -> Response` with a streaming
    `Body`) be parameterized by the handler's row? That is Effekt's and Koka's answer: an effect
    parameter on the signature.

**O4. A callback inside a fold's algebra** (`corpus/pending/map-div-fold.bc`).

- **Where it blocks.** The algebra is a `!` closure that the fold requires to be total, and a
  call of an effectful callback inside it is not elaborated.
- **Where the operator meets it.** `diff` and `merge_patch` fold over `Value` with callbacks,
  total here. The effectful case is any `map` over a list whose callback logs or fails.
- **The question** is from the pending file. The fold's `R` would be the effect's computation
  type, `U (loop …)` for div or `F (R + E)` for failure, sequenced by the effect's bind.
  Elaboration only, for the whole-program case.

**O5. Unwinding** (`corpus/pending/raise-in-fold.bc`).

- **Where it blocks.** `raise` abandons the rest of the computation:
  - in `fold_own`, the frames above own cells that must be freed;
  - in `fold_imm`, a borrow must end.
- **Where the operator meets it.** Every raise under a borrow (`call(cfg, || get(&api, …))`), and
  every cancellation (§2: cancellation is not resuming).
- **The questions.**
  - What happens to a live value with no destructor (a capability, a thunk, SPEC §12 group 3)?
    Either raise is illegal while one is live, or the handler receives it with the error, as
    `close` hands back a residual. The operator's capabilities live in handlers, not in bodies,
    so a body holds only borrows of them, and a borrow just ends. That makes the second answer
    workable.
  - A fold raises at the *last* bad element in list order (the pending file). Is that acceptable?

**O6. Closures that capture and are called many times** (#9, `pending/closure-captures-int.bc`;
#58).

- **Where it blocks.** A `!` closure captures only `!` values: not an `i32`, not an `imm` borrow.
- **Where the operator meets it.** `retry`, `for_each_concurrent`, `filter`/`map` callbacks and
  `call(cfg, || get(&api, &name))` all capture a borrow and are called more than once.
- **The question.** Is an `imm` borrow persistent enough to be captured by a many-use closure?
  It is copyable (`copy`), but not `!`. #9 widens promotion to persistent contexts, and #58 makes
  `imm` copies implicit.

### 5.3 New design, stated as questions

- **N1. Effect rows at the surface.**
  - Are written rows (`/ {Fail<E>, ..}`) needed at all outside library HOFs, or is inference
    plus `total` enough?
  - What is the row variable `..` in a library signature? The core has none, so `..` means
    "specialize here".
- **N2. Handler binding.** "Answering effects: provided by the caller or captured by a closure;
  control effects: to the observer" (§2). Is that one rule the elaborator can state, and does it
  agree with PR #100's `KDem`?
- **N3. `Async` as `iter Wait`.**
  - Is a task's computation type `iter Wait B K`, with a scheduler as an ordinary consumer?
  - Is `race` library code over two such iterators?
  - Or does #52 need a primitive?

  No kernel change is apparent. The runtime needs a host `poll` over an interest set (#52
  phase 6), with no wakers and no interior mutability, since the scheduler maps readiness to its
  own task slots.
- **N4. Homogeneous task pools.**
  - `for_each_concurrent` keeps `n` tasks of one computation type at one lifetime, so no
    existential lifetimes are needed (the `async-borrow.bc` question).
  - Is that enough, with heterogeneous spawning only through `race` and nesting?
  - The operator needs nothing more.
- **N5. `return` and `break` as `Fail`** with a private error, handled at the function's or the
  loop's boundary. SPEC §11 Open notes that `for` has no early exit today.
- **N6. Destructors that perform I/O.** `Conn` and `Listener` must close sockets on every exit.
  - Is a host resource's destructor an extern with a contract?
  - What does a failing close do: ignore, as Rust's `Drop for TcpStream` does, or report to
    `Log`?

  This is SPEC §12 Open.
- **N7. `Metrics.render(out: &mut Buf)`.** An answering operation that lends the *caller's*
  buffer to the handler: is that `needs` with a borrowed argument?
- **N8. Derivation.** How does `T: Json` find `T`'s codec?
  - (i) A `derives` that generates `decode_T`/`encode_T` and an `interface` resolved by
    monomorphization. The generics of decision 8 can call a named function per `T`, but have no
    overloading.
  - (ii) Type-directed elaboration of the codec from the *structural* type (decision 9: types
    are structural), with field names carried as labels. That needs named fields in the core or
    a side table.

  Either is elaboration, not kernel. Choosing between them is a design decision.

## 6. The minimal ordered path

The observation that shortens the path: **a correct operator does not need concurrency.**

- A single task can watch, reconcile inline, requeue by deadline, and shut down on SIGTERM.
- `block_on` implements `wait` as a host `poll` on the socket and the signal fd, with the next
  requeue deadline as the timeout. That is a blocking call, with no state machine, no scheduler,
  and no O1 or O2.
- kube-rs's controller without `owns` converges through requeues, and so does this one.

So steps 1–7 reach a real operator on a real cluster, and steps 8–10 recover the full
experience. Each step is justified by lines of `operator.bc`.

1. **Surface basics.**
   - The work:
     - stage 8 `data`/`box`, with type parameters, values without `box`, lifetime parameters and
       named fields;
     - `fn f<'a>`;
     - stage 9 finite `for`;
     - `|>` (#59);
     - closures capturing `i32` and `imm` (#9, #58; O6).
   - Justified by every type in §2.1 and §2.3, `desired<'a>`, `merge_patch`'s `for`, and
     `retry(…, || get(&api, &name))`.
2. **Bytes and text**, strings S1–S5.
   - The work: `u8`, slices, `buf`, `string`, `lit`, `write_all`/`read_into`.
   - Justified by every string in `ObjectMeta`, `get_req`, `json_lines`, and the `chunks |> lines`
     of `watch`.
3. **Errors**, #18's first slice.
   - The work:
     - `Fail<E>` as the computation type `F (B + E)`, through SPEC §14's three hooks;
     - `raise`, `try`, `map_err`, `return`, `break` (N5);
     - unwinding by destructors, including through folds (O4, O5).
   - Justified by `reconcile`'s early `return AwaitChange`, `raise(ReconcileError::Invalid …)`,
     `reconcile_key`'s `try`, `parse_config`, and the codecs' `JsonError`.
4. **Collections and JSON.**
   - The work: `Vec`, ordered `Map`/`Set` (#64); `Value`, the pull parser and writer over an
     `Iter<Bytes>`; `derives Json` (N8), #65.
   - Justified by `labels`, `set_condition`, `diff`, `merge_patch`, and `decode` in `get` and
     `watch`.
5. **Answering effects.**
   - The work:
     - `effect`/`handler`/`with` as `needs`/`provide` (PR #100);
     - handler state owned and handed back around loops (O1's way out);
     - specialization over a handler record's fields (O3);
     - `Log`, `Clock`, `Metrics`, `Http` as library effects.
   - Justified by `info(…)`/`warn(…)` with no logger parameter, `sleep` in `retry`,
     `send` in `get`, and `main`'s `with json_lines(…), system_clock(…), …`.
   - **Milestone:** Part 3's first three tests run under `bcc interp` and wasm, with a fake API
     server and a virtual clock whose `sleep` just advances time. No async is needed.
6. **Host capabilities and blocking I/O.**
   - The work:
     - `Args`, `Env`, `Clock`, `Signals` (a signal fd) and `Net` (blocking TCP, #66), following
       the SPEC §11 pattern;
     - `wait` as a blocking host `poll` over an interest set (`block_on`);
     - destructors for sockets (N6).
   - Justified by `parse_config(&args, &env)`, `terminated(&mut signals)`, `http_client(&mut
     net, …)`, and `bind`.
7. **A sequential operator on a real cluster.**
   - The work:
     - the HTTP/1.1 client with chunked decoding, the Kubernetes client, and `watch` as an
       iterator over the body's lines;
     - `reconcile` inline after each event;
     - requeue by `poll` deadline;
     - SIGTERM by `poll` on the signal fd;
     - plain HTTP to `kubectl proxy` on a kind cluster (#67 steps 1–3).
   - Justified by all of Part 2 except `run_controller`'s concurrency, `race`, `while_leader` and
     `serve_metrics`.
   - `watcher` can be written as an `Iter` by hand (`unfold`) before generators exist.
   - **Milestone:** the operator creates, scales and finalizes a Memcached on a real cluster.
8. **Deployment in-cluster.**
   - The work: TLS, the service-account token and the CA, through a host or FFI boundary
     (decision 27, #67 step 5); a container with wasmtime and WASI sockets, or native code later
     (#21).
   - Justified by `Endpoint::in_cluster(env)`.
9. **Generators and the adapter library.**
   - The work: `Yield`/`generate` (`pending/generator-handler.bc`, #18) and #48's adapters,
     specialized over effectful iterators (O3's iterator half).
   - Justified by `watch`, `watcher`, `map`/`filter`/`filter_map`, and `triggers`' pipeline.
10. **Async, concurrency and the rest.**
    - The work:
      - #52: the `iter Wait` computation type (N3), `scope`, `race`, `timeout`,
        `for_each_concurrent` (N4) and simulated time;
      - #96's input observations and a loop at borrow type, the kernel side of O1 and O2;
      - `merge` of the two watches (`owns`), leader election, and the metrics server.
    - Justified by `run_controller`'s `concurrency`, `timeout` in `call`, `race` in `main` and
      `while_leader`, `merge(from_crs, from_deps)`, and Part 3's timeout and watcher tests.

The two kernel questions, O1's loop-scoped borrow and O2's input observations (#96), stand only
in step 10. Everything before it is elaboration, library code, or externs under the existing
SPEC §11 pattern.

## 6a. Milestones: standalone programs

The path in §6 is delivered as a ladder of small standalone programs. Each is useful on its
own, forces one cluster of features, and is accepted when it runs end to end with its goldens.
The operator is then mostly composition of them.

| # | deliverable | forces | §6 steps |
|---|---|---|---|
| M1 | text tools (`grep`/`wc`/`cut`-style) | bytes, text, slices; finite `for`; `\|>` over lines; bulk I/O | 1–2 |
| M2 | `jq`-lite: pretty-print and filter JSON | `data`/`box` with generics; `Vec`, maps; recursive data; JSON parse/serialize (derive) | 1, 4 |
| M3 | config validator: all errors, or first error | the error effect with unwinding; `try` ↔ `Result`; a fold with a failing algebra | 3 |
| M4 | rate limiter / retry simulator with tests | answering effects (`effect`/`handler`/`with`); fake logger and clock in tests | 5 |
| M5 | `curl`-lite against localhost | args, env, signals; blocking net; streaming body `\|> lines`; timeouts | 6 |
| M6 | local reconciler: make a directory match a spec | desired vs actual, diff, patch, retry/backoff, graceful shutdown, against the filesystem | 3–6 |
| M7 | streaming log processor built from generators | `gen`/`yield`; the adapter library over pure and effectful sources | 9 |
| M8 | concurrent fetcher with bounded parallelism and timeouts | async, `race`, structured concurrency (O1, O2) | 10 |

M3 and M4 can proceed in parallel once M1–M2 land. M6 runs the operator's control flow
before networking, TLS or Kubernetes, and the same reconcile code runs against the real
filesystem and against fake handlers in tests.

## 7. Surface hypotheses and alternatives

Each spelling below is a hypothesis.

- **`effect` / `handler` / `with`.**
  - Draft 0's `cap` and `handle … in { c -> … }` (`docs/surface-cbpv.md` §2.11) name the
    capability explicitly.
  - The strict account's sketch uses `does` for effects and `needs` for reader demands.
  - This sketch uses implicit capabilities throughout, so that logging does not show at call
    sites.
- **Rows.** `-> T / {E}` follows Koka's placement. The alternatives are `does E` after the
  result, or nothing at all, with inference and `bcc sig` only (N1).
- **No suspension marker at call sites.** The alternative is draft 0's `suspend op(…)` at the
  *operation*, which library code would use (`suspend wait(…)`, `suspend yield(x)`) and user code
  would not meet.
- **`try { … }` returning `Result`**, as the user settled for errors. `catch` arms in place are
  the alternative for local recovery.
- **`fn()` vs `{ -> T }`.** A body called several times (`retry`) is a `fn`. A one-shot suspended
  block is `{ … }`, as draft 0 has it.
- **`derives Json` with `@json("name")`** for renames, as serde's `rename`. The alternative is a
  naming policy (camelCase) per type.
- **Duration literals** `100.ms` and `30.s`. The alternative is `ms(100)`.
