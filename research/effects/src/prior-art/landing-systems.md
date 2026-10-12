# Prior art: how systems languages with ownership landed effects and suspension

Part A of a three-part survey. It covers languages that shipped, or nearly shipped, ownership,
borrowing or linearity together with async, coroutines, generators or effects. For each it records
what shipped, the mechanism, the trade-off accepted, what was given up, and the known negative
results. It proposes no mechanism.

**Not repeated here.** These documents already cover parts of this ground, and this chapter cites
them rather than restating them:
- `borrow-core/docs/prior-art-suspension-borrows.md` (E0626, `Pin`, `gen` blocks, lending
  iterators, io-uring, OxCaml, Swift actors and SE-0446, Hylo yield-once): cited below as **[SB]**;
- `borrow-core/survey.md` §2.3 (the language table) and P1–P15: **[SURVEY]**;
- `prior-art/p8-p5-linearity-drop.md` (linear vs affine, drop, finalisation): **[P8]**;
- `prior-art/i2-capture-resume.md` (capture and resume, the menu M0–M3, T1–T4): **[I2]**;
- `prior-art/p10-p9-exclusivity-lifetimes.md`: **[P10]**.

**Marks.**
- **[read]**: the page was fetched and read for this chapter (2026-10-12); quotations are from it.
- **[SB]**, **[SURVEY]**, …: taken from the named repo document, not re-read here.
- **[Crossref]**: title, authors and venue checked against the DOI's Crossref record.
- **[analysis]**: my own reading, with no source and no proof.
- **[unverified]**: recalled, not checked. Treat as a lead.

---

## 1. Rust

### 1.1 What shipped

| feature | status | source |
|---|---|---|
| `async`/`await`, `Future`, `Pin` | stable since 1.39 (2019) | [SB] §1.1–1.2 |
| async closures, `AsyncFn`/`AsyncFnMut`/`AsyncFnOnce` | stable in 1.85 (2025-02-20) | [read] https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/ ; RFC 3668 https://rust-lang.github.io/rfcs/3668-async-closures.html |
| GATs (enables a `LendingIterator` trait in libraries) | stable in 1.65 (2022-11) | [SB] §1.3 |
| `gen` blocks | unstable (`gen_blocks`, rust-lang/rust#117078); `gen` reserved in edition 2024; RFC 3513 FCP merged 2024-03-23 | [read] https://doc.rust-lang.org/nightly/edition-guide/rust-2024/gen-keyword.html |
| general coroutines (`yield`, `resume`) | unstable, internal | [SB] §1.1 (E0626) |
| `AsyncDrop` | nightly experiment (tracking #126482), not object-safe | [read] https://doc.rust-lang.org/std/future/trait.AsyncDrop.html |
| keyword generics / effects initiative | design; `const` traits nearest to landing; no user effects | [read] https://rust-lang.github.io/effects-initiative/updates/2024-02-09-extending-rusts-effect-system.html |
| Polonius (alpha) | nightly 2026; stabilisation is a stated target, "a target rather than a promise" | [read] https://goals.rust-lang.org/2026/polonius.html ; [read, secondary] https://infoworld.com/article/4206875/rust-preps-improved-borrow-checker-for-stabilization.html |

### 1.2 Suspension and borrows

- **The slice** (movable coroutines may not hold an internal borrow across `yield`; `async` blocks
  may, because they are polled through `Pin<&mut Self>`) is covered in [SB] §1.1–1.2. `gen`
  blocks are on the movable side, so "borrow may still be in use when `gen` block yields" is the
  shipped behaviour [SB] §1.3.
- **What `Pin` buys and costs.** It solves address stability of a self-referential frame stored
  inline as a value, and the `&mut Self` aliasing that a self-borrow creates (RFC 3467
  `UnsafePinned`) [SB] §1.2. Its ergonomic cost drove proposals such as boats' *Pinned places*
  (2024-07-23, https://without.boats/blog/pinned-places/) [SB].
- **Async closures are a lending construct.** RFC 3668 [read]: with `|| async {}`, "the future that
  is returned by the closure cannot reference any of the captures of the closure, which is a
  limitation that makes `|| async {}` quite unusable today." `AsyncFnMut::call_mut` instead returns
  a future borrowing the closure (`CallRefFuture<'a>`, a GAT). Limitations listed in the RFC: the
  associated future types are unnameable on stable; `Send` bounds on the returned future need
  return-type notation (RFC 3654); async closures are not effect-generic.
- **Lending iterators.** Expressible with GATs, but the pervasive *filtering* lending iterator is
  rejected by NLL: it is an instance of NLL "problem case #3" (a conditionally returned reborrow in
  a loop), cut from NLL in 2018. The Polonius 2026 goal [read] says this "blocks the ability to
  write lending iterator patterns entirely". So lending iteration in Rust is blocked by a
  borrow-checker *precision* limit, separately from the suspension question.

### 1.3 The Leakpocalypse, and why Rust is affine

- **Event** (April–May 2015, before 1.0). `thread::scoped` returned a `JoinGuard` whose `Drop`
  joined the child, which borrowed the parent's stack. Its safety "relied on the fact that the
  Drop implementation for JoinGuard was always run" [search summary of Nomicon *Leaking*,
  https://doc.rust-lang.org/nomicon/leaking.html; not fetched]. An `Rc` cycle leaks without `unsafe`
  (rust-lang/rust#24292), so destructors are not guaranteed. **Outcome**: RFC 1066 made
  `mem::forget` safe and `thread::scoped` was removed [read, https://www.ncameron.org/rfcs/1066.html;
  Gankra, *Pre-Pooping Your Pants*, https://cglab.ca/~abeinges/blah/everyone-poops (the URL with a trailing slash
  returned 404 when fetched; contents unverified)].
- **Replacement.** `std::thread::scope` (stable 1.63, [unverified version]) takes a closure and
  joins before returning, so the guarantee is a stack frame, not a destructor [read: boats'
  trilemma post names `thread::scope` and `rayon::join` as the sound API shape].
- **Why not linear.** Aria Desires (Gankra), *The Pain of Real Linear Types in Rust*, 2017-05-08
  [read, https://faultlore.com/blah/linear-rust/]:
  - what people want is "Proper Support For Relevant™ Types" (must-use), since Rust already has
    move-only;
  - **unwinding**: "Any panic can lead to the program continuing, but without an opportunity to
    process the value." Options are a no-panic effect (burdensome) or destructor bombs that abort
    on unwind;
  - **generic code**: every generic API that may drop a `T` needs a `?Leave`-style bound,
    cascading through the ecosystem; containers whose `insert`/assignment drop the old value need
    new signatures;
  - **closures** capturing must-use values add their own complexity;
  - conclusion: feasible but "something that would realistically take years to shake out".
- **Still open.** Proposals continue (a `Forget`/`Leak` marker trait, pre-RFC 2025,
  https://internals.rust-lang.org/t/pre-rfc-forget-marker-trait/22456 [unverified contents]).
  boats, *Asynchronous clean-up* (2024-02-24) [read,
  https://without.boats/blog/asynchronous-clean-up/] names "unforgettable" (destructor always
  runs) and "undroppable" (must be explicitly consumed) types, and notes that for an undroppable
  type "any time you drop any generic value in any code path of that function, that type would
  need to be bound by `Drop`".

### 1.4 The scoped task trilemma

boats, *The Scoped Task Trilemma*, 2023-04-08 [read,
https://without.boats/blog/the-scoped-task-trilemma/]:

> "Any sound API can only provide at most two of the following three desirable properties:
> Concurrency: Child tasks proceed concurrently with the parent. Parallelizability: Child tasks can
> be made to proceed in parallel with the parent. Borrowing: Child tasks can borrow data from the
> parent without synchronization."

- Rust's three corners: `thread::spawn`/`task::spawn` (no borrowing, `'static`);
  `thread::scope`/`rayon::join` (parent blocks); `select!`/`FuturesUnordered` (borrowing and
  concurrency, single-threaded interleaving inside one task).
- The reason is the Leakpocalypse ("every object in Rust can be leaked without running its
  destructor") together with the fact that an async parent is itself a **value** (a future) that
  its caller may drop or forget at any `await`. A self-referential coroutine "close[s] over
  lifetimes that essentially refer to sections of the stack within the coroutine". The post says
  directly: "we are not adding linear types to Rust".
- boats' later *Asynchronous clean-up* sketches the escape: a `!Leak` `Scope` makes the enclosing
  future `!Leak`, `poll_cancel` performs async cancellation, and the synchronous destructor is an
  "emergency backstop" (which blocks). This is a proposal; nothing of it has shipped.

### 1.5 Cancellation and async drop

- **Cancellation is drop.** Any future can be dropped at any `await`. Tokio's definition [read,
  https://docs.rs/tokio/latest/tokio/macro.select.html]: a method is cancellation-safe if "it must be
  a no-op to drop that future and recreate it". `read_exact`, `read_to_end`, `write_all` are not;
  `Mutex::lock`, `Semaphore::acquire` lose their queue position.
- **Futurelock.** Oxide RFD 609 [read via search summary, https://rfd.shared.oxide.computer/rfd/609]:
  a deadlock where a resource owned by future A is needed by future B while the task holding both
  no longer polls A (a `select!` over a `&mut` future). It arises from futures being passive values
  that make progress only when polled.
- **Async drop.** boats [read, *Asynchronous clean-up*] lists why `await` in destructors does not
  work: a value may be dropped in a non-async scope; trait-object and `Send` problems as with async
  methods; implicit await points; sequential destructors where concurrent ones are wanted. The
  nightly `AsyncDrop` exists, but nothing guarantees it runs (any value can still be leaked or
  dropped synchronously).
- **Owned buffers for completion I/O** (io-uring): [SB] §1.4.

### 1.6 Effect polymorphism

- **Keyword generics / effects initiative** [read, Yosh Wuyts, 2024-02-09, link in §1.1]. Effects are
  a **fixed set** (`async`, `const`, `try`, `unsafe`, generators), split into "carried" (desugar to a
  type such as `impl Future`) and "uncarried". Stage I: `#[maybe(async)]` traits; Stage II: effect-
  generic bounds and functions, where "the effect of the function and the effect of the bounds it
  takes all become the same". Explicit non-goals: user-defined effects, effect handlers. A
  maybe-async function cannot call an always-async one. Motivation: "with all five effects, there
  would be 96 different trait variants".
- **Counter-position.** boats, *Coroutines and Effects* (2024-04-20) [read,
  https://without.boats/blog/coroutines-and-effects/]: Rust's coroutine-based effects are
  "statically typed, lexically scoped, and unlayered"; effect forwarding is explicit (`.await`,
  `?`), unlike handlers where "the forwarding of effects by a callee is implicit". boats, *Let
  futures be futures* (2024-02-03) [read, https://without.boats/blog/let-futures-be-futures/]:
  async is the price of native compatibility with the C ABI; "The cost … is the 'function
  coloring' problem."
- **What exists for higher-order effectful callbacks today**: generic `F: FnMut() -> R` where `R`
  may be `Result` or `impl Future`, plus `AsyncFn*`. There is no rank-2 effect polymorphism; the
  closure's effect is carried in its return type, so a callback that is "maybe async" requires
  duplicated APIs [read, effects initiative].

### 1.7 Formal status

RustBelt covers neither coroutines nor `Pin` [SB §1.1, SURVEY §2.3]. Jung's pinning typestate is a
blog-level formalism [SB §1.2]. No mechanised account of async cancellation exists that I found
[unverified absence].

---

## 2. Swift

### 2.1 What shipped

| feature | status | source |
|---|---|---|
| exclusivity enforcement (SE-0176) | Swift 4.0; static + dynamic | [read] https://github.com/swiftlang/swift-evolution/blob/main/proposals/0176-enforce-exclusive-access-to-memory.md |
| `_read`/`_modify` coroutine accessors | in the stdlib and ABI since 5.0, underscored | [read] SE-0474 |
| `yielding borrow` / `yielding mutate` (SE-0474) | **Accepted**; partially implemented behind `CoroutineAccessors` | [read] https://github.com/swiftlang/swift-evolution/blob/main/proposals/0474-yielding-accessors.md |
| async/await, structured concurrency, `async let` (SE-0296/0304/0317) | Swift 5.5 | [read] SE-0304, SE-0317 |
| `borrowing`/`consuming` (SE-0377), `~Copyable` (SE-0390) | Swift 5.9 | [read] status lines |
| region-based isolation, `sending` (SE-0414) | Swift 6.0 | [read] status line |
| `~Escapable` (SE-0446) | Swift 6.2 | [read] |

### 2.2 A lending coroutine in production: `_read`/`_modify` and SE-0474

- `yielding borrow`/`yielding mutate` accessors run until `yield`, lend the value, and "Once the
  caller is finished accessing the value, it resumes the accessor's execution." Rule: "Exactly
  one yield is executed on any path through the accessor" [read]. The resumption is second-class
  and lexically scoped by the access [SB §4].
- **Throwing callers.** An earlier draft "specified that if an error is thrown in a coroutine caller
  while a coroutine is suspended, the coroutine is to 'unwind' and the code after the `yield` is not
  to run." The accepted design **always resumes**: "If an error is thrown in a caller into which a
  value has been yielded, the _caller_ must put the yielded mutable value back into a consistent
  state", and it is an error to consume the yielded value without reinitialising it. Reason:
  "only the caller will be in a position to ensure that [higher-level invariants] are satisfied on
  the throwing path" [read, §"Unwinding the accessor when an error is thrown in the caller"].
- **Negative result, stated by the proposal.** "That the access ends when the coroutine is resumed
  means that the lifetime of the lent value is strictly shorter than that of the base value." A
  `~Escapable` value derived from a `yielding borrow` cannot be returned, because its lifetime "ends
  _within_ `getStuffing`, when the `yielding borrow` coroutine is resumed". Swift therefore plans
  **non-coroutine** `borrow`/`mutate` accessors that impose no lifetime dependency on a coroutine
  access, trading "stronger implementation guarantees for more flexibility in the lifetime of
  derived `~Escapable` values" [read].
- Whether a yielding accessor may itself `await` is not addressed in SE-0474 [read: no occurrence
  of `async`]; I believe `_modify` may not suspend asynchronously [unverified].

### 2.3 Why exclusivity is dynamic

SE-0176 [read]: static enforcement for locals, `inout` parameters and struct properties; dynamic for
class properties, globals and "variables captured in escaping closures", because "Swift cannot
reason about when an escaping closure will be called", and references to class instances "can be
copied arbitrarily". Dynamic bookkeeping is thread-local and "cheap enough to enable by default".
In async code the tracking is per task [unverified]. The lesson: once a mutable place is reachable
through a first-class, escaping or shared handle, Swift gave up static exclusivity and checks at run
time.

### 2.4 Structured concurrency, borrowing and cancellation

- **Children are scoped by the frame, not by a destructor.** SE-0304/0317 [read]: "a child task does
  not persist beyond the scope in which it was created. By the time the scope exits, the child task
  must either have completed, or it will be implicitly awaited. When the scope exits via a thrown
  error, the child task will be implicitly cancelled before it is awaited."
- **Cancellation is cooperative.** SE-0304 [read]: "cancellation has no effect at all unless
  something checks for cancellation"; it is reported by throwing `CancellationError()`, so
  "cancellation introduces no additional control-flow paths". A cancelled child still runs to
  completion before the scope returns.
- **Borrowing into child tasks.** `async let` initialisers are `@Sendable` closures: mutation of a
  captured var is rejected ("mutation of captured var 'localText' in concurrently-executing code")
  [read, SE-0317]. But SE-0446 [read] shows `async let r = asyncBorrowingFunc(value) // OK to pass
  borrowing` for a `~Escapable` local: a **shared** borrow into a concurrent, possibly parallel
  child. `TaskGroup.addTask`, `Task.init`, `Task.detached` take `@Sendable @escaping` closures and
  cannot capture `~Escapable` values [read, SE-0304 signatures; SE-0446].
- **Against the trilemma** [analysis]: Swift gets concurrency + parallelism + (shared, `Sendable`)
  borrowing for `async let` because an async frame is not a first-class value that a caller can
  drop or forget mid-flight, and scope exit *awaits* (suspends, not blocks) the children. The
  trilemma's premise (a leakable future) does not hold. Mutable borrowing into children is still
  excluded, by `Sendable`, not by lifetimes.
- **Actor-isolated `inout` across `await`** is ill-formed (SE-0306) [SB §4].

---

## 3. Hylo (formerly Val)

- **Mutable value semantics, no first-class references** [SB §4, SURVEY §2.3]. Subscripts `yield`
  projections in `let`, `inout`, `sink` and `set` variants [read,
  https://docs.hylo-lang.org/language-tour/subscripts]. A projection is scoped to its access.
- **Spec rules** [read, https://github.com/hylo-lang/specification/blob/main/spec.md §Projections]:
  "If a projection `p` projects an object `o` mutably, `o` is inaccessible for the duration of
  `p`'s lifetime." "An object may capture a projection at its initialization. A captured projection
  is released when the lifetime of the capturing object ends. The captured projections of a closure
  are defined by its environment." This is the "remote part" mechanism: a value (closure or
  struct) may hold a projection, and it is non-escaping because the projected object stays frozen
  or inaccessible until the holder dies. I did not find the words "remote let/inout" in the current
  spec [unverified terminology].
- **Concurrency (design, not shipped).** Teodorescu, *Concurrency: From Theory to Practice*,
  Overload 32(181), 2024 [read, https://accu.org/journals/overload/32/181/teodorescu/]: "The `spawn`
  function returns a future object that is neither movable nor copyable", so the await is in the
  spawn's scope; "the spawned work can safely access the stack available at the spawn point"
  because "the stack used at the spawn point is kept alive until await". Implemented with stackful
  coroutines (`boost::context`) and "thread inversion"; goal "no function colouring"; cancellation
  is future work. The Hylo docs [read, https://docs.hylo-lang.org/language-tour/concurrency] say the
  model "is still under design", and there dropping a handle sends a stop signal and a `StopToken` is
  cooperative. Also ICOOOLPS 2024, *Structured concurrency in Hylo* [unverified contents].
- [analysis] Hylo sidesteps the trilemma the same way Swift does, and more strongly: the future is
  immovable and must be awaited (a linear, second-class handle), so the parent cannot be leaked
  while a child borrows. Stackful execution means no frame is ever reified as a movable value.

---

## 4. Mojo

- **Origins.** An origin "answers two questions: What variable 'owns' this value? Can the value be
  mutated using this reference?" [read, https://mojolang.org/docs/manual/values/lifetimes]. `ref`
  arguments and returns are parameterised by origins; argument exclusivity is enforced.
- **Interior origins (Mojo 1.0, 2026, experimental)** [read, https://mojolang.org/releases/v1.0.0/]:
  "`List`, `Dict`, `String`, and several other types return element references bound to an interior
  origin of the list instead of the whole-list origin, so code that holds an element reference across
  a mutation is rejected". Nick Smith's gist (below) records "Mojo 1.0 has adopted a variation of this
  proposal" [read]. This is the path-based idea of §5 in a shipping language.
- **Linear types.** Explicitly destroyed types (`@explicit_destroy`, now `Deinitable where False`);
  collections of them must be drained with `deinit_with()` [read, v1.0.0 notes].
- **Errors** are typed `raises`, implemented as returns, so destructors run [SURVEY §2.3].
- **Async/coroutines and origins**: undocumented in what I read [read: absent from the lifetimes
  page and the 1.0 notes]. Group borrowing as such is not in Mojo [analysis of the 1.0 notes].

---

## 5. Vale and Valen (Evan Ovadia); group borrowing

### 5.1 Vale

- **Generational references** (runtime check on dereference) and **regions** (planned;
  read-only regions make borrow checking free) [SURVEY §2.3; https://verdagon.dev/blog/generational-references].
- **Higher RAII** (2022-03-22) [read, https://verdagon.dev/blog/higher-raii-7drl]: linear
  "must-explicitly-destroy" types. On panic Vale does not run destructors through unwinding:
  "when a panic happens, we blast away only the containing region". Three options are floated for
  cleaning up linear values on panic, one being "panic expressions" akin to algebraic effects.
- **Parallel foreach with region borrowing** (2022-02-15, "a theoretical feature, and not implemented
  yet") [read, https://verdagon.dev/blog/seamless-fearless-structured-concurrency]: the loop body
  sees all pre-existing data as an immutable region, so threads read parent data without
  synchronisation; the parent is blocked for the loop.

### 5.2 Valen and group borrowing

- **Valen** (2026): a new language by Ovadia for Rust interop, with group borrowing, linear types,
  and an envisioned "Rc that can hold mutable data without RefCell or Cell". Async and effects are
  only on the wish list [read, https://verdagon.dev/blog/golden-spike-reviving-vale-valen,
  2026-09-17].
- **Origin of the idea.** Nick Smith's gist (a Mojo proposal, early draft, last active Jan 2026)
  [read, https://gist.github.com/nmsmith/cdaa94aa74e8e0611221e65db8e41f7b]: "When we associate a
  reference or pointer with a 'lifetime' parameter, we are attempting to model (in the type system)
  the **set of variables** that a pointer can target." References are parameterised by a region
  such as `Pointer[people.items]`. Explained by Ovadia, *Group Borrowing* (2025-08-28) [read,
  https://verdagon.dev/blog/group-borrowing].
- **Mechanism** [read, *Group Borrowing* and *Valen group borrowing*,
  https://verdagon.dev/blog/valen-group-borrowing, 2026-10-11]:
  - "Every object can be described by a path": a local or parameter, then fields, `[]` for
    collection elements, variants.
  - **One kind of reference**; mutability is in the function signature (`mut(...)` effects on paths).
  - **Invalidation**: "When we modify an object, we mark any reference pointing _inside_ that object
    as 'invalidated'"; using an invalidated reference is a compile error. Precisely: mutating a group
    does not invalidate references *to* that group, only references into its **child groups**
    (elements, variant payloads, owned heap objects), which a mutation could destroy, reallocate or
    retype.
  - **Two mutable references to one place are allowed**: `fn attack[mut r: group Entity](ref[r] a:
    Entity, ref[r] d: Entity)`. Sound because "non-owning references cannot destroy objects or
    change their types".
  - "a path isn't really like a lifetime": a lifetime is "a span of instructions"; a path names where
    the data lives.
- **What it gives up** [read]: items of a group must be "mutually isolated … they can't indirectly
  own each other"; no unique references, so no `noalias` for the optimiser; the gist states it
  cannot model Rust's guarantee that a list of `&mut` with one lifetime never alias ("I consider
  this to be a worthwhile trade-off"); more annotation of parameters. Status: Valen's checker runs
  the demonstrated examples; parts ("type-stability exception") are unimplemented.
- **Suspension, async, closures, stored references**: none of the three sources discusses them
  [read: checked for each].

### 5.3 Does a path-indexed discipline change the suspension problem? [analysis]

Everything here is my reading; none of it is in the sources.

- **What a held reference must survive changes.** Under lifetimes, a suspension holding a borrow
  must not outlive the lender, and the lender must not be touched while the lend is open. Under
  paths, a held reference is valid until someone *structurally* mutates a parent of its path; plain
  writes to the same group are allowed. So the resumer can keep mutating the place the suspension
  points at (non-structurally) while the suspension is parked. That is weaker exclusivity, not a
  different answer to *when the suspension may run*.
- **Invalidation is computed from code the checker can see.** It is intraprocedural plus
  signatures. Across a suspension, the code that runs between stop and resume is the resumer's, and
  any structural mutation it performs on an overlapping path must invalidate the parked suspension
  as a whole. For that, the suspension's type must expose the paths it holds, just as a Rust future
  exposes its lifetime parameters. This is the same burden in a different index.
- **Internal (self) borrows.** A path is rooted at a local of the frame. When the frame becomes a
  value (a state-machine state), the root is a field of that value, and the path is relative to the
  suspension object (`g.state.xs[]`). Paths are not addresses, so the *typing* survives moving the
  suspension. The *representation* does not: a runtime reference is still an address, so moving a
  self-referential frame still needs `Pin` or relative pointers. And a lending iterator (yielding
  `ref[g.state.xs[]]`) is then ordinary: the yielded reference is invalidated by any structural
  mutation of `g`, and `resume` is such a mutation unless its signature says otherwise.
- **Order of lifetimes.** Paths carry no total order. Our tier-2 obstruction is about *where a
  lifetime sits* in a total order (adjacency, `segShiftFailsAtEveryCut`). A path-indexed world has
  no stratification to shift, so that specific obstruction has no counterpart. What replaces it is
  a structural-mutation effect on paths, which must then be tracked through effect rows and through
  higher-order callbacks (the gist already restricts trait implementations from adding mutation
  effects).
- **Threads.** Shared mutable aliasing is not data-race-free. Group borrowing as documented is
  single-threaded; moving a group to another task needs a separate rule (as Swift needs
  `Sendable`). Nothing in the sources addresses it.
- **Relevance to `two-writers.bc`** (`corpus/pending/two-writers.bc`: one capability lent `mut`
  twice to one call). Group borrowing accepts exactly this shape when both writers are in one group
  and the callee does no structural mutation; an output stream is a leaf, so writes are not
  structural. The cost is the loss of the guarantee "two `&mut` arguments never alias", which the
  gist names. It is the same point the pending file records as "contraction at some payloads
  (opaque payloads only, where interleaved writes are the stream's own order?)".

---

## 6. Austral, Pony, Verona, Cyclone (only what bears on suspension or effects)

- **Austral** (Borretti). Linear types and capabilities; borrows are lexical regions. **No
  exceptions, abort on contract violation**, and the spec gives linearity as a reason: "we can throw
  an exception before the consumer of a linear resource is called, thus leaking the resource"
  [read, https://austral-lang.org/spec/spec.html]. It cites PacLang (linear environments in
  exception signatures) as the alternative it declined. No async, coroutines or closures
  [unverified: absent from what was read].
- **Pony.** Reference capabilities (`iso`, `val`, `ref`, `box`, `trn`, `tag`) and actors.
  Behaviours run to completion; there is no suspension inside a behaviour, so no borrow is ever held
  across one; asynchrony is by message and promise [SURVEY §2.3; Clebsch et al., *Deny capabilities
  for safe, fast actors*, AGERE 2015, https://doi.org/10.1145/2824815.2824816 [Crossref]].
- **Verona.** Regions with a single entry point and *cowns*; behaviour-oriented concurrency, where
  `when (c1, c2) { … }` acquires all cowns and runs to completion [Cheeseman et al., OOPSLA 2023,
  https://doi.org/10.1145/3622852 [Crossref]; Arvidsson et al., *Reference Capabilities for Flexible
  Memory Management*, OOPSLA 2023, https://doi.org/10.1145/3622846 [Crossref]]. Same choice as Pony:
  no suspension inside a unit of work [SURVEY §2.3].
- **Cyclone.** Lexical and dynamic regions; a function's effect is the set of regions it may access
  [Grossman et al., PLDI 2002, https://doi.org/10.1145/512529.512563 [Crossref]]. Threads: Grossman,
  *Type-safe multithreading in Cyclone*, TLDI 2003, https://doi.org/10.1145/604174.604177 [Crossref]
  (thread-shared regions, lock-annotated types). No coroutines [unverified].

---

## 7. Summary table

| language | suspension holding borrows? how | higher-order effect polymorphism? | linear or affine | cancellation / drop semantics | key negative result |
|---|---|---|---|---|---|
| Rust | external borrows: yes, at the future's lifetime params; internal: only in immovable coroutines (`async`), through `Pin`; `gen` blocks: no (E0626); lending: `AsyncFnMut` returns a future borrowing the closure | none; effects carried in return types (`impl Future`, `Result`); keyword generics: fixed set, no handlers, design only | affine (`mem::forget` safe, RFC 1066) | cancel = drop at any `await`; sync destructors only; `AsyncDrop` nightly, not guaranteed | scoped task trilemma; Leakpocalypse; cancellation-safety and futurelock |
| Swift | own frame: yes (heap async frames, never moved); child tasks: shared `~Escapable` borrows into `async let` only; lending: `yielding borrow/mutate`, exactly once, always resumed | `rethrows`/`reasync`-style only [unverified for `reasync`]; no user effects | `~Copyable` is affine-ish (consumed or implicitly destroyed); no linear | cooperative cancellation (a flag and `CancellationError`); scope exit awaits children | coroutine-lent value strictly shorter than base, so derived `~Escapable` values cannot be returned; exclusivity dynamic for classes, globals, escaping captures |
| Hylo | projections yielded by subscripts, second-class; objects may capture projections (non-escaping); design: immovable, must-await spawn futures may borrow the stack | none found | value semantics; `sink`; no first-class references | design: drop handle = stop signal; cooperative `StopToken` | references cannot be stored or escape; concurrency still design |
| Mojo | not documented | not documented | affine by default, opt-in linear (`Deinitable where False`) | errors are returns, destructors run | interior origins needed to stop element refs dangling after reallocation |
| Vale / Valen | not documented (async on the wish list) | none | linear opt-in (higher RAII) | panic drops the region, not per-object destructors | group borrowing gives up unique references and `noalias`; group items must be mutually isolated |
| Austral | no suspension | none | linear | abort; no unwinding | linear types and exceptions conflict (stated in spec) |
| Pony / Verona | no: behaviours run to completion | none | capabilities, not linear in the resource sense | n/a | (by design) no suspension inside a unit of work |
| Cyclone | no coroutines | region effects (sets of regions) | unique pointers plus regions | n/a | — |

---

## 8. NEGATIVE RESULTS a new language must respect

1. **Leaking is safe once there is shared ownership with cycles, unless linearity is enforced
   everywhere.** An `Rc` cycle is a safe `forget`; any guarantee that relies on a destructor running
   is unsound. (RFC 1066; Nomicon *Leaking*; rust-lang/rust#24292.)
2. **Scoped borrowing children need the scope to be un-leakable.** With leakable parents, at most two
   of concurrency, parallelism and borrowing. (boats, *The Scoped Task Trilemma*, 2023.)
3. **A destructor-based join of a borrowing child is unsound if destructors can be skipped;** a
   closure-scoped join (`thread::scope`) is sound. (Nomicon *Leaking*; trilemma post.)
4. **Linear types conflict with unwinding.** A panic or exception either leaks the linear value or
   needs per-frame obligations (no-panic effects, destructor bombs, abort). (Gankra 2017; Austral
   spec.)
5. **Must-use types infect generic code:** every generic function that may drop a `T` needs a bound,
   and drop-the-old-value APIs need new signatures. (Gankra 2017; boats, *Asynchronous clean-up*.)
6. **Async destructors cannot be guaranteed by a drop hook:** values are dropped in non-async
   contexts, and implicit awaits appear. (boats, *Asynchronous clean-up*, 2024.)
7. **Cancellation-as-drop at every suspension makes many operations cancellation-unsafe** (partial
   reads and writes, lock queue positions). (Tokio `select!` docs.)
8. **Passive futures plus partial polling can deadlock** (futurelock). (Oxide RFD 609.)
9. **An inline, movable suspended frame cannot hold a self-borrow without address pinning;** `gen`
   blocks driven by `&mut self` cannot self-borrow at all. (E0626; RFC 3513; `Pin` docs; [SB].)
10. **A closure returning a suspension cannot lend from its own captures without a lending call
    trait;** `Fn() -> impl Future` cannot express it. (RFC 3668.)
11. **Lending iterators hit borrow-checker precision limits** (NLL problem case #3), separately from
    suspension. (Polonius 2026 goal.)
12. **A value lent by a yield-once coroutine lives strictly shorter than its base,** so values
    derived from it cannot be returned; Swift is adding non-coroutine borrow accessors. (SE-0474.)
13. **Static exclusivity does not reach places behind escaping closures, globals or class
    references;** Swift enforces those dynamically. (SE-0176.)
14. **A suspended accessor should resume, not unwind, when the caller throws;** only the caller can
    restore invariants of the lent value. (SE-0474, the reversed earlier design.)
15. **Shared-mutable (group) borrowing cannot express non-aliasing of same-lifetime `&mut`s and
    loses `noalias`.** (Smith gist; Ovadia, *Group Borrowing*.)
16. **Effect-generic over a fixed keyword set multiplies trait variants** (96 for five effects), and
    maybe-async cannot call always-async. (Rust effects initiative, 2024.)

---

## 9. What this means for our tier 1 and tier 2 (observations only)

1. Shipped child-borrows-parent across concurrent suspension (Swift `async let`, Hylo design) exist only
   where the parent frame is not a droppable value and cancellation is cooperative; results 1–3 stem
   from Rust's leak, which our linear, `forget`-free core does not have.
2. Our suspensions are values (state-machine states), as in Rust, not stackful frames as in Swift and
   Hylo, so "a parked parent the holder never resumes" exists for us even without leaks.
3. No shipped language has a general, nth-order suspension holding an internal borrow with a static
   proof: Rust's `async` rests on unproved `Pin`; Swift and Hylo lend only yield-once, second-class.
4. Lending shipped only where the resumer exclusively borrows the suspension for the lend's duration,
   and Swift reports that this strictly bounds derived lifetimes (result 12).
5. A cancel that returns an owned resource (K3) appears only as Rust's owned-buffer convention and
   boats' unshipped `poll_cancel`; no language types it.
6. No systems language has shipped more than a fixed effect set with "maybe" quantification; none has
   rank-n, row-polymorphic effectful callbacks (tier 1 has no shipped precedent to copy).
7. Path-indexed borrowing has no lifetime order, so our adjacency obstruction has no counterpart; its
   sources are silent on suspension, and it gives up the unique `mut` that `two-writers.bc` probes.
