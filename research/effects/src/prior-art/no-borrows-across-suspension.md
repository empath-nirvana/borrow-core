# The rule "no internal borrows across a suspension": what it costs

**Status.** Observations only, written 2026-10-12 against `borrow-core` main (`4b267fc`). No
build was run. No mechanism is proposed here. Claims about other languages are tagged [read]
when they come from the sibling surveys (`landing.md`, `landing-systems.md`) and [unverified]
when they are from memory.

## The rule under evaluation

A lend opened **inside** a suspendable computation must end before that computation's next
suspension. The computation can be a generator, a handled body, an async task or a coroutine. A
suspension is a resuming control operation whose continuation is captured (`yield`, `await`).

The rule allows the following:
- Lending and borrowing freely between suspension points.
- Holding a borrow to the end once the last suspension has passed.
- Holding a borrow made **outside**, before the handler or generator existed, across
  suspensions (`corpus/gen-borrowed.bc`).
- Ending a lend at its last use, not at the end of its block, as Rust's NLL does.

It is today's T1 (SPEC §19, the table "Which operations cross a borrow's scope") plus
non-lexical lend ending. Abortive operations (`raise`) and answering operations (calls on a
capability) are not suspensions, so they are unaffected.

Three facts of today's kernel decide most of the cases below:

1. **`&mut c` of a capability is a move.** On an opaque capability it elaborates to "move in,
   hand back" (SPEC §11 *Sugar*). It is not a kernel borrow, so a "lend" of `stdin` that spans
   `yield`s is ownership. Whether it is legal turns on K3 (a destructorless value held across an
   affine `yield`), not on this rule.
2. **No lend spans a loop's observations** (SPEC §14 *Borrow scopes over loops*). A borrow block
   whose body is a `for` is re-lent at each observation. Holding an outer borrow across a
   generator's `yield`s therefore works today only when the stored generator is **pulled by
   hand** inside one borrow block (`gen-borrowed.bc` l.8–10). A `for` over that generator inside
   the borrow block is rejected (`reject/lend-iter-borrow.bc`). The rule's "already works today"
   holds for the hand-pulled shape only.
3. **No view at the same lifetime through a pointer** (SPEC §5 *Open*; §9 l.488–500,
   `imm_view_rejected`). Each pointer hop from an `imm 'a` borrow is a `withload`, a fresh lend at
   a shorter `'x ⊏ 'a`, and that lend is opened by whoever makes the hop. For arrays one
   `withload` gives every leaf at `'x`, so it can be done outside the generator. A `μ` list or a
   tree needs one `withload` per hop.

## 1. Corpus

**Classes.**
- **(a)** fits as written.
- **(b)** fits with a rewrite.
- **(c)** ruled out by the rule.
- **(d)** unrelated: something else blocks it.

The "rule-side" column says what the rule alone would do to the program once its (d) blocker is
gone.

### 1.1 `corpus/pending/` (22 programs)

| program | class | rule-side | note (line numbers in the file) |
|---|---|---|---|
| `async-borrow` | (d) #52: no `async fn`, `spawn`, `.await` or scheduler; borrow-across-loop (fact 2) | (a) if the scheduler runs inside the borrow; (c) if the spawning function is itself a task | `borrow imm l` (l.48) is opened in `main` before the tasks exist. The tasks hold the outer `b1`/`b2` across `yield_now().await` (l.41), which the rule allows. `t.await + u.await` (l.52) happens while the lend is open. It fits only under the file's "scoped spawning" reading (l.16), where those awaits are the scheduler loop and not a suspension of `main`. If a task spawned children over its own local, the parent's await would cross its own lend, which the rule rules out (§2 row 4). |
| `backtrack-multishot` | (d) #18 and multi-shot (ignored by decision) | (a) | No lend anywhere (l.36–44). |
| `box-dup` | (d) kernel: same-lifetime `[@a]` comultiplication | (a) | No suspension. |
| `callbacks-in-data` | (d) SPEC §14 Open: the effect of a stored callback | (a) | No suspension. |
| `closure-captures-int` | (d) #9: promotion over persistent slots | (a) | No suspension. |
| `closure-lend` | (d) #54: a lend to a closure call | (a) | `w!(&mut stdout)` (l.42) is a call, not a suspension. |
| `data-box-tree` | (d) #54 stage 8 (`data`, `box`, fold blocks) | (a) | `fold_imm` (l.28) has no suspension. |
| `dig-bang` | (d) kernel: digging `!A ⊸ !!A` | (a) | — |
| `fold-under-u` | (d) SPEC §6: `X` under `U` in `FShape` | (a) | The interpreter threads `(stdin, stdout)` by ownership (l.45–46, 53). |
| `gen-adapters-io` | (d) K3 residual cancel: the capability is held across an affine `yield` (l.11) | (a) at the kernel level; (b) if the rule is read at the surface | `for b in bytes(&mut c)` (l.16) lends `c` across the `yield`s. By fact 1 that is a move and hand-back. Read as a surface lend, the rewrite is `bytes(c)` as in `gen-digits` l.17, with `break` closing the iterator and handing `c` back (`reject/gen-return-held.bc` l.4). K3 remains either way. |
| `gen-digits` | (d) K3 | (a) | `bytes(c)` (l.17) moves `c` into the iterator. No lend is opened. |
| `gen-lazy` | (d) K3 (`o` across `yield`, l.12) | (a) | `putb(&mut o, …)` and `put_dec(&mut o, …)` (l.17, 20, 21) each end at their call, before `yield(i)` (l.22). This is the rule's "lend freely between suspensions". |
| `gen-lines` | (d) K3 | (a) | `bytes(c)` (l.22) is a move. `w!(stdout)` (l.42) is in the consumer's clause, outside the generator. |
| `lend-nested` | (d) #54: a lend inside an operand | (a) | No suspension. NLL is irrelevant. |
| `lend-two` | (d) #54: two lends in one call | (a) | No suspension. |
| `map-div-fold` | (d) SPEC §14: a div callback inside a fold's algebra | (a) | — |
| `needs-stdout` | (d) PR #100 `needs`/`provide` | (a) | `provide stdout { … }` (l.30) is a borrow around code that does not suspend. It would become (c) if `greet` yielded, because `provide` would then be a lend opened inside the generator. |
| `noalloc` | (d) a design question (tracking allocation) | (a) | — |
| `print-borrowed-list` | (d) #57: no borrowed-list iterator; `fold_imm` cannot hold the capability (l.7–11) | the consumer: (a). The iterator as a generator: (c) as written, or (b) at O(n²) | The `for` body (l.37) does not suspend. But `iter(&l)` written as a generator must keep a cursor into the list between `yield`s. By fact 3 that cursor is a view from a `withload` made inside the generator (l.17–18: "each node's view comes from a `withload` at a shorter lifetime"), so it is a lend across a suspension. The rewrite keeps only the outer `imm 'a List` and an index, and re-descends from the head at each step (O(i) per element). The push form (a `fold_imm` whose algebra writes) is blocked by (d). |
| `raise-in-fold` | (d) K4 (early exit from a kernel fold), #161, and lending a place inside an abandonable body (as in `reject/effect-try-lend`) | (a) | `with to_result { view_sum(&bad) }` (l.91): a lend opened inside a handled body across an **abortive** operation, which the rule permits. |
| `two-writers` | (d) a design question: `mut` contraction | (a) | No suspension. |
| `yield-callback` | (d) #161: effectful callbacks | (a) | No lend (l.22–23). |

### 1.2 `corpus/reject/`: effect, generator and lend programs

"Stays rejected" means the rule agrees with today's verdict, for today's reason.

| program | class | under the rule | note |
|---|---|---|---|
| `gen-self-borrow` | (a) under NLL | **newly accepted**, given NLL | `borrow imm c { 'x, b -> yield(*b); () }` (l.12–14). The last use of `b` is the payload `*b`, which is evaluated before `yield` performs. With non-lexical ending the lend is over before the suspension. Accepting it requires the elaborator to end the borrow callback at the last use, the stretch splitting that `LoopLend` already does for loops (SPEC §14). The corpus's canonical self-reference reject is therefore not a self-reference under NLL. A variant that reads `*b` after the `yield` stays (c), and the rewrite is `corpus/gen-cell.bc`'s. |
| `for-lend-resumes` | (b) | stays rejected | `for x in &a { yield(*x) }` (l.14): the iterator holds the lend of the generator's own `a` for the whole loop. Rewrite: `for x in a { yield(x) }` over the owned array, which copies each element out under a one-turn borrow (SPEC §16 table, `corpus/for-data-div.bc`). There is no extra cost. |
| `lend-iter-borrow` | (d) borrow-across-loop (fact 2) | the rule allows it | `over<'a>` (l.19–21) holds an **outer** borrow across `yield`s, the shape the rule explicitly permits. It is rejected because `main`'s borrow block contains a `for` (l.26–28), which is re-lent at each observation. This is SPEC §14 *Not covered* ("a pipeline whose source holds the borrow"). |
| `lend-let-used` | (a) under NLL | **newly accepted** | `let tb = &t` (l.16), last used at l.18, then `free(t)` at l.19. A lexical lend rejects it; NLL accepts it. |
| `lend-array-result` | (d) a call's result mentions the lent lifetime | probably newly accepted under NLL [unverified] | `let h = split_at_mut(&mut a, 2); 0` (l.13–14): `h` is never used, so a last-use lend ends at once. Rust accepts the analogous program. |
| `lend-div-two`, `lend-escape`, `lend-shadow` | (d) borrow scopes over loops (fact 2) | stay rejected | None suspends inside a lend. In `lend-escape`, `b2` is used in the loop (l.22), so NLL does not help. |
| `effect-try-lend` | (d) handing a place back from an abandonable body (K3-like: `stdout` has no destructor) | the rule permits it | `putb(&mut stdout, 10)` (l.8) ends at its call, before `half(3)`, and `half` is abortive anyway. |
| `gen-escape` | (d) outlives | stays rejected; the rule agrees | Returning a stored generator out of the scope of the borrow it holds (l.28–31) is the rule's "a thunk cannot outlive a borrow it holds". |
| `effect-abort-live`, `core-effects-no-dtor` | (d) no destructor across an abort | stay rejected | There is no lend. |
| `effect-clause-op`, `effect-error-type`, `effect-no-handler`, `effect-raise-unhandled`, `core-effects-not-in-row`, `yield-outside` | (d) effect typing and safety | stay rejected | — |
| `effect-fn-value`, `effect-in-closure` | (d) #161 | stay rejected | — |
| `for-break-value`, `for-data-gen-loop`, `for-free-bound`, `for-generated-origin`, `for-value-held`, `gen-break-outside`, `gen-from-elem`, `gen-return-held`, `take-failing`, `io-for-undetermined` | (d) loop, totality and generator typing | stay rejected | — |
| `borrow-escapes`, `array-view-escape`, `aff-outlives`, `aff-bound` | (d) outlives | stay rejected | The escaping value is used, so NLL does not help. |
| `two-mut`, `array-mut-while-viewed` | (d) exclusivity, core text | stay rejected | NLL is a surface elaboration and does not touch core programs. |
| `io-capability-*`, `io-def-capability`, `io-lend-misplaced`, `io-opaque-input`, `reuse-thunk`, `unused-thunk`, `aff-linear-state`, `surface-lend-mode`, `surface-borrow-place`, `rec-*`, `total-*` | (d) linearity, surface, recursion | stay rejected | — |

### 1.3 Passing programs

The rule rejects no passing program.

- **The search.** 40 non-reject, non-pending programs mix a suspension with a borrow (a grep
  for `yield|perform|handle|suspend` × `&|borrow|withbor|withload|lend`). I read the headers of
  the 11 closest: `core-effects-borrows`, `-reborrows`, `-borrow-abort`, `lend-lib-gen`,
  `lend-server`, `lend-pipeline`, `for-data-div`, `gen-div`, `axes/scope-codata-effects`,
  `clause-captures` and `effects-borrow-raise`.
- **Why none is newly rejected.** T1 already rejects every resuming operation inside a borrow's
  scope, so no passing program holds an internal lend across a resuming suspension. Every borrow
  in these programs is one of three kinds:
  - **Crossed only by aborts:** `core-effects-*`, `effects-borrow-raise`.
  - **Lent per observation:** `lend-lib-gen`, `lend-server`, `lend-pipeline`.
  - **Made outside the suspending computation:** `gen-borrowed`, `for-data-div`,
    `axes/scope-codata-effects`.
- **NLL** only shortens lends, so it can only add programs.

### 1.4 The effect model's programs (`docs/effect-model.md` §3.2, l.293–302)

| program | class | why |
|---|---|---|
| `retry` over a lent capability | (a) | The counter is lent from outside the `Fail` handler, and `raise` is abortive. |
| callbacks taking callbacks (`around`/`twice`, a logging wrapper) | (a) for the rule; (d) in borrow-core (#161) | `log` is an answering operation, so there is no suspension. |
| storing and returning a computation (`mk : Ctr ⇒ F (U[x] F int)`) | (a) for the rule; (d) #161 in the surface | The computation closes over an instance passed in from outside. |
| retry/timeout policy values | (a) | A timeout cancels its body, and no internal lend is involved. |
| a reader object (`next : Log`, `close : Fail`) over a lent counter | (a) | An "object holding a lend between method calls" is allowed when the lend is **outer**. |
| a recursion that logs and yields | (a) | There are no lends. |
| a generator holding a resource (push; pulled once; pulled to the end) | (a) | The resource is **owned** by a `using` frame. This is the `gen-cell` pattern. |
| no accidental handling | (a) | — |
| refusals "a suspended continuation holding a lend (T1)" and "the same, through a callback whose row yields" (§3.3) | (c) | These are exactly what the rule forbids, by design. |

### 1.5 Counts

- **Pending (22).**
  - Primary class: all 22 are (d).
  - Rule side: 19 (a); `gen-adapters-io` (a) at the kernel level, or (b) if the rule is read at
    the surface; `async-borrow` (a) under scoped spawning, otherwise (c); `print-borrowed-list`
    (c), or (b) at O(n²), in its generator form.
- **Rejects examined (52 of 64; the other 12 are plain ownership and naming rejects).**
  - Newly accepted by NLL: 2 (`gen-self-borrow`, `lend-let-used`), and probably a third,
    `lend-array-result` [unverified].
  - (b): 1 (`for-lend-resumes`).
  - Rule permits, but blocked by (d): 2 (`lend-iter-borrow`, `effect-try-lend`).
  - The rest stay rejected for unrelated reasons.
- **Passing.** None is newly rejected.
- **Effect model.** 8 programs (a); the 2 T1 refusals are (c) by design.

## 2. Practical programs from other languages

**Costs.**
- "Zero" means no extra copy, lookup, allocation or indirect call. A move of a value is words
  (BRIEF §1a, *Where values live*).
- "Threading" means the value is moved into the call and handed back in its result. That is what
  capabilities already do (`let stdin = for … in digits(stdin)`).
- On cancellation, a threaded value with a destructor is dropped. A destructorless one
  (a capability) hits K3.

| # | program (one line) | feature there | rule | rewrite and cost | how common |
|---|---|---|---|---|---|
| 1 | `let n = sock.read(&mut buf).await?` into a task-local buffer | Rust `async fn` state machine holding `&mut` of its own local across `.await` (self-referential future; `Pin`); C# `await s.ReadAsync(byteArray)` (GC array; `Memory<T>` allowed across `await`, `Span<T>` not) | (c) as written | (b) owned-buffer API: `let (n, buf) = sock.read(buf).await`. This is exactly the shape of tokio-uring, monoio and glommio (`read_at(buf, pos) -> (res, buf)`), which take it for completion I/O because a cancelled lent buffer is unsafe [unverified details]. Runtime: zero. API: every I/O call returns its buffer. | Very high: every tokio program (`AsyncReadExt::read`, `read_exact`, `read_to_end(&mut vec)`). |
| 2 | `async fn read_frame(&mut self)` doing `self.stream.read_buf(&mut self.buffer).await` | Rust `async fn` on `&mut self`; tokio `AsyncRead::poll_read(Pin<&mut Self>, &mut ReadBuf)`; mini-redis `Connection` [unverified exact code] | the method's own `self` is outer and fits; the field reborrows `&mut self.stream` and `&mut self.buffer` are lends opened inside and held across `.await`: (c) | (b) **move** the outer borrow's parts into the callee and have them handed back (`let (s, b, n) = read_buf(s, b).await`), instead of reborrowing. Runtime: zero. API: callees return the borrows they take. Implicit reborrow `&mut *x` is exactly what cannot cross an `await`. | Very high in hand-written protocol and codec code. |
| 3 | `let mut conn = connect().await; conn.send(x).await; conn.recv().await` | calling `&mut self` async methods on a task-local object (any language with methods) | (c): each call lends `conn` across the callee's `await` | (b) threading: `conn = conn.send(x).await`. Runtime: zero. Cancel: `conn` is dropped (destructor) or is a capability (K3). | Very high: every client library. |
| 4 | `let (a, b) = join!(fetch(&cfg), store(&cfg)).await` inside a task | Rust `futures::join!`/`tokio::join!`, `thread::scope`; Swift `async let` with a `borrowing` `~Escapable` argument [read, SE-0446]; Kotlin `coroutineScope { launch { … } }` (GC) | (a) at the root, when the scheduler runs inside the borrow (`async-borrow.bc`'s scoped design). (c) inside a task: the parent's own lend spans its `await` | (b) copy `cfg` into each child, or thread it through one child and back (serialises the children), or share by refcount (Rc/Arc, deferred). Cost: a copy per child, or lost concurrency, or a refcount. | High in Rust async services; it is the "scoped task" pattern. |
| 5 | `let g = m.lock().await; g.push(fetch().await)` | `tokio::sync::Mutex` guard across `.await`; Kotlin `mutex.withLock { suspend… }`; C# `await sem.WaitAsync()` (no borrow) | (c) if the guard is a lend; but the language has no interior mutability (decision: open) | (b) an owned guard (tokio `lock_owned`, `Arc`-based; deadpool/bb8 pool objects are owned): needs a refcount. Or an actor owning the resource (a queue per message). Or reorder, so the value is fetched before the lock. Cost: a refcount or a queue; reordering is zero. | Moderate; tokio's docs steer the async mutex to I/O resources such as a DB connection [read in passing; unverified quote]. |
| 6 | `for w in v.windows_mut(3) { w[1] = w[0] + w[2] }` | a lending iterator (`LendingIterator` via GATs; crates `streaming-iterator`, `lending-iterator`, `gat-lending-iterator`) | (c) as a generator: each yielded window is a reborrow that must end at the next resume | (b) push form, a lending loop that lends each window to a body (`lib/lend.bc` `array_each_imm` is the `imm` instance), or an index loop with a per-turn borrow. Runtime: zero. Lost: adapters (`map`/`zip`) over it. **Disjoint** `chunks_mut` fits as written: the generator owns the rest of an outer `mut` view and splits a piece off each turn (SPEC §16 table, "a view `array_mut`"). | Low: Rust's std has no `windows_mut` for this very reason, and the filtering lending iterator is also blocked by NLL problem case #3 [read]. |
| 7 | A streaming tokenizer yielding `&[u8]` slices of its own refilled buffer | Python generator yielding `memoryview` slices of a reused `bytearray` (dynamic `BufferError` on resize); Go `bufio.Scanner.Bytes()` (valid until the next `Scan`, a pull method) | (c) as a generator | (b) three options. (i) Pull-call API: `scan(&mut sc)` then `bytes(&sc)`, a function returning a reborrow of its argument, with no suspension (fits as written; Rust's `BufRead::fill_buf`/`consume`, quick-xml `read_event_into(&mut buf)` and csv `read_byte_record(&mut rec)` take this shape). (ii) Push callback (zero). (iii) Yield owned copies (a memcpy per token; Rust's `BufRead::lines` does this). Zero-copy over a **whole outer input** (nom, logos, serde_json `&'de str`, httparse over the caller's buffer) fits as written for arrays and buffers: the generator holds the outer view and yields leaf views at its lifetime [unverified that a generator can yield `imm 'x` views today; `gen-borrowed` yields copies]. | High in parsers; the dominant APIs already take one of the fitting shapes. |
| 8 | `while let Some(row) = rows.next()? { use(row.get_ref(0)?) }` with rows borrowed from the cursor | rusqlite `Rows::next() -> Option<&Row>` (not an `Iterator`); SQLite `sqlite3_step`/`sqlite3_column_text` (valid until the next step); JDBC `ResultSet` | (c) as a generator; (a) as a pull-call API | (b) push `query_map(\|row\| …)`, or map each row to owned values (usually done anyway; sqlx `fetch` streams owned rows). Cost: copies of the fields kept. | High usage, low loss. |
| 9 | Lazy in-order traversal of a borrowed tree or list (`for x in tree.iter()`) with a stack of node borrows | Rust `BTreeMap::iter`, `LinkedList::iter`, hand-written `Iter<'a> { stack: Vec<&'a Node> }`; Python/C#/Kotlin recursive generators (GC refs) | (c) **in our calculus**. Rust's `&'a` hops keep `'a`, but here each pointer hop from an `imm 'a` borrow is a `withload` at a shorter lifetime opened by the traverser (fact 3), so the stack of node views is a stack of internal lends held across `yield` | (b) with a real cost. (i) Keep only the outer root borrow and a path or index, and re-descend at each step: O(n²) for a list, O(n·depth) for a tree. (ii) Push form via `fold_imm` with a per-element effect: O(n), but today it is blocked (`print-borrowed-list` l.7–11, K4). (iii) Flatten to an array first: a copy. | Very high in Rust (every collection's `iter`); this is #57's shape. |
| 10 | `dict[k, default: []].append(x)` | Swift `_modify`/`yielding mutate`, a yield-once coroutine lending internal storage [read, SE-0474] | (c) as a coroutine | (b) a function returning a reborrow (`get_mut(&mut d, k)`), or a callback `modify(&mut d, k, \|v\| …)`. Runtime: zero. Swift itself is adding non-coroutine `borrow`/`mutate` accessors because a coroutine-lent value lives strictly shorter than its base [read]. | Pervasive inside Swift's stdlib; rarely user-written. |
| 11 | `auto& slot = cache[k]; co_await io(); slot = v;` | C++20 coroutines holding a reference across `co_await` (unchecked, a known dangling-reference bug source [unverified frequency]) | (c) | (b) look up again after the `await`, or compute first and then borrow. Cost: one extra lookup, or zero if reordered. | Common in C++ async code [unverified]. |
| 12 | An actor `async fn handle(&mut self, m)` holding `self.map.entry(k)` across `fetch().await` | Rust actors (actix, hand-rolled tokio tasks); Swift actors | (c): an internal reborrow of the outer `self` across `await`. **Swift also forbids** actor-isolated `inout` across `await` [read, SE-0306] | (b) `let v = fetch().await; self.map.entry(k).or_default().push(v)`. Cost: zero (reordered), or one extra lookup. | Moderate. |
| 13 | An HTTP handler holding `&req.headers()["auth"]` across `db.check(tok).await` | axum/actix handlers (mostly owned extractors: `String`, `Json<T>`, `Bytes`) | Request passed in by the framework: outer, fits. The header lookup is a pointer hop, an internal lend (fact 3): (c) | (b) copy the header value (a few bytes), or look it up again after the `await`. | Low: frameworks hand handlers owned data. |
| 14 | A NumPy generator yielding `arr[i:i+k]` views of an array it allocated | Python views into generator-owned storage | (c) | (b) yield copies, or a push callback, or `sliding_window_view` (one view object, not a generator: fits). | Moderate in numeric code [unverified]. |
| 15 | A `gen`/`sequence`/`Seq`/C# iterator over **owned** state (`counter` holding a cell, `using` resource) | Kotlin `sequence {}`, OCaml `Seq` via effects, C# `yield return`, Rust `gen` blocks | (a) | — (`gen-cell.bc`, the effect model's generator holding a resource). | Very high. |
| 16 | A struct `Parser<'a> { input: &'a str }` stepped by method calls (or one that owns a buffer and holds `&` into it) | Rust structs with lifetime parameters; the self-referential version needs `ouroboros`/`self_cell` | outer borrow: (a). Own-buffer self-reference: (c) | Self-reference is forbidden in Rust's safe core too; rewrite by owning and re-borrowing per call (`gen-cell`). Cost: zero. | Outer: very high (fits). Self-referential: rare. |

**Languages that forbid the same thing.**
- **C# 13** allows `ref` locals and `ref struct` locals (`Span<T>`) in async and iterator
  methods only when they are not live across an `await` or `yield return`. C# 12 and earlier
  forbade them in such methods entirely. [unverified wording; this is our rule almost verbatim.]
- **Rust `gen` blocks** reject a borrow of a local across `yield` [read, E0626].
- **Rust's `Iterator::next(&mut self)`** cannot lend from `self`, so std has no lending iterator
  [read].
- **Swift actors** may not pass actor-isolated state `inout` across `await` [read, SE-0306].
- **Swift's `_modify`** lends once and is always resumed. The lent value cannot outlive the access
  [read].

Only Rust `async` (through `Pin`, unproved) and unchecked C++ and Python allow the forbidden
shapes.

## 3. Verdict

**Corpus.**
- No passing program is newly rejected.
- NLL newly accepts 2 rejects (`gen-self-borrow`, `lend-let-used`), probably 3 with
  `lend-array-result` [unverified].
- Of the 22 pending programs, 19 are rule-neutral. 2 more (`gen-adapters-io`, `async-borrow`)
  fit under their intended reading: capability lends are moves; the scheduler runs inside the
  borrow. All 22 are blocked by something else, chiefly K3, #54, #161, #57 and #52.
- The rule's real exposure in the corpus is `print-borrowed-list`'s iterator (#57), whose
  generator form it rules out.
- Two programs the rule explicitly permits (`lend-iter-borrow`, and `async-borrow` with a `for`
  driver) are blocked today by "no lend spans a loop's observations". The rule's premise that
  outer borrows across suspensions "already work" holds only for hand-pulled stored generators
  (fact 2).

**Lost, with no zero-cost rewrite.**
- Lazy iteration over a **borrowed pointer-linked structure** (§2 row 9). In our calculus every
  pointer hop is a fresh, shorter lend opened by the iterator (SPEC §5 Open), so a generator's
  cursor is a lend across `yield`. The rewrites cost O(n²) / O(n·depth) re-descent, a copy, or
  push form, and push form is itself blocked today.
- Scoped concurrent children sharing a task-local `imm` (§2 row 4) when the parent is itself a
  task: copy, serialise, or refcount.
- Lending iterators and coroutine accessors (rows 6, 10) lose composability (adapters over them)
  but not speed.

**Rewritable at zero runtime cost, with an API-shape change.**
- Task-local buffers and objects across `await` (rows 1–3): owned-buffer and threading APIs, as
  in tokio-uring.
- Actor state across `await` and C++ references across `co_await` (rows 11–12): reorder, or one
  extra lookup.
- Streaming tokenizers and DB cursors (rows 7–8): pull-call APIs, which fit because a call
  returning a reborrow is not a suspension.
- Mutex guards (row 5): no interior mutability exists yet. An owned guard needs a refcount.

On cancellation, threaded values with destructors drop. Threaded capabilities meet K3, which is
already the blocker of four pending generators.

**The single most important loss.** Lazy, suspendable traversal of borrowed pointer-linked data:
`for x in iter(&list)` as a generator, #57. Rust gets this for free because `&'a` survives a
pointer hop. Here each hop opens a lend inside the iterator, and the rule then forbids holding it
across `yield`. The fallback is quadratic re-descent, a copy into an array, or a push-form fold
that is blocked today.

The **most frequent** loss is different: `x.op(&mut local).await` inside a task (rows 1–3). It
appears in nearly every async program, but it is rewritable by threading ownership at zero
runtime cost.
