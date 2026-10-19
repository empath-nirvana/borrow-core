# Expressiveness: what we cannot express, why, and how to unblock it (#587)

A design unit. It lists the functionality we want and cannot express today, groups it by the
blocker that stops it, gives every way to provide each blocked functionality (Rust's feature is one
way among several), ranks the blockers, and ends with a fixed, ordered list of build units. It
changes no code and no SPEC entry, and it files no issues.

Each claim is marked:

- **measured**: a run of `bcc check`, `bcc run` or `bcc-counts`, reproducible from §10;
- **recorded**: a refusal or a number already recorded in the repo (a `corpus/pending/` header, a
  `corpus/reject/` expectation, `bench/README.md`), cited;
- **by inspection**: read off SPEC or the code, with the section or line cited;
- **cited**: a published result, from `docs/research/` (its own verification marks carry over);
- **hypothesis**: argued here and not checked.

**The binary.** The worktree has no build. Every run used
`~/repos/borrow-core-c3c/.lake/build/bin/bcc` and `bcc-counts`, built from `57da9d0`
(C3c, the parent of `main` `6e3a661`'s merge), whose `lib/` is identical to this tree's (measured,
`diff -r`). Bench timings are not re-measured. They are `bench/README.md`'s (#537), taken before
C0–C3c, and are cited as recorded.

**The governing premise** (the user, 2026-10-19): the goal is not to rebuild Rust's borrow
checker; "a more limited borrow checker with linearity may be enough", and "maybe we have some
structures that can get sort of elaborated into something our borrow checker can reason about with
the right annotations/modes." So for each blocker, §4 asks first whether a higher-level structure,
plus a mode, elaborates into core terms the checker already accepts, and only then whether a new
rule is needed.

**Representation is not a blocker** (the user, 2026-10-19): "on the back end mut view being a swap is
sort of a lowering choice … the fact that the proof was represented that way doesn't mean we need
to compile it that way." So a cost that comes from how the kernel *represents* an operation (a read
through `mut` as two swaps, a write as a replace that drops the old value, a `while` as a driven
state machine) is filed in §5 as a lowering unit, not as an expressiveness blocker.

**Definition of done** (the user, 2026-10-19): no open-ended experimenting. §9 is a fixed list of
build units, each with the blocker it removes, acceptance programs from the target set, and a
one-line "done when". Spikes appear only with a yes/no question, the program they unblock, and a
kill criterion.

## 0. Summary

**Read §12–§15 first.** The target set was widened on 2026-10-19 (Are We Fast Yet, the Benchmarks
Game, Advent of Code, the north star end to end, Lox, data structures, concurrency). §12 is the
catalogue over it, §13 the ways for the new blockers B11–B17, §14 the re-ranking by programs gated,
and §15 the revised build units that end the document. The summary below is the first pass, kept
as written; where §14 and §15 differ from it, they hold.

**The widened set in brief** (§12):
- Nearly everything runs today in some shape. Every Are We Fast Yet program, every Benchmarks Game
  program and all 13 AoC ports run; the object-graph programs (Richards, DeltaBlue, Havlak, CD,
  LRU, the doubly linked list, both Loxes) run as arenas with integer handles.
- **Blocked outright**: the network (B11: no `Net` capability), and real parallelism (B12: no
  threads).
- **Blocked in the natural shape**: several tasks sharing a channel, cache or client (B1; the
  worker pool runs with a scheduler written in the program that serves the queue), aliased mutable
  graphs (B13), recursive data under arrays (B14), containers of `!` functions (B15).
- **Libraries, not language** (B16): pidigits and regex-redux run with a bignum and a Pike VM
  written in the program.
- **Ranked by programs gated** (§14): B7, B3, B2, B1, B11, B4, B10, B17 (the north-star tier), then
  B13, B16, B9, B14, B6, B8, B12, B15, B5.
- **New defects**: an assignment inside a `modify` block is lost silently (`(6, 0)` for `(6, 7)`);
  a callee's `let mut` name changes its caller's check.

**The first pass:**

**The target set** (proposed by the coordinator for the user; §1):
1. **North star**: `corpus/pending/operator-reconcile.bc`, and a JSON round-trip of a resource once
   data declarations exist.
2. **The 14 test programs** T01–T14 of `docs/research/mutation-paradigms.md` §4.
3. **The #537 bench rows**, within a bound against Rust that the user sets.

**The ten most important functionalities we cannot express**, each with its blocker (§2, §3):

| # | functionality | program | blocker |
|---|---|---|---|
| 1 | several interleaved tasks that each call one shared, stateful service (an API client, a cache, an output stream) | `operator-reconcile` (north star), `io-two-tasks`, `async-channel` | **B1** a capability is lent to one task for its whole life |
| 2 | a task, a handler body or a recursion whose loop is unbounded (`while`, a nested scheduler, a drain) | `operator-reconcile`, `async-fanout`, `async-stream`, `reject/rec-loop` | **B2** no handler wraps a div computation |
| 3 | a JSON-like document: a recursive value whose arrays and objects hold values, with named variants and fields | JSON round-trip (north star), T09, T11, n-body | **B3** no data declarations, and no nested recursion (`mu Y` inside `mu X` must be closed) |
| 4 | a stream or generator that reads from, or writes to, a capability it owns (decode a watch stream from a socket, yield lines of input) | `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io`; north-star stage 3 | **B4** a suspended computation cannot own a capability: a cancel hands nothing back |
| 5 | a generator over a borrowed input, consumed by a `for` inside the borrow (a tokenizer yielding views); a task that opens a borrow of its own state and keeps it across `await` while reading its other variables | `parse-recover-gen`, `async-bank`, T03's generator form | **B5** a borrow cannot be held across a resuming operation (T1, #172) |
| 6 | a function that takes two borrows and loops, or a call with two lends, or a `&mut` lend in a call that also uses a handler's service | `lend-div-two`, `lend-two`, T04, T09, T14 | **B6** one lend per call; one borrow per looping callee; §18's rows |
| 7 | nested loops, a lend in one arm of an `if`, a loop-local shadowing name, a recursive call inside a counted loop, a write to a captured `let mut` | #491–#493, #501–#503, #538, #586, T07, T12 | **B7** elaboration refusals (not missing mechanism) |
| 8 | a memo table or store generic in its value type, as a handler's state | `effects-generic-store`, `lc-0070-…-memo`, T06, T08 | **B8** no type parameters on an answering effect; map gaps |
| 9 | read a `mut` view's length or pass it to a callee that takes `imm`, and read one shared view twice | T04, T05, `quicksort`, `sum` | **B9** no `imm` reborrow of `mut` (#174); `imm` borrows not copied implicitly (#58/#142) |
| 10 | an error raised while a string or buffer is borrowed, handled outside the borrow; an early exit from a library fold | JSON parse errors, `config-parse`, `raise-in-fold` | **B10** abort across a buffer/literal borrow; K4 |

**The blockers, ranked** (§6): B2, B1, B7, B3, B4, B5, B6, B10, B8, B9. North-star blockers come
first; within them, the one whose fix is the deeper foundation comes first.

**The recommended way for each top blocker** (§4):

| blocker | recommended way | Rust's way? |
|---|---|---|
| B2 div under a handler | `Div` as a handled effect: S0's spike (#554, PR #562) and `Div` in the kernel (`bed4c8e`) have landed; what remains is #564's `handle_general` (a handler that keeps `κ` around a ticking body) and the surface's use of it | no: Rust has no totality to keep |
| B1 shared service across tasks | **a per-turn lend**: the scheduler owns the service and lends it to the task it resumes, for one turn, which hands it back at its `await`. It reuses §14's per-observation lend with the turn as the step, read as Balzer–Pfenning's acquire/release; that it needs no new lemma is a hypothesis, settled by spike S-B (§9) | no. Rust uses `Rc<RefCell<_>>` (run-time flag) or `Arc<Mutex<_>>`; ours is static and free on one thread |
| B7 elaboration refusals | the already-designed units: loops U2–U4, ergonomics E1, #586's write rule | n/a |
| B3 records, variants, nested data | data declarations (#489) whose nested containers **elaborate to one recursive type**, as Lean elaborates nested inductives into mutual ones | partly: Rust's enums and structs, without its `Box` ceremony |
| B4 suspended computations owning capabilities | the close-with-residual that S0 proved for loops ("unknown 2: the residual … proved", `experiments/DivEffect/README.md`: a loop closed early hands back its residual by a resume with `close`, not a cancel), applied to generators | no: Rust relies on `Drop`; we have no destructor for a capability |
| B5 borrows across a suspension | for tasks, **the lend split at each `await`** (measured: the split program runs `unconditional`, with no `PinLaw`); for generators, **a lending cursor**, whose state is owned (an index) and which is lent the source at each pull. The spanning lend K1 (#172) is not needed for the target set | Rust's own answer for generators is the same index cursor; its self-borrowing generators are not stable |

**The research threads** (§7): used — handler-owned state, SILL_S manifest sharing (as the reading
of the per-turn lend), the Links soundness hazard (as the check on it), the mutation report's
ownership-plumbing finding (B7), adjoint modes (B9's missing shift), explicit RC plus arenas (as
the alternative for unstructured sharing, outside the target set). Set aside, with reasons: codata
cells (#119, not needed by any target program), fork-join with a named assumption (threads are
outside the target set), the BoLo semantic seam for trusted primitives (no target program needs a
primitive the kernel cannot type).

**Surprises** (§8):
- The north-star program's real blocker is not the one its header names. With the `while`
  replaced by a bounded `for` and `spawn` by `spawn_in`, one task runs (measured). Three tasks are
  refused with "two tasks spawned in this block are given the capability of `Api`" (measured). So
  with B2 worked around, the north star meets exactly one more refusal: B1.
- A JSON-shaped value is expressible today when its arrays are encoded in the same `mu` (measured,
  `i32[7]`). The blocker is nested `mu` and naming, not recursion.
- An error escaping a borrow of a literal is refused, but the kernel already has the unwinding
  forms of slice borrows (`sliceBorrowIU`, SPEC §19). B10 is a surface gap.
- **All fourteen test programs run today**, T01 as written and thirteen with workarounds
  (measured, §2.2). Their gaps are elaboration refusals, sugar, records, and two calculus items
  (#174, #58); none is missing functionality.
- T13's Rust shape (a teller holding its account `mut` across `await` while reading its other
  variables) runs today, `unconditional` and with no `PinLaw`, when `main` lends the account to a
  task of `spawn_in` (measured); a borrow block opened inside the task runs once it is split at
  each `await` by hand (measured). Its blocker is elaboration, not T1.
- The per-observation lend that §14 already proves for loops is the mechanism B1 and B5 need for
  tasks and generators (hypothesis for B1 until spike S-B). One rule, three uses.

## 1. The target set, and how entries map onto it

The target set is the user's to adjust. Every catalogue entry in §2 names the target program that
needs it, or says **outside the target set**.

| target | what it needs from this document |
|---|---|
| `operator-reconcile.bc` | B2, then B1 (measured with B2 worked around, §8 item 1). Its other refusals were worked around in the file already (its header) |
| JSON round-trip of a resource | B3 (data declarations; nested recursion), B10 (a parse error raised across the input's borrow); maps of string keys exist (SPEC §36, `bench/wordcount`) |
| T01–T14 | B7 for most; B6 (T04, T09, T14), B3 (T09, T11), B8 (T06, T08), B9 (T04, T05), B5 (T03's generator form); see §2.2. All fourteen run today with workarounds (measured, §2.2) |
| the #537 bench rows | §5's lowering units only; B3's fixed-size records for n-body's last factor against Rust |

## 2. The catalogue

Each entry states what the program does, a program that needs it, whether it runs today and the
blocker. "Runs (shape)" means it runs only in a shape the language forces, named.

### 2.1 Functionality, grouped by blocker

**B1: interleaved tasks that share a stateful service.**

| functionality | program | today | target |
|---|---|---|---|
| reconcile several objects concurrently against one API client whose state (the observed cluster) all tasks read and update | `corpus/pending/operator-reconcile.bc` | refused at three tasks: "two tasks spawned in this block are given the capability of `Api`: a capability is lent to one task at a time" (measured, `op-a.bc`); one task runs (measured, `op-b.bc`) | north star |
| two tasks writing interleaved lines to one output | `corpus/pending/io-two-tasks.bc` | refused, the same message for `Stdout` (measured) | outside (the operator's logger is the same shape) |
| a producer and a consumer over a channel whose buffer a handler owns | `corpus/pending/async-channel.bc` | refused: `spawn`'s `top`-boxed `κ` cannot hold the channel's capability (measured) | outside |
| tasks that print progress through `main`'s stream | `corpus/pending/async-progress.bc` | refused: "the body of `with spawn` … lends a place declared outside it" (measured) | outside |
| a server keeping one cache shared by all connections, serving them interleaved | (no program; the operator's informer cache) | the same rule as the first row (by inspection, SPEC §34 *Tasks*) | north star stage 4 |
| a per-connection cache, each task owning its own | `corpus/async-bank-inbox.bc` | **runs** (recorded) | — |

**B2: an unbounded loop under a handler.**

| functionality | program | today | target |
|---|---|---|---|
| a task that loops until its object converges (`while have != want { … await() … }`) | `operator-reconcile.bc`, `op-e.bc` | refused, a type mismatch against `U (nu X. …)` (measured) | north star |
| a task that runs a scheduler of its own (fan-out to backends) | `corpus/pending/async-fanout.bc` | refused (measured) | outside |
| a task consuming a generator pipeline | `corpus/pending/async-stream.bc` | refused, cause 2 of 2 (recorded) | outside |
| a recursion whose body has a `while`; `with to_result { f(x) }` around a looping `f`; `main_div_error` around `main`'s loop | `reject/rec-loop.bc`, SPEC §21, §39, #517 | refused by design today (recorded) | outside |

**B3: named records and variants; recursive data that nests a container of itself.**

| functionality | program | today | target |
|---|---|---|---|
| a JSON document (null, numbers, strings, arrays of values, objects of named values) parsed, edited and printed | JSON round-trip | the nested type is refused: "`mu Y. …` must be closed" (measured, `json2.bc`); the same value with arrays inlined into one `mu` runs (measured, `json3.bc`) | north star |
| records with named fields updated in place (a configuration filled in steps; particles stepped) | T09, T11 | raw pairs only (SPEC §5; `data` refused, measured) | T09, T11 |
| a tree declared with constructors and walked by pattern | `corpus/pending/data-box-tree.bc` | refused at `data` (measured); its core form runs (recorded) | outside |
| bodies of a simulation as fixed-size records | `bench/n-body` | runs as 7 `f64`s per body in one array; 1.78× Rust, 1.16× C (recorded) | bench |

**B4: a suspended computation that owns a capability.**

| functionality | program | today | target |
|---|---|---|---|
| a generator that reads its input and yields digits, lines or tokens, then hands the input back | `gen-digits`, `gen-lines`, `gen-adapters-io` | refused: the iterator holding `ref input` "is live across a computation that may abort, and its type has no destructor" (measured) | north star stage 3 (a watch stream) |
| a generator that writes as it yields | `gen-lazy` | refused, the same for `ref output` (measured) | outside |

**B5: a borrow held across a resuming operation.**

| functionality | program | today | target |
|---|---|---|---|
| a tokenizer generator over a borrowed source, consumed by a `for` inside the borrow | `corpus/pending/parse-recover-gen.bc` | refused: "the iterator of this `for` holds the borrow of `v`" (measured); pulling by hand runs (`corpus/gen-borrowed.bc`, recorded) | T03 (generator form) |
| a teller task that opens a `mut` borrow of its own account and keeps it across `await` while reading its other variables | `corpus/pending/async-bank.bc` | refused by R1's closed-body premise (measured); **with the lend split at each `await` by hand it runs, `unconditional`, no `PinLaw`** (measured, `bank-split.bc`); with the account lent from outside to a task of `spawn_in`, it runs too (T13, measured) | outside (T13 runs) |
| an iterator over a borrowed list yielding its elements in order | `corpus/pending/print-borrowed-list.bc` (#57) | refused (measured: `iter` does not parse as a value) | outside |
| a function over a borrowed view whose helper loops (a text walker) | `aoc-2020-07`, `for-view-local` (#491) | refused, but this is B7: the source is untyped when the loop is classified (recorded) | — |

**B6: more than one lend at a call.**

| functionality | program | today | target |
|---|---|---|---|
| one call lending a borrowed separator and the output capability | `corpus/pending/lend-two.bc` | refused (measured: a type mismatch) | outside |
| a looping function that takes two borrows | `reject/lend-div-two.bc` | refused by design (recorded) | T04 (two-view form) |
| a buffer filled by a function that also uses injected services | T14 | `fill(&mut b)` refused under the services' `with`s (measured); a `borrow mut` outside them works (measured, §2.2) | T14 |
| one place lent `mut` twice to one call | `corpus/pending/two-writers.bc` | refused, as Rust refuses it (measured) | outside |

**B7: elaboration refusals** (each a filed issue; §4.3).

| functionality | program | today | target |
|---|---|---|---|
| nested loops where an inner loop is unbounded or a looping function is called per element (sieve's strike loop inside its passes; a scan inside a sort's outer loop) — written today as separate functions | `reject/while-in-counted-for.bc`, #503, `docs/loops.md` S1/S2 | refused (recorded) | T03, T04, sieve's forced shape |
| a loop that updates a collection only on some elements (append when a test passes) — the update is a lend in one arm | `for-in-if-lend` (#502), #538 | refused (measured) | T03, T06 |
| a loop body that reuses a name the enclosing code also uses (an innocent local shadowing an owner) | `loop-shadow-*`, `loop-handler-binder` (#493) | refused (measured) | quicksort's forced shape |
| backtracking: a loop over candidates that recurses, pushing and popping a path | `rec-in-for-linear`, `lc-0039` (#492) | refused (measured) | outside |
| a callback or block that updates a local of its caller (a visitor accumulating a sum) | #586 | **runs with a silent wrong answer** (recorded on the issue) | T12 |
| borrowing a value while already working inside another borrow, then using the outer value after | `borrow-nested-handback` (#495) | refused (measured) | outside |

**B8: generic stateful services.**

| functionality | program | today | target |
|---|---|---|---|
| a key-value store effect generic in its value type, used at two types | `corpus/pending/effects-generic-store.bc` | refused at the handler's syntax (measured) | T08 |
| top-down memoisation as a layer over a plain recursion | `corpus/pending/lc-0070-climbing-stairs-memo.bc` | refused: "no handler `memo`" (measured) | T08 |
| word frequency with one probe per word | T06, `bench/wordcount` | runs with two probes (`map_lookup` then `map_insert`), 1.24× Rust (recorded) | T06 |

**B9: views read through `mut`, and shared views used twice.**

| functionality | program | today | target |
|---|---|---|---|
| a sort over a `mut` view that reads the length and elements | T04, `bench/quicksort` | runs with `peek` and `len_mut`; 1.24× Rust (recorded) | T04 |
| a shared view read twice in a loop body | `bench/sum`, T05, `docs/loops.md` AA | runs with `array_copy` (recorded); `*r * *r` refused (recorded) | T05 |

**B10: an error across a borrow of text; early exit from a fold.**

| functionality | program | today | target |
|---|---|---|---|
| parse a number from a string, the error handled outside the string's borrow | `abort1.bc` | refused (measured); handled inside, it runs (measured, `abort2.bc`) | JSON round-trip |
| parse a configuration file with a block that raises, given to `fold_lines` | `corpus/pending/config-parse.bc` | refused (measured) | outside |
| a fold over a list whose algebra raises | `corpus/pending/raise-in-fold.bc` | refused (measured) | outside |

**Outside the target set, with their blockers** (recorded in their headers, measured still pending
§10.1): `backtrack-multishot` (multi-shot, not a goal), `noalloc` (allocation is not tracked),
`fold-under-u` (`X` under `U`, #182), `dig-bang` and `box-dup` (two kernel rules the model
validates), `lc-0208-trie-boxed` (a destructor for `mu` with `X` under `array`, #182; the arena form
is accepted), `closure-captures-int` (#9), `callbacks-in-data`, `map-div-fold`, `div-in-adapter`
(stored callbacks with rows, #161 B), `comp-param-*` (#487, ports), `closure-lend`, `lend-nested`
(#54), `div-answering-clause`, `state-machine-audit` (§14), `async-worker-pool`,
`async-borrow` (#52).

### 2.2 The 14 test programs, today

A subagent of this session wrote each of T01–T14 (`docs/research/mutation-paradigms.md` §4) in today's surface,
with the same behaviour, and ran it; I re-ran all fourteen (measured; programs in §11). **All
fourteen run with the right output.** T01 runs as written (bar `+=`); the other thirteen need a
workaround. So no T program is functionality we cannot express: each is a target for the *natural*
form, and its workarounds are what the units of §9 remove. The expected outputs printed in the
report for T01, T02, T07, T09 and T10 are correct; T08's and T14's were checked against Python.

| T | output today | workaround forced, and the message that forces it | blocker | allocs / indirect |
|---|---|---|---|---|
| T01 | `(220, (3, 10))` | none but `x = x + …` (no `+=`, E2 #583) and arrays built by `array_new` (no array literals) | sugar | 1 / 0 |
| T02 | `(3, (-1, (false, 2)))` | a lend inside an expression: "`&hy0_xs` lends a place to one call: it may appear only in the head `M` of `y <- M; N` (SPEC §11)"; hoisted with `let` | B7 (#525, #510) | 1 / 0 |
| T03 | `[12, -3, 40, 7]`, 1 | a looping function with a view parameter (§14 message); reads in `while` conditions; `push(&mut vals, …)` in an `if` arm inside a `while` ("`vals` is used twice", #502); `push(&mut v, if …)` does not parse | B7 | 2 / 0 |
| T04 | 6 swaps, sorted, reversed | `get` on `array_mut` refused, so `peek`; `len(&v)` at a `mut` view refused, so `len_mut`; a `while` over a `mut` view parameter (§14 message); `loop` inside a `for` (S1) | B9 (#174), B7, L-1 | 2 / 0 |
| T05 | `(3, (-1, (3, 4)))` | owned index reads by `at(&a, i, d)`, each let-bound; no tuple assignment; a shared view used in an inner `for` each row ("`cs` is used twice"), so `array_copy` | B9 (#58/#142), sugar | 12 / 0 |
| T06 | `the:3,cat:1,and:2,hat:1,bat:1` | two probes per word; a conditional `push_byte(&mut out, …)` heading `;` (§11); the per-word update moved into a function ("`hy0_freq` is used twice") | B8 (upsert), B7 | 4 / 0 |
| T07 | `Locked 3 2 1` | states as `bool` (no variants); `st = if …` does not parse; a `for` over a lent literal's view (§14 message), so an owned string | B3, B7 | 1 / 0 |
| T08 | best `(27, 112)`, 27 hits, 139 entries | state as a pair in `handler memo(mut s)`; assigning an outer `let mut` inside `with on_exhausted` refused ("a control handler's body may be abandoned"), so the budget handler is per call. Assigning inside the answering `with memo(&mut cache)` works | B8, B7 | 7 / 0 |
| T09 | `[10, 92, 55]`, 11 | a particle as a pair; one `modify` per element in place of field updates | B3 | 1 / 0 |
| T10 | `6765 2 3 1 21` | no tuple assignment; `p % q` in `main`'s `while` ("the type of the body `main_div_error` handles is not determined", #517), so `checked_rem` | sugar, B7 | 0 / 0 |
| T11 | `80 50 demo true`, 4000, 1 | the record as a nested pair, rebuilt per update | B3 | 2 / 0 |
| T12 | 52, 15, `[0..5]`, 9, 6 | #586 in two faces: a write-only assignment in a block is lost (12, not 52); one that also reads is refused with "`!thunk` promotes only over `!` types"; the state moved into an answering handler; the counter as a hand-built `Aff` | B7 (#586) | 4 / 0 |
| T13 | balances 130 and 20, refused `[0, 1]` | **the Rust shape runs**: `main` lends each account `mut` to a teller of `spawn_in` inside `borrow mut d { 'd, … }`; the teller reads its `txs` argument across `await`; `bcc trusted`: "unconditional" (measured). Only the hand-back of a nested borrow is by hand (#495). The report's shape, a borrow *block inside* the task spanning `await` while reading `txs`, is refused by R1 | B5 only for the block form | 30 / 6 |
| T14 | buffer `[49, 1, 37, 29, 24, 61]`, again 45, 1 log, sum 61 | `fill(&mut b)` inside the `with`s refused: "a place is lent (`&mut x`) in the arguments of `fill`, which also threads a capability: lend it in a call of its own"; `borrow mut b { v -> … }` *outside* the `with`s, with `fill` over an `array_mut` view, works | B6 (§18's row: an ordering constraint, not a missing capability) | 3 / 0 |


## 3. The blockers, exactly

| blocker | the exact reason | where it is decided |
|---|---|---|
| B1 | a capability is a `mut` borrow; a task of `spawn_in` is given it until it ends, so two tasks cannot both use it; a task of `spawn` cannot hold a borrow (`κ` boxed at `top`); a task's observations have the empty row, so it cannot perform an outer control effect | SPEC §34 *Tasks* (PROPOSED), §30 *Open*; `lib/async.bc:31`; measured `op-a`, `op-d` |
| B2 | a handler around a div computation is not provided | SPEC §21 *Open*; measured `op-e` |
| B3 | no `data` declarations; a `mu` nested in a `mu` must be closed; record fields and variants in place are limited | parser; SPEC §5 *Open*, §31 *Open*; #182, #32, #19; measured `json2` |
| B4 | `yield` is affine; what is live across it must drop; a capability has no destructor; a cancel answers `()` | SPEC §15 *Open*, §19 `[let]`; measured `gen-*` |
| B5 | a resuming operation cannot cross a borrow (T1); R1 relaxes it only for a body closed but for its view | SPEC §19 *Open* (T1, #172), §29; measured `parse-recover-gen`, `async-bank` |
| B6 | a call lends one place; a looping callee takes one borrow, re-lent each step; a lend in a capability-threading call, and a capability through `for … in &a`, are not provided | SPEC §14 *Open*, §18 *Not provided* and *Open* |
| B7 | elaboration decisions taken too early or by name (loop class before typing, threaded variables by name, assignments outside joins) | `docs/loops.md` §1; `docs/ergonomics.md` §7.1; #586 |
| B8 | no type parameters on an answering effect; no layer of its own state; map upsert and lookups at other lifetimes | SPEC §18 *Not provided*, §21 *Open*, §36 *Not provided* |
| B9 | no `imm` reborrow of a `mut` family (K2′); `imm` borrows are not copied implicitly | SPEC §9 *Open*, §16 *Open*; #174, #58, #142 |
| B10 | the surface has no unwinding form for a buffer's or literal's lend (the kernel does); a kernel fold cannot stop early | `Frontend/Sugar.lean:3910–3912`; SPEC §19 *As built*, §18 *Open* (K4); measured `abort1` |

## 4. Every way to provide each blocked functionality

For each blocker: the ways, then a table judging each way on four axes, then the elaboration
candidate (the user's "structure plus a mode"), then the recommendation.

- **Performance** is against Rust's equivalent, by construction: what the lowering emits, not what
  LLVM might recover.
- **Proof cost** is against the current calculus: *none* (pure elaboration into terms the checker
  already derives), *lemma* (one compatibility lemma for a new constant, as SPEC's entries add),
  *relation* (a change to the relation or the world, with FP and adequacy re-proved), *open* (no
  known route).
- **Ergonomics** is what the program reads like.

The full list of ways the brief names (Rust's feature, linear ownership transfer, threading,
handler-owned state, codata or generators, lexical lends, arenas, explicit RC, SILL-style shared
processes, structure plus modes) is judged in full at B1 (§4.2), where all of them bear. At the
other blockers a way that cannot provide the functionality is left out of the table.

### 4.1 B2: a div computation under a handler

**What fails.** "a handler around a div computation is not provided for any effect" (SPEC §21
*Open*). A task is `spawn`'s handled computation, so a task whose body has a `while` is refused
(measured, `op-e.bc`: a type mismatch against `U (nu X. F[…] …)`, the message #522 describes). The
same rule refuses `with to_result { f(x) }` around a looping `f`, a recursion whose body loops
(`reject/rec-loop.bc`), a scheduler inside a task (`async-fanout`), and `main_div_error` around a
loop of `main` (§39, #517).

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: no totality; every loop is a CFG loop; a handler is a function | parity | n/a: we would lose `total_every_run` | best | not available: totality is a theorem here (SPEC §13), and decision 67 makes `Div` an effect |
| **`Div` as a handled effect** (S0 #554 and `Div` in the kernel, landed; then #564's `handle_general`): a loop performs `tick`; a handler around a ticking body forwards the ticks; the runtime's driver is the outermost handler | parity once loops lower as loops (#540) | relation: S0 proved the tail-resumptive case (`handle_tail`); the general case, a clause that keeps `κ`, is #564's open proof (parametrised coinduction or step-indexing at ticks) | best: nothing is written | **recommended**; already planned |
| bound every task's loop (`for _ in 0..n { … break }`), as the measured variant does | parity | none | poor: an invented bound in every task | today's workaround |
| run the scheduler outside every handler, the tasks' services passed in | parity | none | poor: inverts the program | rejected: it moves B1, does not remove it |

**Elaboration candidate.** None is needed at the surface: the program already says what it means.
The structure is in the kernel's effect, which is where decision 67 put it.

**Recommendation.** Land #564 as planned, then lift the surface's restriction. Acceptance: `op-e.bc` (one task, `while`, a shared
service) runs; then `async-fanout` and `async-stream`'s second cause.

### 4.2 B1: several interleaved tasks sharing one stateful service

**What fails.** A capability (the state of an answering handler, `stdout`) is a `mut` borrow. A
task of `spawn_in` is *given* the capabilities its body uses, and holds them until it ends (SPEC §34
*Tasks*, PROPOSED). "Two tasks given one capability in one block are rejected" (measured, `op-a.bc`
and `io-two-tasks.bc`). A task of plain `spawn` cannot use them at all: `spawn`'s clauses box `κ` at
`top`, and a borrow does not outlive `top` (recorded, `async-channel`, `async-worker-pool`). Nor can
a task perform the service as control operations handled outside the scheduler: a `Task[A]`'s
observations have the empty row (`lib/async.bc:31`; measured, `op-d.bc`: "this computation performs
the operations `[3.0 …, 3.1 …]`, which are not within the row `[]` here").

What does work (measured or recorded): one task with one service (`op-b.bc`, the right answer);
one-way messages from tasks to the scheduler (`spawn_logged`, `corpus/async-logged.bc`); each task
owning its own state (`corpus/async-bank-inbox.bc`); read-only sharing (`async-workers-scoped.bc`).

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way, one thread: `Rc<RefCell<S>>` captured by each task | a count and a flag test per access | relation, and RC is opt-in only (memory, "no implicit RC") | good, with a run-time panic on overlap | not needed: our tasks only interleave at `await`, so overlap is decidable statically |
| Rust's way, threads: `Arc<Mutex<S>>` | a lock per access | relation (threads, #212) | good | later, for #212's lock-backed handlers; outside the target set |
| linear ownership transfer: the service is passed from task to task by hand | parity | none | poor: every task returns the service and the scheduler re-plumbs it | today's route for one shared service; `operator-rounds.bc` does it synchronously |
| handler-owned state served by the scheduler (an actor): tasks send requests as operations of the scheduler's own effect; it answers from state it owns | one dispatch per request in the driver | lemma at most: the task type's observation takes the answer, an argument without `X` (§22) | fair: the service's ops become scheduler ops | a fallback; it needs a request-response task type, which `lib/async.bc` lacks (only `log`, one-way) |
| **per-turn lend** (the service lent to a task for one turn): the scheduler holds the capability; resuming a task lends it for that turn; the task hands it back at its `await`. This is SPEC §34 *Open*'s first option ("thread the capability through `await` … as a `for`'s site threads its variables") | parity: the capability is a pointer argument of the resume, the state stays in the scheduler's frame | none or lemma (hypothesis, §9's spike S-B): the task type `box 'd U(νX. (Mut 'x S ⊸ F(Mut 'x S ⊗ (A + box 'd U X))) & F 1)` is an affine closure with an argument (§22), `'x` fixed at the `with` | best: the program as written in `operator-reconcile.bc` | **recommended** |
| SILL_S manifest sharing (Balzer–Pfenning, cited): shared and linear layers, acquire ↑ and release ↓ | parity on one thread | relation: a shared mode and shifts | good | used as the *reading* of the per-turn lend, not as new formers: acquire is the resume, release is the `await`, and the equi-synchronising condition (released at the type acquired) is "hands it back" |
| codata cells / #119 branded region | index arithmetic, no check | lemma plus the region-length Kripke fact (#119) | fair | not needed: the service is one value, not a graph of aliases |
| explicit RC | as Rust's `Rc` | relation | fair | outside the target set |

**The elaboration candidate.**
- *What the user writes:* `operator-reconcile.bc` unchanged: `with fake_api(&mut st) { … with spawn { reconcile(1, 3) } … run_until_empty(q) }`, the tasks calling `observed` and `update`.
- *What it elaborates to:* `spawn_with[S]`: a spawn whose clauses keep `κ` at `'d` (as `spawn_in`'s do) and whose task type takes the capability at each observation and answers it back with the step; `run_until_empty` threads the capability through every `resume`, as §32 threads a block's capabilities (`!U(C ⊗ A ⊸ F_Σ(C ⊗ B))`) and §15 a `for`'s variables through its site.
- *Which rule checks it:* §22's affine closure with an argument, §28/§32's BOXED-κ at `'d`, and §32's capability threading. The task never holds the borrow across `await`: it hands it back there. So T1 is not crossed, R1 and `PinLaw` are not used, and the Links hazard (Tang et al., cited: a handler dropping a continuation that holds a linear resource) does not arise, because a suspended task holds no lend.
- *Memory management at the surface:* none.

**Recommendation.** The per-turn lend. It is the strongest foundation of the options because it is
not a new mechanism: it is §14's per-observation lend (a borrow scope over a loop lends its place
again at each step) with the task's turn as the step. Its limit is stated: a task may not keep
anything borrowed from the service across `await` (a view into the cache). That is the honest form
of Rust's `RefCell` rule, checked statically. Threads come later through #212's lock-backed handler
of the same type.

### 4.3 B7: elaboration refusals

**What fails.** Programs the calculus accepts that the elaborator refuses or mis-elaborates. Each
has a filed issue and most have a designed unit (`docs/loops.md`, `docs/ergonomics.md`,
`docs/research/mutation-paradigms.md` D2).

| refusal | issue | unit |
|---|---|---|
| a `while` or a div call inside a counted `for`; a `for` in a `for` in some cells | #503, S1/S2 of `docs/loops.md` | loops U2 (#549) |
| a lend in an `if` arm off the spine; the same owner lent in both arms | #502, #538 | loops U3 (#550), J1 |
| a loop-local name shadowing a threaded variable | #493 | U3 |
| a `for` over a view that is not a typed parameter is taken to loop | #491, #501 | U2 |
| a recursive call inside a counted `for` threading an array | #492 | not predicted fixed by the loops units (`docs/loops.md` §1.4) |
| `return` from inside some nests; `loop`/`while` as values | S4, S10, S11 | U3, U4 (#551) |
| a write to a captured `let mut` is lost silently | #586 | the mutation report's D2: threaded or refused, never dropped |
| an assignment to a shadowing `let` reaches the `let mut` | #504 | D2's name-resolution clause (G1) |
| an owner borrowed inside another borrow block is not handed back | #495 | elaboration |
| `let mut` lent outside a call (the value place); `let (x, r) = f(x, …)` plumbing | #582 (E1, N1/N10) | ergonomics E1 |

The ways here are not alternatives: each is a bug in the elaborator against an accepted design. The
mutation report's finding is the one that bears on expressiveness. A quarter of corpus `let mut`
sites exist only to rebind a linear value a call hands back (its C16), and `f(&mut x)` already
removes most of them (149 of 177, `docs/ergonomics.md` §0). That plumbing is a symptom of B7 and
B6, not a missing paradigm.

**Recommendation.** Build the planned units in their planned order (U2 → U3 → U4, E1, D2). They
are the prerequisite for writing most of T01–T14 naturally (§2.2).

### 4.4 B3: records, variants and nested recursive data

**What fails.** The parser stops at `data` (measured, `data-box-tree.bc`: "expected a declaration
… found name `data`"). A recursive type inside another must be closed (measured, `json2.bc`: "`mu
Y. …` must be closed: it mentions an enclosing type variable"), so `mu X. … List[X] …`, the natural
JSON value, is not a type. Fields of a borrowed record are lent only when every other field is
affine, and variants in place are open (SPEC §5 *Open*, #19). n-body has no fixed-size arrays
(#72, #496), which is where Rust's 1.56× over C comes from (recorded, `bench/README.md`).

What works (measured): the same document with arrays encoded in the one `mu` (`json3.bc`, `i32[7]`,
`live 0`), as raw sums and pairs.

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `enum`/`struct`, `Box` and `Vec` for recursion | the layout Rust has | n/a | good, with `Box` ceremony | adopt the declarations, not the `Box`: SPEC §35 already places one box per node by the elaborator |
| **data declarations elaborating to `mu` and pairs/sums** (#489, #54 stage 8), with nested containers elaborated to one recursive type: `Arr(List[Json])` becomes the container's constructors inlined into `Json`'s `mu`, and the container's functions specialised at it | one box per node, as today | none for the declarations (the core types exist); for nesting, none if the inlining is done by the elaborator (hypothesis), lemma-level if instead the kernel lifts "must be closed" (#182, #32) | good | **recommended**. Lean 4 reduces nested inductive types to mutual ones the same way (prior art from background knowledge, not verified this session; our encoding of mutual recursion is one `mu` with a tag) |
| kernel nested `mu` (#182 item 2, #32) | the same | relation: folds beyond `FShape` | good | the fallback if the elaboration's specialisation of library containers does not hold |
| fixed-size arrays (#72) | constant trip counts, as Rust's `[T; N]` | relation (sized types) | good | for the bench, after records; outside the north star |

**Elaboration candidate.** *Writes:* `data Json = Null | Num(i64) | Str(string) | Arr(List[Json]) |
Obj(List[string * Json])`. *Elaborates to:* `mu X. 1 + (i64 + (string + (A_X + O_X)))` with `A_X`,
`O_X` the list's `1 + (X * Y)` unfolded into fresh summands of the same `mu`, and `List[Json]`'s
uses specialised to it. *Checked by:* the existing `mu`, folds at `FShape`, §35's box per node.
*Memory at the surface:* none.

**Recommendation.** Data declarations first without nesting (T09, T11, n-body's bodies), then the
nesting elaboration, behind the yes/no spike S-D (§9).

### 4.5 B4: a suspended computation that owns a capability

**What fails.** "`io_it1`, of type `U (iter u8 (ref input) (ref input))`, is live across a
computation that may abort, and its type has no destructor" (measured, `gen-digits`, `gen-lines`,
`gen-adapters-io`; `gen-lazy` for `ref output`). `yield` is affine, so what is live across it must
drop; a capability has no destructor and must be handed back; a cancel answers `()` (SPEC §15
*Open*). North-star stage 3 is this shape: a watch stream decoded from a socket the stream owns.

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: the iterator owns the handle; `Drop` closes it | parity | n/a: a capability has no destructor by design (§12) | good | not available as is |
| give the capability a destructor | parity | lemma; changes §12's class 3 | fair: a dropped stream silently closes the input | rejected: the user's linear-obligation goals (#209, #210) want the capability back |
| **close hands back a residual**: cancelling the generator resumes it with `close`, and it returns what it owns | parity | lemma or less: S0 proved it for loops (unknown 2, `experiments/DivEffect/README.md`); generators need the same close at their `yield`'s observation | best | **recommended**: one mechanism with B2 |
| a `linear ctl` iteration effect (no `break`) | parity | lemma | poor: no early exit | a fallback named by SPEC §15 |
| pass the capability per pull (the per-turn lend of B1) | parity | none or lemma (as B1) | fair | the same mechanism as B1; good where the consumer owns the capability anyway |

**Elaboration candidate.** *Writes:* `for b in digits(&mut stdin) { … break … }`. *Elaborates to:*
a stored generator whose `close` observation answers its residual (`ref input`), which the `for`'s
exit hands back to the lender. *Checked by:* the residual close S0 proved (`Residual.lean`), carried to a generator's `close` observation. *Memory at the surface:*
none.

### 4.6 B5: a borrow held across a resuming operation

**What fails.** T1 (#172): "only an abortive operation crosses a borrow's scope" (recorded,
`reject/gen-self-borrow.bc`, `reject/for-lend-resumes.bc`); "the iterator of this `for` holds the
borrow of `v`" (measured, `parse-recover-gen`); R1 under `PinLaw` relaxes it for tasks whose
borrow body is closed but for its view (SPEC §29), which `async-bank` is not (measured: "this
borrow block's body uses `n`, which is outside it").

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `Pin` and borrows across `await`; self-borrowing generators are not stable Rust | parity | open: K1, the spanning lend (#172), has no model ("does not close in this model") | good | not for the target set |
| R1 widened (a body that reads other variables) | parity | assumption: `PinLaw` grows | good | possible for `async-bank`; it enlarges an asserted fact |
| linear ownership transfer: pass the owned value in and out (`async-bank-inbox`'s shape) | parity | none | fair | works today |
| lend from outside: the spawning scope lends the place to a task of `spawn_in`, which holds the borrow as a parameter across `await` (SPEC §34 *Tasks*) | parity | none | good | works today, `unconditional` (measured, T13 §2.2); the form to teach |
| **lending cursor**: a generator whose state across `yield` is owned (an index, a stack of indices) and which is lent its source at each pull; what it yields lives for that pull | parity: Rust's hand-written cursor is the same code | none if the generator is elaborated to a step function `(S, view) → (Tok 'v, S)` (hypothesis); lemma if it stays a stored generator, since its observation's argument is lifetime-polymorphic (§22 *Open*) | good | **recommended** for parsers and tree walks |
| **lend split at each suspension** (the per-turn lend inside one task): a borrow block whose body awaits is elaborated as one lend per turn, ended before each `await` and opened again after it, when nothing borrowed from the view is live across the `await` | parity | none: the split program is accepted today, `unconditional`, with no `PinLaw` (measured, `bank-split.bc`) | good: the program as written in `async-bank.bc` | **recommended** for tasks; it also shrinks what R1 and `PinLaw` must cover |

**Elaboration candidate.** *Writes:* `fn tokens<'a>(src: text 'a) -> … with Yield[Tok 'a]` and
`borrow imm s { v -> for t in tokens(v) { … } }`. *Elaborates to:* when no variable live across a
`yield` but the source itself holds the borrow, the generator's body becomes a step function over
its owned live set, and the `for` a counted or drain loop that lends `v` at each step (§14's
per-observation lend). *Checked by:* §14 and ordinary function typing. *Memory at the surface:*
none. *Limit:* a yielded view cannot be kept past its pull: a lending iterator, not Rust's
`Iterator<Item = &T>`. A generator whose live set holds a sub-view across `yield` is still T1.

**The task form, measured.** `async-bank.bc` with its `borrow mut acct { … }` moved inside the loop,
around each transaction, so that it ends before the `await`, runs with the answer its header
expects, `inr ((i32[130], i32[0]), inr ((i32[20], i32[1]), inl ()))`, and `bcc trusted` reports
"typing: unconditional … unproved boundaries: 0" (§10.2). So for tasks, the elaboration is: a
borrow block whose body suspends is split at each suspension point, by the live variables U3
computes (`docs/ergonomics.md` §3.4's inferred extent, applied at `await`). *Checked by:* the
ordinary borrow rules; no relaxed lend. *Limit:* a view, or a value borrowed from it, that is live
across the `await` keeps the program under R1 or T1.

### 4.7 B6: lends per call

**What fails** (recorded, SPEC §14 *Open*, §18 *Not provided*): a call lends at most one place
(`lend-two`); a looping callee takes one borrow, re-lent at each step (`reject/lend-div-two.bc`); a
`&mut` lend in the arguments of a call that threads a capability; a capability through a `for` over
`&a`. Two live `mut` borrows of one place (`two-writers`) are refused, as in Rust.

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: any number of disjoint borrows per call, checked by NLL | parity | n/a | good | the target, for disjoint places |
| **nested lends at the call**: `f(&mut a, &b)` elaborates to `withbor2 a (λm. withbor1 b (λi. f(m, i)))`, both hand-backs threaded through the result | parity | none (the lends exist; hypothesis that the hand-back threading is the only missing piece, as `lend-two`'s header says) | good | **recommended** (#54) |
| per-step re-lend of a tuple of places (lifts `lend-div-two`) | parity | lemma: §14's rule at a pair of cells, as `withborF2` is at a pair | good | **recommended**, after a spike on the lemma |
| §18's rows (a lend in a capability-threading call; a capability through `for … in &a`) | parity | none (hypothesis): T14 runs today with the `borrow mut` moved outside the services' `with`s (measured, §2.2), so the elaborator can place the lend there itself | good | **recommended** (the mutation report's O7) |
| contraction `Mut ⊸ Mut ⊗ Mut` | — | relation | — | rejected, as Rust rejects it |

### 4.8 B10: an abort across a buffer or literal borrow; early exit from a kernel fold

**What fails.** `with to_result { borrow imm "12x" { v -> parse_i32(v) } }` is refused: "this
borrow block's body performs an abortive operation, and its place (a buffer or a literal) has no
unwinding form here: not provided" (measured, `abort1.bc`). With the handler inside the borrow it
runs (measured, `abort2.bc`). The kernel already has the slice borrows' unwinding forms
(`sliceBorrowMU`, `sliceBorrowIU`, SPEC §19 *As built*); the refusal is the surface's
`unwindingC?` (`Frontend/Sugar.lean:3910–3912`, by inspection). K4: a `raise` in a kernel fold's
algebra (`config-parse`, `raise-in-fold`) needs the fold to stop (#178).

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `?` returns through the borrow; the borrow ends at the return | one branch per level | n/a | good | ours matches it once the surface emits the unwinding form |
| **emit the existing unwinding form** for buffer and literal lends | one branch, as Rust | none (hypothesis: the literal and buffer lends are slice lends) | good | **recommended** |
| the elaborator catches inside and re-raises after the hand-back | one branch | none | good | the fallback if the above fails |
| K4: `fold_lines` over `count_try` (it is a `count_fold` today); `fold_own`/`fold_imm` with an exit | `count_try` exits the loop | none for `fold_lines` (a library change); lemma for the μ folds (#178) | good | `fold_lines` now; μ folds outside the target set |

### 4.9 B8: generic answering effects and the memo layer

**What fails** (measured): an answering effect with a type parameter (`effects-generic-store`:
the message is the handler syntax); the `memo` layer (`lc-0070`: "no handler `memo` is declared").
SPEC §36 *Not provided*: lookup by a key at another lifetime than the map's, `entry` (one-probe
upsert), `get_mut`.

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: a generic struct with `&mut self` methods; `entry` | parity | n/a | good | adopt `entry`'s functionality, not its type (`entry_or` returning `(map, mut slot)` was refuted by the mutation report: the owner cannot move while lent) |
| **type parameters on answering effects, instantiated per instance** (as generic functions are, decision 45) | parity (monomorphised) | none (hypothesis: an instance is an ordinary answering effect) | good | **recommended**, as part of #489 |
| a one-probe upsert as a closure-taking operation, `update_with(&mut m, k, d, f)` | one probe | none | good | **recommended** (library) |

### 4.10 B9: `imm` reborrow of a `mut` view; implicit copies of `imm`

**What fails** (recorded): an `imm` reborrow of a `mut` family is not provided (SPEC §9 *Open*,
K2′, #174); a shared view or `imm` borrow is not copied implicitly (#58, #142; `*r * *r` refused,
`docs/loops.md` §3). Under the user's clarification, the *cost* of reading through `mut` (two swaps)
is a lowering question (§5). What remains here is expressiveness: passing a `mut` view to a callee
typed `imm`, reading `len` of a `mut` parameter, and using one shared view twice.

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `&*v`, `&T: Copy` | parity | lemma (#174 `axWithborMITy`, "does not compose as stated"; the missing shift is the aff→unr pair of the adjoint mode table, `experiments/Shifts`) | good | the target |
| **#58: insert `copy` where an `imm` borrow is used twice** | free (a pointer) | none (`copy` exists) | good | **recommended** |
| `mut`-taking variants of read-only callees (`len_mut`, today) | parity | none | fair | the fallback if #174's spike is killed: the "more limited borrow checker" of the premise |

## 5. Costs that are lowering choices, not blockers

The user's clarification: a cost that comes from the kernel's representation of an operation is a
lowering question. These are the bench rows' gaps, from `bench/README.md` (recorded) and
`bcc-counts` (measured at `57da9d0`). None needs a kernel or borrow-calculus change. Each needs a
lowering rule, and where the rule relies on a law, a proof of that law over Core.

| cost | where it shows | representation | lowering | its justification | unit |
|---|---|---|---|---|---|
| a read through a `mut` view is two swaps (`peek`, `modify m { x -> (x, x) }`) | quicksort 1.24×, sort-generic 1.29×; `bcc-counts` quicksort `loads 87529 stores 83522` (measured): a store per read | `withswap` / `slice_replace_mut` | a load, when the contents are persistent | the lens laws (get-put, put-get) for one location; a derived node on the typed term ("contents persistent"), as C2b's `divLit` is, and an erasure-pass rule with its proof over Core | L-1 |
| a write is a replace that drops the old value | n-body, prefix | `array_replace`, `swapField` | a store, when the old value is persistent (its drop is a no-op) | put-put plus "drop at a persistent type is the identity" | L-1 |
| `while`, `loop` and a generator's body run as a driven state machine | sieve 5.63×, chain-yield 2.10×, chain-gen 21.5× (recorded) | `ν` / `delay` codata, one observation per turn | a native loop wherever the turn does not suspend | #540 (L2b); under S0, `tick`'s clause is tail-resumptive, so the loop is a direct loop (`docs/pipeline-architecture.md` §0) | L-2 (#540) |
| bounds checks at every access | n-body 1.78× (1.16× of C), quicksort, sieve-for | `idx` checks | none where the index is the loop's own counter over the view's length | #213 item 2; a typed fact (the counter is below `len`), carried on the typed term | L-3 |
| addresses as `inttoptr` integers; `malloc + 8` alignment | sum 1.88× (not vectorised) | flat IR words | `getelementptr` from a pointer base; 16-byte aligned arrays | backend only (`bench/repro/vectorize.ll`) | L-4 |
| the `Exhausted` pass-through rebuilds the sum | gen-tree 1.72×, gen-tree-cb 1.96× | `case r { inl x → inl x \| inr e → inr e }` | the callee's words passed through, so the call is a tail call | an identity on sums | L-5 |
| `i32` in 8-byte slots | quicksort footprint | one word per scalar | 4-byte slots | layout | L-6 |
| handler state loaded and stored per operation | handlers-di (at parity already) | the state's cell | the state in a register for the `with`'s extent | `noalias` from the borrow invariants (#531) or scalar replacement by a law | L-7 |

The mutation report's O6(b), "a kernel read through `mut`", is therefore not needed for
performance (L-1 gives it). #174 stays, as expressiveness (B9).

Rows that already beat Rust or sit at parity (recorded): binary-trees 0.40×, gen-tree-dyn 0.04×
(against `Box<dyn Iterator>`), async-tree 0.84×, handlers-di-generic 0.54×, matmul, mandelbrot,
spectral-norm, chain-for, prefix, raise-large.

## 6. Ranking

Ordered by how much functionality each blocker gates, north star first, then by how good a
foundation its fix is. Every count is from §2.

| rank | blocker | gates (target set) | gates (outside) | foundation quality of the recommended fix |
|---|---|---|---|---|
| 1 | B2 div under a handler | north star (first cause) | `async-fanout`, `async-stream`, `rec-loop`, #517 | high: decision 67's plan; S0 landed, #564 is the remaining proof; S0's residual also serves B4 |
| 2 | B1 shared service across tasks | north star (second, and last, cause) | `io-two-tasks`, `async-channel`, `async-progress` | high: §14's per-observation lend reused; no new former (hypothesis until spike S-B) |
| 3 | B7 elaboration refusals | T02, T03, T07, T12, most bench "forced shapes" | 13 pending programs (#491–#495, #501–#504, #538, #586) | high: the designs exist and are agreed |
| 4 | B3 data declarations, nested data | JSON round-trip (north star stage 1), T09, T11, n-body | `data-box-tree`, every `inl`/`inr` site (2197, `docs/ergonomics.md` M1) | high: pure elaboration if spike S-D holds |
| 5 | B4 suspended computations owning capabilities | north-star stage 3 (watch stream); not in `operator-reconcile` | `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io` | high: the same mechanism as S0's residual |
| 6 | B5 borrows across a resuming operation | T03 (generator form) | `parse-recover-gen`, `async-bank`, `print-borrowed-list` (#57) | medium: the cursor is elaboration; K1 stays open and is not needed |
| 7 | B6 lends per call | T04, T09, T14 | `lend-two`, `lend-div-two` | high for nested lends (elaboration); medium for the tuple re-lend (a lemma) |
| 8 | B10 abort across buffer borrows; K4 | JSON parse errors | `config-parse`, `raise-in-fold` | high: the kernel forms exist |
| 9 | B8 generic answering effects | T06, T08 | `effects-generic-store`, `lc-0070` | high: monomorphisation as decided for functions |
| 10 | B9 `imm` reborrow, `imm` copies | T04, T05 | `quicksort`'s `array_copy` | #58 high; #174 medium (a lemma that "does not compose as stated") |

## 7. The research threads

| thread | source | used where | or set aside, and why |
|---|---|---|---|
| handler-owned state | mutation report D5; #119's comment | B1 (the scheduler owns the service), B8 | — |
| SILL_S manifest sharing | session-types report §6 | B1: the per-turn lend read as acquire (resume) / release (`await`), equi-synchronising | its shared *layer* and shift formers are set aside: no target program needs a type-level shared mode once the lend is per turn |
| codata cells | mutation report G4; #119 | named as B1's alternative | set aside for the target set: no target program has aliased handles into one region. Kept for graphs and observer lists |
| the BoLo semantic seam (a trusted or library primitive proved semantically against the relation, as DRFCaml's capsules and RustBelt's `Cell`) | modes report §1, §8 | — | set aside: every recommended fix is typed by existing rules or one compatibility lemma; no target program needs a primitive outside the calculus |
| adjoint modes | graded-adjoint report §3; `experiments/Shifts` | B9: #174 is the missing aff→unr shift of the mode table | the full adjoint re-presentation is set aside: it is a reframing with no target program behind it |
| explicit RC plus arenas | #94, #119 comment, `docs/prior-art-memory-model.md` | B1's comparison column | set aside for the target set; arenas already work as library code (`corpus/leetcode/trees/0208-implement-trie.bc` is accepted) |
| fork-join with a named assumption | #212's scoping (Route 0) | — | set aside: threads are outside the target set. The per-turn lend is designed so that #212's lock-backed handler can serve the same task type |
| the Links soundness hazard | session-types report §9 (Tang et al., POPL 2024) | B1 and B4: the per-turn lend holds no lend at a suspension, and the residual close hands back every linear resource, so no handler can drop a continuation that holds one | — |
| the ownership-plumbing finding | mutation report C16 | B7 (E1, N1/N10) | — |

## 8. Surprises

1. **With B2 worked around, the north star meets one more refusal.** `operator-reconcile.bc`'s header names "a task
   whose loop is a `while`" and "a task performing an answering effect handled outside its
   `spawn`". With a bounded loop and `spawn_in` under a unit cell's scope, one reconcile task runs
   and gives the right answer (measured, `op-b.bc`). Three are refused because "a capability is
   lent to one task at a time" (measured, `op-a.bc`). So the second cause is not lifetimes or
   rows: it is sharing.
2. **Tasks cannot perform outer control effects at all.** `Task[A]`'s observations have the empty
   row (`lib/async.bc:31`; measured, `op-d.bc`). The actor route therefore needs a new task type
   too; it is not free today.
3. **JSON's blocker is naming and nesting, not recursion.** A value whose arrays live in the same
   `mu` runs (measured, `json3.bc`); `mu Y` inside `mu X` is refused (measured, `json2.bc`).
4. **B10 is a surface gap.** The kernel has `sliceBorrowIU`/`MU` (SPEC §19); the surface refuses
   to use them for literals and buffers.
5. **All of T01–T14 run.** The mutation report graded several "X" (refused); each has a working
   form today (§2.2). T14's §18 row is an ordering constraint: the same buffer lent by a
   `borrow mut` outside the `with`s is filled through a function that performs both services.
6. **T13's Rust shape needs no relaxed lend.** `async-bank.bc` with the lend split at each `await`
   runs, and `bcc trusted` reports it `unconditional` (measured, `bank-split.bc`).
7. **One rule, three uses.** §14's per-observation lend (a borrow scope over a loop is lent again at
   each step, so the loop's state must not hold it) is the mechanism B1 (per turn) and B5 (per
   pull) need. Neither needs K1.
8. **The read-through-`mut` cost is visible only before LLVM.** quicksort's `bcc-counts` shows a
   store per read (measured), while its machine code has single loads (recorded,
   `bench/README.md`). That is why L-1 is a lowering law, not a calculus change.

## 9. Build units (first pass, superseded by §15)

A fixed, ordered list. Each unit names the blocker it removes, its acceptance programs (each added
to the corpus with its golden, from the target set where one applies), and when it is done. Spikes
are marked; each has a yes/no question, the program it unblocks, and a kill criterion, and each
ends in a build unit or a documented limit, never in further research. Every unit that changes
which programs are accepted gets its SPEC entry first, and the algebra hard stop applies.

**Track 1: the north star.**

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 1 | **`handle_general`** (#564, on S0 and `Div` in the kernel, landed): a handler that keeps `κ` around a ticking body, and the surface's §21 restriction lifted | B2 | `op-e.bc` (one reconcile task with `while`, a shared service; §10.2) as `corpus/operator-one-task.bc`; `async-fanout`; `async-stream`'s second cause | `operator-one-task` runs with its golden, and SPEC §21 *Open*'s "a handler around a div computation" is removed |
| 2 | **spike S-B**: yes/no — is a task type whose observation takes the service `Mut 'x S` and answers it back, `box 'd U(νX. (Mut 'x S ⊸ F(Mut 'x S ⊗ (A + box 'd U X))) & F 1)` with `'x` fixed at the `with`, derivable from §22's affine closure with an argument and §32's capability threading, with no new compatibility lemma? | B1 (decides its form) | `operator-reconcile.bc` written against a hand-built `spawn_with` in core text | **yes**: unit 3 as designed. **Kill** (a new lemma or relation change is needed): unit 3 builds the actor route instead (a request-response task type, one lemma at §22), with the same acceptance |
| 3 | **the per-turn lend** (`spawn_with`): a scheduler that owns a service and lends it to each task for one turn; the surface `with h(&mut s) { … with spawn { … } … }` elaborates to it when a task uses `h`'s capability | B1 | `corpus/pending/operator-reconcile.bc` (golden `[3, 4, 2]` and the converged cluster, from its header), `io-two-tasks.bc`, `async-channel.bc`, `async-progress.bc` | `operator-reconcile.bc` moves from `pending/` to `corpus/` with its golden, and SPEC §34 *Open*'s "concurrent writers" is removed |

**Track 2: the elaboration units already designed** (they come before most of T01–T14 read as
intended).

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 4 | **loops U2, U3, U4** (#549, #550, #551) as `docs/loops.md` plans them | B7 (loops) | `docs/loops.md` §5's matrix; `for-in-if-lend`, `for-view-local`, `for-view-effect-copy`, `for-buf-borrow`, `loop-shadow-*`, `loop-handler-binder`; T02, T07, T10 | `docs/loops.md` §5.1's programs run, and the listed pending programs move to `corpus/` |
| 5 | **ergonomics E1** (#582) and **the write rule** (#586, #504) as the mutation report's D2 specifies (threaded or refused, never dropped; name resolution; the abort column G2) | B7 (writes, plumbing) | T01, T03, T12 (1) and (2) with 52 and 5102; the stored-thunk case in `corpus/reject/`; `borrow-nested-handback` (#495) | every #586 form gives its D2 answer or its D2 refusal, and no corpus output changes except those listed |

**Track 3: data and JSON** (north-star stage 1).

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 6 | **data declarations** (#489 part 1, #54 stage 8): records and variants elaborating to pairs, sums and `mu`, constructor patterns, field access and field update through `mut` | B3 (names) | T09, T11; `data-box-tree.bc`; n-body's bodies as records | T09 and T11 run as written in the mutation report §4 (spellings aside), and n-body's bench row is no slower |
| 7 | **spike S-D**: yes/no — does a declaration whose variant holds `List[Self]` elaborate to one `mu` (the list's constructors inlined, its functions specialised at the type) that today's checker accepts, with no kernel change? | B3 (nesting) | `data Json = … Arr(List[Json]) | Obj(List[string * Json])` with `len`, `map` and a fold over it | **yes**: unit 9 uses it. **Kill**: unit 9 takes kernel nested `mu` (#182 item 2, #32) as its own SPEC entry and proof |
| 8 | **aborts across buffer and literal borrows**: the surface emits `sliceBorrowIU`/`MU` for them; `fold_lines` over `count_try` | B10 | `abort1.bc` (§10.2); `config-parse.bc` | both run with goldens, and SPEC §18 *Not provided*'s "a borrow of a buffer or a literal crossed by an abort" is removed |
| 9 | **JSON round-trip**: a parser that raises on malformed input and a printer, in `lib/`, over unit 6's (and 7's) declarations | B3, B10 | `corpus/json-roundtrip.bc`: a Deployment-like resource parsed, its `replicas` changed, printed byte-for-byte; a malformed input raising across the input's borrow | the program runs with its golden at every stage and passes `scripts/falsify.sh` |

**Track 4: the rest of T01–T14.**

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 10 | **lends per call**: several lends in one call (nested, hand-backs threaded); a `&mut` lend in a call that threads a capability; a capability through `for … in &a` (§18's rows) | B6 | `lend-two.bc`; T04, T14 (`fill(&mut buf)` under the RNG and logger handlers) | those run, and §14 *Open*'s "a call lends at most one capability" and §18's two rows are removed |
| 11 | **spike S-E**: yes/no — is §14's per-step re-lend at a pair of cells one compatibility lemma by the single cell's proof (as `withborF2` is to `withbor2`)? | B6 (looping callees) | `reject/lend-div-two.bc`'s program | **yes**: build it, and the program moves to `corpus/` (hard-stop item 2 applies: a `reject/` program changes). **Kill**: "a looping callee takes one borrow" stays, documented in SPEC §14 as a limit |
| 12 | **#58 implicit copies of `imm`**, with `array_imm` views (#142) after the user's decision on `reject/double-use-in-callee.bc` (`docs/loops.md` §3, E2) | B9 (copies) | T05; `quicksort` and `sum` without `array_copy`; the loops matrix's AA cell | those run with goldens and counts unchanged |
| 13 | **spike S-F** (#174): yes/no — does `axWithborMITy` follow from the anti-frame and a variant of `wpTS_I_frameX` whose `hQ` is stated at the drop step (#174's proposed route)? | B9 (reborrow) | T04 with `len(&v)` at an `array_mut` parameter | **yes**: build K2′, `len`/`at` through `&*v`. **Kill**: `mut`-taking read functions (`len_mut`) are the API, documented as the premise's limited checker |
| 14 | **generic answering effects and the map's upsert**: type parameters on answering effects, instantiated per instance; `update_with(&mut m, k, d, f)`; the `memo` layer | B8 | T06, T08; `effects-generic-store.bc`; `lc-0070-climbing-stairs-memo.bc` | those run with goldens; SPEC §18's "type parameters on an answering effect" is removed |

**Track 5: suspended computations** (north-star stage 3, outside `operator-reconcile`).

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 15 | **close with a residual** for generators, on S0's residual (unit 1) | B4 | `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io` | all four move to `corpus/` with goldens |
| 16 | **lend split at suspensions** (tasks): a borrow block whose body awaits is one lend per turn, by U3's live variables | B5 (tasks) | `corpus/pending/async-bank.bc` as written; T13 in the report's shape (the borrow block inside the teller) | `async-bank.bc` moves to `corpus/` with its golden and `bcc trusted` reports it `unconditional` |
| 17 | **spike S-C**: yes/no — when no variable live across a `yield` holds the borrow except the source parameter, does the generator elaborate to a step function over its owned live set that the checker accepts inside the source's borrow block, unchanged? | B5 (generators) | `parse-recover-gen.bc` | **yes**: unit 18. **Kill**: the cursor stays hand-written (`corpus/json-tokens.bc`'s shape), documented as the way |
| 18 | **the lending cursor**: that elaboration | B5 | `parse-recover-gen.bc`; T03's generator form | both run with goldens |

**Track 6: lowering** (the bench rows; independent of tracks 2–5, except L-2 after unit 1).

| # | unit | acceptance | done when |
|---|---|---|---|
| L-1 | reads and writes through `mut` at persistent contents as loads and stores: a derived node on the typed term, an erasure-pass rule, and its proof over Core | quicksort, sort-generic, prefix; `bcc-counts` stores per read drop to 0 | each row within the user's bound |
| L-2 | div loops as loops (#540) | sieve, chain-yield, chain-gen | the same |
| L-3 | bounds checks removed where the index is the loop's counter | n-body, sieve-for, quicksort | the same |
| L-4 | pointer addressing and aligned arrays | sum | the same |
| L-5 | the `Exhausted` pass-through as a tail call | gen-tree, gen-tree-cb | the same |
| L-6 | 4-byte `i32` slots | quicksort footprint | the same |
| L-7 | handler state in a register for a `with` | handlers-di | the same |

**Order.** 1, 2, 3 (the north star runs); 4, 5; 6, 7, 8, 9 (JSON); 10–14 (T01–T14); 15–18. Unit 16 may run any time after 4 (it needs U3). The
lowering track runs beside them, L-2 after 1. Nothing here is open-ended: every spike ends in a
build unit or a documented limit.

**Outside the target set** (no unit here): interior mutability and graphs (#119, #94; arenas work
as library code); threads (#212); multi-shot search; allocation tracking (`noalloc`); folds with
`X` under `U` (`fold-under-u`); digging and same-lifetime boxing (`dig-bang`, `box-dup`); a trie
whose nodes own arrays of children (`lc-0208-trie-boxed`, #182); a borrowed list's iterator (#57);
K1 itself (#172).

## 10. Reproduction

Binary: `B=~/repos/borrow-core-c3c/.lake/build/bin/bcc` (built from `57da9d0`; `lib/` identical to
this tree's). Every program below was run with `$B run FILE` (or `$B check`), and the last lines of
the output are quoted.

### 10.1 Every `corpus/pending/` program, today

`for f in corpus/pending/*.bc; do $B check $f | head -1; done`, first line of each, cut at 160
characters (measured; every one is still refused):

```
aoc-2020-07.bc: aoc-2020-07.bc:34:1: `words` loops, so it is called in direct style one step at a time, and a borrow at `'t` cannot stay open acr
async-bank.bc: async-bank.bc:32:17: this borrow block's body uses `n`, which is outside it, and performs the operation 1.0, which resumes: a borr
async-borrow.bc: async-borrow.bc:41:12: expected `[`, found name `l`
async-channel.bc: async-channel.bc:65:21: the clauses box `κ` at `top`, so the handled computation's context must outlive it: `fx_c10`, of type `
async-fanout.bc: async-fanout.bc:30:16: this argument of `push` has type `i32 * (mu X. 1 + ((mu X1. 1 + i32 * X1) + box top U (nu X. F ((mu X. 1 
async-progress.bc: async-progress.bc:39:19: the body of `with spawn` assigns a `let mut` variable declared outside it, or lends a place declared 
async-stream.bc: async-stream.bc:35:4: `sensor` performs `Exhausted`, which its written row does not list
async-worker-pool.bc: async-worker-pool.bc:46:51: `clone` copies a persistent value, and `U (delay (mu X. 1 + i32 * X))` is not persistent
backtrack-multishot.bc: backtrack-multishot.bc:34:1: expected a declaration (`type`, `shape`, `def`, `fn`, `extern`, `effect`, `handler` or `main
borrow-nested-handback.bc: borrow-nested-handback.bc:16:3: `q` is used twice here, and its type `array u8 * i32` is not persistent
box-dup.bc: box-dup.bc:30:63: `boxed['a]`: `x`, of type `box 'l0 i32`, is used inside, and it cannot be shown to outlive `'a`
callbacks-in-data.bc: callbacks-in-data.bc:28:52: type mismatch: expected `!(i32 => i32)`, but this has type `!(i32 => U (delay i32))`
closure-captures-int.bc: closure-captures-int.bc:28:41: `!thunk` promotes only over `!` types, but `n`, of type `i32`, is used inside
closure-lend.bc: closure-lend.bc:42:11: `let (x, y) = V` needs a `*` type, but `V : ref output`
comp-param-capability.bc: comp-param-capability.bc:13:56: the computation parameter `g` uses the capability of `Counter` and is called inside `wi
comp-param-for.bc: comp-param-for.bc:14:3: a `for` over a call of a computation parameter of `any`: not provided (its loop's variables would be t
comp-param-two-sites.bc: comp-param-two-sites.bc:11:65: `with to_result` serves `Fail` for a call of the computation parameter `f`, which is call
config-parse.bc: config-parse.bc:277:5: an operation of `Fail` is performed inside a closure or block that is not run in place, and no handler of
data-box-tree.bc: data-box-tree.bc:23:1: expected a declaration (`type`, `shape`, `def`, `fn`, `extern`, `effect`, `handler` or `main`), found na
dig-bang.bc: dig-bang.bc:22:65: expected `thunk`, `thunkv` or `{` after `!`, found name `x`
div-answering-clause.bc: div-answering-clause.bc:10:3: the clause `add` of `shares` performs an operation of `Fail`: a clause of an answering han
div-in-adapter.bc: div-in-adapter.bc:17:29: an operation of `Fail` is performed inside a closure or block that is not run in place: it cannot rea
effects-generic-store.bc: effects-generic-store.bc:31:9: `assoc`: an answering handler is `handler h(mut s: S): E = { op(x) = e; … }` (or `handle
fold-under-u.bc: fold-under-u.bc:34:8: the type of the closure's parameter `o` is not determined here: pass it where a function type is expected,
for-buf-borrow.bc: for-buf-borrow.bc:16:55: the iterator of this `for` holds the borrow of `v`: a borrow block over a loop lends its place again 
for-in-if-lend.bc: for-in-if-lend.bc:15:3: `a` is used twice here, and its type `array i32` is not persistent
for-view-effect-copy.bc: for-view-effect-copy.bc:16:1: `show__wasi_stdout_cell` loops, so it is called in direct style one step at a time, and a 
for-view-local.bc: for-view-local.bc:14:1: `count` loops, so it is called in direct style one step at a time, and a borrow at `'a` cannot stay op
gen-adapters-io.bc: gen-adapters-io.bc:16:56: `io_it1`, of type `U (iter u8 (ref input) (ref input))`, is live across a computation that may abor
gen-digits.bc: gen-digits.bc:18:27: `io_it1`, of type `U (iter u8 (ref input) (ref input))`, is live across a computation that may abort, and its
gen-lazy.bc: gen-lazy.bc:22:5: `o`, of type `ref output`, is live across a computation that may abort, and its type has no destructor: an abortiv
gen-lines.bc: gen-lines.bc:23:18: `io_it1`, of type `U (iter u8 (ref input) (ref input))`, is live across a computation that may abort, and its t
io-two-tasks.bc: io-two-tasks.bc:22:11: two tasks spawned in this block are given the capability of `Stdout`: a capability is lent to one task at
lc-0039-combination-sum.bc: lc-0039-combination-sum.bc:58:28: in this `case`, `out` is consumed in the `inr` arm but not in the `inl` arm
lc-0070-climbing-stairs-memo.bc: lc-0070-climbing-stairs-memo.bc:38:32: no handler `memo` is declared before this `with`
lc-0208-trie-boxed.bc: lc-0208-trie-boxed.bc:97:56: `io_d23` is not consumed in its scope, and its type `(1 + (mu X. (1 + 1) * array (1 + X))) + 
lend-nested.bc: lend-nested.bc:33:38: type mismatch: expected `i32`, but this has type `ref array i32 * i32`
lend-two.bc: lend-two.bc:31:14: type mismatch: expected `ref output`, but this has type `imm 'io_lb31_3 i32`
loop-handler-binder.bc: loop-handler-binder.bc:18:3: `e` is used twice here, and its type `array_imm 'a u8` is not persistent
loop-shadow-linear.bc: loop-shadow-linear.bc:21:5: `w` is used twice here, and its type `array_imm 'a i32` is not persistent
loop-shadow-owner.bc: loop-shadow-owner.bc:17:42: type mismatch: expected `array u8 * i32`, but this has type `i32`
map-div-fold.bc: map-div-fold.bc:60:93: type mismatch: expected `i32`, but this has type `U (delay i32)`
noalloc.bc: noalloc.bc:30:1: expected a declaration (`type`, `shape`, `def`, `fn`, `extern`, `effect`, `handler` or `main`), found name `noalloc`
operator-reconcile.bc: operator-reconcile.bc:97:34: type mismatch: expected `mut 'fx_rl134 ((mu X. 1 + (i32 * i32) * X) * (1 + 1)) * i32`, but th
parse-recover-gen.bc: parse-recover-gen.bc:136:7: the iterator of this `for` holds the borrow of `v`: a borrow block over a loop lends its place 
print-borrowed-list.bc: print-borrowed-list.bc:37:12: expected a value, found `iter`
raise-in-fold.bc: raise-in-fold.bc:70:69: `sum_alg` performs `Fail` and is passed as a value: it can only be called (effectful callbacks, #161)
rec-in-for-linear.bc: rec-in-for-linear.bc:19:20: in this `case`, `a` is consumed in the `inr` arm but not in the `inl` arm
state-machine-audit.bc: state-machine-audit.bc:72:1: this borrow block's result has type `mut 'fx_l_audit (i32 * i32 * i32) * i32`, which has the
two-writers.bc: two-writers.bc:42:9: `io_lm42_3` is used twice here, and its type `mut 'io_lb42_3 output` is not persistent
```

### 10.2 The probes

**`op-a.bc`, `op-b.bc`, `op-e.bc`: the north star.** Each is `corpus/pending/operator-reconcile.bc`
lines 1–77 (everything before `fn reconcile`), then:

```bc
-- variant A: bounded for with break, spawn_in under a unit cell's scope inside the handler
fn reconcile(name: i32, want: i32) -> i32 with Async, Api =
  let mut updates = 0;
  for i in 0..10 {
    let have = observed(name);
    if have == want { break };
    let ok = with to_result { try_update(name, toward(have, want)) };
    match ok { inl u -> updates = updates + 1 | inr e -> () };
    await()
  };
  updates

fn desired() -> List[Obj] = cons((1, 3), cons((2, 0), cons((3, 2), nil())))
fn initial() -> List[Obj] = cons((2, 4), nil())

main -> List[i32] * List[Obj] =
  let st = alloc((initial(), true));
  let d = alloc(());
  let (d, counts) = with fake_api(&mut st) {
    let counts = borrow mut d { 'd, e ->
      let q = queue_in[i32]();
      let q = push_in(q, with spawn_in { reconcile(1, 3) });
      let q = push_in(q, with spawn_in { reconcile(2, 0) });
      let q = push_in(q, with spawn_in { reconcile(3, 2) });
      with on_exhausted(!{ u -> nil() }) { run_in(q, 20) } };
    (d, counts) };
  let _ = free(d);
  let (cluster, c) = free(st);
  (counts, cluster)
```

`op-a.bc` gives `op-a.bc:97:18: two tasks spawned in this block are given the capability of `Api`: a
capability is lent to one task at a time, which holds it until it ends (SPEC §34 *Open*)`.

`op-b.bc` is `op-a.bc` without the second and third `push_in` lines. It gives
`(inr (i32[3], inl ()), inr ((i32[2], i32[4]), inr ((i32[1], i32[3]), inl ())))` and `live 0`:
one task, three updates, deployment 1 at 3 replicas.

`op-e.bc` is `op-b.bc` with the header's `reconcile` (the `while`):

```bc
fn reconcile(name: i32, want: i32) -> i32 with Async, Api =
  let mut updates = 0;
  let mut have = observed(name);
  while have != want {
    let ok = with to_result { try_update(name, toward(have, want)) };
    match ok { inl u -> updates = updates + 1 | inr e -> () };
    await();
    have = observed(name)
  };
  updates
```

It gives `op-e.bc:99:42: type mismatch: expected `mut 'fx_gl60 (…) * i32`, but this has type `U (nu
X. F[4.0 aff 1 ~> 1, 4.1 aff i32 ~> 1] (…) & F[…] 1)``.

**`op-d.bc`: the service as control operations handled outside the scheduler.** `op-a.bc`'s
reconcile, with

```bc
effect Api {
  ctl observed(name: i32) -> i32;
  ctl update(name: i32, replicas: i32) -> bool
}

-- The replicas of `name`, or 0 when it is absent.
fn lookup(xs: List[Obj], name: i32) -> i32 =
  match unroll xs {
    inl u -> 0
  | inr (o, rest) -> let (n, r) = o; if n == name { r } else { lookup(rest, name) }
  }

-- `xs` with `name` at `r` replicas.
fn store(xs: List[Obj], name: i32, r: i32) -> List[Obj] =
  match unroll xs {
    inl u -> cons((name, r), nil())
  | inr (o, rest) ->
      let (n, q) = o;
      if n == name { cons((n, r), rest) } else { cons((n, q), store(rest, name, r)) }
  }

fn get_or_0(xs: List[Obj], name: i32) -> i32 = with on_exhausted(!{ u -> 0 }) { lookup(xs, name) }

fn put(xs: List[Obj], name: i32, r: i32) -> List[Obj] =
  with on_exhausted(!{ u -> nil() }) { store(xs, name, r) }

-- The cluster, and whether the next update of deployment 2 conflicts.
type Cluster = List[Obj] * bool

handler fake_api[A](mut st: Cluster): Api, A -> A * Cluster = {
  return(a) = (a, st);
  observed(name, k) = { let (xs, c) = st; let r = get_or_0(clone(xs), name); st = (xs, c); k(r) };
  update(name, replicas, k) = {
    let (xs, c) = st;
    if c && name == 2 { st = (xs, false); k(false) } else { st = (put(xs, name, replicas), c); k(true) }
  }
}
```

and

```bc
main -> List[i32] * List[Obj] =
  let r = with fake_api((initial(), true)) {
      let q = queue[i32]();
      let q = push(q, with spawn { reconcile(1, 3) });
      let q = push(q, with spawn { reconcile(2, 0) });
      let q = push(q, with spawn { reconcile(3, 2) });
      run_until_empty(q) };
  let (counts, cl) = r;
  let (cluster, c) = cl;
  (counts, cluster)
```

It gives `op-d.bc:45:50: this computation performs the operations `[3.0 aff i32 ~> i32, 3.1 aff
i32 * i32 ~> 1 + 1]`, which are not within the row `[]` here` (the position is in `lib/async.bc`,
printed under the user's file, #479's B11). The same with `spawn_in` under a unit cell's lend
(`op-c.bc`) gives the R1 message "the row of a relaxed lend's body has only operations that resume
once …".

**`json2.bc`, `json3.bc`: a JSON-shaped value.**

```bc
include rec
type Json = mu X. 1 + (i32 + (mu Y. 1 + (X * Y)))
type Arr = mu Y. 1 + (Json * Y)

fn sum(j: Json) -> i32 =
  match unroll j {
    inl u -> 0
  | inr v -> match v { inl n -> n | inr xs -> sum_list(xs) }
  }
fn sum_list(xs: Arr) -> i32 =
  match unroll xs { inl u -> 0 | inr (h, t) -> sum(h) + sum_list(t) }

fn num(n: i32) -> Json = roll inr (inl n)
fn arr(xs: Arr) -> Json = roll inr (inr xs)
fn acons(x: Json, xs: Arr) -> Arr = roll inr (x, xs)
fn anil() -> Arr = roll inl ()

main -> i32 =
  let inner = arr(acons(num(4), anil()));
  let j = arr(acons(num(3), acons(inner, anil())));
  with on_exhausted(!{ u -> 0 }) { sum(j) }
```

gives `json2.bc:2:31: `mu Y. …` must be closed: it mentions an enclosing type variable`.

```bc
-- JSON-like value with arrays encoded in the same mu: 0 null | 1 num | 2 end-of-array | 3 element(head, rest)
include rec
type Json = mu X. 1 + (i32 + (1 + (X * X)))

fn sum(j: Json) -> i32 =
  match unroll j {
    inl u -> 0
  | inr v -> match v { inl n -> n | inr w -> match w { inl e -> 0 | inr (h, t) -> sum(h) + sum(t) } }
  }

fn num(n: i32) -> Json = roll inr (inl n)
fn cell(x: Json, xs: Json) -> Json = roll inr (inr (inr (x, xs)))
fn end() -> Json = roll inr (inr (inl ()))

main -> i32 =
  let inner = cell(num(4), end());
  let j = cell(num(3), cell(inner, end()));
  with on_exhausted(!{ u -> 0 }) { sum(j) }
```

gives `i32[7]`, `live 0`.

**`abort1.bc`, `abort2.bc`: an error across a literal's borrow.**

```bc
include text
include fail
main -> i32 + ParseError =
  with to_result { borrow imm "12x" { v -> parse_i32(v) } }
```

gives `abort1.bc:4:20: this borrow block's body performs an abortive operation, and its place (a
buffer or a literal) has no unwinding form here: not provided`.

```bc
include text
include fail
main -> i32 =
  borrow imm "12x" { v -> with default(0 - 1) { parse_i32(v) } }
```

gives `i32[4294967295]` (that is, −1; `main`'s value is printed unsigned), `live 0`.

**`bank-split.bc`: the teller with its lend split at each `await`.**
`corpus/pending/async-bank.bc` with `teller` replaced by

```bc
fn teller(start: i32, txns: List[Txn], n: i32) -> i32 * i32 with Async =
  let acct = alloc(start);
  let mut refused = 0;
  let mut rest = txns;
  for _ in 0..n {
    match unroll rest {
      inl u -> rest = nil[Txn]()
    | inr (t, more) ->
        rest = more;
        let ok = borrow mut acct { a -> modify a { b -> match with to_result { apply(b, t) } { inl b2 -> (b2, true) | inr e -> (b, false) } } };
        if ok { () } else { refused = refused + 1 };
        await()
    }
  };
  (free(acct), refused)
```

gives `inr ((i32[130], i32[0]), inr ((i32[20], i32[1]), inl ()))`, `live 0`; `$B trusted
bank-split.bc` gives `typing: unconditional: a CDerives derivation (fundamentalC, adequacyD)` and
`unproved boundaries: 0`.

### 10.3 Counts

`bcc-counts bench/<b>/main.bc`, last line (measured):

```
sieve: allocs 4 indirect 0 copies 0 loads 3479 stores 2443 bounds 2475
chain-gen: allocs 2 indirect 0 copies 0 loads 27 stores 18 bounds 18
chain-yield: allocs 2 indirect 0 copies 0 loads 27 stores 18 bounds 18
quicksort: allocs 4 indirect 0 copies 0 loads 87529 stores 83522 bounds 85524
gen-tree: allocs 3 indirect 0 copies 0 loads 43 stores 34 bounds 36
handlers-di: allocs 6 indirect 0 copies 0 loads 1199 stores 1177 bounds 54
n-body: allocs 3 indirect 0 copies 0 loads 245285 stores 75092 bounds 245226
sum: allocs 4 indirect 0 copies 0 loads 2043 stores 1034 bounds 1036
```

The counts are at the default argument sizes and are not the timed runs.

## 11. Appendix: the T01–T14 programs as they run today

Each was run with `$B run FILE`; its output is in §2.2. The refused variants follow, with the
message each gives in its header or in §2.2. Each program's header comment names its workaround.

### `T01.bc`

```bc
-- T01: loop-carried accumulators over a borrowed array.
fn xs(i: i32) -> i32 =
  if i == 0 { 3 } else if i == 1 { 8 } else if i == 2 { 0 - 2 } else if i == 3 { 7 }
  else if i == 4 { 10 } else if i == 5 { 5 } else if i == 6 { 0 - 6 } else { 4 }

main -> i32 * (i32 * i32) =
  let xs = array_new[i32](8, xs);
  let mut sq = 0;
  let mut odd = 0;
  let mut best = 0 - 2147483647 - 1;
  for p in &xs {
    let x = *p;
    if x % 2 == 0 { sq = sq + x * x } else { odd = odd + 1 };
    if x > best { best = x } else { () }
  };
  (sq, (odd, best))
```

### `T02.bc`

```bc
-- T02: `break e` / `for … else`, and a `while` with a bare `break` and its variables read after.
include iters
include slice

fn xs(i: i32) -> i32 =
  if i == 0 { 4 } else if i == 1 { 1 } else if i == 2 { 0 - 3 } else if i == 3 { 9 }
  else if i == 4 { 2 } else { 8 }

fn first_over<'a>(xs: array_imm 'a i32, limit: i32) -> i32 =
  let mut acc = 0;
  for e in enumerate(elems(xs)) {
    let (i, p) = e;
    acc = acc + *p;
    if acc > limit { break i } else { () }
  } else { 0 - 1 }

main -> i32 * (i32 * (bool * i32)) =
  let xs = array_new[i32](6, xs);
  let mut i = 0;
  let mut all_pos = true;
  let n = len(&xs);
  while i < n { let x = at(&xs, i, 0); if x < 0 { all_pos = false; break } else { () }; i = i + 1 };
  let f10 = first_over(&xs, 10);
  let f100 = first_over(&xs, 100);
  (f10, (f100, (all_pos, i)))
```

### `T03.bc`

```bc
-- T03: a cursor as loop state, numbers pushed into an owned buffer by `&mut`.
-- Workaround: the input is an owned string (a `while` may not keep a view open across its
-- steps, SPEC §14), every read is `at(&s, …)` let-bound before its test (a lend may only head a
-- `let`), so each inner `while` with a read in its condition is a `loop` with `break`; and the
-- conditional push threads the buffer by hand (`push(&mut vals, x)` in an `if` arm inside a
-- `while` is refused: "`vals` is used twice here", cf. pending/for-in-if-lend.bc, #502).
include slice
include buf
include text
include io

fn is_digit(b: u8) -> bool = 48 <= b && b <= 57

fn parse(s: string) -> buf i32 * i32 =
  let (arr, n) = s;
  let mut arr = arr;
  let mut pos = 0;
  let mut vals = buf_new[i32](4);
  let mut errs = 0;
  while pos < n {
    loop { let c = at(&arr, pos, 0); if pos < n && c == b' ' { pos = pos + 1 } else { break } };
    let c = at(&arr, pos, 0);
    let neg = pos < n && c == b'-';
    if neg { pos = pos + 1 } else { () };
    let start = pos;
    let mut k = 0;
    loop {
      let c = at(&arr, pos, 0);
      if pos < n && is_digit(c) { k = k * 10 + to_i32(c) - 48; pos = pos + 1 } else { break }
    };
    let x = if neg { 0 - k } else { k };
    let (v, u) = if pos == start { errs = errs + 1; (vals, ()) } else { push(vals, x) };
    vals = v;
    loop { let c = at(&arr, pos, 0); if pos < n && c != b',' { pos = pos + 1 } else { break } };
    pos = pos + 1
  };
  (vals, errs)

main -> i32 =
  let (vals, errs) = parse(string_of_lit("12,-3, 40,x,7"));
  let (arr0, k) = vals;
  let arr : array i32 = arr0;
  for i in 0..k { let x = at(&arr, i, 0); print_dec(x); print_byte(b' ') };
  print_byte(b'\n');
  errs
```

### `T04.bc`

```bc
-- T04: insertion sort through a `mut` view, then reversing a copy in a `borrow mut` block.
-- Workarounds: the view is threaded (`v = …`) rather than lent per call; reads through it are
-- `peek` (`get` needs `array_imm`, and there is no imm reborrow of a `mut` view); its length is
-- `len_mut`; the inner `while` is a counted `for` with `break` (a looping function may not
-- hold a view across its steps, SPEC §14, and `loop` may not sit in a `for` body); the copy is an `array_new` reading the sorted array with `at(&a, …)`.
include slice
include io
include buf

fn a0(i: i32) -> i32 =
  if i == 0 { 5 } else if i == 1 { 2 } else if i == 2 { 9 } else if i == 3 { 1 } else if i == 4 { 5 } else { 6 }

fn insertion_sort<'a>(v: array_mut 'a i32) -> array_mut 'a i32 * i32 =
  let (v, n) = len_mut(v);
  let mut v = v;
  let mut swaps = 0;
  for i in 1..n {
    let mut j = i;
    for _ in 0..i {
      let (w, x) = peek(v, j - 1, 0);
      let (w, y) = peek(w, j, 0);
      v = w;
      if j > 0 && x > y { v = swap_at(v, j - 1, j); swaps = swaps + 1; j = j - 1 } else { break }
    }
  };
  (v, swaps)

fn print_arr(a: array i32, n: i32) -> array i32 =
  for i in 0..n { let x = at(&a, i, 0); print_dec(x); print_byte(b' ') };
  print_byte(b'\n');
  a

main -> i32 =
  let mut a = array_new[i32](6, a0);
  let swaps = borrow mut a { v -> let (v, s) = insertion_sort(v); discard_mut(v); s };
  let mut b = array_new[i32](6, !{ i -> 0 });
  for i in 0..6 { let x = at(&a, i, 0); b = array_set(b, i, x) };
  let mut lo = 0;
  let nb = len(&b);
  let mut hi = nb - 1;
  borrow mut b { v ->
    let mut v = v;
    while lo < hi { v = swap_at(v, lo, hi); lo = lo + 1; hi = hi - 1 };
    discard_mut(v) };
  let a = print_arr(a, 6);
  let b = print_arr(b, 6);
  swaps
```

### `T05.bc`

```bc
-- T05: dynamic programming on owned arrays: coin change, and LCS with two rows swapped by name.
-- Workarounds: each index read is `at(&a, i, d)` (a lend per read, let-bound), each write
-- `array_set` (`array_replace`); the coin view is copied per row (`array_copy`, #142: a view is
-- not persistent, so an inner `for` over it is refused: "`cs` is used twice here"); the row swap is three rebindings (no tuple assignment).
include slice
include buf
include text

def big : i64 = 9223372036854775807

fn min64(x: i64, y: i64) -> i64 = if x < y { x } else { y }
fn max(x: i32, y: i32) -> i32 = if x < y { y } else { x }

fn coins<'c>(cs: array_imm 'c i32, amount: i32) -> i64 =
  let mut dp = array_new[i64](amount + 1, !{ i -> big });
  dp = array_set(dp, 0, i64[0]);
  let mut cs = cs;
  for a in 1..amount + 1 {
    let (cs1, row) = array_copy['c, i32] cs;
    cs = cs1;
    for p in row {
      let c = *p;
      if c <= a {
        let prev = at(&dp, a - c, big);
        let cur = at(&dp, a, big);
        if prev != big { dp = array_set(dp, a, min64(cur, prev + i64[1])) } else { () }
      } else { () }
    }
  };
  array_forget['c, i32](cs);
  let r = at(&dp, amount, big);
  if r == big { i64[0] - i64[1] } else { r }

fn lcs(x: string, y: string) -> i32 =
  let (xa, m) = x;
  let (ya, n) = y;
  let mut xa = xa;
  let mut ya = ya;
  let mut prev = array_new[i32](n + 1, !{ i -> 0 });
  let mut cur = array_new[i32](n + 1, !{ i -> 0 });
  for i in 1..m + 1 {
    for j in 1..n + 1 {
      let a = at(&xa, i - 1, 0);
      let b = at(&ya, j - 1, 0);
      let d = at(&prev, j - 1, 0);
      let u = at(&prev, j, 0);
      let l = at(&cur, j - 1, 0);
      let v = if a == b { d + 1 } else { max(u, l) };
      cur = array_set(cur, j, v)
    };
    let t = prev;
    prev = cur;
    cur = t
  };
  let r = at(&prev, n, 0);
  r

fn c3(i: i32) -> i32 = if i == 0 { 1 } else if i == 1 { 2 } else { 5 }

main -> i64 * (i64 * (i32 * i32)) =
  let cs = array_new[i32](3, c3);
  let two = array_new[i32](1, !{ i -> 2 });
  let r1 = borrow imm cs { v -> coins(v, 11) };
  let r2 = borrow imm two { v -> coins(v, 3) };
  let l1 = lcs(string_of_lit("abcde"), string_of_lit("ace"));
  let l2 = lcs(string_of_lit("AGGTAB"), string_of_lit("GXTXAYB"));
  (r1, (r2, (l1, l2)))
```

### `T06.bc`

```bc
-- T06: word frequencies in first-seen order, with `lib/map.bc` keyed by views of the text.
-- Workarounds: words are cut out by index (`split_at`; there is no word splitter yielding views),
-- and the view is copied (`array_copy`) for each use (#142); the upsert is two probes
-- (`map_lookup` then `map_insert`); each conditional push threads its buffer by hand (a lend
-- `push(&mut out, …)` in an `if` arm that heads `;` is refused, SPEC §11), and the per-word
-- update is a function threading the map and buffer (lends in a nested `if` inside the `for`:
-- "`hy0_freq` is used twice here", #502); the first-seen order is a buffer of views read with `view_at`.
include textio
include map
include text

fn slice<'t>(t: text 't, i: i32, k: i32) -> text 't =
  match split_at(t, i) {
    inl (h, r) -> array_forget['t, u8](h);
      match split_at(r, k) { inl (w, rest) -> array_forget['t, u8](rest); w | inr r -> r }
  | inr t -> t
  }

-- The word counted once more, and appended to `order` when it is new.
fn bump<'t>(freq: Map[text 't, i32], order: buf (text 't), word: text 't)
    -> Map[text 't, i32] * buf (text 't) =
  let mut freq = freq;
  let mut order = order;
  let (word, k) = array_copy['t, u8] word;
  let old = map_lookup(&freq, k);
  let c = match old { inl c -> c | inr u -> 0 };
  let (word, k2) = array_copy['t, u8] word;
  let (o, u) = if c == 0 { push(order, k2) } else { array_forget['t, u8](k2); (order, ()) };
  let prev = map_insert(&mut freq, word, c + 1);
  (freq, o)

-- (`u0`: named `u`, the first view clashed with the `inr u` of the last loop: "`u` is used
-- twice here, and its type `array_imm 't u8` is not persistent"; not minimised.)
fn freq<'t>(t: text 't) -> string =
  let (t, u0) = array_copy['t, u8] t;
  let n = len(u0);
  let mut t = t;
  let mut freq = map_new[text 't, i32](16);
  let mut order = buf_new[text 't](8);
  let mut start = 0;
  for i in 0..n + 1 {
    let (t2, w) = array_copy['t, u8] t;
    t = t2;
    let b = at(w, i, b' ');
    let (t2, w) = array_copy['t, u8] t;
    t = t2;
    let word = slice(w, start, i - start);
    let (f, o) = if b == b' ' && start < i { bump(freq, order, word) }
                 else { array_forget['t, u8](word); (freq, order) };
    freq = f;
    order = o;
    if b == b' ' { start = i + 1 } else { () }
  };
  array_forget['t, u8](t);
  let (order, k) = len_of(order);
  let mut order = order;
  let mut out = string_new(32);
  for i in 0..k {
    let (o2, w) = view_at(order, i);
    order = o2;
    let o = if i > 0 { let (o, u) = push_byte(out, b','); o } else { out };
    out = o;
    let (w, w2) = array_copy['t, u8] w;
    push_str(&mut out, w2);
    push_byte(&mut out, b':');
    let c = map_lookup(&freq, w);
    let c = match c { inl c -> c | inr u -> 0 };
    push_dec(&mut out, c)
  };
  out

main -> i32 =
  let out = borrow imm "the cat and the hat and the bat" { t -> freq(t) };
  let out = print_string(out);
  print_lit("\n");
  0
```

### `T07.bc`

```bc
-- T07: a turnstile driven by the bytes of a literal; the arms update counters.
-- Workarounds: states are `bool`, Open = true (no named variants, #141; `==` is integer-only); the `match` on a pair is nested `if`s;
-- the events are an owned string iterated by `&evs` (a `for` over the view of a lent literal is
-- refused: "the iterator of this `for` holds the borrow of `v`", SPEC §14); the next state is let-bound and then assigned (`st = if …` does not parse).
include text

fn locked() -> bool = false
fn open() -> bool = true

main -> bool * (i32 * (i32 * i32)) =
  let mut st = locked();
  let mut passed = 0;
  let mut rejected = 0;
  let mut wasted = 0;
  let (evs, k) = string_of_lit("cpppccpcp");
  for p in &evs {
      let e = *p;
      let next = if st {
        if e == b'p' { passed = passed + 1; locked() } else { wasted = wasted + 1; open() }
      } else {
        if e == b'c' { open() } else { rejected = rejected + 1; locked() }
      };
      st = next
  };
  (st, (passed, (rejected, wasted)))
```

### `T08.bc`

```bc
-- T08: a memo table as an answering handler's state (a map and a hit count), consulted by a
-- non-structural recursion (Collatz chain lengths) run under a budget (`on_exhausted`).
-- `best` is assigned inside the answering `with memo` body (accepted). The budget handler is put
-- around each call (`chain_top`): the body of `with on_exhausted` may not assign a `let mut`
-- declared outside it (see T08-best-answered.bc for the other arrangement).
include map
include rec

effect Memo { fn lookup(n: i64) -> i32 + 1; fn store(n: i64, l: i32) }

handler memo(mut s: Map[i64, i32] * i32): Memo = {
  lookup(n) = {
    let (m, h) = s;
    let (m, o) = map_lookup(m, n);
    match o { inl l -> s = (m, h + 1); inl l | inr u -> s = (m, h); inr () }
  };
  store(n, l) = { let (m, h) = s; let (m, o) = map_insert(m, n, l); s = (m, h); () }
}

fn collatz(n: i64) -> i64 = if n % i64[2] == i64[0] { n / i64[2] } else { i64[3] * n + i64[1] }

fn chain(n: i64) -> i32 with Memo, Exhausted =
  if n == i64[1] { 1 } else {
    match lookup(n) {
      inl l -> l
    | inr u -> let l = 1 + chain(collatz(n)); store(n, l); l
    }
  }

fn chain_top(n: i64) -> i32 with Memo = with on_exhausted(!{ u -> 0 }) { chain(n) }

main -> (i32 * i32) * (i32 * i32) =
  let cache = alloc((map_new[i64, i32](64), 0));
  let mut bn = 0;
  let mut bl = 0;
  with memo(&mut cache) {
    for n in 1..30 {
      let l = chain_top(host[extend_s](n));
      if l > bl { bn = n; bl = l } else { () }
    } };
  let (m, hits) = free(cache);
  let k = map_len(&m);
  ((bn, bl), (hits, k))
```

### `T09.bc`

```bc
-- T09: particles bouncing in [0, 100], updated in place through a `mut` lend of the world.
-- Workarounds: a particle is a pair `(x, v)` (no records, #141); the per-particle update is one
-- `modify` answering `(new, bounced)`, in place of field updates `p.x += …`.
include io

fn w0(i: i32) -> i32 * i32 = if i == 0 { (10, 7) } else if i == 1 { (50, 0 - 3) } else { (99, 11) }

fn step<'a>(ps: array_mut 'a (i32 * i32)) -> i32 =
  let mut b = 0;
  for p in ps {
    let r = modify p { e ->
      let (x, v) = e;
      let x = x + v;
      if x < 0 || x > 100 { ((x - 2 * v, 0 - v), 1) } else { ((x, v), 0) } };
    b = b + r
  };
  b

main -> i32 =
  let mut world = array_new[i32 * i32](3, w0);
  let mut bounces = 0;
  for _ in 0..50 { let k = step(&mut world); bounces = bounces + k };
  for p in &world { let (x, v) = *p; print_dec(x); print_byte(b' ') };
  print_byte(b'\n');
  bounces
```

### `T10.bc`

```bc
-- T10: simultaneous updates. Workaround: no tuple assignment or `let (mut a, mut b)`; each
-- update reads the old values into a pair first, then assigns each variable. The remainder is
-- `checked_rem` with its error arm written: `p % q` in the `while` of `main` puts the rest of `main`
-- under `main_div_error` (SPEC §39), refused: "the type of the type of the body `main_div_error`
-- handles is not determined here: ascribe it"; as a `fn gcd … with Fail[DivError]` holding the
-- `while`, `main` gets the div function's loop type in its result (type mismatch).
main -> i32 * (i32 * (i32 * (i32 * i32))) =
  let mut a = 0;
  let mut b = 1;
  for _ in 0..20 { let (na, nb) = (b, a + b); a = na; b = nb };
  let mut x = 1;
  let mut y = 2;
  let mut z = 3;
  for _ in 0..4 { let (nx, ny, nz) = (y, z, x); x = nx; y = ny; z = nz };
  let mut p = 1071;
  let mut q = 462;
  while q != 0 {
    let r = match checked_rem(p, q) { inl r -> r | inr e -> 0 };
    p = q;
    q = r
  };
  (a, (x, (y, (z, p))))
```

### `T11.bc`

```bc
-- T11: a configuration updated field by field from command-line style options, then frozen.
-- Workarounds: the record is a nested pair `width * (height * (title * verbose))` (no records,
-- #141), so each field update destructures and rebuilds it; the options are words of a literal
-- cut out by index (as T06); `parse_i32`'s error is handled with `default` (the old width kept);
-- the per-option update is a function threading the configuration.
include textio
include text
include fail

type Cfg = i32 * (i32 * (string * bool))

fn slice<'t>(t: text 't, i: i32, k: i32) -> text 't =
  match split_at(t, i) {
    inl (h, r) -> array_forget['t, u8](h);
      match split_at(r, k) { inl (w, rest) -> array_forget['t, u8](rest); w | inr r -> r }
  | inr t -> t
  }

-- The option `a` applied: the configuration, and 1 when the option is unknown.
fn apply<'t>(cfg: Cfg, a: text 't) -> Cfg * i32 =
  let (width, (height, (title, verbose))) = cfg;
  let (a, a1) = array_copy['t, u8] a;
  let (a, a2) = array_copy['t, u8] a;
  let n = len(a1);
  let w = slice(a2, 0, 8);
  let (a, a3) = array_copy['t, u8] a;
  let t = slice(a3, 0, 8);
  if eq_lit(w, "--width=") {
    let v = slice(a, 8, n - 8);
    let width = with default(width) { parse_i32(v) };
    ((width, (height, (title, verbose))), 0)
  } else if eq_lit(t, "--title=") {
    let v = slice(a, 8, n - 8);
    let title = to_string(v);
    ((width, (height, (title, verbose))), 0)
  } else if eq_lit(a, "-v") {
    ((width, (height, (title, true))), 0)
  } else { ((width, (height, (title, verbose))), 1) }

fn parse<'t>(t: text 't, cfg: Cfg) -> Cfg * i32 =
  let (t, u0) = array_copy['t, u8] t;
  let n = len(u0);
  let mut t = t;
  let mut cfg = cfg;
  let mut unknown = 0;
  let mut start = 0;
  for i in 0..n + 1 {
    let (t2, w) = array_copy['t, u8] t;
    t = t2;
    let b = at(w, i, b' ');
    let (t2, w) = array_copy['t, u8] t;
    t = t2;
    let word = slice(w, start, i - start);
    let (c, k) = if b == b' ' && start < i { apply(cfg, word) }
                 else { array_forget['t, u8](word); (cfg, 0) };
    cfg = c;
    unknown = unknown + k;
    if b == b' ' { start = i + 1 } else { () }
  };
  array_forget['t, u8](t);
  (cfg, unknown)

main -> (i32 * (i32 * bool)) * (i32 * i32) =
  let cfg0 = (40, (25, (string_of_lit("untitled"), false)));
  let r = borrow imm "--width=80 --title=demo -v --frob" { t -> parse(t, cfg0) };
  let (cfg, unknown) = r;
  let (width, (height, (title, verbose))) = cfg;
  let height = if verbose { height * 2 } else { height };
  let cfg = (width, (height, (title, verbose)));
  let (width, (height, (title, verbose))) = cfg;
  let title = print_string(title);
  print_lit("\n");
  ((width, (height, verbose)), (width * height, unknown))
```

### `T12.bc`

```bc
-- T12: (1) a block that writes a captured variable, (2) a block passed down a recursion that
-- accumulates, (3) a stored counter closure.
-- Workarounds: (1) and (2) keep their state in an answering handler's state, lent from a cell
-- (`with h(&mut c)`), and the blocks perform its operations (SPEC §32): a `let mut` written in a
-- block is lost when the block only writes it (#586: `x * 10 + a` is 12) and refused when it also
-- reads it ("`!thunk` promotes only over `!` types, but `x`, of type `i32`, is used inside").
-- (3) is an `Aff` over its own cell (SPEC §22) called through `aff_call`; its close answers `1`,
-- so the residual count is the last call's answer.
include buf
include rec
include aff
include io
include slice

effect Cell { fn put(v: i32) }
handler cellh(mut s: i32): Cell = { put(v) = { s = v; () } }

effect Visit { fn visit(k: i32) }
handler collect(mut s: i32 * buf i32): Visit = {
  visit(k) = { let (sum, b) = s; let (b, u) = push(b, k); s = (sum + k, b); () }
}

fn ap(f: !(i32 => i32)) -> i32 = f(1)

fn walk(lo: i32, hi: i32, f: !(i32 => 1)) -> 1 with Exhausted =
  if lo < hi { let m = (lo + hi) / 2; walk(lo, m, f); f(m); walk(m + 1, hi, f) } else { () }

-- A counter from `start` by `step`: each call answers the new count.
fn aff_counter<'c>(start: i32, step: i32) -> box 'c Aff[1, i32]<'c> =
  aff_new_boxed[ref (i32 * i32), 1, i32]['c](alloc((start, step)), !thunkv fun (s : ref (i32 * i32)) ->
    < fun (a : 1) ->
        cx <- return (swap[i32 * i32, i32 * i32] s (0, 0));
        let (c, x) = cx;
        let (n, k) = x;
        cu <- return (swap[i32 * i32, i32 * i32] c (n + k, k));
        let (c1, u) = cu;
        return (n + k, c1),
      n <- return (free[i32 * i32] s); return () >)

main -> i32 * (i32 * (i32 * i32)) =
  -- (1)
  let xc = alloc(1);
  let a = with cellh(&mut xc) { ap(!{ u -> put(5); u + 1 }) };
  let x = free(xc);
  -- (2)
  let sc = alloc((0, buf_new[i32](8)));
  with collect(&mut sc) { with on_exhausted(!{ u -> () }) { walk(0, 6, !{ k -> visit(k) }) } };
  let (sum, seen) = free(sc);
  let (arr, k) = seen;
  for i in 0..k { let e = at(&arr, i, 0); print_dec(e); print_byte(b' ') };
  print_byte(b'\n');
  -- (3)
  let tick = aff_counter(0, 3);
  let (t1, tick) = aff_call(tick, ());
  let (t2, tick) = aff_call(tick, ());
  aff_close(tick);
  (x * 10 + a, (sum, (t1 + t2, t2)))
```

### `T13.bc`

```bc
-- T13, the Rust shape: `main` owns the accounts and lends each `mut` to a scoped teller task
-- (`spawn_in`, SPEC §32), which reads its transactions from an argument across `await`s.
-- `c2` and `d` are handed back by hand out of the outer block (#495).
include async

fn teller<'a>(a: mut 'a i32, txs: List[i32], n: i32) -> i32 with Async =
  let mut rest = txs;
  let mut r = 0;
  for _ in 0..n {
    match unroll rest {
      inl u -> rest = nil[i32]()
    | inr (t, more) ->
        rest = more;
        let ok = modify a { b -> if b + t < 0 { (b, false) } else { (b + t, true) } };
        if ok { () } else { r = r + 1 };
        await()
    }
  };
  r

main -> List[i32] * (i32 * i32) =
  let c1 = alloc(100);
  let c2 = alloc(50);
  let d = alloc(());
  let (c2, (d, v)) = borrow mut c1 { 'r, m1 -> let r = borrow mut c2 { 's, m2 ->
    let v = borrow mut d { 'd, e ->
      let q = queue_in[i32]();
      let q = push_in(q, with spawn_in { teller(m1, cons(50, cons(0 - 20, nil())), 2) });
      let q = push_in(q, with spawn_in { teller(m2, cons(0 - 30, cons(0 - 40, nil())), 2) });
      with on_exhausted(!{ u -> nil() }) { run_in(q, 4) } };
    (d, v) }; (c2, r) };
  let _ = free(d);
  (v, (free(c1), free(c2)))
```

### `T14.bc`

```bc
-- T14: a random-number service and a logger as answering handlers with state, and a buffer
-- filled through `&mut` in a call that also uses both capabilities.
-- Workaround: the lend is a `borrow mut b` block with the handlers installed inside it, and the
-- RNG handler installed again on its cell for the read after: `fill(&mut b)` inside the `with`s
-- is refused, "a place is lent (`&mut x`) in the arguments of `fill`, which also threads a
-- capability: lend it in a call of its own" (SPEC §18; T14-lend-refused.bc), and a borrow block
-- inside the `with`s is refused (T14-borrow-block.bc). T14-owned.bc passes the buffer owned.
include buf
include slice
include io

effect Rng { fn next() -> i32 }
handler lcg(mut s: i32): Rng = {
  next() = { s = host[add32](host[mul32](s, 1103515245), 12345); host[shr_u32](s, 16) % 100 }
}

effect Logger { fn log(x: i32) }
handler logger(mut l: i32 * i32): Logger = { log(x) = { let (n, t) = l; l = (n + 1, t + x); () } }

fn fill<'a>(v: array_mut 'a i32) -> 1 with Rng, Logger =
  for p in v { let x = next(); modify p { e -> x }; if x > 50 { log(x) } else { () } }

main -> i32 * (i32 * i32) =
  let lg = alloc((0, 0));
  let sc = alloc(42);
  let mut b = array_new[i32](6, !{ i -> 0 });
  borrow mut b { v -> with lcg(&mut sc) { with logger(&mut lg) { fill(v) } } };
  let again = with lcg(&mut sc) { next() };
  let (n, sum) = free(lg);
  let s = free(sc);
  for p in &b { print_dec(*p); print_byte(b' ') };
  print_byte(b'\n');
  (again, (n, sum))
```

### `T12-586-write-lost.bc`

```bc
-- RUNS but WRONG (#586): prints 12, not 52.
fn ap(f: !(i32 => i32)) -> i32 = f(1)
main -> i32 =
  let mut x = 1;
  let a = ap(!{ u -> x = 5; u + 1 });
  x * 10 + a
```

### `T12-586-read-refused.bc`

```bc
-- REFUSED (#586 read+write form).
fn ap(f: !(i32 => i32)) -> i32 = f(1)
main -> i32 =
  let mut x = 1;
  let a = ap(!{ u -> x = x + 5; u + 1 });
  x * 10 + a
```

### `T13-txs-outside.bc`

```bc
-- REFUSED attempt (kept for its message).
-- T13, the doc's shape: the teller's borrow block reads `txs`, a variable outside it, across `await`.
include async
include fail

fn teller(acct: i32, txs: List[i32]) -> i32 * i32 with Async =
  let cell = alloc(acct);
  let refused = borrow mut cell { a ->
    let mut r = 0;
    let mut rest = txs;
    for _ in 0..2 {
      match unroll rest {
        inl u -> rest = nil[i32]()
      | inr (t, more) ->
          rest = more;
          let ok = modify a { b -> if b + t < 0 { (b, false) } else { (b + t, true) } };
          if ok { () } else { r = r + 1 };
          await()
      }
    };
    r };
  (free(cell), refused)

main -> List[i32 * i32] =
  let q = queue[i32 * i32]();
  let q = push(q, with spawn { teller(100, cons(50, cons(0 - 20, nil()))) });
  let q = push(q, with spawn { teller(50, cons(0 - 30, cons(0 - 40, nil()))) });
  run_until_empty(q)
```

### `T14-lend-refused.bc`

```bc
-- REFUSED attempt (kept for its message).
-- T14: a random-number service and a logger as answering handlers with state, and a buffer
-- filled through `&mut` in a call that also uses both capabilities.
include buf
include slice
include io

effect Rng { fn next() -> i32 }
handler lcg(mut s: i32): Rng = {
  next() = { s = host[add32](host[mul32](s, 1103515245), 12345); host[shr_u32](s, 16) % 100 }
}

effect Logger { fn log(x: i32) }
handler logger(mut l: i32 * i32): Logger = { log(x) = { let (n, t) = l; l = (n + 1, t + x); () } }

fn fill(buf: array i32) -> array i32 with Rng, Logger =
  let mut buf = buf;
  for i in 0..6 { let x = next(); buf = array_set(buf, i, x); if x > 50 { log(x) } else { () } };
  buf

main -> i32 * (i32 * i32) =
  let lg = alloc((0, 0));
  let sc = alloc(42);
  let mut b = array_new[i32](6, !{ i -> 0 });
  let again = with lcg(&mut sc) {
    with logger(&mut lg) { fill(&mut b) };
    next() };
  let (n, sum) = free(lg);
  let s = free(sc);
  for p in &b { print_dec(*p); print_byte(b' ') };
  print_byte(b'\n');
  (again, (n, sum))
```

### `T14-borrow-block.bc`

```bc
-- REFUSED attempt (kept for its message).
-- T14: a random-number service and a logger as answering handlers with state, and a buffer
-- filled through `&mut` in a call that also uses both capabilities.
include buf
include slice
include io

effect Rng { fn next() -> i32 }
handler lcg(mut s: i32): Rng = {
  next() = { s = host[add32](host[mul32](s, 1103515245), 12345); host[shr_u32](s, 16) % 100 }
}

effect Logger { fn log(x: i32) }
handler logger(mut l: i32 * i32): Logger = { log(x) = { let (n, t) = l; l = (n + 1, t + x); () } }

fn fill<'a>(v: array_mut 'a i32) -> 1 with Rng, Logger =
  for p in v { let x = next(); modify p { e -> x }; if x > 50 { log(x) } else { () } }

main -> i32 * (i32 * i32) =
  let lg = alloc((0, 0));
  let sc = alloc(42);
  let mut b = array_new[i32](6, !{ i -> 0 });
  let again = with lcg(&mut sc) {
    with logger(&mut lg) { borrow mut b { v -> fill(v) } };
    next() };
  let (n, sum) = free(lg);
  let s = free(sc);
  for p in &b { print_dec(*p); print_byte(b' ') };
  print_byte(b'\n');
  (again, (n, sum))
```

## 12. The widened target set (2026-10-19)

The user found §1's set too small ("the scope might have been a little bit too small in terms of
target programs if you're just having it look at what we currently have in pending"), and agreed
the set recorded on #587:

1. **Are We Fast Yet**, all 14 (Marr et al.);
2. **the Benchmarks Game**, 10;
3. **an Advent-of-Code subset** from `maneatingape/advent-of-code-rust` (grids, graphs, BFS and
   Dijkstra, parsing, simulation, memo);
4. **the north star end to end**: an HTTP client and server, JSON and YAML, a watch stream,
   retries with backoff and timers, several concurrent reconcilers sharing a client and a cache,
   cancellation;
5. **Lox**, as a tree-walker and a bytecode VM;
6. **data structures**: hash map, B-tree, LRU cache, union-find, priority queue, ring buffer, arena
   allocator, doubly linked list;
7. **concurrency**: parallel map-reduce, a worker pool with channels, a stage pipeline.

§1–§11 stay as written. The T01–T14 programs and the #537 bench rows stay in the set. This section
and the next three extend the document; §15, the revised build units, ends it.

**Method.** Three subagents of this session each wrote the *hard part* of every program in a
category in today's surface, ran it, and recorded the exact refusal of each natural shape that
fails. I re-ran the load-bearing ones (measured, §12.8). Every program is in
`docs/expressiveness-probes/<category>/`, runnable as `$B run FILE` (with `< FILE.in` where an
`.in` exists). The status words are:
- **natural**: the functionality in a reasonable shape;
- **workaround**: it runs in a shape a refusal forced (the refusal is quoted);
- **blocked**: no shape found; the best attempt's message is quoted.

### 12.1 Are We Fast Yet

Every one runs; four need an arena for an object graph.

| program | what it does | status | the refusal, or the workaround | blocker | allocs / indirect | probe |
|---|---|---|---|---|---|---|
| Richards | a scheduler over task records in a linked list, packets in linked queues; tasks change other tasks' state | workaround: task records in an arena (`array i32`, links are indices); packets owned, moved queue to queue (`richards_mu.bc`) | the shared record: "`t` is used twice here, and its type `ref (i32 * i32)` is not persistent"; the per-task function field: "`i` is not consumed in its scope, and it cannot be dropped where its scope ends" (an array of `!` functions); a div helper in an `if` arm returning an owned array, refused in generated code | B13, B15, B7 | 2 / 0 | `awfy/richards.bc` (23246 / 9297, the reference counts) |
| DeltaBlue | a constraint graph: variables and constraints point at each other; the planner walks and mutates strengths | workaround: arena | a constraint in two variables' lists: the same "used twice"; two `imm` views of one cell: "`v` is used twice here, and its type `imm 'a i32` is not persistent" | B13, B9 | 416 / 0 | `awfy/deltablue.bc` (chain test: 100 of 100, plan length 101) |
| Havlak | loop recognition: a CFG with edge lists, DFS numbering, union-find, a loop forest with parent pointers | workaround: arena, explicit DFS stack | the recursive DFS inside the `for` over out-edges: "in this `case`, `last` is consumed in the `inr` arm but not in the `inl` arm" (#492) | B13, B7 | 1806 / 0 | `awfy/havlak.bc` |
| CD | collision detection over a red-black tree keyed by call sign (parent pointers, rotations) | workaround: arena tree with a sentinel | a child holding its parent: "`parent` is used twice here, and its type `ref i32` is not persistent" | B13 | 2 / 0 | `awfy/cd_rbtree.bc` (the tree part only) |
| Json | parse JSON into a tree and print it | natural | a lookup returning a view into the tree: "`unroll V` needs `V : mu X. A`, but `V : imm 'a (mu X. …)`" | B3, B9 | 36 / 0 | `awfy/json.bc` |
| NBody, Mandelbrot, Sieve | — | natural | `bench/` (recorded) | — | — | `bench/n-body`, `bench/mandelbrot`, `bench/sieve` |
| Bounce | balls in an array, mutated in place | natural | `for b in &mut balls { modify b { … } }` | — | 1 / 0 | `awfy/bounce.bc` |
| List | build lists, compare lengths, Takeuchi over lists | workaround: `clone` per extra use (9830 copies) | "`y` is used again …, so this use copies it, and its type … holds recursive data: the copy allocates every node" | B9 (shared immutable data) | 75374 / 0 | `awfy/list.bc` |
| Permute, Queens | recursive search over arrays | natural | — | — | 1 / 0, 40 / 0 | `awfy/permute_natural.bc`, `awfy/queens.bc` |
| Storage | a tree of arrays of arrays, built recursively | workaround: four children as a tuple | children in an array: "`io_d23` is not consumed in its scope, and its type … has no destructor" | B14 | 5461 / 0 | `awfy/storage.bc`, `awfy/storage_array.bc` |
| Towers | Hanoi with piles as linked lists | natural | — | — (cost: a box per push) | 86383 / 0 | `awfy/towers.bc` |

### 12.2 The Benchmarks Game

Every one runs. Two needed libraries written by hand.

| program | status | the refusal, or the workaround | blocker | allocs / indirect | probe |
|---|---|---|---|---|---|
| binary-trees, mandelbrot, n-body, spectral-norm | natural (`bench/`, 0.40×, 1.01×, 1.78×, 0.99× of Rust, recorded) | output is a count or a scaled integer, not the Game's PBM or `%.9f` | B16 (float formatting) | — | `bench/` |
| fannkuch-redux | natural | `for … break` in place of `while` (#503) | B7 | 5 / 0 | `bg/fannkuch.bc` |
| fasta | natural; byte-identical to the reference | — | — | 7 / 0 | `bg/fasta.bc` |
| k-nucleotide | workaround | a lookup by a literal's view: "this argument of `map_lookup` has type `array_imm 'l1 u8`, which is not `K`" (SPEC §36 *Not provided*: a lookup by a key at another lifetime); sorting entries that hold views: "`x` is used twice here, and its type `array_imm 'io_q0 u8 * i32` is not persistent" | B16, B9 | 41 / 0 | `bg/knuc.bc` |
| pidigits | workaround: `lib/float.bc`'s unsigned `Big` plus a sign and a small division written in the program | — | B16 (a signed bignum library) | 533 / 0 | `bg/pidigits.bc` (1000 digits correct) |
| regex-redux | natural, with a Pike VM written in the program (about 230 lines); all counts and replacements match Python's `re` | — | B16 (a regex library, #225) | 591769 / 0 | `bg/regex.bc` |
| reverse-complement | workaround | a lend in an `if` arm (#502); and **a callee's `let mut tbl` makes its caller's `tbl` "used twice"** (new, §12.7) | B7 | 6 / 0 | `bg/revcomp.bc`, `bg/mut-name-capture.bc` |

### 12.3 Advent of Code

All 13 ports in `corpus/aoc/` check today (measured, §12.8). They cover grids (2022-12, 2023-03),
graphs with BFS and Dijkstra over a binary heap (2022-12, 2021-15), parsing (2022-01, 2023-01,
2024-02), simulation (2020-08, 2021-06), maps keyed by views (2022-21, 2024-01, 2024-11), and a stack
(2021-10). The one pending port, `corpus/pending/aoc-2020-07.bc` (memoised recursion over a map
keyed by views), is refused by #491 and #492, both B7. So the AoC subset gates only B7; memo by a
`memo` layer is B8.

### 12.4 The north star, end to end

| part | status | the refusal, or the workaround | blocker | probe |
|---|---|---|---|---|
| HTTP client and server | **blocked** | no network capability: the platform's externs are `read_byte`, `write_byte`, `write_all`, `read_into`, `clock_now`, `clock_sleep`, `read_arg` (`lib/wasi.bc`); `Net` is "designed, not built" (SPEC §11, §34 *Open*, #66). A user extern over a new kind: "expected a type, found name `socket`" | **B11** (new) | `ns/net-extern.bc` |
| HTTP response parsing | workaround: a push parser fed byte by byte from `for b in bytes(&mut stdin)` | the pull form, a generator holding the input: B4's message | B4 | `ns/http-parse.bc`, `ns/http-gen.bc` |
| JSON | natural for the tree (`awfy/json.bc`); names need B3 | — | B3 | — |
| YAML | workaround: an explicit stack of indentation frames | `while` inside `for` (#503); `on_exhausted` cannot wrap the div `for` over the input (B2); a `match` inside a control `with` whose arms differ in printing: "in this `case`, `stdout` is consumed in the `inr` arm but not in the `inl` arm" (new) | B7, B2 | `ns/yaml-indent.bc` |
| a watch stream | blocked: needs B11's socket; its decoding is B4's pull parser | — | B11, B4 | — |
| retries with backoff on the clock | natural for a stateless call (`ns/retry-backoff2.bc`); `corpus/retry-block.bc` now retries (measured: `((inl 200, 30), (inr 503, 10))`), so #479's defect is gone | with a stateful service used inside the retried block: "the computation parameter `f` uses the capability of `Svc` and is called inside `with to_result`, whose body is lent the capability anew: not provided (SPEC §33 *Open*)" | **B17** (new to this document; #487) | `ns/retry-backoff.bc` |
| timers and cancellation | natural: a task polls `Clock` and another cancels it; its cell is freed (`live 0`) | — | — | `ns/timer-cancel.bc` |
| concurrent reconcilers sharing a client and a cache | blocked in the natural form | the cache as an effect: "two tasks spawned in this block are given the capability of `Cache` …"; as a borrow (watch `mut`, readers `imm`): "type mismatch: expected `imm (…) i32`, but this has type `mut 'r i32`" | B1, B2 | `ns/informer-cache.bc`, `ns/informer-borrow.bc` |

### 12.5 Lox

| program | status | the refusal, or the workaround | blocker | allocs / indirect | probe |
|---|---|---|---|---|---|
| tree-walker (jlox) | workaround: environments in an arena (a parent index per environment); a closure is (function id, environment index); instances index a field table. `makeCounter` twice, aliasing a closure, bound methods: output `1 2 1 3 11 12` | two closures sharing one captured variable: "`ml` is used twice here, and its type `mut 'x i32` is not persistent"; a buffer of AST nodes: "`mu X. …` has no filler" | B13, B14 | 124 / 0 | `lox/tree-arena.bc`, `lox/natural-shared-env.bc` |
| bytecode VM (clox) | workaround: arena indices for upvalues, frames, globals; the dispatch `while` is a flat loop (about 1.5 loads and 1.5 bounds checks per instruction, no allocation) | an upvalue pointing into the growing stack: "`stack` is used twice here, and its type `array i32 * i32` is not persistent"; native functions in a table (B15) | B13, B15 | 99 / 0 | `lox/clox-vm.bc`, `lox/natural-upvalue.bc` |

### 12.6 Data structures and concurrency

| program | status | the refusal, or the workaround | blocker | probe |
|---|---|---|---|---|
| hash map | natural (`lib/map.bc`: generic, insert, lookup, remove, a view by `map_get`, iteration) | iterating a map whose keys are owned strings: "type mismatch: expected `array u8 * i32`, but this has type `array_imm 'y u8 * i32`" (at `lib/map.bc:230`) | B16 | `ds/hashmap.bc` |
| B-tree | workaround: arena, generic with a comparator (2000 keys, height 6) | nodes owning arrays of children: "`e` is not consumed in its scope, and its type `1 + (mu X. …)` has no destructor" | B14 | `ds/btree.bc`, `ds/btree-boxed.bc` |
| LRU cache | workaround: arena list with a sentinel plus `Map[i32, i32]`; LeetCode 146's example | the classic map-to-node plus linked nodes: "`n` is used twice here, and its type `ref (mu X. (i32 * i32) * (1 + ref X) * (1 + ref X))` is not persistent" | B13 | `ds/lru-arena.bc`, `ds/lru-cells.bc` |
| doubly linked list | workaround: arena | linking cells both ways: "`a` is used twice here …" | B13 | `ds/dll-cells.bc` |
| union-find, ring buffer, arena allocator | natural | ids are aliases, not distinct types (no `data`) | B3 | `ds/unionfind.bc`, `ds/ringbuf.bc`, `ds/arena.bc` |
| priority queue | natural with a heap written in the program; `lib/buf.bc`'s heap takes an `i32` priority and persistent elements: "`x` is used twice here, and its type `i32 * array u8 * i32` is not persistent" | — | B16 | `ds/pq.bc` |
| parallel map-reduce | workaround: two `spawn_in` tasks over disjoint `split_at_mut` halves, interleaved on one thread; `unconditional` | no threads | **B12** (#212) | `conc/split-halves.bc` |
| worker pool with channels | workaround: **a scheduler written in the program serves the job queue and the results** (control operations `take_job`, `send_res`, `wait_turn`; the decision-57 port). Two workers, five jobs | the natural form, tasks sharing a channel effect: "two tasks spawned in this block are given the capability of `Chan` …" | B1 | `conc/worker-pool-port.bc`, `conc/worker-pool.bc` |
| stage pipeline | natural as generators composed with `\|>`; blocked as tasks over channels (B1's message) | — | B1 | `conc/pipeline-gen.bc`, `conc/pipeline-tasks.bc` |

### 12.7 New blockers and defects

**New blockers** (each with a program that needs it):

- **B11, no network capability.** HTTP client, server, watch stream; the operator end to end. The
  only missing piece of the north star that has no workaround.
- **B12, no threads.** Parallel map-reduce; a worker pool on several cores. The borrow structure
  already checks: disjoint `mut` halves held by two tasks across `await` is `unconditional`
  (measured, `conc/split-halves.bc`).
- **B13, aliased mutable object graphs.** Richards, DeltaBlue, Havlak, CD, LRU, the doubly linked
  list, both Loxes. Every one runs as an arena (index handles); the natural shape (a node reachable
  from two places and mutated) is refused with "used twice". The premise's limited checker refuses
  it by design, as Rust's does without `Rc<RefCell<_>>`.
- **B14, recursive data under an array.** Storage, a B-tree whose nodes own child arrays, a buffer
  of AST nodes, `lc-0208-trie-boxed`: no destructor and no filler for `mu X. … array X …` (#182).
- **B15, containers of `!` functions.** Richards' task functions, Lox's native functions: "`i` is
  not consumed in its scope, and it cannot be dropped where its scope ends" at `array_new[!(i32 =>
  i32)](n, !{ i -> f })`, and "`io_else` is not consumed …" at `if c { f } else { g }` with a `!`
  result. A pair of `!` functions, and a `mu` list of them, work. By inspection this is SPEC §26
  *Open*: "weakening by an unused live slot of a persistent type, as a derived rule of the kernel:
  not derived" (hypothesis that it is the same gap; `i` is a dead `i32` binder at a `!` result).
- **B16, missing libraries.** A signed bignum with big×big and division (pidigits), a regex engine
  (regex-redux, #225), fixed-precision float formatting (n-body, spectral-norm, k-nucleotide's
  output), an O(n log n) sort and a heap with a comparator over owned elements (#497), map lookup by
  a key at another lifetime, iteration over owned keys. Each was written in a program, so each is
  a library gap, except the lookup by another lifetime, which SPEC §36 says needs "a family
  shortened, a kernel constant".
- **B17, a capability used by a computation parameter under its callee's handler** (#487, SPEC §33
  *Open*). Retries around a stateful service.

**New defects** (elaboration, joining B7; none is filed by this unit):

1. **A silent wrong answer: an assignment inside a `modify` block is lost.**
   `let mut x = 5; let mut n = 0; modify &mut x { v -> n = 7; v + 1 }; (x, n)` gives `(6, 0)`
   (measured, `awfy/modify_assign.bc`). It is #586's class in a new place.
2. **A callee's `let mut` name changes its caller's check.** A function with `let mut tbl = tbl`
   makes a caller's `let mut tbl` threaded through an `if` refuse: "`tbl` is used twice here"
   (measured, `bg/mut-name-capture.bc`); renaming the callee's binder fixes it.
3. A div call in one arm of an `if` whose other arm returns an owned value is refused in generated
   code (`awfy/div_arm.bc`); the components of a div call's result have type `1` at a generic call
   (`awfy/div_generic.bc`).
4. A lend nested in an expression is not refused at the lend but typed `1`, failing later and far
   away (`bg/lend-arith.bc`); the same for a type used before its declaration.
5. A `match` inside a control `with` whose arms differ in printing is refused (`ns/arm-stdout.bc`).
6. A program's function with a library function's name silently resolves to the library's
   (`awfy/name_clash.bc`).

### 12.8 Re-run here

`B=~/repos/borrow-core-c3c/.lake/build/bin/bcc`, from `docs/expressiveness-probes/` (measured):

```
awfy/richards.bc: (i32[23246], i32[9297])
awfy/deltablue.bc: (i32[100], i32[101])
awfy/havlak.bc: (i32[75], (i32[74], i32[122]))
awfy/cd_rbtree.bc: (i32[877], (i32[1], f64[…]))
awfy/json.bc: i32[12]
awfy/fn_array.bc: fn_array.bc:5:44: `i` is not consumed in its scope, and it cannot be dropped where its scope ends
awfy/modify_assign.bc: (i32[6], i32[0])
bg/mut-name-capture.bc: mut-name-capture.bc:14:14: `tbl` is used twice here, and its type `array u8` is not persistent
bg/mut-name-capture-renamed.bc: runs
bg/pidigits.bc: runs
ds/lru-cells.bc: lru-cells.bc:14:3: `n` is used twice here, and its type `ref (mu X. (i32 * i32) * (1 + ref X) * (1 + ref X))` is not persistent
ds/dll-cells.bc: dll-cells.bc:19:3: `a` is used twice here, and its type `ref (mu X. i32 * (1 + ref X) * (1 + ref X))` is not persistent
ds/btree-boxed.bc: btree-boxed.bc:80:46: `e` is not consumed in its scope, and its type `1 + (mu X. (array i32 * i32) * array (1 + X) * i32)` has no destructor
ds/lru-arena.bc: runs
conc/worker-pool-port.bc: ((i32[3], i32[2]), inr (i32[51], inr (i32[42], inr (i32[31], inr (i32[22], inr (i32[11], inl ()))))))
lox/tree-arena.bc, lox/clox-vm.bc, ns/yaml-indent.bc: run
corpus/aoc/*.bc (13 files): all check
```

## 13. Every way to unblock the new blockers

### 13.1 B11: a network capability

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `std::net` over OS sockets, `Drop` closes | parity | n/a | good | its *surface* is not ours: a socket here is a linear capability, and its close returns the error (#210) |
| **`Net` as an effect served by the platform's outermost handler** (SPEC §34's model for `Stdout`), a connection a linear handle (no destructor; `close` hands back the error), the extern contract proved as stdio's is (`externs_loop_every_run`, SPEC §11) | parity: a direct call to the host (`effect handling is erased`) | lemma per extern, by the stdio pattern | good | **recommended** |
| session-typed HTTP over it (#209) | parity | relation (sessions) | best | later; not needed to run the operator |

The elaboration candidate: `with net { let c = connect(addr); … }` elaborates to the platform's
handler of `Net` and its externs, as `print_byte` elaborates to `wasi_stdout`. Memory at the
surface: none. The WASI target needs WASI sockets; the native target uses libc.

### 13.2 B13: aliased mutable object graphs

What fails: a node reachable from two places and mutated through either (measured, eight
programs). What works today: every one as an arena with integer handles (measured).

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `Rc<RefCell<Node>>` with `Weak` for back edges | a count update per clone and drop, a flag test per borrow; a heap object per node | relation (RC is explicit and deferred, memory "No GC"); `RefCell` is a run-time check | fair | **not the best way here**: the AWFY graph programs' work is all index arithmetic in the arena form, with no counts |
| Rust's other way: an arena with typed indices (`slotmap`, `petgraph`) | an index computation and a bounds check per access | none: it runs today | good once ids are distinct types (B3) | **recommended now**, as a library `Arena[T]` with an `Id[T]` newtype |
| handler-owned region with branded handles (#119; GhostCell's split of permission and data) | index arithmetic with **no** bounds check: a handle of brand `'r` is below the region's length by the region-length Kripke fact | lemma: the `Cell<'r, T>` clause and the monotone length fact (#119) | good: handles are copyable data; get/set are operations, copy in and out | **recommended next**, behind spike S-G; it is the arena with its bounds check removed by typing |
| codata cells (an object as a handler with operations) | a call per access | none | fair | for objects with behaviour (Lox instances), on the same region |
| SILL_S shared processes | a message per access | relation | poor for data structures | set aside |
| explicit RC | as Rust | relation | fair | set aside for the target set; no program needs unstructured lifetime |

**The elaboration candidate.** *Writes:* `region g { let a = g.new(Node{…}); let b = g.new(Node{…});
a.next = b; b.prev = a; … }`. *Elaborates to:* an answering handler owning `buf Node`, handles as
indices of brand `'g`, field reads and writes as its operations (`withswap` on the slot, §18).
*Checked by:* the answering-handler rules, with no new rule for the unbranded version; the branded
version adds #119's lemma. *Memory at the surface:* none; the region frees everything at its end,
as an arena does.

### 13.3 B12: threads

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: scoped threads and rayon's `join` over `split_at_mut`; `Send`/`Sync` | parity | n/a | good | its structure is ours: the split already types (measured) |
| **fork-join `join`/`par_for` over a split context**, sequential on Wasm and on a work-stealing pool natively (#212); soundness at first a named assumption, as R1's is under `PinLaw` (#212's Route 0) | parity | an assumption now; #212's routes B or C later | good | **recommended**: the research thread "fork-join with a named assumption", now used |
| tasks on a thread pool (async across threads) | — | relation | — | after fork-join; outside this set's programs |

### 13.4 B14: recursive data under an array

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `Vec<Box<Node>>` with `Drop` | parity | n/a | good | the target |
| **a destructor and fold for `mu` with `X` under `array`** (#182 item 2) | parity | lemma: one more `FShape` case for `foldOwn` and its destructor | good | **recommended**, behind spike S-H |
| children as a tuple, or in an arena | parity | none | fair | today's workaround |

### 13.5 B15: containers of `!` functions

| way | performance | proof cost | ergonomics | verdict |
|---|---|---|---|---|
| Rust's way: `Vec<fn(i32) -> i32>`, or `Box<dyn Fn>` | an indirect call | n/a | good | the target |
| **derive the weakening of a dead persistent binder** (SPEC §26 *Open*) or elaborate the tabulator so it does not need it | an indirect call, or none after specialisation | lemma (§26) | good | **recommended** |
| a tag and a `match` (defunctionalisation) | a branch | none | fair | today's workaround, and what the backend makes of a known set anyway |

### 13.6 B16: libraries

Each is a library unit, written in the language, with its corpus program: a signed bignum
(`lib/float.bc`'s `Big` extended), a regex engine (Pike VM, #225), `%.Nf` formatting, an O(n log
n) sort and a heap with comparators over owned elements (reading through views, #497), map
iteration over owned keys. The one language item is lookup by a key at another lifetime, which
needs SPEC §36's "family shortened" constant. Rust's way (generic `Borrow<Q>`) is the functionality
to match.

### 13.7 B17: a capability used by a computation parameter under its callee's handler

SPEC §33 *Open* records the cause: the argument should take its capabilities at lifetimes of its
own, `!U(∀'x. Mut 'x S ⊗ A ⊸ F_Σ (Mut 'x S ⊗ B))` (decision 57, R2a). That was built and taken out
because "the checker compares types without α-conversion of lifetime binders" (*Incompleteness*
2). The way is to make the checker compare lifetime binders up to renaming, then restore R2a. Proof
cost: none in the kernel (it is the checker's completeness). Rust's equivalent (`FnMut(&mut S)`,
higher-ranked) is the same idea.

## 14. Re-ranking every blocker by target programs gated

A program is *gated* when its natural shape is refused or it cannot be written at all. North-star
blockers come first, each tier ordered by count; ties go to the better foundation.

| rank | blocker | north star? | programs gated (natural shape) | count |
|---|---|---|---|---|
| 1 | B7 elaboration refusals and silent defects | yes (YAML) | T02, T03, T04, T06, T07, T10, T12; Havlak, Richards, fannkuch, reverse-complement, YAML, B-tree, AoC 2020-07, clox (#493), the `modify` write defect | 16 |
| 2 | B3 data declarations, nested data | yes (JSON, YAML) | JSON round-trip, YAML, AWFY Json, Lox ASTs (2), T07, T09, T11, arena ids (union-find, arena, B-tree) | 11 |
| 3 | B2 div under a handler | yes | operator-reconcile, the watch task and the server's accept loop (by inspection: tasks whose loop is unbounded), YAML over the input, the reconcilers | 5 |
| 4 | B1 a service shared by tasks | yes | operator-reconcile, the reconcilers' cache, the worker pool, the task pipeline, `io-two-tasks` | 5 |
| 5 | B11 network capability | yes | HTTP client, HTTP server, watch stream, the operator end to end | 4 |
| 6 | B4 suspended computations owning capabilities | yes | HTTP response pull parser, watch stream decoder | 2 |
| 7 | B10 aborts across buffer borrows | yes | JSON parse errors, YAML parse errors | 2 |
| 8 | B17 capability in a computation parameter | yes | retries around a stateful client | 1 |
| 9 | B13 aliased mutable graphs | no | Richards, DeltaBlue, Havlak, CD, LRU, doubly linked list, jlox, clox | 8 |
| 10 | B16 libraries | no | pidigits, regex-redux, k-nucleotide, n-body and spectral-norm output, priority queue | 6 |
| 11 | B9 `imm` duplication, borrowed walks, `imm` reborrow | no | List, AWFY Json lookup, DeltaBlue's views, k-nucleotide's sort, T04, T05 | 6 |
| 12 | B14 data under arrays | no | Storage, B-tree, jlox's AST buffer | 3 |
| 13 | B6 lends per call | no | T04, T09, T14 | 3 |
| 14 | B8 generic answering effects | no | T06, T08, AoC memo by layer | 3 |
| 15 | B12 threads | no | parallel map-reduce, worker pool on cores, parallel quicksort | 3 |
| 16 | B15 containers of `!` functions | no | Richards, clox natives | 2 |
| 17 | B5 borrows across a resuming operation | no | T03's generator form, `parse-recover-gen` | 2 |

**What changed from §6.** The first pass ranked B2 and B1 first because one program gated them.
Counted over the wider set, the elaboration refusals (B7) and data declarations (B3) gate the most
programs, and both are prerequisites of the north star's JSON and YAML. B13 (graphs) is the largest
blocker outside the north star, and it already has a working encoding.

**Outside the target set** after widening: multi-shot search; allocation tracking (`noalloc`);
folds with `X` under `U` (`fold-under-u`); digging and same-lifetime boxing (`dig-bang`, `box-dup`);
a borrowed list's external iterator (#57, beyond B9's borrowed walk); K1 itself (#172); stored
callbacks with rows (#161 B: `callbacks-in-data`, `map-div-fold`, `div-in-adapter`), which no
target program needs once B15 holds; ports beyond B1 (`comp-param-two-sites`, `comp-param-for`).

**Research threads, revised.** Two threads §7 set aside are now used:
- **codata cells and #119's handler-owned region**, for B13 (C-1, C-2);
- **fork-join with a named assumption** (#212's Route 0), for B12 (C-10).

The **BoLo semantic seam** is used as well. The region's `Cell<'r, T>` clause (C-2) is a library
primitive proved against the relation, which is the DRFCaml and RustBelt style. **SILL_S** stays
only the reading of the per-turn lend.

**Surprises, revised.**
- §8 item 2 said the actor route "is not free today". It is writable today, as a scheduler in the
  program that serves the shared state through control operations whose resumption takes the
  answer (`conc/worker-pool-port.bc`, measured). `lib/async.bc` cannot host it, but user code can.
  B-2's kill path is therefore a library, not a lemma.
- `corpus/retry-block.bc` now retries (measured), so #479's "does not retry" no longer holds.
- Permute's recursion inside a counted `for` threading an array runs, while #492 refuses Havlak's
  conditional DFS. #492 fires only in some shapes.
- The clox dispatch `while` is already a flat loop at the flat IR, with no allocation or indirect
  call per instruction (measured).

## 15. Build units, revised for the widened target set

This list supersedes §9. It is fixed and ordered. Each unit names the blocker it removes, its
acceptance programs (added to the corpus with goldens, drawn from §12's set and §2.2's), and a
one-line "done when". A spike has a yes/no question, the program it unblocks and a kill path, and
it ends in a build unit or a documented limit. Every unit that changes which programs are accepted
gets its SPEC entry first; the algebra hard stop applies. The probe programs named are in
`docs/expressiveness-probes/`.

**Track A: elaboration first** (B7; it gates the most programs, and every later acceptance program
is written naturally only after it).

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| A1 | **loops U2, U3, U4** (#549, #550, #551) | B7 (loops) | `docs/loops.md` §5.1's programs; T02, T07, T10; `fannkuch`, `yaml-indent` and `havlak` with `while` where the probes use `for … break`; `corpus/pending/for-*`, `loop-*` | those run as written and the pending ones move to `corpus/` |
| A2 | **the write rule** (#586, #504; the mutation report's D2 with its abort column) covering `modify` blocks (§12.7 defect 1), and **ergonomics E1** (#582) | B7 (writes) | T01, T03, T12 (52 and 5102); `awfy/modify_assign.bc` gives `(6, 7)` or a refusal; `borrow-nested-handback` | no assignment anywhere elaborates to a dead rebinding (each #586 form and defect 1 gives its D2 answer or refusal) |
| A3 | **binding hygiene and early lends**: a callee's binders never reach its caller (§12.7 defect 2); a lend nested in an expression is lifted to a binding (#510, #525) or refused at the lend; a div call's result typed at a generic call; the `match`-in-`with` arm case (defects 3–5); name clashes with the library reported | B7 (hygiene) | `bg/mut-name-capture.bc`, `bg/lend-arith.bc`, `awfy/div_arm.bc`, `awfy/div_generic.bc`, `ns/arm-stdout.bc`, `awfy/name_clash.bc` | each runs or gets a message at its cause, and `reverse-complement` runs with its callee's binder named `tbl` |
| A4 | **#492**: a recursive call inside a counted `for` that threads an array | B7 | `havlak_dfs_rec.bc`, `rec-in-for-linear`, `lc-0039`, `aoc-2020-07` (with A1's #491) | those run with goldens |

**Track B: the north star.**

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| B-1 | **`handle_general`** (#564, on S0 and `Div` in the kernel, landed) and the surface's §21 restriction lifted | B2 | `op-e.bc` as `corpus/operator-one-task.bc`; `yaml-indent.bc` with one `on_exhausted` around its loop over the input; `async-fanout` | those run, and SPEC §21 *Open*'s "a handler around a div computation" is removed |
| B-2 | **spike S-B**: yes/no — is the per-turn task type `box 'd U(νX. (Mut 'x S ⊸ F(Mut 'x S ⊗ (A + box 'd U X))) & F 1)` derivable from §22's affine closure with an argument and §32's threading, with no new compatibility lemma? | B1 (its form) | `operator-reconcile.bc` against a hand-written `spawn_with` | **yes**: B-3 builds the per-turn lend. **Kill**: B-3 builds the port instead, as a library: a scheduler that serves the shared state through control operations, which already runs (`conc/worker-pool-port.bc`) |
| B-3 | **the shared service**: per-turn lend (or the port), with the surface `with h(&mut s) { … with spawn { … } … }` elaborating to it | B1 | `operator-reconcile.bc` (golden `[3, 4, 2]` and the converged cluster); `io-two-tasks`, `async-channel`, `conc/worker-pool.bc`, `conc/pipeline-tasks.bc`, `ns/informer-cache.bc` | `operator-reconcile.bc` moves to `corpus/`, and SPEC §34 *Open*'s "concurrent writers" is removed |
| B-4 | **data declarations** (#489 part 1, #54 stage 8): records, variants, newtypes, patterns, field update through `mut` | B3 | T07, T09, T11; `data-box-tree`; union-find, the arena and the B-tree with distinct `Id` types; n-body's bodies as records | they run as written (spellings aside) and n-body's bench row is no slower |
| B-5 | **spike S-D**: yes/no — does a declaration whose variant holds `List[Self]` elaborate to one `mu`, the list's functions specialised at it, accepted by today's checker? | B3 (nesting) | `data Json = … Arr(List[Json]) \| Obj(List[string * Json])` | **yes**: B-7 uses it. **Kill**: kernel nested `mu` (#182) as its own SPEC entry before B-7 |
| B-6 | **aborts across buffer and literal borrows**: emit `sliceBorrowIU`/`MU`; `fold_lines` over `count_try` | B10 | `abort1.bc`, `config-parse.bc` | both run, and SPEC §18's "a borrow of a buffer or a literal crossed by an abort" is removed |
| B-7 | **JSON and YAML libraries**: parse (raising on malformed input) and print, over B-4's declarations | B3, B10 | `corpus/json-roundtrip.bc` (a Deployment-like resource read, `replicas` changed, printed byte for byte); `corpus/yaml-roundtrip.bc` (the same resource in YAML, to JSON); malformed inputs raising across the input's borrow | both run at every stage and pass `scripts/falsify.sh` |
| B-8 | **`Net`**: an effect served by the platform's outermost handler; connections as linear handles whose `close` returns its error; externs over libc (native) and WASI sockets | B11 | `corpus/net-echo.bc`: a server and a client, both in the language, exchanging a line over localhost | the echo runs natively, and SPEC §11's `Net` moves from *Designed* to built |
| B-9 | **close with a residual** for generators, on S0's residual | B4 | `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io`; `ns/http-gen.bc` (a pull parser over a socket after B-8) | those move to `corpus/` |
| B-10 | **lifetime binders compared up to renaming**, then decision 57's R2a | B17 | `ns/retry-backoff.bc` (retry with a stateful service); `comp-param-capability.bc` | both run, and SPEC §33 *Open*'s R2a row is removed |
| B-11 | **HTTP/1.1 client and server library** over B-8 (request, response, chunked bodies) | B11 | `corpus/http-get.bc`: the client fetches a JSON document from a server written in the language | the client prints the document byte for byte |
| B-12 | **the operator, end to end**: a watch task decoding a stream into an informer cache; N reconcilers sharing the client and cache (B-3); retries with backoff (B-10), timers and cancellation | — | `corpus/operator.bc` against a fake API server written in the language (B-11) | the operator converges three objects, survives a conflict, and cancels its tasks on shutdown with `live 0` |

**Track C: graphs, data and the rest of the set.**

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| C-1 | **`Arena[T]` with `Id[T]` newtypes** in `lib/`, and the `region` elaboration of §13.2 in its unbranded form | B13 | Richards, DeltaBlue, Havlak, CD, LRU, the doubly linked list, jlox, clox, the B-tree, each as a corpus program over the library | all ten run with goldens, and none indexes a raw `array i32` by hand |
| C-2 | **spike S-G** (#119): yes/no — do branded handles into a handler-owned region make every access in bounds by the region-length Kripke fact, as one lemma with no change to the relation? | B13 (bounds) | DeltaBlue over C-1 with its bounds checks gone | **yes**: build it; `bcc-counts` bounds per access drop to 0. **Kill**: checked indices stay, documented as the arena's cost |
| C-3 | **spike S-H**: yes/no — is a destructor and fold for `mu` with `X` under `array` one more `FShape` case of `foldOwn`, one lemma? | B14 | `awfy/storage_array.bc`, `ds/btree-boxed.bc`, `lc-0208-trie-boxed` | **yes**: build it and the three run. **Kill**: tuple children and arenas are the way, documented in SPEC §6 |
| C-4 | **containers of `!` functions**: SPEC §26's weakening by a dead persistent binder, or an elaboration of the tabulator that does not need it | B15 | `awfy/fn_array.bc`, `richards_fnfield.bc`, `lox/fn-in-array.bc`, `lox/map-closures.bc` | those run |
| C-5 | **#58 and #142, implicit copies of `imm`**, and **a borrowed walk of `mu`** (`unroll` at an `imm` view) | B9 | List without `clone`; AWFY Json's lookup returning a view; DeltaBlue's two views; T05 | those run, and List's `copies` are 0 |
| C-6 | **spike S-F** (#174): yes/no — does `axWithborMITy` follow from the anti-frame and a variant of `wpTS_I_frameX` with `hQ` stated at the drop step? | B9 | T04 with `len(&v)` at a `mut` parameter | **yes**: build K2′. **Kill**: `mut`-taking read functions stay the API |
| C-7 | **lends per call**, and **spike S-E** for a looping callee's second borrow | B6 | T04, T14 (`fill(&mut buf)` under the services), `lend-two`; `lend-div-two` if S-E says yes | those run; S-E's kill keeps one borrow per looping callee, documented in SPEC §14 |
| C-8 | **generic answering effects** and `update_with` | B8 | T06, T08, `effects-generic-store`, `lc-0070` | those run |
| C-9 | **libraries**: signed bignum, regex (#225), `%.Nf`, O(n log n) comparator sort and comparator heap over owned elements (#497), map iteration over owned keys; lookup at another lifetime by SPEC §36's constant | B16 | pidigits, regex-redux, k-nucleotide (Game output exactly), n-body and spectral-norm with `%.9f`, `ds/pq.bc` over strings | the Benchmarks Game programs print the Game's exact output |
| C-10 | **fork-join** (#212): `join` and `par_for` over a split context, sequential on Wasm, a work-stealing pool natively; soundness as a named assumption (`ParLaw`, as `PinLaw` is) | B12 | parallel map-reduce (`conc/split-halves.bc` with `join`), parallel quicksort, the worker pool on cores | each gives the same answer on Wasm and native, and runs faster on native with more than one core |
| C-11 | **lend split at suspensions** (tasks) | B5 | `async-bank.bc` as written; T13 in the report's shape | `async-bank.bc` moves to `corpus/`, `unconditional` |
| C-12 | **spike S-C**, then **the lending cursor** | B5 | `parse-recover-gen.bc`; T03's generator form | **yes**: both run. **Kill**: the hand-written cursor (`json-tokens.bc`'s shape) is the way |
| C-13 | **the benchmarks as bench rows**: the 14 AWFY and 10 Game programs in `bench/` with their Rust sides, measured by `make bench` | — | `bench/out/results.md` with every row | every row is within the bound the user sets |

**Track N: lowering, on the new backend** (`docs/compiler.md`'s N1–N5). The first pass's L-1 to L-7
become items of those units. Nothing here is a recovery pass: #540 was stopped by the user as one,
so native loops come by construction from `iterate` and the erasure pass, not from L2b.

| item | was | belongs to | how, by construction | acceptance |
|---|---|---|---|---|
| reads and writes through `mut` at persistent contents as loads and stores | L-1 | N2 | a derived node on the typed term ("contents persistent", as C2b's `divLit`), and an erasure rule with its proof over Core | quicksort and sort-generic within the bound; `bcc-counts` shows no store per read |
| `while`, `loop` and generator bodies as native loops | L-2 | N4 | `iterate` is an LIR loop with loop-carried variables; `tick`'s clause is tail-resumptive, so the erasure pass makes it a direct back edge | sieve ≤ 1.4×, chain-yield ≤ 1.2× (`docs/compiler.md` §5.3); the clox dispatch loop with no `drive` |
| bounds checks where the index is the loop's counter over the view | L-3 | N1 | the typed term carries "counter below `len`" for `count_try` over a view; LIR emits the access unchecked | n-body, sieve-for, quicksort, the AWFY array programs |
| typed pointers, `getelementptr`, aligned arrays | L-4 | N5 | as `docs/compiler.md` §3.4 | sum's loop vectorises |
| the `Exhausted` pass-through as a tail call | L-5 | N2 | the abortive rule's identity (#537 fix 3, merged into N2) | gen-tree, gen-tree-cb ≤ 1.4× |
| 4-byte `i32` slots | L-6 | N1 | layouts from types | quicksort's footprint halves |
| handler state a local variable for a `with` | L-7 | N2 / LIR §3.3 | the handler's scope is one code | handlers-di ≤ 0.9× |
| arena handles without bounds checks | new | N1 (after C-2) | the brand's fact carried on the typed term | DeltaBlue, Richards over C-1 |
| a node reused in place when a list is rebuilt (Towers' re-roll on push) | new | N1 | `foldReuse` (SPEC §6) chosen where the source is owned and dead | Towers' allocations per move fall to 0 |

**Order.** A1–A4; then B-1 to B-12 (the north star runs end to end); C-1 to C-13 in the order
listed. N items go with their N units, beside the other tracks. Any track may run while another is
in progress; within a track the order holds. Every spike ends in a build unit or a documented
limit.

**Outside the target set** (no unit): multi-shot search; allocation tracking; folds with `X` under
`U`; digging and same-lifetime boxing; an external iterator over a borrowed list (#57); K1 (#172);
stored callbacks with rows (#161 B); ports beyond the shared service (`comp-param-two-sites`,
`comp-param-for`); explicit RC; interior mutability beyond the region of C-1/C-2 (#119's
`RefCell`-like projections, #160).
