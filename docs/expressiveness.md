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
| 5 | a generator over a borrowed input, consumed by a `for` inside the borrow (a tokenizer yielding views); a teller task holding a `mut` account across `await` while reading its other variables | `parse-recover-gen`, `async-bank`, T03, T13 | **B5** a borrow cannot be held across a resuming operation (T1, #172) |
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
| B2 div under a handler | `Div` as a handled effect (S0, #554; #564), already in flight | no: Rust has no totality to keep |
| B1 shared service across tasks | **a per-turn lend**: the scheduler owns the service and lends it to the task it resumes, for one turn, which hands it back at its `await`. This is §14's per-observation lend applied to tasks, and Balzer–Pfenning's acquire/release | no. Rust uses `Rc<RefCell<_>>` (run-time flag) or `Arc<Mutex<_>>`; ours is static and free on one thread |
| B7 elaboration refusals | the already-designed units: loops U2–U4, ergonomics E1, #586's write rule | n/a |
| B3 records, variants, nested data | data declarations (#489) whose nested containers **elaborate to one recursive type**, as Lean elaborates nested inductives into mutual ones | partly: Rust's enums and structs, without its `Box` ceremony |
| B4 suspended computations owning capabilities | the cancel-with-residual that S0 already has to settle ("the residual a loop closed early hands back, by a resume with `close`") | no: Rust relies on `Drop`; we have no destructor for a capability |
| B5 borrows across a suspension | **a lending cursor**: a generator whose state is owned (an index) and which is lent the source at each pull. The spanning lend K1 (#172) is not needed for the target set | Rust's own answer is the same index cursor; its self-borrowing generators are not stable |

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
  after B2, the north star waits on exactly one thing: B1.
- A JSON-shaped value is expressible today when its arrays are encoded in the same `mu` (measured,
  `i32[7]`). The blocker is nested `mu` and naming, not recursion.
- An error escaping a borrow of a literal is refused, but the kernel already has the unwinding
  forms of slice borrows (`sliceBorrowIU`, SPEC §19). B10 is a surface gap.
- The per-observation lend that §14 already proves for loops is the same mechanism B1 and B5
  need for tasks and generators. One rule, three uses.

## 1. The target set, and how entries map onto it

The target set is the user's to adjust. Every catalogue entry in §2 names the target program that
needs it, or says **outside the target set**.

| target | what it needs from this document |
|---|---|
| `operator-reconcile.bc` | B2, then B1 (measured, §8 item 1). Nothing else: its other refusals were worked around in the file already (its header) |
| JSON round-trip of a resource | B3 (data declarations; nested recursion), B10 (a parse error raised across the input's borrow); maps of string keys exist (SPEC §36, `bench/wordcount`) |
| T01–T14 | B7 for most; B6 (T04, T09, T14), B3 (T09, T11), B8 (T06, T08), B9 (T04, T05), B5 (T03's generator form, T13's Rust shape); see §2.2 |
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
| a teller task holding its account `mut` across `await` while reading its other variables | `corpus/pending/async-bank.bc`, T13 | refused by R1's closed-body premise (measured); **with the lend split at each `await` by hand it runs, `unconditional`, no `PinLaw`** (measured, `bank-split.bc`) | T13 |
| an iterator over a borrowed list yielding its elements in order | `corpus/pending/print-borrowed-list.bc` (#57) | refused (measured: `iter` does not parse as a value) | outside |
| a function over a borrowed view whose helper loops (a text walker) | `aoc-2020-07`, `for-view-local` (#491) | refused, but this is B7: the source is untyped when the loop is classified (recorded) | — |

**B6: more than one lend at a call.**

| functionality | program | today | target |
|---|---|---|---|
| one call lending a borrowed separator and the output capability | `corpus/pending/lend-two.bc` | refused (measured: a type mismatch) | T14 |
| a looping function that takes two borrows | `reject/lend-div-two.bc` | refused by design (recorded) | T04 (two-view form) |
| a `&mut` buffer filled by a function that also uses injected services | T14 | §18 *Not provided* (by inspection); §2.2 | T14 |
| one place lent `mut` twice to one call | `corpus/pending/two-writers.bc` | refused, as Rust refuses it (measured) | outside |

**B7: elaboration refusals** (each a filed issue; §4.3).

| functionality | program | today | target |
|---|---|---|---|
| a `while` inside a counted `for`; nested counted loops in some nests; a div call in a counted body | `reject/while-in-counted-for.bc`, #503, `docs/loops.md` S1/S2 | refused (recorded) | T03, T04, sieve's forced shape |
| a lend in one arm of an `if` | `for-in-if-lend` (#502), #538 | refused (measured) | T03, T06 |
| a loop-local name equal to a threaded variable | `loop-shadow-*`, `loop-handler-binder` (#493) | refused (measured) | quicksort's forced shape |
| a recursive call inside a counted `for` that threads an array | `rec-in-for-linear`, `lc-0039` (#492) | refused (measured) | outside |
| a write to a captured `let mut` from a block or `run` | #586 | **runs with a silent wrong answer** (recorded on the issue) | T12 |
| an owner borrowed inside another borrow block | `borrow-nested-handback` (#495) | refused (measured) | outside |

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

@@T-TABLE@@

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
| **`Div` as a handled effect** (S0 #554, then #564's `handle_general`): a loop performs `tick`; a handler around a ticking body forwards the ticks; the runtime's driver is the outermost handler | parity once loops lower as loops (#540) | relation: one clause for rows with `Div` (S0's spike settles its form) | best: nothing is written | **recommended**; already planned |
| bound every task's loop (`for _ in 0..n { … break }`), as the measured variant does | parity | none | poor: an invented bound in every task | today's workaround |
| run the scheduler outside every handler, the tasks' services passed in | parity | none | poor: inverts the program | rejected: it moves B1, does not remove it |

**Elaboration candidate.** None is needed at the surface: the program already says what it means.
The structure is in the kernel's effect, which is where decision 67 put it.

**Recommendation.** Land S0 and #564 as planned. Acceptance: `op-e.bc` (one task, `while`, a shared
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
| linear ownership transfer: the service is passed from task to task by hand | parity | none | poor: every task returns the service and the scheduler re-plumbs it | today's only route; it is what `operator-rounds.bc` does synchronously |
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
| **data declarations elaborating to `mu` and pairs/sums** (#489, #54 stage 8), with nested containers elaborated to one recursive type: `Arr(List[Json])` becomes the container's constructors inlined into `Json`'s `mu`, and the container's functions specialised at it | one box per node, as today | none for the declarations (the core types exist); for nesting, none if the inlining is done by the elaborator (hypothesis), lemma-level if instead the kernel lifts "must be closed" (#182, #32) | good | **recommended**. Lean 4 elaborates nested inductives into mutual ones the same way (cited as prior art; our encoding of mutual recursion is one `mu` with a tag) |
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
| **close hands back a residual**: cancelling the generator resumes it with `close`, and it returns what it owns | parity | relation: the same item S0 settles for loops ("the residual a loop closed early hands back, by a resume with `close`, not a cancel", `docs/pipeline-architecture.md` §0) | best | **recommended**: one mechanism with B2 |
| a `linear ctl` iteration effect (no `break`) | parity | lemma | poor: no early exit | a fallback named by SPEC §15 |
| pass the capability per pull (the per-turn lend of B1) | parity | none or lemma (as B1) | fair | the same mechanism as B1; good where the consumer owns the capability anyway |

**Elaboration candidate.** *Writes:* `for b in digits(&mut stdin) { … break … }`. *Elaborates to:*
a stored generator whose `close` observation answers its residual (`ref input`), which the `for`'s
exit hands back to the lender. *Checked by:* S0's clause for the residual. *Memory at the surface:*
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
| §18's rows (a lend in a capability-threading call; a capability through `for … in &a`) | parity | none or lemma (unknown; SPEC records them only as not provided) | good | **recommended** (the mutation report's O7) |
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
| 1 | B2 div under a handler | north star (first cause) | `async-fanout`, `async-stream`, `rec-loop`, #517 | high: decision 67's plan; one relation clause; also unblocks B4 (the residual) |
| 2 | B1 shared service across tasks | north star (second, and last, cause) | `io-two-tasks`, `async-channel`, `async-progress`, T13's Rust shape | high: §14's per-observation lend reused; no new former (hypothesis until spike S-B) |
| 3 | B7 elaboration refusals | T02, T03, T07, T12, most bench "forced shapes" | 13 pending programs (#491–#495, #501–#504, #538, #586) | high: the designs exist and are agreed |
| 4 | B3 data declarations, nested data | JSON round-trip (north star stage 1), T09, T11, n-body | `data-box-tree`, every `inl`/`inr` site (2197, `docs/ergonomics.md` M1) | high: pure elaboration if spike S-D holds |
| 5 | B4 suspended computations owning capabilities | north-star stage 3 (watch stream); not in `operator-reconcile` | `gen-digits`, `gen-lines`, `gen-lazy`, `gen-adapters-io` | high: the same mechanism as S0's residual |
| 6 | B5 borrows across a resuming operation | T03 (generator form), T13 (Rust shape) | `parse-recover-gen`, `async-bank`, `print-borrowed-list` (#57) | medium: the cursor is elaboration; K1 stays open and is not needed |
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

1. **The north star waits on one thing after B2.** `operator-reconcile.bc`'s header names "a task
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
5. **One rule, three uses.** §14's per-observation lend (a borrow scope over a loop is lent again at
   each step, so the loop's state must not hold it) is the mechanism B1 (per turn) and B5 (per
   pull) need. Neither needs K1.
6. **The read-through-`mut` cost is visible only before LLVM.** quicksort's `bcc-counts` shows a
   store per read (measured), while its machine code has single loads (recorded,
   `bench/README.md`). That is why L-1 is a lowering law, not a calculus change.

## 9. Build units

A fixed, ordered list. Each unit names the blocker it removes, its acceptance programs (each added
to the corpus with its golden, from the target set where one applies), and when it is done. Spikes
are marked; each has a yes/no question, the program it unblocks, and a kill criterion, and each
ends in a build unit or a documented limit, never in further research. Every unit that changes
which programs are accepted gets its SPEC entry first, and the algebra hard stop applies.

**Track 1: the north star.**

| # | unit | removes | acceptance | done when |
|---|---|---|---|---|
| 1 | **S0 and `handle_general`** (#554, #564): `Div` as a handled effect; a handler around a ticking body | B2 | `op-e.bc` (one reconcile task with `while`, a shared service; §10.2) as `corpus/operator-one-task.bc`; `async-fanout`; `async-stream`'s second cause | `operator-one-task` runs with its golden, and SPEC §21 *Open*'s "a handler around a div computation" is removed |
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
| 16 | **lend split at suspensions** (tasks): a borrow block whose body awaits is one lend per turn, by U3's live variables | B5 (tasks) | `corpus/pending/async-bank.bc` as written; T13 in its Rust shape | `async-bank.bc` moves to `corpus/` with its golden and `bcc trusted` reports it `unconditional` |
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

@@REPRO@@
