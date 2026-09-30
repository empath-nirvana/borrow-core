# Iteration — design

Status: a design for the user to decide, second pass. Nothing here is built. The runnable examples
it cites are in `docs/iteration-examples/` (outside the corpus and the gate; `run.sh` runs them).

Contents:

- §0 Summary, and the decision asked for
- §1 Why this document exists: PR #132, the first pass, and what the user decided
- §2 Requirements, and the design questions
- §3 What the language has today, and nine facts that constrain every design
- §4 The direction model: push, pull, data with a cursor, and the boundaries between them
- §5 The target programs (the test set)
- §6 Prior art, read from primary sources, and how each treats direction
- §7 The candidates
- §8 Q0: `for` per direction, or no `for`
- §9 The adapters, per direction
- §10 Comparison and recommendation
- §11 The corpus, loop by loop
- §12 Open questions for the user
- §13 The runnable examples, and their counts

---

## 0. Summary

**Direction is real, and the design does not abstract over it.** A producer either owns the loop
and calls its consumer (**push**), or is stepped by its consumer (**pull**). The two are distinct
in the types, and the language says which at every source and every adapter:

- **Push is data.** A producer that owns the loop over data ends because the data ends, so it is
  total. Push adapters are `rf → rf` transducers (Clojure's shape): `map`, `filter`, `take`,
  `scan`, and `flat_map` whose inner source is data all live here, including the ones that emit
  several elements per input.
- **Pull is codata.** A generator is stepped by its consumer (`gen`, `iter`, `loop`, SPEC §7,
  §15). Each step is total; draining one is div (SPEC §14) unless fuelled.
- **Data with a cursor** (a count `a..b`, a view, a lent array) can be pulled for free: the index
  is the cursor. It is the one kind of source that is both.

**A direction change is an explicit operation with a stated cost** (§4.2):

| change | operation | capacity | cost |
|---|---|---|---|
| pull → push | drain: `for` over a pull source, or a fold of it | 1 (the element in hand) | div, inherited |
| push → pull, at most one output per step | the pull side steps the push stage inline, with a local `B ⊕ 1` | 1 | none: it fuses |
| push → pull, at most `k` per step | a buffer of `k` in the pull side's state | `k` | fixed state, no heap |
| push → pull, unbounded | an explicit collect into a heap value | all | one allocation per element, written |
| push → pull, without a buffer | the producer suspended as a generator | — | no allocation; the result is codata, div |

Within one direction stages fuse, because one party owns the loop: push by composing the steps
(foldr/build), pull by composing `next` into one state machine (stream fusion, as today). A
direction change is a fusion boundary; a capacity-1 change is not really one. **The cost of a
pipeline is the number of direction changes above capacity 1**, which the checker knows and
reports, and which a new corpus count, `boundaries`, would track (§4.4).

**Candidates** (§7):

| | model | status |
|---|---|---|
| **A. Data with a cursor** | a `for` over a count, a view or a lent array is K0′ (a counted loop that can stop early) over the data's own length: push, total; the same data pulled by its index is total | the base of every other candidate; pass 1's A, unchanged |
| **B′. Push transducers** | `rf → rf` stages over push sources, state in the state type, composed statically | replaces pass 1's B, whose Mealy restriction existed only to run both ways; Mealy is now the capacity-1 class of B′ |
| **C′. Producers with a declared direction** | a producer written with `yield` is pull (`gen fn`, today's) or push (`push fn`, provisional), by its declaration; a call has that direction wherever it appears | replaces pass 1's C, whose one generator was pushed or pulled by context |
| **D. No `for`** | combinators per direction (D1 with today's closures, D2 with second-class blocks) | Q0's alternative, restated per direction |

**Recommendation** (§10): **A, then B′ written through C′** (the push library's stages are `push
fn`s over push sources, elaborated to `rf → rf` steps), with the boundary adapters of §9 (`zip`,
`through`, `collect`, `suspend`). Q0, whether `for` exists at all, stays open; §8 shows the
programs under each answer, and recommends keeping `for` with one meaning per direction read off
the source's type.

**Corpus** (§11): 145 `for` loops in 84 files of `corpus/` and `lib/`, and 19 in three book
chapters. Every one pulls its source today (132 are drains; 32 are loops inside generator bodies,
pull in and pull out), and every one keeps its meaning and its text under the recommendation: a
`gen fn` stays a pull producer. None crosses a boundary above capacity 1 (the three `zip`s are
pull × pull, the three `flat_map`s pull a pull inner). Two pending programs change text and
become expressible (`for-finite`, `iter-mut`). 61 loops are over finite
producers written as generators, which could be written push and total; none of them is
rewritten, because each is a test or an example of generators, of the per-observation lend, or
of a pull-side rejection.

---

## 1. Why this document exists

### 1.1 PR #132

PR #132 (branch `strings-s4`, open, not merged) was stage S4 of `docs/strings-slices-design.md`
and stage 9 of typed elaboration. Its `for` over a **bounded** source became `count_fold` with
the source's bound, so the function stayed total. The bounded sources were a table of library
names (`range`, `iter_imm`, `iter_mut`, and `map`/`filter`/`enumerate`/`skip`/`scan`/`from_iter`/
`take` of a bounded source) with a bound each. The PR's own text says what is wrong with it: the
bounds are **by name** ("they are bounded when their module is included and the program does not
define them"), **unproved** ("a wrong bound is a wrong answer, never an unsafe run"), dependent on
adapter code (`filter`'s bound holds only because it skips instead of looping), and `for`
accumulated cases. Finiteness recovered from names is rejected.

### 1.2 The first pass, and where it went wrong

The first pass of this document compared four candidates: A (typed data sources), B (Mealy
transducer pipelines), C (a `for` over a gen-fn call inlines the generator) and D (no `for`). It
went wrong at its requirement R2, "adapters written once for all sources", which demanded that an
adapter not care whether it is pushed or pulled. Every candidate paid for it:

- **Today's library** makes everything a generator, so everything is pulled, arrays included.
  That loses the fact that data ends, and it is the root of #132: finiteness had to be recovered
  from names.
- **B** narrowed transducers to Mealy machines (at most one output per input) so they could run
  both ways, and lost `flat_map`. Clojure's `rf → rf` transducers express `mapcat`; they are
  push-only.
- **C** pushed or pulled the same generator call depending on where it appeared, so a producer's
  totality depended on its context.

### 1.3 The user's decision

"I am not sure why we got stuck in sort of ignoring direction, i don't think we can or should."
Direction is real, and this pass builds on these settled points:

1. R2 is dropped. Push and pull are distinct and visible in the types. Push is data: the producer
   owns the loop, is total because data ends, and `rf → rf` transducers live there. Pull is
   codata: a generator is stepped by its consumer, and is div unless fuelled, with a visible "ran
   out".
2. Data with a cursor can be pulled for free. The inherently one-directional things are producers
   that own control.
3. Adapters exist per direction. `map` and `filter` exist twice. `flat_map` is natural on the
   push side. `zip` needs at least one pull side, and the type says which, and hence whether it
   is total.
4. Direction changes are explicit operations with a visible cost: pull → push drains in a loop
   and inherits div; push → pull is a buffer whose capacity is the outputs of one step (1, `k`,
   or an explicit collect into a `box`), or a suspension of the producer as a generator.
5. A direction change is a fusion boundary. The checker knows each one, so it belongs in reports
   (#126), and in a corpus count beside allocations, dispatched calls and copies.

---

## 2. Requirements and questions

From the user and the standing decisions:

- **R1. Total iteration over finite data.** Finiteness comes from types and data, never from
  names or guessed bounds. Nothing may silently truncate a loop.
- **R2. No colouring within a direction.** An adapter is written once per direction, and that one
  definition serves pure, fallible, I/O-performing and (later) suspending sources, by
  instantiation (SPEC §15, generic generators; §14, specialization). This is effect-agnosticism,
  not direction-agnosticism: pass 1's R2 asked for both.
- **R3. Direction in types.** Whether a source is a push producer, a pull producer or data with a
  cursor is fixed by its type or its declaration, never by the context of a call and never by a
  name. So is whether an adapter is a push stage, a pull stage or a boundary.
- **R4. Explicit boundaries, with capacity.** Every direction change is an operation the program
  or an adapter's type states, with its capacity: 1 (local, no allocation), `k` (bounded,
  fixed), unbounded (an explicit collect into a heap value), or none (suspension, which makes
  codata). A change that allocates is visible in the source, as heap allocation is everywhere
  else.
- **R5. Fusion within a direction, and zero cost.** A pipeline in one direction is one loop
  (push) or one state machine (pull), with no allocation and no dispatched call; a capacity-1
  change fuses too. Allocation or indirection only where C or Rust would put it.
- **R6. Borrowing.** Iterate borrowed data, mutate elements in place, use borrowed state and
  capabilities in the body.
- **R7. Honest codata.** Infinite and external streams are supported; draining them is visibly
  div; fuel is the explicit route to totality, with a visible "ran out".
- **R8. Early exit and results**: `break`, `return`, `find`, `take`, and a loop's final value.
- **R9. State in bodies**: `let mut` variables updated by the loop.
- **R10. Effects in a body escape the loop.** A body may perform I/O, capability operations or
  `raise`, and they belong to the enclosing function, handled by enclosing handlers.

Threads are required eventually. They are not designed here; §4.5 notes where direction meets
them.

**Questions each candidate answers:**

- **Q0. Should the language have `for` at all?** Open (§8).
- **Q3.** How does a loop know which kind of source it has? By type (R3); §4.1 gives the table.
- **Q4.** What is an adapter? A push stage, a pull stage, or a boundary (§9).
- **Q5.** Early exit and final values.
- **Q6.** Loop-body state, and how escaping effects interact with it.
- **Q7.** How totality is established, and which existing theorems prove it.
- **Q8.** Fusion and zero cost, per direction and at boundaries.

Settled by the direction decision and removed: pass 1's **Q1** (one notion of iterable or two:
three kinds, §4.1) and **Q2** (push, pull or both, and whether adapters can be written once for
both: both, distinct, per direction).

---

## 3. What exists today

### 3.1 Inventory

| piece | where | direction | what it gives iteration |
|---|---|---|---|
| `fold_own`, `fold_imm`, `fold_reuse` | SPEC §6 | push | total eliminators of `μ` data; a **right** fold |
| `count_fold` (K0) | SPEC §16 | push | the total counted loop; one machine step, no allocation; runs to its bound |
| `tab`, `drop`, `array_map` | SPEC §9; `experiments/PositiveArrays` | push | the array's own loops |
| `[L]` views, K2–K5 | SPEC §9 | data with a cursor | an array lent as a family; split at an index; write at an index |
| `νX. C`, `unfold` | SPEC §7 | pull | codata; `iter A B R` (never skips), `gen A B R` (may skip), `loop B R` |
| div as an effect | SPEC §14 | pull | draining codata is div, inferred; `total` is checked; `div_fuel` is the fuel handler |
| one state machine per body | SPEC §15 | pull | a generator or div body is one `unfold`; no dispatched call |
| specialization at the callback's type | SPEC §14, §15 | — | a higher-order function is copied at a div callback, or at one that yields |
| generators, generic `gen fn`, `lib/adapters.bc` | SPEC §15 | pull | `map`, `filter`, `take`, `zip`, `flat_map`, … as pull stages |
| the per-observation lend | SPEC §14; `lib/lend.bc` | pull | a borrow over a codata loop, lent again at each observation; `array_each_imm` is its push form |
| `for x in V { M }` | `Frontend/Sugar.lean` | pull → push (a drain) | over an `iter` or a `gen` only; always div; threads what `M` assigns and the capabilities |

Every `for` today pulls its source: it is a drain, or a loop inside a generator body (pull in,
pull out). Every total loop today is push, written as a call of `count_fold` or a fold.

### 3.2 Nine facts that constrain every design

- **F1. A loop over data is one computation; a loop over codata is many.** A `count_fold` or a
  fold runs inside one `F`, so a borrow block around it holds the borrow for the whole loop. A
  codata loop is observed step by step, and no borrow spans observations: "a lend that spans
  observations does not close" (`experiments/LoopBorrow`, Verdict). `upper-for.bc` is the
  consequence: `for c in iter_mut(v)` inside `borrow mut` is rejected; the same loop as
  `count_fold` (`upper-count.bc`) is total and runs. **F1 is direction**: a push loop over data
  keeps its borrow, a pulled source cannot.
- **F2. Totality is proved once; truncation is not a safety property.** Every elaborated loop is
  checked core, so `total_no_infinite_run` (SPEC §14) covers every div-free program. A counted
  loop run for too small a count is safe and wrong, so a bound must come from the data by
  construction.
- **F3. `μ` folds are right folds, and `fold_imm`'s result must outlive every lifetime.** An
  in-order iterator over a borrowed list is open (SPEC §7 Open; #57's list half).
- **F4. A generator's skips are unbounded; an `iter` never skips.** `n` observations of an `iter`
  give at most `n` elements, by type; a `gen` may skip any number of times before its next
  element. So one element pulled from an `iter` is one total step, and one element pulled from a
  `gen` is a loop.
- **F5. Closures capture only `!` values, and cannot assign outer variables.** Promotion needs
  `!Γ`: a `!` closure cannot capture an `i32` (#9; `docs/iteration-examples/push-flatmap.bc`
  hit it, "`!thunk` promotes only over `!` types, but `n`, of type `i32`, is used inside"), and
  assignment inside a closure of an outer variable is not provided (decision 38). A `for` body is
  not a closure: it is code in the enclosing body, elaborated in place.
- **F6. A counted loop cannot stop early.** `count_fold` runs to its bound (SPEC §16 Open).
- **F7. `return` in a `fn` body is the core's `return`** (decision 41).
- **F8. A `for` body in a div body must be total** (SPEC §14 Open;
  `corpus/reject/io-for-nested.bc`). A generator body may nest loops.
- **F9. A `!` closure may capture `!` functions, and the backend calls them directly.** A stage
  `!{ (s, x) -> rf(s, f(x)) }` capturing the persistent `rf` and `f` checks, and a pipeline of
  such stages over `count_fold` allocates nothing and makes no dispatched call:
  `push-flatmap.bc` reports 8 closure calls, all direct (`bcc-counts --sites`: "direct 8 (union
  8, flow 0) dispatched 0"). This is what makes `rf → rf` composition possible without
  capturing linear state (§7.2).

**A stale line in SPEC, noted and not edited.** SPEC §14 Open says "A div function has no type
parameters", and §15 Open says "Generic `fn`s: only generators are generic". Both are stale
since #131: `fold-generic.bc` is a generic `fn` with a `for` over a generator
(`fold__g0 : … => U (delay i32)`), and `lib/slice.bc`'s functions are generic `fn`s
(`fn len[A]<'a>`). They should be corrected in the next SPEC change.

---

## 4. The direction model

### 4.1 Three kinds of source

| kind | who owns the loop | types | consumed by | totality |
|---|---|---|---|---|
| **data with a cursor** | whoever consumes it: the index (or the rest) is the cursor | a count `a..b` (syntax); `array_imm 'a A`, `array_mut 'a A`; `&a`, `&mut a` of an array | pushed: K0′ over its length; pulled: one step per element | its length |
| **push producer** | the producer | a `push fn` call, a push pipeline `src |> stage …` (spellings provisional, §7.3); in core, a template over its consumer's state (below) | a step: a `for` body, a fold's step, the next stage | inferred on the instance: total when its loops are over data |
| **pull producer** | the consumer | `U (gen A B R)`, `U (iter A B R)`, `U (loop B R)` (SPEC §7, §15) | observation | each observation total; draining is div; a counted pull of an `iter` is total (F4) |

**A push producer in core** is `count_fold`'s shape with the element added:

    push A   ≈   ∀S E. !(S ⊗ A ⇒ S ⊕ E) ⊗ S ⇒ S ⊕ E

It is given its consumer's step and first state, and answers the last state or the consumer's
exit (K0′'s `inr`, §7.0). The core has no quantifier over `S` at run time: instances are
whole-program monomorphization (SPEC §15, generic functions). So a push producer is a **template**,
instantiated at each consumer's state type, as GHC's `build` takes an argument polymorphic in
the list's result (§6.4). It can be passed to a known function, which is specialized at it (the
mechanism of SPEC §14 for callbacks), but it is not a first-class value that can be stored in
data or returned from an unknown call. A pull producer is a first-class value: it is codata.

**Why push is data.** A push producer's loops are the loops of its body. When they are counted
loops over data (K0′, the folds), the producer is total, and the inference that decides it is the
existing one (SPEC §14). A push producer may also drain a pull source (`for b in bytes(&mut
stdin) { yield b }` declared push); it is then div because of that drain, by the same inference.
So "push is total" is exact for push producers built from data and push stages; direction and
totality meet at the drains.

### 4.2 Direction changes

| from → to | operation (spelling provisional) | capacity | memory | totality |
|---|---|---|---|---|
| pull → push | **drain**: `for` over a pull source; a fold of it | 1: the element in hand | none | div (inherited) |
| push → pull, ≤ 1 output per step | **`through(g, stage)`**: the pull side steps the push stage inline into a local `B ⊕ 1` | 1 | none | the stage's; the pull side as before |
| push → pull, ≤ `k` per step | **`buffer[k]`**: `k` slots and a fill count in the pull side's state | `k` | `k` elements in the state | as above |
| push → pull, unbounded | **`collect`** into a heap value (a list, a boxed array) | the whole output | one allocation per element (or per growth), written in the source | total when the producer is |
| push → pull, no buffer | **`suspend(p)`**: the producer's body elaborated as a generator | none | none: one state machine | codata: draining is div |
| data with a cursor → push | K0′ over its length | — | none | total |
| data with a cursor → pull | its index as the state | — | none | each pull total; a drain bounded by its length is K0′ |

The capacity of a push → pull change is **the number of outputs of one step** of the push stage
at the boundary. It is a property of the stage's type: a Mealy stage (`T ⊗ A ⇒ T ⊗ (B ⊕ 1)`)
has capacity 1; a stage emitting at most `k` (a UTF-8 encoder, at most 4 bytes per scalar) has
`k`; `flat_map` has the length of its inner source, unbounded unless the inner's type bounds it.

**Buffer or suspension.** They trade the same things in opposite directions. A buffer keeps
totality and pays memory (a `collect` of a total producer is total, and pulling the result is
pulling data with a cursor). A suspension pays no memory and gives up totality by type: the
generator's skips are unbounded (F4), so its consumer is div. `boundary-collect.bc` and
`boundary-suspend.bc` are the two sides of one program (240 with 10 allocations, total; 660 with
none, div; they differ in order because the collected list is last-first). Suspension needs the
producer's body, which a push producer has, being a template.

### 4.3 Fusion, and where it stops

- **Push fuses by composing steps** (Gill, Launchbury and Peyton Jones's foldr/build, §6.4): the
  source's loop calls the composed step, and each stage's step calls the next. With the stages
  known at the consumer, every call is to known code: `push-flatmap.bc`, four push stages over a
  count with a nested `flat_map`, is 0 allocations, 0 dispatched calls, 0 copies, total.
- **Pull fuses by composing `next`** into one state machine per body (SPEC §15, stream fusion
  with the skip): `corpus/gen-pipeline-adapters.bc` is 0, 0, 0 today.
- **At a change of owner neither inlining crosses.** A push producer cannot be composed into a
  `next` without suspending it, and a pull producer cannot be composed into a step without a
  drain loop. What the boundary materialises into is its buffer.
- **A capacity-1 change is not really a boundary**: the pull side steps the push stage inline,
  and the slot is a local `B ⊕ 1`. `boundary-cap1.bc` runs one Mealy stage both ways, 0, 0, 0.
- **A drain is capacity 1 too**: the element in hand is the loop's variable, and the push stages
  after it are inlined into the drain's body. A drain costs div, not memory.

So **the cost of a pipeline is its number of direction changes above capacity 1**: each is a
buffer the program wrote (`buffer[k]`, `collect`), or a suspension, which is visible as the
codata it makes. The checker knows each at elaboration.

### 4.4 Reports and a corpus count

- **Reports** (#126): each direction change above capacity 1 is reported with its position, its
  capacity, and its kind (bounded buffer, collect, suspension), as a lend or a div inference is.
  Drains are reported as the div they cause (today's report).
- **The count `boundaries`** (proposed, not implemented): a fourth column of
  `corpus/counts.expected`, `name allocs indirect copies boundaries`, the number of direction
  changes above capacity 1 in the elaborated program. It is static (a property of the program,
  counted at elaboration), where the other three are per run; a buffer's run-time cost already
  shows in `allocs`. It would read 0 for every corpus program today (§11). Of §13's programs,
  T12's two surface forms would read 1 each (`collect`, `suspend`); `zip-push-pull.bc` and
  `boundary-cap1.bc` would read 0 (capacity 1). As hand-lowered today none has a boundary the
  elaborator knows of. Like the other columns, a rise fails the gate and a fall is reported.

### 4.5 Threads (noted, not designed)

A buffer between two threads is a channel: capacity `k` is a bounded channel, capacity 1 a
one-slot channel, and an unbounded collect an unbounded queue, which this design would only allow
written. A push producer on one thread and a pull consumer on another is the producer/consumer
pair, and the channel is the boundary. A suspension is the one-thread form of that pair: the
producer runs when the consumer asks. Fan-in (`zip`, the operator's `merge`) pulls from several
producers, so across threads it is a `select`; fan-out (`tee`, `unzip`) pushes to several
consumers. Nothing here closes a door on those: the boundary is already a named operation with a
capacity.

### 4.6 Borrowing, per direction

F1 is direction. A push loop over data is one computation, so a borrow block around it holds the
borrow for the whole loop, and an element may be lent `mut` to the body. A pull producer is
observed between steps, so what it holds cannot hold the borrow; the per-observation lend (SPEC
§14) is how a pull loop uses borrowed state. `upper-for.bc` (rejected today) is a pull loop over a
view; the same loop as a push over the view is `upper-count.bc`'s, accepted and total.

---

## 5. The target programs

The test set. Each is written once in the syntax the `for` candidates aim at (spellings are
provisional: `a..b` for a count, `for x in v` over a view, `&a`/`&mut a` lending an array, `|>`
for a pipeline, `for … else` for a loop's value when it does not break). Each program is marked
with its direction. A `-- runs:` line names an example that runs today in some form.

### T1 `io-wc` (corpus) — a drain

```
fn count(c: In) -> In * (i32 * (i32 * i32)) =
  let mut lines = 0; let mut words = 0; let mut chars = 0; let mut in_word = false;
  for b in bytes(&mut c) {                    -- pull → push: drain; div
    chars = chars + 1;
    if b == 10 { lines = lines + 1 };
    if is_space(b) { in_word = false }
    else { if not(in_word) { words = words + 1 }; in_word = true }
  };
  (c, (lines, (words, chars)))
-- runs: wc-for.bc (today's syntax, unchanged)
```

### T2 `split-at-mut` (P10) — push over data

```
total fn reverse<'a>(v: slice mut 'a u8) -> () =
  let n = len_mut(&mut v);
  for i in 0..(n >> 1) { swap_at(&mut v, i, n - 1 - i) }          -- a count: push, total

total fn upper<'a>(v: slice mut 'a u8) -> () =
  for c in v { modify c { x -> if b'a' <= x && x <= b'z' { x - 32 } else { x } } }   -- a view

main -> i32 =
  let mut b = read_all(&mut stdin);                     -- div: reads to the end
  let n = len_of(&b);
  borrow mut b { v -> match split_at_mut(v, n >> 1) { inl (l, r) -> reverse(l); upper(r) | inr _ -> () } };
  write_all(&mut stdout, &b);
  n
-- runs: corpus/split-at-mut.bc (count_fold and a hand-driven iterator)
```

### T3 the slice programs (P7, P12, the library) — push over data

```
for x in &mut a { modify x { v -> v * 10 } };            -- P12
let s = for x in &a { acc = acc + *x };                   -- a sum over a lent array
total fn find<'a>(v: slice 'a i32, x: i32) -> i32 + 1 =
  for i in 0..len(v) { if at(v, i) == x { return inl i } };       -- R8: early return
  inr ()
total fn sort<'a>(v: slice mut 'a i32) -> () =            -- P7: nested total loops
  let n = len_mut(&mut v);
  for i in 1..n { for k in 0..i {
    let j = i - 1 - k;
    if peek(&mut v, j) > peek(&mut v, j + 1) { swap_at(&mut v, j, j + 1) } else { break } } }
-- runs: upper-count.bc, find-break.bc (library `find`), corpus/sort-numbers.bc (library `sort`)
```

### T4 the strings design's loops (P1–P15)

| program | loop | direction | needs |
|---|---|---|---|
| P1 `fields` | `for i in 0..(k + 1) { match split_once(rest, sep) … }` | push over a count | state `rest`, `found` |
| P1 `main` | `for b in bytes(&mut stdin) { … borrow line { v -> … } … }` | drain | a borrow block in the body; capabilities |
| P2 `parse-int` | `for d in digits { acc = … }` | push over a view | error state |
| P3 `replace_all` | `for _ in 0..(len(&rest) + 1) { … }` | push over a count (the user's fuel) | the count is stated |
| P5 `utf8-count` | `t |> chars |> count` | push: `chars` is a Mealy stage over the view's bytes | total pipeline over data |
| P6 `key-value` | `for l in t |> lines { … push(&mut pairs, …) }` then `for p in ps { … }` | push over a view; push over a view | total pipeline; capability in the body |
| P7 `sort-lines` | nested counts; `for l in v { write_str(&mut stdout, *l) }` | push | nested loops; I/O body |
| P9 `http-request` | `for h in headers { … }` | push over a view | state is an owned buffer |
| P10 `split-at-mut` | T2 | push | `mut` leaves |
| P12 `iter-mut` | T3 | push over a lent array | `mut` leaves under a lend |
| P13 `labels-json` | `for c in t |> chars { … push_char(&mut s, c) }` | push | total pipeline |
| P14 `args` | `for i in 0..n { … read_arg(&mut args, i, &mut arg) … }` | push over a count | capabilities in the body |

### T5 the operator's loops (`docs/operator/operator.bc`) — pull, and one push inside a generator

```
fn watch<K>(api, sel, rv, t) -> Iter<WatchEvent<K>, ()> = generate {       -- 1.6
  let resp = send(&watch_req(api, sel, rv, t));
  if resp.status == 410 { raise(KubeError::Api(gone())) };
  let events = resp.body |> chunks |> lines |> map(|line| decode(&line));   -- pull: body is codata
  for ev in events { yield(ev) } }                  -- drain inside a generator; Async, Fail

fn watcher<K>(api, sel) -> Iter<Event<K>, never> = generate {
  loop { match try { let (items, mut rv) = list(api, sel);
                     for o in items { yield(Apply(o)) };        -- push over data (a Vec), inside a generator
                     yield(Resync);
                     loop { for ev in watch(api, sel, &rv, 290) { rv = …; yield(…) } } } {
         … Err(e) -> sleep(backoff.next()) } } }

fn triggers(cfg, stop) -> Iter<Trigger, ()> =                  -- pull: merge is fan-in
  merge(from_crs, from_deps) |> take_until(stop) |> debounce(1.s, trigger_key) |> inspect(…)

fn serve_metrics(l: Listener) -> never =
  for conn in accept_all(l) { … respond(conn, 200, &b) }        -- drain, forever: div, Async

fn run_controller(triggers, concurrency, grace, reconcile)       -- for_each_concurrent: a drain across tasks
fn diff(a, b) = … |> filter_map(…) |> collect()                   -- push over data, then a collect
```

`for o in items { yield … }` inside a generator is a push over data whose consumer is a
suspension point: the generator's body is a state machine, and the view loop is a state holding
its index (§7.0, *Bodies*).

### T6 Advent-of-Code loops

```
-- (a) sum per line (corpus/io-aoc.bc): a drain
for b in bytes(&mut stdin) { if b == 10 { sum = sum + num; num = 0 } else { num = num * 10 + (b - 48) } }

-- (b) the largest group sum (2022 day 1): a drain, or a pull pipeline and a drain
for b in bytes(&mut stdin) { if b == 10 { if nl { best = max(best, cur); cur = 0 } else { … } } else { … } }
-- runs: aoc-groups.bc (for), aoc-groups-pipe.bc (a pipeline)

-- (c) the two entries summing to 2020: nested push over counts, exit across both
total fn solve<'a>(v: slice 'a i32) -> i32 + 1 =
  for i in 0..len(v) { for j in (i + 1)..len(v) {
    if at(v, i) + at(v, j) == 2020 { return inl (at(v, i) * at(v, j)) } } };
  inr ()
-- runs: aoc-pair.bc (nested count_fold, no early exit)

-- (d) a histogram into an array (a drain), then the most frequent (push over a count)
let mut counts = box array(26, zero);
for b in bytes(&mut stdin) { if is_lower(b) { modify_at(&mut counts, b - 97, { c -> c + 1 }) } };
let mut best = 0;
for i in 0..26 { if at(&counts, i) > at(&counts, best) { best = i } };

-- (e) iterate to a fixed point: genuinely may not end
loop { let next = step(&grid); if next == grid { break }; grid = next }     -- div, honestly
for _ in 0..1000 { … }                                                       -- or fuel, explicitly
```

### T7 `zip` — a boundary adapter

```
for (x, y) in zip(gen_a(), gen_b()) { … }        -- pull × pull: div            runs: zip-pull.bc
for (x, y) in zip(0..6 |> map(ten), pows()) { … } -- push × pull (an iter): total  runs: zip-push-pull.bc
for (x, y) in zip(&a, gen_b()) { … }              -- push × pull (a gen): div
for (x, y) in zip(&a, &b) { … }                   -- push × data: the second pulled by its index, total
for (x, y) in zip(&mut a, &b) { *x = *x + *y }    -- a `mut` view driven, an `imm` one pulled
for (x, y) in zip(p, q) { … }                     -- push × push: rejected; one side is
                                                  --   collected (total) or suspended (div)
```

### T8 an infinite stream with `take` — pull

```
for x in take(fib(), 10) { acc = acc + x }       -- runs: take-fib.bc (div; a `gen` may skip)
```

Total only if `fib` is an `iter` pulled under a count (F4), or fuelled.

### T9 early return, and a final value — push over data

```
fn first_neg<'a>(v: slice 'a i32) -> i32 + 1 =
  for x in v { if *x < 0 { return inl *x } };
  inr ()

let r = for x in v { if p(*x) { break *x } } else { default };     -- Zig's loop value
```

### T10 a body that only does I/O (R10) — push over data

```
for x in &a { put_dec(&mut stdout, *x); putb(&mut stdout, 32) }    -- runs: print-for.bc, print-count.bc
```

### T11 `flat_map` over data — push, total

```
total fn f() -> i32 =
  let mut acc = 0;
  for y in 0..5 |> flat_map(i -> 0..i) |> filter(pos) |> map(sq) |> take(3) { acc = acc + y };
  acc
-- runs: push-flatmap.bc (hand-lowered: `rf → rf` stages over count_fold), 6, total, 0/0/0
```

### T12 a pull consumer of a many-output push stage — a boundary

```
let ys = 0..5 |> flat_map(i -> 0..i) |> collect;            -- unbounded: written, allocates
for (x, y) in zip(0..20 |> map(ten), ys) { acc = acc + x * y }
-- runs: boundary-collect.bc (total, 10 allocations); boundary-suspend.bc (suspended, div, 0)
```

---

## 6. Prior art

The reading was done for this document from primary sources: language references, standard
library source, papers and blog posts by the designers. Each subsection lists what was read. A
claim marked *(read as code)* was inferred from source code, not quoted. Sources that could not
be fetched are named; nothing is taken from them. §6.1–§6.9 are the first pass's reading; §6.10
adds, for each design, how it treats direction, from a second reading listed there.

### 6.1 Rust: `Iterator`, `IntoIterator`, `for`

**Read:** the Reference, "Loop and other breakable expressions" (iterator loops, labels, `break`
values); std `Iterator` (`next`, `fold`, `try_fold`, `for_each`) and the `std::iter` module docs;
`AsyncIterator` and futures `Stream`; RFC 3513 (`gen` blocks); the GAT stabilization post
(lending iterators); PR #45595 (`try_fold`); issue #28728 (opening post only); N. Popov, "Rust ❤
LLVM" (LLVM Dev Meeting 2024 slides).

- **Q0–Q3.** `for` desugars to `IntoIterator::into_iter` and a `loop` over `next`, with the body
  forced to `()`. One pull trait for all sources; `iter`/`iter_mut`/`into_iter` choose the
  ownership mode. Types do not distinguish finite from infinite ("`ones.min()` … Oh no! An
  infinite loop!").
- **Q2, Q8.** Push exists as provided methods on the same trait (`fold`, `try_fold`, `for_each`),
  and adapters override them for speed: `for_each` "may also be faster than a loop, because it
  will use internal iteration on adapters like `Chain`". `try_fold` was added later (PR #45595),
  and every other method delegates to it ("Change this method with care!").
- **Q5, Q6.** The body is inline, so `break`, `return` and `?` act on the enclosing function; in a
  `for_each` closure "`break` and `continue` are not possible". `for` has no value.
- **Q7.** None; issue #28728 shows an unsoundness from LLVM deleting side-effect-free infinite
  loops.
- **Paid.** No lending iterator (GATs made the trait expressible; `for` cannot drive it). A second
  hierarchy for async (`Stream`, still unstable in std). `gen` blocks cannot hold a borrow across
  `yield` and have no final value (RFC 3513). No close step, no residual.
- **For us.** Rust's pull trait carries push as provided methods, and the push path is the fast
  one (`Chain`); the direction model makes them two things instead (§6.10). The inline body is what
  makes `return` and `?` work.

### 6.2 Lean 4: `ForIn` and "do unchained"

**Read:** S. Ullrich and L. de Moura, "`do` Unchained: Embracing Local Imperativity in a Purely
Functional Language", PACMPL 6 (ICFP 2022) art. 109, §§1–10 (the author's copy; the ACM PDF was not
reachable); lean4 sources `Init/Core.lean` (`ForInStep`, `ForIn`, `ForIn'`),
`Lean/Elab/BuiltinDo/For.lean`, `Init/While.lean`, `Init/Data/Range`, `Std.Iterators`
(`IterStep`, `Finite`, `Productive`), PR #13209; the reference manual's iteration chapters.

- **Q0, Q6.** `for` is one `forIn xs init f` call, `f : α → β → m (ForInStep β)`, with
  `ForInStep = done | yield` carrying the loop state. The paper translates `let mut` as `StateT`
  layers, `return` as `throw` in `ExceptT`, and `break`/`continue` as two more `ExceptT` layers:
  "by separating every extension into its own effect … we will not have to worry about how to
  preserve the state on break". The shipped elaborator instead packs the reassigned variables in
  a tuple; `break` is `done tuple`, `return e` is `done (some e, …)` dispatched after the loop.
  This is today's `forLoop` and §7.0's exit rule.
- **Q7.** "using fold-like traversal as a primitive is particularly interesting for total
  languages … because it delegates the issue of termination to the combinator": `for` over a
  `List`, `Array` or `Range` terminates by its instance ("A `for` loop terminates with the
  collection it iterates"). `while` was a `partial def`, opaque to proofs, until PR #13209.
  `Std.Iterators` has `IterStep = yield | skip | done` and termination as `Prop` classes
  (`Finite`, `Productive`) that adapters propagate: `take` of a productive iterator is finite,
  `filter` is productive only over a finite base. Fusion there "is not guaranteed".
- **Q2.** `forIn` is push; parallel `for x in xs, y in ys` pushes `xs` and pulls `ys`.
- **Paid.** The verified translation (StateT/ExceptT over `List`) is not the shipped elaborator,
  so the theorem does not cover the production code. Allocation-free loops needed CPS monad
  transformers and heavy specialization. `mut` scoping rules were added after bugs.
- **For us.** "`for` is a fold with an inferred accumulator" is exactly Lean's design, with the
  same exit encoding (§7.0). Lean's `Productive`/`Finite` are the typed version of our F4: `iter`
  is productive by its type. Its warning: prove what ships (§7.0's lemma is about the template
  the elaborator emits).

### 6.3 Clojure transducers

**Read:** clojure.org "Transducers" (reference, all sections); R. Hickey, "Transducers are Coming"
(2014); `clojure/core.clj` (`transduce`, `sequence`, `reduced`, `take`, `partition-by`,
`halt-when`, `Eduction`), `TransformerIterator.java`; core.async `chan`, `pipeline`.

- **Q1–Q4.** A transducer is `rf → rf`: it calls the downstream reducing function "0 or more
  times", has a completion arity to flush state, and composes by function composition. It "does
  not care" about the source: collections, lazy sequences and channels run the same transducer.
- **Q2.** Push only. Pull (`sequence`, `eduction`) is by buffering the outputs of each step, which
  may be unbounded (`cat`).
- **Q5.** Early exit is a dynamic wrapper, `(reduced x)`, that every process must check and
  "convey"; a distinct final value needs a sentinel (`halt-when`).
- **Q6.** Stateful transducers keep state in `volatile!` boxes created per use, "unsafe for use
  across threads".
- **Paid.** No lockstep `zip` in the push core (read as code: multi-input exists only in
  `sequence`'s pull path, and channels need a separate `async/map`). Protocol rules are prose.
- **For us.** B′ is transducers with the state in the type, since our closures capture only `!`
  values (F5, F9), and `reduced` is K0′'s `inr`.

### 6.4 Haskell: foldr/build and stream fusion

**Read:** A. Gill, J. Launchbury, S. Peyton Jones, "A Short Cut to Deforestation", FPCA 1993 (§3,
§7–9); D. Coutts, R. Leshchinskiy, D. Stewart, "Stream Fusion: From Lists to Streams to Nothing at
All", ICFP 2007 (§§1–4, 6.3, 7–10, via an archived copy); the GHC User's Guide on rewrite rules;
GHC base's fusion notes; O. Kiselyov et al., "Stream Fusion, to Completeness", POPL 2017 (§1, §3).

- **foldr/build (push).** `foldr k z (build g) = g k z`; a producer is written against its
  consumer's `cons`. It cannot fuse both inputs of `zip`: "The list xs may disappear … but ys never
  will".
- **Stream fusion (pull).** `Step a s = Done | Yield a s | Skip s`. Skip "is not necessary for the
  semantics but … is crucial for the implementation … it is what allows all stepper functions to
  be non-recursive" (for `filter`). The price is a Skip-invariance obligation "we do not have a
  formal proof" of. It fuses `zip`, but depends on the optimizer: "Stream fusion by itself does
  not … reduce allocation"; `concatMap` is "quite fragile"; about 5% of programs got
  "dramatically" worse.
- **Rules.** "GHC makes absolutely no attempt to verify that the LHS and RHS of a rule have the
  same meaning", nor confluence or termination; sharing a list stops `foldr/build` from firing.
- **Paid.** Fusion is never guaranteed. Kiselyov et al.: "Rather than relying on an optimizer to
  eliminate artifacts of stream composition, we do not introduce the artifacts in the first
  place."
- **For us.** Our `gen` is stream fusion's `Step` with a skip, and our pull form already fuses
  without an optimizer (one state machine per body). C′'s `push fn` is foldr/build with `yield`
  as `build`'s `cons`, applied by the elaborator at every call, so it fires by construction,
  which is Kiselyov et al.'s point. foldr/build pushes one side of `zip` and pulls the other,
  which is §9's `zip`.

### 6.5 Koka and Effekt

**Read (Koka):** *The Koka Programming Language* (§2.3–2.6, §3.1.4, §3.2, §3.3.6, §3.4); std
`core.kk` (`while`, `for`, `for-while`, `fold-while`), `core/undiv.kk`; D. Leijen, "Koka:
Programming with Row-polymorphic Effect Types", MSFP 2014 (§2.7, Theorem 4); D. Leijen, "Type
Directed Compilation of Row-Typed Algebraic Effects", POPL 2017 (§2.3, §4.1, §5.1).
**Read (Effekt):** the Effekt tour (loops, computations, captures); stdlib `stream.effekt`,
`control.effekt`; J. Brachthäuser, P. Schuster, K. Ostermann, "Effects as Capabilities", OOPSLA
2020 (§1–2); P. Schuster et al., "Compiling Effect Handlers in Capability-Passing Style", ICFP
2020.

- **Koka.** No loop statements: `while`, `for`, `foreach` are library functions with trailing
  lambdas; generators are a user effect. Early exit is a `maybe` result (with opposite polarities
  in `for-while` and `fold-while`); `return` in a lambda does not leave the enclosing function.
  Koka is the one surveyed system that types divergence (`div`, Theorem 4: `div ∉ ε` implies
  termination), but its `for`, `repeat` and `fold` are typed total through `pretend-decreasing`,
  "_Unsafe_ … Use with care to not accidentally allow actual divergence". Specialization makes a
  trailing-lambda `for` cheap.
- **Effekt.** One native loop (`while`); the rest are functions over **second-class blocks**, which
  "can neither be returned nor stored in data structures. The loss of expressivity is the price
  for an effect system which we argue is significantly more lightweight". Effects of a block
  "propagate to the call-site … handled in the lexical scope where f was written": R8 without
  threading. Two stream notions, `emit` (push) and `next`/`stop` (pull), with connectors, so
  adapters are written for one or the other. `break`/`continue` are a `Label` capability passed to
  the block. Its producers return their result beside the fold (`returning::` variants), the one
  analogue in the survey of our `gen`'s finishing value. No termination story.
- **For us.** Koka shows what `total` loops cost without data eliminators: a trusted escape hatch.
  Our K0′ and folds make that a theorem. Effekt's second-class blocks are D2, and its
  capabilities are ours (decision 30).

### 6.6 Swift, C++ ranges, Java streams

**Read:** Swift `stdlib/public/core/Sequence.swift` (the doc comment behind the `Sequence` page),
`docs/SequencesAndCollections.rst`, SE-0298 (`AsyncSequence`); cppreference (range-for, ranges,
`filter_view::begin`), P2214R1, P3329R0 (N. Josuttis, "Healing the Filter View"); Java SE 21
`java.util.stream`, `Stream`, `Spliterator`, JEP 485 (Gatherers), B. Goetz on checked exceptions
(lambda-dev, 2013). Not read: developer.apple.com (did not render), a primary source for Java's
missing `zip`.

- **Swift.** `for-in` over `makeIterator().next()`; `Sequence` makes "no requirement … whether they
  will be destructively consumed", so `Collection` marks multi-pass. `AsyncSequence` duplicates
  the hierarchy; an early exit calls no close.
- **C++20 ranges.** One `range` concept with sentinels; lazy views composed with `|`. Paid:
  `filter_view` caches `begin()`, and P3329R0 reports the view library "considered to be unusable
  and dangerous for many companies … Most of the broken use cases are a consequence of the fact
  that filter views cache begin()".
- **Java streams.** Collections are finite; streams "need not" be, are consumed once, and are
  push-driven, with a `Spliterator` offering both `tryAdvance` (pull) and `forEachRemaining`
  (push, "should be overridden whenever possible"). Finiteness is a run-time flag (`SIZED`).
  Short-circuiting is a property of an operation. Paid: checked exceptions in lambdas ("a 2x
  explosion in SAM types"), no `zip`, and a user extension point (Gatherers) added after three
  JEP rounds.
- **For us.** Java's `SIZED` is PR #132's bound as a run-time flag; ours must be the type former.
  Every one of these duplicated its API for effects (async, throwing), which R2 (no colouring
  within a direction) exists to avoid.

### 6.7 OCaml `Seq` and `Iter`

**Read:** the OCaml `Seq` documentation; the `iter` library's README, `Iter.mli`, `Iter.ml`.

- `Seq` (`unit -> 'a node`) is pull, has `zip`, and allocates per element. `Iter`
  (`('a -> unit) -> unit`) is push: "Control is not handed back to the caller before the whole
  iteration is over. This makes zip impossible to implement", but any internal traversal is an
  `Iter`, and with flambda it compiles "to an actual loop with no overhead". `Iter.take` exits by
  a local exception.
- **For us.** The push/pull trade in one ecosystem, as two libraries: the direction model's two
  adapter libraries (§9).

### 6.8 Briefly

- **Kotlin** (kotlinlang.org, inline functions, sequences): a lambda may `return` from the
  enclosing function "if the function the lambda is passed to is inlined"; `crossinline` forbids
  it. Non-local exit from a block depends on inlining, which our specialization provides.
- **Zig** (language reference): loops are expressions; "break, like return, accepts a value …
  When you break from a while loop, the else branch is not evaluated." The `else` is the value on
  exhaustion (§12, question 5).
- **Python** (Reference §8.3, PEP 380): `for … else`; a generator's `return v` is
  `StopIteration(v)`, which `yield from` receives and a `for` discards; `close()` forwards
  `GeneratorExit`. The closest mainstream analogue of `gen`'s finishing value and `close`.
- **Scala** (Scala 3.4 specification, ch. 6; `scala.util.boundary`): `for` is "defined by
  translation to invocations of four methods: map, withFilter, flatMap, and foreach"; early exit
  is `boundary`/`break`, non-fatal exceptions.
- **Agda sized types** (the Agda manual): sizes track depth "across definition boundaries", but
  `--sized-types` "is inconsistent with constructor-based guarded corecursion" and is off by
  default. A bound in the type is the literature's answer to "a finite producer passed as a
  value"; it is not proposed here.
- Elm, and Haskell as a loop-free language: no source was fetched; §8.3 cites Haskell only
  through the fusion papers.

### 6.9 What the survey says, collected

| system | notions | push/pull | Q5 early exit | Q7 totality | paid |
|---|---|---|---|---|---|
| Rust | one trait, no finite/infinite split | both on one trait | inline body; `try_fold` | none | `Stream` split; no lending `for` |
| Lean 4 | `ForIn` (push) and `Iter` (pull) | push `for`, pull `zip` | `ForInStep.done`, return slot | `for` over data by its instance; `Finite`/`Productive` as proofs | shipped ≠ verified |
| Clojure | any reducible or channel | push; pull by buffering | `reduced` sentinel | none | no zip; mutable state |
| Haskell | lists | foldr/build push, streams pull | laziness, `Done` | none | fusion never guaranteed |
| Koka | none; per container | push | `maybe`; effects | `div` typed; loops by `pretend-decreasing` | trusted totality |
| Effekt | `emit` and `next` effects | both, with connectors | `Label` capability | none | second-class blocks; two stream notions |
| Swift | `Sequence`/`Collection` | pull | inline | none | async hierarchy |
| C++ | `range` concept | pull | inline | none | `filter_view` hazards |
| Java | collections and streams | push, `Spliterator` both | short-circuit ops | none | checked exceptions; no zip |
| OCaml | `Seq` and `Iter` | one each | stop forcing; exceptions | none | two libraries |

No surveyed system types "finite data" at the loop and proves loops over it terminate without a
trusted step, except Lean for its own collection instances. Every push design lacks a two-sided
`zip`, and every pull design pays for external iteration or skips. The inline loop body is what
makes `break`/`return`/`?` direct; the closure-based systems add machinery for them (Koka's
`maybe`, Kotlin's `inline`, Effekt's `Label`, Scala's `boundary`, Lean's return slot).

### 6.10 Direction, per design

**Read for this pass** (quotes below are from these, fetched 2026-09-30):
Go: `src/iter/iter.go` (package doc, "Pulling Values", `Pull`), `src/runtime/coro.go`, and the
Go blog "Range Over Function Types" (go.dev/blog/range-functions, "Pull iterators").
R. Nystrom, "Iteration Inside and Out" (journal.stuffwithstuff.com, 2013-01-13) and its part 2
(2013-02-24, the Ruby and fibers section).
Clojure: `src/jvm/clojure/lang/TransformerIterator.java` (all), `src/clj/clojure/core.clj`
(`sequence`, `cat`, `mapcat`, `eduction`, `Eduction`), `RT.java` (`chunkIteratorSeq`),
clojure.org/reference/transducers.
O. Kiselyov, A. Biboudis, N. Palladinos, Y. Smaragdakis, "Stream Fusion, to Completeness", POPL
2017 (arXiv 1612.06668: §3, §6.1, §6.3, §6.4 Theorem 1, related work).
A. Gill, J. Launchbury, S. Peyton Jones, "A Short Cut to Deforestation", FPCA 1993 (§9); A.
Farmer, C. Höner zu Siederdissen, A. Gill, "The HERMIT in the Stream", PEPM 2014 (§1, §3, related
work).
Rust: `library/core/src/iter/traits/iterator.rs` (`for_each`, `try_fold`),
`iter/adapters/zip.rs`, `iter/adapters/flatten.rs`.
Lean 4: `src/Init/Core.lean` (`ForIn`), `src/Init/Data/Iterators/Basic.lean`,
`Consumers/Monadic/Loop.lean`, `Combinators/Monadic/FlatMap.lean`,
`src/Std/Data/Iterators/Combinators/Monadic/Zip.lean`, `src/Std/Data/Iterators.lean`.
withoutboats: "Iterators and traversables", "Generators", "poll_next", "Iterator and generator"
(without.boats/blog).
O. Kiselyov, "Towards the best collection API" (okmij.org/ftp/papers/LL3-collections-enumerators.txt)
and "Searching for the best enumerator" (okmij.org/ftp/Scheme/enumerators-callcc.html).
Java SE 21 `Spliterator`. Kotlin `kotlinx-coroutines-core/common/src/flow/internal/Combine.kt`.

**Could not be fetched this pass**, and nothing is taken from them here: the ICFP 2007 stream
fusion paper (its `zip` and `concatMap` claims below come from HERMIT and Kiselyov et al.; §6.4's
quotes are from the first pass's archived copy), Meijer's "Your Mouse is a Database" (403), the
kotlinlang.org Flow pages. Not attempted: Python, Swift, C# `IObservable`, Lean's "do unchained"
for direction.

- **Go.** Push is the standard type, `type Seq[V any] func(yield func(V) bool)`: "The standard
  iterators can be thought of as 'push iterators', which push values to the yield function." Pull
  is a pair of functions, not a named type, and "Pull iterators are not supported directly by the
  for/range statement." The conversion is a call: `Pull` "converts a standard push iterator to a
  'pull iterator'". Its mechanism is a runtime coroutine (read as code: `newcoro`, and
  `coroswitch` on every `next`), which the runtime describes as "like a special channel that
  always has a goroutine blocked on it", and "Coros are heap allocated and garbage collected". A
  pull iterator needs `stop`: "there is no way to force the yield function to return false".
  `zip` is done by pulling both sides: "sometimes we may need to iterate over two containers in
  parallel … we use a different kind of iterator: a pull iterator." **For us:** direction in the
  types, push as the loop's own form, and push → pull as an explicit call that suspends the
  producer: our `suspend`, paid there with a heap-allocated coroutine and here with a state
  machine.
- **Nystrom.** "With an internal iterator, the code that generates values decides when to invoke
  the code that uses that value." Interleaving two internal iterators "you simply can't solve
  … unless you're willing to reach for some heavy weaponry like threads or continuations", and
  "Whoever gets put on top of the stack is in the weaker position". He names the push → pull
  costs this design names: Ruby's `zip` "converts its arguments to arrays before doing anything",
  an unbounded collect; a generator reifies one stack frame ("they only reify one"); Ruby's
  `to_enum` "spins up a new fiber", a whole-stack suspension. **For us:** `zip` is a pull
  operation; the three ways across are `collect`, `suspend` of one body, and a thread.
- **Clojure `sequence`/`eduction`.** A transducer is "independent from the context of their input
  and output sources"; `Eduction` implements both `Iterable` and `IReduceInit` (read as code). The
  pull path is a buffer between the transducer and the iterator (read as code,
  `TransformerIterator`): the terminal step adds each output to a buffer that goes `Empty` →
  `Single` → `Many`, and `Many` is a `LinkedList` with no bound; a source element is pulled only
  when the buffer is empty. With `cat`/`mapcat` a step's whole inner collection goes into the
  list. `sequence` over several collections pulls each (`MultiIterator`: "until any one of the
  colls is exhausted"). **For us:** exactly §4.2's buffer, with capacity the outputs of one step:
  `Single` is capacity 1, `Many` an unbounded heap queue that the program does not see. Here the
  unbounded case is a written `collect`, and `zip`'s pull is at the inputs, as in `sequence`.
- **Kiselyov et al., "Stream Fusion, to Completeness".** "Whereas push streams represent a stream
  as a fold, pull streams, dually, are the expression of an unfold." "Where push streams stumble
  is the zipping of two streams … This simply cannot be done with constant per-element processing
  cost"; "Rx is push-based and supports zip at the cost of maintaining an unbounded intermediate
  queue." Their stream type records rate: "Exactly one stream element is produced per advance in
  state. We call such streams linear … What destroys it is filtering and nesting." A zip with a
  linear side steps the linear one inside the other's loop; a zip of two nested streams must
  "convert one of them to a linear stream … 'reifying' a stream", and "There is no way around
  this". Their Theorem 1: "The resulting code—with the sole exception of pipelines zipping two
  flat-mapped streams—constructs no data structures beyond those constructed by" the user's own
  functions, and for two streams "both made by flattening inner streams … the rate-adjusting
  allocation is inevitable, even in hand-written code". And the loop is push-shaped: "the consumer at the end of
  the pipeline generates the loop". **For us:** their "linear" is our capacity-1 (Mealy) class,
  which crosses for free; `zip` of two `flat_map`s is the one boundary that must allocate or
  suspend, and they prove that is inherent. Their staging does statically what B′ does by
  specialization.
- **GHC, foldr/build and its dual.** Gill et al. §9: "there seems to be no easy way to extend the
  technique here so that both input lists to zip may be deforested … The list xs may disappear
  using the foldr/build transformation, but ys never will." HERMIT (2014): "The unfoldr/destroy
  system fuses zip and foldl, but cannot fuse filter or concatMap. Stream Fusion improves on
  unfoldr/destroy by fusing filter, but it still cannot fuse concatMap"; "As the dual to
  foldr/build, the unfoldr/destroy approach cannot fuse unzip"; and `concatMap` fails because
  "the generator for the inner stream … is not statically known in the body of go2", so it cannot
  be inlined. **For us:** push (foldr/build) fuses `flat_map` and not `zip`; pull (unfold, stream
  fusion) fuses `zip` and not `concatMap`. That is §9's inventory: `flat_map` push, `zip` pull,
  `unzip` push. Our pull `flat_map` fuses anyway because `yield from` is a state of one machine,
  not an unknown inner stepper.
- **Rust.** `Iterator` is pull, and push is provided methods on it: `for_each` "may also be faster
  than a loop, because it will use internal iteration on adapters like `Chain`", and `try_fold`'s
  note asks implementors to call `try_fold` "on the internal parts". `FlatMap`'s pull form keeps
  one suspended inner iterator (`frontiter`, read as code); its push form is nested folds. `Zip`'s
  general `next` pulls both; for two `TrustedRandomAccess` sources ("random-accessible
  efficiently", with an exact `size_hint`), `fold` is `for i in 0..len { … self.get_unchecked(i) }`
  (read as code), a hidden unstable specialization. **For us:** a `zip` of two indexed sources is
  one counted loop: data with a cursor is pulled for free, which Rust recovers by specialization
  and we have by type (A).
- **Lean 4.** Two types: `ForIn` is push (`forIn (xs : ρ) (b : β) (f : α → β → m (ForInStep
  β))`), and `Iter`/`IterM` is pull (`IterStep = yield | skip | done`; "Allowing `skip` steps is
  necessary to generate efficient code from a loop over an iterator"). Consumers of an `Iter` are
  loops built on `ForIn` ("The basis is a `ForIn`-style loop construct"), the drain. No conversion
  from `ForIn` to `Iter` was found. Termination is typed on the pull side: `Finite`
  ("terminates after finitely many steps") and `Productive` (a value "after finitely many
  skips"). `zip`'s state holds the left side, a memo of one left element, and the right side
  (read as code), and is `Finite` "only if either `left` or `right` is finite and the other is
  productive"; `flatMap` holds one suspended inner iterator. **For us:** the nearest system: two
  types by direction, a drain from pull to push, a capacity-1 memo in `zip`, and `Productive` as
  the typed form of our F4 (`iter` never skips, so pulling one element is one step).
- **withoutboats.** An iterator is "a state machine yielding a number of values, one after
  another"; "'internal iteration' is not iteration at all, but rather an alternative form of
  'traversal.'" Generators are "an imperative syntax for writing functions that compile to
  iterators": the pull side, written in the push style, with the state machine generated.
  **For us:** `gen fn` is exactly that, and stays the pull side; `push fn` is the traversal.
- **Kiselyov, enumerators.** "a left-fold-like combinator with premature termination … is
  superior: in efficiency; in ease of programming; in more predictable resource utilization", and
  any such enumerator converts to a cursor by `call/cc`: "the enumerator and its caller act as
  coroutines". **For us:** push with early exit (K0′) as the primary form, and pull recovered by
  suspending the producer (`suspend`, a state machine rather than `call/cc`).
- **Java `Spliterator`** has both directions on one type, "individually (tryAdvance()) or
  sequentially in bulk (forEachRemaining())". **Kotlin `Flow.zip`** (read as code) collects the
  second flow in a `produce` coroutine into a channel, "This approach only works with rendezvous
  channel": push → pull by suspension, with a capacity-0 hand-off.

**Direction, collected:**

| system | direction in types | push → pull | pull → push | `zip` | `flat_map` |
|---|---|---|---|---|---|
| Go | push `Seq`; pull a pair of functions | `iter.Pull`: a heap coroutine | `for` over `next` | pulls both | push |
| Clojure | none (a transducer is either) | buffer: 1, or an unbounded `LinkedList` | `reduce` | pulls the inputs | push; pull via the unbounded buffer |
| Kiselyov et al. | rate (linear/nested) in the stream type | reify one side (suspension) | the consumer's loop | linear side stepped inline; two nested: allocate | push |
| GHC | none (rules) | — | — | foldr/build: one side only; stream fusion: both | foldr/build: yes; stream fusion: fragile |
| Rust | pull trait; push as methods | — | `for` | pulls both; by index when both indexed | pull keeps one inner; push nests folds |
| Lean 4 | `ForIn` push, `Iter` pull | none found | loops on `ForIn` | one-element memo | one suspended inner |
| Nystrom (Ruby) | — | collect to arrays; fiber | — | pulls | — |
| Kotlin `Flow` | push `Flow`, pull `Sequence` | coroutine + rendezvous channel | — | suspends the second | — |
| **this design** | cursor data, push, pull, by type | `through` (1), `buffer[k]`, `collect`, `suspend` | drain | a pull or cursor side, by type | push; pull via `yield from` |

Every system that lets a push producer be pulled either buffers (Clojure's list, Ruby's arrays,
Rx's queue) or suspends it (Go's coroutine, Kotlin's channel, a generator, a fiber). None makes the
buffer's capacity part of the program; Clojure's is silent and unbounded. Kiselyov et al. show
that among fused pipelines only a `zip` of two nested streams must allocate, which is §9's one
boundary that neither `through` nor a cursor covers.

---

## 7. The candidates

### 7.0 What every candidate shares

**Source kinds, by type former** (§4.1). The elaborator reads the source's type, never its name:

| kind | types | eliminator | termination |
|---|---|---|---|
| count | `a..b` (syntax; two `i32`s) | K0′ over `[a, b)` | the count, a machine step (SPEC §16) |
| view | `array_imm 'a A`, `array_mut 'a A` | K0′ over `len(v)`, leaf `i` by `idx` (`imm`) or `split_first_mut` (`mut`) | the view's own length |
| lent array | `&a`, `&mut a` of `a : array A` | `slice_borrow_*` (K2) around the view loop | as the view |
| push producer | a `push fn` call or a push pipeline (§7.2, §7.3) | its body, instantiated at the consumer | inferred on the instance |
| never-skip codata under a count | `U (iter A B R)` with an explicit count | K0′ over the count, one observation per step | the count (fuel, stated) |
| pull producer | `U (iter A B R)`, `U (gen A B R)`, `U (loop B R)` | a drain: a state of the body's machine (today's `for`) | none: div |
| `μ` data | `μX. T` | the folds (bottom-up), or not a `for` source (§12, question 6) | size of the value |

A count is a *syntactic* form: the core is structural (decision 9), so `range(a, b) : i32 * i32`
would make every pair a count.

**K0′: a counted loop that stops early.**

    count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)

    (μ, count_try (f, (n, (i, s)))) ↦ (μ, case f (i, s) { inl s′ → count_try (f, (n, (i + 1, s′)))
                                                        | inr e  → inr e })       if i < len(n)
                                    ↦ (μ, inl s)                                  otherwise

It is `count_fold` with an exit: the step answers the next state or an exit value. `break e`,
`return e`, `find`'s answer, `take`'s end, and (later, #18) a `raise` are exits. It is Clojure's
`reduced` as a sum in the step's type rather than a wrapper every process must check (§6.3).
Its proof is `countLoop_wp`'s induction with one more case; its lowering is `count_loop` with one
more branch. It is the one kernel change: a push stage's early exit and a `for` body's `break`
both need it (F6; `push-flatmap.bc`'s `take` carries its counter to the end of the count without
it).

**The completeness lemma.** F2 says the relation does not prove that a loop visits every element.
For the view eliminator this is one template, `count_try` over `n = array_len(v)` with leaf `i`
taken by `idx (v, i)`, and its completeness is a fact about three machine steps (`count`,
`array_len`, `idx`): for every `i < n`, `idx` answers `inj₁ (ℓ + i)`. It can be proved once in
`Support/`, on the step relation.

**Bodies** (Q6, R9, R10). The body of a `for` is code in the enclosing body, not a closure (F5),
so it may read and assign `let mut` variables, use capabilities and borrows. The elaboration
threads what the body assigns and the capabilities it uses, as today's `forLoop` does and as
Lean's `do` does (§6.2). What escapes is decided by the body's computation type:

| body's effect | push (data, push producers) | pull (a drain) |
|---|---|---|
| total (capabilities, threaded) | K0′; the enclosing function stays total | a machine state; div |
| exits (`break`, `return`, later `raise`) | K0′'s `inr`; every exit hands on the threaded variables and hands back the capabilities | today's `break`; the iterator closed first |
| suspends (a div call, a nested drain, `yield`, later `wait`) | a machine state holding the cursor (the index, or the rest of the view); the function is div or a generator because of its body | a machine state (today) |

The last row lifts F8. A push loop over a locally lent array whose body suspends uses the
per-observation lend with an index in the state (`lib/lend.bc`'s `array_each_imm`), since the
view cannot be held across observations (F1).

**Exits and threaded state.** Every way out of a loop (the end, `break`, `return`, a raise, and
for a drain `close`) hands on the current values of the threaded variables, hands back what has
no destructor, and drops the rest (SPEC §12). This is today's `break`'s rule.

### 7.1 Candidate A: data with a cursor (the base)

**Model.** A `for` whose source is data with a cursor is K0′ over the data's own extent, total.
Data with a cursor pulled by a consumer (the second side of a `zip`, a pull adapter over a view)
is its index in the consumer's state, one step per element, total. PR #132's name table is
deleted: `range` becomes `a..b`, and `iter_imm(v)`/`iter_mut(v)` are not needed as `for` sources
(`for x in v`). A never-skip pull source under an explicit count (§12, question 7) is K0′ over the
count.

**The programs.** T2, T3, T9, T10, P7, P9, P10, P12, P14 total, as written in §5. T6c: the inner
`return` is K0′'s exit through both loops. T1, T6a–b, T5 unchanged (drains). P5, P6, P13 and T11
(pipelines over a view) are not expressible as pipelines in A alone: the program writes the loop
over the view itself.

**Split.** Kernel: K0′. Library: nothing new; the name table goes. Elaboration: the data-kind
dispatch in `for` (PR #132's `forTotal`, keyed by type former instead of name), `a..b`, PR #132's
array lend `&a`/`&mut a`, exits through K0′. **Cost:** small. Proof: K0′ and the completeness
lemma.

### 7.2 Candidate B′: push transducers (`rf → rf`)

**Model.** A push stage is a function from its downstream step to its upstream step:

    stage : !(S ⊗ B ⇒ S ⊕ E) ⇒ !((T ⊗ S) ⊗ A ⇒ (T ⊗ S) ⊕ E)        (T: the stage's own state)

It may call the downstream step zero or more times per input (Clojure's "0 or more times"), so
`flat_map` with a data inner source is a stage that runs the inner's counted loop inside its step.
A pipeline is a source applied to the composition of its stages and a terminal step; the source
owns the loop (K0′ over data, or a drain of a pull source). This replaces pass 1's B: a Mealy
stage (`T ⊗ A ⇒ T ⊗ (B ⊕ 1)`) is the capacity-1 class of B′, and lifts to it (`mealy_rf` in
`boundary-cap1.bc`); it is kept as a class because it is what crosses to the pull side for free
(§9).

**Composition stays capture-free.** F5 forbids a closure to capture anything that is not `!`.
Three ways were weighed:

- **Closures over `!` functions, with state in the type (chosen).** A stage's step captures only
  the downstream step and the stage's function argument, both `!` (F9). What a stage keeps from
  element to element, and any argument that is not `!` (an `i32` count), is a component of the
  state type `T`, initialized by the pipeline's first state. `push-flatmap.bc` does exactly this;
  its `take` had to move its count from an argument into the state when F5 rejected the capture.
  The first state of a pipeline is then a tuple of each stage's initial state and the terminal's.
- **Inlining.** The stages are generic functions known at the consumer, so the elaborator can
  specialize each at its function argument (the mechanism SPEC §14 uses at callbacks), and every
  call in the composed step is to known code. Today the backend's 0-CFA already finds one code at
  each of the example pipelines' calls (all direct in `push-flatmap.bc`, `zip-push-pull.bc`,
  `boundary-cap1.bc`, `boundary-collect.bc`). I have not established that it does for every
  pipeline under a monovariant analysis (two pipelines sharing a stage instance at one type with
  different functions); specialization would make it so by construction, where the analysis
  makes it so by finding it. Kiselyov et al.'s point (§6.4, §6.10) is to not rely on the finding.
- **Defunctionalization.** A pipeline as first-order data (a sum of stage kinds) interpreted by
  one step function. It closes the set of stages (a program cannot add one) and puts a `case` on
  the stage kind in every step. Not proposed.

**Early exit.** A stage exits through K0′'s `inr` (`take`'s end, `take_until`, `find`). The
source's loop stops, and every stage's state is dropped by the exit rule (§7.0). Without K0′ a
stage carries a finished state to the end of the count, which is `push-flatmap.bc`'s `take`.

**First-class pipelines.** A push pipeline is a template in its consumer's state (§4.1), so it
is second-class: it may be passed to a known function, which is specialized at it, and it may
not be stored or returned from an unknown call. A function that takes a push pipeline and stays
total is such a specialization. This is the one thing pass 1's B had (a `Pipe` value of fixed
type) that B′ does not; §12, question 2.

**The programs.** As A, plus: T11 total, 0/0/0 (`push-flatmap.bc`). P5, P13 (`t |> chars`), P6
(`t |> lines`) total, `chars` and `lines` being Mealy stages over the view's bytes (a UTF-8
decoder is one byte in, at most one scalar out). T7's push × pull `zip` (§9). T6b's pipeline over
the input is a drain into push stages: div, and with no list allocations once `lines` yields
views of a buffer.

**Split.** Kernel: K0′. Library: the push stages (`lib/push.bc`, provisional name) beside
`lib/adapters.bc`, which stays the pull library. Elaboration: A's, plus `|>` and a `for` over a
push pipeline (the source's loop with the composed step and the body as the terminal step). **Cost:**
medium, mostly the library. Proof: none beyond A: stages are ordinary code.

**Written by hand, B′ is unpleasant**: an `rf → rf` stage is a closure returning a closure over
explicit state (`push-flatmap.bc`). C′ is how the library and users write stages.

### 7.3 Candidate C′: producers with a declared direction

**Model.** A producer written with `yield` has **one** direction, fixed by its declaration:

- `gen fn f(…) -> A, B = S` is a **pull** producer, today's, unchanged: its call is a
  `U (gen A B R)`, first-class codata.
- `push fn f(…) -> A, B = S` (spelling provisional) is a **push** producer: its body is the
  template of §4.1, with `yield e` meaning "call the consumer's step on `e`" and `return`/the
  body's value its finishing value. It is foldr/build's `build` with `yield` as the `cons`,
  applied by the elaborator at every call, since the call has no other meaning.

A call has its declaration's direction wherever it appears. Pass 1's C pushed a `gen fn` call
under a `for` and pulled it elsewhere, so the call's totality depended on its context; C′ drops
that. A `for` over a `gen fn` call is a drain, always; a `for` over a `push fn` call is a push
loop, always.

**Push adapters in direct style.** A push stage is a `push fn` over a push source, and its body
reads like today's pull adapter:

    push fn map[A, B](src: push A, f: !(A => B)) -> B = for x in src { yield f(x) }
    push fn flat_map[A, B](src: push A, f: !(A => push B)) -> B = for x in src { for y in f(x) { yield y } }
    push fn take[A](src: push A, n: i32) -> A = let mut k = n; for x in src { if k == 0 { break }; yield x; k = k - 1 }

`for x in src` over a push parameter is the push consumer, so the body elaborates to the `rf → rf`
stage of B′ (the loop's threaded variables are the stage's state `T`, `break` is K0′'s exit), and
`push-flatmap.bc` is the hand-lowered form. `map` and `filter` exist twice, once `gen fn` and
once `push fn`, with nearly the same text; that is accepted (§1.3). `zip` does not exist as a
`push fn`: it needs a pull side (§9).

**Totality is inferred on the instance.** A `push fn` whose loops are over data is total; one
that drains a pull source, or has a `while`, is div; the existing inference decides, after
elaboration, with nothing bounded and nothing to truncate.

**Crossing to pull.** `suspend(p)` (provisional) elaborates a push producer's body as a
generator: the same body, `yield` now a suspension point (SPEC §15's machine). No allocation;
the result is codata. `collect(p)` is the buffer. Neither is implicit.

**The programs.** As B′, with the stages written in direct style. T5: `for o in items { yield
(Apply(o)) }` inside a generator is a push over data inside a pull producer's body (§5, T5). T7:
`zip(p, q)` of two push producers is rejected; `zip(p, suspend(q))` is div, `zip(p,
collect(q))` total and allocating.

**Split.** Kernel: K0′. Library: the push stages as `push fn`s. Elaboration: A's and B′'s, plus
`push fn` (the body elaborated as a template at each consumer, reusing `makeInst` and the
specialization of SPEC §14) and `suspend` (the body elaborated by SPEC §15's machine). **Cost:**
medium. The push elaboration is a substitution into a generic instance's body, with the join
function and the exits of pass 1's C; what changes is that it is selected by the declaration.
Proof: none beyond A.

### 7.4 Candidate D: no `for`, per direction

**Model.** No loop syntax; iteration is combinators, with `|>` (not yet provided: decision 40):

- push side (data, push producers): `fold`, `try_fold`, `for_each`, `find`, `any`, `all`, `sum`,
  `count`, and the stages, over K0′ and the folds; total;
- pull side (generators): `drain`, `fold`, `for_each`, … over the machine; div;
- boundaries: `zip`, `through`, `collect`, `suspend`, as functions.

Generators keep `gen fn` and `yield`; their bodies still need a loop over their source, so D keeps
`for`/`while` inside `gen fn` bodies or a pull primitive (`next(it)`).

Two variants, by what a combinator's body can be:

- **D1: today's closures.** A body is a `!` closure capturing only `!` values (F5, F9). Every
  `let mut` variable, capability and borrow the body uses is a component of the accumulator;
  early exit is the step's answer (`try_fold`).
- **D2: second-class blocks.** A block argument `{ x -> … }` to a known function may capture
  linear state, assign `let mut` variables, lend, and exit with `break` and `return` (Kotlin's
  inline lambdas, Effekt's blocks; §6.5). It is elaborated by the existing specialization: the
  function is copied at the block, the block's captured state becomes extra state of the copy's
  loop, and an exit is a K0′ exit. A push producer is then exactly a function taking a block,
  and `for x in p { B }` is `p({ x -> B })`.

**Direction under D.** The combinator's name says the direction: `fold` over a push source is a
push loop, over a pull source a drain. D2 makes a push producer and a block the same thing (the
producer calls the block), which is B′/C′ with the block in place of the step; the direction
decision makes D2 more natural than it was in pass 1, not less.

**Cost.** D1: small for the library, large for the corpus (§11). D2: large: second-class blocks
are a new elaboration feature with its own rules. **Cannot express:** D1: a body that uses a
capability or a `let mut` without threading it by hand; D2: nothing of the test set, once blocks
exist.

### 7.5 Dropped and merged

- **Pass 1's B (Mealy pipelines)** is merged into B′: its restriction to one output per input
  existed so that one transducer could run both ways. Under direction-in-types a stage is push;
  Mealy is the class that crosses to pull at capacity 1 (`through`). Its `Pipe` value, a
  first-class total pipeline, is §12's question 2.
- **Pass 1's C (one producer, pushed or pulled by context)** is replaced by C′. Its mechanism
  (inline the producer's body at the consumer, `yield` as the consumer's step) survives as the
  elaboration of `push fn`; its selection by context does not.
- **Pass 1's A** is kept as the base, unchanged.

---

## 8. Q0: `for` per direction, or no `for`

Q0 is open. It is the one decision here that is hard to reverse: it fixes how the corpus, the
book and every user program read. Under the direction model a `for` has two possible meanings,
one per direction of its source:

- over **push** (data with a cursor, a push producer): the body is the consumer's step, inlined;
  the loop is the producer's (K0′ over data); total when the producer is.
- over **pull** (a generator): the body is inside a drain loop; div.

### 8.1 Three answers

**(i) `for` over both, its meaning read off the source's type.** One syntax; the source's type
says whether the loop is push or a drain, and the function's inferred divergence reports a
drain. Nothing is chosen by context: a source has one direction (R3).

```
for b in bytes(&mut stdin) { chars = chars + 1 }                  -- a drain: div
for x in &a { put_dec(&mut stdout, *x) }                          -- push over a view: total
for y in 0..5 |> flat_map(i -> 0..i) |> map(sq) { acc = acc + y }  -- push: total
```

**(ii) `for` over push only; a pull source is drained by name.** A `for` whose source is pull is
rejected; the program writes the drain, `for b in drain(bytes(&mut stdin)) { … }`, where `drain`
turns a pull producer into a push producer that is div. The pull → push change is in the text
at every drain, and "a `for` is push" is a rule.

```
for b in drain(bytes(&mut stdin)) { chars = chars + 1 }           -- written drain: div
for x in &a { put_dec(&mut stdout, *x) }                          -- push: total
```

**(iii) No `for`: D.** With D1 today's closures (every accumulator and capability threaded by
hand, `wc-fold.bc`, `aoc-pair.bc`, `print-count.bc`); with D2 blocks, `bytes(&mut stdin) |>
drain |> for_each({ b -> chars = chars + 1 })`, `&a |> for_each({ x -> put_dec(&mut stdout, *x)
})`. Under the direction model, D2's `for_each` over a push producer *is* the producer called
with the block, so `for` is sugar for it; the choice is whether to keep that sugar.

### 8.2 The programs side by side

**T1 `io-wc`.** (i): today's text, `wc-for.bc`. (ii): the same with `drain(bytes(&mut c))`. D1
(`wc-fold.bc`, runs): a named step over a 4-tuple accumulator and a library fold of the stream.
D2: `bytes(&mut c) |> drain |> for_each({ b -> chars = chars + 1; … })`.

**T6c, nested push loops with an exit across both.** (i) and (ii):

```
for i in 0..n { for j in (i + 1)..n {
  if at(v, i) + at(v, j) == 2020 { return inl (at(v, i) * at(v, j)) } } };
inr ()
```

D2: `(0..n) |> find_map({ i -> ((i + 1)..n) |> find_map({ j -> … }) })`. D1 (`aoc-pair.bc`, 36
lines, runs): two nested `count_fold`s carrying the answer, no early exit.

**T10, an effect-only body.** (i)/(ii): `for x in &a { put_dec(&mut stdout, *x) }`. D1: a
`count_fold` with `stdout` in its state (`print-count.bc`). D2: `&a |> for_each({ x -> … })`.

**T11, a push pipeline.** (i)/(ii): `for y in 0..5 |> flat_map(…) |> … { acc = acc + y }`. D1:
the pipeline's terminal is a `fold` with a closure over the accumulator. D2: `|> for_each({ y ->
acc = acc + y })`.

**The operator** (T5). Its pipelines are already combinators (`merge(…) |> take_until(stop) |>
debounce(…)`), its drains are `for` inside `generate { }` and `serve_metrics`, and its
combinator bodies are blocks that capture borrows and perform effects (`retry(…, { … })`,
`span(…)`): D2's blocks, which it needs with or without `for`.

### 8.3 Trade-offs

- **Visibility of the drain.** (ii) writes every pull → push change; (i) leaves it to the source's
  type and the div report. Under (ii), 129 loops of the corpus and the book gain `drain(…)`
  (§11.2), 63 of them over input. R4 asks that direction changes be explicit; a drain has
  capacity 1 and no memory cost, and its one cost, div, is already reported by inference and
  checked by `total`. So (i) meets R4 through the type, (ii) through the text. Precedent is
  split (§6.10): Lean's `for` over an `Iter` drains without a word (its loops are built on
  `ForIn`), which is (i); Go's `for`/`range` takes only push iterators ("Pull iterators are not
  supported directly by the for/range statement"), so a Go drain is a loop the program writes
  over `next`, which is closer to (ii).
- **Readability and familiarity.** `for`, `break` and `return` read as in Rust, Python, Swift, Zig
  and Lean. D1 reads worse on this test set, for a reason specific to this language: its bodies
  capture nothing linear (F5). D2 reads as well as `for`, once blocks exist.
- **Where the machinery lives.** `for` needs threading of assigned variables and capabilities,
  lends in the body, `break`/`return`, and the choice of eliminator by the source's type. D2
  needs all of it in block specialization, where every higher-order function uses it. The choice
  is where the machinery lives, not whether it exists.
- **Precedent** (§6). With `for` over one abstraction: Rust, Swift, C++, Zig, Python; Lean's `for`
  is push (`ForIn`) with a pull second source. Without loop statements: Haskell, Koka, Effekt,
  Clojure.

### 8.4 Where this pass lands on Q0

Keep `for`, with answer (i): one meaning per direction, read off the source's type, so that the
direction decision costs no program its text and the drain's cost (div) stays where it is
reported today. Plan for `for` to become D2's `for_each` with a block when blocks exist, so that
the machinery ends up in one general mechanism. (ii) is the choice if the user wants every drain
in the text. The user decides; §12, questions 0 and 1.

---

## 9. The adapters, per direction

**Push stages** are `push fn`s over a push source (C′), elaborated to `rf → rf` steps (B′).
**Pull stages** are today's `gen fn`s in `lib/adapters.bc`. **Boundary adapters** change
direction and state their capacity.

| adapter | push | pull | outputs per input | notes |
|---|---|---|---|---|
| `map`, `inspect` | yes | yes (today) | 1 | Mealy |
| `filter`, `filter_map` | yes | yes (today) | ≤ 1 | Mealy; a pull skip is a filtered-out element |
| `enumerate`, `scan` | yes | yes (today) | 1 | state in `T` (push) or in the machine (pull) |
| `skip`, `take`, `take_until` | yes; `take`/`take_until` exit by K0′ | yes (today) | ≤ 1 | early stop closes a pull source; ends a push loop |
| `chunks(n)`, `batch`, `windows(k)` | yes | yes (today: `chunks`, `batch`) | ≤ 1 | the group is state: a list today (allocates per element), an array of `n` later |
| `lines`, `chars` (bytes → lines, UTF-8 → scalars) | yes | yes (today: `lines`) | ≤ 1 | Mealy; with views of a buffer, `lines` allocates nothing |
| `chain(a, b)` | yes: `a`'s loop, then `b`'s | yes (today: `yield from`) | — | sequential composition of sources, same direction |
| `flat_map(f)` | yes: `f(x)` a push source, run inside the step | yes (today: `f(x)` a generator, `yield from`) | unbounded | natural on the push side; total when the inner is data |
| `from_iter` | — | yes (today) | 1 | an `iter` as a `gen` |
| `tee`, `unzip`, `partition` (fan-out) | yes: the step calls two consumers | no: needs a buffer as large as the lag | — | push-only |
| `merge` (fan-in, the operator) | no | yes | — | pull-only; across threads a `select` |
| terminals `fold`, `sum`, `count`, `find`, `any`, `all`, `for_each` | total over data | div (a drain) | — | exist twice |

**Boundary adapters:**

| adapter | direction change | capacity | memory | totality |
|---|---|---|---|---|
| `zip(p, g)`, `g` an `iter` | push `p` drives; `g` pulled once per element | 1 | none | total (F4; `zip-push-pull.bc`) |
| `zip(p, g)`, `g` a `gen` | push drives; `g` pulled until an element | 1 | none | div (skips unbounded) |
| `zip(p, d)`, `d` data with a cursor | push drives; `d` pulled by its index | 1 | none | total |
| `zip(g, h)`, both pull | both pulled (today's `zip`, `gen_pull`) | 1 each | none | div |
| `zip(p, q)`, both push | rejected: one side must be `collect`ed or `suspend`ed | — | — | — |
| `through(g, stage)` | a push stage with ≤ 1 output, stepped by a pull side | 1 | a local `B ⊕ 1` | the stage's (`boundary-cap1.bc`) |
| `buffer[k](g, stage)` | a push stage with ≤ `k` outputs per step, pulled | `k` | `k` slots in the state | the stage's |
| `flat_map` under a pull consumer | push stage, pull consumer | the inner's length: unbounded | `collect` or `suspend` | total with `collect`; div with `suspend` |
| `collect(p)` | push → pull (or → data) | all | written heap allocation (`boundary-collect.bc`: 10 for 10) | total when `p` is |
| `suspend(p)` | push → pull | none | none | div by type (`boundary-suspend.bc`) |
| `drain(g)` / `for` over pull | pull → push | 1 | none | div |

Which side of `zip` is pull is fixed by position (the second, as today's `zip` pulls its second
source), and its type says whether the second is an `iter`, a `gen` or data, hence whether the
`zip` is total. foldr/build's `zip` and Lean's parallel `for` make the same choice, one side
pushed and the other pulled; Clojure's `sequence` over several collections and Go's `zip` by
`iter.Pull` pull every input (§6).

---

## 10. Comparison and recommendation

### 10.1 Table

| | A cursor data | B′ push stages | C′ declared direction | D1 no `for`, closures | D2 no `for`, blocks |
|---|---|---|---|---|---|
| R1 finiteness by type, no truncation | yes | yes | yes (no bound exists) | yes | yes |
| R2 no colouring within a direction | yes | yes (generic stages) | yes | yes | yes |
| R3 direction in types | yes | yes | yes, by declaration | by combinator name | by combinator name |
| R4 explicit boundaries with capacity | n/a (no pipelines) | with §9's adapters | with §9's adapters | same | same |
| R5 fused within a direction, 0 alloc, 0 dispatch | yes | yes (measured, §13) | yes | yes | yes |
| R6 borrowed data, `mut` elements, borrows in body | yes | yes (push over data spans the lend, F1) | yes | by threading | yes |
| R7 honest codata, fuel | yes | yes | yes | yes | yes |
| R8 `break`/`return`/`find`/`take`/value | yes (K0′) | yes | yes | combinators only | yes |
| R9 `let mut` state | yes | yes | yes | accumulators | yes |
| R10 escaping effects | yes | yes | yes | no (threaded by hand) | yes |
| total pipeline over data, `flat_map` included | no | yes | yes | yes | yes |
| a total producer passed to a function | take the data | specialized (second-class) | specialized | take the data | specialized |
| kernel | K0′ | K0′ | K0′ | K0′ | K0′ |
| new library | none | push stages | push stages as `push fn` | combinators per direction | combinators per direction |
| elaboration | dispatch by type former; `a..b`; lends | A + `|>`; `for` over a push pipeline | B′ + `push fn`, `suspend` | `|>` | `|>`; second-class blocks |
| implementation cost | small | medium | medium | small (library), large (corpus) | large |
| proof cost | K0′; completeness lemma | as A | as A | K0′ | K0′ |
| corpus change (§11) | 2 pending loops | same | same | 164 loops | 164 loops |

### 10.2 Recommendation

1. **Q0: keep `for`, answer (i)** (§8.4); open for the user.
2. **Now: A**, with K0′, `a..b`, `for x in v` over views, PR #132's array lend, the exit rule and
   the completeness lemma. It is the base of every other candidate.
3. **Next: B′ written through C′.** Push stages as `push fn`s over push sources, elaborated to
   `rf → rf` steps with state in the type; `|>`; `for` over a push pipeline. Total pipelines over
   data, `flat_map` included, with no bound anywhere.
4. **With it: the boundary adapters** `zip` (push × `iter`, push × data), `through`, `collect`,
   `suspend`, each stating its capacity, and the `boundaries` report and count (§4.4).
   `buffer[k]` when a program needs it.
5. **Later: D2's blocks**, driven by the operator (#18, handlers); then `for` as `for_each` with
   a block, and a push producer as a function taking one.

Reasons: A and C′ keep every existing program's text and meaning (a `gen fn` stays pull); the
direction of every source is its declaration or type former (R3), where the kernel already has
the distinction (F1, F4); every direction change is an adapter with a capacity (R4); and none of
it closes the door on D2.

---

## 11. The corpus, loop by loop

### 11.1 Method

Every `for … in` outside comments in `corpus/**/*.bc` and `lib/*.bc`, excluding the hand-written
`.core.bc` sides of sugar pairs: **145 loops in 84 files** (132 in `corpus/`, 13 in
`lib/adapters.bc`). Pass 1 counted 86 files; two of those mention `for … in` only in a comment
(`iter-mut-count.bc`, `reject/gen-callback-outside.bc`). The book: **19 loops in three chapters**
(`guide/generators.md` 11, `guide/divergence.md` 4, `guide/command-line-tools.md` 4);
`planned/pipelines.md` mentions `for` and `|>` in prose only. Each loop's source was read to its
definition.

**Today, every one of the 164 loops pulls its source**, a `for` over an `iter` or a `gen`. 132 are
drains (pull → push: the loop runs its body until the source ends); 32 are loops inside generator
bodies (29 in the corpus, 3 in the book), which pull their source and are themselves pulled: pull
in, pull out, one state machine, no direction change.

The push loops today are not `for`s: 14 calls of `count_fold` in 8 corpus files and 11 in
`lib/` (`slice.bc` 10, `div.bc` 1), and the `μ` folds.

### 11.2 Classes

| class | what the source is | corpus | book | today | recommended design, as written | boundary above capacity 1 | text changes |
|---|---|---|---|---|---|---|---|
| input | codata from a capability: `bytes …`, a generator or pipeline over input | 60 | 9 | drain, div | drain, div | none | none |
| pull stage | a `for` over a generator parameter in a `gen fn` or HOF body (13 in `lib/adapters.bc`) | 23 | 3 | pull in, pull out: one machine | same (the pull library) | none | none |
| finite generator | a program's generator finite by a count or straight-line `yield`s, or a pull pipeline over one | 54 | 7 | drain, div | drain, div (a `gen fn` stays pull) | none | none required; could be push and total |
| generator holding an output | `upto(&mut stdout, …)`, `ticks(&mut stdout, …)` | 4 | 0 | drain, div | same | none | none |
| infinite generator | `take(10, fib())` | 1 | 0 | drain, div | same | none | none |
| data (pending) | `iter_mut(&mut a)`, `range(n)`, `iter(&l)` | 3 | 0 | not expressible | push over data, total, for two | none | 2 |
| **total** | | **145** | **19** | | | **0** | **2** |

The "today" column is the loop's own: 7 loops of the input and finite classes are inside
generator bodies (`gen-adapters-io.bc:30`, `gen-digits.bc:12`, `gen-from.bc:30` and `:40`,
`gen-lines.bc:22`, `gen-block.bc:43`, `reject/gen-return-held.bc:9`), so they pull in and pull
out rather than drain; with the 22 pull stages in generator bodies and the book's 3 they are the
32 of §11.1.

The 145 by place: 21 in `corpus/reject/` (12 input, 9 finite), 6 in `corpus/pending/` (3 data,
2 input, 1 finite), 13 in `lib/adapters.bc`, and 105 in running programs.

**Boundaries.** No loop crosses a direction change above capacity 1, today or as written under the
recommendation. The three `zip`s (`gen-adapters.bc:49`, `gen-adapters-io.bc:60`,
`lib/adapters.bc:76`) are pull × pull, each side pulled one element at a time. The three
`flat_map`s (`gen-adapters-fail.bc:61`, `gen-adapters-io.bc:56`, `lib/adapters.bc:57`) pull a pull
inner with `yield from`, a state of the machine, not a buffer. Every other pipeline is pull stages
ending in one drain.

**Text changes.** Two, both pending programs that become expressible:
`corpus/pending/for-finite.bc` (`for i in range(n)` → `for i in 0..n`, total) and
`corpus/pending/iter-mut.bc` (`for x in iter_mut(&mut a)` → `for x in &mut a`, total, push over a
lent array). `corpus/pending/print-borrowed-list.bc` (`for x in iter(&l)` over a borrowed list)
stays pending: an in-order traversal of a borrowed `μ` list is F3's open problem in either
direction. No book loop changes; `book/src/guide/planned/pipelines.md`'s prose ("`for x in it
{ … }`, sugar for a `for_each` consumer over an iterator") would be rewritten when the push side
lands, and `guide/generators.md` would gain a section on push producers.

**The 61 finite-generator loops** (54 corpus, 7 book) could each be written as a push over a count
or a `push fn`, and would then be total. None is rewritten: 39 are tests of generators (`gen-*`,
`sugar/gen-*`, `sugar/for-value.bc`), 5 test the per-observation lend over a codata loop (`lend-pipeline.bc:41`,
`lend-div.bc:33`, `sugar/lend-block.bc:33`, `sugar/lend-let.bc:30`, `sugar/lend-div.bc:32`),
whose subject would disappear, 9 are rejects of pull-side rules, and 1 is pending
(`generator-handler.bc`); the book's 7 are the generators chapter's examples and one reject
example in `divergence.md`. The push side is tested by new programs, as §13's.

**Under D** (no `for`), all 164 loops are rewritten (D1 non-locally: accumulators and threaded
capabilities; D2 locally, once blocks exist), and the `for`-specific programs, sugar pairs and
rejects (`io-for-*`, `sugar/for*`, `reject/for-*`, `reject/io-for-*`: 10 programs) are deleted or
rewritten. Under §8's answer (ii), every `for` over a pull source outside a generator body gains
`drain(…)`: 129 loops (164, less the 32 in generator bodies and the 3 over data).

### 11.3 Files

Every loop, by file (line numbers at `main` a30d65b). Classes: **in** input, **stage** pull
stage, **fin** finite generator, **cap** generator holding an output, **inf** infinite generator,
**data** pending over data. Every loop is a drain today and as written under the
recommendation, with no boundary above capacity 1, unless marked.

| file | loops | class |
|---|---|---|
| `lib/adapters.bc` | 20, 26, 33, 39, 45, 57 (`flat_map`), 62, 69, 76 (`zip`), 93, 106, 125, 134 | stage |
| `corpus/axes/borrow-across-loop.bc` | 30 | in |
| `corpus/axes/codata-effects.bc` | 34 | cap |
| `corpus/axes/data-effects.bc` | 36 | in |
| `corpus/axes/scope-loop-lend.bc` | 27 | in |
| `corpus/gen-adapters-fail.bc` | 51, 53, 55, 57, 59, 61 (`flat_map`), 63, 65, 67, 71 | fin |
| `corpus/gen-adapters-io.bc` | 30, 47, 51, 56 (`flat_map`), 60 (`zip`), 65, 69 | in |
| `corpus/gen-adapters.bc` | 39, 43, 49 (`zip`) | fin |
| `corpus/gen-block.bc` | 26 | stage |
| | 40, 41, 42 | fin |
| | 43, 45 | in |
| `corpus/gen-borrowed.bc` | 30 | stage |
| `corpus/gen-cell.bc` | 23 | fin |
| `corpus/gen-close.bc` | 28 | stage |
| | 35 | fin |
| `corpus/gen-digits.bc` | 12, 20 | in |
| `corpus/gen-div.bc` | 45 | stage |
| | 56, 73 | in |
| | 70, 71 | fin (a div call per element: div as push too) |
| `corpus/gen-fib.bc` | 27 | stage |
| | 34 | inf |
| `corpus/gen-from.bc` | 30, 47 | in |
| | 40, 45, 48 | fin |
| `corpus/gen-lazy.bc` | 36 | cap |
| `corpus/gen-lines.bc` | 22, 40 | in |
| `corpus/gen-pipeline-adapters.bc` | 24 | fin |
| `corpus/gen-pipeline.bc` | 20, 24 | stage |
| | 29 | fin |
| `corpus/gen-produce.bc` | 19 | fin |
| `corpus/gen-return.bc` | 45 | fin |
| | 46, 47 | cap |
| `corpus/gen-value.bc` | 24 | stage |
| | 31, 32, 33 | fin |
| `corpus/io-aoc.bc`, `io-cat.bc`, `io-guess.bc`, `io-head.bc`, `io-hex.bc`, `io-lines.bc`, `io-sections.bc`, `io-upper.bc`, `io-wc.bc`, `io-fuel.bc`, `reverse-bytes.bc`, `split-at-mut.bc` | one each (79, 10, 91, 56, 22, 11, 41, 15, 33, 47, 27, 43) | in |
| `corpus/io-break.bc`, `io-for-assign.bc`, `io-for-then.bc` | two each (12, 19; 11, 13; 12, 23) | in |
| `corpus/lend-config.bc`, `lend-mut.bc`, `lend-server.bc` | 40; 18; 32 | in |
| `corpus/lend-div.bc` | 33 | fin |
| `corpus/lend-pipeline.bc` | 30, 34 | stage |
| | 41 | fin |
| `corpus/surface/io-wc.bc`, `surface/io-upper.bc` | 18; 12 | in |
| `corpus/sugar/for.bc`, `for-untyped.bc`, `residual-alias.bc` | 7; 7; 40 | in |
| `corpus/sugar/for-value.bc` | 17, 19 | fin |
| `corpus/sugar/gen-block.bc`, `gen-callback.bc`, `gen-div.bc`, `gen-from.bc`, `gen-range.bc`, `gen-return.bc`, `gen-yields.bc` | 11; 18; 38; 20; 18; 21; 15 | fin |
| `corpus/sugar/lend-block.bc`, `lend-div.bc`, `lend-let.bc` | 33; 32; 30 | fin (a core `iter` finite by a count) |
| `corpus/pending/for-finite.bc` | 24 | **data**: becomes `0..n`, total; **changes** |
| `corpus/pending/iter-mut.bc` | 39 | **data**: becomes `&mut a`, total; **changes** |
| `corpus/pending/print-borrowed-list.bc` | 37 | data: stays pending (F3) |
| `corpus/pending/closure-lend.bc`, `lend-nested.bc` | 39; 33 | in |
| `corpus/pending/generator-handler.bc` | 38 | fin |
| `corpus/reject/for-generated-origin.bc`, `for-value-held.bc`, `gen-return-held.bc` (9, 16), `io-for-nested.bc` (5, 6), `io-for-undetermined.bc`, `lend-escape.bc`, `lend-let-used.bc`, `lend-shadow.bc`, `total-calls-div.bc`, `total-loops.bc` | 9; 8; 9, 16; 5, 6; 7; 22; 18; 21; 7; 7 | in |
| `corpus/reject/for-break-value.bc`, `gen-block-empty.bc`, `gen-break-outside.bc`, `gen-escape.bc`, `gen-from-elem.bc`, `gen-self-borrow.bc`, `lend-div-two.bc`, `lend-iter-borrow.bc`, `take-failing.bc` | 10; 6; 10; 30; 14; 20; 16; 26; 16 | fin |
| `book/src/guide/generators.md` | 15, 19, 77 | stage |
| | 24, 57, 83, 138, 152, 171 | fin |
| | 100, 114 | in |
| `book/src/guide/divergence.md` | 17, 51, 142 | in |
| | 166 | fin (a reject example) |
| `book/src/guide/command-line-tools.md` | 12, 56, 84, 124 | in |

Two rejects would be accepted if rewritten push: `reject/lend-iter-borrow.bc` (a generator over
a borrowed array inside the borrow block: a push over the array keeps the borrow, F1, §4.6) and,
in the book, the same program in `divergence.md`. They stay as written: they test the pull rule.

### 11.4 What of PR #132 is reusable

| piece of PR #132 | fate |
|---|---|
| `&a`/`&mut a` of an owned array at a view parameter (`lendSlice`, `slice_borrow_*` around the call) | kept (A) |
| a lend in a total `for`'s source as a borrow block around the loop | kept, for `for x in &mut a` (A) |
| generic instances whose type arguments carry lifetimes | kept; essential for push stages over views (B′) |
| `iter_imm`/`iter_mut` as generators over a view | kept as the pull form of a view (a cursor pulled) |
| `len_imm` | kept |
| `forTotal`'s `count_fold` template (state = source + threaded variables; step a closure capturing nothing) | kept, keyed by type former; it is the push loop's template |
| the bounded-source table (names and bounds) | deleted |
| `range` as the elaboration's name | replaced by `a..b` |
| `take(from_iter(bytes(&mut c)), n)` total by name | replaced by the counted pull of an `iter` (explicit count) |
| the programs (`for-finite`, `iter-mut`, `split-at-mut` in direct style, `slice-total`, `slice-pipeline`, `print-borrowed-array`, `take-bytes`) | kept with spellings changed; `slice-pipeline` is a push pipeline under B′ |

---

## 12. Open questions for the user

Only undecided design questions, each with a recommendation. Spellings are provisional and not
asked (`a..b`, `push fn`, `|>`, `through`, `collect`, `suspend`, `drain`, `buffer[k]`,
`lib/push.bc`).

0. **Q0: keep `for`?** Recommended: yes, with answer (i) of §8 (one meaning per direction, read
   off the source's type), and a plan to redefine it as D2's `for_each` once blocks exist. The
   alternatives are (ii) and D, shown in §8.
1. **Is a drain written?** Under (i), `for` over a pull source is a drain, reported as div. Under
   (ii), it is rejected unless written `drain(g)`; 129 corpus and book loops gain it. This is the
   one-way door on how every input loop reads. Recommended: not written; the type and the div
   report make it visible, and a drain has capacity 1.
2. **Push pipelines are second-class** (§4.1, §7.2): passed to known functions and specialized,
   never stored in data or returned from an unknown call. Accept that, or add later a
   first-class push value of fixed state type (pass 1's `Pipe`: a view with a stage chain and its
   state), for a program that must store one. Recommended: accept; no target program stores a
   push pipeline, and the operator stores pull producers.
3. **K0′.** Add `count_try` beside `count_fold`, or replace `count_fold` by it (decision 20), which
   needs the core's `0` to have an eliminator the lowering erases. Recommended: beside, and
   replace later if the lowering erases the empty exit.
4. **`return` in a `fn` body** (F7). Give `return e` Rust's meaning in surface `fn` bodies, or a new
   keyword for early return, or keep early return to `break e` out of a loop whose value is the
   function's result. Recommended: Rust's meaning, since a core `return V` is written `V` as a
   tail expression already.
5. **A loop's value.** `let r = for … { break e } else { d }` (Zig), or the value of a push `for` is
   `E + 1` (`inl e` after `break e`, `inr ()` at the end), or no value. Recommended: Zig's `else`,
   which gives a value of the body's type with no sum to match.
6. **`for` over `μ` data.** Not a `for` source (folds only), or a right-to-left order stated, or an
   owned list consumed front to back by a new eliminator (a kernel change). An owned list's rest is
   a cursor, so a bounded pull of it is total (`boundary-collect.bc`), but a drain to its end is a
   loop with no count. Recommended: not a `for` source now; a borrowed list in order stays open
   (F3).
7. **The counted pull of an `iter`** reports whether the source ran out (as `div_fuel`'s `A ⊕ Q`
   does), or not. Recommended: it reports, since R7 asks for a visible "ran out".
8. **The completeness lemma** (§7.0): prove it in `Support/` with A, or accept the view loop as a
   reviewed template. Recommended: prove it with A.
9. **`zip` of two push producers**: rejected, with the error naming `collect` and `suspend`, or
   one side suspended automatically. Recommended: rejected; an automatic suspension would make the
   loop div with nothing in the text (R4).
10. **Capacity-`k` buffers now, or when needed.** Recommended: when a program needs one (a UTF-8
    encoder feeding a pull consumer); capacity 1 and `collect` cover the test set.
11. **The `boundaries` count** (§4.4): add it to `corpus/counts.expected` when the first boundary
    adapter lands, static, with a rise failing the gate. Recommended: yes.

Removed from pass 1's list: the choice between candidates A–D as then defined (superseded by §10),
the count's spelling (provisional syntax), and the stale SPEC line (a note in §3.2, not a
question).

---

## 13. The runnable examples

`docs/iteration-examples/`, run by `docs/iteration-examples/run.sh` at `iteration-design`. Each is
checked, interpreted, compiled to WebAssembly and run, and counted (allocations, dispatched calls,
copies; `bcc-counts`). Interpreter and compiled outputs agree for every one. The new ones are
hand-lowered to today's surface where the feature does not exist, and say so in their first
comment.

**New in this pass (the direction model):**

| file | shows | result | allocs / indirect / copies |
|---|---|---|---|
| `push-flatmap.bc` | T11: a push pipeline with `flat_map` over data (`rf → rf` stages over `count_fold`, a nested count as the inner source); hand-lowered | 6, total | 0 / 0 / 0 |
| `zip-push-pull.bc` | T7: `zip` of a push side (a count through `map`) and a pull side (an `iter`, one observation per element); hand-lowered | 2580, total | 0 / 0 / 0 |
| `boundary-cap1.bc` | a capacity-1 change that fuses: one Mealy stage run push (over a count) and pull (stepped inline by a generator, slot `B ⊕ 1`); `through` hand-written | (2, 10): push total, pull div | 0 / 0 / 0 |
| `boundary-collect.bc` | T12: an unbounded push → pull change as an explicit collect into a list, then pulled by its cursor in a `zip`; hand-lowered | 240, total | 10 / 0 / 0 |
| `boundary-suspend.bc` | T12 the other way: the producer suspended (today's pull adapters), zipped | 660, div | 0 / 0 / 0 |

`bcc-counts --sites` reports every closure call direct in the four hand-lowered programs
(`push-flatmap` 8 of 8, `zip-push-pull` 26 of 26, `boundary-cap1` 106 of 106, `boundary-collect`
7 of 7).

**From pass 1 (today's forms):**

| file | style | result | allocs / indirect / copies |
|---|---|---|---|
| `wc-for.bc` | T1, a drain with `for` (today) | `3 10 50`, div | 2 / 0 / 0 |
| `wc-fold.bc` | T1, D1: fold with a tuple accumulator | `3 10 50`, div | 2 / 0 / 0 |
| `fold-generic.bc` | D's generic `fold` over a generator | 6, div | 0 / 0 / 0 |
| `sumsq-count.bc` | push over a count: `count_fold` called directly | 285, total | 0 / 0 / 0 |
| `sumsq-gen.bc` | a drain of the program's own finite `range` generator | 285, div | 0 / 0 / 0 |
| `sumsq-gen-total.bc` | the same with `total` | rejected: "it has a `for`" | — |
| `upper-count.bc` | P12, push over indices with `get_mut` | 100, total | 1 / 0 / 0 |
| `upper-for.bc` | P12, a drain of `iter_mut(v)` inside `borrow mut` | rejected: "the iterator of this `for` holds the borrow" (F1) | — |
| `find-break.bc` | T9: `break e` in a drain (div), and the library's `find` (push, total, no early exit) | (8, 6) | 1 / 0 / 0 |
| `aoc-pair.bc` | T6c, nested `count_fold`s, no early exit (D1) | 514579, total | 1 / 0 / 0 |
| `aoc-groups.bc` | T6b, a drain with five `let mut` | 24000, div | 2 / 0 / 0 |
| `aoc-groups-pipe.bc` | T6b as a pull pipeline: `lines`, `map` of a fold, `batch`, max | 24000, div | 43 / 0 / 0 |
| `take-fib.bc` | T8, `take` of an infinite generator | 88, div | 0 / 0 / 0 |
| `zip-pull.bc` | T7 pull × pull | 140, div | 0 / 0 / 0 |
| `print-for.bc` | T10, a drain whose body only writes | `1 2 3 4 5`, div | 1 / 0 / 0 |
| `print-count.bc` | T10, D1: `count_fold` threading `stdout` by hand | `1 2 3 4 5`, total | 2 / 0 / 0 |

What they show:

- A push pipeline over data with a many-output stage (`flat_map`) is total and fuses with no
  allocation and no dispatched call (`push-flatmap`), with stages that capture only `!` values
  and keep their state in the state type.
- `zip` with a push side is total exactly when its pull side is an `iter` (or data), and costs
  nothing (`zip-push-pull`).
- One Mealy stage runs on both sides, and across a capacity-1 change nothing is materialised
  (`boundary-cap1`).
- An unbounded change costs one allocation per element when it is a buffer, and totality when it
  is a suspension (`boundary-collect` against `boundary-suspend`).
- Every `for` today is a drain, including `sumsq-gen.bc`, whose generator is finite; the total
  versions today are `count_fold` calls written by hand, which is what A's `for` over data
  elaborates to.
- The pipeline form of T6b allocates 43 objects against 2 for the loop: `lines` builds each line
  as a list. With `lines` yielding views of a buffer (strings S5) the two would match.
