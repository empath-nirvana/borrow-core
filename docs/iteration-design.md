# Iteration — design

Status: a design for the user to decide. Nothing here is built. The runnable examples it cites
are in `docs/iteration-examples/` (outside the corpus and the gate; `run.sh` runs them).

Contents:

- §0 Summary, and the decision asked for
- §1 Why this document exists: what PR #132 did, and where it went wrong
- §2 Requirements, and the design questions Q0–Q8
- §3 What the language has today, and eight facts that constrain every design
- §4 The target programs (the test set)
- §5 Prior art, read from primary sources
- §6 The candidates
- §7 Q0: `for`, or no `for`
- §8 Comparison and recommendation
- §9 Corpus impact
- §10 What of PR #132 is reusable
- §11 The runnable examples, and their counts
- §12 Open questions for the user

---

## 0. Summary

Iteration here has two kinds of source, and the kernel already tells them apart by type:

- **Finite data**: a count, a view `[L]` of an array, an owned array, a `μ` value. Each has an
  eliminator whose termination is a theorem (`count_fold`, SPEC §16; the folds, §6; `tab` and
  `drop`, §9). A loop elaborated to one of them is one computation, so a function that contains
  it stays `total`, and a borrow block around it keeps its borrow for the whole loop.
- **Codata**: `iter`, `gen`, `loop` (§7, §15). A loop over codata is a sequence of observations.
  Draining it is div (§14), and a borrow crosses it only by lending again at each observation
  (`experiments/LoopBorrow`).

PR #132 made `for` total by recognising a list of library **names** as finite and running the
loop for a bound the library claimed. That fails R1: the bound is a claim about code, not a fact
of a type, and a wrong one truncates silently.

This document proposes four candidates:

| | model | `for`? |
|---|---|---|
| **A. Typed sources** | today's `for`, plus: over a *data* source (a count `a..b`, a view, a lent array) it is a counted loop over the data's own length. Adapters stay generators, so a pipeline over data is div. | yes |
| **B. Data pipelines as values** | A, plus finite pipelines as first-class values: a data source with a **Mealy transducer** (one element in, at most one out, with state). The same transducers run over generators. | yes |
| **C. One producer, pushed or pulled** | A, plus: a `for` over a generator *call* inlines the generator with each `yield` replaced by the loop's body (foldr/build). The loop is then over whatever the generator's own loops are over, so it is total exactly when those are data. Adapters are today's `gen fn`s, unchanged. | yes |
| **D. No `for`** | combinators (`fold`, `try_fold`, `for_each`, `find`, …) over data and codata, `|>`, generators. D1 with today's closures; D2 with second-class blocks that may capture linear state. | no |

Every candidate needs one kernel change: a counted loop that can stop early (**K0′**, §6.0), so
that `break`, `return`, `find` and a raising body cost nothing after they exit. No candidate
needs a new type former or a `CDerives` rule.

**Recommendation** (§8): keep `for` (Q0), build **A** now, then **C**. A is small, fixes R1 by
type, and removes the name table. C adds pipelines over data with no bound anywhere and no
change to the adapter library. D2's second-class blocks are wanted anyway (the operator uses
them for `retry`, `span`, `race`); when they exist, `for` can be redefined as `for_each` with a
block, and programs written with `for` do not change. Removing `for` would rewrite 145 loops in
86 files and the book (§9), and D1 is visibly worse on the test set (§7). The user decides.

---

## 1. Why this document exists

PR #132 (branch `strings-s4`, open, not merged) was stage S4 of `docs/strings-slices-design.md`
and stage 9 of typed elaboration. Its `for` over a **bounded** source became `count_fold` with
the source's bound, so the function stayed total. The bounded sources were a table (SPEC 0.24
§16, *The total `for`*, in the PR):

| source | observations |
|---|---|
| `range(n)`, `range(a, b)` | the count |
| `iter_imm(v)`, `iter_mut(v)` | `len(v) + 1` |
| `map`, `filter`, `enumerate`, `skip`, `scan`, `from_iter` of a bounded `s` | those of `s` |
| `take(s, n)` | `n + 1` when `s` never skips; else those of `s` plus one |

and the PR's own text says what is wrong with it:

- **By name.** "The names are the library's: they are bounded when their module is included and
  the program does not define them." A program's own finite generator, a `chain` of two bounded
  sources, or a list's iterator is not bounded.
- **Unproved.** "They are not proved: the elaboration is checked core, so a wrong bound is a wrong
  answer, never an unsafe run." The PR tested each bound by a program whose answer changes if the
  bound is one short. The check is by test; the failure mode is silent truncation.
- **Skips.** `filter`'s bound is its source's only because `filter` skips instead of looping
  internally. The bound is a property of the adapter's code, which a later edit can change.
- **`for` accumulates cases.** The PR added about 400 lines to `Sugar.lean` (the total `for` and the array lend), and the total `for`'s
  fallbacks (a body that breaks, yields, returns, or whose value is kept, is a loop again) are
  cases of the one construct.

The user's direction: design this properly. Two ideas were floated during the PR and are
treated here as candidates, not conclusions: "`for` is a transducer terminal" (§6.2, §6.3) and
"`for` is a fold with an inferred accumulator" (§5.2, Lean's `ForIn`; §6.1).

---

## 2. Requirements and questions

From the user and the standing decisions:

- **R1. Total iteration over finite data.** Finiteness comes from types and data, never from
  names or guessed bounds. Nothing may silently truncate a loop.
- **R2. No colouring.** The same adapters work over pure, fallible, I/O-performing and (later)
  suspending sources.
- **R3. Zero cost.** Pipelines fuse into loops with no allocation and no dispatched calls.
- **R4. Borrowing.** Iterate borrowed data, mutate elements in place (`iter_mut`), and use
  borrowed state and capabilities in the body.
- **R5. Honest codata.** Infinite and external streams are supported; draining them is visibly
  div; fuel is the explicit route to totality.
- **R6. Early exit and results**: `break`, `return`, `find`, `take`, and a loop's final value.
- **R7. State in bodies**: `let mut` variables updated by the loop.
- **R8. Effects in a body escape the loop.** A body may perform I/O, capability operations or
  `raise`, and they belong to the enclosing function, handled by enclosing handlers, not threaded
  or returned by hand. A `for` whose body only performs effects is fine.

The questions each candidate answers:

- **Q0. Should the language have `for` at all?** (§7; the user is not sure it is a good idea.)
- **Q1.** One notion of "iterable", or two (finite data and codata)?
- **Q2.** Push, pull, or both; can adapters be written once for both?
- **Q3.** How does a loop know which kind of source it has, by type?
- **Q4.** What is an adapter: a transducer, a generator transformer, or both?
- **Q5.** Early exit and final values.
- **Q6.** Loop-body state, and how R8's escaping effects interact with it.
- **Q7.** How totality is established, and which existing theorems prove it.
- **Q8.** Fusion and zero cost.

---

## 3. What exists today

### 3.1 Inventory

| piece | where | what it gives iteration |
|---|---|---|
| `fold_own`, `fold_imm`, `fold_reuse` | SPEC §6 | total eliminators of `μ` data; a **right** fold (the tail is folded before the head) |
| `count_fold` (K0) | SPEC §16 | the total counted loop; one machine step, no allocation; runs to its bound |
| `tab`, `drop`, `array_map` | SPEC §9; `experiments/PositiveArrays` | the array's own loops: build, free, map (the map is proved in the experiment, not promoted) |
| `[L]` views, K2–K5 | SPEC §9 | an array lent as a family with no cell; split at an index; write at an index |
| `νX. C`, `unfold` | SPEC §7 | codata; `iter A B R` (never skips), `gen A B R` (may skip), `loop B R` |
| div as an effect | SPEC §14 | draining codata is div, inferred; `total` is checked; `div_fuel` is the fuel handler |
| one state machine per body | SPEC §15 | a generator or div body is one `unfold`; loops are states; no dispatched call |
| specialization at the callback's type | SPEC §14, §15 | a higher-order function is copied at a div callback, or at one that yields |
| generators, generic `gen fn`, `lib/adapters.bc` | SPEC §15 | `map`, `filter`, `take`, `zip`, … written once, instantiated per source |
| the per-observation lend | SPEC §14; `lib/lend.bc` | a borrow over a codata loop, lent again at each observation |
| `for x in V { M }` | `Frontend/Sugar.lean` (`forLoop`, `mWalk`) | over an `iter` or a `gen` only; always div; threads the variables `M` reads or assigns, and the capabilities; `break`, `break e`, `let r = for …` |

### 3.2 Eight facts that constrain every design

These are established in the repository; each cites where.

- **F1. A loop over data is one computation; a loop over codata is many.** A `count_fold` or a
  fold runs inside one `F`, so a borrow block around it holds the borrow for the whole loop
  (K2's callback is one computation). A codata loop is observed step by step, and no borrow
  spans observations in this model: "a lend that spans observations does not close"
  (`experiments/LoopBorrow`, Verdict). What works is to lend again at each observation.
  `docs/iteration-examples/upper-for.bc` shows the consequence: `for c in iter_mut(v)` inside
  `borrow mut a { 'x, v -> … }` is rejected, "the iterator of this `for` holds the borrow of
  `v`". The same loop as `count_fold` (`upper-count.bc`) is total and runs.
- **F2. Totality is proved once; truncation is not a safety property.** Every elaborated loop is
  checked core, so the totality theorem (`total_no_infinite_run`, SPEC §14) covers every div-free
  program with no per-loop proof. But the relation proves safety, not that a loop visits every
  element: a counted loop run for too small a count is safe and wrong. That is why a bound must
  come from the data by construction, not from a claim.
- **F3. `μ` folds are right folds, and `fold_imm`'s result must outlive every lifetime.** A
  left-to-right loop with state over a borrowed list cannot be a `fold_imm` into a function
  `U(S ⊸ F S)`, because a thunk has no outlives rule (SPEC §6; LoopBorrow, *Zip*). An in-order
  iterator over a borrowed list is open (SPEC §7 Open, "Lifetime-indexed iteration"; #57's list
  half).
- **F4. A generator's skips are unbounded; an `iter` never skips.** `gen A B R`'s `next` may
  skip, so the number of observations to the next element is not bounded by anything in its
  type. `iter A B R` has no skip, so `n` observations give at most `n` elements, by type.
- **F5. Closures capture only `!` values, and cannot assign outer variables.** Promotion needs
  `!Γ` (`corpus/pending/closure-captures-int.bc`, #9: a `!` closure cannot capture an `i32`), and
  "assignment inside a closure … of a variable outside it" is not provided (decision 38). So a
  combinator's body, a closure, cannot use a `let mut` variable, a capability or a borrow from
  its surroundings. `for`'s body is not a closure: it is code in the enclosing body, elaborated
  in place.
- **F6. A counted loop cannot stop early.** `count_fold` runs to its bound; "a finished state is
  carried to the bound, which costs a test per remaining count" (SPEC §16 Open). The slice
  library's `find` does this (`lib/slice.bc`).
- **F7. `return` in a `fn` body is the core's `return`.** Early return from a function exists
  only in generator bodies (decision 41: "giving it Rust's meaning there would change what
  existing core-style bodies mean").
- **F8. A `for` body in a div body must be total** (SPEC §14 Open; `corpus/reject/io-for-nested.bc`:
  "the body of a `for` is one step of its loop and must be total, but it has a `for`"). A
  generator body may nest loops.

One stale item: SPEC §14 Open says "A div function has no type parameters". Since #131 a generic
`fn` with a `for` over a generator checks and runs (`docs/iteration-examples/fold-generic.bc`,
`fold__g0 : … => U (delay i32)`).

---

## 4. The target programs

The test set. Each is written here once in the syntax the `for` candidates aim at (A–C; §6 says
where a candidate differs), and §7 writes the key ones again without `for`. Spellings are
hypotheses: `a..b` for a count (Rust's), `for x in v` over a view, `&a`/`&mut a` lending an array
(PR #132's row), `for … else` for a loop's value when it does not break (Zig's). A `-- runs:`
line names an example that runs today in some form.

### T1 `io-wc` (corpus)

```
fn count(c: In) -> In * (i32 * (i32 * i32)) =
  let mut lines = 0; let mut words = 0; let mut chars = 0; let mut in_word = false;
  for b in bytes(&mut c) {                    -- codata: div
    chars = chars + 1;
    if b == 10 { lines = lines + 1 };
    if is_space(b) { in_word = false }
    else { if not(in_word) { words = words + 1 }; in_word = true }
  };
  (c, (lines, (words, chars)))
-- runs: wc-for.bc (today's syntax, unchanged)
```

### T2 `split-at-mut` (P10)

```
total fn reverse<'a>(v: slice mut 'a u8) -> () =
  let n = len_mut(&mut v);
  for i in 0..(n >> 1) { swap_at(&mut v, i, n - 1 - i) }

total fn upper<'a>(v: slice mut 'a u8) -> () =
  for c in v { modify c { x -> if b'a' <= x && x <= b'z' { x - 32 } else { x } } }

main -> i32 =
  let mut b = read_all(&mut stdin);                     -- div: reads to the end
  let n = len_of(&b);
  borrow mut b { v -> match split_at_mut(v, n >> 1) { inl (l, r) -> reverse(l); upper(r) | inr _ -> () } };
  write_all(&mut stdout, &b);
  n
-- runs: corpus/split-at-mut.bc (count_fold and a hand-driven iterator)
```

### T3 the slice programs (P7, P12, the library)

```
for x in &mut a { modify x { v -> v * 10 } };            -- P12
let s = for x in &a { acc = acc + *x };                   -- a sum over a lent array
total fn find<'a>(v: slice 'a i32, x: i32) -> i32 + 1 =
  for i in 0..len(v) { if at(v, i) == x { return inl i } };       -- R6: early return
  inr ()
total fn sort<'a>(v: slice mut 'a i32) -> () =            -- P7: nested total loops
  let n = len_mut(&mut v);
  for i in 1..n { for k in 0..i {
    let j = i - 1 - k;
    if peek(&mut v, j) > peek(&mut v, j + 1) { swap_at(&mut v, j, j + 1) } else { break } } }
-- runs: upper-count.bc, find-break.bc (library `find`), corpus/sort-numbers.bc (library `sort`)
```

### T4 the strings design's loops (P1–P15)

| program | loop | source kind | needs |
|---|---|---|---|
| P1 `fields` | `for i in 0..(k + 1) { match split_once(rest, sep) … }` | count | state `rest`, `found` |
| P1 `main` | `for b in bytes(&mut stdin) { … borrow line { v -> … } … }` | codata | a borrow block in the body; capabilities |
| P2 `parse-int` | `for d in digits { acc = … }` | view | error state (`-- #18`: a `raise` would exit) |
| P3 `replace_all` | `for _ in 0..(len(&rest) + 1) { … }` | count as fuel | the count is the user's, stated |
| P5 `utf8-count` | `count(chars(t))` | generator over a view | total pipeline over data (B, C) |
| P6 `key-value` | `for l in lines(t) { … push(&mut pairs, …) }` then `for p in ps { … }` | generator over a view; view | total pipeline; capability in the body |
| P7 `sort-lines` | nested counts; `for l in v { write_str(&mut stdout, *l) }` | count; view | nested loops; I/O body |
| P9 `http-request` | `for h in headers { let (k, v) = *h; push_lit(&mut r, k); … }` | view | state is an owned buffer |
| P10 `split-at-mut` | T2 | count; view | `mut` leaves |
| P12 `iter-mut` | T3 | lent array | `mut` leaves under a lend |
| P13 `labels-json` | `for c in chars(t) { … push_char(&mut s, c) }` | generator over a view | total pipeline |
| P14 `args` | `for i in 0..n { … read_arg(&mut args, i, &mut arg) … }` | count | capabilities in the body |

### T5 the operator's loops (`docs/operator/operator.bc`)

```
fn watch<K>(api, sel, rv, t) -> Iter<WatchEvent<K>, ()> = generate {       -- 1.6
  let resp = send(&watch_req(api, sel, rv, t));
  if resp.status == 410 { raise(KubeError::Api(gone())) };
  let events = resp.body |> chunks |> lines |> map(|line| decode(&line));
  for ev in events { yield(ev) } }                  -- codata; Async, Fail in the body

fn watcher<K>(api, sel) -> Iter<Event<K>, never> = generate {
  loop { match try { let (items, mut rv) = list(api, sel);
                     for o in items { yield(Apply(o)) };        -- data (a Vec) inside a generator
                     yield(Resync);
                     loop { for ev in watch(api, sel, &rv, 290) { rv = …; yield(…) } } } {
         … Err(e) -> sleep(backoff.next()) } } }

fn triggers(cfg, stop) -> Iter<Trigger, ()> =                  -- a pipeline over codata
  merge(from_crs, from_deps) |> take_until(stop) |> debounce(1.s, trigger_key) |> inspect(…)

fn serve_metrics(l: Listener) -> never =
  for conn in accept_all(l) { … respond(conn, 200, &b) }        -- forever: div, Async

fn run_controller(triggers, concurrency, grace, reconcile)       -- for_each_concurrent
fn diff(a, b) = … |> filter_map(…) |> collect()                   -- total fold over data
```

These are codata loops with control effects in the body (`Async`, `Fail`), a data loop inside a
generator (`for o in items`), and pipelines over codata. They test R2, R5 and R8.

### T6 Advent-of-Code loops

```
-- (a) sum per line, 2020 day 1 input format (corpus/io-aoc.bc)
for b in bytes(&mut stdin) { if b == 10 { sum = sum + num; num = 0 } else { num = num * 10 + (b - 48) } }

-- (b) the largest group sum, groups separated by blank lines (2022 day 1)
for b in bytes(&mut stdin) { if b == 10 { if nl { best = max(best, cur); cur = 0 } else { … } } else { … } }
-- runs: aoc-groups.bc (for), aoc-groups-pipe.bc (a pipeline)

-- (c) the two entries summing to 2020 (2020 day 1): nested loops, exit across both
total fn solve<'a>(v: slice 'a i32) -> i32 + 1 =
  for i in 0..len(v) { for j in (i + 1)..len(v) {
    if at(v, i) + at(v, j) == 2020 { return inl (at(v, i) * at(v, j)) } } };
  inr ()
-- runs: aoc-pair.bc (nested count_fold, no early exit)

-- (d) a histogram into an array, then the most frequent
let mut counts = box array(26, zero);
for b in bytes(&mut stdin) { if is_lower(b) { modify_at(&mut counts, b - 97, { c -> c + 1 }) } };
let mut best = 0;
for i in 0..26 { if at(&counts, i) > at(&counts, best) { best = i } };

-- (e) iterate to a fixed point (a simulation): genuinely may not end
loop { let next = step(&grid); if next == grid { break }; grid = next }     -- div, honestly
for _ in 0..1000 { … }                                                       -- or fuel, explicitly
```

### T7 `zip`

```
for (x, y) in zip(gen_a(), gen_b()) { … }        -- pull × pull: both codata      runs: zip-pull.bc
for (x, y) in zip(&a, gen_b()) { … }             -- push × pull: data driven, codata pulled
for (x, y) in zip(&a, &b) { … }                  -- push × push: two data sources in lockstep
for (x, y) in zip(&mut a, &b) { *x = *x + *y }   -- a `mut` view with an `imm` one
```

(LoopBorrow's `zip-push-pull.bc` and `zip-push-push.bc` are these, in core, with owners in the
loop's state.)

### T8 an infinite stream with `take`

```
for x in take(fib(), 10) { acc = acc + x }       -- runs: take-fib.bc (div today)
```

### T9 early return, and a final value

```
fn first_neg<'a>(v: slice 'a i32) -> i32 + 1 =
  for x in v { if *x < 0 { return inl *x } };
  inr ()

let r = for x in v { if p(*x) { break *x } } else { default };     -- Zig's loop value
```

### T10 a body that only does I/O (R8)

```
for x in &a { put_dec(&mut stdout, *x); putb(&mut stdout, 32) }    -- runs: print-for.bc, print-count.bc
```

---

## 5. Prior art

The reading was done for this document from primary sources: language references, standard
library source, papers and RFCs. Each subsection lists what was read. A claim marked *(read as
code)* was inferred from source code, not quoted. Sources that could not be fetched are named;
nothing is taken from them.

### 5.1 Rust: `Iterator`, `IntoIterator`, `for`

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
- **For us.** Push and pull on one abstraction pays off (`Chain`), which is C's shape. The inline
  body is what makes `return` and `?` work.

### 5.2 Lean 4: `ForIn` and "do unchained"

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
  This is today's `forLoop` and §6.0's exit rule.
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
  same exit encoding (§6.0). Lean's `Productive`/`Finite` are the typed version of our F4: `iter`
  is productive by its type. Its warning: prove what ships (§6.0's lemma is about the template
  the elaborator emits).

### 5.3 Clojure transducers

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
- **For us.** Candidate B is transducers with the state in the type, since our closures capture
  nothing (F5), and `reduced` is K0′'s `inr`.

### 5.4 Haskell: foldr/build and stream fusion

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
  without an optimizer (one state machine per body). Candidate C's push is foldr/build with
  `yield` as `build`'s `cons`, done by the elaborator at a known call, so it fires by
  construction, which is Kiselyov et al.'s point. C pushes one side of `zip` and pulls the other,
  as foldr/build is forced to.

### 5.5 Koka and Effekt

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

### 5.6 Swift, C++ ranges, Java streams

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
  Every one of these duplicated its API for effects (async, throwing), which R2 exists to avoid.

### 5.7 OCaml `Seq` and `Iter`

**Read:** the OCaml `Seq` documentation; the `iter` library's README, `Iter.mli`, `Iter.ml`.

- `Seq` (`unit -> 'a node`) is pull, has `zip`, and allocates per element. `Iter`
  (`('a -> unit) -> unit`) is push: "Control is not handed back to the caller before the whole
  iteration is over. This makes zip impossible to implement", but any internal traversal is an
  `Iter`, and with flambda it compiles "to an actual loop with no overhead". `Iter.take` exits by
  a local exception.
- **For us.** The push/pull trade in one ecosystem, as two libraries. C gets both from one
  definition.

### 5.8 Briefly

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
- Elm, and Haskell as a loop-free language: no source was fetched; §7.2 cites Haskell only
  through the fusion papers.

### 5.9 What the survey says, collected

| system | Q1 notions | Q2 push/pull | Q5 early exit | Q7 totality | paid |
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

---

## 6. The candidates

### 6.0 What every candidate shares

**Source kinds, by type former** (Q1, Q3). The elaborator reads the source's type, not its name:

| kind | types | eliminator | termination |
|---|---|---|---|
| count | `a..b` (syntax; two `i32`s) | K0′ over `[a, b)` | the count, a machine step (SPEC §16) |
| view | `array_imm 'a A`, `array_mut 'a A` (`[L]`) | K0′ over `len(v)`, leaf `i` by `idx` (`imm`) or `split_first_mut` (`mut`) | the view's own length |
| lent array | `&a`, `&mut a` of `a : array A` | `slice_borrow_*` (K2) around the view loop | as the view |
| never-skip codata under a count | `U (iter A B R)` with an explicit count | K0′ over the count, one observation per step | the count (fuel, stated) |
| codata | `U (iter A B R)`, `U (gen A B R)`, `U (loop B R)` | a state of the body's machine (today's `for`) | none: div |
| `μ` data | `μX. T` | the folds (bottom-up), or not a `for` source (§12, question 6) | size of the value |

A count must be a *syntactic* form or a type the program cannot confuse with a pair: the core is
structural (decision 9), so `range(a, b) : i32 * i32` would make every pair a count. `a..b` is
syntax, so no library name is involved.

**K0′: a counted loop that stops early.**

    count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)

    (μ, count_try (f, (n, (i, s)))) ↦ (μ, case f (i, s) { inl s′ → count_try (f, (n, (i + 1, s′)))
                                                        | inr e  → inr e })       if i < len(n)
                                    ↦ (μ, inl s)                                  otherwise

It is `count_fold` with an exit: the step answers the next state or an exit value. `break e`,
`return e`, `find`'s answer and (later, #18) a `raise` are exits. Its proof is `countLoop_wp`'s
induction with one more case; its lowering is `count_loop` with one more branch. By decision 20,
`count_fold` becomes its instance at `E = 0` in the same change, if the core's `0` has an
eliminator the lowering erases; otherwise both stay (§12, question 3).

**The completeness lemma.** F2 says the relation does not prove that a loop visits every
element. For the view eliminator this is one template, `count_try` over `n = array_len(v)` with
leaf `i` taken by `idx (v, i)`, and its completeness is a fact about three machine steps
(`count`, `array_len`, `idx`): for every `i < n`, `idx` answers `inj₁ (ℓ + i)`. It can be proved
once in `Support/` (a lemma on the step relation, not the logical relation). It is the lemma PR
#132 could not state, because its bounds were claims about adapter code.

**Bodies** (Q6, R7, R8). The body of a `for` is code in the enclosing body, not a closure (F5),
so it may read and assign `let mut` variables, use capabilities and borrows. The elaboration
threads what the body assigns and the capabilities it uses, as today's `forLoop` does and as
Lean's `do` does (§5.2). R8 is met at the surface: the program never names the threading. What
escapes is decided by the body's computation type:

| body's effect | over data | over codata |
|---|---|---|
| total (answering effects: capabilities, threaded) | K0′; the enclosing function stays total | a machine state; div |
| exits (`break`, `return`, later `raise`) | K0′'s `inr`; every exit hands on the threaded variables and hands back the capabilities | today's `break`; the iterator closed first |
| suspends (a div call, a nested codata loop, `yield`, later `wait`) | a machine state holding a cursor (the index, or the rest of the view); the function is div or a generator because of its body | a machine state (today) |

The last row lifts F8: a loop body that loops is a nested point of the machine, as it already is
in generator bodies. A data loop whose body suspends over a locally lent array uses the
per-observation lend with an index in the state (`lib/lend.bc`'s `array_each_imm`), since the
view cannot be held across observations (F1).

**Exits and threaded state.** Every way out of a loop (the end, `break`, `return`, a raise, and
for codata `close`) hands on the current values of the threaded variables and hands back what has
no destructor, and drops the rest by its destructor (SPEC §12). This is one rule, the one today's
`break` follows. A raise from a body inside `try { … }` in the same function therefore sees the
`let mut` variables as the body left them, as Rust and Lean do.

**`return` in a `fn` body** (F7). R6 needs Rust's `return` inside a loop. The options are in §12,
question 4.

### 6.1 Candidate A: typed sources (minimal)

**Model.** Today's `for` stays for codata. A `for` whose source is a data kind of §6.0 is a K0′
loop over the data's own extent, elaborated in the surface pass, total. PR #132's name table is
deleted: `range` becomes `a..b`, `iter_imm(v)`/`iter_mut(v)` are not needed as `for` sources
(`for x in v`), and adapters stay generators, so `for x in map(v, f)` is a loop over codata and
div. A never-skip source under an explicit count (`for b in bytes(&mut c) up to n`, spelling
open) is K0′ over `n` observations and reports whether the source finished, as `div_fuel` does.

**The programs.**

- T1 unchanged (codata, div). T6a, T6b unchanged.
- T2, T3, P7, P9, P10, P12, P14: as written in §4, total.
- T6c: as written; the inner `return` is K0′'s exit through both loops (an exit of the inner
  loop is the outer step's `inr`).
- P5, P6, P13 (`count(chars(t))`, `lines(t)`, `chars(t)`): generators over a view, so **div**. To
  stay total the program writes the loop over the view itself (a UTF-8 decoder inline), or the
  library provides `count_chars(t)` etc. as total functions with their own loops over the view.
- T7: `zip` of two views is written with indices (`for i in 0..min(len(v), len(w)) { … }`),
  or with a `mut` view as `let mut rest` and `split_first_mut` in the body. `zip(&a, gen)` pulls
  the generator in the body: total when it is an `iter` (one observation per element, F4), div
  when it is a `gen`.
- T8: div, or `for x in fib() up to 10` if `fib` is written as an `iter` (never skips).
- T9: K0′. T10: total, `stdout` threaded.
- T5: unchanged: every operator loop is over codata or is a generator.

**R1–R8.** R1 met by type. R2: adapters are generators, written once for every source, but a
pipeline over data is div (partly met). R3: data loops are one K0′ loop with a known step (0
allocations, 0 dispatched calls, as `sumsq-count.bc`); pipelines are today's machines (0, 0).
R4 met for views (the loop is one computation, so the lend spans it). R5 met. R6 met with K0′.
R7 met (today's threading). R8 met for answering effects; control effects per §6.0.

**Split.** Kernel: K0′. Library: nothing new required (the name table goes). Elaboration: the
data-kind dispatch in `for` (PR #132's `forTotal`, keyed by type former instead of name), `a..b`,
PR #132's array lend `&a`/`&mut a`, exits through K0′.

**Cost.** Implementation: small. `forTotal` exists; the change removes its name table and its
generator-observation template, and keys on the type former. Proof: K0′ (one induction case
beyond `countFold_compatX`), and the completeness lemma (§6.0).

**Cannot express.** A total pipeline over data (`map`, `filter`, `chars`, `lines` of a view, in
total code). A function over a finite producer that stays total, other than one taking the data.

### 6.2 Candidate B: data pipelines as values (Mealy transducers)

**Model.** A plus a second kind of adapter. A **transducer** is a Mealy machine, one element in
and at most one out, with its own state and a way to stop:

    Xf T A B ≜ !(T ⊗ A ⇒ (T ⊗ (B ⊕ 1)) ⊕ T)          -- next state and maybe an output; or stop

`map(f)`, `filter(p)`, `take(n)`, `enumerate`, `scan`, `take_until(p)`, `skip(n)`, `inspect` are
transducers; composing two is ordinary code (state `T₁ ⊗ T₂`). A **pipeline value** is a data
source with a transducer and its initial state, `Pipe = V ⊗ (Xf T A B ⊗ T)` at a view type `V`:
data, so a `for` over it is K0′ over the view with the transducer run in the step, total, and a
function may take a `Pipe` as an argument and stay total. The same transducer runs over a
generator through one generic adapter, `through(g, xf)`, a `gen fn` that pulls `g`, steps `xf`,
and yields or skips: written once for both.

`flat_map`, `chunks` without allocation, `lines` of bytes into views, and `zip` are not Mealy
(one element in, several out; or two sources). They stay generators, and over data they are
nested loops in the body.

Clojure's transducers are the precedent (§5.3), with the difference that Clojure's stateful
transducers hide their state in a mutable box; here the state is in the type, `T`, because a `!`
closure captures nothing (F5).

**The programs.** As A, plus: P5 `count(chars(t))`, P13 `for c in chars(t)` are total when
`chars` is a transducer over the view's bytes (a UTF-8 decoder is Mealy: one byte in, at most one
scalar out, with the partial sequence as state). P6 `lines(t)` over a view is total as a
transducer that emits a sub-view at each newline (state: the start index). `v |> filter(p) |>
map(f)` passed to a `total fn` stays total. T7 `zip` as A. T8: `take(10)` is a transducer, but
over `fib()` (a generator) the loop is still codata, div.

**R1–R8.** R1 met by type (the pipeline's source is data). R2 met for Mealy adapters over data
and codata, written once; not for `flat_map`/`zip`/`chunks`. R3: a transducer's step is a `!`
function, known by 0-CFA, so no dispatched call; state in tuples, no allocation. R4: the pipeline
holds the view, so it lives in the lend, and the loop is one computation. R5–R8 as A.

**Split.** Kernel: K0′. Library: `lib/xf.bc` (the transducers, `through`, `Pipe` builders).
Elaboration: A's, plus `for` over a `Pipe` (the view loop with the transducer in the step).

**Cost.** Implementation: medium. A second adapter library beside `lib/adapters.bc`, written in
a less direct style (a step function over explicit state, where a `gen fn` writes a loop with
`yield`). Proof: none beyond A: transducers are ordinary code.

**Cannot express.** Total `flat_map`/`chunks`/`zip` pipelines over data as values (they are
written as nested loops). A transducer that emits several elements per input.

### 6.3 Candidate C: one producer, pushed or pulled

**Model.** A, plus one transformation. A `for` whose source is a **call of a `gen fn`** (or a
chain of them, as `map(filter(v, p), f)`) is **pushed**: the generator's body is inlined at the
loop, with each `yield e` replaced by the loop's body at `x = e`. A generator's parameter that is
itself a generator call is pushed in turn. What remains is a loop over the generator's own
sources, and the elaboration of §6.0 applies to it: over data it is K0′ and total; over codata
it is a machine state and div. A `for` over anything else (a generator held in a variable,
passed as an argument, returned, or zipped as the second source) is **pulled**: today's `for`,
the state machine, div.

This is Gill, Launchbury and Peyton Jones's foldr/build (§5.4) with `yield` as the `cons` of
`build`, applied by the elaborator at a known call rather than by a rewrite rule, so it fires
exactly when the source is a call, and never otherwise. The pull form is stream fusion with the
skip (§5.4). A generator is written once; it is pushed or pulled according to how it is used.

**Details.**

- **Several `yield`s.** The body is inlined once, as a join function of the element and the
  threaded state (a `!` function capturing nothing), and each `yield e` calls it. The machine
  already builds joins this way (SPEC §15, *Moves*), so there is no code duplication and no
  dispatched call.
- **`break` and `return` in the body** leave the inlined generator's loops too: each is a K0′
  exit (data) or today's loop exit (codata), and what follows those loops in the generator does
  not run. What the generator holds is handed on or dropped by the exit rule of §6.0, which is
  what its `close` would have done in the pull form.
- **Totality is inferred, not claimed.** After inlining, the loop is total if and only if the
  existing divergence inference says so. `for x in map(filter(v, p), f)` becomes `for x in v { if
  p(x) { body[f(x)] } }`, total. `for y in take(fib(), 10)` becomes `fib`'s `while true` with
  `take`'s counter and `break` inside: a `while` loop, div. Nothing is bounded, so nothing can be
  truncated.
- **`while` in a pushed generator** becomes a `while` in the enclosing body. Today `while` is
  only a generator's; in a div body it is one more machine state (small).
- **`zip`.** `zip(a, b)` pushes `a` and pulls `b`. Pulling `b` is one observation per element when
  `b`'s type is `iter` (never skips, F4), so a zip driven by data over an `iter` is total. Over a
  `gen`, a pull may skip without bound, so the loop is div. The data-over-data case (`zip(&a,
  &b)`) is best a library function over two views with one index, total.
- **Borrowing.** A pushed loop over a view is one computation inside the lend (F1), so
  `for c in iter_mut(v)` inside `borrow mut` — rejected today (`upper-for.bc`) — is total and
  accepted.

**The programs.** As A, plus: P5, P6, P13 total (`chars`, `lines`, `count` over a view are
`gen fn`s whose loops are over the view). `v |> filter(p) |> map(f)` in a `total fn`, total, with
today's adapters. T5 unchanged (codata, pulled or pushed; div either way; the generators and
adapters are the same ones the tests run over a `Vec`, which is R2 in the operator's sense).
T6b as a pipeline (`lines`, `map`, `batch`, `max`): pushed, but over `bytes(&mut stdin)`, so div
(honest), and with no list allocations if `lines` yields views of a buffer rather than lists.
T7: as above. T8 div, or fuel.

**R1–R8.** R1 met: no bound exists; totality is the existing inference over the inlined loop.
R2 met: one adapter library, today's; each adapter is pushed or pulled per use. R3 met: pushed
loops are K0′ or machine states with known steps; pulled ones are today's (0, 0 in
`corpus/gen-pipeline-adapters.bc`). R4 met for pushed loops; pulled loops keep the
per-observation lend. R5–R8 as A.

**Split.** Kernel: K0′. Library: none (today's adapters; `range` retired for `a..b`; `iter_imm`
and `iter_mut` become `gen fn`s over a view, as PR #132 wrote them). Elaboration: A's, plus the
push transformation, and `while` in div bodies.

**Cost.** Implementation: medium. The push transformation is a substitution into a generic
instance's body (the instance exists already: `makeInst`), with the join function and the exits.
It must run before divergence inference. Proof: none beyond A.

**Cannot express.** A function that takes a finite producer as a *value* and stays total: the
argument is pulled, so the function is div. (Mitigations: take the data and apply adapters
inside; or later, specialize a function at a generator-call argument, as it is specialized at a
callback today; that is inlining at the call and is not proposed here.) A total pull of a `gen`
(a `zip` whose second source skips).

### 6.4 Candidate D: no `for`

**Model.** No loop syntax. Iteration is combinators over data and codata, with `|>` (not yet
provided: decision 40), and generators:

- over data (views, counts, `μ`): `fold`, `try_fold` (step answers continue or stop), `for_each`,
  `find`, `any`, `all`, `sum`, `count`, `map`, `filter`, `collect`, written over K0′ and the folds,
  total;
- over codata: the same names, written over the machine, div;
- generators keep `gen fn` and `yield`; their bodies still need a loop over their source, so D
  keeps either `for`/`while` inside `gen fn` bodies or a pull primitive (`next(it)`) with
  `while`.

Two variants, by what a combinator's body can be:

- **D1: today's closures.** A body is a `!` closure capturing nothing (F5). Every `let mut`
  variable, capability and borrow the body uses is a component of the accumulator; early exit is
  the step's answer (`try_fold`).
- **D2: second-class blocks.** A block argument `{ x -> … }` to a known function may capture
  linear state, assign `let mut` variables of the enclosing body, lend, and exit with `break` and
  `return` (Kotlin's inline lambdas, Effekt's blocks, Smalltalk's non-local return; §5.5). It is
  elaborated by the existing specialization: the function is copied at the block, the block's
  captured state becomes extra state of the copy's loop, and an exit is a K0′ exit. That is the
  same threading `for` does, moved into specialization, where every higher-order function gets
  it (`retry`, `span`, `with`, `race` in the operator all take such blocks).

**The programs** (§7 has them side by side). T1 is a `fold` of the byte stream with a 4-tuple
accumulator (`wc-fold.bc`, runs, 2 allocations, same as `wc-for.bc`). T2's `reverse` and `upper`
are `count_fold`/`for_each` calls; T6c is two nested `try_fold`s (runs today as two nested
`count_fold`s carrying the answer, `aoc-pair.bc`: 36 lines against about 8 with `for`). T10 in D1
threads `stdout` by hand (`print-count.bc`); in D2 the block captures it.

**R1–R8.** R1 met by type (combinators over data are total). R2 met (combinators specialized per
source). R3 met (0-CFA; known steps). R4: D1 threads the view in the accumulator; D2 captures it.
R5 met. R6: `find`, `take`, `try_fold` in D1; D2 adds `break`/`return` in blocks. R7: D1 by
accumulators only; D2 by capture. R8: D1 fails at the surface (capabilities are threaded by the
program through the accumulator); D2 met.

**Split.** Kernel: K0′. Library: the combinators, per source kind. Elaboration: `|>`; D2's
blocks (capture of linear state and assignment in specialization, non-local exits).

**Cost.** D1: small for the library, large for the corpus (§9). D2: large: second-class blocks
are a new elaboration feature with its own rules (a block may not escape; what it captures is
threaded), and non-local exits through arbitrary library code.

**Cannot express.** D1: a body that uses a capability or a `let mut` without threading it by
hand; a nested loop with an exit across both except by nested `try_fold`s. D2: nothing of the
test set, once blocks exist.

---

## 7. Q0: `for`, or no `for`

The user asked whether the language should have `for` at all. It is the one decision here that
is hard to reverse: it fixes how the corpus, the book and every user program read.

### 7.1 The programs side by side

**T1 `io-wc`.** With `for` (A, B, C; today's syntax, `wc-for.bc`):

```
fn count(c: In) -> In * (i32 * (i32 * i32)) =
  let mut lines = 0; let mut words = 0; let mut chars = 0; let mut in_word = false;
  for b in bytes(&mut c) {
    chars = chars + 1;
    if b == 10 { lines = lines + 1 };
    if is_space(b) { in_word = false }
    else { if not(in_word) { words = words + 1 }; in_word = true }
  };
  (c, (lines, (words, chars)))
```

D1 (`wc-fold.bc`, runs today):

```
fn wc_step(p: (i32 * (i32 * (i32 * bool))) * i32) -> i32 * (i32 * (i32 * bool)) =
  let ((lines, (words, (chars, in_word))), b) = p;
  let lines = if b == 10 { lines + 1 } else { lines };
  if is_space(b) { (lines, (words, (chars + 1, false))) }
  else { if in_word { (lines, (words, (chars + 1, true))) }
         else { (lines, (words + 1, (chars + 1, true))) } }

main -> … = let (lines, (words, (chars, _))) = fold_bytes(&mut stdin, (0, (0, (0, false))), wc_step); …
```

D2: `let (lines, words, chars) = bytes(&mut stdin) |> fold((0, 0, 0, false), { (s, b) -> … })`,
or with capture, `bytes(&mut stdin) |> for_each({ b -> chars = chars + 1; … })`, which is `for`
spelled as a call.

**T2 `upper`, P12.** With `for`: `for c in v { modify c { x -> up(x) } }`. D1/D2: `v |>
for_each({ c -> modify c { x -> up(x) } })`. Equal; the body uses nothing from outside.

**T6c, nested loops with an exit across both.** With `for` (A–C):

```
for i in 0..n { for j in (i + 1)..n {
  if at(v, i) + at(v, j) == 2020 { return inl (at(v, i) * at(v, j)) } } };
inr ()
```

D2: `(0..n) |> find_map({ i -> ((i + 1)..n) |> find_map({ j -> if … { some(…) } else { none } }) })`.
D1 today (`aoc-pair.bc`, 36 lines, runs): two nested `count_fold`s whose state carries the view,
the outer entry and the answer, with no early exit.

**Loops with several accumulators and I/O** (T6b, P1's `main`, P14). With `for`, the variables
are `let mut` and the body calls `put_dec(&mut stdout, …)`. D1 puts `stdout` in the accumulator
(`print-count.bc`'s `emit`, `(Out * array i32)` threaded); D2 captures it.

**The operator** (T5). It is already written without loop statements for its pipelines
(`merge(…) |> take_until(stop) |> debounce(…)`), and with `for` inside `generate { }` blocks and
in `serve_metrics`. Its combinator bodies are blocks that capture borrows and perform effects
(`retry(…, { … })`, `span("reconcile", key, { … })`): D2's blocks, which it needs with or without
`for`.

**An effect-only body** (T10). With `for`: `for x in &a { put_dec(&mut stdout, *x) }`. D1:
`count_fold(emit, n, 0, (stdout, a))` with `emit` a named function taking and returning `stdout`.
D2: `&a |> for_each({ x -> put_dec(&mut stdout, *x) })`.

### 7.2 The trade-offs

- **Readability and familiarity.** `for`, `break` and `return` read as in Rust, Python, Swift,
  Zig and Lean; most users will look for them first. Combinators read as Rust's iterator chains
  and Haskell; they are clearer for a transformation (`filter |> map |> sum`) and less clear for
  a loop with three accumulators and an exit. D1 is worse than both on this test set, for a
  reason specific to this language: its bodies cannot capture (F5), so every accumulator is a
  tuple component and every capability is threaded by the program (`wc-fold.bc` against
  `wc-for.bc`; `aoc-pair.bc`).
- **Semantic clarity.** D's advantage: which eliminator runs is the name of the combinator
  (`fold` over a view is total, `drive` of a stream is div), not a decision hidden in `for`. With
  `for`, the same syntax is a K0′ loop or a machine state, and the reader learns which from the
  source's type. The candidates keep that decision to one table (§6.0), read off the type former,
  and `total` makes it checkable.
- **Elaboration complexity.** What `for` needs that combinators (D1) do not: threading of
  assigned variables and capabilities, lends in the body, `break`/`return`, the choice of
  eliminator. PR #132 showed the risk: `for` became the place where source kinds, bounds, lends
  and fallbacks accumulated. D1 has none of that, and pays for it in every program (above). D2
  has all of it, in specialization instead of in `for`, where every higher-order function uses
  it. So the real choice is where the machinery lives, not whether it exists.
- **Precedent** (§5). Without loop statements: Haskell (list comprehensions desugar to
  foldr/build), Koka (`for`, `while` are library functions with trailing lambdas; `return` in a
  lambda does not leave the function), Effekt (one `while`; the rest are functions over
  second-class blocks, with `break` as a `Label` capability), Clojure (transducers driven by
  `reduce`). With `for` over an abstraction: Rust (`IntoIterator`), Lean (`ForIn`, with `let mut`
  threading and `break`/`return` compiled into the state), Swift, C++, Zig (loops as expressions
  with `else`), Python. Scala's `for` is sugar for `foreach`/`map`/`flatMap`/`withFilter`. Kotlin
  has both, with inline lambdas that may `return` from the enclosing function. The survey's
  pattern (§5.9): where the body is a closure, `break` and `return` need extra machinery.
- **Middle options.**
  - *`for` over data only.* A `for` over codata is rejected; codata is consumed by combinators.
    This makes "`for` is total" a rule, but codata loops (T1, T5, T6a–b, most of the corpus) lose
    the syntax that serves them best.
  - *`for` as sugar for `src |> for_each(block)`, with no `break` and no threading.* With D1's
    closures this is useless (the block can use nothing); with D2's blocks it is exactly D2,
    and `for` costs nothing to keep.
  - *`for` now, defined by D2 later.* Keep `for` with the elaboration of A/C. When second-class
    blocks land, redefine `for x in s { B }` as `for_each(s, { x -> B })`, and move the threading
    into block specialization. Programs do not change.

### 7.3 Answer to Q0

Keep `for`, and keep it narrow: one table of source kinds by type former, one transformation
(push, in C), the exit rule, and the threading it already does. Do not remove it now: removal is
a large rewrite (§9), D1 reads worse on the test set, and D2 needs a feature (blocks) that is not
designed. Plan for `for` to become D2's `for_each` with a block once blocks exist, so that the
machinery ends up in one general mechanism. The user decides.

---

## 8. Comparison and recommendation

### 8.1 Table

| | A typed sources | B + Mealy pipelines | C + push/pull | D1 no `for`, closures | D2 no `for`, blocks |
|---|---|---|---|---|---|
| R1 finiteness by type, no truncation | yes | yes | yes (no bound exists) | yes | yes |
| R2 adapters once for all sources | generators only; pipelines over data div | Mealy adapters yes; `flat_map`/`zip` no | yes (today's adapters) | yes | yes |
| R3 fused, 0 alloc, 0 dispatch | yes | yes | yes | yes | yes |
| R4 borrowed data, `iter_mut`, borrows in body | yes | yes | yes | by threading | yes |
| R5 honest codata, fuel | yes | yes | yes | yes | yes |
| R6 `break`/`return`/`find`/`take`/value | yes (K0′) | yes | yes | combinators only | yes |
| R7 `let mut` state | yes | yes | yes | accumulators | yes |
| R8 escaping effects | yes | yes | yes | no (threaded by hand) | yes |
| total pipeline over data | no | yes, Mealy only | yes | yes (combinators) | yes |
| finite producer passed as a value, total | no | yes (`Pipe`) | no | yes (data + combinator) | yes |
| kernel | K0′ | K0′ | K0′ | K0′ | K0′ |
| new library | none | `lib/xf.bc` | none | combinators | combinators |
| elaboration | dispatch by type former; `a..b`; lends | A + `Pipe` loops | A + push transform; `while` in div bodies | `|>` | `|>`; second-class blocks |
| implementation cost | small | medium | medium | small (library), large (corpus) | large |
| proof cost | K0′; completeness lemma | as A | as A | K0′ | K0′ |
| corpus change (§9) | none required | none required | none required | 145 loops | 145 loops |

### 8.2 Recommendation

1. **Q0: keep `for`** (§7.3).
2. **Now: candidate A**, with K0′, `a..b`, `for x in v` over views, PR #132's array lend, the exit
   rule, and the completeness lemma. It fixes R1 by type, deletes the name table, and makes the
   strings programs over views total. It is a subset of B and C, so nothing is thrown away.
3. **Next: candidate C.** It adds total pipelines over data with the adapter library as it is,
   and no bound anywhere: a pushed pipeline is total exactly when the loops it inlines to are over
   data, which the existing inference decides. It is the design in which "a wrong bound would
   silently truncate" cannot happen, because there is no bound.
4. **Not now: B.** Its one advantage over C is a finite pipeline as a first-class, total value.
   No target program needs it; the operator passes codata. If one does, B's `Pipe` can be added
   on top of C.
5. **Later: D2's blocks**, driven by the operator (#18, handlers), and then `for` as
   `for_each` with a block.

Reasons, briefly: A and C keep every existing program and the adapter library; they put the
source-kind decision on the type former, where the kernel already has it (F1–F4); C removes the
need for any bound, which is the defect of PR #132; and neither closes the door on D2.

---

## 9. Corpus impact

`for` loops today (`grep` of `for … in` outside comments, in `corpus/` and `lib/`, excluding
the hand-written `.core.bc` sides of sugar pairs): **145 loops in 86 files**, of 216 `.bc` files.
The book has 21 more in four chapters (`guide/divergence.md`, `generators.md`,
`command-line-tools.md`, `planned/pipelines.md`). By source:

| source | loops | examples |
|---|---|---|
| external input (`bytes(&mut stdin)`, `lines(stdin)`, pipelines over input) | 59 | `io-*`, `lend-*`, `gen-adapters-io` |
| a call of a finite generator (`range`, `upto`, pipelines over them) | 51 | `gen-*`, `sugar/gen-*` |
| a generator held in a variable (inside `gen fn` bodies: every adapter) | 29 | `lib/adapters.bc` (13), `gen-pipeline` |
| a generator holding an output capability | 4 | `gen-lazy`, `axes/codata-effects` |
| data (a view, a list) | 2 | `pending/iter-mut`, `pending/print-borrowed-list` |

Of the 145: 13 are in `lib/adapters.bc`, 21 in `corpus/reject/`, 5 in `corpus/pending/`, 15 in
`corpus/sugar/` (pairs whose core side is hand-written), and the rest are running programs.

| candidate | what the corpus needs |
|---|---|
| A | nothing: every loop keeps its meaning (all are over codata). The `range` generators programs define stay generators; PR #132's programs change `iter_mut(v)` to `v` and `range(n)` to `0..n`. Two pending programs become expressible (`for-finite`, `iter-mut`). |
| B | as A; the Mealy library is new code with new programs. |
| C | nothing required: the 51 loops over finite generator calls are pushed, with the same answers. They stay div, because the corpus's `range`/`upto` are written with `while`; each becomes total if rewritten over `a..b` (mechanical). Counts are expected not to rise (a pushed loop has no machine state per adapter); not measured. |
| D1 | every loop is rewritten. The 59 input loops become `fold`/`for_each` over the stream with explicit accumulators, and those using `stdout` thread it (a mechanical but not local rewrite). The 29 loops in generator bodies need a pull primitive and `while`, or D keeps `for` inside `gen fn` (then D is "no `for` outside generators"). The `for`-specific programs, sugar pairs and rejects (`io-for-*`, `sugar/for*`, `reject/for-*`, `reject/io-for-*`: 10 programs) are deleted or rewritten. The four book chapters are rewritten. |
| D2 | as D1, but each rewrite is local (`for x in s { B }` → `s |> for_each({ x -> B })`), once blocks exist. |

**Shapes that become awkward or impossible**, by candidate:

| shape | A | B | C | D1 | D2 |
|---|---|---|---|---|---|
| nested loops with an exit across both (T6c) | `return`/labelled `break` | same | same | nested `try_fold`, answer carried | nested `find_map`, or `return` from a block |
| several accumulators with I/O (T1, T6b, P1) | natural | natural | natural | tuple accumulator; capability threaded by hand | natural |
| lockstep over two views (T7) | index loop | index loop | index loop, or `zip` pushing one and pulling an `iter` | `zip` combinator over views (library) | same |
| lockstep over two generators | pull × pull, div | same | same | same | same |
| total pipeline over a view (P5, P6, P13) | not total (div) | total if Mealy | total | total | total |
| a total function over a finite producer given as an argument | take the data | `Pipe` value | take the data | take the data | take the data |
| a borrowed `μ` list in order | open (F3) | open | open | open | open |
| an element lent by a pulled iterator (a lending `next`) | excluded in every route (`not_lendingYield_*`, LoopBorrow); push form works | same | same | same | same |
| a loop in a loop body in a div function | allowed (§6.0, lifts F8) | same | same | nested combinators | same |

---

## 10. What of PR #132 is reusable

| piece of PR #132 | A | B | C | D |
|---|---|---|---|---|
| `&a`/`&mut a` of an owned array at a view parameter (`lendSlice`, `slice_borrow_*` around the call, a returned view dropped) | kept as is | kept | kept | kept |
| a lend in a total `for`'s source as a borrow block around the loop | kept, for `for x in &mut a` | kept | kept | becomes the lend around a combinator call |
| generic instances whose type arguments carry lifetimes (`'gl0` parameters; `map` at `imm 'x i32`) | kept (needed for generators over views) | kept | kept, essential (pushed and pulled adapters over views) | kept |
| `iter_imm`/`iter_mut` as `gen fn`s over a view | not needed as `for` sources; kept for pulling | kept for `through` | kept: they are the generators pushed into view loops | kept |
| `len_imm` | kept | kept | kept | kept |
| `forTotal`'s `count_fold` template (state = source + threaded variables; step a closure capturing nothing) | kept, keyed by type former; its generator-observation part removed | kept | kept | becomes the library's `fold` |
| the bounded-source table (names and bounds) | deleted | deleted | deleted | deleted |
| `range` as the elaboration's name | replaced by `a..b` | same | same | a library count source |
| `take(from_iter(bytes(&mut c)), n)` total by name | replaced by the counted pull of an `iter` (explicit count) | same | same | a combinator over `iter` |
| a `for` last in a body as a statement | kept | kept | kept | n/a |
| the programs (`for-finite`, `iter-mut`, `split-at-mut` in direct style, `slice-total`, `slice-pipeline`, `print-borrowed-array`, `take-bytes`) | kept with spellings changed; `slice-pipeline` is div in A | kept | kept, all total | rewritten |

---

## 11. The runnable examples

`docs/iteration-examples/`, run by `docs/iteration-examples/run.sh` at `main` (a30d65b). Each is
checked, interpreted, compiled to WebAssembly and run, and counted (allocations, dispatched
calls, copies; `bcc-counts`). Interpreter and compiled outputs agree for every one.

| file | style | result | allocs / indirect / copies |
|---|---|---|---|
| `wc-for.bc` | T1, `for` (A–C, today) | `3 10 50`, div | 2 / 0 / 0 |
| `wc-fold.bc` | T1, D1: fold with a tuple accumulator | `3 10 50`, div | 2 / 0 / 0 |
| `fold-generic.bc` | D's generic `fold` over a generator | 6, div | 0 / 0 / 0 |
| `sumsq-count.bc` | `count_fold` called directly (D1) | 285, total | 0 / 0 / 0 |
| `sumsq-gen.bc` | `for` over the program's own `range` generator | 285, div | 0 / 0 / 0 |
| `sumsq-gen-total.bc` | the same with `total` | rejected: "it has a `for`" | — |
| `upper-count.bc` | P12 with `count_fold` and `get_mut` (D1) | 100, total | 1 / 0 / 0 |
| `upper-for.bc` | P12 with `for c in iter_mut(v)` inside `borrow mut` | rejected: "the iterator of this `for` holds the borrow" (F1) | — |
| `find-break.bc` | T9: `break e` over a generator (div), and the library's `find` (total, no early exit) | (8, 6) | 1 / 0 / 0 |
| `aoc-pair.bc` | T6c, nested `count_fold`s, no early exit (D1) | 514579, total | 1 / 0 / 0 |
| `aoc-groups.bc` | T6b, `for` over the input with five `let mut` | 24000, div | 2 / 0 / 0 |
| `aoc-groups-pipe.bc` | T6b as a pipeline: `lines`, `map` of a fold, `batch`, max | 24000, div | 43 / 0 / 0 |
| `take-fib.bc` | T8, `take` of an infinite generator | 88, div | 0 / 0 / 0 |
| `zip-pull.bc` | T7 pull × pull (`zip` of `range` and `filter`) | 140, div | 0 / 0 / 0 |
| `print-for.bc` | T10, `for` whose body only writes (`stdout` threaded implicitly) | `1 2 3 4 5`, div | 1 / 0 / 0 |
| `print-count.bc` | T10, D1: `count_fold` threading `stdout` by hand | `1 2 3 4 5`, total | 2 / 0 / 0 |

What they show:

- The pipeline form of T6b allocates 43 objects against 2 for the loop: `lines` builds each line
  as a list. With `lines` yielding views of a buffer (strings S5) the two would match.
- Every `for` over a generator is div, including `sumsq-gen.bc`, whose generator is finite. The
  total versions today are `count_fold` calls written by hand (`sumsq-count`, `upper-count`,
  `aoc-pair`, `print-count`), which is what candidate A's `for` over data elaborates to.
- D1 today costs lines, not run time: the counts are the same or lower, and the programs are
  longer (`aoc-pair.bc` is 36 lines for an 8-line loop; `print-count.bc` names a step function
  to thread `stdout`).

Sketches that need unbuilt features: every program in §4 written with `a..b`, `for x in v`,
`for … else`, `return` in a `fn`, `|>`, or blocks.

---

## 12. Open questions for the user

0. **Q0: keep `for`?** Recommended yes (§7.3); the alternative is D2 once blocks exist, with D1 in
   between.
1. **Candidates.** A now and C next (recommended), or A then B, or D.
2. **The count's spelling.** `a..b` (syntax, recommended), `range(a, b)` kept as the elaboration's
   own form (PR #132), or a nominal `Range` once modules give opaque types (#63).
3. **K0′.** Add `count_try` beside `count_fold`, or replace `count_fold` by it (decision 20),
   which needs the core's `0` to have an eliminator the lowering erases.
4. **`return` in a `fn` body** (F7). Give `return e` Rust's meaning in surface `fn` bodies (a
   core `return V` would be written `V`, as a tail expression already is), or a new keyword for
   the early return, or keep early return to `break e` out of a loop whose value is the
   function's result.
5. **A loop's value.** `let r = for … { break e } else { d }` (Zig), or the value of a `for` over
   data is `E + 1` (`inl e` after `break e`, `inr ()` at the end), or no value (Rust's `for`).
6. **`for` over `μ` data.** Not a `for` source (folds only), or a right-to-left order stated,
   or an owned list consumed front to back by a new eliminator (a kernel change). A borrowed list in
   order stays open (F3).
7. **The counted pull of an `iter`.** Spelling (`for b in bytes(&mut c) up to n`, or a library
   `first(n, it)`), and whether the loop's value reports that the source did not finish (as
   `div_fuel`'s `A ⊕ Q` does).
8. **The completeness lemma** (§6.0): prove it in `Support/` with A (recommended), or accept the
   view loop as a reviewed template.
9. **SPEC §14 Open's "A div function has no type parameters"** is stale since #131
   (`fold-generic.bc`); correct it in the next SPEC change.
