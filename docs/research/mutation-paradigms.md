# Expressing what Rust uses `let mut` for in borrow-core

## 1. Bottom line

- **No single mechanism replaces `let mut`. The work divides by what the state is.** Six paradigms were proposed and each was critiqued against the repo. None of them covers all 14 test programs, and every "one mechanism" claim failed on review. What survived:
  1. **Loop-carried values** cover accumulators, counters, trackers, flags, state machines and rotations (C1–C4, C8, C11). That is 30 of the 51 Rust bench sites and most of the corpus sites.
  2. **Lends at the call** (`f(&mut x)`, SPEC §11 / ergonomics A4) and **place update** cover collections (C6, C7, C10, C16).
  3. **Answering handlers with state** cover injected services and memo tables (C9, C14).
  4. **Affine closures (`Aff`) with state** cover stateful closures that escape (C13, the counter case).
  5. **Generators** cover callbacks we can invert (C13 visitors).
- **The trap the user describes is real, but it sits in the plumbing, not in the binder.** About a quarter of corpus `let mut` sites (C16: 333 of 1201 by mechanical bucket, 9 of 45 in the hand sample) do nothing that Rust's `let mut` does. They exist to rebind a linear value that a consuming call hands back: `let (v2, x) = peek(v, j); v = v2` and `let mut x = x`. Rust writes these as `&mut` calls. Removing this plumbing is the largest available win, and most of the mechanism for it already exists: `f(&mut x)` rewrote 149 of 177 sites with the same output.
- **"Mutability is a state effect" is right as theory and wrong as an elaboration target.** Koka implements `var` with a state handler (verified). Our `handle_fold` reads handler state as state passing. But elaborating a variable as `borrow mut (alloc e) { … }` over the rest of its scope fails to type wherever a resuming operation occurs: `await`, `yield`, and every `while` once B2 makes it a Div loop. The reasons are T1 (#172) and Row.Unwind (SPEC §14). `handle_fold` is a one-way `Steps` fact about one cell, so it does not justify choosing between a register and a cell per site. So: use the State laws to say what an assignment means, and keep today's threading as how it runs.
- **`let mut` stays as a surface form, demoted to what it already is.** It is sugar for a local whose value the elaborator threads through folds and joins. One new invariant applies to it: **every assignment is threaded or refused, never dropped.** Dropping the marker altogether (the MVS and Places proposals) was refuted: it removes an enforced local-reasoning check (rustc rejects reassigning an immutable binding), and it widens the stale-read hazard to every captured variable. The spelling is open.
- **Pure-sugar gains with no kernel cost:**
  - `+=` and the other compound assignments;
  - simultaneous tuple assignment `(a, b) = (b, a + b)`, which replaces temporaries and `mem::swap`;
  - `break e` / `else` loop values, which replace the flag-plus-sentinel pattern;
  - freezing by shadowing (`let cfg = cfg`).
- **#586 is closed by an elaborator rule, not by a new paradigm:**
  - An assignment inside an in-place `run` or a head is joined, as #581 was.
  - Inside a closure at a block parameter (§30/§32), the value is threaded in and out, as §32 already does for capabilities. This gives 52.
  - Anywhere else it is a compile error that points at an alternative.
- **The hard gaps are in the borrow layer and the library, not in `let mut`:**
  - Reads through a `mut` view cost two swaps (`peek`).
  - There is no index read of an owned array.
  - A looping callee may take only one borrow (lend-div-two).
  - SPEC §18 does not provide a `&mut` lend in the arguments of a call that threads a capability, nor a capability threaded through `for … in &a`.
  - `withswap` has no unwinding form.

  These decide whether T04, T05, T09 and T14 read like Rust.

## 2. What `let mut` is used for

These counts were mined this session over `~/repos/borrow-core-audit` at dd133c8. The Rust bench sites were all read by hand; the corpus figures come from a heuristic classifier plus a seeded hand sample of 45. None of these numbers is in the repo docs yet. `docs/ergonomics.md` §1.2 uses a narrower method for the `let mut x = x` count (68 against 241 here), and the two have not been reconciled.

| Category | Rust bench (51 `let mut`) | Corpus mechanical bucket (of 1201) | Hand sample (of 45) |
|---|---|---|---|
| C1 loop accumulator | 16 | 198 (`x = x op e`) | 7 |
| C2 counter / while index | 11 | 200 (`x = x ± 1`) | 8 |
| C3 best-so-far tracker | 3 | — | 4 |
| C4 flag / mode bit | 0 (Rust uses `break`) | 59 | 4 |
| C5 cursor / parser position | 0 (counted under C2) | in "other" (~247) | 8 |
| C6 collection builder | 1 (+2 API-filled buffers) | — | 1 |
| C7 in-place collection update | 10 | 59 (mut-borrowed, never reassigned) | 3 |
| C8 state machine | 0 | rare | 0 |
| C9 memo through recursion | 0 | 3 sites | 0 |
| C10 simulation stepped in place | 1 | — | 0 |
| C11 swap / rotate | 0 explicit | — | 0 |
| C12 config record filled in steps | 1 | 0 (no records yet) | 0 |
| C13 write through a closure (#586) | 1 | 0 (avoided because #586 drops the write) | 0 |
| C14 stateful object / `&mut` out-param | 4 (+13 `mut self`, 43 `&mut`) | 55 handler `mut` params | 0 |
| C15 state across `await` | 3 | ~25 async files | 0 |
| **C16 ownership plumbing (ours only)** | **0 by construction** | **333** (225 pair-rebind + 108 `x = f(x, ..)`); 241 exact `let mut x = x` | **9 (the largest group)** |

The hand-sample row as summarised adds up to 44, so one site went unlabelled. Most Rust mutation does not go through `let mut` locals at all; it goes through `&mut` parameters and methods (43 `&mut`, 13 `mut self`, 0 `Cell`/`RefCell`/`Rc`). C12 and C9 are rare because of design gaps, not because they are rarely needed: the k8s-operator north star needs C8, C12 and C14.

## 3. Fit matrix (after the critics' corrections)

Key:
- **N**: natural.
- **W**: workable.
- **A**: awkward.
- **X**: refused or impossible as written today.
- **C**: conditional on an unbuilt piece, named in the cell.
- \*: the paradigm's own critic did not correct this grade, but a finding in another critique applies to it.

| Test | State effect | Loop carry | Mutable value semantics | Codata objects | Streams / dataflow | Places + extents |
|---|---|---|---|---|---|---|
| T01 acc + count + max | N (fold form = today) | N | N | W (object is ceremony) | N | N |
| T02 flag / early exit | N | N | N | A (no `position`/`find(pred)`/`or`) | W (no sized `scan`) | N |
| T03 tokenizer cursor | N | A (frame rule broken by `(pos, n) =`) | N | X (lend across `yield`, T1) | W | N |
| T04 insertion sort | C (`while` after B2) | A | A–W (imm-of-mut reborrow, `peek` cost) | X (`&mut` in a capability-threading call) | W | W (only one borrow allowed) |
| T05 DP + ping-pong | A/X (`<->` not available) | A | N\* (no owned index read) | A | X (step synchrony needs a copy) | W |
| T06 word freq | X (§18 rows) | A/X | W\* (missing lib) | A | X (`entry_or` untypable) | A / not today |
| T07 turnstile | N | C (U3) | N (#141) | W (#141) | N | N (#141) |
| T08 memo Collatz | W | A | W | X (`!` closure in adapter) | A | W (no `mut Map` ops) |
| T09 particles | X today | A | A | X | A | W |
| T10 swap / rotate / gcd | N | N | N | W (stream seeds) | N | N |
| T11 config builder | N | W (#141) | W (#141) | W (#141) | N (#141) | W |
| T12 closures (#586) | C (vars as capabilities, unbuilt) | X | A | (2)(3) N, (1) C | X ((2) only) | C (`aff {}`, N1) |
| T13 async tellers | X (R1) | W? | X (blocked pending/async-bank shape) | X | A, unverified | X |
| T14 RNG + logger + buffer | X (§18 rows) | A | W | X (§18 rows) | A | N\* (`for slot in` a view parameter is a reborrow) |

Read down the columns: no paradigm is N or W on all 14. Read across the rows: every program has at least one N or W cell except T13. T13's Rust shape (a task holding `&mut` from outside while reading other variables) is refused by R1 under every paradigm. The corpus shape (`corpus/async-bank-inbox.bc`) works.

## 4. Recommended design

There are seven parts, D1–D7, and one invariant. Spellings are provisional throughout, and `let mut` below is today's spelling, not a decision.

### D1. Loop-carried locals (C1–C4, C8, C11, C5 cursors)

- **Surface.** `let mut x = e`; assignment `x = e`; `x op= e`; tuple assignment `(a, b) = (b, a + b)`; `break e` and `for … else { d }`; freezing by `let x = x`.
- **Elaborates to.** Today's threading: `count_fold` / `count_try` for counted loops, the machine loop for `while`/`loop`, and join points at `if`/`match`. The carried set is inferred. U3 (live variables with scope) fixes #493's capture cause without a new surface. Tuple assignment reads every right-hand side first, then rebinds. The value of `while`/`loop` (S11/U4) is planned.
- **Laws.**
  - Loop beta: a loop is the fold of its step.
  - `countTry_exit` is proved (Support/Dynamics/Completeness.lean).
  - Carried permutation is α-renaming of the step's parameters.
  - Tupling several folds into one (banana-split; attribution unverified) holds only for duplicable sources.
  - "Dead-state elimination" is dropped: it is unsound for linear carried values.
- **Lowering.** Carried values become loop-header parameters. Honest caveat: today's `count_try_loop` calls the step on a copy of the closure with the state as one value. Registers and phis "by construction" are a property of the planned compiler (docs/compiler.md §3.3), not of today's backend.
- **Borrows.** Unchanged. A carried `mut` view is linear, so every exit hands it on.
- **Status.** Pure sugar. N3 `+=`, tuple assignment and `break e` need frontend work only. U3 and U4 are already planned.

### D2. The write-resolution invariant (#586)

- **Rule.** An assignment to `x` is legal only where the elaborator threads `x` through it. Writes are refused, with a message, in exactly these places:

  | Where the assignment sits | Elaboration |
  |---|---|
  | Same frame: body, arms, heads | Join points (#581 / PR #585, U3) |
  | Inside an in-place `run` | ANF into the enclosing sequence, then joined |
  | Inside a closure written at a block parameter `!(A => B)` of a declared function (§30) | `x` is threaded into the block and handed back, exactly as §32 threads a capability ("takes them first and hands them back first", `!U(C ⊗ A ⊸ F_r (C ⊗ B))`). `corpus/block-capability.bc` is #586's shape for handler state and gives 6 today. |
  | Stored thunk, stored or let-bound closure, a `!` value that is not a block, or anything escaping | **Refused**: "`x` is written inside a closure that outlives this statement; return the value, pass the closure as a block, or put the state in a cell / `Aff`" |

- **Laws.** In place, the global-state laws for one location (get-get, put-get, put-put, get-put; Plotkin–Power, equation list unverified) make threading equal to a cell. The refusal covers exactly the places where threading would not equal a cell. None of these laws is a Core theorem today, so stating them is a proof task.
- **Status.** Elaborator only, with no kernel change. It needs a SPEC entry because it changes which programs are accepted. Extending §32's block rule from capabilities to `let mut` values is new elaborator work. **Hypothesis:** it is the same derivation with the value in place of the capability. That is unchecked.

### D3. Lends at the call instead of rebinding (C16, C6, C7)

- **Surface.** `f(&mut x, …)`.
- **Elaborates to.**
  - For an owned value, the SPEC §11 lend (A4): move in, move out.
  - For an owned array passed to a call, `slice_borrow_mut`.
  - For a `mut` parameter, a reborrow (`withbor3`).
- **Gaps to close, in order.**
  - (a) A4 is refused at 14 sites where the threaded value is itself a view. These need a reborrow; "move the view in and out" fails once the body iterates or splits it.
  - (b) SPEC §18 does not provide a `&mut` lend in the arguments of a call that threads a capability. That blocks T04/T09/T14 with an injected service.
  - (c) Several `&mut` arguments in one call: unverified.
  - (d) **Abort semantics:** with A4 value threading, a `raise` inside `f` drops `x` with the frame. By-reference would keep it. This is the critic's reading of SPEC §11 and must be confirmed and designed before A4 is extended.
- **Method syntax `x.m()`.** Left open (O4). It collides with §38's `n.op(v)` for named instances.

### D4. Place update on collections (C7, C10, C12)

- **Surface.** `a[i] = e`, `r.f = e`, `p.f += e` through a `mut` element.
- **Elaborates to.**
  - On an owned array, `array_replace` (in place, because handles are never persistent; SPEC §9).
  - On a record field through `mut`, `swapField` (Core/Records.lean, per the critic) rather than a whole-record `modify`.
  - The right-hand side is computed **before** the swap, because `withswap` has no unwinding form (SPEC §19). That is an ANF obligation on the elaborator.
- **Laws.** The lens laws hold only in range and for persistent elements. `array_replace` past the end answers `inr x` and changes nothing. Put-put on a linear element must run its destructor.
- **Not built.**
  - An index read of an owned array: there is no kernel read, and `at(&a, i, d)` is a lend per read.
  - A direct read through a `mut` view: `peek` is two `slice_replace_mut` calls.
  - An imm reborrow of a `mut` view (`len(&v)` on a `mut` parameter).

  The view-read items are a **borrow-calculus change** and need a SPEC entry and a proof; see O6. Records depend on #141.

### D5. Stateful services and memo tables (C9, C14): answering handlers with state

- **Surface.** Already shipped: `handler h(mut s: S): E = { op(x) = { s = …; … } }`, `with h(&mut c) { … }`, and the state read after through the caller's cell (bench/handlers-di, #538). Named instances are §38.
- **Laws.** `op_tail` / `op_answer` (a tail-resumptive op is `withswap` on the cell); `handle_fold` (a `Steps` fact for a straight-line list of operations on one cell).
- **Lowering.** A tail-resumptive clause becomes a direct call on a local cell of the handler's scope (docs/compiler.md §3.2). Caveat: a stateful **resuming** handler dispatches a closure call per resume (SPEC §21; native handler parameter not built).
- **Gaps.**
  - The §18 rows from D3(b), plus "capability threaded through `for … in &a`".
  - `.state` after `with h(e)` does not exist: the cell is dropped, so the program must use `with h(&mut c)`.
  - Every corpus handler has one `mut` parameter; multi-field state goes in a pair or record.

### D6. Escaping stateful closures (C13 counter, visitors you do not own)

- **Surface.** An affine closure over its own state, called through `Mut` (`aff_call_mut`). Its close hands the residual state back.
- **Elaborates to.** SPEC §22 `Aff` (`corpus/aff-counter.bc`, `logProg` in docs/fnmut.md).
- **Cost.** `aff-counter` measures 2 allocations and 0 indirect calls. `aff-higher` measures 6 indirect calls once closures built at two sites reach one function (monovariant flow).
- **Gaps.** `aff { }` sugar and its checker rule are not built (fnmut.md §9). A borrow-capturing `Aff` must be boxed at a shorter lifetime under a scope of its own.

### D7. Callback inversion and stream seeds (C13 visitors, C11 alternatives)

A callee we own is rewritten as a generator consumed by `for`: `bench/gen-tree-cb` is direct and allocation-free. Rolling state can also be a stream seed (`unfold`), as library code. This is **not** for cursors that hold a lend across `yield` (T1).

### What is sugar and what needs kernel work

| Item | Kind |
|---|---|
| D1; `+=`; tuple assignment; `break e`; freeze by shadowing; D7 | Pure sugar, or library |
| D2 | Elaborator plus SPEC entry; no kernel change |
| D3 (a)(b), D5 gaps | Elaboration rules around capabilities. SPEC entries; proof status to be checked against §18 |
| D4 reads through `mut` views, imm-of-mut reborrow | **Borrow-calculus change**: SPEC entry plus proof, subject to "nothing breaks the borrow calculus" |
| Native handler state parameter (§21), `aff { }` checker rule, polyvariant closure flow | Effect side and compiler |
| State laws as Core theorems | Proof work. Independence needs a side condition excluding an instance and its own reborrow |

### All 14 test programs in the recommended surface (provisional syntax)

**T01** (D1, today plus `+=`)
```
let xs = [3, 8, -2, 7, 10, 5, -6, 4];
let mut sq = 0; let mut odd = 0; let mut best = i32_min;
for x in &xs { if x % 2 == 0 { sq += x * x } else { odd += 1 }; if x > best { best = x } };
println(sq, odd, best)                                   -- 220 3 10
```

**T02** (D1; `break e` / `else` exist for `for`; the `while` value is U4)
```
fn first_over<'a>(xs: array_imm 'a i32, limit: i32) -> i32 =
  let mut run = 0;
  for (i, x) in enumerate(elems(xs)) { run += x; if run > limit { break i } } else { -1 }
main =
  let xs = [4, 1, -3, 9, 2, 8];
  let mut i = 0; let mut all_pos = true;
  while i < len(&xs) { if at(&xs, i, 0) < 0 { all_pos = false; break }; i += 1 };
  println(first_over(&xs, 10), first_over(&xs, 100), all_pos, i)   -- 3 -1 false 2
```

**T03** (D1 cursor as loop state, D3 for the builder; a generator holding the input's lend across `yield` is refused by T1)
```
let s = b"12,-3, 40,x,7";
let mut pos = 0; let mut vals = buf_new[i32](4); let mut errs = 0;
while pos < len(&s) {
  while pos < len(&s) && at(&s, pos, 0) == b' ' { pos += 1 };
  let neg = pos < len(&s) && at(&s, pos, 0) == b'-';
  if neg { pos += 1 };
  let start = pos; let mut n = 0;
  while pos < len(&s) && is_digit(at(&s, pos, 0)) { n = n * 10 + digit(at(&s, pos, 0)); pos += 1 };
  if pos == start { errs += 1 } else { push(&mut vals, if neg { -n } else { n }) };   -- A4
  while pos < len(&s) && at(&s, pos, 0) != b',' { pos += 1 };
  pos += 1
};
println(vals, errs)                                      -- [12, -3, 40, 7] 1
```

**T04** (D3 + D4; `get` through a `mut` view is gap O6, today it is `peek`; only one borrow parameter is allowed because of the `while`)
```
fn insertion_sort<'a>(v: array_mut 'a i32) -> i32 =
  let mut swaps = 0;
  for i in 1..len_of(v) {                       -- needs imm-of-mut reborrow (O6); today len_mut
    let mut j = i;
    while j > 0 && get(v, j - 1) > get(v, j) { swap(v, j - 1, j); swaps += 1; j -= 1 } };
  swaps
main =
  let a = [5, 2, 9, 1, 5, 6];
  let swaps = insertion_sort(&mut a);           -- §9 lend of an owned array to one call
  let b = copy(&a);
  let mut lo = 0; let mut hi = len(&b) - 1;
  borrow mut b { v -> while lo < hi { swap(v, lo, hi); (lo, hi) = (lo + 1, hi - 1) } };
  println(a, swaps, b)
```

**T05** (D4 on owned arrays; the owned index read is a gap; ping-pong is tuple assignment)
```
fn coins<'c>(cs: array_imm 'c i32, amount: i32) -> i64 =
  let mut dp = array_new[i64](amount + 1, i64_max);
  dp[0] = 0;                                        -- array_replace
  for a in 1..amount + 1 { for c in elems(cs) {
    if c <= a && dp[a - c] != i64_max { dp[a] = min(dp[a], dp[a - c] + 1) } } };   -- reads: gap
  if dp[amount] == i64_max { -1 } else { dp[amount] }
fn lcs(x, y) -> i32 =
  let mut prev = array_new(len(y) + 1, 0); let mut cur = array_new(len(y) + 1, 0);
  for i in 1..len(x) + 1 {
    for j in 1..len(y) + 1 { cur[j] = if x[i-1] == y[j-1] { prev[j-1] + 1 } else { max(prev[j], cur[j-1]) } };
    (prev, cur) = (cur, prev) };                    -- rename two handles, no copy
  prev[len(y)]
```

**T06** (D3; single-probe upsert, `split`, and view-keyed maps are library or lifetime gaps; two probes today)
```
let text = "the cat and the hat and the bat";
let mut freq = map_new[text 't, i32](16); let mut order = buf_new(8);
for w in split_char(text, ' ') {
  let c = lookup_or(&mut freq, w, 0);               -- lib gap; one-probe upsert wanted
  if c == 0 { push(&mut order, w) };
  insert(&mut freq, w, c + 1) };
let mut out = string_new(32);
for w in &order { if len(&out) > 0 { push_byte(&mut out, b',') }; push_str(&mut out, w); ... };
println(out)
```

**T07** (D1; arm assignments under an assignment head need U3; named variants need #141)
```
let mut st = Locked; let mut passed = 0; let mut rejected = 0; let mut wasted = 0;
for e in bytes("cpppccpcp") {
  st = match (st, e) { (Locked, b'c') -> Open | (Locked, _) -> { rejected += 1; Locked }
                     | (Open, b'p') -> { passed += 1; Locked } | (Open, _) -> { wasted += 1; Open } } };
println(st, passed, rejected, wasted)                    -- Locked 3 2 1
```

**T08** (D5; the recursion is non-structural, so div or a budget; state is a pair because corpus handlers take one `mut` parameter; assigning `best` inside an answering `with` body is a hypothesis)
```
effect Memo { fn lookup(n: i64) -> i32 + 1; fn store(n: i64, l: i32) }
handler memo(mut s: Map[i64, i32] * i32): Memo = { lookup(n) = …hit → s.1 += 1…; store(n, l) = … }
fn chain(n: i64) -> i32 with Memo = if n == 1 { 1 } else match lookup(n) {
  inl l -> l | inr _ -> let l = 1 + chain(collatz(n)); store(n, l); l }
main = let cache = alloc((map_new(64), 0)); let mut best = (0, 0);
  with memo(&mut cache) { for n in 1..30 { let l = chain(n); if l > best.1 { best = (n, l) } } };
  let (m, hits) = free(cache); println(best, hits, map_len(&m))
```

**T09** (D3/D4; the bounce count is returned rather than passed as an out-parameter; records need #141; `p.x += …` is `swapField`)
```
fn step<'a>(ps: array_mut 'a P) -> i32 =
  let mut b = 0;
  for p in ps { p.x += p.v; if p.x < 0 || p.x > 100 { p.v = -p.v; p.x += 2 * p.v; b += 1 } };
  b
main = let world = [P{x: 10, v: 7}, P{x: 50, v: -3}, P{x: 99, v: 11}]; let mut bounces = 0;
  for _ in 0..50 { bounces += step(&mut world) };
  println(map_x(&world), bounces)                        -- [10, 92, 55] 11
```

**T10** (pure sugar)
```
let (mut a, mut b) = (0, 1); for _ in 0..20 { (a, b) = (b, a + b) };
let (mut x, mut y, mut z) = (1, 2, 3); for _ in 0..4 { (x, y, z) = (y, z, x) };
let (mut p, mut q) = (1071, 462); while q != 0 { (p, q) = (q, p % q) };
println(a, x, y, z, p)                                   -- 6765 2 3 1 21
```

**T11** (D1 + D4 on a carried record; #141; the old title is dropped by §12; `parse_i32` raises, so the right-hand side is computed before the field swap)
```
let mut cfg = Cfg{ width: 40, height: 25, title: string_of("untitled"), verbose: false };
let mut unknown = 0;
for a in &args { match option_of(a) { Width(v) -> cfg.width = parse_i32(v) | Title(v) -> cfg.title = string_of(v)
                                     | Verbose -> cfg.verbose = true | Other -> unknown += 1 } };
if cfg.verbose { cfg.height *= 2 };
let cfg = cfg;                                           -- frozen
println(cfg, cfg.width * cfg.height, unknown)
```

**T12** (D2 + D6)
```
fn ap(f: !(i32 => i32)) -> i32 = f(1)
fn walk(lo: i32, hi: i32, f: !(i32 => 1)) = if lo < hi { let m = (lo + hi) / 2; walk(lo, m, f); f(m); walk(m + 1, hi, f) }
main =
  let mut x = 1;
  let a = ap({ u -> x = 5; u + 1 });                     -- block: x threaded in and out → 52
  let mut sum = 0; let mut seen = buf_new(8);
  walk(0, 6, { k -> sum += k; push(&mut seen, k) });     -- block passed to its own recursion (§30)
  -- (3) stored counter: refused under D2 unless O3 adopts second-class closures; today:
  let tick = aff_counter(0, 3);                          -- Aff over its own state (D6)
  let (t1, tick) = call(tick); let (t2, tick) = call(tick); let n = close(tick);
  println(x * 10 + a, sum, seen, t1 + t2, n)             -- 52 15 [0..5] 9 6
```
In (3), the `call` rethreading is the cost of `Aff` without `aff_call_mut` sugar. `let t = { x = 5; 2 }` followed by a later force is refused by D2.

**T13** (unchanged corpus shape, `async-bank-inbox.bc`: each task owns its account cell and lends it inside itself; the Rust shape, `&mut` from outside plus reads of `txs`, is refused by R1)
```
fn teller(acct: i32, txs: …) -> i32 * i32 with Async =
  let cell = alloc(acct);
  let refused = borrow mut cell { a -> let mut r = 0;
    for t in txs { let ok = modify a { b -> if b + t < 0 { (b, false) } else { (b + t, true) } };
                   if !ok { r += 1 }; await() }; r };
  (free(cell), refused)
-- scheduler: lib/async.bc spawn_in / run_in; balances returned with the results
```
This is unverified against R1's closed-body premise, because the body names `txs`. `corpus/async-bank-inbox.bc` is the reference shape to match.

**T14** (D5. Today the buffer is passed owned in and out; after gap D3(b) is closed it can be `fill(&mut buf)`)
```
effect Rng { fn next() -> u32 }   handler lcg(mut s: u32): Rng = { next() = { s = s * 1103515245 + 12345; (s >> 16) % 100 } }
effect Logger { fn log(x: u32) }  handler logger(mut l: u32 * u32): Logger = { log(x) = { l = (l.0 + 1, l.1 + x) } }
fn fill(buf: array u32) -> array u32 with Rng, Logger =
  let mut buf = buf; for i in 0..6 { let x = next(); buf[i] = x; if x > 50 { log(x) } }; buf
main = let lg = alloc((0, 0));
  with lcg(42) { let buf = with logger(&mut lg) { fill(array_new(6, 0)) };
                 let again = next(); let (n, sum) = free(lg); println(buf, again, n, sum) }
```

## 5. #586 under the recommendation

| Issue form | Today | Under D2 |
|---|---|---|
| `let a = ap(!{ u -> x = 5; u + 1 }); x*10+a` | 12 (write lost) | 52: block threading, as `corpus/block-capability.bc` does for capabilities |
| `g(run if x == 1 { x = 5; 2 } else { 3 })` | 1102 (per the issue) | 5102: ANF, joined like #581 |
| `let t = { x = 5; 2 }; … t! …` | write lost | compile error with a suggestion |
| stored or escaping counter closure | write lost | compile error; use `Aff` (D6) or, under O3, a second-class local closure |

**Why the bug class becomes impossible.** #586 happens because the elaborator copies a `let mut` into a frame it cannot thread back out of, and the rebinding inside that frame is dead. Under D2 the elaborator decides **per assignment node** whether the node lies on a path it threads: same frame, in-place `run`, or block argument. If it does not, the node is an error. No assignment can elaborate to a dead rebinding. This is checkable as an elaborator property, and it can be pinned with corpus cases: the 52 and 5102 programs in corpus, and the stored thunk in `corpus/reject/`.

The stronger guarantee, that threading equals the cell semantics wherever it is chosen, rests on the state laws over the relation. Those laws are not yet Core theorems (proof task in §4).

Precedents: Koka accepts writes from local closures and rejects a `var` captured by an escaping closure (verified). Lean restricts reassignment to the declaring `do` block (verified). Lean 4.32 adds `do←` to let reassignments flow out through wrapper functions (seen in search results only). The Lean addition shows that pure refusal has a real ergonomic cost, which is why D2 threads through blocks rather than refusing them.

## 6. Rejected or deferred options

| Option | Status | Critic's reason |
|---|---|---|
| `let mut` elaborated as a State handler (`borrow mut (alloc e)` over its scope), with lowering chosen between fold and slot by `handle_fold` | Rejected as elaboration (kept as theory) | Does not type around `await`/`yield`/B2 `while` (T1, Row.Unwind). `handle_fold` is a one-way `Steps` fact on one cell and relates no cell program to SSA. Register promotion would be an unbuilt pass with no law (against the no-workaround rule). Capabilities are themselves threaded the way `let mut` is, so nothing is removed. |
| `prev <-> cur` as `modify` over another instance | Rejected | An operation inside a `withswap` `!` callback is not provided (§18). |
| Dropping the `mut` marker (MVS, Places) | Rejected | Removes enforced local reasoning (rustc enforces `mut`). Makes every capture a stale-read hazard (`let x = 1; f = !{_ -> x}; x = 2; f()` gives 1). |
| `inout` parameters, `once(..) + 'c`, `&mut self`-style `object` declarations with dot autoref | Rejected as surface | Swift/Hylo/Rust surface. Dot collides with §38 `n.op(v)`. The (K) "objects" are existing handlers plus records, with no ν-η privacy law. |
| Copy-in/copy-out as an equivalence (L1) | Rejected as stated | Fails under abort: value threading drops `x` on `raise`. Now open choice O5. |
| Mandatory `carry` heads on loops | Deferred | Frame rule forbids the mixed bind/assign tuples its own examples use. Undecided whether the body value or its assignments give the next state. `break e` with linear carried state is unaddressed. #493 is already fixed by U3. |
| Step-synchronous `next` with staged place writes | Rejected (scalar `carry`/`next` stays an option) | Staging extends place borrows past `yield` (T1). It is inconsistent with in-place inner-loop writes without a copy. A `next` through a captured lend has no step to land at. |
| Promoting a closure-assigned `let mut` to `alloc` + lexical `mut` lend with `once`/`aff` closures | Deferred | Needs mode-carrying closure literals and retyping of every `!(A => B)` HOF in lib. A let-bound thunk is refused under lexical lends (`lendLet`). §32 block threading is cheaper for the non-escaping case. |
| Fold-combinator pipelines (`folds`, `count`, `position`, …) as the primary form | Deferred to library | Banana-split is ill-typed for linear sources. There is no sized `scan`. Adapters over borrowed views are §7 Open. |
| Generator cursor holding a lend across `yield` (T03) | Rejected | T1 (#172), or R1 under PinLaw with a closed body. |
| `pull X 0 X` with a `close` that returns its carry | Rejected | Not producible; close answers R = 1 (§15). `Aff` already covers this (D6). |
| `entry_or` returning `(map, mut slot)` | Rejected | The owner cannot be moved while lent. |
| Inout address ABI for large value-threaded records | Deferred | Needed only if large records are value-threaded. Unbuilt. |

## 7. Prior art that shaped the recommendation

**Verified this session:**
- Koka book §3.2.4 "Local Mutable Variables". `var` is implemented with a state handler. A `local<h>` row appears on closures that assign a var. An escaping var closure is a type error. Vars are "not quite first-class and we cannot pass them as parameters".
- Ullrich & de Moura, "'do' Unchained", ICFP 2022. `let mut` as a local StateT. Reassignment is restricted to the declaring `do` block.
- Swift SE-0176, exclusive access to memory. Instantaneous versus non-instantaneous accesses. Escaping captures get dynamic enforcement.
- Futhark loop expressions: `loop (x, y) = (1, 1) for …`. Simultaneous loop state; T10 is Futhark's own example.
- Roc: `var $x` reassignable only in the declaring function; callbacks cannot reassign it.
- Effekt tour, "Mutable Variables": vars are stack-allocated. The region and capture-set claims are **unverified**.
- Muhcu, Schuster, Steuwer, Brachthäuser, "Multiple Resumptions and Local Mutable State, Directly", PACMPL 9 (ICFP 2025). Local `var` semantics under handlers is subtle. Not relevant to us beyond that, because multi-shot is ignored.
- Brachthäuser, Schuster, Ostermann, "Effects as Capabilities", OOPSLA 2020. Handlers as second-class capabilities; the model for D5.
- Bourke et al., Vélus (PLDI 2017). Precedent for proving a loop-state desugaring adequate.
- Racordon et al., arXiv 2106.12678, title and authors only. The copy-in/copy-out reading of it is **unverified**.

**Unverified:**
- Lean v4.32.0 `do←` (search snippet only).
- Plotkin & Power's equation list for state.
- Staton, LICS 2013, instances (abstract only).
- Meijer, Fokkinga & Paterson for banana-split.
- Marshall, Vollmer & Orchard, "Linearity and Uniqueness" (ESOP 2022): uniqueness is a fact about the past, which is why in-place update relies on handles never being persistent.
- Downen et al., "Codata in Action".
- SE-0035 (the MVS critic did not fetch it).
- Hylo subscripts and inout.

**In-repo (read this session by the agents):** SPEC §9, §11, §14, §15, §16, §18, §19, §21, §22, §29, §30, §32, §35, §38; docs/ergonomics.md (A4, N1–N12); docs/loops.md; docs/compiler.md §3.2–3.3; docs/fnmut.md; corpus/block-capability.bc; corpus/aff-counter.bc; corpus/reject/lend-div-two.bc; corpus/pending/async-bank.bc; corpus/counts.expected.

## 8. Open choices for the user

| # | Choice | Options | Recommendation |
|---|---|---|---|
| O1 | The binder | (a) keep `let mut`; (b) respell it in our own words; (c) drop the marker | Keep **a** marker (it is enforced local reasoning). Its meaning becomes "a threaded local under D2". Spelling deferred. |
| O2 | How loop state is declared | (a) inferred, as today, with U3; (b) optional `carry` head; (c) mandatory `carry` | (a) now. Revisit (b) after U4 gives loops values. |
| O3 | A let-bound closure that writes a captured local | (a) refuse (Lean, Roc); (b) second-class local closure, callable as a block in scope and refused if stored or returned (Koka); (c) promote to cell + `Aff` | (a) now with an `Aff` hint. (b) as the next elaborator rule; it needs a SPEC entry. |
| O4 | Method-call syntax over a `&mut` first argument | (a) none, keep `f(&mut x)`; (b) `x.m()` with a resolution rule against §38; (c) `|>` | Defer to the data-declarations work, where "methods are codata" will be decided. |
| O5 | A value lent by A4 when the callee raises | (a) dropped (value threading); (b) kept (cell) | Decide before extending A4. (b) matches Rust/Swift and the "errors are one model" rule. |
| O6 | Reads through a `mut` view | (a) library `peek` (two swaps); (b) a kernel read / imm-of-mut reborrow with a SPEC entry and proof | (b). It is the main cost gap for C7/C10, but it is a borrow-calculus change and must be proved first. |
| O7 | §18 not-provided rows (`&mut` in a capability-threading call; capability through `for … in &a`) | lift / keep | Lift. They block the service-injection shape (T04, T09, T14) that the k8s north star needs. |
| O8 | The one-borrow limit on looping callees (lend-div-two) | accept / lift via the spanning lend K1 (#172) | Accept for now and document it. Lifting it is borrow-calculus work. |
| O9 | Hidden-state objects | (a) answering handlers for injected services plus `Aff` for escaping state; (b) an `object` declaration over ν | (a) now. Revisit (b) with records (#141) and "methods are codata". |

---

## Completeness critique

The draft is right that no single mechanism replaces `let mut`. Five gaps should change what it recommends: G1, G2, G4, G5 and G7.

**Gaps that change the recommendation**

**G1. Issue #504 contradicts "freezing by shadowing".**
- Issue #504 is open. In `let mut n = 0; let n = 10; n = n + 1`, the assignment is accepted and updates the outer `mut` binding. The program prints 11, and 13 when the shadowing sits inside a loop.
- So `let cfg = cfg` freezes nothing today. A later `cfg.height *= 2` would still go through to the mutable binding. That is a silent wrong answer, the same kind of bug as #586.
- Fix: D2's "threaded or refused, never dropped" invariant should also cover name resolution. An assignment must resolve to the binding in scope, never to one behind a shadowing binding.
- Cite #504 as part of D2, and as a precondition for the freezing item in §1 and for T11. As drafted, T11 is wrong whenever an assignment follows the shadowing.

**G2. Writes that come before a `raise` or abort are missing from D2.**
- D2's table has no row for an assignment inside a `with h { … }` body whose handler aborts (`to_result`, `default`, `Fail[DivError]`), or inside a `for` that a raise leaves by its exit.
- The comment in `corpus/div-recover.bc` says "the unwind drops the buffer built so far" (SPEC §19). If `x` is threaded through such a body, then in `let mut seen = 0; with to_result { …seen += 1; raise… }; seen` the increments are lost on the abort path. Cell semantics would keep them.
- The draft raises this only for A4 calls (D3(d), O5), but the same question applies to every `let mut` threaded through any body that can abort. I have not run it; whether today's elaborator loses the write is unverified.
- Fix: add an abort column to D2's table: joined on the abort edge, refused, or documented as dropped. Add a corpus case for it.
- This matters because errors are one model (raise plus handlers), so this shape will be common. It is the next #586.

**G3. Two places that already thread state are missing from D2's table.**
- SPEC §15 (line ~1815) already threads the locals a `for x in g(e)` body assigns through the operation (`w <- perform[n.0] (v, w)`).
- SPEC line ~1981 does the same for "callbacks that yield": a block takes the loop's threaded variables.
- §14 (line ~1607) does it for borrow blocks whose body loops.
- These are working instances of D2's "thread in and out" rule, and #586 is the case where that threading is missing. Adding them would turn D2's "Hypothesis: it is the same derivation" into "the rule §15 and §32 already apply". The draft names neither.
- Fix: add the rows to the table and cite `corpus/yield-callback.bc` and `corpus/block-yield-inner.bc`.
- The draft also has no mutation category for writes inside a generator body that a generator still holds across `yield` (the stored-codata case). Under D2's escape rule these should be refused, and the draft should say so.

**G4. Interior mutability is missing as a paradigm (#119, and the user's codata suggestion).**
- Issue #119 is an open design: branded indices into a region owned by a handler, with `get`/`set` as operations. It is Rust's `Cell` discipline enforced at the effect boundary, compiled to base plus offset.
- The context says the user just suggested interior mutability via codata. The draft treats "codata objects" only as a fit-matrix column and defers it in O9. It never evaluates #119 or a codata-cell design against T08, T12(3) or T14.
- This is the strongest candidate for "a more natural way than `let mut`" for shared, hidden state: memo tables, loggers, counters captured by stored closures. Today the draft sends that state to `Aff` plus call rethreading, which is visibly worse in T12(3).
- Fix: add a column (region cells or codata cells), with #119's laws (copy-in/copy-out, no interior reference) and the Kripke region-length invariant. Then re-grade T08, T12(3) and T14.
- Per the user's standing direction, interior mutability is still open, so present this as an option with trade-offs, not as rejected.

**G5. The draft re-proposes work already filed as issues.**
- D3 and gap (a) are #582 (E1, N1: "borrowing a `let mut` value outside a call … a cell scoped to the lend"; `docs/ergonomics.md` line 196). #582's acceptance already measures 66 sites against a hypothesis of 41.
- The `+=`, mut-parameter and `*m = e` items are #583 (E2: N2, N3, N9).
- O6, the imm-of-mut reborrow, is #174 (`axWithborMITy`), an open theory issue with recorded partial results (anti-frame plus `wpTS_I_frameX`). Those results say "does not compose as stated", which is the obligation the draft calls "must be proved first".
- Fix: cite these issues in place of the new numbering, so nothing gets filed twice. Restate D3 as "land #582, then measure". O6's cost estimate should cite #174's partial results.

**G6. Threads and parallelism are left out.**
- The draft has no category for mutation across threads.
- #212 (fork-join) depends on exactly the distinctions in play here. `Imm` gives Sync for free, owned values give Send for free, and "only handler-owned state and capabilities … need explicit thread safety". It also proposes a "parallel-safe row" predicate.
- D5 (state in handlers) and the #119 option both decide what `par_for` can capture.
- The user's standing rule is that threads are required, so designs must keep the door open.
- Fix: for each of D1–D7, add a line saying whether it stays parallel-safe. D1 and D3 (disjoint `mut`, `split_at_mut`) do. D5, a `Mut`-borrowed service, does not without a lock- or actor-backed handler.
- This is a constraint on D5, not a change to the recommendation.

**G7. #586's `run` arm still has no rule for linear values.**
- D2 turns every in-place `run` into ANF and joins it. The draft never says what happens when the `let mut` holds a linear value (a buffer, a `mut` view) and the run is in a head of an `if`/`match` whose other arm does not consume it.
- That is the frame-rule problem the draft itself raises against `carry` heads, and it stays open for D2.
- Fix: state the join rule for linear threaded values in heads, and add a test with `push(&mut buf, …)` in one arm only.

**Smaller gaps**

- **G8. Paradigms not considered.** The draft never cites these, though each argues for D1/D2 or against them:
  - ST-style local state with a rank-2 escape check (Launchbury–Peyton Jones, unverified). It is the closest prior art to D2's escape refusal and to #119's brand. The brand `'x` from `withbor` already plays the rank-2 role.
  - Wadler's `let!` (unverified). It is a precedent for the imm-of-mut reborrow in O6.
  - Granule graded state or graded uniqueness (unverified). Memory says grades should follow Granule.
  - Tofte–Talpin regions (unverified), relevant to #119 and arenas.
- **G9. Swap of two places has no design.** The draft covers `mem::swap` of locals by tuple assignment. Swapping two places, such as two fields of a borrowed record, or two elements of different arrays (Rust's `mem::swap(&mut a[i], &mut b[j])`), needs `withborF2` (SPEC §5) plus `swap`. `mem::replace` and `take` through `mut` are also missing. Add a row to D4.
- **G10. Mutating a borrowed record's field needs a precondition.** D4 uses `swapField`, but SPEC §5 says projecting one field of a borrowed record drops the other fields' views, which must be `Affine`, and that "variants in place" is open (`Ref` does not distribute over `⊕`). So `p.v = -p.v` in T09 is only safe for all-affine field types, and assigning a variant field through `mut` is not available today. Grade T09 and T11 against this.
- **G11. Finalisers and cancel.** Finalisers may perform operations (SPEC §27, cancel rows). The draft does not say whether a `let mut` assigned before a generator's `close`, or before `break` cancels the continuation (SPEC line 1823), is seen by its finaliser, or by code after the loop. One D2 row is needed.
- **G12. Unchecked claims.**
  - "149 of 177 sites with the same output" is not in the repo. #582's 66/41 figures are, so reconcile the two.
  - The 68 vs 241 count of `let mut x = x` is admitted unreconciled, yet C16 is called "the largest available win". Settle the count first.
  - The census leaves out `lib/*.bc` (`async.bc` 36, `float.bc` 48, `map.bc` 21 `let mut`). Library code is where C7 and C14 mutation concentrates.
  - D3's "for an owned array passed to a call, `slice_borrow_mut`" is not checked against ergonomics M4 ("the parameter type chooses container or elements"), which #582 fixes as choice 2.
- **G13. Test programs not run.**
  - None of T01–T14 was elaborated or run. Several comments state outputs ("-- 220 3 10", "-- Locked 3 2 1") that were not checked, so mark them expected and unverified.
  - T13's body names `txs`, which may break R1's closed-body premise. The draft says so but still lists it under the recommendation.
  - T04 uses `len_of(v)` in a `for` bound, which needs #174.
  - No program covers G2 (a write before a raise) or G1 (shadowing).
- **G14. Small drifts from the user's rules.**
  - D2's error message suggests "put the state in a cell / `Aff`". A cell needs `alloc`, which is an effect, so check that the hint does not push programs into allocation where Rust would not allocate (the zero-cost target).
  - O5's recommendation (b), keeping the value on raise, is a semantics change to A4 that the draft calls "the critic's reading". It must come from SPEC §11, not from a critic.

**Effect on the recommendation**

- **G1:** drop "freezing by shadowing" or make it depend on fixing #504, and add name resolution to D2.
- **G2:** add an abort column to D2. Without it, D2 does not deliver "every assignment is threaded or refused, never dropped".
- **G4:** O9 and T12(3) should weigh #119 or a codata cell as a real option, not defer it.
- **G5:** rebase D3, O6 and the sugar list on #582, #583 and #174.
- **G7:** add the linear-value join rule.

G3 strengthens D2's evidence and G6 adds a constraint. The rest are corrections and missing citations.