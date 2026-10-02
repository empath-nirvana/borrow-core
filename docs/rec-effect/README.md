# Recursion as an effect: a design corpus

> **Revised (SPEC §21, decision 59).** The design below made each self-reference a `rec` operation
> and layers handlers that intercept it. As built now, a recursive group is the bounded fixed point
> of its generator, called directly: a self-call is a direct call of the self-reference the
> generator is given, with no `rec` operation and no site, and a layer is a transformer of the
> generator, applied before the fixed point (`with L { … }`). The environment a step needs
> (capabilities, a layer's state) is passed in its argument, as §3.2's finding 5 found it must be
> (`rec : !(S * A => S * B)`, the `FnMut` row). The `rec` site was what blocked an operation that
> resumes, an answering capability and members with different result types in a recursion
> (`docs/second-class-and-system-c.md`). The drivers (`bounded`, `deep`) and `Exhausted` are as
> `bounded-deep.md` describes. The corpus and the lowerings below stand as the record of what was
> explored.

Status: design work for PR #133. Nothing here changes SPEC, the kernel, the checker, the compiler
or `lib/`. It has two parts:

- **The target corpus** (`*.rec`): programs written the intended way, with provisional spellings
  (§2). Each file also gives the intended elaboration into `rec`, a driver and layers, the
  totality and stack behaviour, and what the checker should report.
- **Hand-lowerings** (`NN-*.bc`): each program written in today's language, so we can see what
  the mechanism costs and where it breaks. `run.sh` checks each one, compiles it to WebAssembly,
  runs it under wasmtime (`bcc run`) and counts it (`bcc-counts`). A program marked
  `-- expect: rejected` or `-- expect: fails` records a refusal or a failure, quoted in §5. The
  hand-lowered recursion effect itself is `rec.bc`, which `run.sh` puts in front of each
  program that says `-- uses: rec.bc`.

`run.sh` is outside the CI gate, like `docs/iteration-examples/run.sh`. It takes about a minute.
The counts in §4 are its output. Two notes on the counts:

- Where a program is marked `counts-at`, it was counted at a smaller size. At full size,
  `bcc-counts`'s flat-IR interpreter overflows Lean's stack (observed on 03 at n = 10⁶: "Stack
  overflow detected. Aborting."), although wasmtime runs the program.
- The source interpreter (`bcc interp`) is not run by default. It took about 50 s on
  `01-fib-deep.bc` at fib(15), 4000 observations; the compiled run takes 0.03 s.

Contents: §1 the decided design · §2 the provisional surface · §3 the mechanism as lowered · §4
the programs · §5 what was refused or failed, quoted · §6 requirements the corpus puts on the
mechanism · §7 what `for` needs from the mechanism · §8 where layers attach, and where implicit
`rec` is ambiguous · §9 what I have not established.

---

## 1. The design, as decided

These points were given by the user, and the corpus is built to them:

- **Recursion is an effect.** A self-reference is `rec`, and it is implicit: `fib(n - 1)` in
  `fib`'s body is a `rec`.
  - A definition yields its open step (for layering) and a closed default driven by `fix`.
  - A mutually recursive group shares one `rec`.
  - There is no `perform`: an operation is a call on a capability.
- **Drivers and layers.**
  - `fix` is the one driving handler, and it is div.
  - Layers intercept `rec` and never drive it. `memo(cache)`: a hit answers; a miss forwards to
    the outer handler, stores the answer, then answers. `fuel(n)`: counts, and fails visibly
    after n.
  - Layers compose with `|>`, innermost first: `fib |> memo(cache) |> fuel(1000) |> fix`.
- **Loops are the same mechanism.** A loop is `rec` in tail position: the continuation is used
  once, immediately, so it compiles to a jump. General recursion is `rec` in non-tail position:
  continuations are pending, so there is a stack.
- **The driver sets totality.** `fix` is div. Fuel taken from a source's bound is total. `fuel(n)`
  is total, and "ran out" is visible.
- **`for` is the familiar special case**, desugared as in Rust: `into_iter`, then a loop over
  `next`, with `break`, `continue` and `return`.
- **Stack behaviour is a choice of driver**, not a limit of the language:
  - `fix` uses the host stack: fast, and depth-limited;
  - a deep driver keeps the pending continuations on its own growable stack, and pays an alloc
    effect;
  - a tabulating driver fills the memo bottom-up, so no call is deep.
- **Effects in bodies escape by forwarding.** Capabilities are arguments, and the lowering is
  chosen by specialisation.
- **No map type exists yet.** A dense key (node ids, grid cells, fib's n) uses an array. A sparse
  key is written against a map *effect* (`get`/`insert`, handled by a map handler).

## 2. The provisional surface

Every spelling below is provisional. None of them is a proposal to fix syntax.

| form | meaning |
|---|---|
| `fn f(x) = … f(y) …` | `f(y)` in `f`'s own body (or its group's) is `rec(y)` |
| `f(x)` elsewhere | the closed default, `(f |> fix)(x)` |
| `f |> L1 |> L2 |> D` | open step `f`, layers `L1` (innermost), `L2`, then driver `D`; the result is callable |
| `fix` | driver: host stack, div |
| `deep` | driver: heap frames, stack-safe, div, allocates per non-tail call |
| `fuel(n)` | layer counting `rec`; adjacent to the driver, a total driver (§6 R7) |
| `memo(&mut c)`, `memo(&mut c, key = x)` | layer; `c` an array for a dense key, a map capability for a sparse one |
| `group(f |> L, g |> L') |> D` | a mutually recursive group with per-member layers; `ev.f(x)` calls a member |
| `for x in y { … } else { … }` | Rust's desugaring; `else` is the value when the source ends (Zig) |
| `e.fail(v)` / `try { e -> … }` | an operation on a `Fail` capability, and its handler |
| `handle_map { m -> … }` | a map handler; `m.get(k)`, `m.insert(k, v)` |
| `never` | the empty type, the "ended" value of a source that cannot end |

## 3. The mechanism, as lowered today

### 3.1 The machine and the deep driver (`rec.bc`)

A recursive definition is lowered to a **machine**: two persistent functions over a state `S`.

    start  : !(S * A => S * Out)          run a call on the argument a
    resume : !(S * (K * B) => S * Out)    resume a pending frame k with the answer b
    Out = B + ((A * (K + 1)) + Z)         answer b | rec(a) with frame k | rec(a) in tail position | stop z

The pieces:

- **Frames.** `K` is the defunctionalised continuation. Each non-tail `rec` site has a variant,
  holding the variables live there. A `for` or `while` whose body performs `rec` puts its cursor
  and state in the frame (09, 14).
- **Tail calls.** A tail `rec` carries no frame.
- **Stopping.** `Z` stops the whole recursion. An error effect that does not resume, and fuel
  running out, both use it.
- **The `deep` driver** is library code over `unfold` (SPEC §7), like `div_bind`. It is a loop
  whose state is `S`, the next action (a call, or an answer to give back), and the pending
  frames as an owned list.
  - Each observation is one `start` or one `resume`.
  - A tail call pushes nothing.
  - Each non-tail call allocates one list cell.
  - It is div. `deep_fuel` is the same loop under `div_fuel`, which is total.

**Layers are machine transformers.** A layer takes the inner machine and returns one with its
own state, frames and requests added. It does not drive.

- `memo` has state `C * S` and requests `A + A`: `inl a` looks up, `inr a` runs the inner
  machine. Its frames are `K + A`, where `inr a` means "store for `a`, then answer". A miss
  becomes `rec(inr a)` with the store frame. That is "forward to the outer handler, store,
  answer", with the store as memo's own continuation.
- `fuel` has state `i32 * S` and stops with `1 + Z`.
- A stop from the inner machine passes through both layers unchanged.

### 3.2 The open form on the host stack (Cook-style), and where it breaks

The task's first encoding was a step that takes the recursive call as an argument
(`rec : !(A => B)`), with `fix` to tie the knot and layers written as step → step functions
(02, 04, 05, 06, 07). What was observed:

1. **`fix` cannot tie the knot.**
   - A `fn` does not see its own name (30).
   - The self-applicable type is refused: "the type variable `X` occurs under `U`" (31).

   What can be built is the fixed point **unrolled to a depth `d`**: `count_fold` applies the
   step `d` times to a bottom that always runs out. This `fix` is total, with depth as its fuel,
   and each `rec` is a native call.
2. **The host stack bounds the depth.** 04 (fib with memo) runs at n = 3000. At 3500, and at
   10⁶ (05), it fails with "wasm trap: call stack exhausted".
3. **Unrolling costs more than it should.** At depth 3000, 04 makes 4 504 501 allocations, which
   is (n + 1)(n + 2)/2 at n = 3000, with 2999 copies and 5999 dispatched calls. `--sites` reports "recursive-types
   1 [2]": each level is a closure whose environment holds the level below. I have not
   established why the growth is quadratic. The copies column suggests that copying a level
   copies the chain beneath it.
4. **"Ran out" is passed on by hand** at every call site, because there is no exit effect.
5. **A stateful layer cannot capture its state** (07): "`!thunk` promotes only over `!` types,
   but `c`, of type `array i32`, is used inside". A linear closure could hold the cache, but
   could be called only once. The state is threaded instead: `rec : !(S * A => S * B)`, with
   the step generic in `S` so that a layer can add its component. This is the `FnMut` row of
   SPEC §2's closure table.
6. **Tabulation is the cheap case.** When every call is at most 2 deep (06, `for i in 0..=n`
   over a memo filled bottom-up), the unrolled fixed point has constant depth 3 and is known
   statically. At n = 10⁶ it is total and makes 1 allocation (the table) and 0 dispatched calls.

### 3.3 Drivers of one definition

The same fib definition under each driver:

| driver | program | n | host stack | allocations | totality |
|---|---|---|---|---|---|
| deep, no memo | 01 | 15 | constant | 1972 (a frame per non-tail call) | div |
| host (unrolled), no memo | 02 | 15 | depth n | 6568 | total (depth fuel) |
| deep + memo | 03 | 10⁶ | constant | 3 per level (30 000 at 10⁴) | div |
| host + memo | 04 | 3000 | depth n | 4 504 501 | total (depth fuel) |
| host + memo | 05 | 10⁶ | exhausted | — | — |
| tabulate + memo | 06 | 10⁶ | ≤ 3 | 1 | total |

## 4. The programs

"Runs" means it checks, runs under wasmtime and gives the stated answer with `live 0`. The counts
are `allocs / indirect (dispatched) / copies`, from `run.sh`.

| program (`.rec`) | surface form | elaboration | driver | layers | totality | stack | runs today? how | counts | blocker (observed) |
|---|---|---|---|---|---|---|---|---|---|
| fib (fib.rec) | `fib(n-1) + fib(n-2)` | 2 non-tail `rec`; frames `n`, `x` | fix | — | div | host, depth n | 01 under `deep`; 02 unrolled open form | 1972/0/0; 6568/1979/991 | 30: self-call refused; 31: knot refused |
| fib memo, deep (fib.rec) | `fib |> memo(&mut c) |> deep` | + store frame per miss | deep | memo | div | heap | 03, n = 10⁶ | 30000/0/0 at 10⁴ | none |
| fib memo, host (fib.rec) | `… |> fix` | open form, state threaded | fix | memo | div (as lowered: total) | host, depth n | 04 at 3000; 05 at 10⁶ fails | 4504501/5999/2999 | stack exhausted at 3500 |
| fib tabulated (fib.rec) | `for i in 0..=n { f(i) }` | memo filled bottom-up | fix, depth ≤ 3 | memo | total | ≤ 3 | 06, n = 10⁶ | 1/0/0 at 10⁴ | none |
| memo capturing its cache | `memo(c)` as a closure | — | — | memo | — | — | rejected (07) | — | F5 |
| grid paths DP (grid-paths.rec) | `paths(g, cell+w) + paths(g, cell+1)` | 2 non-tail `rec`; `g` invariant, lent per step | fix | memo, key = cell | div | host, depth w+h | 08 under `deep` | 350/0/0 | none |
| DFS (dfs.rec) | `for w in nbrs(v) { n = n + dfs(w) }` | `rec` in a `for` body; frame (v, cursor, n) | fix | — | div | host, DFS depth | 09 under `deep` | 9/0/0 | none |
| BFS (bfs.rec) | `while let v = q.pop() { for w … }` | tail `rec` only | fix, or fuel from `0..n` | — | div / total | constant | 10 as `count_fold` over n | 4/0/0 | no `break` in `count_fold` (F6) |
| owned tree (tree.rec) | `sum(l) + v + sum(r)` | 2 non-tail `rec`; frame holds owned subtree | fix / deep | — | div (structural: could be total) | heap under deep | 11: deep at depth 10⁵; `fold_own` at 10³ | 12000/0/0 at 10³ | `fold_own` on a tree exhausts the stack at 10⁵ |
| borrowed tree (tree.rec) | `sum(&l) + *v + sum(&r)` | request `&Tree`; needs the children's views at `'a` | fix | — | — | — | 12 via `fold_imm` (not `rec`); 13 rejected | 12001/0/0 | 13: `unroll` of a view refused |
| parser + error (parser.rec) | expr/term/factor; `e.fail(pos)` | one group; loop accumulators in frames; `Stop` | fix | — | div | host, nesting depth | 14 under `deep` | 21/0/0 | none |
| Intcode (intcode.rec) | `run(mem, pc')` in tail position | tail `rec` only, no frame | fix; fuel | fuel | div; total | constant | 15 `deep`, `deep_fuel` | 3/0/0 | none |
| even/odd (even-odd.rec) | `n == 0 \|\| odd(n-1)` | one group, tail `rec` only | fix | — | div | constant | 16, n = 10⁵ | 0/0/0 | none |
| even/odd memo (even-odd.rec) | `group(even |> memo(ce), odd |> memo(co))` | per-member memo; tail calls become non-tail | fix | memo ×2 | div | depth = misses | 17, n = 10⁴ | 20004/0/0 | none |
| while (while.rec) | `while n != 1 { … }` | tail `rec` | fix; fuel | fuel | div; total | constant | 18 as a generator drain; `div_fuel` | 0/0/0 | 19: `while` only in `gen fn` |
| for over data (for-data.rec) | `for i in 0..10`, `for x in &a`, view, `&mut a`, `break` | fuel from length | fuel(len) | — | total | constant | 20 as `count_fold` | 1/0/0 | no early exit (F6); lifetime-generic step needs a closure |
| for over an owned list (for-list.rec) | `for x in l` in order | tail `rec` on the rest | fuel(size) | — | total (intended) | constant | 21: loop under `deep` (div); `fold_own` reversed; `fold_own` into closures | 16/5/0 | no in-order total descent (C2) |
| for over a generator + break (for-gen.rec) | `for d in digits(n) { … break e }` | pull; tail `rec` | fix | — | div | constant | 22, as written | 0/0/0 | 22b: `break <arith>` internal error |
| never-ending source (never-ends.rec) | `for i in naturals() { … break t }` | value = break type | fix | — | div | constant | 23 with a dummy finishing value | 0/0/0 | 24: no way to end a body at `0` |
| for over stdin lines (for-stdin.rec) | `for l in lines(&mut stdin) { … }; print` | pull, effectful `next` | fix | — | div | constant | 25, as written with `lines` | 14/0/0 | none |
| fuel, "ran out" (fuel.rec) | `ack |> fuel(f) |> fix` | fuel layer; 1 non-tail `rec` | fuel+fix | fuel | total | heap under deep | 26 (layer inside `deep_fuel`) | 529/0/0 | 27: layer under `deep` is not total |
| sparse-key DP (collatz-map.rec) | `clen |> memo(map) |> fuel |> fix` | memo over a map capability | fuel+fix | memo, fuel | total | heap | 28 with an association list | 12617/6267/0 | no map; list look-up allocates per entry |
| continuation as closure | `Out = μX. B + A × U(B ⊸ F X)` | — | — | — | — | — | rejected (29) | — | `X` under `U` |

## 5. What was refused or failed, quoted

Each entry is an observed checker error or run failure. Line numbers are those `run.sh` prints.

| program | observed |
|---|---|
| 30-self-call | `unknown variable \`fib\`` |
| 31-knot | `the type variable \`X\` occurs under \`U\` (inside a computation type)` — `type Self = mu X. !(X => i32)` |
| 29-continuation-closure | the same message, for `mu X. i32 + (i32 * U (i32 -o F X))` |
| 07-memo-capture | `` `!thunk` promotes only over `!` types, but `c`, of type `array i32`, is used inside `` |
| 05-fib-memo-host-deep | `wasm trap: call stack exhausted` (also at n = 3500; n = 3000 runs) |
| 11 (`fold_own` at depth 10⁵, before it was reduced to 10³) | `wasm trap: call stack exhausted`; `--sites`: `owned-folds reversed 0 recursive 1` |
| 13-tree-borrowed-rec | `` `unroll V` needs `V : mu X. A`, but `V : imm 'x (mu X. 1 + X * i32 * X)` `` |
| 19-while-in-fn | `` `while` is a generator's loop: it may appear only in the body of a `gen fn` `` |
| 22b-break-arith | `internal error: a surface form was not elaborated before checking` at `break 0 - 1 - i` (a bug; binding the value by `let` first checks) |
| 24-never-ends-empty | `` type mismatch: expected `0`, but this has type `i32` `` |
| 27-fuel-layer-not-total | `` `ack_fuel` is declared `total`, but it calls a div function (SPEC §14) `` |
| 02 (while writing it) | `` `i` is not consumed in its scope, and it cannot be dropped where its scope ends `` — promoting a `!` closure in a function whose `i : i32` parameter is live; the promotion was moved to its own function |
| 14, 26 (while writing them) | `a pair is checked against \`i32\`, which is not a \`*\` type` — `deep`'s type arguments were not inferred when `A` is a pair; they are written |
| 20 (while writing it) | `` type mismatch: expected `!(i32 * array_imm 'x i32 * i32 => …)`, but this has type `!(all 'l1 < top. …)` `` — a lifetime-generic step passed to `count_fold`; wrapped in a closure |
| rec.bc (while writing it) | `` the type `A` of `fix_obs` is not determined by its arguments `` — a generic `fn` called from a generic `def` at the def's type variables; the driver's observation is written as a core `def` instead |
| 03 counted at 10⁶ | `bcc-counts`: `Stack overflow detected. Aborting.` (Lean; wasmtime runs it) |

## 6. Requirements the corpus puts on the mechanism

Each requirement is traced to the programs that force it.

**R1. Continuations of non-tail `rec` are data (defunctionalised frames), made by the
elaborator.**

- Forced by: every non-tail program (01, 03, 08, 09, 11, 14, 17, 26, 28).
- A continuation cannot be a closure. Its type occurs under `U` in its own definition (29).
- The frame is exactly the variables live at the `rec` site. That is what SPEC §15's "one state
  machine per body" already computes for loops and direct-style div calls. `rec` adds one kind
  of resumption point, whose continuation is pushed rather than held.

**R2. State in layers is threaded, not captured.**

- Forced by: 03, 04, 06, 08, 17, 28 (memo); 26 (fuel's counter).
- A layer is `!` code, since it runs at every `rec`. F5 forbids capturing the cache (07).
- The layered step's state is the product of the layers' states: `memo` adds `C`, `fuel` adds
  `i32`. The inner step is generic in the state it threads (04), or peels its own component
  (`rec.bc`).
- The same holds for loop-invariant arguments that are not keys:
  - the grid in 08, the graph in 09 and the input in 14 are machine state, lent `imm` per step;
  - the visited set in 09 and the memory in 15 are lent `mut` per step.

  This is the per-observation lend of SPEC §14, done by hand. The elaborator could do it for
  any argument that every `rec` passes unchanged.

**R3. Deep non-tail recursion needs a driver with its own stack, and the choice of driver must
be free per use.**

- Forced by: 03 (fib at 10⁶), 05 (the same on the host stack fails), 11 (a tree 10⁵ deep).
- `deep` keeps frames on the heap:
  - one allocation per non-tail call;
  - a tail call pushes nothing (15, 16);
  - constant host stack.
- `fix` on the host stack is depth-limited: about 3000 levels for 04's step. `fold_own` on a
  tree and `fold_imm` on anything keep native frames (Backend/README.md, Stack).
- Tabulation (06) is the third driver. It has depth ≤ 3, is total, and allocates nothing
  beyond the table. Its depth bound is written by hand. A checker cannot see that the table
  makes every call a hit.
- `deep`'s allocation is the driver's alloc effect. Whether it should be one allocation per
  frame (a list cell, as lowered) or a growable array of frames is open (§9).

**R4. Memo turns tail calls into non-tail calls.**

- Forced by: 17 against 16.
- A memoised tail-recursive group needs a store frame per miss. The stack is then as deep as the
  chain of misses: 20 004 allocations at n = 10⁴, against 0 without memo.
- fib has no tail call, so it loses nothing (03).
- A checker report should say this when memo is layered on a tail-recursive definition.

**R5. Memo keys: which arguments.**

- Forced by: 08. The grid is an argument of every call, but only `cell` is the key. 17's key is
  the member and n.
- A borrowed argument cannot be a key. A key must be copyable and comparable (and hashable, for
  a map).

**R6. A map, as an effect or a type.**

- Forced by: 28, where the Collatz values are sparse.
- Dense keys use an array: 03, 06, 08, 09, 10, 17.
- The lowering uses an association list threaded as state. A look-up must rebuild the list,
  because `fold_own` consumes it. Its algebra cannot capture the key (F5, #9), so the list is
  folded into a function of the key, one closure per entry per look-up: 12 617 allocations and
  6267 dispatched calls for 29 starts.
- A map capability (`get`/`insert`) whose handler owns the storage would remove all of that.
  So would #9, partly.

**R7. Totality comes from the driver, not from a layer.**

- Forced by: 26 and 27, 15, 18, 20, 28.
- A fuel layer under a div driver counts and stops visibly, but the definition stays div (27).
  Fuel counted by the driver is total: `deep_fuel`, `div_fuel` (15, 18, 26, 28).
- So `fuel(n) |> fix` must elaborate to one fuelled driver when the two are adjacent. With other
  layers between them, it still must, if the fuel layer is outermost.
- As lowered, the layer's count of calls and the driver's count of observations differ. Each
  call is at most 2 observations, so a driver with 2n + 2 observations never cuts off before the
  layer does. The driver's own "ran out" is then unreachable, but still in the type (26).

**R8. Structural recursion is total by size, if the checker sees the descent.**

- Forced by: 11 (owned tree), 21 (owned list in order), 13 (borrowed tree).
- Under `fix` or `deep`, 11 and 21 are div. The kernel's `fold_own` is total, but it is a right
  fold and fixes the order.
- For `rec` on strict subterms of an owned argument to be total, `rec` needs the argument's
  size as fuel. That means either a descent eliminator (prior-art matrix C2 for lists) or a
  checker rule that recognises the descent.

**R9. Borrowed descent at one lifetime.**

- Forced by: 13 and 12; `corpus/pending/print-borrowed-list.bc`.
- `sum(&t)` by `rec` needs a request type `&'a Tree` whose children are again `&'a Tree`. Today
  a view cannot be unrolled (13).
- `fold_imm` runs (12), but only for results that outlive every lifetime, and on the host stack.
  This is gap (b) of the prior-art matrix (C3).
- Without it, borrowed trees and lists can be walked only structurally, and not by `rec`, `for`,
  memo or a deep driver.

**R10. `rec` inside a loop body, and loops in any body.**

- Forced by: 09 (a `for` body that recurses), 14 (`while` bodies that recurse), and 19.
- Today a `for` body must be total (SPEC §14 Open, F8), and `while` exists only in generators
  (19).
- In the machine, a loop with a `rec` in its body is one machine with the loop's cursor in the
  frame. Nothing new is needed beyond R1.

**R11. Errors escape the recursion as a stop, through the layers.**

- Forced by: 14, 15 (unknown opcode), 26 (ran out is the same path).
- A non-resuming operation inside the recursion ends the machine and drops its frames. Frames
  hold linear data (11: owned subtrees), so dropping them runs their destructors. The error
  then leaves through every layer.
- A frame holding something with no destructor (a capability) could not be dropped. As lowered,
  capabilities stay in the state, never in frames. I have not tried one in a frame (§9).

**R12. Groups.**

- Forced by: 14 (three members), 16 and 17 (two).
- One `rec` per group, with the request tagged by member.
- A per-member layer is one layer that dispatches on the member (17).

**R13. An empty "ended" value.**

- Forced by: 23 and 24.
- The loop over a source that cannot end should have exactly the break type. Today the source
  must end its body with a value it never reaches.

**R14. What the lowerings needed that is not about recursion.**

- `deep`'s type arguments had to be written when `A` is a pair (14, 26).
- A lifetime-generic step needed a closure around it (20).
- `break <arith>` hit an internal error (22b).
- A generic `fn` cannot be called at a generic `def`'s type variables (`rec.bc`).
- Promoting a `!` closure fails while an `i32` is live in the context (02).

## 7. What `for` needs from the mechanism

`for x in y { M }` desugars as in Rust:

    let it = into_iter(y);
    loop { match next(it) { some x -> M | none -> break } }

The `loop` is `rec` in tail position over `(it, the variables M assigns)`. So `for` uses exactly
these pieces of the mechanism:

1. **Tail `rec` and nothing else.** A `for` whose body does not recurse never pushes a frame.
   The loop itself allocates nothing in 15, 16, 18, 20, 22, 23 and 25. What they do allocate is
   their data: arrays, and 25's line lists. It does not use frames (R1), memo or
   groups.
2. **A driver.** Which one follows from the source's type:
   - a **sized** source (a count, an array, a view, an owned list) gets fuel from its bound,
     computed from the data. It is total, with no "ran out" case, because `next` answers `none`
     exactly when the fuel is spent (20; 21 intended);
   - an **unbounded** source (a generator, stdin) gets `fix`: div (22, 23, 25);
   - an explicit `fuel(n)` gives total with "ran out" (18).
3. **The step's exit.** `break e` is the step answering "done", `S ⊗ A → S ⊕ R`. It is the
   machine's `Out` with no request: answer instead of `rec`. `continue` is `rec` with the state
   unchanged. `return` is a stop (the `Z` path) caught at the function's boundary.
4. **The source's "ended" value.** The loop's value is `ended + break`:
   - a source that can end contributes its finishing value (25: `()` and the capability back);
   - a source that cannot end contributes `never` (R13).
5. **Effect forwarding.** `next` is effect-polymorphic: 25's `lines` is the same code over a pure
   source. A body's effects (`e.fail`, I/O) escape as they do from any `rec` body (R11).
6. **The per-step lend** (R2). `for x in &a`, `&mut a` and a view lend the element inside one
   step, as the machine lends loop-invariant arguments (20; F1 of the iteration design).

`for` does **not** need the frame stack, the memo layer's request tagging, or groups. A `for`
whose body performs `rec` (09's DFS) is not a special `for`. It is a recursion whose frame holds
the loop's cursor (R10).

## 8. Where layers attach, and where implicit `rec` is ambiguous

**Attachment.** In this corpus, layers attach **at the use site**, by `|>`, to the definition's
open step: `fib |> memo(&mut c) |> deep`.

- The definition stays plain.
- The same definition is used under different drivers and layers (fib.rec uses four).
- The cache is the caller's (`&mut c`), so its lifetime and its representation (array or map)
  are the caller's choice.

Attaching at the definition (`fn fib … with memo`) would fix the cache's owner and type at the
definition, and give every caller the same stack behaviour. Nothing in the corpus needs that. The
per-member layers of a group (17) are the one place where attachment is awkward:
`group(even |> memo(ce), odd |> memo(co))` names the members at the use site.

**Ambiguity of implicit `rec`:**

- **Groups (14, 17).** When `expr` calls `term`, the call is either the group's `rec` (one
  machine, one stack, and layers on the group see it) or a call of `term`'s own closed default
  (`term |> fix`, a nested driver). Both give the same answer, with different stacks and a
  different reach for layers. Treating each strongly connected component as one group is the
  reading used here. It has to be the elaborator's rule, and reported.
- **Calls through a value.** A self-reference passed as a value (`map(xs, f)` inside `f`) is not
  a direct call. Whether it is `rec` (a capability passed on) or the closed default is not
  settled by "self-call means `rec`". No program in this corpus does it.
- **A layer on a member vs on the group.** In `group(even |> memo(ce), odd)`, even's layer
  sees only requests to `even`, including those `odd` makes. This is the reading lowered in 17.
- **Which arguments a layer keys on** (R5).

## 9. What I have not established

- Why 04's allocations grow as (n + 1)(n + 2)/2. I have observed the count and the 2999 copies. I have
  not traced which copy allocates.
- Whether `deep`'s frame stack could be a growable array instead of a list, so that it
  allocates only on growth. Only the list was written.
- Whether frames holding a capability (a value with no destructor) can be dropped on a stop.
  No lowering puts one in a frame.
- The exact host-stack limit, beyond 04's step running at 3000 and failing at 3500.
- Whether the unrolled open form (§3.2) could be made cheap by the elaborator in general. 06
  shows that it costs nothing when the depth is a small constant known statically.
- The typing of a `for` over a sized source as total with no "ran out" case. As lowered, the
  bound is passed to `count_fold` by hand.
- Anything about threads, async, or multi-shot continuations. `rec`'s continuations here are
  one-shot.
