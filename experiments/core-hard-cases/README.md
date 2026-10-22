# #669 hard cases: can a Core → Core effect elimination handle them?

Each case is written by hand as **effect-free core** (no `handle`, `perform`, `raise`, row or
`tick`), the target a generic Core → Core pass would produce. Each term is checked by the kernel
(`bcc check`), run at the reference interpreter, the LIR interpreter and Wasm, and compiled by the
new backend with its effect layer unused. Then memory and ownership bugs are injected to see
whether the kernel refuses them. No kernel, checker or backend change was made, and nothing here
is imported by the library.

## Tools

- `run.sh file.bc…` (from the repository root): one line per term. It gives the `assurance` line
  or the kernel's first error (`REFUSED`), the output at the reference interpreter (`src`, 60 s
  timeout), the LIR interpreter and Wasm, the effect erasure's postcondition (`bcc lir --erasure`),
  the plain-path line, and the counts (`bcc-counts --backend new`).
- `PlainPath.lean` (`lake env lean --run experiments/core-hard-cases/PlainPath.lean f.bc`): runs
  `Backend2.lirOf` and reports which of the conversion's GLOBAL pieces (#670) ran:
  - `machines`: the state machines converted (§49). With none, `lirOf` returns before
    `tailPass`, `cellPass`, `threadedOf` and `stackedOf`.
  - `tailSites`: the sites `tailPass` reads.
  - `merged`: the task variants `genMerges` merges.
  - `threaded` and `stacked`: the second run's machines (§50 cells passed on, §52 task stacks).
  - `statics`: the static cells.
  - `effectOps`: the LIR's stack, frame, κ-region, static-cell and `unreachable` operations.
  - `reads`: the facts the conversion read, by key.

  On every effect-free term all of these are `0` or `[]`. For contrast, main's
  `bench/async-tree/main.bc` reports `machines 6 merged 1 stacked 1 statics 3` and ten
  stack/frame/κ operations.

**Bug kinds** (user, 2026-10-22):
- **MEMORY/LEAK**: use after free, double free, a resource never released, a mutable alias, a
  borrow outliving its lender, an affine resource duplicated. The kernel must refuse each one.
- **SEMANTIC**: a wrong value, a wrong order of effects, or the wrong summand resumed. The kernel
  is expected to accept these; they are controls.

A resource the term forgets to release is either refused, or repaired by the checker's implicit
destructor (SPEC §12), which the program then runs (`live 0`). A repair is not a leak. The `linear`
variant of the same bug shows the kernel refusing it when no repair is allowed.

## Summary

Every term was written by hand. **No rewriter was built.** "Typed" means the kernel accepts the
term, with the assurance shown. "Plain" means the `PlainPath` line is all `0` with `effectOps []`,
and the erasure line is `handles 0 performs 0 raises 0`. Counts are allocs / indirect calls
(loads/stores where they matter), against main's compile of the same source. MEMORY counts the
MEMORY/LEAK bugs the kernel refused, out of those injected. The rest of each count was accepted
**with the checker's implicit destructor repairing it** (`live 0` at every stage), not leaked.

| case | typed | extension needed | plain path | counts against main | MEMORY refused | SEMANTIC |
|---|---|---|---|---|---|---|
| H1 `gen-tree` at its `for` | yes, unconditional | none | yes | 0/0, equal; native 102 ms against main's 103 and Rust's 103 | — | — |
| H1 stored recursive generator (two walks zipped) | yes, unconditional | none (frames are a `mu` list in the `unfold` state) | yes | n=16384: 131072 / 0 against main's 196608 / 131084; native 56 ms against main's 231 | 2/2 (+1 repaired) | accepted |
| H1 `async-tree`, recursive task | yes, unconditional | none | yes | `mu`-list frames: 1 alloc per push (131073). **Owned-array frames: 5 / 0** against main's 13 / 0 (task stacks); native 179 ms against main's 249 and Rust's 109 (iterative) | 3/3 (+1 repaired) | accepted |
| H2 `async-r1-local-borrows` | (a) refused; (b) yes, inline scheduler only; **(c) yes, unconditional** | none for (c); E1 for (b) at a queue; E2 for (a) | yes | (c) 2/0/0/7/7, equal | 8/8 for H2 (+1 repaired) | accepted |
| H2 `async-logged` | **(c) yes, unconditional** (main: `PinLaw`) | none | yes | 22/0/0/166/148 against 22/0/0/206/188 | (as above) | accepted |
| H2 `async-cancel` | **(c) yes, unconditional** (main: `PinLaw`) | none | yes | 5/0/0/69/66 against 5/0/0/137/134 | (as above) | — |
| H3 owned tree, re-borrow per step | yes, unconditional | none to type it | yes | **native 514 ms: 2.73× task stacks, 2.52× Rust: KILL** | 7/7 for H3 (+2 repaired) | accepted |
| H4 `async-race`, ν as the existential | yes, unconditional | none | yes | 3 / **11** against 3 / 0 (main uses `genMerges` + `tailPass`) | 5/5 (+2 repaired) | accepted |
| H4 `async-race`, defunctionalised in Core | yes, unconditional | none (needs a closed closure class: a whole-program Core rewrite) | yes | 3 / 0, equal | 5/5 (+2 repaired) | accepted |
| H4 bodies holding borrows, one queue | yes, unconditional | none (`box 'd` with `'d` strictly inside each lend) | yes | 2/0/0/5/2 (no counterpart on main) | 3/3 | accepted |
| H5 cancel at the perform, finaliser writes | yes, **unconditional** (main: `PinLaw`) | none | yes | 1/0/0/2/2, equal | 8/8 (+1 repaired) | accepted |
| H5 stored task cancelled later, finaliser re-lends and writes | yes, unconditional | none | yes | 16/4/0/97/92 against 15/6/0/285/297 | 10/10 (+2 repaired) | accepted |
| H6 `hygiene-handler-state`, `answers-two-types` | yes, unconditional | none | yes | 0/0 against 0/2 | none applies | accepted |
| H6 `clause-captures` | yes, unconditional | none | yes | 6/0/0/10/10 against 6/3/0/10/10 | 6/6 (+1 repaired) | accepted |
| H7 dropped task | yes, unconditional | none | yes | 1/0/0/1/1, equal | 6/6 (+1 repaired) | accepted |
| H8 derived view held across the stop | **refused** (box rule, or "cannot show `U (pull …)` outlives `top`") | **E2** | — | — | — | — |
| H8 view re-derived as an index | yes, unconditional | none | yes | 1/0/0/6/3, 4 bounds (p6's push form: 0) | 4/4 (+1 repaired) | accepted |
| H8 a cursor into a borrowed `mu` value | yes, but **quadratic** (copy + walk per step) | E2 alone does not fix it: Core has no partial walk of `mu` under `imm` | yes | N=200: 80,601 allocs against 600 for the owned zipper | (as above) | — |

**No MEMORY/LEAK bug got past the kernel.** Across H1–H8, every injected use after free, double
free, mutable alias, affine duplicate, borrow stored in state or outliving its lender, and
finaliser run twice was refused. Every skipped release was refused under `linear`. Without
`linear`, the checker inserted the destructor (`close` for a task), and the run ended `live 0`.
Every SEMANTIC control was accepted, as expected.

**Kill criteria.**
- Effect-free form not typeable without giving up a borrow guarantee: **not hit**. H8's held
  view is refused. Its re-derived forms type, but one of them (the cursor into a `mu`) costs
  quadratically.
- A seeded ownership or borrow bug passing the kernel: **not hit**.
- H3 worse than task stacks or above 1.2× Rust: **hit** for re-borrow per step (2.73× task stacks,
  2.52× Rust) and for the owned zipper (2.03×, 1.88×). Only the consuming walk is competitive
  (0.94× task stacks, 0.87× Rust in total; its walk alone is about 1.7× Rust's).

**The plain path** (the coordinator's requirement):
- Every typed term compiles with **none of #670's GLOBAL pieces**: no `genMerges`, `tailPass`,
  `cellPass`/`threadedOf`, task stack or second conversion run. `lirOf` returns before them,
  since `machines 0`. `directFacts`/`machineOps`/`stackOps` run but find no `handle` node. No
  tick numbering is used, because no `Div` tick is left.
- What runs is the derivation-following conversion (#670's slice 1: every `reads` key is a node
  fact, a mask, or a constant's expansion) and Lower.
- **One whole-program analysis still runs on every program: `Layouts`**, the closure classes
  (0-CFA) that Lower uses for closure representation and for copy and drop layouts. It decides
  representation (L2/L12), not ownership. Whether its correctness is "local" in #670's sense is
  **not established**: a wrong closure class would mis-dispatch a call, which is a memory fault.
- **Zero cost needs no ownership-deciding lowering,** with two qualifications:
  - H4's zero indirect calls come from a Core rewrite that needs a closed closure class. The
    kernel checks its output, so a wrong analysis there gives wrong semantics, not memory
    unsafety. With the ν form, L12 (finite dispatch over `Layouts` classes) would be needed.
  - H1's recursive task reaches zero allocations per `await` because its frames are an owned
    array chosen **in Core** (`a1b`). The `mu` list costs one allocation per frame push unless
    L11 (in-place reuse) is built. L11 is not built.

## H7. The #671 leak: a task dropped without a cancel

See `h7/` and `h7/results.txt`.

**The source on main.** Four kernel-typed programs drop a suspended task that owns resources:
- `h7-drop-task-source`: a task suspended at its `await`, owning a cell, never used;
- `h7-drop-in-queue-source`: two such tasks in a queue that is never run;
- `h7-drop-recursive-source`: a recursive task (a stack machine, so it runs on a §52 task
  stack), suspended 3 levels deep with a cell at each level. One task is dropped after one
  resume, and a queued one is never run;
- `h7-drop-in-kappa-source`: a task held in the frames of a continuation that a clause drops
  (`stop(k) = 0`).

All four **type** (`assurance: unconditional`). All four end **`live 0`** at the reference
interpreter, the LIR interpreter, Wasm and natively. The LIR interpreter counts task stacks,
frames and cells as live objects (`Backend2/Interp.lean`, `stackNew`, `framePush`), so a leaked
stack would show.

**Why no leak.** The kernel never drops a task silently. `Task[A]` is
`box top U (nu X. F (A + box top U X) & F 1)`, which is class 2 of SPEC §12: its destructor is
`close`, the task's cancel. An unused task gets that destructor from the checker. In the LIR it
is `x.1` (the second observation), followed by `drop` of its `1`. A queue's destructor is
`fold_own` with each task's `close`. A dropped κ's destructor is its cancel. **The §52/#671 leak
was not reproduced by any kernel-typed program tried here.** SPEC §52 *Not leak-free* and #671
describe a drop that, on these programs, the kernel turns into a cancel. A program that
reaches a drop with no `close` was not found; see *Not verified*.

**The Core form** (`h7-core-drop-task.bc`):
- The task is an `unfold` whose state is the cell. `next` frees it and answers; `close` frees it.
- `with spawn` is the first segment (the `alloc`) and the machine boxed at `top`.
- `main` never uses `t`.

It is accepted `unconditional`, gives `i32[7] live 0` at every stage, has no machine and no
effect-layer operation, and counts `allocs 1 indirect 0 copies 0 loads 1 stores 1`. That equals
main's count for the source (`h7-drop-task-source`: 1 0 0 1 1 0, with 1 machine).

**What the kernel does with the drop:** it **forces the drop to run cancel** (an implicit `close`).
A `linear` binder **refuses** the drop. It **never allows a leak.**

| bug (`h7/bugs/`) | kind | kernel |
|---|---|---|
| `b1` close forgets `free c` | MEMORY/LEAK | accepted, **repaired**: the checker inserts `free c`; `live 0` at every stage |
| `b2` the same with `c` bound `linear` | MEMORY/LEAK | refused: ``d` is declared `linear` and is not consumed in its scope`` |
| `b3` close frees `c` twice | MEMORY/LEAK | refused: ``c` is used twice here, and its type `ref i32` is not persistent`` |
| `b4` next reads `c` after `free` | MEMORY/LEAK | refused: ``c` is used twice here …`` |
| `b5` the task resumed, then the same value cancelled | MEMORY/LEAK (affine duplicated) | refused: ``t` is used twice here, and its type `box top U (nu …)` is not persistent`` |
| `b6` the task bound `linear` and dropped | MEMORY/LEAK | refused: ``t` is declared `linear` and is not consumed in its scope`` |
| `b7` close returns the cell instead of releasing it | MEMORY/LEAK | refused: `type mismatch: expected `1`, but this has type `ref i32`` |
| `s1` next answers the value + 1 | SEMANTIC | accepted (control) |
| `s2` cancel explicitly instead of dropping | none (control) | accepted, the same counts |

MEMORY/LEAK: 6 of 6 refused, and 1 repaired (`b1`) with no leak. SEMANTIC: accepted.

## Rule sketch (one rule per construct, read off the typed term)

| construct | effect-free Core |
|---|---|
| tail clause at a `for` site | the work, a `!` def taking and answering the handler's state σ, called at the `perform` (`tail_resumes`); the loop has no row |
| last clause that cancels (`[handle-last]`) | `case` on the work's answer; the cancel arm runs the region's finalisers innermost first, then exits (T-B1/T-B1′) |
| abortive operation | `F_Σ R ↦ F (R ⊕ P)`; each frame between is a `case` arm; `on_exhausted` is a `case`; recursion under `Exhausted` is `bounded_fix` with a `+ 1` budget summand |
| stored κ (generator, task) | an `unfold` whose state has one summand per resumption point, carrying that point's live variables. Resume is `.1`, cancel is `.2` (`close`), which drops what the state owns (the checker's destructors) |
| a call that suspends inside a machine | **non-tail:** push a frame record (a sum over the caller's points that are inside a call, carrying their live variables) onto the frames in the state. **Return:** pop and continue at that frame's point. **Tail call:** no frame |
| the frames' representation | a `mu` list (one `roll` per push), or an owned array in the state (`a1b`, zero allocations per `await`); chosen in Core, so the kernel checks it |
| `with spawn` | runs the first segment, then `boxed[top]` the machine, or a finished task |
| tasks of several bodies in one queue | ν is the existential: each body is an `unfold` at its own state type, packed into one `Task[A]`. Or, when the closure class is closed, the slot is a sum of the bodies' states (whole-program) |
| handler holding a `mut` borrow | the borrow threaded linearly through the body; each operation is a `withswap`; the lend ends at the `with` |
| R1 lend where only the borrow crosses a stop (H2 (c)) | the state holds the owner. Every live `mut 'x T` / `imm 'x T` is stored as `1`. The resuming observation re-opens `withbor2` and refills those positions. `close` re-opens the lend for the borrower's finaliser, ends it, then runs the owner's destructor. **Precondition:** `'x` occurs in the live variables' types only as the borrow itself, under `*`/`+` (never under `U`, `view`, a family, or a reborrow) |
| a dropped task | nothing: the checker inserts its `close` |

**What is not a handler law.** Re-borrow per step (H2 (c), H5b, H8b), frames as an array (H1 `a1b`)
and the defunctionalised queue (H4b) are program transformations. The kernel checks their output,
so a wrong one gives wrong semantics, not a memory fault.

## H1. Recursive machines (`h1/`)

- **No new type former.** κ of a recursive generator or task is an `unfold` state holding its frames.
  - The stored zip of two `gen-tree` walks (`g2`) has state `(lo, hi, r, Stack)`, with
    `Stack = mu L. 1 + (Frame * L)` and one frame summand (`K_left`), since the right call is a
    tail call.
  - `async-tree` (`a1`) has frames `K_left(m, hi, r) + K_right(a, m, r)`. The task at its `await` is
    first-order data, held by value in the scheduler's array slot (#669's p3c).
- **Native time** (CPU ms, median of 9, `h3/bench-results.txt`):

  | program | ours | main | Rust |
  |---|---|---|---|
  | `gen-tree` at its `for` | 102 | 103 | 103 |
  | stored zip | 56 | 231 | — |
  | `async-tree`, `mu`-list frames | 389 | 249 (task stacks) | 109 (iterative) |
  | `async-tree`, array frames | 179 | 249 (task stacks) | 109 (iterative) |

- **Counts.** The `mu` list costs one allocation per push. The owned array (doubling; the grow
  path was exercised with a 1-slot start) costs 5 allocations in all, against task stacks' 13.
  It pays more bounds checks (393,220 against 131,088 at n=16384), from `array_replace` with no
  in-range fact (§52 *Open*).

## H2. A borrow of a local held across `await` (`h2/`)

| encoding | result |
|---|---|
| (a) the borrow as a field of the state | **refused**. Box rule: "`boxed['x]`: `s0`, of type `1 + mut 'x i32 * i32`, … cannot be shown to outlive `'x`" (`h2a-pair-view-field`). Accepted when the lend is external and spans the run (`h2a-pair-view-external-field`, `TaskIn<'d>`'s case). |
| (b) the lend re-supplied at each resume | **accepted** with the owners hoisted to `main` and an inline scheduler (`h2b-local-borrows-resupply`). At the library's `Task[A]` queue, a fresh lend per resume is **refused** by `NuOk` (`h2b-lib-fresh-lend`): that is E1. Hoisting also moves ownership out of the task, so its cancel no longer frees the cell. |
| (c) re-borrow from owned state per step | **accepted, `unconditional`**, for all three: `h2c-local-borrows`, `h2c-logged` (the library's `lpush`/`run_logged` unchanged), `h2c-cancel` (`close` frees `buf` then `extra`; `bcc interp --check tags` clean). |

Main reports these sources under `PinLaw`. Form (c) needs no assertion, because no borrow is held
between observations. It is legal exactly when nothing derived from the borrow crosses the stop.

## H3. A task that owns a tree (`h3/`)

The tree is `mu X. 1 + (ref X * (i32 * ref X))`.

**Main's source.** Main cannot hold an `imm` borrow of the tree across `await` (an `imm` R1 is
refused), so the source it compiles (`src-owned-tree`) is a **consuming** recursive walk on §52
task stacks.

**The Core forms:**
- `r3`: re-borrow per step. The state owns the tree and a path array. Each step takes one lend and
  one `withload` per level, so it costs O(depth).
- `z3`: the consuming walk, by the H1 rule, with array frames holding owned subtrees.
- `zz3`: an owned zipper. Nodes are taken apart on the way down and rebuilt on the way up.

**Rust** (`main.rs`): `Box` nodes, an `async fn` with a `Vec<&Node>`, and `async-tree-iter`'s
scheduler.

**Results** at n = 1,048,576 and 8 tasks, CPU ms, median of 9:

| program | total | vs Rust | vs task stacks |
|---|---|---|---|
| Rust, borrowing walk | 204.0 | 1.00× | — |
| main's consuming source (task stacks) | 188.2 | 0.92× | 1.00× |
| **`r3`, re-borrow per step** | **514.3** | **2.52×** | **2.73×** |
| `z3`, consuming | 176.5 | 0.87× | 0.94× |
| `zz3`, zipper | 382.7 | 1.88× | 2.03× |

Building the tree takes 165 ms in Rust and 108 ms in Core. With the build subtracted, the walks
take: Rust 39 ms, task stacks 80, `z3` 68, `zz3` 275, `r3` 406.

**Kill: hit.** Re-borrow per step is worse than task stacks and above 1.2× Rust. A non-destructive
O(1) walk has to hold positions in the tree across `await`, which is E2 (H8).

**Representation finding.** `withload` at an inline `mu` deep-copies the value in both backends.
In `probe-view-copies`, two lends of a 1000-node tree make 3001 allocations. A walk that
re-borrows therefore needs the tree's recursion under `ref`.

## H4. Tasks of different bodies in one queue (`h4/`)

- **No existential former is needed: `ν` is the existential.** Each body (`lookup`, `sleeper`) is
  an `unfold` at its own state type, packed into one `Task[i32]` (`h4a`). The resumes are
  indirect calls (11).
- **Defunctionalised (`h4b`).** The task type is the sum of the bodies' states. This reaches
  main's counts (3/0) with no `genMerges` or `tailPass`. It is a whole-program Core rewrite: it
  needs the task type's closure class to be closed.
- **Bodies holding borrows (`h4c`).** Two different bodies, each holding an `imm` borrow of a
  different cell, share `box 'd U (nu X. F (i32 + box 'd U X) & F 1)`. That is `TaskIn<'d>`, with
  `'d` strictly inside each lend (non-strict box rule, §23). Boxing at the lend's own `'b` is
  refused. No existential with an outlives bound is needed while `'d` is fixed for the queue's
  life. A queue whose tasks are lent afresh per resume is H2 (b), which needs E1.

## H5. Cancel with finalisers that write (`h5/`)

**`h5a`: the clause cancels κ at the `perform`.** The `perform` becomes the region's finalisers in
order: the write of 99 through `m`, the end of the borrow, the end of the lend, `free c`. The
form needs no R1, so it is **unconditional**, where main's is `PinLaw`.

**`h5b`: a stored task, cancelled later** by a killer task. A third task is dropped. The state
owns `buf` and `extra`. `close` re-opens the lend, writes 99, ends the lend, frees `buf`, then
frees `extra`.

**Exactly-once release on finish, cancel and drop is enforced by the kernel's linearity.**
- A double release is refused.
- A skipped release is refused under `linear`, or for a type with no destructor. A finaliser
  packaged as a thunk and never run is refused: "`U (F i32)` has no destructor".
- Otherwise the skipped release is repaired by the inserted destructor.
- A write through `m` after the lend ends is refused, and so is the borrow escaping.

The kernel does not enforce the content or order of a non-releasing finaliser, such as the write
of 99. That is SEMANTIC.

## H6. Handler state (`h6/`)

- **The state** is threaded through a `!` work as argument and answer (`σ → σ * answer`, evidence
  passing). With two answer types, each clause has its own work, so the old backend's answer
  variants do not arise.
- **`count(&mut n)`:** the `mut` borrow is threaded linearly. Each `tick` is a `withswap`.
- **`releasing`:** abortive, so it becomes `A + E` and a `case`, each arm freeing `c`.
- **`asking`:** threads an owned cell, freeing the old cell and allocating the new one per
  `ask`.
- **Counts:** the indirect calls go to 0 (0/2 → 0/0; 6/3 → 6/0).

## H8. A derived view held across a suspension (`h8/`)

- **The held view needs E2.** The stored cursor of `for-lend-resumes` (`array_imm 'l i32` and an
  index) is **refused** (`h8a`): "cannot show that `U (pull i32 1 1)` outlives `top`". #669's
  `p5` is the box-rule form of the same refusal. The same view held under an *external* lend is
  accepted (`h8a2`).
- **Re-derived as an index:** accepted (`h8b`). It pays a bounds check per step, which §46's
  in-range fact no longer covers.
- **A cursor into a borrowed `mu` value** (`h8c`): **not expressible even within one
  observation.** `fold_imm` is the only eliminator of `imm (mu …)`. Its algebra is `!` code, and a
  run-time position cannot be made `!`. So each step copies and walks: N=200 costs 80,601
  allocations, which is quadratic. The owned walk (`h8d`) costs 600 but takes the list apart.

**E2, sketched** (the spanning lend of `experiments/LoopBorrow`):

    Δ ⊢ A ⊒ @b    'x ∉ FV(A, B, R)
    Δ, 'x ⊏ ⊓Δ ; m : Mut 'x A ⊢ M : F (U (νX. F (B ⊗ U X ⊕ ['x] R) & F 1))
    ─────────────────────────────────────────────────────────────────────────── [lend-ν]
    r : Ref A ⊢ withborν r (Λ'x. λm. M) : F (U (νX. F (B ⊗ U X ⊕ Ref A ⊗ R) & F (Ref A)))

- **What it relaxes:** the machine's state may hold `m` and anything derived from it. The
  elements `B` stay free of `'x` (no lending yield). The owner comes back at the end or at
  `close`.
- **Soundness:** the lend is held folded between observations. That needs a register of open
  lends in `wpTS`/`TW`, with `↭`'s `mut` clause read modulo the register.
- **Obligation:** #645 classes 2/3 (validity at every `Ext` extension). This is open, and
  LoopBorrow refutes the refold route without the register.
- **Cost:** `Core/World`, `Wp` and every frame rule reading `↭`. That is thousands of lines, and
  whether it can be proved is unknown.
- **Relation to PinLaw:** E2's compatibility lemma is what R1's `PinStop` asserts. Proving E2
  for machines makes `PinLaw` a theorem there.
- **A cursor into a borrowed `mu`** (`h8c`) also needs a partial walk of `mu` under `imm`
  (SPEC §5 *Open*).

## Extensions (proposals; none built)

| | statement | admits | soundness in a sentence | rough cost |
|---|---|---|---|---|
| E1 | `NuOk` admits an observation `forall 'b < @. (A_b -o D)`, with `X` in `D` only under `box @c` and `'b ∉ @c` | H2 (b) at a library queue: a lend supplied afresh at each resume to a task that outlives each lend | the `box @c` keeps the rest from capturing `'b`, so each observation is an ordinary call at a fresh lifetime | `∀` in `cB`; `unfold`'s map at `allE`/`allI`; the `nuIn`/`nuOut`/`unfold` compatibility cases. About 0.5–1.5k lines (estimate) |
| E2 | `[lend-ν]` above | H8's held views; H3's non-destructive O(1) walk; R1 machines with no assertion | the lend is held folded, with a register of open lends | #645 classes 2/3, open research; thousands of lines; feasibility unknown |
| E5 | a partial walk of `mu` under `imm` (a cursor eliminator that yields the view of a child) | `h8c` within one observation; with E2, across stops | a child of an `imm` node is `imm` at the same lifetime | a `foldImm`-sized constant and its compatibility lemma (SPEC §5 *Open*); not costed |

## Verdict

**Does Core → Core solve the borrow part of lowering for the hard cases?**

**For the effect layer, yes.** Every case's effect-free form types except a held derived view.
That includes:
- recursive generators and tasks;
- tasks of several bodies;
- finalisers on cancel;
- handler state;
- borrows of locals across `await` (by re-borrow per step);
- dropped tasks.

The kernel refused or repaired every memory and ownership bug injected. Each typed term compiles
on the plain path with none of the GLOBAL pieces. Three of the forms (H2 (c), H5a, H5b) are
**unconditional** where main's are `PinLaw`.

**For self-borrows held across a suspension, no, not at zero cost.**
- **H3's kill is hit.** Re-borrow per step on an owned tree is 2.7× task stacks and 2.5× Rust.
- **H8's held views need E2,** which is open research.
- A cursor into a borrowed `mu` value is not expressible in Core even within one observation.

The only competitive owned-tree form is the destructive walk.

**Fraction that would stay hand-lowered.** Of the effect layer's pieces in #669's table:
- **Expressed as Core here:** κ machines, stored generators, task bodies, the frames of
  recursive tasks (as an owned array), `genMerges` (as a sum of states), handler state and
  aborts.
- **Still needed below the kernel:**
  - **`lendR`**, a borrow held in a stored machine (R1 with a derived value crossing, and the
    O(1) owned-tree walk). It has no Core form without E2. Today it is `PinLaw` plus Backend2's
    hand-lowering.
  - **L11** (in-place reuse) is needed only if the frames stay a `mu` list.
  - **L12 / `Layouts`** for zero indirect calls where the closure class is open.

Measured over the cases: 7 of 8 have a kernel-checked form with no extension. H3 types too, but
not at an acceptable cost; H8 needs E2. So the hand-lowered residue is the R1/`lendR` class:
self-borrows that must hold a position across a stop at O(1).

## Not verified

- **No rewriter was built.** Every term was produced by hand from the rule sketch. That a generic
  pass produces exactly these terms is argued, not shown. Meaning preservation is unproved.
- **H7:** no kernel-typed program was found that reaches #671's leak. That does not show none
  exists. A drop placed by Backend2 itself, and not by the checker, was not searched for.
- **`Layouts`' status** as a local lowering is not established.
- **Proofs and costs:** E1, E2 and E5 were not attempted. Their costs are estimates.
- **Sizes:** counts at bench sizes were too slow under `bcc-counts`. H1's counts are at
  n=16384, 4 tasks. Some reference-interpreter runs timed out at 60 s; there LIR and Wasm agree
  with the source's answer.
- **H3:** the walk-only figures subtract a separate build-only run. `r3`'s path array is fixed at
  64 slots and does not grow. Rust's `async-tree` is iterative.
- **H2:** (b) was written only for `async-r1-local-borrows`, and (a) only for `pair_view`. The
  others are argued.
- **H5:** `h5b`'s source on main leaves out the write of 99, since the surface has no `unwind`.
- **Native timing** was taken for H1 and H3 only.
- `make gate` was not run (targeted checks only).
