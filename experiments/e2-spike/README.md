# #682 Investigation B: a scoped scheduler, and the owned tree in two steps

Hand-written terms and measurements for #682's Investigation B. Nothing here changes Core, the
checker, the backend or `lib/`, and the library imports none of it. Every `.bc` was checked by
main's `bcc` (8555116). The tools are #669's (`experiments/core-hard-cases`, branch
`core-hard-cases`), copied: `run.sh`, `PlainPath.lean`, and H3's reference programs in `h3ref/`
(`src-owned-tree.bc`, `b3-build-only.bc`, `main.rs`, unchanged).

- `run.sh f.bc…` gives one line per term: the assurance or the kernel's first error, the output at
  the reference interpreter, the LIR interpreter and Wasm, the erasure line, the plain-path line
  and the counts. The output is in `results.txt`, at the files' sizes (n = 200, 3 tasks).
- `bench.py` gives native CPU time: the median of 9 interleaved runs at n = 2²⁰ and 8 tasks. The
  output is in `bench-results.txt`.
- `b2/cached_check.sh` runs the cached form (unchecked) against the proven form. The output is in
  `b2/cached-results.txt`.

## B1: a scoped scheduler, with the tree owned by `main` and borrowed by the tasks

`lib/async.bc` already has a scoped scheduler: `spawn_in`/`TaskIn[A]<'d>` boxes the continuation
at `'d`, the meet of the lifetimes in scope, and `run_in` runs a list queue for a counted number
of rounds. The variant here (`round_at`, `run_at`) is `lib/async.bc`'s in-place array round
(`round`) at `TaskIn[A]<'d>`, run for a counted number of rounds. It is counted because a `while`
cannot stay inside a lend (SPEC §14). In the core forms the tasks are `unfold`s boxed at `'d`
(`TaskAt[A]<'d>`, the same type). `'d` is a unit cell's lend inside the trees' lend `'l`, because
the box rule's `Imm` case is strict (SPEC §23).

| file | form | tree | positions held across `await` | kernel |
|---|---|---|---|---|
| `b1/s1-arena-held.bc` | surface (`spawn_in`, `await`) | arena: one array of `(key, left, right)`, children by index | a stack of leaf views `imm 'l Node` | **accepted, `assurance: unconditional`** |
| `b1/c1-arena-held.bc` | effect-free core, ν boxed at `'d` | arena | the same stack, in the `unfold` state | **accepted, `unconditional`** |
| `b1/c1d-arena-held-defun.bc` | effect-free core, state defunctionalised | arena | the same | **accepted, `unconditional`** |
| `b1/s3-mu-held.bc` | surface | H3's `mu X. 1 + (ref X * (i32 * ref X))` | a stack of `imm 'l Tree` | **refused**: `35:39: type mismatch: expected imm 'l (mu …), but this has type imm 'y (mu …)` |
| `b1/c0-mu-child-at-l.bc` | core probe | H3's | one child at `'l` | **refused**: `20:45:` the same mismatch |
| `b1/s2-mu-child-probe.bc` | surface probe, `data Tree` | §42 block tree | a child by a constructor pattern on the view | **refused**: ``11:3: `unroll V` needs `V : mu X. A`, but `V : imm 'l (mu …)` `` |
| `b1/c2-mu-path.bc` | core, ν at `'d` | H3's, an array of trees | the root's borrow only, plus the path (re-walked from the root each step) | accepted, `unconditional`; **the new backend fails** (below) |
| `b1/c2s-mu-path-shared.bc` | core, ν at `'d` | H3's, one tree shared by all tasks | the root's borrow plus the path | accepted, `unconditional` |
| `b1/neg/n1-box-at-lend.bc` | `c1` boxed at `'l` itself | | | refused: `` `boxed['l]`: `s2` … cannot be shown to outlive `'l` `` |
| `b1/neg/n2-run-after-lend.bc` | `c1` with the tasks run after the lend | | | refused: "this borrow block's result has type `array (… box 'd …)`, which has the block's lifetime `'d`" |

**Typing.** Over H3's tree, the `Vec<&Node>` walk needs a new rule, which is the kill criterion.

- The only way into a borrowed `mu` node is `withload`. Its callback sees the node at a fresh
  `'y ⊏ 'l`, and the children as `imm 'y Tree` (`Imm̲` at `μ`, SPEC §6). Its answer is `box 'y R`.
- So a child's position at the tree's lifetime `'l`, the element of a stack held across `await`,
  has no term.
- The rule it needs is a child view at the parent's lifetime: E5's "a child of an `imm` node is
  `imm` at the same lifetime". As stated, the update relation excludes it
  (`experiments/FrameEnd`, `imm_view_rejected`; SPEC §5 *Open*), so it is a model change, not
  only a rule.
- The scheduler is not the obstacle. The same task holding the root's borrow types
  `unconditional` (`c2`, `c2s`).

Over an arena, the same walk types with no new rule. Leaf views of an `array_imm 'l` family are at
the family's own lifetime and are top-level cells (SPEC §9 *Leaf views are direct places*), so a
stack of them can sit in a state boxed at `'d ⊏ 'l`. No `PinLaw` is used: the lend is outside the
task.

**Backend failure (`c2`).** The kernel accepts `c2-mu-path.bc` and the LIR interpreter runs it to
`i64[297900] live 0`. But Wasm, native and `bcc-counts` all stop with:
"`internal: closure classes not a fixed point: f19 (lam): a load: a read through a shared borrow of
contents at node 12206 (Backend2.Lay.NK.ref 12204) as node 12212 (Backend2.Lay.NK.ref 12204): not
one node, and not a reading of it`". This is `Layouts`, the closure-class analysis. The trigger
is the roots, leaf views of an `array Tree` passed to `r3`'s `nav`. `c2s` lends one tree from a
cell instead and compiles. The failure was not investigated further (no backend change).

**Counts** (n = 200, 3 tasks; allocs / indirect / loads / stores / bounds):

| program | counts | plain path |
|---|---|---|
| `s1` surface, compiled by main (one machine per task body) | 9 / 0 / 42984 / 39384 / 6018 | `machines 3 tailSites 1 merged 1` |
| `c1` core, ν at `'d` | 6 / **600** / 31911 / 28311 / 6012 | all 0 |
| `c1d` core, defunctionalised | 6 / 0 / 28284 / 24684 / 6012 | all 0 |
| `c2s` core, path re-walked | 405 / 600 / 44867 / 23819 / 8721 | all 0 |
| H3's main source (task stacks, consuming walk) | 1210 / 0 / 37908 / 30720 / 1212 | `machines 6 … stacked 1` |

`c1`'s 600 indirect calls are one per resume through the ν (H4a's cost). `c1d` removes them.

**Native time** (`bench-results.txt`; CPU ms, n = 2²⁰, 8 tasks; walk = total − build):

| program | total | walk | vs Rust (total / walk) |
|---|---|---|---|
| Rust H3 (`h3ref/main.rs`: each task owns a Box tree, `Vec<&Node>`) | 204.6 | 39.4 | 1.00 / 1.00 |
| Rust B1 (`b1_borrowed.rs` 0: `main` owns the Box trees, tasks borrow them) | 200.4 | 35.3 | — |
| Rust B1 arena (`b1_borrowed.rs` 3: `Vec<ANode>`, a stack of `&ANode`) | 62.3 | 34.0 | — |
| main, H3 source, task stacks (consuming) | 187.7 | 78.0 | 0.92 / 1.98 |
| **`s1` surface arena** | **100.4** | 67.1 | 0.49 / 1.70 against Rust H3; 1.61 / 1.97 against Rust arena |
| **`c1` core arena, ν at `'d`** | **60.3** | 27.0 | 0.29 / 0.69 against Rust H3; 0.97 / 0.79 against Rust arena |
| **`c1d` core arena, defunctionalised** | **57.3** | 24.0 | 0.28 / 0.61; 0.92 / 0.71 |
| `c2s` one shared H3 tree, path re-walked | 393.1 | 377.9 | against Rust one shared tree (52.6 / 31.0): 7.5 / 12.2 |

The arena totals are not comparable with H3's: the build is one allocation instead of one per
node (33 ms against 110 for the same 8 × 2²⁰ nodes). Against the Rust walk over the same arena,
the core forms are at 0.92–0.97× in total and 0.71–0.79× on the walk. The surface form is 1.6×.
The arena walk with held views (24–27 ms) is faster than task stacks' consuming walk (78 ms) and
than Rust H3's Box-tree walk (39 ms).

## B2: the owned tree, in two steps

### B2.1 The proven form

| file | owner in the state | per step | kernel | total | walk |
|---|---|---|---|---|---|
| `b2/p1-r3-owned-reborrow.bc` (#669's `r3`, unchanged) | `ref Tree` (H3's tree) and the path | lend the cell `imm`, walk the path from the root: O(depth) | `unconditional` | **511.0** (2.50× Rust H3, 2.72× task stacks) | 401.3 |
| `b2/p2-arena-owned-reindex.bc` | its own arena (`array Node`) and a stack of indices | lend the arena `imm`, re-derive the top's view by `array_get` (one bounds check): O(1) | `unconditional` | **54.4** | 21.1 |

`p2` is the proven form at O(1). The state holds the owner and first-order indices, never a borrow.
It is faster than Rust's arena walk (0.87× total, 0.62× walk), but over an arena, not H3's tree.

### B2.2 The cached form (UNCHECKED)

`b2/cache_edit.py` edits the LLVM IR that `bcc` emits for `p1`. It renames the proven `adv` (the
resume) and puts in its place a wrapper that calls `b2/cached_step.c`'s `cached_adv`. That function
keeps a stack of node-cell pointers in the path array's memory across resumes. It is rebuilt once,
at the first resume, from the path the proven first segment left; after that a resume pops,
adds, and pushes the right child's leftmost chain (Rust's loop). The build, `spawn0` and the
scheduler are the compiled proven program. The step is linked under LTO.

| program | total | walk | vs Rust H3 (total / walk) | vs task stacks (total / walk) |
|---|---|---|---|---|
| `p1` proven (re-lend + path) | 511.0 | 401.3 | 2.50 / 10.2 | 2.72 / 5.1 |
| **`p1c` cached** | **152.4** | **42.7** | **0.74 / 1.08** | **0.81 / 0.55** |
| Rust H3 | 204.6 | 39.4 | 1.00 / 1.00 | |
| task stacks | 187.7 | 78.0 | | 1.00 / 1.00 |

The cached step gives the proven answer, `live 0` and the same 1207 allocations
(`cached-results.txt`). Totals favour ours because our build is cheaper (110 against 165 ms); on
the walk alone the cached form is 1.08× Rust's.

### B2.3 The invariant: does "the owner's cell is unchanged and unmoved between steps" follow from typing?

Every program below is typed `unconditional` and gives the proven answer (`results.txt`).
`cached_check.sh` applies the cached step to each, with the program's own change kept. For
`inv-c` and `inv-c2` the change is inlined into `adv`, so it is written again in C. The check
counts pops of a cell that is no longer a live node.

| case | program | typing fact, or the typed counterexample | cached run |
|---|---|---|---|
| read-only owner | `p1` | every use of the owner in a step is `withbor1` (an `imm` lend), which hands back the same `Ref`; `Imm̲` is read-only down through `ref X`; the `Ref` is affine and a lend's borrow cannot outlive it (`[x] B`), so no alias survives a step | right, 0 stale |
| the machine mutates the owner between yields | `inv-b-owner-mutated.bc`: at key 50 a `mut` lend of its own cell swaps in a fresh tree of the same shape and frees the old one | types: a `mut` lend of an owned cell in the machine's step is ordinary | **wrong: `i64[224778]`, 3 stale pops** |
| owner moved, `free` then `alloc` | `inv-c-owner-moved.bc`: at key 50 the tree moves to a new cell | types | right, 0 stale, **by accident**: the runtime's free list hands the same block back, so the "new" cell is at the old address |
| owner moved to a fresh cell | `inv-c2-owner-moved-fresh.bc`: contents swapped out, new cell allocated, then the old one freed | types | right answer, **1 stale pop**: a read of the freed cell, right only because its key and right-child words were not overwritten |
| the holder moves the owner | `inv-d-holder-moves-owner.bc`: with the state defunctionalised (`i64 + St` in the scheduler's array), the scheduler moves the task's tree to a new cell before every resume | types: `St` is ordinary data | not run (the same mechanism as `inv-c`) |
| …with the state behind ν | `inv-d2-nu-hides-owner.bc` | refused: "`let (x, y) = V` needs a `*` type, but `V : U (delay i32)`": `unfold` hides the state's type, and the machine is affine | — |

**Result: caching is valid only for read-only owners.** Precisely, the cache can stand in for
re-derivation across a step exactly when all three hold:

1. **The state is behind ν** (`unfold`). Then only the machine's own observations touch it, so
   between two observations nothing runs on it. This is a typing fact: the holder sees
   `U (nu X. C)`, which does not mention the state (`inv-d2`), and cannot observe it twice.
   - With the state defunctionalised (`r3`, `p1`, `p2`, `c1d`, H4b), it is not a typing fact. The
     holder may take the owner and mutate or move it (`inv-d`).
   - It would take a whole-program fact that the holder only moves the state.
2. **The owner is behind a stable cell:** its type is `ref A` (or an array handle), and the
   cached positions point into heap cells reachable from it.
   - The state record itself moves at every resume (the step answers the next state by value),
     so a position into an owner held inline in the state would dangle.
   - The type is the typing fact. That a `ref` held across a suspension is a heap object at a
     fixed address is a backend fact, not a typing one: SPEC §29 *Lowering*; §35 frames only the
     scoped cells no suspension crosses.
3. **Every observation uses the owner only through `imm` lends** (`withbor1`, `withload`,
   `slice_borrow_imm`): no `withbor2`, `withswap`, `swap` or `free` of it, and no move of it.
   - This can be read off the typed term, but typing does not imply it. A `mut` lend or an owned
     use is ordinary in a step (`inv-b`, `inv-c`, `inv-c2`).
   - The typing also cannot tell a harmless mutation (a key written in place, which leaves the
     cells where they are) from one that frees cells (a subtree replaced). So any non-`imm` use
     of the owner in a step must drop the cache, and the next step must re-derive.

**Relation to the rules.**
- Under 1–3 the cached state holds a view of an `imm` lend across observations. That is R2's
  shape (`lendLoopR`, SPEC §29): it is in `CDerivesP`, its soundness is `PinLaw.loop`
  (asserted), and the checker does not emit it (U6).
- For the arena, R2 with leaf views would type the cached form.
- For H3's tree it would not: positions below the root still need the same-lifetime child view
  that B1 found missing.

## What is not verified

- **The cached form is unchecked.** `cached_step.c` was written by hand against the
  representation read off the emitted IR: a `Tree` cell is `tag | left | key | right`, and the
  path array is packed 4-byte slots, 256 bytes, enough for 32 pointers at depth 21.
  - That it computes what `adv` computes is argued, then tested on the four runs above and the
    bench (same answer, `live 0`, same allocations).
  - The stale-pop check only tests the popped cell's tag word.
- **The equivalence argument for 1–3 is not mechanised.** It also rests on an `imm` lend leaving
  the cell's contents and every location below it unchanged. The nearest theorem is
  `experiments/FrameTheorems`' `wpTS_footprint` / `imm_call_keeps`: every location the resource
  holds only immutably keeps its value, on the exhibited run and on every run that does not
  allocate. That experiment is on the CBPVWorld-era carrier and builds only at `7de358e^`, not
  at main. It was not re-checked here.
- **B1's kill rests on the absence of a term:** no constant was found that yields a child of an
  `imm` `mu` node at the parent's lifetime, and the update relation is stated to exclude one
  (`imm_view_rejected`). E5's cost was not estimated further.
- **The arena is a different representation from H3's tree.** Its numbers measure caching and
  layout together. The like-for-like caching figure is `p1` against `p1c`.
- **`c2`'s backend failure** (`Layouts`) was not investigated.
- **Not done:** bug injection beyond the two scoping negatives (`b1/neg`); `inv-d`'s cached run;
  a Rust owned-arena variant for `p2`. The reference interpreter timed out at 60 s on `inv-b`
  and on H3's source; LIR and Wasm agree with the answer there.
- **Gate:** `make gate` was not run (targeted checks only).
