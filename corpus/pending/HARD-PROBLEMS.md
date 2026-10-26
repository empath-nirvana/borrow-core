# Hard problems

Programs a general-purpose language must run, written the way a user would write them. They
are the requirements the design must meet, whatever else the corpus contains. They keep the
corpus from implying that the subset that runs today is the whole problem. A program is in
`corpus/pending/` while it is refused, and moves into the corpus with its golden once it checks
and runs (`scripts/check-corpus.sh` fails when it does).

Each file's header gives the problem, its issue, the intended answer, the Rust equivalent, and
how it fails today. "Today" below is what `bcc check` says on main. `bcc run --backend old` and
`--backend new` stop at the same message for every pending program here. Where a program first
meets an obstacle other than its own, the `pending:` line names it first ("first #686").

## The problems

| # | program | problem | issue | today |
|---|---|---|---|---|
| 1 | `hard-async-iter-borrowed.bc` | an iterator over a borrowed vector (`&Vec`, `imm 'a (array i32)`) held across `await` | #682 (H8, E2) | refused at `*x`: the element is typed `1` (#686) |
| 1a | `hard-iter-borrowed-vec.bc` | the same loop with no suspension | SPEC §14 | refused: the iterator holds the borrow over the loop |
| 1′ | `../async-slice-iter-await.bc` | the same iterator over a view the task is given (`&[i32]`) | #682 | **runs**, with scaffolding (below) |
| 1″ | `hard-async-slice-natural.bc` | 1′ and 11 in their natural form: `spawn` + `run_until_empty` inside the borrow | #52 | refused: the scheduler's answer cannot be shown to outlive the borrow |
| 2 | `hard-gen-owned-yields-refs.bc` | a generator that owns a vector and yields views into it (self-reference, a lending generator) | #172, #682 | refused: T1, the lend of `&buf` around a loop that yields |
| 3 | `hard-gen-tree-cursor-borrowed.bc` | a cursor (a stack of child views) into a borrowed tree, held across `yield` | E5 (SPEC §5 *Open*), #682 | refused at `*k` (#686); without `*`, the `unroll` of an `imm (mu …)` (E5) |
| 4 | `hard-async-owned-tree-walk.bc` | a task that owns a tree and walks it in order, O(1) per step, without taking it apart | #682 (H3) | refused: T1, the task's borrow of its own tree across `await` |
| 5 | `hard-gen-mutate-owner.bc` | a generator that holds views of its buffer across `yield` and grows the buffer between yields (caching the views is wrong) | #501 / SPEC §14 first, then #682 (B2.3) | refused by #501's restriction (`for-buf-borrow.bc`), with or without the `yield`s |
| 6 | `hard-async-relend-per-resume.bc` | tasks lent `main`'s tally afresh at each resume, `main` reading it between turns | E1 (#669), #682 | refused: `with spawn` may not lend a place declared outside it |
| 7 | `hard-async-mixed-borrowers.bc` | one queue of tasks with different bodies, each holding a borrow of different data, run until empty | #52, #682 | refused: the scheduler's answer cannot be shown to outlive the borrows |
| 8 | `hard-async-nested-lends-view.bc` | three nested lends (record, field, slice) held across `await`, the slice derived from the innermost | #682 | refused: T1 at the outer borrow block |
| 9 | `hard-async-cancel-finaliser-op.bc` | a task holding a lend is cancelled; its finaliser writes through the view and performs an operation | SPEC §27, U2 | refused: the surface has no finaliser form (`await` unknown in the core binding form) |
| 9′ | `hard-async-cancel-finaliser-op-core.bc` | 9 in the core text, after `async-r1-cancel-finaliser-writes.bc` | SPEC §27 | refused: the finaliser's `perform[2.0]` is at the empty row; the core text cannot write a cancel row |
| 10 | `hard-gen-adapters-borrowed.bc` | `zip(filter(…), map(…))` over generators of views of borrowed vectors, run by a `for` | #172, #682 | refused: the generator call passed to `filter` is typed `1` (#686) |
| 11 | `../async-two-readers-views.bc` | two tasks holding views (an iterator; two leaf views) of one shared view across `await` | #682, #52 | **runs**, with scaffolding (below) |
| 12 | `hard-gen-nested-withload.bc` | a generator over a borrowed vector of vectors, holding views loaded at two levels across `yield` | #682 | refused at `*x` (#686) |
| 13 | `hard-tree-lookup-borrowed.bc` | a loop whose cursor moves from a borrowed node to its child (no suspension) | E5 (SPEC §5 *Open*) | refused: as 3 |
| 14 | `hard-gen-words-borrowed.bc` | a tokenizer yielding sub-slices of borrowed text | #682; closer to #54 | refused: the elements mention the lifetime of the lend made for the call |

### Coverage beyond #669's cases

| program | problem | issue | today |
|---|---|---|---|
| `hard-gen-move-suspended.bc` | a suspended self-borrowing generator moved between resumes (into a call, into a pair, back) | #172 | refused: T1 in the generator |
| `hard-gen-self-borrow-close.bc` | a self-borrowing generator closed early, by `take` and by `break` | #172 | refused: T1 in the generator |
| `hard-gen-tree-recursive-borrowed.bc` | a recursive generator over a borrowed tree (H1 × borrows), the natural spelling of 3 | E5, #682 | refused at `*k` (#686) |
| `hard-tree-insert-mut-cursor.bc` | BST insert by a loop whose `mut` cursor moves to a child (E5 at `mut`) | E5 | refused at `modify key`: the binder is typed `1` (#686) |
| `hard-gen-pinloop.bc` | PinLoop: a self-borrow made once and held across the observations of an endless generator | #172 | refused: T1 at the borrow block |

### Kernel gaps of the R5 fallback (#680)

| program | problem | issue | today |
|---|---|---|---|
| `hard-async-stream-awaits.bc` | an asynchronous stream: a generator that awaits before each `yield`, read through `take` inside a task, so each observation of the stored generator performs `await`, handled by the enclosing `spawn` | #691 | refused at `take(feed(n), want)`: a generator that performs operations besides what it yields has no stored generator |
| `hard-async-two-schedulers.bc` | a suite of jobs taken from a list, each run under `spawn` (answer `Task[i32]`) and `spawn_logged` (answer `Stopped[i32]`): a first-class computation forced under two handlers of `Async` with different answer types | first #161, then #692 | refused at the list's first element: a function that performs `Async` passed as a value (#161) |
| `../async-two-schedulers.bc` | the same harness with one named job | #692 | **runs**: `trial` is specialised at its call, so no first-class computation is forced |

### Implicit copies of `imm` views

| program | problem | issue | today |
|---|---|---|---|
| `hard-imm-view-copy.bc` | a shared view used twice (`*x + *x`, one view passed to two calls) | #58 | refused: `x` is used twice and is not persistent |
| `hard-filter-views.bc` | `filter` over a generator of views: its predicate takes a view, and `filter` then yields it | #58 | refused first by SPEC §14 (the `for` drains a generator holding the view); stored with no loop, at #686 |

This is a requirement of its own. Once their own obstacle is gone, rows 3, 4, 10, 13 and 14 still
use a view twice: `cons(cur, todo)` after `match cur`, `*key` twice, `filter`, and `len(w)` twice.
A Rust user expects `&T: Copy`. The intended form is a `copy['a, A]` that the elaborator inserts and
the kernel checks, as it inserts `&`. Row 7's explicit `copy['t, i32] e` is a workaround this
would remove.

## What runs today, and what it needs

Rows 1′ and 11 run (`assurance: unconditional`, every stage). Each task is given a family of leaf
views at the lender's lifetime (SPEC §9) and holds them across `await`; no lend is held across a
suspension. They need scaffolding that a user would not write:

- a unit cell `d = alloc(())` lent `mut`, only to make a scope `'d` strictly below the borrow;
- `spawn_in`, which boxes each task at `'d`;
- `run_in(q, 8)` under `on_exhausted`: a bounded number of rounds, so that the scheduler runs
  inside the borrow (`run_until_empty` is unbounded).

Without the `'d` cell, `spawn_in` is refused at the clauses' box. The natural form, `spawn` and
`run_until_empty` inside the borrow, is row 1″, refused.

What does not run:
- a view loaded from a borrow of a vector, at a lifetime of its own (1, 1a, 12);
- a child view at its parent's lifetime, `imm` or `mut` (3, 13, the recursive walk, the insert);
- anything that holds a lend across a suspension (2, 4, 5, 8, the move, the close, PinLoop).

## The `1` fallback (#686)

Rows 1, 3, 10, 12, 13 and the recursive walk and insert are first refused by one elaborator bug:
an expression it cannot elaborate is typed `1`, and the error is reported later, about the `1`.
#686 has the reproductions. The programs keep their natural spellings and record that message
until it is fixed; their headers name the obstacle behind it.

## Reject files for the same class

- `corpus/reject/gen-self-borrow.bc`: a generator holding a borrow of its own local across `yield`.
- `corpus/reject/for-lend-resumes.bc`: a `for` over `&a` whose body yields.

Both pin today's T1 message, and both say "rejected today; intended to run: pending #172,
`hard-gen-owned-yields-refs.bc`". When #172 lands, the gate reports them accepted: move them to the
corpus then.

## Out of scope

#669's H6 (handler state) and H7 (a dropped task) are not here. They are not structural: both have
kernel-checked forms with no extension (#669's hard cases).
