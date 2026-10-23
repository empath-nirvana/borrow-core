# Hard problems

Programs a general-purpose language must run, written the way a user would write them. They
are the requirements the design must meet, whatever else the corpus contains. They keep the
corpus from implying that the subset that runs today is the whole problem. A program is in
`corpus/pending/` while it is refused, and moves into the corpus with its golden once it checks
and runs (`scripts/check-corpus.sh` fails when it does).

Each file's header gives the problem, its issue, the intended answer, the Rust equivalent, and
how it fails today. "Fails" below is what `bcc check` says on main. `bcc run --backend old` and
`--backend new` stop at the same message for every pending program here.

| # | program | problem | issue | today |
|---|---|---|---|---|
| 1 | `hard-async-iter-borrowed.bc` | an iterator over a view loaded from a borrowed vector (`&Vec`), at a lifetime of its own, held across `await` | #682 (H8, E2) | refused: an `await` inside the load's callback cannot reach its handler (#161) |
| 1′ | `../async-slice-iter-await.bc` | the same iterator over a view the task is given (`&[i32]`), at the lender's lifetime | #682 | **runs** (`unconditional`, `i32[100]`) |
| 2 | `hard-gen-owned-yields-refs.bc` | a generator that owns a vector and yields views into it (self-reference, a lending generator) | #172, #682 | refused: T1, the lend of `&buf` around a loop that yields |
| 3 | `hard-gen-tree-cursor-borrowed.bc` | a cursor (a stack of child views) into a borrowed tree, held across `yield` | E5 (SPEC §5 *Open*), #682 | refused: a `match` on a borrowed node is not elaborated as a view of its fields |
| 4 | `hard-async-owned-tree-walk.bc` | a task that owns a tree and walks it in order, O(1) per step, without taking it apart | #682 (H3) | refused: T1, the task's borrow of its own tree across `await` |
| 5 | `hard-gen-mutate-owner.bc` | a generator that holds views of its buffer across `yield` and grows the buffer between yields (caching the views is wrong) | #682 (B2.3) | refused: SPEC §14, the iterator holds the borrow between steps |
| 6 | `hard-async-relend-per-resume.bc` | tasks lent `main`'s tally afresh at each resume, `main` reading it between turns | E1 (#669), #682 | refused: `with spawn` may not lend a place declared outside it |
| 7 | `hard-async-mixed-borrowers.bc` | one queue of tasks with different bodies, each holding a borrow of different data, run until empty | #52, #682 | refused: the scheduler's answer cannot be shown to outlive the borrows |
| 8 | `hard-async-nested-lends-view.bc` | three nested lends (record, field, slice) held across `await`, the slice derived from the innermost | #682 | refused: T1 at the outer borrow block |
| 9 | `hard-async-cancel-finaliser-op.bc` | a task holding a lend is cancelled; its finaliser writes through the view and performs an operation | SPEC §27 *Open*, #682 | refused: the surface has no finaliser form (`await` unknown in the core binding form) |
| 10 | `hard-gen-adapters-borrowed.bc` | `zip(filter(…), map(…))` over generators of views of borrowed vectors, run by a `for` | #172, #682 | refused: the generator call passed to `filter` is typed `1` |
| 11 | `../async-two-readers-views.bc` | two tasks holding views (an iterator; two leaf views) of one shared view across `await` | #682, #52 | **runs** (`unconditional`, `[9, 19]`) |
| 12 | `hard-gen-nested-withload.bc` | a generator holding views loaded at two levels (a row, then its elements) across `yield` | #682 | refused: a `yield` inside the inner load's callback cannot reach its handler (#161) |
| 13 | `hard-tree-lookup-borrowed.bc` | a loop whose cursor moves from a borrowed node to its child (no suspension) | E5 (SPEC §5 *Open*) | refused: as 3 |
| 14 | `hard-gen-words-borrowed.bc` | a tokenizer yielding sub-slices of borrowed text, the consumer keeping one | #682 | refused: the generator's elements mention the lifetime of the lend made for the call |

Rows 1′ and 11 run today: a view the task is given, as a family of leaf views at the lender's
lifetime (SPEC §9), may be held across `await` by a task boxed below that lifetime
(`spawn_in`). What does not run is a view derived at a lifetime of its own (rows 1, 12), a
child view at the parent's lifetime (3, 13), and anything that holds a lend across a suspension
(2, 4, 5, 8).
