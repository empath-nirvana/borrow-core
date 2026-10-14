# Tier 2: the separate problems

"Tier 2" has been used for several different problems at once, and work on one kept being read as
progress on another. This page separates them. Each problem gets:
- a statement;
- the test programs;
- whether it is really about effects;
- what is known;
- what counts as solved;
- what it depends on.

Proofs are in Lean against Core. "Solved" always includes the fundamental property and adequacy
holding over whatever relation the solution uses, every borrow guarantee, and every corpus and
kernel program running with the same output.

## A. An operation that crosses a borrow's scope, inside the scope

**Statement.** A borrow block's body performs a *resuming* operation (`yield`, `await`, a state
operation) whose handler lies outside the block. Every continuation that holds the borrow is
resumed or cancelled before the block ends. Lifetimes still nest:
- a borrow the handler opens is opened after the block's borrow and closed before the
  continuation resumes;
- a stored continuation that holds the borrow has a type that mentions the borrow's lifetime, so
  the existing outlives rule keeps it inside the scope.

Today such a body may perform only aborting operations (SPEC §19, T1).

Interleaving is not in A. Suppose two tasks each borrow their own local across an `await`, and a
scheduler interleaves them: task 1 borrows at `'x1` and suspends, task 2 borrows at `'x2` and
suspends, then task 1 resumes and ends `'x1` while `'x2` is live. That breaks nesting, so it is B.

**Test programs.**
- `corpus/reject/gen-self-borrow.bc`: an `imm` borrow of the generator's own local, live at a
  `yield`, consumed by `for`. It moves to the accepted corpus with its output.
- The same program at `mut` (to write: `borrow mut c` and a write through the borrow after the
  `yield`).
- `corpus/pending/async-borrow.bc`: two tasks read one borrowed list and are awaited before the
  borrow ends. The continuations are stored, but inside the scope.
- The reader object: `Log` handled outside a counter's borrow, with a value read through the
  borrow live at the operation (to write).
- Cancellation: an affine continuation holding the borrow is cancelled. Finalisers run, and the
  borrow ends (to write).

**About effects?** Yes, but shallowly. The borrow rule is proved by running the body to
completion under a frame; the work is extending that proof to bodies that stop at an operation
and later resume or are cancelled.

**Known.**
- The lenders' side is proved for straight-line bodies: `law2_straight` on branch
  `law2-typed-world`.
- A derivation-indexed judgment covers 59 of Core's 91 typing rules: `pj_fundamental`, with 32
  enumerated `sorry`s and none refuted.
- A pure call that returns a view across a stop is proved (`view_call_spans`).
- For `mut`: Core's effect-aware weakest precondition does not allow a run to stop holding a
  newly created `mut` cell. So a `mut` borrow live at a stop must be ended at the stop and
  re-made on resume (GhostEnd's `Relend`), or the weakest precondition must change.
- Whether the `imm` case needs anything beyond the frame lemma at a resuming operation has not
  been checked.
- The probes' target statements drifted (answer types without closures, a slot-by-slot context).
  The statements below are the ones to prove.

**Solved when:**
- The compatibility lemmas of the borrow rules (`withbor1/2/3`, `withload`, `withswap`, the slice
  borrows) hold when the body performs resuming operations whose continuations stay inside the
  scope, against Core's own context relation, with no restriction on answer types.
- T1 is lifted in the checker for exactly that class.
- The test programs run.

**Depends on:** nothing below. Order: `imm`, then `mut`, then cancellation.

## B. A borrow that lives as long as a value, not a scope

**Statement.** A value owns a place and also holds a borrow of that place, and the value outlives
the scope it was created in. In the model every lifetime belongs to a dynamic scope, so there is
no way to say "this borrow lasts as long as this value". Physically nothing is wrong: moving the
owner does not move the location.

**Test programs** (none written; all without effects first):
- A struct owning a buffer and a borrow into it, returned from the function that built it, then
  read.
- A closure owning a cell and a borrow of it, returned and later called.
- With effects, after A: a generator holding a borrow of its own local, stored and returned from
  the scope that created it, then resumed elsewhere.
- With effects, after A: two interleaved tasks, each holding a borrow of its own local across an
  `await`.

**About effects?** No. It is a borrow-calculus problem; Rust has it too (`Pin`, `ouroboros`). A
stored continuation is one instance.

**Known.**
- Moving a region's lifetimes by an order embedding breaks the relation: `not_reslotInvC`, at a
  borrow of a borrow. This holds on every lifetime carrier: `no_fsCarrier`, `carrier_iff`.
- Re-making the borrows at fresh lifetimes preserves the relation at every first-order type at
  any depth (`relend_fov`), and for every term the fundamental property relates (`semD_relend`).
- The natural construct is a package `∃'x. (own c, borrow of c at 'x, what was built from it)`:
  - opening it picks a fresh `'x` beneath the current stack;
  - closing it ends the borrow;
  - between openings no borrow is live.

  This is the re-make, phrased as unpack and repack. It has not been defined or tested.

**Decided (2026-10-14): the closed package, with history bookkeeping.**
- A suspended self-borrow is ended while the value is stored. The package holds only owned cells,
  plus contents typed abstractly in `'x`. It is re-made at a fresh lifetime on each opening.
- Lifetimes stay the model's well-founded measure: no step-indexing.
- The reason: stratification is ordered by ancestry. A `mut` cell's witness must strictly outlive
  it, so a *live* self-borrow at a hidden `x` can never sit under a `mut` cell at `'q`, whatever
  shape the lifetime order has. A scheduler could then not store a self-borrowing task in a
  mutably borrowed queue. A closed package has no cell at `x`, so it can.
- The cost is accepted: re-making at function types holds for what typed programs build, not
  pointwise, so the proofs carry a derivation-indexed invariant (as in problem A's work).

**Solved when:**
- A package construct, or another one, is in the kernel with typing rules.
- Its compatibility lemmas are proved.
- The fundamental property and adequacy hold.
- The test programs run.
- Stored generators lower to it on top of A.

**Depends on:** nothing. It can be done without effects, in parallel with A.

## C. Borrows that escape in a payload (lending iterators)

**Statement.** A suspended computation hands out a borrow of its own state: a generator yields
`&self.buf[i]`. The consumer holds that borrow while the generator is suspended, and resuming
must end it.

**Test programs** (to write): a lending iterator over a buffer the generator owns; an adapter
composed over one.

**About effects?** Partly. Without suspension this is "`&mut self` returns a borrow of its own
state", which Core's reborrow rule already handles. With suspension it is a reborrow out of a
B-package.

**Known.** Nothing beyond the prior-art note: shipped designs allow this only while the resumer
holds the suspension exclusively (Swift's accessors, Rust's async closures).

**Solved when:** the test programs type and run, with the reborrow rule's compatibility lemma
proved at a package.

**Depends on:** B.

## D. The model admits junk that is sensitive to lifetime spacing

**Statement.** The relation accepts some values no program builds, and whether it accepts them
depends on how many lifetimes lie between two others, not just their order. Any proof that
re-assigns lifetimes fails on these values.

**Witnesses** (none is a program):
- `coreAllAdjacent`: a lifetime-polymorphic function that returns a fixed borrow.
- `core_not_relend_kU`: a closure from a type that is empty when two lifetimes are adjacent.

**About effects?** No, and not about the language: it is a property of the proof technique. It
matters only to proofs that re-assign lifetimes: B, and A's `mut` case if that ends and re-makes
borrows.

**Known.** Every term the fundamental property relates is unaffected (`semD_relend`). There are two
ways to handle it:
- track what typed programs build (a derivation-indexed invariant);
- change the representation so the relation cannot see spacing, for example cells that store a
  type and a lifetime environment instead of a semantic predicate.

**Solved when:** inside B (or A), every lemma that re-assigns lifetimes is stated over
configurations that typed programs build, or the relation is changed so it cannot see spacing.
This is not a separate deliverable.

## E. An owned resource held across a cancellable stop

**Statement.** A generator holds a linear resource that has no destructor (an output capability)
across a `yield`. A consumer that stops early cancels the continuation. Cancel answers `()`, so
the resource cannot come back.

**Test programs:** `corpus/pending/gen-lazy.bc`, `gen-digits.bc`, `gen-adapters-io.bc`,
`gen-lines.bc`.

**About borrows?** No. It concerns what a cancel returns (K3).

**Known.** No surveyed system has a cancel that hands back an owned value. The decided algebra
has cancel answer `()` (finaliser decisions), so solving this changes a decided point and needs a
decision first.

**Depends on:** a decision on what cancel may return.

## Not tier 2: the effect algebra without borrows

- Row polymorphism (Law 1, OA4): effectful callbacks, `corpus/pending/yield-callback.bc` (#161),
  `bench`, `compose`.
- The handler laws (h1–h4): `TailLaw`, `AlgLaw`, `EtaHold`, models and comodels, equations in
  signatures.

Neither involves borrows; both are in [the effects algebra](foundations/effects-algebra.md).

## Order

1. A at `imm`, then `mut`, then cancellation.
2. B, without effects, in parallel with A.
3. C after B; stored generators as A plus B.
4. E when its decision is made.

The algebra tracks run independently of all of these.
