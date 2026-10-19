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
