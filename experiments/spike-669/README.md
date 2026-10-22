# #669 spike: effects eliminated inside Core, then blessed lowerings

The question: can each of three effectful programs be written by hand as an **effect-free Core term
the kernel accepts**? Effect-free means no `handle`, `perform`, `raise`, row or `tick` remains. The
terms below are `.bc` files in core syntax (with surface `fn`s where they elaborate to plain core). Each
one was run through `bcc check` (the kernel's checker), `bcc interp` (the reference semantics; the
`p3`/`p3b` runs did not finish within 60 s there), `--stage lir`, Wasm (`bcc run --backend new`),
`bcc lir --erasure` and `bcc-counts --backend new`. `results.txt` has every line.

Proof bar (the user's, 2026-10-22): the output must be Core that the kernel re-checks. A rewrite
whose meaning-preservation is unproved is acceptable, since the worst case is wrong semantics, not
memory unsafety. Below, **accepted** (required) and **rewrite proved** (nice to have) are kept
apart.

No kernel change was made. Nothing here is imported by the library.

## Yes/no per program

| program | term | kernel accepts | output = golden | rewrite proved |
|---|---|---|---|---|
| 1 `capture-take-hand` (`for` + `break`, owned cell, finaliser) | `p1-take-hand.bc` | **yes** | yes | the steps are proved machine lemmas; the end-to-end equivalence is not |
| 1b `for-yield-branch` (a looping generator; `break` in a branch) | `p1b-for-yield-branch.bc` | **yes** | yes | the same |
| 2 `gen-fib` (stored generator `U (pull …)`, stepped by hand) | `p2-gen-fib.bc` | **yes** | yes | no: κ defunctionalised into `unfold` |
| 3 `async-tree-iter` (spawn/await, scheduler, `Exhausted` at depth) | `p3-async-tree-iter.bc` | **yes** | yes (sum of the 4 tasks' values) | no |
| 3b the same, with one code per task body as a Core rewrite | `p3b-async-one-code.bc` | **yes** | yes | no |
| 3c the same, with the scheduler holding task states by value | `p3c-async-by-value.bc` | **yes** | yes | no (a library rewrite) |

All of them are accepted as `assurance: unconditional`, at `erased handles 0 performs 0 raises 0
left 0 0`. **The kill criterion was not hit.**

## How each term is produced

**1. A `for` with `break`** (`[handle-last]` shape, SPEC §51). The clause is `work` followed by
`inl y → κ.1 y | inr z → κ.2 (); exit z`.
- *T-B1* (`last_resume_direct`, b2-main `Core/DivHandleLastRuns.lean`): each `perform` becomes a
  call of the work. On `inl w` the producer goes on at `w`.
- *T-B1′* (`last_cancel_direct`, `kappa_cancel_steps`, `cancel_prefix`): on `inr z`, the cancel of
  `κ` becomes the region's finalisers, innermost first (here `free c`), then the exit.
- *H-ret* (`catch_ret`): the producer's end is `inl`.
- In loops 1 and 2 of 1b, the clause is `effHandleT`'s: `tail_resumes` and `kappa_resume_steps` give
  a call of the work, and the copy goes on with its answer.
- A generator that loops is an `unfold` at `Loop` with no row. The caller's body is one machine
  (§14) whose states hold the callee's loop.

**2. A stored generator.** The site's clause keeps `κ`. `κ` is **defunctionalised**:
- its resumption point is a summand of an `unfold` state, carrying the live variables;
- resuming it (`kappa_resume_steps`) is the step's arm for that summand;
- cancelling it (`kappa_cancel_steps`) is the state's `close`, whose finalisers are the drops the
  checker inserts (§12).

The stored generator is `unfold` at `pull i32 0 1`. `take`'s copy for `main`'s site calls the
tail clause's work in place.

**3. An async task.**
- **κ at `await`:** defunctionalised as in 2, into an `unfold` at the task's observation type.
  The rest is boxed (`box top U X`, allowed by `NuOk`).
- **`with spawn`:** runs the task's first segment and answers `boxed[top]` of the machine. Its
  return clause is the finished task.
- **`Exhausted`:** abortive, so it becomes a sum. `descend` answers `Stack + 1` through
  `bounded_fix`'s self-reference, and `on_exhausted` is a `case` (`catch_abort`).
- **The counted loop at a resuming row** is the unfold itself, one turn per observation.
- **The scheduler** in `lib/async.bc` was already effect-free Core over `Task[A]` and is used
  unchanged.

"Suspended at several depths": the `await` is two calls deep (`task` → `tsum` → the loop body),
under an abortive handler. In the state those frames are flat: the `on_exhausted` frame is the
`case d` in the step. A callee that suspends would sit in its caller's state as its machine
(`U (νX…)`), which is how `main_step` in 1b holds each copy's loop. No recursive task (unbounded
nesting) was written; see *Not verified*.

## Resource mapping

Key:
- **(same)**: the same kind of resource in Core;
- **(re-encoded)**: a different kind, with how it changed;
- **(no counterpart)**: Core cannot express it.

**Program 1 (`capture-take-hand`):**

| source resource | effect-free Core |
|---|---|
| owned cell `c` (`ref (1+1)`), live across 3 `yield`s | (same) an owned `ref` in the producer, used once on every path |
| `κ`, affine, linear-ish use (resume or cancel once) | (re-encoded) no value: `κ.1` is "continue after the call", `κ.2` is the `inr` arm. The capture cell (§25) disappears, so no allocation and no `kappaC` |
| the `then`/drop-glue finaliser that frees `c` on cancel | (re-encoded) explicit `free c` in each `inr` arm, the region's finaliser copied to each perform site (size: performs × frames) |
| the handler's threaded variables `(n, stopped)` | (same) a value threaded through the work's argument and answer |

**Program 2 (`gen-fib`):**

| source resource | effect-free Core |
|---|---|
| `κ` at `yield`, affine, stored in `U (pull …)` | (re-encoded) the `unfold` state `inr (a, b)`: `κ`'s live variables as data; `κ.2` is `close` |
| the stored generator `it` passed to `take` | (same) a linear `U (pull i32 0 1)`, observed and closed exactly once |
| `take`'s `break` closing `it` | (same) `(nu_out it).2` on that path |

**Program 3 (`async-tree-iter`):**

| source resource | effect-free Core |
|---|---|
| owned arrays (the stack), live across each `await` | (same) owned in the machine state, dropped by `close` (cancel) or at the end |
| `imm` slice lends of the arrays for each read | (same) opened and closed inside one observation (no lend spans an `await` in the source either) |
| `κ` at `await`, BOXED-κ at `top` | (re-encoded) `boxed[top]` of an `unfold` machine whose state is the live variables |
| the `Exhausted` handler frame between `await` and the task | (re-encoded) a `case` on `Stack + 1` |
| the scheduler's queue of tasks | (same) in 3/3b; (re-encoded) in 3c: by value in an array slot, not a closure |

### Borrows held across a former suspension

The user's encoding is never to store the borrow. It was tested on four programs.

| program | borrow across the suspension | effect-free Core | kernel |
|---|---|---|---|
| `gen-self-borrow` at a `for` site (tail clause) | self-borrow across `yield` | after `tail_resumes` the `yield` is a call; the borrow spans a call (`p4`) | **accepted** |
| `for-lend-resumes` at a `for` site | lend of `a` around a counted walk that `yield`s | the same; the lend spans calls (`p6`) | **accepted** |
| `gen-self-borrow` stored (`U (pull …)`), borrow stored in state | self-borrow in the machine state | `p5`, `p5c` | **refused**: box rule, `s0 : imm 'x i32 + 1 … cannot be shown to outlive 'x` |
| `gen-self-borrow` stored, **owner in state, re-borrow per step** | none stored | `p5b` | **accepted** |
| `async-r1-nested` (R1 under `PinLaw`, `mut` self-lends at 2 depths) | two `mut` self-lends across 2 `yield`s | owners in state, each lend opened again in the observation that uses it (`p8`) | **accepted**, `unconditional` (the source is `PinLaw`-conditional) |
| lend from outside, κ takes the borrow at each resume, lender's scope fixed | `mut 'a i32` passed in and handed back at every `next` | `p9`: `nu X. (mut 'a i32 -o F (mut 'a i32 * (i32 * U X))) & F 1` inside the lend | **accepted** as written |
| lend from outside, a fresh lend for each resume (a queue holds the task across lends) | `forall 'b. mut 'b i32 -o …` per observation | `p9b` | **refused**: `CTy.NuOk` (no lifetime binder in an observation tree) |
| #645/B2's 12 pending lend programs | a lend across a loop's `tick` | 11 are on main as corpus programs, with loops as `unfold` and the lend per observation (§14); all `bcc check` unconditional (`lend-div-iter` exists only on b2-main) | **accepted** (on main) |

Notes on the table:
- **The 12 pending lend programs.** They are untypeable only once loops are `Div`-ticks. If `tick`
  is erased to `unfold` before the kernel re-checks, as main elaborates today, they stay typeable
  with no extension.
- **The re-lend encoding is a program transformation, not a handler law.**
  - It narrows each lend to the observations that use it, re-opened on the same cell. Writes and
    reads happen in the same order, and the cost is the same: `p8` counts 2/0/0/4/4/0, equal to
    Backend2's `async-r1-nested`.
  - It is legal when nothing *derived* from the lend is held across the suspension: a view, a
    reborrow, or an iterator over `&a`. Such a value must itself be re-derived, for example an
    index in place of a view. Turning views into indices automatically is not attempted here.

## Is the translation type-preserving?

Each step above maps a source derivation to one the kernel then gives the output. The rewrite was
done by hand and re-checked; no translation of derivations was written. It is **not
type-preserving** in these places:

1. **A lend open across a stored κ (R1/`PinLaw`, `CDerivesP`).** It has no direct counterpart.
   The output is typeable only through the re-lend transformation, and only when nothing derived
   from the lend crosses the stop.
2. **A lend from outside, re-lent at a fresh lifetime per resume** (a task in a queue that outlives
   each lend). Refused by `NuOk`.
3. **A stored κ whose state holds a borrow of the state's own owner.** Refused by the box rule.
   This is correct: it is a self-reference.

Everything in programs 1–3 is type-preserving in this sense: owned values stay owned, lends stay
inside observations, and κ becomes data or control flow.

## Syntactic linearity after rewriting

Cf. GHC Core Lint and linear types. The kernel accepted every output as written, apart from
surface-syntax fixes (arguments bound to variables, sums ascribed). Four hazards came up:

1. **Let-floating a thunk out of `boxed[…]` turns an accepted term into a refused one** (`p7`).
   - A variable of type `U C` is a leaf of the outlives judgment, so `boxed[top] t` is refused
     where `boxed[top] (thunkv …)` is accepted.
   - The same happens with `f <- return unbang unfold[…]` before a box (`p3` first try). Keeping
     `f` as the persistent `!` value fixed it.
   - A rewriter must not float thunks out of boxes. The kernel alternative: the outlives judgment
     of a variable bound to a value form reads the form's captured context (a let-transparency
     rule for `[]I`). Cost: one premise in the box rule's checker, and `[]I`'s compatibility at a
     let-bound value.
2. **`unfold` needs a `!` step, and `!` does not commute with a lifetime binder.**
   - `!(all 'x. U(…))` instantiates to `U`, not `!U`. A step generic in a lifetime must therefore be
     written inline inside the binder (`p5`, `p9`); it cannot be a shared `def`.
   - Extension: `unfold` at `forall 'x. !U(…)`, or a `def` form that stays `!` after `['x]`. This is
     a growth item: inline steps code-size per site.
3. **T-B1′ copies the region's finalisers to every perform site** (`p1`: `free c` in four arms).
   - The kernel accepts it, because each arm consumes `c` once.
   - Code size is performs × frames. A join point, a `!` function taking the owned values, avoids
     the copies and is ordinary Core.
4. **No case-of-case or inlining step broke linearity here.** The rewrites keep each linear
   variable on exactly one path. Untested: rewrites that duplicate a scrutinee across arms or float
   a `let` of a linear value into a branch. The kernel would refuse those as written: exact use,
   no implicit drop of a non-persistent value.

Prior art, only where it fixes a choice:
- **Tail-resumptive clauses called in place, with their captures passed as arguments:** Koka's
  evidence passing (Xie & Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021).
  Backend2's "frame access by evidence" becomes ordinary arguments in Core.
- **κ taking the borrow at each resume, never storing it (`p9`):** System C's second-class
  capabilities (Brachthäuser et al., *Effects, Capabilities, and Boxes*, OOPSLA 2022). Their
  `box` for escaping matches what `p9b`'s extension needs.

## Extensions (proposals, not built)

None of the three programs needs one. They matter for the cases in the table above.

| | extension | admits | proof obligation |
|---|---|---|---|
| E1 | `NuOk` admits an observation `forall 'b < @. (A_b -o D)`, with `X` in `D`'s results only under `box @c`, `'b ∉ @c` | `p9b`: a lend re-passed at each resume when the machine outlives each lend (a task queue holding a borrowing task) | `Φ_C` monotone through `∀` (the relation already has `∀'x ⊏ @b. C` at every `C`); `unfold`'s map through `allE`/`allI`; the compatibility of `nuIn`/`nuOut`/`unfold` at the wider positivity. The `box` keeps the rest from capturing `'b`, so no new `Ext` reasoning (the #645 class-2 gap) is needed |
| E2 | a lend whose scope is a codata's lifetime, owner inside the machine (spanning lend; §7 *Open*, `experiments/LoopBorrow`, R1 as a Core rule) | stored self-borrows that hold a derived view across a stop | the #645 class 2/3 obligation (validity at every `Ext`-extension); open |
| E3 | the box rule reads through a let-bound value form | rewriter freedom (hazard 1) | `[]I` compatibility at a let; checker premise |
| E4 | a `!` step under a lifetime binder | shared lifetime-generic steps (hazard 2) | `!` and `∀` commuting at `unfold`'s premise |

## Blessed lowerings (draft)

Each lowering reads only the checked term's node and type. It maps each Core value to one
representation and adds no use, copy or drop: those are the term's own (the split masks, the `dtor`
nodes, `close`). It decides representation only.

| lowering | decides | reads | why it cannot change ownership |
|---|---|---|---|
| L1 known call | direct call or inline | `unbang` of a `!` constant; the callee code | a call passes the argument value; the argument's ownership is the term's |
| L2 closure of known code | env record + code pointer; boxed (heap), or unboxed when the class has one code and the value is linear | the closure class (0-CFA), the captured context from the masks | the environment is exactly the captured slots; `U C` is linear, so unboxed storage is never shared |
| L3 tail call | jump / `musttail` | tail position in the term | control only |
| L4 pairs | flat words | `⊗` types | layout only |
| L5 sums | tag + payload, niches | `⊕` types (and the abortive payloads after §47's row-to-sum rewrite) | layout only |
| L6 `μ` data | a node per `roll`, or reuse (`foldReuse`) | `μ` types, `fold*` nodes | allocation follows `roll`/`unroll` one for one |
| L7 cells and borrows | heap cell or frame slot (§35/§50 rule); borrow = address | `alloc`/`free`, `withbor*`, `lendCell` | the extent is the `withbor` callback's; the slot rule asks for the owner's one consumer to be a `free` |
| L8 arrays | base + length | `array` nodes | as L7 |
| L9 codata | `unfold step s` represented as its state + step code (a defunctionalised L2); observation = call of the step | the `unfold` node | the state is the term's value; `close` is the term's |
| L10 `bounded_fix` | loop with budget (§48 `genFix`) | the node | as today |
| L11 in-place reuse | the storage of a consumed linear value (a machine state, a `U` closure) reused for its successor | linearity from the masks; the closure class | the old value is dead by the term's own use |
| L12 finite dispatch | an indirect call over a closure class of known codes becomes a switch | the closure class | control only |

## Counts (allocs / indirect)

Today's Backend2 on main (`corpus/counts-backend2.expected`), against the effect-free terms under
Backend2's existing pure-fragment lowering (which implements L1–L10 and L12 in part, not L11):

| program | main / B2 #665 | #667 / #666 | effect-free term | note |
|---|---|---|---|---|
| `capture-take-hand` | 1 / 0 (1 machine) | 1 / 0 | `p1`: **1 / 0**, no machine | equal |
| `for-yield-branch` | 0 / 0 (6 machines) | 0 / 0 | `p1b`: **0 / 0** | equal |
| `gen-fib` | 0 / 0 (#665: 0 / 21) | 0 / 0 | `p2`: **0 / 0** | equal to main and #667 |
| `async-r1-nested` | 2 / 0 | 2 / 0 | `p8`: **2 / 0** | equal, and unconditional |
| `async-tree-iter` `1000 4` | 8035 / 0 (old backend 8035 / 4004) | #666: 20 / 0 | `p3`: **8024 / 4000**; `p3b`: **8024 / 0**; `p3c`: **9 / 0** | see below |

`async-tree-iter` (the bench's own run includes about 11 allocations of argument parsing and
printing, which the terms leave out):
- **`p3`, the direct translation:** allocations at parity. The 4000 indirect calls are a resume
  through a closure class of two codes (finished task, suspended task). The old backend has 4004.
- **`p3b`:** the two codes as summands of one machine state, a Core rewrite. 0 indirect. This is
  Backend2's `genMerges` lifted into Core.
- **`p3c`:** the scheduler specialised to the one task body, holding each task's state by value
  in an array slot and resuming it in place. **9 allocations**, against #666's 20 for the whole
  bench. Loads and stores are 112,608 / 104,608, against #666's 217,209 / 209,167.
  - This is a rewrite of the scheduler library at one body, not a lowering.
  - For tasks of several bodies, the slot is a sum of the bodies' states, or L2/L12.
  - The 2 allocations per `await` in `p3`/`p3b` are the `unfold` rest closure and the queue's list
    node. L11 (rest in place) removes the first; the scheduler's representation removes the second.

**No program forces an allocation that the current backend avoids.** Where the direct translation
costs more (`p3`'s indirect calls), a Core rewrite (`p3b`) or L12 removes it.

## Convert's effect layer under the split

Backend2's hand lowerings are the templates; their counts are the cost target and their goldens are
the oracle.

| Convert piece | becomes | its Core form |
|---|---|---|
| §47 erasure: `convHandle`, direct-call `perform`, `convWork`/`ensureWork`, rows as payload sums (`ofC`, `payOf`), `effRaise`/`effLet`/`effThen` | **Core → Core rewrite** | a tail clause is a `!` work `def` called at the perform (`p1b`, `p2`); an abortive raise is sum propagation, `F_Σ R ↦ F (R ⊕ P)`, its frames `case` arms (`p3`'s `Exhausted`). The LIR side is L5 |
| `convK`, `genMach`, `performK`, `pointK`, `resumeTm`/`cancelTm` (machines, §49) | **Core → Core rewrite** (defunctionalisation of κ) | the machine state is a Core sum, one summand per resumption point with its live variables; κ is a linear `U (νX. C)` value built by `unfold`; resume is `.1`, cancel is `.2` (`close`, with the frames' finalisers as the checker's drops); a call point's state holds the callee's machine (`p1b` `main_step`); `[let]`/`[then]` frames are data in the state |
| `convDrive`, `genKap` (a `handle` as a drive; κ's code) | **Core → Core rewrite** | the clause runs inline on the machine's observation result; a stored clause's answer is the `unfold` value itself (`p2`, `p3`) |
| `genMerges` (one code per task body) | **Core → Core rewrite** (`p3b`) or **L12** | a sum of the body's codes in one state |
| `tailPass` | **lowering** (L3) | the defunctionalised term's tail calls |
| `cellPass`, `threadedOf` (state cells, §49/§50) | **lowering** (L11), or a Core rewrite holding states by value (`p3c`) | the consumed state's storage reused |
| `lendR` (R1 in a machine) | **no counterpart** without E2 | the re-lend transformation (`p8`) where nothing derived crosses the stop |
| frame access by evidence | **deleted** | ordinary captures and arguments |
| b2-main `lastPerform`, `lastClauseDrive` (`effHandleL` erased) | **Core → Core rewrite** | exactly `p1`: a call of the work, `case`, and a cancel arm running the region's finalisers then the exit (T-B1/T-B1′) |
| b2-main `genIter`/`genIterK` (`iterate` under the runtime or at a machine row) | **Core → Core rewrite**, then L9/L10 | `iterate (f, s)`'s Div tick erased to `unfold` at `Loop` (the §14 machine, main's current form) |
| b2-main `genReify` (`reify_res t`) | **Core → Core rewrite** | `t`'s segments defunctionalised into an `unfold` (`drive_reify_*`, `Core/DivDrive.lean`); the same κ defunctionalisation at `tick` |
| async-task-stack (#666, §52) task stack, κ in the stack region | a **Core rewrite** of the scheduler (`p3c`: state by value in a slot) plus **L8/L11** | a recursive task's frames would be a Core `μ` list or array of frame records (sums per point) in the state; not written |

## Menu

1. **Adopt the split for the three classes tested.** These are tail/last clauses at `for` sites,
   stored generators, and spawn/await tasks with BOXED-κ.
   - The rewrite pass is Core → Core: defunctionalised κ, works called in place, aborts as sums.
     The kernel re-checks its output.
   - The lowering list is L1–L12.
   - Cost: a rewriter over typed terms (hand-checked here), plus L11 and L12 in Backend2.
   - The rewrites are unproved end to end. Their steps are proved machine lemmas: `tail_resumes`,
     `kappa_resume_steps`, `kappa_cancel_steps`, `last_resume_direct`, `last_cancel_direct`,
     `catch_abort`.
2. **Same as 1, plus specialise the scheduler per task body in Core (`p3c`).** This reaches #666's
   allocation count with no task-stack lowering. Open: tasks of several bodies (a sum per queue
   type, or L12 with a closure per task).
3. **Borrows across suspension:**
   - (a) re-lend from owned state, a transformation the rewriter performs when nothing derived
     crosses the stop (`p5b`, `p8`), no kernel change;
   - (b) κ takes the borrow per resume within the lender's scope (`p9`), no kernel change;
   - (c) E1, for a machine that outlives each lend (`p9b`);
   - (d) E2 for derived views across a stop: open research (#645 classes 2/3).
4. **Rewriter hygiene:** forbid floating thunks out of boxes (no kernel change), or E3. Then E4, or
   inline lifetime-generic steps.
5. **Keep `Div` loops as `unfold` before the kernel re-check.** The 12 lend programs then need no
   call-graded rule (#654).

## Algebra

No drift. Handlers stay deep: the copy's work runs at every `perform`, and a callee's machine is
re-entered with the handler applied again. A cancel runs the region's finalisers and no clause of the
region: the `inr` arm reaches no handler. Finaliser raises would propagate as sums; no program
exercises one. Dead-handler escapes and multi-shot are untouched.

## Not verified

- **No rewriter was built.** Every term was produced by hand; the mapping from the effectful
  typed term is described, not implemented.
- **No meaning-preservation proof.** The machine lemmas are proved per step, not as a Core → Core
  equivalence. Defunctionalising κ into `unfold` (programs 2 and 3) has no lemma at all.
- **Not written:**
  - a recursive task (unbounded nesting of suspended calls, `async-tree`, `rec-emit`);
  - handler state (`tail+state`, `answers-two-types`);
  - `resume-or-cancel` clauses beyond `[handle-last]`;
  - finalisers that perform;
  - unrestricted operations;
  - tasks of several bodies in one queue;
  - views held across a stop and re-derived as indices.
- **The blessed lowerings are a draft.** L11 is not built in Backend2. The counts are Backend2's
  existing pure-fragment lowering, not the list.
- **Program 3 is the bench at fixed `1000 4`.** It answers the sum of the values rather than
  printing them; the reference interpreter did not finish `p3`/`p3b` within 60 s; the LIR, Wasm and
  `p3c`'s reference run agree.
- **E1–E4 are proposals.** No proof was attempted.
- `make gate` was not run (spike: targeted checks only).
