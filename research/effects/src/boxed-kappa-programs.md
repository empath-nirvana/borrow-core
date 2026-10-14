# BOXED-κ against its programs: P4 with stored continuations, and ν rests (P2b)

This page takes the rule proved in `experiments/BoxedKappa` and asks two questions of it:

1. **P4 redone.** Can interleaved tasks be stored as plain handler continuations in a queue lent
   `mut` at `'q`, instead of being hand-written as `ν` state machines with boxed rests
   ([B on paper](b-package-typing.md), P4)?
2. **ν rests.** Can a `ν` observation's rest be typed `[@d] U X` when the state outlives `@d`,
   and does that rescue P2b?

What is machine-checked, what was run by `bcc`, and what is checked by hand only is marked on
each claim. The three kinds stay separate:

- **Proved**: a Lean theorem in `experiments/BoxedKappa/BoxedKappa/Programs.lean`, `lake build
  BoxedKappa`, no `sorry`, axioms within `[propext, Classical.choice, Quot.sound]`.
- **Checked**: accepted or rejected by today's `bcc check`, files in `experiments/BoxedKappa/bc/`.
- **By hand**: a derivation written here and not checked by a machine.

## 1. The rule and the spawn handler

**BOXED-κ** (`handle_compatCB`, `handleV_compatCB`, proved) is `[handle]` with each capturing
clause at `!U(A ⊗ [@d] K ⊸ F_Σ R)`, plus two premises on the handled computation `e : F_{E_n ⊕ Σ} A`
under `Γ₂`:

- `CtxOutlives Δ Γ₂ d`: `Δ ⊨ @d`, and every live slot of `Γ₂` outlives `@d`;
- `Row.AnsOutlives Δ d (E_n ⊕ Σ)`: every non-abortive answer type outlives `@d`.

Nothing is asked about what is live at a stop. The stop lemma derives that the continuation's
share is in `Res_{δ(d)}` from the start context and the answers.

BOXED-κ is a compatibility lemma, not a `CDerives` constructor. So no checker accepts a handler
whose clause has the boxed type. That fact was checked:

- a clause with a bare `κ` that boxes the task it answers is rejected at `boxed[top]`: *"`k`, of
  type `U ((1 -o F …) & F 1)`, is used inside, and it cannot be shown to outlive `top`"*;
- a clause typed `!U(1 ⊗ [@⊤] K ⊸ F E)` passed to `handle_with` is rejected, read as the clause
  of an abortive operation whose argument is `1 ⊗ [@⊤] K`.

(Both were diagnostic files, not committed.)

**The effect.** `await` is the operation `1.0 : 1 ↠^aff 1`, affine so that a stored task can be
cancelled.

**The task type.** A stored task answers its next observation with a value or with the rest:

    Task^d ≜ U(νX. F(i32 ⊕ [@d] U X) & F 1)        E^d ≜ [@d] Task^d

- `next` resumes the task to its next `await` and gives `inr` of the rest, or gives `inl v` once
  it has finished.
- `close` cancels it.
- `Task^d` is positive at every `@d` (`taskBodyG_nuOk`, proved): `[@d] U X` is a polynomial
  position by `VTy.Poly`'s box case (SPEC §22). [B on paper](b-package-typing.md) left this
  open.

**The spawn handler** (`bc/spawn-handler.bc`, checked as a value; the type matches BOXED-κ's
clauses exactly, `handler_shape`, proved):

    h_ret = !λv. boxed[@d] (thunk nu_in ⟨return (inl v), return ()⟩)
    h_await = !λ(u, bk). boxed[@d] (thunk nu_in ⟨k ← unbox bk; r ← (force k).1 (); return (inr r),
                                              k ← unbox bk; (force k).2⟩)
    spawn = !λtb. handle_1 (tb ()) with (h_ret, (h_await, ()))

    spawn : !U([@d] U(1 ⊸ F_{await} i32) ⊸ F E^d)

`spawn` runs the task's code to its first `await` and answers the stored task.

| step | rule | side condition | holds |
|---|---|---|---|
| `h_ret` | `lam`, `boxI`, `thunkV`, `nuIn`, `withI`, `sumI₁` | `boxI`: `CtxOutlives {v : i32} @d` | `VOutlivesR.int` |
| | `nuIn` | `NuOk` of `Task^d`'s body | `taskBodyG_nuOk` |
| | `withI` | `v` dropped in the `close` branch | `i32` is persistent |
| `h_await` | `tensorE`, `unitE`, `boxI` | `boxI`: `CtxOutlives {bk : [@d] K} @d` | box rule: `Δ ⊨ @d ⊑ @d` (non-strict, SPEC §23) |
| | `boxE`, `force`, `proj₁`/`proj₂`, `app`, `sumI₂` | `K = U((1 ⊸ F E^d) & F 1)`, `kTy [] E^d aff 1` with the empty cancel row | by `clausesTyB`'s definition |
| `spawn` | BOXED-κ | `[handle]`'s: `n = 1 ≠ 0`, `n ∉ Σ = []`, the pair a value form over a dead context | ✓ |
| | | `CtxOutlives {tb : [@d] Code} @d` | box rule, `Δ ⊨ @d ⊑ @d` (`run_ctxOutlives`) |
| | | `AnsOutlives`: `await` answers `1` | `VOutlivesR.unit` (`await_ansOutlives`) |

So **the premises of BOXED-κ hold for `spawn` at every `@d`**, because the task arrives as boxed
code. What decides whether a task may be stored at `@d` is the `[]I` that boxes its code, over
the code's captures. If the handler is written around the task's body instead of being taken as
a function, that same condition is BOXED-κ's `CtxOutlives` premise, over the body's context.

## 2. P4 redone with BOXED-κ

### The program

*Hypothetical surface* (`async` is not built, #52):

    fn task1() -> i32 with Await =                 -- owns its local, borrows it around two awaits
      let c = alloc(10);
      let v1 = *&c; await(); let v2 = *&c; await(); let v3 = *&c;
      v1 + v2 + v3 + free(c) + 90                  -- 130
    fn task2(k: imm 'r i32) -> i32 with Await =    -- variant (b) only: an outside borrow
      …
    main =
      let q = queue();                             -- ref Q
      push(q, spawn(task1)); push(q, spawn(task2));
      run_until_empty(q)                           -- each step lends q mut at a fresh 'q

*Core.* The programs are written in the core text and checked:

| file | variant | `bcc check` |
|---|---|---|
| `bc/spawn-handler.bc` | the handler's pair, at `@d = ⊤` | accepted |
| `bc/sched-a.bc` | (a), driven by a bounded driver (for the Lean run) | accepted |
| `bc/sched-a-div.bc` | (a), the run-until-empty loop handed back undriven | accepted |
| `bc/sched-b.bc` | (b), bounded scheduler inside `'r` and `'d` | accepted |
| `bc/sched-b-div.bc` | (b), run-until-empty loop handed out of the blocks | rejected at `boxed['d]` |
| `bc/sched-c-equal.bc` | (c), `@d = 'r` | rejected at `boxed['r]` |
| `bc/sched-c-outside.bc` | (c), `'d` opened outside `'r` | rejected at `boxed['d]` |

In each scheduler file `spawn` is a parameter of `main`, because the checker cannot type it.

**The borrow across `await`: ADD-5, the degenerate case.** In every task the only value at a type
mentioning the borrow's lifetime that would cross an `await` is the lend itself. So each stretch
that uses the borrow is its own `withbor` (`peek`, `bump`). The task holds its owned cell across
the `await`, and the checker inserts the drop glue (`[then]`, finaliser `free c`) as for
`corpus/core-effects-drop-glue.bc`. **No package is needed.**

What a package would change, if derived state crossed an `await` (P6′'s leaf view): ADD-1, ADD-2
and ADD-4 as in [B on paper](b-package-typing.md). BOXED-κ adds nothing to that, because its
premises look at the task's start context and at answer types, not at what is live at the
`await`. A closed package created inside the task needs no outlives rule to sit in a stored
continuation. The stop lemma places the whole share in `Res_{δ(d)}`. *Believed, not checked:*
Core has no package.

**The queue and the scheduler** (`sched-a.bc`).

- `L ≜ μY. 1 ⊕ (E ⊗ Y)` is a list of stored tasks, and `Q ≜ (L ⊗ L) ⊗ bool` holds a front list,
  a back list, and whether the scheduler is moving the back to the front. That makes it a FIFO
  with no recursion.
- The scheduler is `unfold` at `loop i32 1`, over the state `ref Q ⊗ i32`: the queue's owner and
  an accumulator.
- Each observation:
  1. lends the owner at a fresh `'q` (`withbor2`);
  2. takes the contents out with `withswap['q]`;
  3. does one move: step the front task (`nu_out (force (unbox t)).1`), or move one task from the
     back to the front, or finish when both lists are empty;
  4. puts the contents back and ends the lend.
- A finished task's value `v` is folded in as `acc·1000 + v`, so the order of completion shows in
  the answer.
- `close` frees the queue and closes every task left (`fold_own`, each task's `close` cancelling
  its `κ`).

This is `LoopLend`'s per-observation lend (SPEC §14), written inline.

### Variant (a): both tasks borrow only their own locals

`@d = ⊤`. `Δ = ∅` throughout, except inside the borrows, where `Δ` gains `'x ⊏ ⊓Δ` or `'q ⊏ ⊓Δ`.

| step | rule | side condition | check |
|---|---|---|---|
| task 1's segments | `withbor1` | `'x` fresh, `VScoped ∅ i32`, `'x ∉ FV(i32)` | ✓ |
| | `withload`, `boxI` at `'z`, `'x` | `i32 ⊐ 'z`, `i32 ⊐ 'x` | `int` |
| | `effPerform` at `1.0` | not abortive (`1` is not `0`) | ✓ |
| | `effThen` (inserted) | `c : ref i32` live across an affine operation; finaliser `free c` at the pure row; `NZ`, `Uniq` | ✓ |
| task 2's segments | `withbor2` | side condition `∃b. Δ ⊨ b ∧ i32 ⊒ b`, `b = ⊤` | `int` |
| | `withswap`, `forgetMut` | none | ✓ |
| boxing the code | `boxI` at `⊤` over `(unbang task1)` | `CtxOutlives ∅ ∅ ⊤`: `Δ ⊨ ⊤`, no live slot | ✓ |
| spawning | BOXED-κ at `⊤` (via `spawn`) | as in §1 | ✓ (proved) |
| the queue | `roll` at `L` | `L.NoMut 0`, `L` closed | ✓ |
| the lend of the queue | `withbor2['q, ⊤, Q, i32 ⊕ i32]` | `∃b. Δ ⊨ b ∧ Q ⊒ b`: `b = ⊤`; `Q`'s only lifetime is `E`'s box, `Δ ⊨ ⊤ ⊑ ⊤` | ✓ |
| | | `'q` fresh, `'q ∉ FV(Q)`, `'q ∉ FV(i32 ⊕ i32)` | ✓ |
| | callback's result `boxed['q] res` | `i32 ⊕ i32 ⊐ 'q` | `int` |
| stepping a task | `boxE`, `force`, `nuOut`, `proj₁`, `sumE` | `NuOk` of `Task`'s body | ✓ |
| the scheduler loop | `unfoldN` at `loop i32 1`, `nuIn`, `nuOut` | `loopBody_nuOk` | ✓ |
| `close` | `foldOwn` over `1 ⊕ (E ⊗ X)` | `F.WF`, `F.Guarded` | ✓ |

**Run-until-empty types.**

- The loop's type `U(loop i32 1)` mentions no lifetime. So it leaves every scope, and a `main`
  that loops hands it to the runtime, which drives it until the queue is empty (SPEC §11, §14).
  `sched-a-div.bc` returns that loop and is accepted.
- `sched-a.bc` drives it with a unary-count driver (at most 16 observations; by hand it needs 13), only
  because a closed `main : F i32` is total and the Lean run needs a value.

**Machine-checked end to end** (`Programs.lean`):

- `spawnBody_sem`: `spawn`'s body by `handleV_compatCB`.
- `prog_sem`: the program `f ← main_sched; f spawn` at `F i32`. The checked parts come through
  `fundamentalC`, and `spawn` through `handleV_compatCB`.
- `prog_every_run`: every run from the empty memory continues to an `i32` at the empty memory
  (`theorem32D`).
- `prog_eval`: the interpreter answers `41130` with no cell left. Task 2 finishes first (`41`),
  then task 1 (`130`). Running task 1 to the end first would give `130041`.

**Verdict (a): TYPES WITH ADDITION** BOXED-κ, as the `[handle]` variant, which is a compatibility
lemma and not a `CDerives` rule. ADD-5 is used in its degenerate case, so there is no package and
no other kernel change. The scheduler runs until the queue is empty. The queue is under `Mut 'q`.

### Variant (b): one task captures an outside `imm 'r`

`sched-b.bc`.

- `cfg = 42` is lent `imm` at `'r`.
- Inside that, a unit cell is lent `mut` at `'d`, the queue's bound, as `corpus/aff-capture.bc`
  names its `'w`. So `Δ = ('d ⊏ 'r), ('r ⊏ ⊤)`.
- Task 2 takes `k`, copies it, reads through one copy before its `await`, and **holds the other
  copy across the `await`**. It also owns a cell, which it bumps.
- Everything else is (a)'s, at `'d` in place of `⊤`. The types become `Task<'d>`, `E<'d>` and
  so on, and each `def` is `all 'd < top.`.
- `spawn` is a parameter at every bound: `!(all 'd < top. [@'d] Code ⊸ F E^'d)`.

| step | rule | side condition | check |
|---|---|---|---|
| boxing task 2's code | `boxI` at `'d` over `{k : Imm 'r i32}` | `Imm 'r i32 ⊐ 'd`: `Δ ⊨ 'd ⊏ 'r` (the `Imm` rule, strict) | ✓ (`'d ⊏ ⊓Δ = 'r`) |
| spawn's instance | `allE` | `Δ ⊨ 'd ⊏ ⊤` | ✓ |
| | BOXED-κ at `'d` | `CtxOutlives {tb : [@'d] Code} 'd`: box rule `'d ⊑ 'd`; `AnsOutlives`: `1` | ✓ (by hand; see below) |
| task 2 across `await` | `[let]`/`[then]` at the affine row | `k2 : Imm 'r i32` and the owned cell live across the `await` | ✓ (accepted by the checker) |
| | T1 | the `perform` is in task code, handled by `spawn`'s handler inside the callbacks, whose rows are pure | not involved |
| the queue's lend | `withbor2['q, 'd, Q<'d>, …]` | `∃b. Δ ⊨ b ∧ Q<'d> ⊒ b`: `b = 'd`, box rule `'d ⊑ 'd` | ✓ |
| the result | `boxI` at `'d`, `'r` | `i32` | ✓ |

**If the task is spawned in place** (the handler written around task 2's body, its context
`{k : Imm 'r i32}`), BOXED-κ's premise reads `CtxOutlives Δ {k : Imm 'r i32} 'd`, and that holds
**iff `Δ ⊨ 'd ⊏ 'r`** (`ctxOutlives_imm_iff`, proved).

So variant (b) types **iff `'r` strictly outlives the queue's bound**, which is what was asked:

- the generic `spawn` checks it at the `[]I` forming the code;
- an in-place spawn checks it at BOXED-κ;
- either way, the condition is `'d ⊏ 'r`.

The stop lemma's reading: `k2`'s cell, held in the stored continuation, is in `Res_{δ('d)}`
because `δ('d) < δ('r)`.

**Run-until-empty does not type.** `sched-b-div.bc` is rejected at `boxed['d]`: *"`l`, of type
`U (delay i32)`, is used inside, and it cannot be shown to outlive `'d`"*. The loop has to be
driven to the end somewhere, and nowhere works:

- **Inside the blocks of `'r` and `'d`**: a borrow block's callback is a computation `F(['x] B)`
  that returns. A closed div-free computation terminates (`Core/Totality.lean`), so code inside
  the block can observe the loop only a bounded number of times.
- **Outside the blocks**: the loop must leave them, and `U` has no outlives rule
  (`aff_not_outlives`'s reason). Boxing the loop would need its state to outlive `'d`. But the
  state holds task 2, which holds `k : Imm 'r`, and the state's type mentions `'d`.
- **At `main`'s lifetime**: a `main` that names `'main` has type `F A` (`mainLife`), so it cannot
  loop.

What run-until-empty needs here is **a lend that spans the loop's observations**: `'r` (and
`'d`) open while the runtime drives the loop. That is the spanning lend of SPEC §14 and
`experiments/LoopBorrow`, a model change that has not been verified. `LoopLend`'s per-observation
re-lend covers the queue's `'q` but not `'r`: a stored task holds `k` across observations, so `'r`
cannot be re-made per observation.

Two notes:

- The same holds for **any** `@d ≠ ⊤`, even with no captured borrow, since the queue's type
  mentions `@d`.
- So, in Core today, **a scheduler that runs until its queue is empty can hold only tasks
  bounded by `⊤`**. This is the analogue of the `'static` bound on Rust's `tokio::spawn`. That
  conclusion is by hand, from the three facts above. `sched-b-div.bc` is one checked instance.

**Verdict (b):**

- **TYPES WITH ADDITION** BOXED-κ when the scheduler is bounded (`sched-b.bc`, a fixed driver of
  16 observations), **iff `Δ ⊨ 'd ⊏ 'r`**.
- Run-until-empty **DOES NOT TYPE**: it needs the spanning lend.
- Also needed: a scope only to name `'d` (a borrow of a unit cell), since the box rule is
  non-strict but the `Imm` rule is strict. This is SPEC §23's *a lifetime without a cell*.

This changes the program the brief asked for. **Original:** run until the queue is empty.
**Change:** at most 16 scheduler moves, inside the blocks. **Why:** run-until-empty is the
rejected `sched-b-div.bc`, for the reason above.

*Not run.* `sched-b.bc` is checked, but neither interpreted nor proved in Lean. `bcc` cannot run
a program whose `spawn` is a parameter, and the Lean composition of (a) was not repeated for a
`spawn` polymorphic in `'d`. Its answer, if run, would be `87130`, computed by hand.

### Variant (c): the captured borrow does not outlive the queue's bound

| file | arrangement | rejected by | message |
|---|---|---|---|
| `sched-c-equal.bc` | `@d = 'r`: the queue bounded by the captured borrow's own lifetime | `[]I` (`boxI`'s `CtxOutlives`), the `Imm` rule of `VOutlives`: `Δ ⊨ 'r ⊏ 'r` | *"`k`, of type `imm 'r i32`, … cannot be shown to outlive `'r`"* |
| `sched-c-outside.bc` | `'d` opened outside `'r`, so `'r ⊏ 'd` | the same rule: `Δ ⊨ 'd ⊏ 'r` fails | *"… cannot be shown to outlive `'d`"* |

- **Spawned in place**, both are BOXED-κ's `CtxOutlives` premise.
- **At `@d = 'r`** the premise fails at every satisfiable `Δ` (`not_ctxOutlives_imm_self`,
  proved).
- **Picking another bound for task 2**, `'e ⊏ 'r`, gives it type `E<'e>`, which is not
  `E<'d>`. The `withswap` callback that pushes it does not type.
- **The rejected variant of [B on paper](b-package-typing.md) P4**, a task made inside `'q`'s
  scope over `k2 : Imm 'r2` with `'r2 ⊏ 'q ⊏ 'd`, fails the same premise: `Δ ⊨ 'd ⊏ 'r2`.

Is each rejection necessary?

- **`sched-c-outside`**: yes. The queue lives in `'d`'s scope, which encloses `'r`'s block. A
  task left in the queue after `'r` ends would read `cfg` after its owner may have freed it.
- **`sched-c-equal`**: the program is not obviously unsafe, since the queue is freed inside
  `'r`'s block. It is rejected by the strictness of the `Imm` rule, which the model needs:
  - a borrow's own cell is not in `Res_'r`;
  - 6.60 fails with a non-strict `Imm` rule (`not_vC_outlives_le`, SPEC §23 *Left as printed*).

  The cost is the extra scope that names `'d`, as in `aff-capture.bc`.

**Verdict (c): DOES NOT TYPE**, by the right rule.

### Variant (d): an answer type that does not outlive `@d`

Surface operation types are closed in lifetimes (SPEC §19). So at the surface, an answer type
fails `AnsOutlives` only when it has, outside a `[@·]` or a `!`:

- a bare `U`: a thunk, a closure, a stored generator or a continuation;
- or a borrow at a constant lifetime.

*Example* (by hand): a worker task receives jobs from the scheduler.

    recv : 1 ↠^aff U(1 ⊸ F i32)      -- the scheduler answers a job

- A task with `recv` in its row fails BOXED-κ's answer premise at every `@d`
  (`not_ansOutlives_thunk`, proved): `VOutlivesR` has no case for `U`. So the task cannot be
  spawned. **Rejected.**
- The premise covers **forwarded** operations too, since their answers come back into the
  continuation.
- It does not cover operations handled **inside** the task, which are not in the row at the
  spawn.

**Is the rejection reasonable for real programs?**

- **The repair is local.** Declare the answer `[@⊤] U(1 ⊸ F i32)` or `!U(1 ⊸ F i32)`. Each
  outlives every defined `@d` (`ansOutlives_boxTop`, proved, and `VOutlivesR.bang`). The handler
  then boxes the job at `⊤` where it forms it, which checks that the job captures nothing
  borrowed.
  - A clause's own context is persistent, so a job formed in the clause meets that condition
    unless it captures the operation's payload.
  - The obligation is the analogue of a `'static` bound on a channel's message type. For the
    message-passing and job-queue patterns of async runtimes it costs a type annotation.
- **What is lost**: an effect whose answer is a closure over borrowed data, delivered into a
  stored task. In such a program the task could keep that closure across a later `await`,
  beyond the borrow. That is exactly what the premise protects against.
- **At the kernel only**: an answer type mentioning a short lifetime, as in the README's
  candidate witness, cannot be written at the surface.
- **Whether the premise could be weakened** (README, *Necessity of the answer-type condition*)
  is still not determined.

**Verdict (d): DOES NOT TYPE** (failing condition: `AnsOutlives`, at the `U` in `recv`'s answer).
This is **reasonable**, since the repair is one annotation at the effect's declaration.

### Do stored continuations replace the ν state-machine encoding?

**Yes, for the tasks.** Each task is direct-style code that performs `await`. There is no per-task
`ν` machine, no step function per stretch between `await`s, and no hand-written state type. The
two `ν` types that remain are generic, each written once:

- the stored task `Task^d`, which is the spawn handler's answer type, as §15's stored generator
  is;
- the scheduler's loop, as any div loop is.

**For the scheduler, it depends on the bound:**

- **(a)**, tasks bounded by `⊤`: the scheduler runs until the queue is empty, which
  [B on paper](b-package-typing.md) P4 could not do (it flagged a fixed number of rounds).
- **(b)**, tasks that capture a borrow: the scheduler must be bounded, with stored continuations
  or with `ν` machines alike. The limit is the spanning lend, not the encoding.

## 3. ν rests (P2b)

**Can a `ν` observation's rest be typed `[@d] U X` when the state outlives `@d`? Yes, by existing
rules; no new rule is needed.**

- **Positivity.** `NuOk` admits `[@d] U X` at any polynomial position, through `VTy.Poly`'s box
  case (SPEC §22).
  - Proved instances: `affBody_nuOk` (Core) and `taskBodyG_nuOk` (here).
- **Formation through `unfold`.** The step at state `S` returns the rest as `[@d] S`, by `[]I`
  over the step's context: `S ⊐ @d`. `unfold`'s map at `[@d] B` is its map at `B`, since `[]I`
  and `[]E` are typing rules on the same term (`mapV`, `map_ok`).
  - That is `d_mkBox` (`Core/AffRules.lean`), a `CDerives` derivation.
- **Formation directly.** Build the codata by `nuIn` and box it by `[]I` over its context.
  - This is what the spawn handler does at each `await`, checked in `spawn-handler.bc` and
    proved sound in (a).

**P2b typed that way.** Give the package's contents the boxed-rest closure:

    ∃'x ⊏ ⊤. ⟨mut i32⟩ U(Aff^c i32 i32),     Aff^c i32 i32 = νX. (i32 ⊸ F(i32 ⊗ [@c] U X)) & F 1

| step | rule | side condition | at `c = 'x` | at `c ⊏ 'x` |
|---|---|---|---|---|
| form the closure over `m : Mut 'x i32` with boxed rests | `d_mkBox` (`[]I` at `c`) | `Mut 'x i32 ⊐ c`: `Δ ⊨ c ⊏ 'x` | **fails**: the `Mut` rule is strict (`logState_not_outlives` is this failure for `aff-capture`'s logger) | ✓ with a scope `c` inside the callback, as `aff-capture`'s `'w` |
| close the package | `[closeI]` (B, ADD-1) | the contents' context `⊒ₓ ∅`: `Pₓ(c)`, i.e. `c ≡ 'x` | ✓ | **fails**: `c` is neither `'x` nor above a parent. `FV(T) ⊆ dom Δ ∪ {'x}` fails too, since `c`'s scope ends inside the callback |
| re-close after a call, holding the rest `r : [@c] U(Aff^c …)` | `[closeI]` | `Pₓ(c)` | as above | as above |

**Verdict P2b: DOES NOT TYPE with boxed rests either.**

- At `c = 'x`, `d_mkBox`'s `[]I` (`Mut 'x i32 ⊐ 'x`) fails.
- At `c ⊏ 'x`, `[closeI]`'s `Pₓ(c)` fails.
- At `c` above the package's parents, `Mut 'x i32 ⊐ c` fails, because `'x` is fresh beneath its
  parents.

The obstacle is not the rest's typing. A rest boxed at `@d` excludes the `mut` cell at `@d`
itself (`[@d] A` is membership in `Res_d`, and the box modality is strict, SPEC §23). P2b's
closure holds exactly that cell, the lend at `'x`.

**What P2b needs** is a different rest modality, the one [B on paper](b-package-typing.md) named:

    ⌈'x⌉ U X inside ν      (a closable rest)

- **Positivity**: `VTy.Poly` extended by `⌈'x⌉ B` over a polynomial `B`, with `'x` bound by the
  enclosing package.
- **Formation**: `[closeI]` (ADD-1) on the rest's context: every live slot satisfies `Pₓ`, so
  cells at `'x` itself are admitted.
- **Relation**: the contents' resource as `Pkg.CloseOK` reads it in `experiments/Nominal` (reading
  (b): no cell at or beneath `'x` other than the lend). It is not `Res_α` for any `α`: a
  "stratum" whose `mut` cells sit at its own lifetime cannot be built
  (`no_nonstrict_stratum`, `experiments/Outlives`).

**This rule belongs to B, not to `ν`.** Core has no package type, so it has no statement to make
the rule's compatibility lemma about. The lemma would sit on Nominal's carrier beside `Pkg`, after
the package's own fundamental-property case. I did not state it in Lean and did not prove it. I
have not derived that it is sound, and I have not verified that any obstruction to it is real.

## 4. Lean names and status

All in `experiments/BoxedKappa/BoxedKappa/Programs.lean`. **Proved** means no `sorry`, with the
axioms checked by `scripts/Axioms.lean`.

| name | statement | status |
|---|---|---|
| `handler_shape`, `handler_derives` | `spawn-handler.bc`'s `main` is `CDerives ∅ []` at `retTy [] i32 E ⊗ clausesTyB [] E ⊤ [await]` | proved (`decide +kernel` over the checker) |
| `sched_shape`, `sched_derives` | `sched-a.bc`'s `main` is `CDerives ∅ []` at `U(spawnT ⊸ F i32)` | proved (same) |
| `runE_derives` | `u ← (); c ← tb; c u` at `F_{await} i32` under `tb : [@⊤] Code` | proved |
| `run_ctxOutlives`, `await_ansOutlives` | BOXED-κ's two premises for `spawn` | proved |
| `spawnBody_sem` | `handle_1 (tb ()) with (h_ret, hs)` at `F E`, by `handleV_compatCB` | proved |
| `spawnV_sem` | `spawn : !U([@⊤] Code ⊸ F E)` | proved |
| `prog_sem` | the program at `F i32` | proved |
| `prog_every_run` | every run continues to an `i32` at the empty memory | proved |
| `prog_eval` | the interpreter answers `41130`, no cell left | proved (`decide +kernel`) |
| `taskBodyG_nuOk`, `taskBody_nuOk` | `νX. F(A ⊕ [@d] U X) & F 1` is positive | proved |
| `ctxOutlives_imm_iff` | (b): `CtxOutlives Δ {k : Imm 'r A} d ↔ Δ ⊨ d ∧ Δ ⊨ d ⊏ 'r` | proved |
| `not_ctxOutlives_imm_self` | (c): never at `d = 'r` | proved |
| `not_ansOutlives_thunk` | (d): a bare `U` answer fails the answer premise | proved |
| `ansOutlives_boxTop` | (d)'s repair: `[@⊤] U C ⊐ d` | proved |
| `semV_closed_dead` | a closed value typed at `[]` is typed at a dead context | proved |

**Sorries:** none.

**Not machine-checked:**

- `spawn` polymorphic in `'d` (variant (b)'s parameter type). Its instance at each `'d` is
  `spawnBody_sem`'s argument at a variable bound. The handler's derivation at an open `Δ` was not
  produced.
- Variant (b)'s run.
- The claim that run-until-empty requires bound `⊤`. It is argued above from totality, the
  missing `U` outlives rule and `mainLife`, and is checked only at `sched-b-div.bc`.
- Everything about packages.
- BOXED-κ as a `CDerives` constructor. It would add one case to `fundamentalC`, which is
  `handleV_compatCB`, and one to each inversion.
