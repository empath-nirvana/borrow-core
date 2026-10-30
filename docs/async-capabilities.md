# Async with capabilities, and borrows held across a suspension

**Status: a spec entry draft, for approval.** It becomes a SPEC.md section once approved; SPEC.md
is not edited here. Tracking issue: #52. Lean: `experiments/AsyncCap/` (`lake build AsyncCap`).
Surface spellings are provisional throughout. Each says so where it appears.

**Marks.** Every claim carries one of these:

- **EXISTS**: in `Core/`, `Frontend/`, `Backend/` or `lib/` on `main`. The name is given.
- **PROVED**: machine-checked, either in `experiments/AsyncCap` (this branch) or on the branch
  named.
- **ASSERTED**: a consequence of `PinLaw`, the one named hypothesis (§4).
- **DESIGNED**: specified here, not built.
- **NOT DETERMINED**: I have not derived it and have not checked that any obstruction is real.

**The decision this entry implements** (user, #52): the System C method; pinning with as little
ceremony as possible for the programmer; the bare minimum assertion needed to make it compile,
taken as an escape hatch in the proof; then a test suite that tries to break it.

---

## 0. Summary

- **The programmer writes ordinary code.** Tasks are direct-style functions that `await`. They
  borrow their own locals and outer values across `await`, and use `spawn` and cancellation.
  There is no `Pin`, no `unsafe`, and no annotation (§3.4).
- **One mechanism makes borrows across a suspension sound: ghost end** (GhostEnd, PROVED for the
  lender side). At a suspension the lend is *ended*, as at a return. At the resumption the place
  is *lent again* at a fresh lifetime. The suspended code's views are the place's location, so
  they are valid again. `wpG`'s stop conditions are unchanged (`Core/EffDefs.lean:37`, `:40`),
  and so is every Core theorem. Nothing is added to the machine.
- **Two relaxed typing rules.** R1, `lendR`: a borrow block may perform resuming operations
  (`await`, `yield`, a scheduler's `log`). R2, `lendLoopR`: a shared (`imm`) borrow block may
  contain an unbounded loop whose state holds the borrow (the scheduler of A3).
- **The assertion is `PinLaw`** (§4). It is a `Prop` over **typed programs**: every quantifier
  over code ranges over derivations of the extended judgment `PDerives`. In one sentence:
  *code that Core's rules (plus R1 and R2) type, suspended while it holds views of a lend, is
  again in the relation when the place is lent afresh.* It is stated as the compatibility lemmas
  of R1 (`PinStop`) and R2 (`PinLoop`) themselves, and is tested by programs (§6), not proved.
- **PROVED from `PinLaw`, with no `sorry`:** `fundamentalC_pin`, `adequacyC_pin`,
  `adequacyD_pin`, `adequacyD_pin_safe` (no run is stuck). Programs that use neither relaxed rule keep `fundamentalC` and `adequacyD`
  unconditionally (`PDerives.ofC`).
- **Many programs need no assertion.** When only the borrow itself crosses an `await`, the
  elaborator splits the block into ordinary lends (L0, §3.3; ADD-5 on `nominal-lifetimes`).
  `PinLaw` is used only when a value *derived* from a borrow is live across a suspension: a
  closure over it, a pair holding it, a sub-view.
- **The machine does not detect a dangling or aliased borrow** (§6.1). A load, store or free of
  a location absent from memory is stuck. Borrows are bare locations, so aliasing and a stale
  view of a live cell run silently. §6.1 gives the minimal dynamic check.
- **The plan** is eight PR-sized units (§7). Each turns acceptance programs green.

---

## 1. Goal and acceptance programs

**Goal.** A cooperative async scheduler without function colouring, with effects. One function
written once is used by synchronous code and by tasks. Tasks borrow, are stored, are cancelled,
and perform other effects while suspended. Every borrow guarantee holds, conditional at most on
`PinLaw`.

The programs are in `experiments/AsyncCap/bc/`. Each is marked pending and records today's
`bcc check` message (they do not parse: the surface is provisional). A1 and A4 run, and are in the
corpus (`corpus/async-scheduler.bc`, `corpus/async-map.bc`; U2, SPEC §30), and so do A5 and A6
(`corpus/async-logged.bc`, `corpus/async-cancel.bc`; SPEC §32). `lib/async.bc` EXISTS
(U2, SPEC §30). `effect Async { ctl await() }` declares `await : 1 ↠^cancel 1`. The scheduler is,
per task, a handler of `Async` whose clause stores the task's continuation as the task's rest
(`with spawn { … }`), and across tasks a loop that resumes the queued tasks until none is pending
(`run_until_empty`). The spelling `async::run { s -> s.spawn { … } }` below is the designed one;
U2 spells spawning `push(q, with spawn { … })` (SPEC §30 *Open*: `s.spawn` needs a provided
effect).

| program | what it tests | relaxed rule | verdict once built |
|---|---|---|---|
| **A1** `corpus/async-scheduler.bc` | run-until-empty scheduler; tasks own their data | none | runs: `[1111, 22]`, `live 0` |
| **A2** `a2-local-borrows.bc` | tasks borrow their own locals across `await`, `imm` and `mut`: the borrow itself (`reader`), a closure over it (`counter`), a pair holding it (`pair_view`) | `reader`: none (L0); the others: R1 | runs: `[20, 12, 7]`, trusted: PinLaw at 2 blocks |
| **A3** `a3-scoped-shared.bc` | tasks borrow a shared outer value; scoped spawn; the scheduler runs with no bound inside the borrow | R2 | runs: `[6, 9]`, trusted: PinLaw at 1 loop |
| **A4** `corpus/async-map.bc` | an awaiting block passed to `map`, written once and also used synchronously | none | runs: `([2, 3, 4], [[10, 20, 30]])` |
| **A5** `corpus/async-logged.bc` | tasks log (an operation of the scheduler) and raise (handled per task) while holding a borrow across `await` | R1 | runs: `[30, -2]`, log `[3, 2, 3, 2]` (SPEC §32) |
| **A6** `corpus/async-cancel.bc` | a suspended task holding a borrow and an owned value is cancelled; its finalisers run, the borrow ends | R1 | runs: `[2]`, `live 0` (SPEC §32: the victim is held by the task that cancels it, and a finaliser does not log) |
| **A7** `reject/n1`–`n9`, `accept/m1`–`m3` | the adversarial list (§6.2) | — | as §6.2 |

A5's log is in the order the two tasks interleave: each logs its cell before and after its
`await`.

The surface syntax `with Async`, `{A => B}` for a block parameter, `s.spawn { … }`,
`t.cancel()` and `||` closures is provisional. `with Async` is today's spelling of a function's
row; under §2 it names the capability the body uses, bound where the function is called.

---

## 2. The capability design at Core (O2-lt)

The option is O2-lt of `research/effects/src/prior-art/rows-vs-capabilities.md` (on
`nominal-lifetimes`): capabilities as borrows, with System C's capture sets replaced by BoLo
lifetime bounds. That page lists O2's costs: (a) an outlives rule at `U C` for stored callbacks;
(b) control operations as lends, the tier-2 stop change; (c) FnMut-shaped block parameters; (d)
aliased stateful capabilities (`twoBlocks_refused`). This section says what each piece is and
whether it exists.

### 2.1 What is second-class

| piece | status |
|---|---|
| A **block** parameter, `f: {A => B}`: called in the callee's body, never stored or returned. Its type names no effect. | EXISTS (SPEC §30; written `f: !(A => B)`, a block at a parameter of function type). At Core a block is an ordinary thunk argument `U(A ⊸ F_Σ B)` at the row of the copy that uses it (§2.2); "second-class" is enforced by the elaborator, which rejects storing a block. Core needs no second-class modality: storing a thunk whose captures hold a borrow is already refused by `[]I` (`boxI_compatC`, `Core/Compat.lean:497`), whose premise is the context outliving the box's lifetime. |
| A **capability** for answering operations (`log`): the handler's state, lent. | EXISTS: §18 elaborates an answering handler to `withbor`/`withswap` on a `Mut` lend of the state. PROVED at the paper layer that this is System Ξ's handler (`HandlersAsBorrows`: `translate_typed`, `effect_safety`). |
| A **capability** for control operations (`await`): the name of the lexically enclosing handler site. | EXISTS: static names, resolved lexically (SPEC §19 *Names*). It is not a lend, and need not be: §3 makes a lend *crossed* by `await` sound without making `await`'s capability a lend. So O2's cost (b) is replaced by R1. |
| A **stored** callback or continuation: first-class, boxed at a lifetime bound. | §2.3. |

### 2.2 A called-only callback gets its effects from context; no row variable

A block's effects are those of the context it was written in: it performs `await` because an
`Async` handler encloses the block's definition, and its call inside `map` reaches that handler
(static names; no accidental handling, since `map` declares no handler of `Async`). `map`'s
signature mentions no effect, and the kernel has no row variable:

- **The elaborator copies `map` per block row** and checks each copy at closed rows. EXISTS for
  divergence (SPEC §14, *specialization at the callback's type*) and per effect assignment
  (SPEC §18); `[let-poly]` (SPEC §24, `CDerives.letPoly`) types one closed function at each use.
  Effectful callbacks at the surface (#161) are DESIGNED in `docs/surface-callbacks.md` (branch
  `effects-async-a1`, E2–E8). U2 takes its elaboration with one change: a called-only block's type
  carries no row (E1 gives every callback type an inferred row); the block's effects come from
  the enclosing sites and the copy per use. EXISTS for called-only blocks (SPEC §30: the copy
  `map__n2_b1n1` of `corpus/async-map.bc`; OQ-S1 handled there as a PROPOSAL pending the user's decision: a loop at the row
  for a counted loop at a `with`'s site). A *stored* callback or continuation does carry its
  row, `U(A ⊸ F_Σ B)` boxed at a bound (§2.3), inferred and never written: the store needs a type,
  and this is the one place rows reach a type the programmer could see. Its kernel programs `async-tasks` and `async-colourless`
  (`Core/EffAsyncPrograms.lean` there) run one generic function at the pure row and in two
  interleaved tasks.
- **The lowering's control class: specialization, as today.** Each copy of `map` is at closed
  rows, and its block is known code, so the lowering reads the class (none, abortive,
  suspending) off the copy, as SPEC §19 *Lowering* does today. The alternative, O2-g (a class
  grade on block and box types), is not needed: every acceptance program passes known blocks,
  and the compiler is whole-program. O2-g is needed only for one shared un-specialised body,
  which no unit here asks for (OQ-4).

### 2.3 Stored callbacks and continuations: boxed at a lifetime bound (BOXED-κ)

A scheduler stores each task's continuation `κ` in its queue. `VOutlivesR`
(`Core/Types.lean:1761`) has no case for `U C`, and `[handle]` hands a clause `κ` at a bare type,
so today a stored `κ` cannot be given a `[@d]` type.

- **BOXED-κ** is the variant of `[handle]` whose clause receives `κ : [@d] K`, given that the
  handled computation's context outlives `@d` and every non-abortive answer type outlives `@d`.
  PROVED on `nominal-lifetimes` (`experiments/BoxedKappa`): `stop_lemma`, `stop_sem`,
  `handle_compatCB`, `handleV_compatCB`. The P4 scheduler is typed, safe on every run and run to
  `41130` (`prog_sem`, `prog_every_run`, `prog_eval`). **It will be ported** (U1); it is not a
  `CDerives` rule today.
- **BOXED-κ needs nothing new for lends opened inside the task.** At the stop, a lend opened
  inside the handled computation is ended (§3.2). The continuation holds the *owner*, which is
  owned data, not a borrow. So BOXED-κ's premise is about the task's context only, exactly as
  proved. This is established for the extended judgment by composition: `handle_compatCB` takes
  the handled computation's *semantic* judgment, which `fundamentalC_pin` supplies (PROVED once
  ported, by adding one case; no new obligation).
- **A stored block or closure** is `[]I` at its captures' bound, `[@c] U(Clo^c A B)` for one that
  is called many times. EXISTS (`boxI_compatC`; SPEC §22's `Clo` closure).

### 2.4 What of (c) FnMut-shaped blocks and (d) aliasing the acceptance programs need

- **(c)** A block called many times while capturing a `Mut` is SPEC §22's `Clo` closure
  `Clo^c A B = νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1`, with an effectful variant positive at closed
  operation types (`cloEffBody_nuOk`). EXISTS. A2's `bump` and A6's `peek` are such closures over
  a view, held across `await`: that is what makes them need R1, not what makes them typable.
- **(d)** Not needed. A5 shares a stateful capability between tasks by making it an operation of
  the scheduler's handler (`log`), whose state the handler owns and serialises: state behind
  control, SecondClass P5 (`p5-two-blocks.bc`, EXISTS as a checked probe). Two tasks capturing one
  `&mut` capability stays refused (`twoBlocks_refused`; `reject/n2`).

---

## 3. Pinning with minimal ceremony

### 3.1 The starting point, and the gap

#52's hypothesis holds in the model: **only cells are borrowable, and an owned cell never moves.**
A place is a cell (`alloc`); a borrow is the cell's location; the owner of a cell is a pointer.
Moving a value moves pointers, never cells. So no runtime `Pin` is needed (§3.5 checks Rust's
rules one by one). **The gap is the proof**: Core refuses every lend that spans a suspension.

- **Typing.** Every borrow callback's row is `Row.Unwind` (`Core/EffBorrow.lean:133`): abortive
  operations only. The surface reports "this borrow block's body performs the operation …, which
  resumes" (`corpus/reject/gen-self-borrow.bc`).
- **Semantics.** `wpG` has two conjuncts that a lend open at a stop would break: `↭`,
  `ResU.UpdV ρ π` (`Core/EffDefs.lean:37`), forbids a run ending with a new `mut` cell; and the
  frame condition `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)` (`Core/EffDefs.lean:40`,
  T1) forbids an `imm` frame open at the stop. A pointwise relaxation of either was refuted by
  configurations no program builds (LoopBorrow `refoldKripke_false`; DenseCarrier
  `core_not_relend_kU` on `law2-typed-world`).

**Where this sits against the prior art.** `docs/prior-art-suspension-borrows.md` §6 recommends
the standard slice (no lend opened inside a suspendable computation is live at a suspension that
reifies the continuation; Rust's E0626) plus the liveness elaboration that is L0 below, and finds
that "nothing in the literature is both less restrictive and proved". This entry takes L0, and
goes beyond the slice under `PinLaw`, per #52's decision: R1 and R2 are less restrictive and
asserted, not proved.

### 3.2 Ghost end: the lend ends at the stop and is re-lent at the resumption

GhostEnd (`experiments/GhostEnd`, on `main`) keeps both conjuncts and changes when the lend ends:

- **At a stop, the borrower's lend is ended** as 6.65 ends it at a return: the `mut` cell moves
  back into the owner, `↭` holds from the run's start, and the frame lists are unchanged
  (`freeze_at`; the borrower's view owns nothing, `noOwn_ptoMutS`). PROVED.
- **At the resumption, the lender lends the place again** at a fresh lifetime below the bound,
  6.65 re-applied at each resumption (`ewpTS_M_frameR`; `imm` lends: `ewpTS_I_frameR`). PROVED.
- **Cancelled at a stop**, the continuation unwinds and the owner goes to the lender's finaliser:
  `withborR_compat`, the unwinding `withbor` at a resuming row (`GhostEnd/Drop.lean:126`). PROVED.
- **The borrower's view needs no change**: it is the location `ℓ`, and the fresh cell at `ℓ` puts
  it back in the relation at the new lifetime (`mutView`). PROVED.

What is not proved for every program is the borrower's half: that the *rest* of the suspended
code, re-run at the fresh lifetime, is in the relation. For a straight-line borrower it is PROVED
(`relend_fin`, `relendO_chain`); for branches, loops, closures over the view, a callee that
yields with the view (`branch_spans_yields`, `loop_spans_yields`, `closure_spans_yield`,
`callee_spans_yields`) PROVED instance by instance. For every typed borrower it is Law 2's (S1),
§4.3. That is `PinLaw`.

### 3.3 The relaxed rules

Both are in `experiments/AsyncCap/AsyncCap/Derives.lean`, as constructors of `PDerives`, which is
`CDerives` with every premise in `PDerives` (generated by `scripts/gen.py`, so a relaxed lend may
contain another). Neither adds a machine step.

**R1, `lendR`: a borrow block whose body performs resuming operations.**

    Δ ⊨ b defined   x fresh   T, B free of 'x   B has no U   Δ ⊢ T ⊒ @b'   Row.ResumeO Σ 'x
    M closed but for m   ·  ⊢ d : Ref T ⊸ 1        Δ, 'x ⊏ b ; m : Mut 'x T ⊢ M : F_Σ ([@x] B)
    ─────────────────────────────────────────────────────────────────────────────────────────
              r : Ref T ⊢ withborU d r (Λ. λm. M) : F_Σ (Ref T ⊗ B)

- The term is Core's unwinding `withbor` (`withborUV`, SPEC §19). EXISTS. Only the callback's row
  changes: `Row.ResumeO` (resuming, not unrestricted, empty cancel row, answering `1`, argument
  closed data with no `U`) instead of `Row.Unwind`.
- Its premise is the callback's **derivation**, in `PDerives`.
- Its compatibility lemma is `PinLaw.stop` (§4).
- R1 lends `mut` only. A shared borrow of a task-local place is lent `mut` and read: the place is
  owned by the task, so exclusivity costs nothing. An `imm` R1 (and `withload`, and a fold whose
  algebra suspends, `corpus/pending/async-borrow.bc`) is OQ-2.

**R2, `lendLoopR`: a shared borrow over a loop whose state holds the borrow.**

    x fresh   A, B, R free of 'x   B, R have no U   Δ ⊢ A scoped   N, K closed but for p   s₀ closed
    Δ, 'x ⊏ ⊓Δ ; p : Imm 'x A ⊗ S ⊢ N : F (B ⊕ S)      Δ, 'x ⊏ ⊓Δ ; p : Imm 'x A ⊗ S ⊢ K : F R
    Δ, 'x ⊏ ⊓Δ ; · ⊢ s₀ : S                                           (S may mention 'x)
    ─────────────────────────────────────────────────────────────────────────────────────────
         r : Ref A ⊢ lend_loop_imm (Λ. λp. N, Λ. λp. K) (r, s₀) : Loop (Ref A ⊗ B) (Ref A ⊗ R)

- The term is the per-observation lend of `lib/lend.bc` / `LoopBorrow` (`lendLoopApp`), at the
  loop body. PROVED to be `bcc`'s erasure of the checked `lend_loop_imm` and `lend_loop_mut`
  (`lendLoopE_is_checked`; `bc/lend-loop-term.bc` runs to `2113`, `live 0`).
- It is `LoopLend` (SPEC §14) **with its side condition removed**: today the state between
  observations must outlive `'x` ("an iterator that holds the borrow" is reported).
- **`imm` only.** Each observation hands the step a fresh view beside the state's. Two `imm`
  views of one place are sound together; two `mut` views are not (`reject/n6`). A `mut` R2 needs
  an interface that hands no fresh view once the state holds one (OQ-3).
- Its compatibility lemma is `PinLaw.loop`, ASSERTED (§4.3).

**R2 is what makes "unbounded loops" fit.** A computation of `F_Σ A` is total: `ewpTS` is a
least fixed point, so a borrow callback that performs `await` forever is not in the relation.
Unbounded loops are codata (SPEC §14, §19 *Divergence*), so a borrow held across a loop's
iterations is held across observations, not stops.

**L0, segmenting (no relaxed rule).** When the only value whose type mentions `'x` live across a
resuming operation is the borrow itself, the elaborator splits the block at the operation into
ordinary lends of the same place. This is ADD-5's degenerate case
(`research/effects/src/b-package-typing.md` on `nominal-lifetimes`; P5 and P6 there are checked
by hand-segmenting with today's `bcc`), and `LoopLend`'s mechanism moved from an observation
boundary to a suspension. It is DESIGNED (U3) and needs no `PinLaw`: the elaborated program is
`CDerives`. `corpus/reject/gen-self-borrow.bc` moves to the corpus under it.

### 3.4 What the checker still enforces

All of the following are rules that exist, or premises of R1/R2. Each acceptance-relevant one has
a negative program (§6.2).

1. **`mut` exclusivity.** A `mut` view is linear (`Ctx.SplitP`; BoLo B6). R1 lends an owned place
   once; R2 is `imm` only. Two tasks cannot hold `mut` views of one cell (`n2`), and a loop state
   cannot hold a `mut` view beside the fresh one (`n6`).
2. **Outlives of stored tasks.** A stored continuation is `[@d] K` with the task's context
   outliving `@d` (BOXED-κ); a stored callback is `[@c] U …` by `[]I`. A task holding a borrow
   from outside cannot outlive it (`n1`, `n3`, `n8`). Lends opened inside the task impose nothing
   (§2.3).
3. **What crosses a relaxed lend's stop.** Only operations of `Row.ResumeO`: no abortive operation
   (`n4`; OQ-1), no unrestricted one (`n7`), and arguments of closed data, so neither the view nor
   anything holding it is handed to a handler (`n5`, `n9`).
4. **What leaves a relaxed lend.** Its answer `[@x] B` has `B` free of `'x`, as for every lend.
5. **Continuations are used at most once** (`refuses_R_clauses`, `not_der_at08`): EXISTS. Every
   cancellable continuation is resumed or cancelled, so a task's finalisers run (A6).

**Developer-facing annotation: none is needed.** The programmer writes `borrow`, `&x`, `&mut x`,
`await`, `spawn` and `cancel` as ordinary code. The elaborator chooses L0 where it applies, R1
otherwise, and R2 for a shared borrow over a loop. The one place a programmer sees the design is
a rejection: a `mut` borrow held by a loop's state (`n6`), or an abortive operation crossing a
held borrow (`n4`). Both are design limits with open questions (OQ-3, OQ-1), not annotations.
`bcc trusted` (EXISTS as a subcommand) reports which blocks rely on `PinLaw` (§5).

### 3.5 Rust's `Pin`, rule by rule

| Rust rule | the hazard it prevents | does it exist here? |
|---|---|---|
| A `!Unpin` future must not move after its first poll (`Pin<P>`) | a self-referential future holds a reference into its own field; moving the future by `memcpy` leaves the reference dangling | **No, in the model**: a borrow is the location of a cell, and a task's state holds the cell's owner (a pointer). Moving or swapping a suspended task moves pointers (`accept/m1`). **In the lowering, it is an obligation**: SPEC §19 lowers a continuation to a state record of statically known size, moved by value. A lent cell must not be inlined into a record that is later moved. Either the cell stays out of line (today: `alloc` is a heap cell), or the record is allocated once per task and never moved after the first suspension (Rust's `Box::pin`, which `tokio::spawn` also pays). The compiler enforces this; the programmer writes nothing. DESIGNED (U5's lowering note). |
| No `&mut T` from `Pin<&mut T>` for `!Unpin` (`get_mut` is `unsafe`), so `mem::swap`/`mem::replace` cannot move the pinned value | swapping the pinned value out moves it | **No**: the owner of a lent cell is inside the suspended continuation, so no code outside the task can name it. The task's own code reaches the cell only through the view, which `withswap` swaps the *contents* of, at the cell's fixed location. |
| `Drop` must run before a pinned value's memory is invalidated (the drop guarantee) | intrusive structures (wakers, linked lists) point into pinned memory; freeing without drop leaves them dangling | **No `mem::forget` exists for a continuation**: `forget κ` has no derivation (`not_forget_kappa`), cancelling runs the finalisers innermost first, and adequacy ends at the empty memory (`adequacyD`, and `adequacyD_pin`). A program that never ends never drops its tasks, as in Rust. |
| `Unpin` auto trait | marks types safe to move when pinned | No analogue needed. |
| Pin projection (structural pinning of fields) | a field of a pinned struct must be treated as pinned or not, consistently | No analogue: a field that is borrowed is its own cell or a leaf of a family, lent by its own lend. |
| `async fn` cannot hold a borrow of its own local across `.await` without `Pin` (E0626 for movable generators) | the generator's frame is self-referential | **Sound under ghost end**: R1 (`PinLaw.stop`), or L0 with no assertion. |
| Recursive `async fn` needs `Box::pin` | the future's size would be infinite | Same cost: a code whose state holds its own continuation is one heap object per level (SPEC §19 *Lowering*; `accept/m3`). |

---

## 4. PinLaw: the bare-minimum assertion

### 4.1 The statement

`experiments/AsyncCap/AsyncCap/PinLaw.lean`. `PinLaw` is a `structure … : Prop` with two fields.
It is never an axiom: it is a hypothesis of the theorems that use it.

```lean
/-- R1's compatibility lemma: the lend held across resuming operations is in the relation. -/
def PinStop : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) →
    Row.ResumeO S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV Δ [] d (.lolli (.ref T) .unit) →
    PDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- R2's compatibility lemma: the shared lend over a loop whose state holds the borrow. -/
def PinLoop : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (A S B R : VTy) (N K s0 : Expr),
    Δ.find? x = none → Δ.meetOfDom.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → ¬ VFree x R → NoThunkT B → NoThunkT R → VScoped Δ A →
    closedAt 1 N = true → closedAt 1 K = true → closedAt 0 s0 = true →
    PDerives (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    PDerives (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    PDerives (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))

structure PinLaw : Prop where
  stop : PinStop
  loop : PinLoop
```

**In one sentence:** code typed by Core's rules plus R1 and R2, suspended (at an operation, or
between a loop's observations) while it holds views of a lend, is again in the relation when the
place is lent afresh at a new lifetime.

Each field is the compatibility lemma of its rule, at the rule's own premises. Nothing in it
says *why* the rule is sound (ghost end, a re-lendable reading, a frame lemma): an assertion of a
proof route can be wrong where the rule is not, and then every theorem resting on it is vacuous.

### 4.2 Why it is stated this way, and what part is proved

- **Over typed programs.** Every quantifier over code is a quantifier over `PDerives`
  derivations: `PinStop` quantifies over `M` *with its derivation*, `PinLoop` over `N`, `K`, `s₀`
  with theirs. Nothing is pointwise over configurations or over semantically related values.
  The pointwise forms were refuted by junk configurations (`core_not_relend_kU`,
  `refoldKripke_false`), and asserting a false `Prop` would make every theorem below vacuous.
- **The compatibility lemmas of exactly the relaxed rules, and nothing smaller.** Asserting
  only the borrower's half of R1 (GhostEnd's `Relend` at `opTableO`) and proving the lender's half
  would put a proof route's intermediate step inside the assertion. That step is doubtful: its
  cancel clause hands the owner back before the borrower's finalisers run, while `[then]` lets a
  finaliser hold the view (§4.3). Shrinking `PinLaw` is U8's proof work.
- **What is proved from it (no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):**

| result | statement | status |
|---|---|---|
| `fundamentalC_pin (hPin : PinLaw) : PDerives Δ Γ e j → SemJ Δ Γ e j` | the Fundamental Property for the extended judgment: `fundamentalC`'s induction, case for case, plus `hPin.stop` and `hPin.loop` | PROVED |
| `adequacyC_pin (hPin : PinLaw)` | a closed `PDerives` program of `F 1` runs to `()` at the empty memory | PROVED |
| `adequacyD_pin`, `adequacyD_pin_safe` | every run continues to `()` at the empty memory; no run is stuck | PROVED |
| `PDerives.ofC` | every `CDerives` derivation is a `PDerives` one | PROVED |
| `lendLoopE_is_checked` | R2's term is `bcc`'s erasure of the checked `lend_loop_imm`/`lend_loop_mut` | PROVED |
| `resumeO_await_yield`, `not_resumeO_raise` | `Row.ResumeO` admits `await` and `yield`, and refuses an abortive operation | PROVED |

### 4.3 Why I believe it, how much is proved elsewhere, and what would falsify it

**`PinStop`.**

- **Evidence** (for one route to proving it; none of it is asserted). Law 2 (branch
  `law2-typed-world`, `experiments/Law2`) proves the borrower's re-lendability
  at the linear table and over `CDerives` (`relendOfTyped'`, `law2`, `law2_depth1`) from a
  fundamental lemma for the re-lendable reading, `pj_fundamental`: one induction on `CDerives`,
  91 cases, **59 proved, 6 proved at part of their instances, 26 not derived** (each its own
  `sorry`, `fl_…`; README table). At the fragment of proved rules there is no open step
  (`law2_frag`, `law2_depth1_frag`). GhostEnd PROVES it for straight-line, branching, looping and
  closure-holding borrowers instance by instance (§3.2), and at cancellable yields for straight-line
  borrowers (`relendO_chain`). No rule failed in a machine-checked configuration (Law2's kill
  criterion, not met).
- **What that route leaves open:** Law 2's 26 rules not derived (the inner
  lends, `[]I` at a type that does not outlive, `∀` with `U` in the context, `μ`/`ν`, writes
  through a `mut` leaf of a family, `[raise]`/`[then]`, `[handle]` of the lenders' name); the
  cancel path for every borrower, not only straight-line ones; and nested relaxed lends,
  which Law 2 covers on the lender side (`fold_mixed`, every mixed stack) but not inside
  `PDerives`. At the cancel path the route's table must re-lend the place for the borrower's own
  finalisers before the owner returns: `[then]` gives a finaliser the body's context, so it may
  write through the view (§6.2 row 16). Not machine-checked either way.
- **Why it should be true.** The lend's view is the location `ℓ`, the same at every lifetime. A
  typed borrower's behaviour does not depend on which lifetime it was typed at: its derivation is
  re-run at the fresh one, as `segment_fundamental` re-runs `fundamentalC`. A typed borrower can
  hand the view to no one: operation arguments are closed data, the answer is free of `'x`, and
  an unrestricted continuation captures only persistent values (`multiShot_ref_refused`).
- **What would falsify it.** A `PDerives` program using R1 that gets stuck, leaks, answers a
  value outside its type, or trips §6.1's tag check, on some run (by `adequacyD_pin`, any of the
  first three refutes `PinLaw`). The test is programs (§6); no Lean refutation is attempted.

**`PinLoop`.**

- **Evidence: less.** No lender-side lemma at an observation boundary exists; GhostEnd's are at
  stops. LoopBorrow showed the *refold* route fails (`refoldKripke_false`: the Kripke order of the
  state between observations cannot see the lend's lifetime, at a consumer frame that arises,
  `refold_fails_at_consumer_frame`) and that a pull-form lending yield is excluded
  (`not_lendingYield_imm`). Its README's promotion route is a register of open lends in
  `wpTS`/`TW`, a model change; R2 asserts instead. R2 does not take the refold route: like `PinStop`, it
  re-derives the state's relation from the steps' derivations at the fresh lifetime, and its
  outputs `B`, `R` are free of `'x`, so it hands no lending yield out.
- **Why it should be true.** `imm` only: the place is read-only while lent and unreachable
  between observations (the owner is in the loop's state), so its content is the same at every
  observation, and duplicate `imm` views are sound.
- **What would falsify it.** A `PDerives` program using R2 that misbehaves on some run, as above.
- **Minimisation not done.** A lender-side lemma for R2 (GhostEnd's `ewpTS_I_frameR` re-applied
  per observation) would reduce `PinLoop` to a borrower-side statement. NOT
  DETERMINED whether it goes through; it is U8.

---

## 5. How it threads

- **Statements.** `fundamentalC_pin (hPin : PinLaw) : PDerives Δ Γ e j → SemJ Δ Γ e j` and
  `adequacyC_pin (hPin : PinLaw) : PDerives ∅ [] e (F 1) → Steps ∅ e ∅ ()`, with
  `adequacyD_pin`/`adequacyD_pin_safe` for every run. PROVED (§4.2).
- **Unconditional where possible.** A program that uses neither R1 nor R2 is a `CDerives`
  program, and `fundamentalC`, `adequacyC`, `adequacyD` cover it with no hypothesis. L0 programs
  are among them.
- **In Core (U5).** `PDerives` moves to Core as `CDerivesP`, beside `CDerives`, which is
  unchanged. The checker emits a `CDerives` derivation when it uses no relaxed rule, and a
  `CDerivesP` one otherwise. `bcc check` prints the program's assurance on one line, `assurance:
  unconditional` or `assurance: PinLaw (R1 at 23:5, 41:3; R2 at 30:7)`, and `bcc trusted` lists
  the same in the generated trusted base. The programmer writes nothing (no `trust`).
- **BOXED-κ** composes with both: its case in `fundamentalC_pin` is `handleV_compatCB` on the
  handled computation's `SemC`, which the induction hypothesis gives (U1).

---

## 6. The falsifier and the test suite

### 6.1 Does the machine detect a dangling or aliased use? No.

Determined from the code:

- **Memory steps.** `load`, `store` and `free` step only at a location present in the memory
  (`h : μ ℓ = some v`, `Paper/S3_Dynamics/Definitions.lean:250`–`256`); `alloc` takes a location
  with `μ ℓ = none`. A use of a freed location that was not reallocated is a stuck configuration.
- **Reuse.** `wpTS` quantifies over every allocator (`Core/Alloc.lean`), including ones that
  reuse a freed location, and `runM` allocates one past the largest location in use
  (`Core/Run.lean`), which reuses a freed top location. A use after free then reads the new
  cell's content. `Demonic.lean`'s `mapProgC_every_run` is such a run, and it is safe because the
  program is typed.
- **Aliasing and stale views.** A borrow is the bare location `ℓ`; the machine keeps no
  permission, kind or lifetime. Two `mut` views of one live cell, or a view used after its lend
  ended while the owner lives, load and store with no stuck state.
- **Leaks** are detected: adequacy ends at the empty memory.

So a falsifying program shows up as: a stuck run (use of a freed, unreused location), a leak, or a
wrong answer. Aliasing that happens to compute the expected answer is invisible.

**The minimal dynamic check** (BUILT, U4), in `bcc interp`, not the semantics:

1. **A never-reuse allocator**: every `alloc` takes a location never used before. Every use after
   free is then stuck.
2. **Tagged locations** (as Stacked Borrows, simplified to BoLo's lends): each location carries a
   stack of lend tags `(id, kind)`; a view value carries its tag; `withbor`/`withload` push, the
   callback's return pops. At a stop crossed by a relaxed lend the tag is marked *suspended*; at
   the resumption it is reactivated, not replaced (ghost end re-lends the same place to the same
   view). An access through a tag that is not live, or a write through any tag while a `mut` tag
   above it is live, or any access by the owner while a tag is live, is an error.
3. **Differential runs**: each program under the leastFree allocator, the never-reuse allocator
   and the tagged interpreter must give the same answer with `live 0`.

**Built (U4).** `Backend/Falsify.lean`, `bcc interp --alloc least | --check fresh | --check tags`
(and `bcc kernel interp`), `scripts/falsify.sh`. Determined while building it: `bcc interp`'s
default (`Support`'s `Mem.alloc`) already never reuses a location (its `next` only grows), so the
reusing run is the new `--alloc least` (`Alloc.leastFree`, as `runM`).

- *How tags are attached.* The erasure has no mark at a lend (`withbor1`/`withbor2`/`withbor3`,
  the slice and block borrows all erase to `withbor`; the unwinding forms to `withborUE d`;
  `withload`/`withloadU` to `withload`). Before a tagged run, these closed terms are replaced by
  forms calling three interpreter-only markers (a literal applied to an argument, which no typed
  program contains): `LEND` pushes a fresh tag over the source's cells (a location, or a family's
  `n` cells) and hands the callback the view through it; `RETAG` sees `withload`'s contents through
  a fresh `imm` tag; `END t` frames the callback. No erasure, kernel term or other stage changes.
- *Kinds.* `withbor1` and `withbor2` erase alike, so a lend from an owner has kind `lend`
  (exclusive, `imm` or `mut` unknown); a lend from a view (`withbor3`) is `mut`; `withload`'s is
  `imm`. A write through an `imm` view lent by `withbor1` is therefore not detected.
- *Suspension.* A tag is active exactly when its `END` frame is on the path from the term's root to
  the redex. A resuming operation that crosses the frame suspends the tag (it stays live, inactive
  while the continuation is held, active again when it is resumed or cancelled, so a borrower's
  finaliser runs with it active); an abortive one ends it.
- *Checks.* An access through an ended tag, through an inactive one, a free through a view, a
  write through an `imm` tag, any access through a tag (or the owner) under a live exclusive tag,
  a write under a live `imm` one, and a lend not ended at the end of the run.
- *Observation boundaries.* A `main` that returns a loop is driven one observation at a time. At
  each boundary between observations (and before the first) every live tag must be *suspended*:
  a resuming operation crossed its frame and the frame has not been on the running path since, so
  the lend is held by the loop's state, inside a suspended continuation. A live tag that is not
  suspended is reported ("active at an observation boundary"), and once the loop finishes no tag
  may be live (`checkBoundary`, `checkEnded`, `driveSource`). Before R1 the harness asked for
  every lend to have ended at each boundary, which a generator holding a relaxed lend between
  observations breaks (`corpus/async-r1-drain.bc`). The negative test `neg-active-at-boundary`
  begins a lend with no frame and answers the rest of the loop: it is reported at the first
  boundary.
- *Results.* Every corpus program the source stage runs (149; five `no-source` programs are too
  large for it), `bc/lend-loop-term.bc` and the 41 kernel programs pass all four modes with one
  output and `live 0`; no resuming operation crossed a lend in any of them (none can before
  R1/R2). Eight untyped negative tests (`Backend/FalsifyTests.lean`, `bcc kernel negatives`) trip
  each check; with `--alloc least` the use after free answers silently.

### 6.2 The adversarial list

Rejections are by the rules of §3.4; acceptances must run cleanly under §6.1's check. All are in
`experiments/AsyncCap/bc/reject` and `bc/accept`, surface provisional.

| # | program | verdict | why |
|---|---|---|---|
| 1 | use-after-scope via a stored task (`n1`): a task spawned into an outer scheduler captures a borrow from an inner block | **reject** | BOXED-κ: the task's context does not outlive the queue's bound |
| 2 | two tasks holding `mut` borrows of one cell (`n2`) | **reject** | `mut` is linear; the second capture is a second use (B6) |
| 3 | a task resumed after its captured borrow's scope ended | **reject** (same as 1) | the only way to resume it after the scope is to store it beyond the scope, which BOXED-κ refuses |
| 4 | cancellation while holding a lend (A6, `corpus/async-cancel.bc`) | **accept**, runs: finalisers innermost first, `live 0` | `withborR_compat`'s cancel path: the lend ends, the owner's finaliser runs (PROVED lender side) |
| 5 | a task stored in a queue that outlives a captured borrow (`n3`) | **reject** | `[]I`/BOXED-κ: the queue's box is at the lend's lifetime, and the block's result must outlive it |
| 6 | swap or move of a task's state while it is suspended (`accept/m1`) | **accept**, runs `[13, 7]` | the state holds the owner (a pointer); cells do not move (§3.5) |
| 7 | nested handlers inside tasks: a generator over a borrowed array, inside a relaxed lend, awaiting between elements (`accept/m2`) | **accept**, runs `[60]` | `yield` is caught inside the borrower and crosses no lend (Law 2's `InStop`); `await` crosses it (R1) |
| 8 | an awaiting callback passed to a HOF and **stored** (`n8`) | **reject** when it captures a task-local borrow | storing is `[]I`, whose context premise fails; passed and only called, it is accepted (A4) |
| 9 | recursion inside a task (`accept/m3`) | **accept**, runs `[1, 6]` | `bounded_fix` at every row (`boundedFix_compatX`); one heap object per level |
| 10 | spawn inside a task, the spawned block capturing a held borrow (`n9`) | **reject** | the view would leave the lend through an operation argument (`Row.ResumeO`) and outlive it (BOXED-κ). Spawning with no lend open is accepted (OQ-61 of the draft spec) |
| 11 | an abortive operation crossing a relaxed lend (`n4`) | **reject (v1)** | `Row.ResumeO`; OQ-1 |
| 12 | the view handed to a handler as an operation argument (`n5`) | **reject** | `Row.ResumeO`: arguments are closed data |
| 13 | a loop state holding a `mut` view (`n6`) | **reject** | R2 is `imm` only; `LoopLend` reports it today |
| 14 | an unrestricted (multi-shot) operation inside a relaxed lend (`n7`) | **reject** | `Row.ResumeO` excludes `unr` |
| 15 | stress (U7): many tasks, each with nested relaxed lends of several locals and closures over them, interleaved under a random schedule, with cancellations | **accept**, every run under §6.1's check clean | this is the test of `PinStop` at the rules Law 2 did not derive (inner lends, closures over views) |
| 16 | a cancelled task whose finaliser writes through a view it holds: `borrow mut c { await () then … unwind (write through m) }`, cancelled at the `await` | **accept**, runs: the borrower's finaliser writes, then the lend ends and the owner's finaliser runs; `live 0` | `[then]` gives the finaliser the body's context. The run order is safe; a proof route that returns the owner first does not cover it (§4.3) |

The stress row is where `PinLaw` is most exposed: inner lends held across a stop, `[]I` of a
closure over a view, and cancel paths, which are exactly the parts not derived (§4.3).

---

## 7. Implementation plan

Ordered; each unit is one PR and turns the programs named green. No unit but U1 changes `CDerives`,
`fundamentalC` or `adequacyD`; U1 adds one rule and its case (SPEC §28).

| unit | content | turns green |
|---|---|---|
| **U0** | this entry; `experiments/AsyncCap` (the statements, `fundamentalC_pin`, adequacy) | — |
| **U1** | port BOXED-κ from `nominal-lifetimes` as a `CDerives` rule (`effHandleVB`), its case `handleV_compatCB`, one case per inversion; the checker emits it | `BoxedKappa`'s `sched-a.bc`, `sched-b.bc` in the corpus |
| **U2** | `lib/async.bc` (`Async`, `run`, `run_until_empty`, `run_logged`, task handles, `cancel`), and effectful blocks at the surface (#161, `docs/surface-callbacks.md` E2–E8: a block's row, its call, copies per use; a counted loop at a resuming row). EXISTS (SPEC §30): `Async`, `spawn`, `resume`, `cancel`, `queue`, `push`, `run_until_empty`; `spawn_logged` and `run_logged` (A5), `spawn_in` and `run_in` (tasks over an outer borrow) are SPEC §32 | A1, A4, A5, A6 (and E1, E6 from source) |
| **U3** | L0: segmenting a borrow block at a resuming operation when only the borrow crosses it (ADD-5's degenerate case), in `Frontend/Elab` beside `LoopLend` | A2's `reader`; `gen-self-borrow.bc` moves to the corpus |
| **U4** | the falsifier: never-reuse allocator and tagged interpreter in `bcc interp`; a script that runs every program three ways (§6.1) | the harness, run on A1, A2 (`reader`), A4 and the corpus |
| **U5** (built, SPEC §29) | R1 in Core: `CDerivesP` (AsyncCap's `PDerives`), `fundamentalC_pin`, `adequacyD_pin`; the checker's R1 (callback row `Row.ResumeO`, emitted only when L0 does not apply); `bcc check`/`bcc trusted` report `PinLaw`; the lowering keeps a cell lent across a suspension out of line, or the task record unmoved (§3.5) | A2, A5, A6; `n2`, `n4`, `n5`, `n7`, `n9` |
| **U6** | R2: `LoopLend` keeps its rewrite when the loop's state holds an `imm` view, emitting `lendLoopR` | A3; `n6`, `n1`, `n3`, `n8` (with U1) |
| **U7** | the adversarial suite (§6.2) in `corpus/reject` and the corpus, with the stress generator | §6.2 rows 1–15 |
| **U8** | proof track, independent of the others, not on the async path: prove R1's compatibility lemma (for example through Law 2's re-lendable reading, at a cancel table that re-lends for the borrower's finalisers, §4.3); a lender-side lemma at observation boundaries for R2 | shrinks `PinLaw`; no program changes |

---

## 8. Open questions

> **OQ-1. An abortive operation crossing a relaxed lend.** `borrow mut b { … await(); …?… }`
> with the error handled outside the block is rejected in v1 (`n4`). Options: (a) extend
> `Row.ResumeO` to rows mixing resuming and abortive operations, adding them to `PinStop`'s row
> (believed by the LIFO frame lemmas `wpTS_M_frameU` with GhostEnd's `Drop`; not checked); (b)
> keep v1 and have the elaborator move the handler inside the block where the error's type
> allows. (a) grows `PinLaw`; (b) costs programs.

> **OQ-2. `imm` relaxed lends, `withload` and folds whose algebra suspends.** Needed by
> `corpus/pending/async-borrow.bc` (a yield inside `fold_imm`'s algebra, under the fold's own
> loads). GhostEnd has the lender side (`RelendI`, `ewpTS_I_frameR`); the unwinding form and a
> relaxed `foldImm` are not built. Each would add one field to `PinLaw`.

> **OQ-3. A `mut` lend over a loop whose state holds the view.** R2 hands a fresh view at every
> observation, which is unsound beside a stale `mut` one. A `mut` R2 needs the interface
> "initialise the state from the view once, then step the state alone", so that one view exists.
> Needed for a task whose body loops forever with a `mut` local borrowed across `await` (a
> server loop).

> **OQ-4. A class grade (O2-g).** Only if an un-specialised shared body is wanted (code size, or
> separate compilation). Not needed by any unit.

> **OQ-5. `await` answering data inside a relaxed lend.** `Row.ResumeO` asks `o.B = 1`, as
> GhostEnd and Law 2 do. A join that returns the joined task's value is outside it while a lend
> is held; outside a lend it is ordinary.

---

## Sources

- `Core/EffDefs.lean:27`–`40` (`wpG`, conjuncts 37 and 40), `Core/EffBorrow.lean:133`
  (`Row.Unwind`), `Core/Types.lean:1761` (`VOutlivesR`), `Core/Compat.lean:497` (`boxI_compatC`),
  `Core/EffRules.lean:642` (`KapRel`), `:755` (`ewp_handle`), `Core/Fundamental.lean:508`
  (`fundamentalC`), `:668` (`adequacyC`), `Core/Demonic.lean:284`, `:312` (`fundamentalD`,
  `adequacyD`), `Core/Alloc.lean`, `Core/Run.lean`, `Paper/S3_Dynamics/Definitions.lean:247`–`256`.
- `experiments/GhostEnd` (`Open.lean`, `Drop.lean`, `ImmLend.lean`, `Relend.lean`, README);
  `experiments/LoopBorrow` (README, `Dormant.lean`); `experiments/HandlersAsBorrows`,
  `experiments/SecondClass`, `experiments/HandlersControl` READMEs.
- Branch `nominal-lifetimes`: `experiments/BoxedKappa` (README, `Stop.lean`, `Handle.lean`,
  `Programs.lean`, `bc/`), `research/effects/src/boxed-kappa-programs.md`,
  `research/effects/src/b-package-typing.md` (ADD-5, P5, P6),
  `research/effects/src/prior-art/rows-vs-capabilities.md` (O2, O2-lt, O2-g),
  `research/effects/src/synthesis.md` (D2a/D2b, Law 2).
- Branch `law2-typed-world`: `experiments/Law2` (README, `Target.lean`: `law2`, `law2_depth1`,
  `relendOfTyped'`), `experiments/DenseCarrier` (`core_not_relend_kU`),
  `research/effects/src/tier2-problems.md`.
- Branch `effects-async-a1`: `docs/surface-callbacks.md`, `Core/EffAsyncPrograms.lean`.
- `docs/prior-art-suspension-borrows.md` (§1.2 `Pin`, §6 the slice and the liveness
  elaboration).
- SPEC.md §11, §14 (*specialization at the callback's type*; *Borrow scopes over loops, per
  observation*; *Not covered*), §15 (*Stored generators*, *Self-reference*), §18, §19 (*Kinds of
  operation*, *Typing*, *Theorems*, *Lowering*, *Open*), §22, §23, §24.
