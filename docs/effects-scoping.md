# Effects and handlers (#18): scoping

Status: a scoping pass, not the design. Stage S1 is being built from it: S1a (effect signatures,
stateful handlers, `with`) is SPEC §18. Every surface spelling is provisional unless §6 marks it
as a one-way door. It answers the user's
"let's do a scoping pass first and see if we need to break it down further", and grounds the
syntax and semantics in prior art (§4, §5).

Inputs read: issue #18 with all its comments; #52, #119, #125; `docs/decisions.md`;
`docs/prior-art-effects-coeffects.md`; `docs/ideas-handlers-and-borrows.md`;
`docs/surface-cbpv.md` §§1, 2.9, 2.11, 5.7, 7; `docs/operator/README.md` and `operator.bc`
Part 1; SPEC §§2, 5, 7, 11, 12, 14, 15, 16; `experiments/Coeffects`, `CoeffectsStrict` and
`Grades` (READMEs); on branch `iteration-design`, `docs/rec-effect/README.md` and
`docs/prior-art-iteration-matrix.md`; the drafts `docs/platform-design.md` (branch
`platform-design`) and `docs/type-declarations-design.md` (branch `type-declarations`).

Contents: §0 summary · §1 what the core already has · §2 the decomposition · §3 staging · §4
prior art, per system · §5 comparison and recommendation per piece · §6 syntax sketches · §7
risks, tensions and open questions · §8 proposed sub-issues · §9 what I have not established ·
Sources.

---

## 0. Summary

**Most of #18 surfaces what the core already has.** Every effect idea on the issue has a core form
today (§1.1): a capability is a linear value lent by `withbor`; a resume-once handler clause is a
`!` call on that lent value; abort is a sum exit, as `count_try`'s `inr` and `return` through a
`for` already are; suspension is `ν` codata compiled as one state machine per body (SPEC §15);
divergence is `Loop` (SPEC §14); finalisation is SPEC §12's destructors and `ν`'s mandatory
`close`; and polymorphism over effects is SPEC §14's specialisation at the callback's computation
type. So the recommended principle is: **a handler's meaning is its elaboration into core**. Effect
safety is then the existing Fundamental Property and adequacy on the elaborated term, with no new
case. Rows never reach the core (decision 19). The erasure theorem's *statement* becomes nearly
free, and its useful content moves to per-class handler laws on the elaborated terms and to
cost-parity counts (§1.2).

**Where that breaks** (§1.3) is a short, named list, and it is where the kernel work is:

| kernel or semantics item | needed by | existing thread |
|---|---|---|
| K1. a borrow held across a suspension (a spanning lend) | async tasks that borrow; a `yield` under a borrow; projection ops across a `yield` | O1, `experiments/LoopBorrow`, #52 phase 5 |
| K2. codata observations that take input (resume *with a value*, later) | `await` that answers data; several tasks sharing one `Mut` capability | #96, operator O2 |
| K3. destructors that perform I/O or can fail | finalising abandoned continuations that hold host handles | SPEC §12 Open, platform §2.3 |
| K4. early exit out of a kernel fold (`fold_own`/`fold_imm`) | `raise` inside a fold over `μ` data | operator O5, matrix C2 |
| K5. structural and borrowed descent for `rec` | total recursion by size; `rec` over a borrowed tree | rec-effect R8, R9; matrix C2, C3 |

None of K1–K5 is needed for the first slice.

**Decomposition** (§2): fifteen pieces, E1–E15. Five are almost pure surfacing (signatures,
handlers, capability resolution, generators as `Yield`, IO bundles as handlers), seven are
elaboration and lowering work (resumption classes, erasure as acceptance, rows, polymorphism,
errors, `rec`/drivers/layers, `|>`), and three touch K1–K5 (finalisation, projection ops,
suspension with input).

**Recommended first slice** (§3, stage 1): *answering effects and `Fail`, erased, rows inferred*.
Effect signatures, stateful handlers with tail-resumptive clauses, `raise`/`try`, finalisation on
abort by the existing destructors, inferred rows with `total` as the only written promise, and
the handler laws for the two classes it has. It makes target example 2 (a fallible fold without
`try_fold`) and a first form of example 4 (a `Map` interface with two handlers, `get` answering a
copy) read well, and needs no kernel change.

**Prior art, in one line per piece** (§5): Effekt for capability passing, lexical resolution and
second-class callbacks; Koka for operation kinds by cost, `with` as handler application, and
`finally`; Helium and Effekt for named instances; Flix for the answering/control split in handler
syntax; OCaml 5 as the warning about abandoned continuations; Scala 3 capture checking as the
model for storing things that capture capabilities; Rust's keyword generics as what not to do
(colour-polymorphism syntax); Lean's `do` as the precedent for exits as sums.

**Recommended syntax** (§6, provisional): the issue's own `with` clause on signatures, which is
Effekt's implicit capability list, with a name added only when there are several instances:

```
effect Kube[T] { fn get(name: &str) -> T; fn apply(obj: &T) }
fn reconcile(foo: &Foo) -> Action with Kube[ConfigMap], Log, Requeue = …
fn sync(foo: &Foo) with src: Kube[ConfigMap], dst: Kube[ConfigMap] = dst.apply(&src.get(foo.name))
handler kube[T](c: &mut Client) for Kube[T] { get(n) -> c.fetch(n); apply(o) -> c.patch(o) }
controller(Foo, reconcile) |> timeout(30.s) |> retry(backoff) |> log(json(&mut stderr)) |> kube(&mut client)
```

---

## 1. What the core already has

This section answers the user's question, "some of 18 is just surfacing things that are already
in the kernel, right?". It classifies each effect idea as **(a)** surfacing what the core already
has, **(b)** elaboration or lowering work only, or **(c)** new in the kernel or the semantics.

### 1.1 Each effect idea, and its core form

| effect idea | core form today | class | where |
|---|---|---|---|
| a capability | a linear value (a cell with opaque content, or a record of them) lent by `withbor` for a scope; an operation takes `mut 'a C` | (a) | SPEC §11 *Capabilities*; decision 30; #18's body: `withbor h (Fun 'h. fun cap -> …)` |
| a handler | a value implementing the operations: a state cell plus `!` clause code, lent for the handled scope | (a) | SPEC §2's closure table, row `FnMut`: `(env, !code)` behind a `Mut` borrow |
| a handler with no state | the same with state `1`, which erases | (a) | unit erasure in the backend |
| resume once, in tail position | a `!` call on the lent capability | (a) | the ideas doc's row 1: "a stateful handler is a borrow presented through an interface" |
| never resume (abort) | a sum exit: the step answers `inr e` and the loop or body leaves | (a) | `count_try` (SPEC §16), `return`/`break` through `DivSt.exits` |
| resume once, later (suspend) | `ν` codata; one state machine per body; delegation by `yield from` | (a) | SPEC §7, §15 |
| resume once, not in tail position | a pushed frame: the continuation as defunctionalised data on a driver's stack | (b) | rec-effect R1 and `rec.bc` (hand-lowered, not in the library) |
| resume more than once | not provided; `copy` exists only at `!` types | excluded | decision (standing) |
| divergence | `Loop B R`, the delay bind, `div_fuel`; the runtime drives `main` | (a) | SPEC §14 |
| finalising an abandoned continuation | SPEC §12's derived destructors at the end of each path; `ν`'s mandatory `close`; the residual of what has no destructor | (a) | SPEC §7 *Destructor*, §12, §14 *The residual* |
| polymorphism over effects | specialisation of a function at the computation type of a callback argument, then the effect's own inference on the copy | (a) for parameters, (b) beyond | SPEC §14 *Higher-order functions* |
| an effect row in a type | nothing: answering effects are capability parameters (the context side), control effects are computation types (`F (B ⊕ E)`, `Loop`, `gen`) | (b), surface only | decision 19; operator README §2 |
| "no capability, no effect" | a theorem | (a) | `wpTSD_frame_own` (SPEC §11 *Theorems*) |
| erasing a stateless capability | nothing to erase: a control effect's capability is a name the elaborator resolves, and a stateless answering handler's state is `1` | (b) | `experiments/Grades` (grade 0) is not needed; see §1.3 item 6 |

### 1.2 The claim, tested: handlers defined by elaboration

**The claim.** If a handler is *defined* by its elaboration into the core terms of §1.1, then
there is no separate handler-level semantics to prove a lowering against, and effect safety
follows from the existing Fundamental Property. The erasure theorem is then nearly free.

**Where it holds.**

- **Safety is free.** The elaborator's output is core that the checker derives, returning a
  `CDerives` proof (decision 26: sugar "stays outside the trusted base anyway, because its output
  is a core program that the checker must derive"). `fundamentalC` and `adequacyC` apply
  unchanged, as they did for div (§14), generators (§15) and the `for` loop (§16). An effect
  program cannot be unsafe or leak, whatever the elaborator does.
- **Effect containment is free.** "A function given no capability performs no effect" is
  `wpTSD_frame_own`. For control effects it is the computation type: a function of type `F B`
  cannot suspend or abort.
- **The erasure theorem's statement is free, and empty.** With no reference semantics, "the
  erased lowering agrees with the handler semantics" is true by definition. What it would have
  meant has to be recovered in two other forms:
  1. **Handler laws on the elaborated terms.** The elaborator can be wrong about *meaning* while
     staying safe: it is outside the trusted base for safety, but it is the definition of what a
     handler does. The algebraic laws (the return clause; an operation's clause applied to the
     continuation; for tail-resumptive clauses, `handle E[op v] = handle E[clause v]`) are
     theorems about the elaboration *schema*, one per resumption class. They are small and
     generic. `experiments/CoeffectsStrict/Handler.lean` already proves the shape at one
     effect: "a deep handler of `{write : I32 ⇝ 1}` is the fold of its free model"
     (`handle_return`, `handle_write`, `handle_unique`).
  2. **Cost parity, measured.** The corpus counts (allocations, dispatched calls, copies) per
     resumption class, and the report of which shape each handler was lowered to (#126). This is
     a measurement, as the issue's acceptance already says ("corpus counts showing no allocation
     or indirection for the resume-once and abort cases").
- **Backend correctness** is unchanged: tested, not proved (SPEC §11 *Adequacy's scope*).

**Where it breaks.** Each item names what elaboration alone cannot do.

1. **Polymorphism over effects beyond whole-program parameters.** SPEC §14 specialises only at
   parameter types: "a callback's effect in a stored or returned type is the one its type says".
   Three cases fall outside:
   - a callback stored in data, including a handler record whose clauses have effects (operator
     O3). This is (b), an extension of the specialiser, but it is new design;
   - a callback inside a kernel fold's algebra (O4), which must be total `!` code (see item 4);
   - code compiled separately or chosen at run time (plugins, a multiplatform binary). It needs a
     general representation: an indirect call for answering operations and a request type for
     control ones. That is (b), but cost parity then means "like `dyn`", as the issue's
     refinement allows.
2. **Suspension across calls.** The whole-chain transformation exists: SPEC §14 specialises a
   function at a callback that loops, and §15 makes a call of a yielding callback a
   `yield from`. It breaks at three points, and only the third is elaboration:
   - a borrow held across the suspension (K1). §15 already rejects a `yield` inside a borrow
     block, and SPEC §14 says a lend that spans observations "needs a model change that is not
     verified (`experiments/LoopBorrow`)";
   - a resumption that passes a value in (K2). A state machine's observation takes no input
     (SPEC §7's `NuOk`); the operator avoids it by making `wait` return nothing;
   - suspension inside non-tail recursion: frames plus the machine, which rec-effect R1 and R10
     say needs "nothing new … beyond R1". (b).
3. **Operations that return a borrow into handler state.** A borrow at the handler's own
   lifetime, through the pointer to its storage, is excluded by the model: SPEC §5 Open,
   "Same-lifetime views through a pointer are excluded by the update relation
   (`experiments/FrameEnd`, `imm_view_rejected`, `mut_view_rejected`)". What is expressible is a
   *projection*: the handler lends a view at a fresh, shorter lifetime to a block, as `withload`
   does. That is (b) if the surface is `let v = m.get(k)` elaborated as a lend for the rest of the
   block (decision 40's `let r = &x`). A projection held across a suspension is K1 again.
4. **Early exit from a kernel fold.** `fold_own` and `fold_imm` are constants whose algebra is
   total `!` code. A `raise` inside one either propagates as a sum to the end of the fold (O5:
   "A fold raises at the *last* bad element in list order") or needs a descent with an exit
   (matrix C2), which is a new constant: (c), K4.
5. **Rows in the core.** Not needed. Answering effects are capability parameters and control
   effects are computation types. Decision 19 forbids a judgment index "for later". So the
   claim holds here: rows are a surface and report artefact.
6. **Erasure of capabilities.** #52 records "zero-cost via erased (grade 0) capabilities (proved
   in experiments/Grades, not landed)". Elaboration does not need grades: a control effect's
   capability is a name resolved by the elaborator and never materialised, and an answering
   handler's capability is its state, which is exactly what the hand-written program would
   pass. So (b), with no kernel grade.
7. **Totality of `rec`.** A `rec` elaborated to a machine under `fix` is div. Total recursion by
   size needs the descent the checker can see (R8) and borrowed descent at one lifetime (R9):
   K5, (c). Deferrable: `fuel` and data-sized drivers give totality meanwhile.
8. **Finalisation that performs I/O.** Abandoning a continuation runs destructors; a host
   handle's destructor is an extern that can fail (SPEC §12 Open: "Whether such a type gets an
   implicit destructor, and what a failing one does, is not decided"). The platform draft (§2.3)
   calls its kernel side "small: `dtorE` is built from existing rules", with `dtor_wf` taking
   the extern context. K3, (c)-small.

**Verdict.** The claim holds for everything the first two stages need. It breaks in exactly
K1–K5, and each of those already has an issue or an experiment. The recommendation is to adopt
"a handler's meaning is its elaboration" as the design principle, and to replace "an erasure
theorem" in #18's acceptance by: (i) the elaborated program checks (free); (ii) handler laws per
resumption class, proved on the elaboration schema; (iii) cost-parity counts per class, with the
lowering shape reported (#126).

---
## 2. The decomposition

Fifteen pieces. The candidate list is revised in four ways:

- *Handlers* and *resumption classes* stay separate, but a fifth class is added: **resume once,
  not in tail position** (a clause that resumes and then does more work: `memo`'s store after a
  miss, a timing span, a transaction). The issue's erasure table has no row for it. It lowers to
  a pushed frame (rec-effect R1), which is the issue's refinement's "non-tail recursion: a
  stack".
- *Erasure* becomes an acceptance piece, not a lowering piece: with handlers defined by
  elaboration (§1.2) the lowering *is* the elaboration, so what remains is the laws and the
  counts.
- *Effect polymorphism* is split from *rows*: rows are syntax and inference; polymorphism is the
  specialiser, and its extension to stored callbacks is separate design (§1.3 item 1).
- *Suspension with input* is split off from generators and deferred to #52: it is K2.

Each piece gives: what it decides; the target examples of #18 (numbered as in the issue's last
comment: 1 fib with layers, 2 fallible fold, 3 named capabilities, 4 `Map` with handlers, 5 the
reconciler chain, 6 the controller loop, 7 the platform bundle); its class (§1); kernel impact
and a rough proof burden; dependencies; and whether it is a one-way door.

### E1. Effect signatures

- **Decides:** how an effect and its operations are declared: `effect Kube[T] { fn get(name:
  &str) -> T; … }`; type parameters on effects (`Kube[ConfigMap]`); whether an operation's
  resumption class is in the signature (Koka's `fun`/`ctl`) or read off the handler (#52's
  refinement: "no separate operation-kind annotation is needed"); an operation that returns
  `never` (abort, forced by its type).
- **Examples:** all.
- **Class:** (a)/(b). An effect is a record type of operations over a lent state; it elaborates
  through the type-declarations draft's "name plus an isomorphism" (its §2), with no kernel
  former.
- **Kernel:** none. **Proof:** none beyond the checker's derivation.
- **Depends on:** type declarations (records, type parameters; branch `type-declarations`).
- **One-way door:** *yes*, for where the resumption class is stated. If it is in the handler
  only (the standing decision), a function's computation type depends on the handler installed
  above it, so every function between an operation and its handler is specialised per handler.
  That is the decided no-colouring mechanism, and it must be accepted with its code-size cost.

### E2. Handlers: definition and installation

- **Decides:** the handler form (`handler h(state) for E { op(x) -> e }`); installation (`with h
  { … }`, or `body |> h`, E10); state (parameters lent for the scope); the return clause; deep by
  default at the surface, with shallow as the primitive (decision 15: "one observation is a
  shallow handler, and a deep handler is a fold or a loop"); `finally`/`initially` clauses.
- **Examples:** 2, 4, 5, 7.
- **Class:** (a) for the answering and abort cases: a handler is a value lent by `withbor`, and
  its clauses are `!` code over the threaded state (rec-effect R2: "State in layers is threaded,
  not captured"). (b) for the elaboration of a body under it.
- **Kernel:** none. **Proof:** handler laws per class (E5), on the schema.
- **Depends on:** E1.
- **One-way door:** no, apart from the resumption notation (E4).

### E3. Capabilities: resolution and named instances

- **Decides:** how an operation call finds its handler: implicitly, lexically, to the innermost
  handler of that effect in scope (Effekt), or by a name when there are several; how names appear
  in signatures (`with src: Kube, dst: Kube`); how a capability is passed to callees (implicitly
  by the elaborator, as SPEC §11's `&mut c` lend); what can capture a capability and be stored
  (E6).
- **Examples:** 3 (two clusters, two maps, two caches), 5, 7; #18's first comment: "two nested
  same-typed capabilities".
- **Class:** (a): capabilities are values lent per call today (SPEC §11 *Sugar*, decision 38).
  (b): the implicit passing and resolution.
- **Kernel:** none. **Proof:** none. The frame theorem `wpTSD_frame_own` already says a callee
  given no capability cannot touch it.
- **Depends on:** E2.
- **One-way door:** *yes*: lexical resolution (Effekt, Helium) against dynamic, innermost-at-run-
  time resolution (Koka, OCaml). They differ when a closure made under one handler runs under
  another. The standing decision is lexical.

### E4. Resumption classes and their typing

- **Decides:** the five classes and how each is recognised and typed:

  | class | clause shape | core form | lowering | cost-parity reference |
  |---|---|---|---|---|
  | 0: abort | never uses `k`; or the op returns `never` | sum exit | a branch, early return | Rust `?` / `return Err` |
  | 1, tail | answers a value | `!` call on the lent state | a direct call, inlined when known | a method call |
  | 1, non-tail | resumes, then more work | a pushed frame | a frame on a driver's stack, or the native stack | an explicit stack, recursion |
  | 1, later | stores `k` | `ν` state machine | a stackless state machine | Rust `async`, `gen` |
  | many | resumes twice | — | excluded, or an explicit copy at `!` types | an explicit clone |

  and how the continuation appears in a clause: implicitly for answering clauses, as a linear
  value `k` otherwise (so the surviving shift is visible in the handler, decision 26).
- **Examples:** 1 (tail and non-tail `rec`, `memo`'s store), 2 (abort), 5, 6.
- **Class:** (a) for 0, tail-1 and later-1; (b) for non-tail-1 (the frame machinery exists only
  hand-lowered, in `rec.bc`).
- **Kernel:** none. Multi-shot stays excluded. **Proof:** the class is read off the handler's
  type (#52: "the lowering is decided by SHIFT CANCELLATION … read off the handler's type"), so
  nothing to prove beyond E5's laws.
- **Depends on:** E2.
- **One-way door:** *yes*, for the clause notation (implicit answer vs explicit `k`), because it
  fixes what a reader sees of cost.

### E5. Erasure: acceptance

- **Decides:** #18's acceptance, restated per §1.2: the elaborated program checks; the handler
  laws per class hold on the elaboration schema; corpus counts per class; the report of the
  lowering shape (#126).
- **Examples:** all, as tests.
- **Class:** (b).
- **Kernel:** none. **Proof:** one lemma family per class, over the schema. The model is
  `CoeffectsStrict/Handler.lean` (a deep handler is the fold of its free model). Moderate: each
  law is an equation between two elaborated terms under `wpTS`.
- **Depends on:** E4.
- **One-way door:** no.

### E6. Effect polymorphism by specialisation

- **Decides:** extending SPEC §14's specialisation from "parameter types only" to: callbacks
  stored in a *known* record (a handler record, an adapter's state); observations of an iterator
  argument; fold algebras (O4, as elaboration where the fold's result is the effect's
  computation type); the representation for code that is not specialised (separate compilation,
  run-time choice), with its cost visible. Also: what a stored callback may capture (a
  capability borrow bounds its lifetime, as a System C box's capture set does), and what that
  needs from #9 and #58 (a many-use closure that captures an `imm` borrow).
- **Examples:** 5 (a handler record whose `send` suspends under one handler and not another,
  O3), 6, and every `map` with an effectful callback.
- **Class:** (b), with (c) dependencies: #9 widens promotion, a kernel rule.
- **Kernel:** none for the specialiser. **Proof:** none (elaboration). #9 has its own.
- **Depends on:** E3, E7 (rows give the key of a specialisation); SPEC §14.
- **One-way door:** *yes*, for what a stored callback's type says about its effects (written
  row, captured capabilities by lifetime, or nothing). Decision 6 of typed elaboration fixes it
  to "its written type" today.

### E7. Effect rows at the surface

- **Decides:** inferred rows (as div is inferred in declaration order, SPEC §14), a written row
  as a checked promise (as `total`), the spelling (`with E, F` after the signature), what `..`
  means in a library signature ("specialise here", operator N1), and the reports (`bcc sig`, the
  RBAC generator's input).
- **Examples:** 5 ("RBAC is generated from the effect row"), 2, 7.
- **Class:** (b), surface and reports only. No row in the core (decision 19).
- **Kernel:** none. **Proof:** none.
- **Depends on:** E1, E3.
- **One-way door:** *yes*, for whether rows are ever *required* (in exported signatures, for
  separate compilation). Recommendation: never required, as `div` is never required.

### E8. Errors: `Fail` as the first effect

- **Decides:** `effect Fail[E] { fn raise(e: E) -> never }`; the handlers `try` (to a sum),
  `catch` (in place), `map_err`; that `?` disappears; the retirement of `A + E` results in the
  library (decision 46: "Errors are sums (provisional until the error effect, #18)"); how an
  abort leaves loops (`count_try`'s exit), `for` bodies, generators and nested handlers; what
  happens to live values with no destructor on the abort path (E9); `return` and `break` as
  private aborts (operator N5).
- **Examples:** 2; the reconciler's `Fail[KubeError]`; the platform draft's `IoError`.
- **Class:** (a) the sum exit exists; (b) elaboration of a body with `raise` on its spine,
  reusing `DivSt.exits`. (c) only for early exit from a kernel fold (K4).
- **Kernel:** none for the first slice; K4 if a `raise` inside `fold_own`/`fold_imm` must stop
  the fold. **Proof:** the abort-class law (E5). K4 is a constant with a machine step, like
  `count_try` (SPEC §16), with its own compatibility lemma.
- **Depends on:** E2, E4, E9.
- **One-way door:** *yes*, for `try` returning a sum vs `catch` in place as the primary form, and
  for `?`'s removal.

### E9. Finalisation and cancellation

- **Decides:** what runs when a continuation is abandoned (abort, `close`, a lost race, a
  timeout): the destructors of SPEC §12 in reverse binding order; `close` of each held codata;
  the handing back of values with no destructor (a capability, a class-3 thunk) through the
  residual, or a rejection of the abort while one is live; `finally` clauses; effectful and
  failing destructors (K3; #18's design note on files, "Leaning: 3 as the idiom, 1 as the
  default destructor").
- **Examples:** 5 (`timeout`), 6 (a cancelled watch), the file design note; #52 phase 3 ("the
  close/unwind cancel path").
- **Class:** (a) destructors, `close` and residuals exist; (b) placing them on abort paths; (c)
  K3.
- **Kernel:** K3 only (small, per the platform draft §2.3). **Proof:** `dtor_wf` with the extern
  context.
- **Depends on:** E4.
- **One-way door:** *yes*: whether an abort is legal while a value with no destructor is live
  (reject, or hand it to the handler with the error, as `close` hands back a residual). Operator
  O5 prefers the second.

### E10. `rec`, drivers and layers

- **Decides:** implicit `rec` (a self-call, or a call within a strongly connected group, is
  `rec`); the open step and the closed default (`f` is `f |> fix`); drivers `fix`, `deep`,
  tabulation; layers `memo`, `fuel`; that totality comes from the driver (R7); groups by SCC and
  its report; memo keys (R5).
- **Examples:** 1; #125's `eval_step |> fix |> object_store |> stdio`.
- **Class:** (b): rec-effect §3.1's machine (`start`/`resume`, defunctionalised frames), made by
  the elaborator from SPEC §15's one-state-machine walk with one more kind of resumption point.
  Drivers are library code over `unfold`. (c) only for K5 (total structural and borrowed
  descent).
- **Kernel:** none; K5 later. **Proof:** none for the elaboration; the non-tail-1 law (E5).
- **Depends on:** E2, E4, E8 (a stop), E11 (`|>`).
- **One-way door:** *yes*: implicit `rec` makes self-reference legal on the surface, which
  decision 24 excluded ("There is no general direct recursion on the surface"). It must be
  confirmed that decision 24 is revised to "direct recursion is `rec`, run by a driver".

### E11. `|>` as handler application

- **Decides:** one rule for `|>`: `e |> f(a…)` is `f(e, a…)`, with `e` suspended (thunked) when
  `f`'s first parameter is a computation; innermost first; the order of a chain is semantics.
- **Examples:** 1, 5, 6; #125.
- **Class:** (b), surface only.
- **Kernel:** none. **Proof:** none.
- **Depends on:** E2; #17, #59.
- **One-way door:** *yes*: the piped position. Draft 0 puts it last (`surface-cbpv` §2.9:
  "`e |> f(a, …)` is `f(a, …, e)`"); the operator and the adapters put it first (decision 40:
  "draft 0 puts the piped value last (#17), and #109's adapters take the source first"). And
  whether `|>` may suspend its left side is a semantic choice, not a spelling.

### E12. Effects on generators: `Yield`

- **Decides:** `yield` as the operation of `effect Yield[T]`; `gen fn` and `gen { }` as the
  handler that stores the continuation (SPEC §15's machine, unchanged); `for` over a generator as
  the consumer; effects inside a generator (a fallible source, a generator holding a
  capability) as the sum of computation types (operator README §2: "`Async` together with
  `Yield<T>` is `iter (Wait + T) B K`").
- **Examples:** 6; the operator's watch stream; #18's acceptance test "an EXTERNAL iterator over
  a borrowed pointer-linked tree, built as fold_imm + yield under a suspending handler".
- **Class:** (a): this is SPEC §15 re-read as a handler. (b) for effects combined inside.
- **Kernel:** none. **Proof:** the later-1 law (E5).
- **Depends on:** E1, E2, E4.
- **One-way door:** no: `yield` stays a keyword-like call either way.

### E13. Borrowing through operations (projection operations)

- **Decides:** how "an operation returns a borrow into the handler's storage" is typed: as a
  projection that lends a view at a fresh, shorter lifetime to the rest of a block (the
  `withload` shape; Hylo's yield-once subscript; the iteration matrix §7.3's "yield-once
  projection without a coroutine"), since a view at the handler's own lifetime is excluded
  (SPEC §5 Open); the surface `let v = m.get(k)` as a lend for the rest of the block (decision
  40); `get_mut` exclusive; the copy-out alternative (#119's branded cells: "copy in/out, no
  reference into the interior").
- **Examples:** 4 (the hard case).
- **Class:** (b) for the scoped form; (c) K1 for a projection held across a suspension. A view
  at the handler's lifetime is not recommended: it contradicts a refutation in our model.
- **Kernel:** none for the scoped form. **Proof:** that the projection's derived type checks
  (a `withbor`/`withload` composition); I have not built it.
- **Depends on:** E2, E3; decision 40's lend-for-the-rest-of-the-block.
- **One-way door:** *yes*: whether `let v = m.get(k)` means a scoped projection (rest of block)
  or a copy. Programs written against one read differently under the other.

### E14. IO and platform bundles as handlers

- **Decides:** each capability of SPEC §11 and the platform draft's catalogue becomes an
  `effect` (the platform draft §2.9: "each capability's operations become an `effect`
  signature"); the platform package is the outermost handler; ambient only in `main`; tests
  swap handlers; the answering level (`block_on`) vs the scheduler (#52) as two handlers of the
  same operations.
- **Examples:** 5 (tests swap the bottom handlers), 7.
- **Class:** (a): SPEC §11 *Designed, not built*: "a capability can be served by any value
  meeting the extern's type: the host, the model … or later a user-defined handler (#18)". (b):
  bundles as implicit capability lists.
- **Kernel:** none (the platform draft's `withborS` at `opq` is "one check of `withborS`'s
  proof"). **Proof:** none new; each handler over host externs meets its contract as today.
- **Depends on:** E3, E8 (`IoError`); platform stage P1.
- **One-way door:** no.

### E15. Suspension with input, and the async bridge (deferred to #52)

- **Decides:** resumption with a value (`await` answering data); several tasks sharing one `Mut`
  capability (operator O2); borrows across a suspension (O1); `timeout`, `race`, `merge` over
  suspended computations.
- **Examples:** 5 (`timeout`), 6 (`merge(timers.due())`).
- **Class:** (c): K1, K2.
- **Kernel:** #96 (input observations on `ν`), the spanning lend. **Proof:** each is a model
  question, with a failure criterion already written on #96.
- **Depends on:** E9, E12.
- **One-way door:** no, at this stage.

### 2.1 Dependency graph

```
 type declarations (branch type-declarations)     SPEC §14 specialisation   §15 machine   §12 dtors
          │                                                │                     │             │
          E1 signatures                                    │                     │             │
          │                                                │                     │             │
          E2 handlers ─────────────┬──────────────┬────────┼─────────────┐       │             │
          │                        │              │        │             │       │             │
          E3 capabilities/names    E4 resumption classes ◄─┼─────────────┼───────┘             │
          │    │                   │    │   │              │             │                     │
          │    │                   │    │   E9 finalisation ◄────────────┼─────────────────────┘
          │    │                   │    │   │         │                  │
          │    E7 rows ◄───────────┘    │   │         │                  │
          │    │                        E5 erasure (acceptance)          │
          │    E6 polymorphism ◄────────────┘ │                          │
          │                                   E8 Fail ◄──────────────────┘ (E2, E4, E9)
          │                                   │
          E13 projections      E11 |> ◄─── #17/#59
          │                    │
          E14 IO/platform      E10 rec, drivers, layers ◄── E8, E11
          (◄ E3, E8, P1)       E12 Yield ◄── E1, E2, E4
                               E15 suspension with input ◄── E9, E12, #96, O1
```

Read an arrow as "is needed by". The spine is E1 → E2 → E4 → {E5, E8, E9}; everything else
hangs off it.

### 2.2 The pieces by class

| piece | (a) surfacing | (b) elaboration/lowering | (c) kernel or semantics |
|---|---|---|---|
| E1 signatures | ● | ● | |
| E2 handlers | ● | ● | |
| E3 capabilities, names | ● | ● | |
| E4 resumption classes | ● (0, tail, later) | ● (non-tail) | |
| E5 erasure | | ● | |
| E6 polymorphism | ● (parameters) | ● (stored, folds, separate) | #9 (promotion) |
| E7 rows | | ● | |
| E8 `Fail` | ● | ● | K4 (fold exit), optional |
| E9 finalisation | ● | ● | K3 |
| E10 `rec` | | ● | K5, later |
| E11 `|>` | | ● | |
| E12 `Yield` | ● | ● | |
| E13 projections | | ● | K1 across a suspension |
| E14 IO/platform | ● | ● | |
| E15 suspension with input | | | K1, K2 |

---

## 3. Staging

**Principle.** Land what is surfacing and elaboration first, prove the handler laws as each
class arrives, and leave K1–K5 to the stages whose programs need them. Each stage lands under
decision 17 ("A feature is done when it compiles"): spec entry, checker, lowering, corpus
programs, counts.

| stage | pieces | kernel | target examples it makes read well | deliberately deferred |
|---|---|---|---|---|
| **S1. Answering effects and `Fail`, erased, rows inferred** | E1, E2, E4 (classes 0 and tail-1), E5 (those two laws), E7 (inferred; `total` the only written promise), E8, E9 (abort paths with existing destructors) | none | **2** (fallible fold, no `try_fold`, no `?`); **4** in a first form (a `Map` effect with two handlers; `get` answers a copy) | names (S2); `raise` stopping a kernel fold early (K4); projections (S4) |
| **S2. Named capabilities and platform bundles** | E3 (names, lexical resolution), E14, E7 (written rows, the RBAC report) | none (the `withborS` at `opq` check) | **3** (two clusters, two maps, two caches); **7** (`wasi` and `posix` handlers); **5** without `timeout` (handlers in a chain, tests swap the bottom, RBAC from the row) | stored callbacks with effects |
| **S3. `rec`, drivers, layers, `|>`** | E10, E11, E4 (non-tail-1), E5 (its law) | none | **1** (`fib |> memo(cache) |> fuel(1000) |> fix`); **5**'s chain order as semantics; #125's `eval_step |> fix` | K5 (total descent) |
| **S4. `Yield`, effects inside generators, projections, stored callbacks** | E12, E13 (scoped form), E6 (stored callbacks, fold algebras), E4 (later-1 law) | none (K1 rejected with a message) | **4**'s hard case (`get` lends a view to the rest of the block); **6** without `merge` (the watch loop as a `for` over a fallible, suspending source) | K1 |
| **S5 (#52). Suspension with input, cancellation of tasks** | E15, E9 (K3) | K1, K2, K3 | **5**'s `timeout`; **6**'s `merge(timers.due())` | multi-shot |

**The first slice** is S1. It changes the most code patterns (every `A + E` result, every `?`,
every `try_fold`-shaped loop), which is why the issue sequenced #18 after the string work, and
it needs no kernel change. Its acceptance:

- a corpus program folding over fallible elements, written with `raise` and `try`, with no sum
  threaded by hand, whose counts equal the hand-written sum version's;
- the same program under two handlers of `Fail` (to a sum, and a `catch` that substitutes a
  default), from one source;
- a `Map` effect with an association-list handler and a sorted-array handler, one client, two
  runs; `get` answers by copy;
- the abort and tail-1 laws, proved on the elaboration schema;
- `bcc check` reports each inferred row, and each handler's lowering shape.

---

## 4. Prior art, per system

Each entry answers: how an operation is declared, called and handled; how effects appear in
types; how polymorphism over effects is written; how multiple instances are named; what compiles
to what; and what it means for us. Every quotation was checked against the saved text of the
source named at the head of the entry (URLs under **Sources**). Where a source was not read, the
entry says so. Tags as in `docs/prior-art-sessions.md` are not repeated per quote; the heading
says which parts were read.

### 4.1 Koka

Read: the Koka book (koka-lang.github.io/koka/doc/book.html), §§2.3, 3.4; Xie and Leijen,
*Generalized Evidence Passing for Effect Handlers*, ICFP 2021 (author's copy); Xie, Cong,
Ikemori, Leijen, *First-Class Names for Effect Handlers*, OOPSLA 2022 (author's copy); the
compiler's `lib/std/core/hnd.kk` and `samples/handlers/named/ask.kk`. Not read: Leijen POPL 2017.

- **Declare.** `effect raise` / `ctl raise( msg : string ) : a`; one-operation sugar `effect
  ctl raise(…)`; `effect val width : int`.
- **Call.** A plain call: `if y==0 then raise("div-by-zero") else x / y`.
- **Handle.** A handler is a function over the action: "The handler{ <ops> } expression is a
  function that itself expects a function argument over which the handler is scoped", with the
  statement form `with ctl ask() resume(21)`, which scopes over the rest of the block.
- **Operation kinds, and their cost.**
  - `ctl`: "The resume function is implicitly bound by a ctl operation and resumes back to the
    call-site with the given result." Multi-shot is allowed, and "Since resume is a first-class
    function … it is possible to store it in a list for example to implement a scheduler".
  - `fun`: defined as a `ctl` that resumes with its body's value; "when the operation is a
    tail-resumptive fun, it calls it directly as a regular function … This gives fun (and val)
    operations a performance cost very similar to virtual method calls". Declaring `fun` in the
    effect restricts every handler to `fun`.
  - `val`: a `fun` returning a fixed value.
  - `final ctl`: undocumented in the book; in the runtime it is `clause-never`, a clause that
    never resumes and so needs no resumption.
  - `linear effect`: "Use linear effect to declare effects whose operations are always
    tail-resumptive and use only linear effects themselves", which "removes the need for the
    monadic transformation".
- **Types and polymorphism.** Rows with variables, inferred: `map : (xs : list<a>, f : (a) -> e
  b) -> e list<b>`; `<l|e>` extends a row; duplicate labels are allowed.
- **Instances.** `mask<eff>(action)` skips the innermost handler ("The expression
  mask<eff>(action) modularly masks any effect operations in eff inside the action"), and the
  OOPSLA 2022 paper argues its limit: "if we use mask to choose among nested handlers, we must
  know the exact number and order of handlers surrounding an expression." Hence named handlers
  (`named effect`, `with r <- named handler …`, `r1.ask()`), made safe by scoped effects.
- **Compiles to.** "it compiles handlers into an internal free monad based on multi-prompt
  delimited control … that only allocates continuations in the case one is actually yielding up
  to a general ctl operation"; "The Koka compiler uses (generalized) evidence passing … to pass
  down handler information to each call-site". Memory by Perceus reference counting.
- **Finalisation.** `finally` "is always executed when either returning normally, or when
  unwinding for a non-resuming operation"; `initially` reruns on a second resumption. The book
  admits the multi-shot hazard: a second resume finds "the file handle will be closed again".
- **For us.** Koka supplies the cost vocabulary (`fun` is a call, `ctl` captures), the
  `with`-as-handler-application form, and `finally`. We differ in three places: the kind is read
  off the handler (the standing decision) rather than declared per operation; resolution is
  lexical, not by evidence at run time; and there is no reference counting to fall back on.

### 4.2 Effekt

Read: the Effekt tour (effects, captures, computation, regions, FFI), the documentation on
effect polymorphism and implementation; Brachthäuser, Schuster, Ostermann, *Effects as
Capabilities*, OOPSLA 2020; Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects,
Capabilities, and Boxes*, OOPSLA 2022; Schuster, Brachthäuser, Ostermann, *Zero-cost Effect
Handlers by Staging* (tech report); Muhcu et al., ICFP 2025 (LLVM backend); Voigt et al., OOPSLA
2025 (abstract and examples).

- **Declare.** `interface Exception { def throw(msg: String): Nothing }`; one-operation sugar
  `effect tell(): Int`.
- **Call.** Either on an explicit capability (`exc.throw("uhoh")`) or implicitly with a keyword:
  "every operation can also be used as an effect by omitting the receiver and prepending the
  keyword do".
- **Handle.** "Each handler consists of a try block, followed by one or more handlers";
  `try { … } with exc: Exception { … }` names the capability; `resume` is implicit in a clause.
  Resolution is lexical (the historical lift-inference page shows an operation resolving to the
  handler in scope where it was written).
- **Types.** An effect set after a slash, `Double / { Exception }`, and separately a capture set
  on values: "an effect is an open demand; a capture is a fixed capability."
- **Polymorphism, without variables.** "Effekt does not have language constructs for type-level
  effect variables or quantification over effects … polymorphism implicitly arises from the
  calling context".
- **Instances.** "Handlers (implicitly or explicitly) introduce capabilities that are then passed
  to the position where an effect is used."
- **Second-class blocks.** "Functions (and all other computation types) are second-class in
  Effekt"; "Effekt distinguishes between values (that can be returned and stored) and
  computation (that can be passed, but not returned)". Storing needs a box: "Boxing converts a
  second-class value to a first-class value" and the box's type records its captures. OOPSLA
  2022: "tracked blocks in System C correspond to second-class values".
- **Compiles to.** Capability-passing style, then Core (System C), then JavaScript, Chez Scheme
  or LLVM. The staging paper assumes the handlers and their order are known statically: "Guided
  by the stack shape, we then perform an iterated CPS translation". The LLVM backend "enables
  constant-time continuation capture and resumption when resumed exactly once". I have not
  verified that the current compiler monomorphises.
- **Resources.** Voigt et al. add `on suspend` / `on resume` / `on return` clauses and "state and
  prove a theorem of resource safety", as an extension of the research language.
- **For us.** The closest system. Its thesis is the standing decision ("effects elaborate to
  capabilities passed implicitly, resolved lexically"), its "polymorphism from the calling
  context" is SPEC §14's specialisation, and its staging paper's premise (handlers known
  statically) is our whole-program assumption. We differ in having no `do` (the standing
  decision), and in using lifetimes where Effekt uses second-class-ness (§7.1).

### 4.3 Eff

Read: Bauer and Pretnar, *Programming with algebraic effects and handlers*, arXiv 1203.1539
(2012, the version with instances); Pretnar's tutorial (eff-lang.org/handlers-tutorial.pdf);
the current repository's `examples/choice.eff`, `threads.eff` and README.

- **Declare, call.** Today `effect Decide : bool;;`, called with a keyword: `perform Decide`. In
  2012, operations belonged to an effect type (`type choice = effect operation decide : unit ->
  bool end`) and were called on an instance: `c# decide ()`.
- **Handle.** `handler | effect Decide k -> k true @ k false | x -> [x]` (multi-shot, deep), with
  a `finally` clause (`| finally x -> x initial`).
- **Types.** The implementation's types carry no effects: "Types in eff are like those of ML [9]
  in the sense that they do not capture any information about computational effects" (2012).
  The tutorial's calculus does: "Every computation type has the form A ! ∆".
- **Instances.** First-class, generated: "The computation new E generates a fresh effect
  instance of effect type E." Instances carry *resources*, a state and default behaviour; real
  I/O is the predefined instance `std`.
- **Compiles to.** A prototype interpreter.
- **For us.** Eff's 2012 `new E` with a resource is the nearest ancestor of "a capability is a
  linear value with a model" (SPEC §11): the resource is our opaque cell's model, and `std` is
  our `stdout`. Its instances are dynamic; ours are lexical.

### 4.4 Frank

Read: Convent, Lindley, McBride, McLaughlin, *Doo Bee Doo Bee Doo*, JFP 2020; the POPL 2017
paper's future-work section.

- **Declare, call.** `interface State S = get : S | put : S -> Unit`; commands are called as
  functions (`receive!` for a nullary one). No keyword.
- **Handle.** No handler construct: "A function is but the special case of a Frank operator that
  interprets no commands." A handler is an operator that pattern-matches requests in an argument
  (`state s <get -> k> = state s (k s)`), and several arguments make a multihandler. Shallow:
  "Frank’s continuation variables are shallow in that they capture only the rest of the
  subordinated computation, not the result of handling it".
- **Types and polymorphism.** "Effect typing in Frank employs a novel form of effect
  polymorphism which avoids mentioning effect variables in source code. This is achieved by
  propagating an ambient ability inwards". `map : {{X -> Y} -> List X -> List Y}` is shorthand
  for the version with `[ε |]` on both arrows.
- **Instances.** By position: "an ability is a map from interfaces to lists of interface
  instances. When invoking a command, it is always directed at the right-most interface
  instance". Adaptors reshape it; `mask` "skips the nearest enclosing handler for the specified
  effect".
- **Linearity.** Future work: "for State, it is usual for the handler to invoke the continuation
  exactly once, meaning that there is no need to allocate space for the continuation in the
  heap".
- **For us.** The ambient ability is the model for *inferred* rows with no effect variables in
  source; decision 15's "shallow primitive, deep derived" is Frank's position. Positional
  instances and adaptors are what names replace (Helium, §4.6).

### 4.5 Links

Read: Hillerström and Lindley, *Liberating Effects with Rows and Handlers*, TyDe 2016;
Hillerström, Lindley, Atkey, *Effect Handlers via Generalised Continuations*, JFP 2020; the Links
wiki pages *Effect-Sugar* and *Control-flow-linearity*.

- **Declare, call.** No declaration: an operation is a label in a row. "In Links, abstract
  operations like Move, are invoked using the do primitive, for instance `do Move(Alice,3)`".
- **Handle.** `handle(m) { case Return(x) -> x case Move(p,n,k) -> … }`; deep by default,
  shallow with `shallowhandler`: "Whereas a deep handler performs a fold over a computation, a
  shallow handler merely performs a case-split." Parameterised handlers thread a state value.
  Multi-shot.
- **Types.** "the function arrow (->) is prefixed by a row enclosed in curly braces. This row is
  the effect signature, or effect row, of the function." Rémy-style rows with presence
  polymorphism.
- **Instances.** None: "Rows have the property that they mention each label at most once."
- **Compiles to.** A generalised CEK machine on the server; CPS to JavaScript on the client.
- **Linearity.** The CFL extension: "The CFL extension tracks control-flow linearity, which
  enables sound combination of linear types (session types) and multi-shot effect handlers";
  "`A =@ B` represents signatures for control-flow-linear operations", and its continuation "is
  given a linear function type and must be used exactly once".
- **For us.** The deep-is-a-fold, shallow-is-a-case-split sentence is decision 15 exactly.
  Links' CFL is the one system that types *which operations* may capture a linear context; we
  get that from the handler's type instead (E4).

### 4.6 Helium

Read: Biernacki, Piróg, Polesiuk, Sieczkowski, *Abstracting Algebraic Effects*, POPL 2019, and
*Binders by Day, Labels by Night: Effect Instances via Lexically Scoped Handlers*, POPL 2020
(authors' copies); the README.

- **Declare, call.** `effect Reader A = { ask : Unit => A }`; `signature State (X : Type) = | put
  : X => Unit | get : Unit => X`. Called as a plain function; with an instance, `get 'x ()`.
- **Handle.** `handle e with | ask () => resume "Dave" | return x => x end`, deep, multi-shot,
  with `finally`.
- **Types.** POPL 2019: rows with variables (`[Error, Nondet | r]`). POPL 2020 drops them: "we do
  not need row types in our calculus, as finite sets of (instances of) effects are sufficient".
- **Instances.** POPL 2020's contribution: "lexically scoped effects in which each use (an
  “instance”) of an effect can be singled out by name, bound by an enclosing handler and tracked
  in the type of the expression". One instance stays implicit; with two, "our typechecking
  algorithm would protest if we omitted the instance arguments." The paper argues names are
  "more amenable for efficient implementation" than coercions (`lift`, swap).
- **Compiles to.** A CEK-like abstract machine; a bytecode VM.
- **For us.** This is the standing decision "effects by default, named capabilities when there
  are several instances", with a type system and a soundness proof. Its lexical instances are
  also what our capabilities already are: a name bound by the enclosing `withbor`.

### 4.7 Idris 2 (and Idris 1's `Effects`)

Read: the Idris 2 documentation for `Control.App` (introduction, interfaces, exceptions and
state, linear resources); Idris 1's `Effects` tutorial, kept separate.

- **Idris 2 has no handlers.** An "operation" is an interface method returning `App`
  (`interface Console e where putChar : Char -> App {l} e ()`); an implementation of the
  interface is the "handler". Effects appear as constraints on an index: `helloCount : Has
  [Console, State Counter Int] es => App es ()`.
- **Instances.** By an erased type-level tag: "The tag is used purely to distinguish between
  different states, and is not required at run-time"; `get Counter`.
- **Linearity.** `App` tracks whether a computation may throw "so that we can know where it is
  safe to reference linear resources"; `bindL` "guarantees to run the continuation exactly
  once".
- **Idris 1 `Effects`.** Labels: "The ::: operator allows an arbitrary label to be given to an
  effect" (`'Tag ::: STATE Int`), used as `'Tag :- get`. Handlers there are multi-shot.
- **For us.** Idris 2's `NoThrow` path is the same insight as §7.10: a linear resource is safe to
  hold only where no abort can abandon it. Its tags are erased names, as our control-effect
  capabilities are.

### 4.8 Unison

Read: the Unison documentation on abilities (fundamentals, using and writing abilities, the
language reference pages on declarations, function types, handlers, and the typing rule; the
FAQ); the JIT announcement.

- **Declare, call.** `structural ability Store a where Store.get : {Store a} a`; a plain call,
  no keyword.
- **Handle.** `handle e with h`, where `h` pattern-matches `{Store.get -> k}` and `{a}`. The
  handler re-installs itself by recursion (shallow in effect). "A handler can choose to call the
  continuation or not, or to call it multiple times."
- **Types and polymorphism.** "A function type in Unison like A -> B is really syntactic sugar
  for a type A ->{e} B"; `List.map : (a ->{𝕖} b) -> [a] ->{𝕖} [b]`; requirements are inferred.
- **Instances.** None: "No, you cannot require two of the same ability in a function … Our type
  system does not currently support this."
- **Compiles to.** "the way abilities work in the intermediate code and interpreter is based on
  delimited continuations"; a Chez Scheme JIT. "The IO ability is the only Unison ability whose
  handler is provided by the runtime".
- **For us.** Unison is the closest in *surface feel* to what #18 asks (plain calls, inferred
  requirements, `IO` handled by the runtime as our platform package is), and it shows the cost
  of having no instances.

### 4.9 OCaml 5

Read: the manual, *Language extensions: effect handlers* (5.3); Sivaramakrishnan et al.,
*Retrofitting Effect Handlers onto OCaml*, PLDI 2021 (§§1, 2, 5.2).

- **Declare, call.** `type _ Effect.t += Xchg: int -> int t`; `perform (Xchg 0)`.
- **Handle.** Deep, with syntax since 5.3: `try comp1 () with | effect (Xchg n), k -> continue k
  (n+1)` ("Here effect is a keyword which signifies that the Xchg n pattern matches effects and
  not exceptions"). "Unlike deep handlers, OCaml does not provide syntax support for shallow
  handlers." `continue` or `discontinue`.
- **Types.** None: "Unlike languages such as Eff and Koka, effect handlers in OCaml do not
  provide effect safety".
- **One-shot, dynamically.** "Attempting to use a continuation more than once raises a
  Continuation_already_resumed exception."
- **Abandoned continuations.** "Not resuming continuations will leak the memory allocated for
  the fibers as well as any resources that the suspended computation may hold." The remedy is
  `discontinue`, or a GC finaliser whose "runtime cost … is much more than the cost of capturing a
  continuation."
- **Compiles to.** Fibers: "runtime-managed, dynamically growing segments of stack". Stack
  switching, which decision 25 excludes as the semantics.
- **For us.** The warning case. What OCaml checks dynamically (one-shot) or leaves to the
  programmer (finalising an abandoned continuation) is, here, linearity: a continuation is a
  linear value, so an abandoned one is dropped by its destructor (§12), and a second resume does
  not type. #18's requirement "abandoned continuations are finalised" is exactly the gap OCaml
  documents.

### 4.10 Flix

Read: the Flix book (doc.flix.dev), chapters on effects and handlers; flix.dev FAQ and
principles; the compiler's `EffectBinder.scala` and `GenFunAndClosureClasses.scala`.

- **Declare.** `eff DivByZero { def divByZero(): Void }`; `eff Emit[t] { def emit(x: t): Unit }`.
- **Call.** A plain qualified call: `DivByZero.divByZero()`, `Emit.emit(b)`.
- **Handle.** `run { … } with handler DivByZero { def divByZero(_resume) = … }`; `resume` is an
  explicit last parameter of each clause; an operation returning `Void` cannot be resumed.
  "Flix effect handlers use dynamic scope, deep handlers, and support multiple resumptions."
  Stacked handlers: "The innermost handler (listed first) intercepts the original operation, and
  then delegates to the next outer handler."
- **Types and polymorphism.** Effect sets with Boolean formulas, explicit variables: `def map(f:
  a -> b \ ef, l: List[a]): List[b] \ ef`; handlers subtract (`\ ef - Amb`).
- **Instances.** None found; and "within a function, a polymorphic effect must be used with the
  same type arguments everywhere."
- **Compiles to.** "Flix has a whole-program optimizing compiler that uses monomorphization and
  inlining". The documentation does not say how handlers compile; the source suggests
  resumable frame objects for control-impure functions only (my reading of compiler code).
- **Finalisation.** "Note: Flix does not (yet) support a finally block."
- **For us.** Flix is the precedent for whole-program monomorphisation with handlers, for the
  `resume` parameter written explicitly (our E4 notation), and for `Void`/`never` forcing abort.

### 4.11 Ante

Read: the Ante language documentation (effects, handlers, implicits); the blog posts *Algebraic
Effects, Ownership, and Borrowing* (2024-02-20) and *Why Algebraic Effects?* (2025-05-21). The
2024 post says its ownership changes "are not yet reflected in the documentation".

- **Declare, call.** `effect Yield t =` with `yield: fn t -> Unit`, "a type holding several
  function values, similar to a trait"; a plain call.
- **Handle.** "handler <name> for <capability-expr> in <expr>"; `resume` in the clauses; deep.
  One-shot: "resume in Ante is typed as a FnOnce which limits it to only being called once".
  Tail-resumptiveness can be demanded: "it is possible to specify when declaring the effect that
  all handlers for it must be tail-resumptive".
- **Types.** A `can` clause: `yield_and_return_10 (): I32 can Yield I32`; a missing clause is
  pure and is checked. Polymorphism: `map (input: Vec a) (f: a -> b can e): Vec b can e`.
- **Instances.** By type argument (`Throw FileError, Throw ParseError`) or named handlers, which
  "are temporary and may be removed in the future".
- **Ownership (2024 post).** "Since a handler’s body may be called multiple times, it may not
  move any value in its environment." Borrowing out of a handler: "each function using the same
  Read (&own mut Box String) effect is considered to borrow from the same effect handler.
  Attempting to retrieve two owned, mutable references from the same handler then would be a
  lifetime error". A reference passed *into* an operation ties the resumption: "we cannot call
  resume until they are dropped." Resume kinds per operation (`fork.resume: FnMut _ _`).
- **Compiles to.** The 2024 post: "by converting effectful functions to continuation passing
  style (CPS) - like Ante does", and a footnote crediting Effekt's staging. I have not verified
  the current implementation.
- **For us.** The only other language combining handlers with Rust-style ownership. Its
  handler-as-lender is §7.3's projection; its `FnOnce` resume is our linear `k`; its per-op
  resume kinds are Koka's `fun`/`ctl` moved into the resume's type. Its admission that
  effect-polymorphic `map` then needs `given Clone e, Send e, Fn e.resume _` "would have to be
  manually specified on map" is what whole-program specialisation avoids.

### 4.12 Scala 3: capture checking and capabilities

Read: the Scala 3 reference pages *Capture Checking* and *CanThrow Capabilities*; the Gears book;
*Scoped Capabilities for Polymorphic Effects* (arXiv 2207.03402; abstract, introduction, box
rules).

- **Declare, call, provide.** A capability is a value: "In the effects as capabilities model, an
  effect is expressed as an (implicit) parameter of a certain type." It is passed by `using`:
  "It is quite natural to model capabilities with implicit parameters since it greatly reduces
  the wiring overhead once multiple capabilities are in play." There are no handlers: `try`
  provides `CanThrow`; Gears' `Async.blocking` provides the root `Async`.
- **Types.** Capture sets: `T^{c₁, …}`; "the new single arrow function type A -> B stands for a
  function that cannot capture any capabilities"; "The impure function type A => B is treated as
  an alias for A ->{cap} B."
- **Polymorphism.** Mostly implicit: "The signature of map does not have to account for effects.
  It takes a closure as always, but that closure may refer to capabilities in its free
  variables." Explicit capture-set variables `X^` where needed.
- **Instances.** They are values, named like any other (`def test1(async1: Async, others:
  List[Async])`).
- **Storing.** Escape checking: "if a capturing type is an instance of a type variable, that
  capturing type is not allowed to carry the universal capability cap", and "mutable variables
  cannot have universal capture sets."
- **Compiles to.** Ordinary or erased parameters: "all CanThrow capabilities are compile-time
  only artifacts; they do not have a runtime footprint"; "Boxing and unboxing has no runtime
  effect".
- **For us.** Scala is the precedent for (i) effects as implicit parameters with no handler
  machinery for the answering case, (ii) erasing the capability of an abort-only effect
  (`CanThrow` is `erased`), and (iii) storing capturing values under a checked bound, which is
  what our lifetimes do (§7.1).

### 4.13 Rust's effects and keyword-generics initiative (the contrast)

Read: the Inside Rust posts *Announcing the Keyword Generics Initiative* (2022-07-27) and
*Keyword Generics Progress Report: February 2023*; Wuyts, *Extending Rust's Effect System*; the
initiative's README; RFC 3513 (`gen` blocks); the async book; the Reference on block
expressions.

- **Effects are fixed keywords.** "What we're working on is intentionally limited to built-in
  keywords only". The goal: "to solve the function coloring problem 1 through the type system
  not just for async, but for const and all current and future function modifier keywords" (the
  `1` is the post's footnote marker).
- **Polymorphism is written.** `?async fn read_to_string(reader: &mut impl ?async Read)`, and
  "All generics eventually need to have their types known, and keyword generics are no
  different."
- **Call sites stay marked**: `copy(reader, writer).await?`; `.await` "is necessary to mark the
  cancellation point in case the function is compiled as async".
- **Colours are kept.** "In today's Rust application authors choose whether their application
  will be sync or async … What we're targeting is the choice made by library authors".
- **Compiles to.** State machines: "async transforms a block of code into a state machine that
  implements a trait called Future." `gen` blocks are "mostly implemented via existing
  coroutines … with an additional check forbidding holding borrows across yield points".
- **For us.** Rust shares our lowering (state machines, monomorphisation) and our self-borrow
  rule (§15's *Self-reference*), and differs in the surface: its polymorphism is written per
  function (`?async`) and its suspension points are marked. We take the lowering and leave the
  surface. The initiative's "sandwich problem" (`my_option.map(|x| x.await)`) is exactly what
  SPEC §14's specialisation at the callback's type already solves for div.

### 4.14 Lean 4's `do`

Read: Ullrich and de Moura, *'do' Unchained*, ICFP 2022 (§§1–2, parts of 3–4, 5.2–5.3); the
Lean reference manual's chapters on `do`, lifting and monad transformers.

- **Effects are monads**; operations are actions bound in `do`; several effects are a
  transformer stack, and "not all monad transformers commute."
- **Local imperative sugar is elaboration into effects.** "we
  implement return 𝑒 by raising 𝑒 as an exception (R1), … and finally catching the exception"; "local mutation is interpreted as a local
  state effect". And "so that the core language does not have to be changed."
- **Polymorphism.** Type-class constraints (`[Monad m] [MonadLiftT BaseIO m]`) with automatic
  lifts: "Lean automatically inserts lifts when they are available".
- **Instances.** By type: "A single monad may support multiple version of the same effect … As
  long as they have different types, it should be convenient to access both" (`getThe String`).
- **Compiles to.** Specialisation and inlining, after one fix: "We addressed this issue by using
  CPS versions of StateT and ExceptT monad transformers."
- **For us.** The direct precedent for S1: `return`, `break` and exceptions as elaborated exits
  with no core change, made cheap by specialisation. Our `count_try` exit plays `ForInStep`'s
  role (iteration matrix §7.2). Lean's instances-by-type are what our names improve on.

---

## 5. Comparison, and a recommendation per piece

### 5.1 The table

| system | declare | call | handler; shots | effects in types | polymorphism | several instances | compiles to |
|---|---|---|---|---|---|---|---|
| Koka | `effect` with `fun`/`val`/`ctl` ops | plain call | `with`/`handler`, deep; multi-shot | rows `<l\|e>` | row variables, inferred | `mask`; named handlers | evidence passing; multi-prompt control; `fun` a direct call |
| Effekt | `interface`, `effect` | `do op()` or `cap.op()` | `try … with`, lexical; multi-shot | set after `/`; capture sets | none written: from the calling context | capabilities named at the handler | capability passing; CPS; LLVM |
| Eff | `effect Op : t` (2012: effect types) | `perform` (2012: `c#op`) | `handler`, deep; multi-shot; `finally` | none in the implementation | HM only | 2012: `new E` instances with resources | interpreter |
| Frank | `interface` | plain call | operators on requests; shallow; multihandlers | ability `[I]` | implicit ambient ability | position; adaptors, `mask` | abstract machine |
| Links | none (labels) | `do Op` | `handle`, deep or `shallowhandler`; multi-shot | row on the arrow | Rémy rows, presence | none: labels unique | CEK; CPS to JS |
| Helium | `effect`/`signature` | plain call | `handle … with`, deep; `finally` | rows (2019), sets (2020) | row and instance variables | lexical instance names | abstract machine; VM |
| Idris 2 | interface over `App` | plain call in `do` | an implementation; no continuations | `Has [...] es` | constraints on `es` | erased type tags | ordinary code |
| Unison | `ability` | plain call | `handle … with`, re-installed; multi-shot | `->{A}` | `{g}` variables, inferred | not supported | delimited continuations |
| OCaml 5 | `Effect.t +=` | `perform` | `effect` pattern, deep; one-shot, checked dynamically | none | n/a | generative constructors | fibers (stack switching) |
| Flix | `eff` | plain qualified call | `run … with handler`, deep, dynamic; multi-shot | Boolean effect sets | explicit variables | none | whole-program monomorphisation |
| Ante | `effect` of fn values | plain call | `handle`, deep; `resume` is `FnOnce` | `can` clause | `can e` | type args; named handlers (temporary) | CPS (2024 post) |
| Scala 3 | capability class | method call, `using` | none: a scope provides it | capture sets `->{c}` | implicit; `X^` | ordinary values | ordinary or erased parameters |
| Rust KG | fixed keywords | `.await`, `?` marked | executor, `block_on` | `?async` etc. | written per function | n/a | state machines |
| Lean 4 | monad, transformer | action in `do` | `run` of a transformer | the monad `m α` | type-class constraints | by type (`getThe`) | specialised, CPS transformers |

### 5.2 Recommendation per piece

| piece | follow | why |
|---|---|---|
| E1 signatures | Koka's and Flix's `effect`/`eff` block with typed operations; Flix's `Void` (our `never`) forcing abort | the declaration is a record of typed operations in both; `never` makes the abort class a fact of the signature |
| E2 handlers | Koka's handler-as-function and `with`; Links' "deep is a fold, shallow is a case-split" | handler application is then ordinary application (E11), and decision 15 is already Links' position |
| E3 capabilities, names | Effekt (capabilities passed implicitly, lexical) plus Helium POPL 2020 (a name only when two instances are in scope, else an error) | exactly the standing decision, with a soundness story in print; Koka's own paper says `mask` needs "the exact number and order of handlers" |
| E4 resumption classes | Koka's cost vocabulary (`fun` a call, `ctl` a capture, `final ctl` never resumes), read off the handler as #52 decided; Flix's explicit `resume` parameter; Ante's `FnOnce` resume | Koka names the classes by cost; an explicit `k` keeps the surviving shift visible in the handler |
| E5 erasure | Effekt's staging premise (handlers known statically) and Lean's specialisation | both reach direct code by knowing the handler at compile time, as we do |
| E6 polymorphism | Effekt/Frank (no effect variables in source); Scala 3 capture checking for stored values | "polymorphism implicitly arises from the calling context" is SPEC §14; storing is bounded by lifetimes as Scala bounds it by capture sets |
| E7 rows | the issue's `with` clause, which is Scala's `using` and Ante's `can`; Unison's inference | written rows are optional promises; an implicit capability list reads as a parameter list |
| E8 `Fail` | Lean's `return` as an exception, elaborated with no core change; Scala's erased `CanThrow` | both show the abort effect as elaboration plus an erased capability |
| E9 finalisation | Koka's `finally`; OCaml 5's documentation as the counter-example | linearity gives what OCaml leaves to the programmer |
| E10 `rec` | rec-effect's own design; Koka's `with` for layers | no language read has recursion as a handled effect with drivers; the layers are Flix's "innermost … delegates to the next outer handler" |
| E11 `|>` | Koka's `with` statement and Effekt's "`with f(args);`" sugar, which pass the rest of the block as the last block argument | the same semantic move (the handled computation is an argument), applied to a chain |
| E12 `Yield` | Koka's generator (`ctl yield`), compiled as Rust's `gen` blocks are | SPEC §15 already is Rust's lowering |
| E13 projections | Hylo's yield-once subscripts; Ante's "borrow from the same effect handler" | the only precedents for a handler lending into its own state |
| E14 IO, platforms | Unison ("The IO ability is the only Unison ability whose handler is provided by the runtime"); Eff 2012's `std` resource | the platform package is that runtime handler, as a library |
| E15 suspension with input | Effekt's LLVM backend (one-shot constant-time capture) and Rust `async` as cost references | K2 is ours to design; nothing read has input observations on codata |

**Not followed.** Rust's written colour polymorphism (`?async`) and marked call sites; OCaml's
untyped effects and stack switching (decision 25); multi-shot as a default (every language but
OCaml and Ante has it, and Koka documents its hazard with resources); Koka's run-time evidence
(we resolve statically); Links' unique labels and Unison's missing instances (target 3 needs
two `Kube`s).

---

## 6. Syntax sketches

Three candidates, each following one line of prior art. The target examples are #18's; the
reconciler and watch loop are cut to their effect-relevant lines. All spellings are provisional.

- **A. `with` clauses (Effekt semantics, the issue's own spelling).** Rows are an implicit
  capability list after `with`; a name is added when there are several; handlers are functions
  over computations, applied with `|>` or installed with `handle`.
- **B. Koka-style rows and `with` statements.** Rows `/ {E}` (operator.bc's spelling); `with
  h { }` installs; `fun`/`ctl` kinds in the handler; named handlers `named`.
- **C. Frank/Unison abilities.** Abilities in brackets on the result (`-> {Kube} T`); handlers
  pattern-match requests with an explicit continuation.

### 6.1 fib with layers (target 1)

```
-- A
fn fib(n: i32) -> i32 = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }   -- self-calls are rec
let f = fib |> memo(&mut cache) |> fuel(1000) |> fix
f(30)

-- B
fun fib(n: int) : rec<int,int> int = if n < 2 then n else fib(n - 1) + fib(n - 2)
with fix
with fuel(1000)
with memo(&mut cache)
fib(30)

-- C
fib : Int -> {Rec Int Int} Int
fib n = if n < 2 then n else rec (n - 1) + rec (n - 2)
fix! (fuel 1000 (memo cache (fib 30)))
```

### 6.2 A fallible fold (target 2)

```
-- A
effect Fail[E] { fn raise(e: E) -> never }
fn total(xs: &[text]) -> i32 = {                   -- inferred: with Fail[ParseError]
  let mut s = 0
  for x in xs { s = s + parse_i32(x) }             -- parse_i32 raises; no ?, no try_fold
  s
}
let r = total(&lines) |> try                       -- r : i32 + ParseError

-- B
effect fail<e> { final ctl raise(e: e) : a }
fun total(xs: list<string>) : fail<parse-error> int
  var s := 0
  xs.foreach fn(x) s := s + parse-i32(x)
  s
val r = try { total(lines) }

-- C
total : [Text] -> {Fail ParseError} Int
total xs = foldl (\s x -> s + parseI32 x) 0 xs
r = handle total lines with { raise e -> Left e; v -> Right v }
```

### 6.3 Two named `Kube` instances (target 3)

```
-- A
fn sync(foo: &Foo) with src: Kube[ConfigMap], dst: Kube[ConfigMap] =
  dst.apply(&src.get(foo.name))
{ sync(&foo) } |> handle src = kube(&mut staging), dst = kube(&mut prod)

-- B
fun sync(foo: foo, src: ev<kube<config-map>>, dst: ev<kube<config-map>>) : <kube<config-map>> ()
  dst.apply(src.get(foo.name))
with src <- named kube(staging)
with dst <- named kube(prod)
sync(foo, src, dst)

-- C  (Unison has no instances; Frank would use an adaptor; the nearest is two effect types)
sync : Foo -> {Kube Staging ConfigMap, Kube Prod ConfigMap} ()
```

### 6.4 The reconciler chain (target 5)

```
-- A
fn reconcile(foo: &Foo) -> Action with Kube[ConfigMap], Log, Requeue = …
controller(Foo, reconcile) |> timeout(30.s) |> retry(backoff) |> log(json(&mut stderr)) |> kube(&mut client)

-- B
fun reconcile(foo: foo) : <kube<config-map>, log, requeue> action …
with kube(client)
with log(json(stderr))
with retry(backoff)
with timeout(30.s)
controller(foo, reconcile)

-- C
reconcile : Foo -> {Kube ConfigMap, Log, Requeue} Action
kube client (log (json stderr) (retry backoff (timeout 30s '(controller Foo reconcile))))
```

In A the chain reads innermost first, as #18 wants; in B the `with` statements read outermost
first; in C the nesting is explicit.

### 6.5 The watch loop (target 6; `merge` is #52's)

```
-- A
for ev in watch[Foo]() |> merge(timers.due()) {    -- a fallible, suspending source; a plain for
  match reconcile(&ev.obj) { Requeue(d) -> timers.add(ev.key, d); Done -> () }
}

-- B
for(watch<foo>().merge(timers.due())) fn(ev)
  match reconcile(ev.obj) { Requeue(d) -> timers.add(ev.key, d); Done -> () }

-- C
forEach (merge (watch Foo) (due timers)) (\ev -> case reconcile ev.obj of …)
```

### 6.6 A `Map` with two handlers (target 4)

```
-- A
effect Map[K, V] { fn get(k: &K) -> Option[&V]; fn insert(k: K, v: V) }   -- get: a projection (§7.3)
handler assoc[K, V](l: &mut List[(K, V)]) for Map[K, V] { get(k) -> lookup(l, k); insert(k, v) -> push(l, (k, v)) }
handler sorted[K, V](a: &mut Buf[(K, V)]) for Map[K, V] { get(k) -> bsearch(a, k); insert(k, v) -> place(a, k, v) }
fn count_words(ws: &[text]) with Map[text, i32] = for w in ws { let n = match get(&w) { Some(c) -> *c, None -> 0 }; insert(w, n + 1) }
{ count_words(&ws) } |> assoc(&mut l)
{ count_words(&ws) } |> sorted(&mut a)

-- B
effect map<k,v> { fun get(k: k) : maybe<v>; fun insert(k: k, v: v) : () }
with assoc(l)  count-words(ws)
with sorted(a) count-words(ws)

-- C
ability Map k v where get : k -> {Map k v} Optional v; insert : k -> v -> {Map k v} ()
handle countWords ws with assoc l
```

### 6.7 Recommendation

**A, provisionally.** Reasons:

- It is the spelling the issue already uses (`fn reconcile(foo: &Foo) with Kube[ConfigMap], Log,
  Requeue`), and it makes the standing decision visible: a row is a list of implicit
  capabilities, and naming one (`src: Kube`) turns it into a named capability with no second
  mechanism. Helium's rule completes it: a name is required exactly when two instances are in
  scope.
- `|>` reads the chain innermost first, which #18 asks for ("The order of the chain is
  semantics"); B's `with` statements read outermost first, the reverse of the chain.
- It needs no effect variables in source (Effekt, Frank), which suits decision 45's
  per-instance checking.
- B's kinds (`fun`/`ctl`) on operations contradict the standing decision that the class is read
  off the handler; C has no instances (Unison) or positional ones (Frank).

**One-way doors in A** (all flagged in §2): the handler clause notation (implicit answer vs
explicit `k`), `|>`'s piped position and its suspension of the left side, lexical resolution,
`let v = m.get(k)` as a projection, and whether rows are ever required. Everything else (`with`,
`handle`, `effect`, `handler`, `never`) is a spelling.

---

## 7. Risks, tensions and open questions

Only real ones, each with a recommendation. The first three are the ones the task named.

### 7.1 Effekt's second-class capabilities against our need to store things

**The tension.** Effekt gets effect polymorphism without row variables because blocks are
second class: a block that closes over a capability cannot be stored or returned unless it is
boxed, and the box records what it captured (§4.2). We must store things that use effects:
generators that hold a capability (SPEC §15 already does, handing it back in the residual),
handler records whose clauses have effects (operator O3), adapter pipelines, task pools (#52).

**What we already have is stronger than Effekt's rule, not weaker.** A capability here is a
borrow at a lifetime, or an owned cell. Something that captures a borrow at `'h` can be stored
anywhere its type says outlives `'h`, which is the outlives relation's job; System C's box with a
capture set, and Scala's capture sets (§4.12: "the new single arrow function type A -> B stands
for a function that cannot capture any capabilities"), are the same idea with capabilities in
place of lifetimes. So storing is allowed, and escape is checked by lifetimes, not by a
second-class restriction.

**Where it bites.** A closure that captures a borrow and is called many times is not `!` today
(operator O6: "A `!` closure captures only `!` values: not an `i32`, not an `imm` borrow").
Every stored effectful callback is either `FnOnce` (a linear thunk), or `FnMut`-shaped (`(env,
!code)` behind a `Mut`, SPEC §2's table), or waits for #9/#58.

**Recommendation.** Two tiers, as Effekt has them, but with lifetimes as the box:
- **parameter callbacks** (the common case) never capture their capabilities: the specialiser
  passes the caller's capabilities through (SPEC §14's latent demand). Zero cost, no closure.
- **stored callbacks** capture their capabilities at creation (lexical resolution), and their
  type carries the lifetime of what they captured. This is E6, and it makes #9 (promotion over
  persistent contexts) and #58 (implicit `imm` copies) prerequisites of S4, not of S1.

### 7.2 Row inference against per-instantiation checking (decision 45)

**The tension.** Decision 45: "A generic `fn`'s body is elaborated per instance … an error in a
generic body is reported at the first use that instantiates it, and a generic `fn` never called
is not elaborated". So a generic function's row is known only per instance. Three consequences:

1. **A generic function has no row of its own.** `map`'s row is its callback's; that is what
   `..` means in operator N1 ("specialize here"). Fine under whole-program compilation.
2. **A written row on a generic function is a promise checked per instance.** `fn f[A](…) with
   Log` means "every instance's row is within `{Log}`", and a violation is reported at the
   instantiating call, as body errors already are.
3. **Row inference is in declaration order today, and implicit `rec` breaks that.** SPEC §14:
   "Definitions are in dependency order (recursion is structured, decision 24), so one pass in
   declaration order infers this; there is no fixed point." Implicit `rec` (E10) makes groups;
   the row of a strongly connected group is the union over the group, a least fixed point over a
   finite lattice. Cheap, but it is a change to §14's stated algorithm.

**Recommendation.** Rows are inferred per instance, never required; a written row is a promise
checked per instance; the SCC fixed point replaces declaration order when E10 lands. For
separate compilation (not a goal now), an exported generic function must carry a written row
with `..`, and the specialiser's fallback is the general representation (§1.3 item 1).

### 7.3 How "an operation returns a borrow" can be typed at all

**The constraint.** A `get` returning `imm 'h V` into storage the handler reaches through a
pointer, at the handler's own lifetime `'h`, is a same-lifetime view through a pointer, which
"[is] excluded by the update relation (`experiments/FrameEnd`, `imm_view_rejected`,
`mut_view_rejected`)" (SPEC §5 Open). The borrow-splitting survey records the same: "L1 at the
same lifetime is refuted in the current model".

**What can be typed.** A *projection*: the operation lends a view at a fresh lifetime `'x`,
shorter than `'h`, to a continuation that returns something outliving `'x`. That is
`withload`'s shape (decision 29: "`withload` turns that borrow into the family of leaf views
`[Imm 'x A]` at a shorter `'x`"), and Hylo's yield-once subscript and Swift's yielding accessors
(iteration matrix §7.3: "Control comes back to the subscript once after the last use of the
yielded projection at the call site"). Ante takes the same line at the handler: "each function
using the same Read (&own mut Box String) effect is considered to borrow from the same effect
handler" (§4.11).

**Recommendation.**
- `let v = m.get(k); S` elaborates to the projection with `S` as the continuation: decision 40's
  "`let r = &x` lends `x` for the rest of the block", applied to an operation.
- While `v` is live, another operation on `m` is a borrow conflict if `m` was lent `mut` (one
  `get_mut` at a time), and allowed if `imm`.
- `v` held across a `yield` or `wait` is K1, rejected until the spanning lend exists, with the
  same message as §15's `yield` inside a borrow block.
- The copy-out form (`get` answers a value; #119's discipline) stays available and is what S1
  ships.
- Not recommended: a kernel extension that gives views at the handler's lifetime. It would
  reopen a refutation in our own model.

I have not built the projection's derived type in Lean.

### 7.4 "No `perform`" against the governing rule's visible shift

`docs/surface-cbpv.md` §1's table marks "an operation whose handler receives the continuation"
as a shift that never cancels, with the surface "**visible**: `suspend c.op(e)`", and decision 26
says sugar may not "hide a surviving polarity shift". The standing decision removes `perform`,
and with it `suspend`. The precedent is already there: SPEC §14's direct-style div call and §15's
yielding callback are unmarked surviving shifts. **Recommendation:** amend the governing rule so
that the visibility of a suspending operation is carried by the inferred row and by `bcc check`'s
report per call site (#126), not by a token; keep the continuation visible *in the handler*
(the explicit `k` of E4). This needs the user's confirmation, since it edits a rule.

### 7.5 "Effects elaborate to capabilities" is exact only for answering effects

The standing decision reads as if every effect becomes a capability. For control effects the
mechanism is the computation type (operator README §2: "They change the **computation type**
of every function that performs them"; #18's design note: "two kinds of effect, two
mechanisms"). A control effect still has a *name* resolved lexically (which `try` catches a
`raise`, with two nested `Fail[E]`), but no run-time value. **Recommendation:** state the
decision as "answering effects elaborate to capabilities passed implicitly; control effects
elaborate to computation types; both are resolved lexically by name". No behaviour changes.

### 7.6 Lexical resolution against "a control effect goes to whoever runs it"

The operator's `Async` is resolved dynamically: "a `wait` goes to whoever is running the
computation … not to the handler that was in scope where the code was written. That is what lets
`timeout` cancel a read performed by a body stream that the HTTP handler created." That is the
one place the design wants non-lexical resolution. **Recommendation:** keep resolution lexical,
and read `Async` as a computation type (a task is `iter Wait B K`), not as an operation looked
up in scope: the observer of the codata is whoever holds it, which is lexical in the holder.
This dissolves the tension, but it should be checked on the operator's `timeout` example in S5.

### 7.7 Implicit `rec` against decision 24

Decision 24: "There is no general direct recursion on the surface: it is a source of stack
overflows, accidental non-termination and invisible cost." Implicit `rec` makes `fib(n - 1)`
legal again. The rec-effect design answers all three objections (the driver makes the stack a
choice, totality comes from the driver, and the report names the stack shape), but the decision
text has to change. **Recommendation:** revise decision 24 explicitly in the E10 spec entry,
rather than let E10 contradict it silently.

### 7.8 `|>`'s piped position

Draft 0 pipes into the last argument; the operator, the adapters and every target example on
#18 pipe into the first (`fib |> memo(cache)` is `memo(fib, cache)`). And `controller(…) |>
timeout(30.s)` only means "run the controller under a timeout" if `|>` suspends its left side
when the parameter is a computation. **Recommendation:** first argument; suspend the left side
exactly when the parameter's type is a computation (type-directed, allowed by decision 26).
Settle #17/#59 with it. One-way door.

### 7.9 Code size from specialising per handler

With resumption classes read off the handler (E1's door), every function between an operation
and its handler is copied per distinct handler class above it. The operator names the cost:
"with the cost Rust's generics already have: one copy per instantiation". **Recommendation:**
accept it, measure it (a code-size column in the counts), and copy per *class* (answering,
abort, suspend), not per handler, where the handler's own code is a call: two answering
handlers of `Log` then share one copy of the client.

### 7.10 What to finalise when an abort meets a value with no destructor

A capability, a thunk of `F A` and a `μ` outside `FShape` have no destructor (SPEC §12 class
3). An abort that abandons one either is rejected, or hands it to the handler with the error.
The operator (O5) notes that its capabilities live in handlers and bodies hold only borrows,
"and a borrow just ends". **Recommendation:** S1 rejects the abort while a class-3 value is
live and names it (honest and reversible); the residual form, as `close` hands back a residual,
comes with E9 in S4/S5. rec-effect §9 lists the same question for frames: "Whether frames
holding a capability (a value with no destructor) can be dropped on a stop."

---

## 8. Proposed sub-issues

For the user to approve; none is created. Each is one spec entry or one design note, and lands
under decision 17.

1. **Effects S1a: effect signatures and stateful handlers (answering operations).** Declare
   `effect E[T] { fn op(…) -> … }` and `handler h(…) for E { op(x) -> e }`; install with `with h
   { … }`. Elaborate a handled body to a `withbor` of the handler's state with `!` clause calls
   (SPEC §2's `FnMut` row). Rows inferred, not written. Acceptance: a `Map` effect with two
   handlers and one client; tail-1 law on the elaboration schema; counts equal to the
   hand-written capability-passing program. No kernel change.
2. **Effects S1b: `Fail` as the first effect.** `raise`, `try`, `catch`, `map_err`; abort as a
   sum exit through `DivSt.exits` and `count_try`; destructors on the abort path; rejection of an
   abort while a class-3 value is live. Retire `A + E` results and `?` in `lib/`. Acceptance:
   the fallible fold (target 2) with counts equal to the sum version; the abort law. Records K4
   (early exit from a kernel fold) as open.
3. **Effects S1c: the handler laws and lowering reports.** Replace "an erasure theorem" in #18's
   acceptance by the per-class laws and the per-handler lowering shape in `bcc check` (#126).
   Prove the abort and tail-1 laws generically (after `CoeffectsStrict/Handler.lean`).
4. **Effects S2a: named capabilities and lexical resolution.** Names in `with` clauses when an
   effect appears twice; the innermost handler otherwise; an ambiguity error that asks for a
   name. Acceptance: two clusters, two maps, two caches (target 3); `handleFailList` and two
   nested same-typed capabilities (#18's first comment).
5. **Effects S2b: IO and platform bundles as handlers.** The SPEC §11 capabilities and the
   platform draft's catalogue as `effect`s; the platform package as the outermost handler;
   tests swap handlers; written rows as promises and the RBAC report from a row. Depends on
   platform stage P1. Acceptance: target 7, and target 5 without `timeout`.
6. **Effects S3a: `|>` as handler application.** First-argument piping, suspending the left side
   at a computation parameter; reconcile with #17/#59. Acceptance: the reconciler chain (target
   5) with its order observable in a test.
7. **Effects S3b: `rec`, drivers and layers.** Implicit `rec`, SCC groups, the machine of
   rec-effect §3.1 made by the elaborator; `fix`, `deep`, tabulation; `memo`, `fuel`; the
   non-tail-1 law; revise decision 24. Acceptance: target 1 and rec-effect's corpus; #125's
   first milestone.
8. **Effects S4a: `Yield` and effects inside generators.** SPEC §15 as a handler; a fallible,
   capability-holding generator as one source; #18's external-iterator acceptance test.
9. **Effects S4b: projection operations.** `let v = m.get(k)` as a scoped projection; the
   borrow-conflict rules; rejection across a suspension. Acceptance: target 4's hard case.
10. **Effects S4c: stored effectful callbacks.** Specialisation at known records and iterator
    observations (O3), effectful fold algebras (O4), lifetime-bounded capture; depends on #9 and
    #58.
11. **Design note: suspension with input and cancellation (K1, K2, K3), for #52.** Scope #96 and
    the spanning lend against the operator's `timeout` and the controller loop (targets 5, 6).

---

## 9. What I have not established

- That the projection form of §7.3 has a derived type in the core. I have argued it from
  `withload`'s shape and SPEC §5's refutation; I have not written the derivation.
- That the handler laws of E5 hold for the elaboration schemas as stated; `CoeffectsStrict`
  proves the shape at one effect only.
- That S1 needs no kernel change for every program in its acceptance list. It holds if `raise`
  is never inside a `fold_own`/`fold_imm` algebra; I have not checked the library's folds.
- That Effekt's current compiler monomorphises (the publication list places Lutze et al. under
  its compilation techniques, but that paper does not mention Effekt), and how Flix compiles
  handlers (only inferred from its compiler source).
- Ante's current implementation strategy, beyond its 2024 blog post.
- The size of the code growth from specialising per handler class (§7.9).
- Whether reading `Async` as a computation type (§7.6) serves the operator's `timeout` example.
- Leijen POPL 2017, Schuster et al. PLDI 2022 and ESOP 2022, Brady's Idris 1 effects paper, and
  the Eff-to-OCaml compilation paper were not read.

## Sources

Internal: the files listed at the head of this document, and issues #18, #52, #96, #119, #125.

External, as read (saved copies checked for every quote):

- Koka book, https://koka-lang.github.io/koka/doc/book.html
- Xie, Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021,
  https://xnning.github.io/papers/multip.pdf
- Xie, Cong, Ikemori, Leijen, *First-Class Names for Effect Handlers*, OOPSLA 2022,
  https://xnning.github.io/papers/oopsla22namedh.pdf
- Koka sources: https://raw.githubusercontent.com/koka-lang/koka/master/lib/std/core/hnd.kk,
  `samples/handlers/named/ask.kk`
- Effekt tour and docs, https://effekt-lang.org/tour/ (effects, captures, computation, regions,
  ffi), https://effekt-lang.org/docs/ (concepts, implementation)
- Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020,
  https://ps.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA
  2022, https://se.cs.uni-tuebingen.de/publications/brachthaeuser22effects.pdf
- Schuster, Brachthäuser, Ostermann, *Zero-cost Effect Handlers by Staging* (tech report);
  Muhcu et al., ICFP 2025; Voigt et al., OOPSLA 2025 (via the Effekt publications page)
- Flix book, https://doc.flix.dev/print.html; https://flix.dev/faq/; https://flix.dev/principles/
- Bauer, Pretnar, *Programming with algebraic effects and handlers*, https://arxiv.org/pdf/1203.1539;
  Pretnar, https://www.eff-lang.org/handlers-tutorial.pdf; the Eff repository's examples and README
- Convent, Lindley, McBride, McLaughlin, *Doo Bee Doo Bee Doo*, JFP 2020,
  https://homepages.inf.ed.ac.uk/slindley/papers/frankly-jfp.pdf; Lindley, McBride, McLaughlin,
  *Do Be Do Be Do*, https://arxiv.org/pdf/1611.09259
- Hillerström, Lindley, *Liberating Effects with Rows and Handlers*, TyDe 2016,
  https://homepages.inf.ed.ac.uk/slindley/papers/links-effect.pdf; Hillerström, Lindley, Atkey,
  *Effect Handlers via Generalised Continuations*, JFP 2020,
  https://homepages.inf.ed.ac.uk/slindley/papers/ehgc.pdf; the Links wiki (*Effect-Sugar*,
  *Control-flow-linearity*)
- Biernacki, Piróg, Polesiuk, Sieczkowski, *Abstracting Algebraic Effects*, POPL 2019,
  https://www.ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf, and *Binders by Day, Labels by Night*,
  POPL 2020, https://www.ii.uni.wroc.pl/~ppolesiuk/papers/popl20.pdf
- Idris 2 documentation, https://idris2.readthedocs.io/en/latest/app/; Idris 1 `Effects`,
  https://docs.idris-lang.org/en/latest/effects/
- Unison documentation, https://www.unison-lang.org/docs/ (abilities; language reference; FAQ);
  https://www.unison-lang.org/blog/jit-announce/
- OCaml manual, https://ocaml.org/manual/5.3/effects.html; Sivaramakrishnan et al.,
  *Retrofitting Effect Handlers onto OCaml*, PLDI 2021, https://arxiv.org/pdf/2104.00250
- Ante, https://antelang.org/docs/language/; https://antelang.org/blog/effects_ownership_and_borrowing/;
  https://antelang.org/blog/why_effects/
- Scala 3 reference, https://docs.scala-lang.org/scala3/reference/experimental/cc.html and
  `canthrow.html`; the Gears book, https://natsukagami.github.io/gears-book/print.html;
  https://arxiv.org/pdf/2207.03402
- Rust: https://blog.rust-lang.org/inside-rust/2022/07/27/keyword-generics/;
  https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report-feb-2023/;
  https://blog.yoshuawuyts.com/extending-rusts-effect-system/; the initiative's README;
  https://rust-lang.github.io/rfcs/3513-gen-blocks.html; the async book; the Reference, block
  expressions
- Lean: Ullrich, de Moura, *'do' Unchained*, ICFP 2022, https://lean-lang.org/papers/do.pdf; the
  Lean reference manual, *Functors, Monads and `do`-Notation*
