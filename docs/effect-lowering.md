# Effect lowering: handlers resolved statically, state machines last (#541)

A design for the backend's lowering of effects. It changes no code. Each claim is marked:

- **measured**: a run of `bcc`, `bcc-counts` or a script over the backend's own functions, on
  `origin/main` at `7a6d275`, reproducible by the commands given;
- **by inspection**: read off the code or SPEC, with no run behind it;
- **hypothesis**: argued here, not checked.

The hard requirements are #541's: every `perform` resolves statically to its handler's clause;
run-time choice only where the hand-written Rust program would choose at run time too; every
lowering visible in the closure or flat IR; every decided law and every borrow guarantee kept.

## 0. Summary

- **Inventory.** The 35 corpus programs with dispatched calls split as follows (§1.4):

  | class | programs | what dispatches |
  |---|---|---|
  | (a) Rust dispatches too | 3 whole, and part of 2 more | a queue that holds tasks of more than one body |
  | (b) our flow analysis | 1 (`clo-higher`) | one code called with closures of two codes |
  | (c) caused by a handler | 25 | a handler with a state (7); the two codes of a stored task or generator (8); one task body copied per spawn site (10) |
  | (d) a closure chain built by a fold | 4 whole, and part of 2 more | not effects; outside this design |

  `sched-a` and `sched-b` are counted under (a) and also have (d) sites.

  (c) is the large class, and none of it is a handler search. It comes from three representation
  choices: the state-passing encoding of a handler's state (SPEC §21); a codata value whose
  first and later states are different codes; and a copy per static name.
- **State machines that were never needed** (§1.5):
  - `bench/chain-yield`'s `yield` is a state machine, not a direct call. The `for` body has an
    `if`, and `Capture`'s test for a tail-resumptive clause (`tailClause?`) accepts a resume only
    when it is the clause's last call, not one resume in each arm of a `case`. Removing the `if`
    makes it a direct call (measured).
  - `sieve` and every program that reads its arguments run as the frontend's §14 state machine,
    which `drive` turns one observation at a time. `Capture` builds nothing in them.
  - `chain-gen`'s adapters are state machines because each adapter's instance never meets the
    generator it is given.
- **Pipeline** (§3).
  1. Specialise first.
  2. Classify every site by the law its clause satisfies.
  3. Lower the sites that need no continuation: direct calls, a branch, a native handler state.
  4. Run `Capture` last, on the continuations that really escape.
  5. Then #540's loops and its narrowed state.
  6. Adapters drained by one `for` become push stages, at elaboration.
- **No algebra hard stop.** No option here needs a decided law changed (§2.8). Two candidate
  lowerings would have; each is excluded by a condition stated where it applies.
- **No kernel change.** Every option is lowering or elaboration into terms the checker already
  types (§2.9).

## 1. Inventory

### 1.1 The passes, erasure to target

`Backend/Driver.lean`'s `closTypesOf` is `convert`, then `lowerEffects` = `capture`, `unwind`,
`collapseT`; `Flat.lower` calls the flow analysis and the layout types again.

| pass | file | decides | from | discards |
|---|---|---|---|---|
| elaboration, check, erasure | `Frontend/` | sites and names (§18, §38); one copy per assignment of sites (§18 *Rows*); copies per block row (§30) and per tunneled row (§33); each div body as one `unfold` (§14) | types, rows, lexical scope | types, rows, a site's clause kind, the handler's declaration, which `unfold` is which loop and who drives it (§1.2) |
| `Convert` | `Clos/Convert.lean` | ANF, closure codes, ownership; recognises fixed points, `swap`, η, literals, scoped cells, `ubind`'s `sel` code | the untyped erasure | nothing semantic; λ-structure becomes codes |
| `Poly` | `Clos/Poly.lean` | a polymorphic let used at different rows is converted per use | its own run of the effect analysis | — |
| `Capture` | `Clos/Capture.lean` | control sites to `drive`/`κ`/`Res` codes; which codes suspend; the conventions; tail-resumptive operations as direct calls; every other suspending code a machine | its own 0-CFA (`SFacts.of`), static names, clause shapes read syntactically | `hnd`/`perform`: afterwards there are only codes answering `inl v` or `inr (p, k)` |
| `Unwind` | `Clos/Unwind.lean` | raises to branch-per-call sums, `catch`, `fin` | keys `(n, i)`, the flow | `raise`, `catch`, `fin` |
| `Collapse` | `Clos/Collapse.lean` | a codata thunk's first state built eagerly; codes equal up to renaming merged; dead codes dropped | flow, code text | the replaced codes |
| layout types | `Clos/Types.lean` | a layout per variable; each closure type's union of codes | unification over the closure IR | — |
| flow | `Clos/Flow.lean` | the codes each call may reach (monovariant 0-CFA) | the closure IR | — |
| flat IR | `Flat/Lower.lean` | words, defunctionalisation (a direct call, or the type's `apply` switch), `drive` for `main`'s loop, injections padded with zeros (`mkInj`, `mkCon`) | layout types, flow | closures as values |
| Wasm, LLVM | `Wasm/`, `Native/` | instructions; `musttail` per tail-call class | flat IR | — |

`lowerEffects` runs `capture` twice when the layout types fail the first time, the second time
with answers carried as variants (`Ops.wrapsAnswers`). It is a retry because `Capture` runs
before any type is known. By inspection.

### 1.2 What the frontend knew that the backend recovers or loses

| fact | frontend | backend |
|---|---|---|
| which site an operation goes to | resolved lexically: `call 16:18: yield (Yield) → perform[1.0], handled by the caller at 14:1` (`bcc check`) | kept: the name `n` is a literal in `perform`'s payload |
| the clauses at a site | the handler declaration's clauses, with their types | recovered: `Solver.clausesAt` over the flow |
| the clause's kind (tail-resumptive, abortive, keeps `κ`) | partly in the report (`its clause keeps the continuation as the rest`) | recovered syntactically: `tailClause?`, `findResume` |
| the handler's state | §21's `S = S' ⊗ P` | lost: it is a closure `U(S ⊸ F …)` applied at each resume, a dispatched call |
| that two copies are one body at two names | the copy table (`range__n1`, `ticker__n1`, `ticker__n2`) | lost: the codes differ in their keys |
| which `unfold` is a `while` and who observes it | §14's machine, `main` driven by the runtime | lost: an `unfold` is a closure; `drive` exists for `main` only |
| a stored generator drained by exactly one `for` | known at the adapter's instance | lost |
| types | all | recovered by unification (layout only) |

### 1.3 Method for the inventory

- `lake exe bcc-counts --sites <file>` for each program: static calls, direct by union, direct by
  flow, dispatched.
- A script over the backend's own functions (`Backend.closOf`, `Clos.Prog.types`,
  `Prog.flowAll`, `Flat.knownCalls`) that prints, for each dispatched site, the code it is in,
  its closure type's union and the codes the flow finds there, with the start of each code's
  body. A union `[]` is a site in a code whose closure is never built: dead, never run.
- The binaries were built from `7a6d275` in a clean checkout.

### 1.4 Every dispatched call in `corpus/counts.expected`

Every dispatched call is a `switch` on a closure's tag in the type's `apply`, which tail-calls
one of the union's codes (`Flat/Lower.lean`; there is no `call_indirect` and no function
pointer). What a dispatch costs is that `switch`, the union's padding words, and a call that the
caller cannot specialise.

"Sites" counts the dispatched sites in live unions only; "indirect" is the run's count from
`counts.expected`. The unions are measured.

**(c) caused by a handler: a handler with a state (SPEC §19 *Handler state*, §21).** Each union is
two codes: the return clause's answer `λs. …` and an operation clause's answer. They are
applied after the site, and inside the clause at each `k(v)`. A Rust program keeps the state in a
struct, and the body calls its methods directly.

| program | indirect | sites | union |
|---|---|---|---|
| `answers-two-types` | 2 | 2 | `[0, 2]` |
| `clause-captures` | 3 | 2 | `[18, 23]` |
| `div-infer` | 4 | 4 | `[17, 19]`, `[24, 26]`: `scaled`'s two uses |
| `effects-cancel-two-sites` | 4 | 4 | `[4, 6]`, `[13, 15]` |
| `hygiene-handler-state` | 2 | 2 | `[0, 2]` |
| `reconcile-chain` | 3 | 8 | `[2, 4]`, `[25, 27]`: `service` |
| `reconcile-clock` | 8 | 8 | four unions of two: `on_clock` and the other stateful stages |

**(c) caused by a handler: a stored task's or generator's two codes.** A stored generator (§15) or
a task (§30) is a `ν` value built by the site's clauses. The return clause builds one thunk,
which answers the value. The operation clause builds another, which resumes `κ`. Every
observation dispatches between the two. Rust's coroutine is one type, and resuming it is a direct
call that matches on its state. Each union below is that pair; the program steps each task or
generator at a site of its own.

| program | indirect | sites | union |
|---|---|---|---|
| `capture-store-raise` | 2 | 3 | `[0, 2]` (the file's comment says so) |
| `async-r1-cancel` | 5 | 4 | `[1, 11]`, `[35, 45]` |
| `async-r1-drain` | 3 | 2 | `[22, 35]` |
| `async-r1-effects` | 6 | 4 | `[1, 18]`, `[42, 59]` |
| `async-r1-generator` | 3 | 2 | `[1, 14]` |
| `async-r1-local-borrows` | 4 | 4 | `[1, 15]`, `[39, 50]`: two tasks, stepped by an inline scheduler |
| `async-r1-nested` | 3 | 2 | `[1, 16]` |

`async-race` (indirect 15, 17 sites) is also this. `race[A]` is copied per use (#509), and each of
its arguments has a closure type of its own whose union is a pair: `[0, 2]`, `[10, 12]`,
`[20, 22]`, `[33, 35]`. So no `race` call sees two task bodies. Rust's `select` over two futures
is generic and polls each directly.

**(c) caused by a handler: one task body, copied per spawn site.** The queue holds tasks of one
function, spawned at two sites (or one site in a loop). Each `with spawn` is a site with its own
static name, so the body is copied per site (`ticker__n1`, `ticker__n2`). The copies differ in
their payload keys, and they stay two codes. The union is then the return thunk plus one await
thunk per site. Rust's tasks of one `async fn` have one type, so a queue of them needs no
`dyn`.

| program | indirect | sites | union | bodies |
|---|---|---|---|---|
| `async-bank-inbox` | 6 | 11 | `[21, 23, 52]` | `teller` × 2 sites |
| `async-cancel` | 3 | 13 | `[21, 23]`, `[34, 36]` | `killer` in the queue, `victim` stepped by `killer` |
| `async-lend-slots` | 6 | 11 | `[21, 23, 68]` | `task` × 2 |
| `async-logged` | 4 | 17 | `[246, 358]` | `careful` × 2 |
| `async-map` | 4 | 11 | `[32, 34]` | one site |
| `async-mapreduce` | 9 | 12 | `[51, 53]` | one site, in a loop |
| `async-scheduler` | 6 | 11 | `[21, 23, 32]` | `ticker` × 2 |
| `async-scoped` | 4 | 10 | `[1, 3, 16]` | `reader` × 2 |
| `async-try-join` | 17 | 42 | three unions of three | `job`, one site (`task`) |
| `async-workers-scoped` | 7 | 10 | `[1, 3, 16]` | `worker` × 2 |

**(b) caused by the monovariant flow analysis.**

| program | indirect | sites | union, flow | cause |
|---|---|---|---|---|
| `clo-higher` | 6 | 3 | `[101, 113, 133, 145]`, flow `[101, 133]`; `[108, 140]` | `runner`'s call of its argument, which the counter's closure and `clo_of_fn`'s reach at two call sites. A Rust `runner` with a generic `call<F: FnMut>` is monomorphised per closure type. |

**(a) Rust's program dispatches too: a queue of tasks of more than one body.** A Rust executor
over these holds `Pin<Box<dyn Future>>`, and each poll goes through the vtable (as
`bench/async-tree/main.rs` does).

| program | indirect | sites | union | bodies in one queue |
|---|---|---|---|---|
| `async-timers` | 5 | 11 | `[1, 5, 12]` | `slow_job`, `heartbeat`, `fetch` |
| `io-task` | 7 | 10 | `[5, 7, 18]` | `ticker`, `quiet` |
| `sched-a-div` | 5 | 3 | `[21, 23, 41]` | task 1, task 2 |
| `sched-a` | 18 | 3 + 2 | `[21, 23, 41]`; and `[86, 87]` under (d) | task 1, task 2 |
| `sched-b` | 18 | 3 + 2 | `[21, 23, 50]`; and `[100, 101]` under (d) | task 1, task 2 |

Even here a resume chooses among one pending code per body plus the return thunk. After (c)'s
fixes it chooses among the bodies only: one dispatch per resume, as Rust's.

**(d) a closure chain built by a fold.** Not caused by an effect and not by the flow analysis. A
fold whose result is a function builds a chain whose links are different codes (a recursive
closure type, `bcc-counts --sites`: `recursive-types 1 [2]`). Rust would need
`Box<dyn Fn>` to build the same value; a Rust programmer would write the recursion instead. This
design does not remove them. Fusing the fold into a recursion would.

| program | indirect | union |
|---|---|---|
| `13-2-sum-prog`, `sum-prog-exact` | 9, 9 | `[13, 14]`, `[30, 31]`: `add` (Backend README, *Open*) |
| `axes/data-effects` | 9 | `[8, 13]`: the fold into `Run` |
| `axes/free-monad` | 4 | `[9, 14]`: `run_out`, a fold into a computation |
| `sched-a`, `sched-b` (part) | — | `[86, 87]`, `[100, 101]`: the unary-count driver, a fold into a function |

I have not split `sched-a`'s and `sched-b`'s 18 between (a) and (d). Neither class is removed
here, so the prediction does not need the split.

Totals: (a) 5 programs, (b) 1, (c) 25, (d) 4. 35 in all.

### 1.5 State machines that were never needed

**`bench/chain-yield`: a tail-resumptive clause missed (measured).** The `for` body is
`let y = x * 3 + 1; if y % 7 != 0 { s = s + y } else { () }`. Its clause, code 34, is
`case c [inl ⇒ … k.resume s | inr ⇒ … k.resume (s + y)]`: one resume in tail position in each arm.

- `tailClause?` requires `B.tail` to be an application, and `findResume` takes the first resume
  only. So `tailResumptive` returns nothing for the name, and all 13 codes that may suspend
  become machines.
- The same program with the body `s = s + y` gives `tail-resumptive direct [(1, 0)]`.
- Native, at `n = 3·10⁸`, single runs (`bcc run --native`, compile time subtracted by a run at
  `n = 1`): chain-yield about 0.9 s; the variant without the `if` about 0.45 s. The variant does
  less work, so this only bounds the machine's share at about half.

The README's line "chain-yield is 6.1×: one `while` generator whose `yield` is a direct call of
the body" (`bench/README.md`) does not hold for this program.

**`sieve`, and every program that reads its arguments: §14's machine (measured).**
- `Capture` sees no control name in `sieve` (`control names []`, no machines).
- Its 5.6× is the frontend's div machine. `main` loops (its `while`, and `next_arg`'s), so every
  loop of `main` is a state of one `unfold`, and the runtime's `drive` runs one turn per call.
  `strike` is a callee loop held in a state of `main`'s machine and observed once per turn.
- No consumer here can observe the turns: the runtime drives `main` to the end and never closes
  it (§14 *The outermost handler*). The state machine exists because a div body is codata at
  elaboration, before anything knows its consumer.

**`bench/chain-gen`: adapters that never meet their generator (measured).**
- Three control names. Name 1 is the `for` in `main` over `filter`'s output; it is
  tail-resumptive.
- Names 2 and 3 are the stored-generator sites of `map` and `range` (`bcc check`: `stored
  generator of map … its clause keeps the continuation as the rest`).
- 39 codes may suspend.
- Each adapter's instance drains its `it` with exactly one `for`, and `it` is linear, so it has
  no other use. The generator is known at the call (`range(…) |> map(…)`). The instance is made
  without it, so the pull site's `κ` is materialised for every element.

**gen-tree: no unneeded machine.** `walk`'s `yield` is a direct call (`tail-resumptive direct
[(2, 0)]`). Its 1.72× is the right call's re-injected sum and the depth budget (#537).

## 2. Lowering by handler law

The laws are SPEC §19 *Laws* (items 1–9, machine-checked in `Core/EffMachine.lean` and its
neighbours), §18 *Laws* (`Core/Handlers.lean`), §33 *Laws* 1–4, and the constraints of
`research/effects/src/decisions.md` (deep handlers, cancellation as built, multi-shot ignored,
handling erased). That file has no section titled "The decided algebra". I read those as the
decided algebra.

For each kind of continuation: the law, the lowering, and what must be known at the `perform`.

### 2.1 Answering operations

- **Law.** `op_tail`, `op_answer`: a call on the capability `ℓ` is `withswap ℓ (λs. g (s, v))`.
  In any context it reduces to the clause run on the cell's contents, and continues with the
  answer. `handle_fold`: handling is the state-passing fold of the clauses (§18 *Laws*).
- **Lowering.** A direct call of the clause on the lent cell. Built: `handlers-di` runs 0
  dispatched calls at 0.98× Rust's `dyn`.
- **Needed at the call.** The clause's code, which the copy per assignment fixes (§18 *Rows*).
  Nothing to change.

### 2.2 Abortive operations

- **Law.** H-op at an abortive operation (`catch_abort`); algebraicity `raise e to x. P = raise e`
  (`abort_absorbs`); finally (`then_fin`); unwinding innermost first (`unwind_prefix`). Items 1, 2
  and 6.
- **Lowering.** A branch per call (`Unwind`), as Rust's `Result` and `?`. Built.
- **Needed.** The key `(n, i)`, a literal.
- **Two gaps in the shape the branch takes** (#537). Neither changes a law:
  - The re-injection `case r {inl x ⇒ inl x | inr e ⇒ inr e}` after a call is the identity on
    the sum (the right unit, `M to x. return x = M`, a β-step of the machine). Passing the
    callee's words through makes the call a tail call (gen-tree).
  - A `count_try` step's error should leave the loop, not share its loop-carried locals
    (raise-small).

### 2.3 Tail-resumptive control operations

- **Law.** H-op (`catch_step`), then `κ`'s resume reinstalls the handler (`kappa_resume_steps`).
  For a clause `λ(v, k). M; k.resume y`, the step `hnd (n, H) K[perform (n, v)]` reaches
  `hnd (n, H) K[y]` with `M` run outside the site.
- **Lowering.** A direct call of the clause at the `perform`, with its resume removed. `M` then
  runs inside `K`, so this is the law only when two conditions hold:
  1. `M` uses `κ` exactly once on every path, as the resume in tail position: in every arm of a
     `case`, not only as the body's last call (chain-yield, §1.5);
  2. the names `M` performs or raises are handled nowhere in `K`. The old backend's rule is
     stronger: `M` neither suspends nor raises. The checker decides the weaker condition (SPEC
     §19, *The clause's names in the continuation*) over the names the clause's own code
     performs or raises (`handlerNames`; its row's where it may run code it does not hold),
     which bound every run of `M` without its resume (`tail_clause_names`): none is one the
     program's flow record may catch (`cond2B`, `Checked.unhandledNames`), the frames of the
     handled computations and of the code that flows into them, recursion and continuations
     included. A clause with no names meets it in every `K`.
- **Needed at the `perform`.** The site (a literal), its clause code, and the clause's shape.
- **A tail-resumptive clause of a handler with a state.** The clause needs the instance's state.
  Pass the state as a capability: a cell lent for the site's duration, the clause a direct call on
  it, as §2.1 does (§19 *Open*'s "native parameter"; §21's state-passing encoding replaced by
  §18's).
  - This is not Koka's run-time evidence. Nothing is searched or indexed. The argument is the
    state's address, and the code is known, as a Rust method's `&mut self` is.
  - **Law.** The state-passing answer `U(S ⊸ F …)`, with a clause that resumes in tail position
    passing on `s'`, equals threading `s` through the cell.
  - This follows from H-op, `kappa_resume_steps` and β, by induction on the body's run. It is not
    a Core theorem by name. **Hypothesis**, to be stated as one with the unit (§6).
  - It holds for a must-resume or cancellable operation. An `unr` continuation resumed twice would see one
    cell where state-passing gives each resume its own state. `unr` keeps state-passing; multi-shot
    is not designed for (decision 63).

### 2.4 Resume or cancel (the `deadline` pattern)

A clause that, on each path, either resumes `κ` in tail position or cancels `κ` and then runs
code outside the site: `timeout`'s `deadline`, `scaled` in `div-infer` and
`effects-cancel-two-sites`, `reconcile-*`.

- **Law.** `kappa_cancel_steps`. A cancel is `ccatch (K†[raise (⊥, none)])`: `K`'s finalisers run
  innermost first, its handler frames are dead, the first finaliser error is kept and re-raised
  at the canceller (`cancel_prefix`, item 5). Then the clause's rest runs outside the site.
- **Lowering.** A direct call of the clause's deciding part at the `perform`. It answers either
  "resume with `y`" or "cancel, then run `N`". On cancel, unwind `K` in place under the cancel's
  semantics: a key no frame in `K` catches (`⊥`), first error kept, re-raised at site `n`, and
  then `N` there. This is `Capture`'s cancel arm (`cancelArm`, `reraise`) run where the
  operation stands, with no `κ` built.
- **The excluded variant.** Lowering the cancel as an ordinary raise of the clause's error,
  through `K`, would let a finaliser's raise supersede, where a cancel keeps the first error. It
  would also let `K`'s handlers catch it, where a cancelled region's handlers are dead. That
  changes laws 5 and 6. It is not proposed.
- **Needed.** As §2.3, and the clause's split into a deciding part and the rest.

### 2.5 Cancellable and must-resume continuations that are stored

A clause that keeps `κ`: a stored generator's site (`κ` is the rest), `spawn`'s `await` (BOXED-κ,
§28), a scheduler's queue.

- **Law.** H-op with `κ` as a value; resume (`kappa_resume_steps`); cancel (`kappa_cancel_steps`);
  `κ` used once (item 4). A linear `κ` has no cancel branch (`kappaC_cancel_lin`).
- **Lowering.** A state machine (`Capture`): Rust's coroutine transform, sized statically,
  suspension through calls nests. This is the one place a state machine is the behaviour's own
  cost.
- **The (c) dispatches here are representation.**
  - *One code per value.* The return clause's thunk and the operation clause's thunk are two
    codes of one `ν` type. Build both as one code whose environment is a sum (finished `v`, or
    pending `κ`). That is Rust's single coroutine type with a state tag. The observation is then a
    direct call and a `case`.
    - The dispatch becomes a branch inside the call. The program still decides at run time
      whether the task finished, as Rust's `Poll` match does.
    - **Law:** none is needed. It is a change of representation of one closure type
      (defunctionalisation's union becomes a sum inside one code), with the same observations.
  - *One body, one code, across names.* Copies of one body at two sites differ in their payload
    keys only (`docs/effect-polymorphism.md` §5.8(1)). They can share one code with one key when
    neither site's region can run inside the other's. Then a `perform` of the shared key always
    meets its own site's handler as the nearest (H-fwd, item 3).
    - The condition is static: neither site's body reaches the other site, and no block written
      under one is run under the other.
    - Where it fails, the copies stay apart. Merging them would let one site catch the other's
      operations: accidental handling, which item 3 rules out.
- **Needed.** That `κ` escapes the clause (the clause shape), and the codes the stored value can
  have.

### 2.6 Async and PinLaw

The same as §2.5. A task's continuation holds the location of a cell lent across `await` (R1,
§29), never its contents. Every lent cell a suspension crosses is a heap object
(`crossedScopes`, `suspendedScopes`). That is SPEC §29's *Lowering*: "a suspended code's state
holds the cell's location, a word, never its contents".

Every lowering here must keep it:
- #540's narrowing passes a state's words between turns, and the words are addresses;
- a frame slot is used only when no resumption point lies in the scope;
- the merged task code (§2.5) moves `κ`, never copies it.

### 2.7 Divergence (§14) and generators (§15)

- **Law.** A div loop is `ν` codata. The runtime drives `main` until it finishes and never closes
  it (§14 *The outermost handler*; §11 `loop_every_run`). `div_fuel` is `driveE n`, which counts
  observations.
- **Loops as loops.** Turns that a complete driver observes one after another can run as one
  native loop. The driver is the runtime, or a drain inside a body the runtime drives. Nothing
  can observe the boundary between those turns.
  - Under `div_fuel`, the count of observations is the program's meaning. Fusing turns there
    would change it, so it is not done.
  - #540's flat-IR pass (inlining, known tags, call-pattern specialisation of `drive`, narrowing)
    keeps every run's computation (its module doc, `Backend/Flat/Opt.lean` on branch
    `loops-as-loops`, uncommitted when read). So it is valid at every driver, `div_fuel`
    included: it changes the code, never the observations.
- **Push stages.** `for x in it { M }` over a stored generator `it` (a drain of the pull site,
  whose clause answers `(x, rest)`) is equal to `for x in g(e) { M }` (the push site, clause
  `M; k.resume`).
  - **Law.** H-op, `kappa_resume_steps` and `ν`'s β (`nu_out (nu_in t) = t`), by induction on
    `g`'s run.
  - Each pull observation resumes `κ` under the reinstalled pull handler (deep). The push handler
    runs `M` and resumes. In both, `M` runs outside `g`'s site (§15: "the clause runs outside the
    site"). `break` cancels `κ` in both, running `g`'s finalisers.
  - The two differ only in the number of observations (pull skips a turn that yielded nothing).
    That is observable only under `div_fuel`, so push is chosen only where the drain is driven to
    completion.
  - Stored generators are pure (§15 *Open*: a generator over a row is not stored), so no other
    operation's order changes. **Hypothesis**, to be proved as an equation over elaborated terms
    in the unit (§6).

### 2.8 The algebra hard stop

No lowering proposed here requires changing a decided law. Two candidate lowerings would have,
and each is excluded where it applies:

| candidate | law it would break | excluded by |
|---|---|---|
| a cancel lowered as an ordinary raise (§2.4) | 5 (cancel not interceptable, dead frames), 6 (first error kept) | the cancel runs with `⊥`'s semantics |
| merging copies whose regions may nest (§2.5) | 3 (static names, no accidental handling) | the static non-nesting condition |
| fusing turns under `div_fuel` (§2.7) | `div_fuel = driveE` (§14), the observation count | only at a complete driver; #540's pass changes no observation |

Multi-shot (`unr`) is left on today's lowering and never shapes a choice (decision 63).

### 2.9 Borrow interactions, per kind

| kind | a resumption held across a lend | PinLaw (§28–§29) | finalisers, cancel rows (§27) | guarantees |
|---|---|---|---|---|
| answering | no continuation; the capability is a lend, as today | — | — | unchanged |
| abortive | none: unwinding ends each lend, innermost first (`unwind_prefix`) | — | a finaliser's raise supersedes (item 6), as `Unwind` builds | unchanged |
| tail-resumptive, direct | none is built. A lend around the `perform` spans a call, not a suspension. Typing still refuses a resuming operation inside a borrow block unless R1 (T1, §19), and the lowering accepts nothing new | an R1 lend under a direct `yield` holds across a call only | the clause runs no finaliser | unchanged; scoped cells there become frame slots (no resumption point) |
| resume or cancel | none is built; the cancel unwinds `K`'s lends in place, innermost first | as above | cancel rows read where the cancel is invoked, as today; a finaliser that may suspend stays rejected (`Capture`, §27 *Lowering*) | unchanged |
| cancellable or must-resume, stored | as today: the state holds the lent cell's location | as today | as today | unchanged |
| async (BOXED-κ, R1) | as today | the merged task code moves `κ` and copies no cell | `cancel(t)` runs the same cancel arm | unchanged |

No option needs a kernel change. Push stages change what the elaborator emits; the checker types
it with the rules it already has. The assurance report follows the derivation, so it reports
`PinLaw` exactly when an R1 lend is in the typed program.

### 2.10 Where static resolution is not available today

| case | today | options |
|---|---|---|
| stored callbacks with a row (#161 B, §33 *Open*) | rejected | **specialise**: ports fixed by the stored type (decision 57, R6), so every `perform` inside is static; which callback is stored is the program's own run-time choice, a dispatch Rust's `Box<dyn Fn>` makes too, class (a). **Restrict**: `!` captures only. **Reject**: keep today's rule. Each is a decision about what a stored value means (§33 *Open*), not a lowering. |
| computation parameters (§33) | one copy per tunneled row; ports static | static already; sharing copies across names is §2.5's merge |
| a handler passed as a value | not in the language: a handler is a declaration | if added: **specialise** when the choice is a static branch (copy the body per branch); **dispatch** when it is a run-time value, class (a) as `&mut dyn Trait`; or **reject** |
| re-entry of one site (`memo` under itself, §19 *Names*) | the nearest instance of the name | the clause's code is static; the instance's state is a capability argument (§2.3) |
| recursion through a site (§21 *Open*) | rejected | needs generative names (T2, #173): a kernel change, not proposed |

## 3. The proposed pipeline

    elaboration (frontend)
      + push stages: an adapter instance whose stored-generator argument is drained by one `for`
        is made at that generator (§2.7)
      + (option H1) a site table: per static name, the clause kind and the handler's state
    convert, poly
    specialise           clone codes per (code, closure codes of its function-typed arguments),
                         bounded (§3.2); merge copies equal up to non-nesting names (§2.5)
    flow                 0-CFA on the specialised program
    classify             each site by its law: answering, abortive, tail-resumptive (every arm),
                         resume or cancel, stored (§2.1–§2.5)
    lower, no κ          direct calls; native handler state; resume-or-cancel in place
    capture              state machines for the stored continuations only
    unwind, collapse     + one code per codata value built by a site's clauses (§2.5)
    types, flow, flat    + #540: loops as loops, narrowed state, `poison` padding

### 3.1 Which IR keeps `handle` and `perform` structured: carry or recover

The closure IR keeps `hnd`, `perform` and `ubind` structured until `classify`. The choice is where
`classify` gets the clause's kind and the handler's state from.

| option | how | for | against |
|---|---|---|---|
| **H1: carry, then verify** | the frontend writes a table keyed by the static name: clause kind, state shape, copies of one body, drained-once generators. The backend checks each entry against the closure IR before using it. | no syntactic guessing; one source for the report and the lowering | a second channel beside the checked erasure; it must be checked, since a wrong hint miscompiles |
| **H2: recover (today)** | flow plus syntactic recognition of shapes | no trust beyond the erasure | brittle: chain-yield's `if` defeats it; every new clause shape needs its recogniser |
| **H3: lower the typed core** | the backend starts from the elaborated, typed core and checks that its erasure is the checked erasure (as `Frontend/Check/CrossCheck.lean` compares erasures) | types at every decision, so no `wrapsAnswers` retry | the largest change: every pass moves to a typed IR |

**Recommendation:** H2 now, with the recognisers stated by law (every arm, §2.3), since unit 1
needs nothing else. Then H1 for what cannot be recovered: copies of one body, and the handler's
state. H3 only if the layout-type retries keep growing.

### 3.2 Specialisation, bounded against #509

Today every use of a definition is a copy (#509), so specialisation is total and size is
unbounded. `docs/effect-polymorphism.md` §5.8(2) makes one body per (function, profile) the
default, with callbacks dispatched. #541 asks for the opposite where Rust monomorphises.

| option | key of a copy | dispatch | size |
|---|---|---|---|
| **S0: copy every use** (today) | the use | none from callbacks | grows per call site (#509: 21 calls of `print_f64` exceed Wasm's local limit) |
| **S1: Rust's key** | (definition, assignment of sites, closure codes of its function-typed and stored-generator arguments) | none where the codes are known; (a) where a recursion makes new codes per level | one copy per key, Rust's size |
| **S2: one body per profile** (§5.8(2)) | (definition, profile) | a switch per callback call | smallest; dispatch of class (b) everywhere a callback differs |

**Recommendation: S1.**
- It removes (b) (`clo-higher`) and #509's per-site copies at once.
- §2.5's merge across names is the same sharing.
- A recursion that creates closure codes without bound falls back to dispatch, and the report
  names it.
- Pin the size with a code-size column (kill criterion 5).

### 3.3 Push or pull, per adapter

| adapter (`lib/adapters.bc`) | drains its source | form |
|---|---|---|
| `map`, `filter`, `skip`, `enumerate`, `scan`, `take_until`, `chunks`, `lines`, `batch` | one `for` | push |
| `take` | one `for`, `break` after `n`, close at `n ≤ 0` | push: `break` cancels the source, as the pull's close does |
| `chain` | two `for`s, one after the other | push both |
| `flat_map` | a `for` over the source, and one over each inner generator | push both |
| `zip` | two sources, observed alternately by hand (`nu_out`) | pull at least one; **option**: push `a` and pull `b`, or pull both. Push-`a` makes `zip`'s loop the push clause, with `b`'s observation inside it. |
| any stored generator that escapes (stored in data, returned, a task) | — | pull: a state machine (§2.5) |

**Recommendation:** push wherever the source is drained by one `for` of an instance driven to
completion. `zip` pushes `a` and pulls `b`. The condition is decided at elaboration, where the
instance and its argument are known. It is not recovered by the backend.

### 3.4 Div loops as loops

| option | how | for | against |
|---|---|---|---|
| **L1: #540** | the flat-IR partial evaluator specialises `drive` and the steps at known tags | built, both targets, changes no observation (§2.7) | bounded by budgets (`budget`, `specMax`, `depthMax`): a large step can stay driven. That is an optimiser, not a construction. |
| **L2: construct** | the frontend marks each `unfold` whose consumer is a complete driver. The closure IR lowers it as a loop code. | by construction | duplicates #540; a new mark through the erasure (H1) |

**Recommendation:** L1, with a check that makes it a construction: `bcc-counts --sites` reports
the loops still turned by a driver at a complete consumer, and the gate pins it at 0 for the
corpus and `bench/`. If the check cannot reach 0 within #540's bounds, switch to L2 (kill
criterion 6).

### 3.5 State machines last, and their state

- After `classify` and the direct lowerings, `Capture` sees only continuations that escape a
  clause. Its state is already per point and live-only (`framesLive`, one variant per point).
- What #537 measured as 71 words is the driver's union of every loop code, padded with zeros
  (`mkInj`, `mkCon`). That is #540's narrowing and `poison` padding, which this design keeps.

## 4. Prior art, compared on fit

| system | continuation kinds covered | resolution | cost model | fit |
|---|---|---|---|---|
| LLVM coroutines (`llvm.org/docs/Coroutines.html`) | one: a coroutine split into ramp, resume and destroy functions (`CoroSplit`), the frame heap-allocated unless `CoroElide` proves it local | none: a coroutine is called through its handle | split inside the optimisation pipeline, after earlier passes have run on the unsplit body (as the documentation describes it) | the target-level analogue of `Capture`, run late. Not usable as the semantics: it is LLVM-only, and #541 and decision 25 require every lowering to run on both targets. Its ordering (optimise, then split) is this design's "state machines last". |
| Rust's coroutine transform (`compiler/rustc_mir_transform/src/coroutine.rs`) | `async`/`gen` bodies: a state enum over the suspension points, the locals live across each point saved, variants sharing storage | static: a coroutine is a type; `dyn Future` only where the program asks | iterator chains are not coroutines: `Map<Filter<Range>>` is pull with monomorphisation and LLVM's inlining | the cost reference. Its live-only state per point is `Capture`'s. Its iterator chains fuse through LLVM, an optimiser; push stages (§3.3) reach the same by construction. |
| Koka (Xie and Leijen, *Generalized Evidence Passing*, ICFP 2021; Xie et al., *Effect Handlers, Evidently*, ICFP 2020) | `fun` (tail-resumptive, in place), `ctl`, `final ctl`; multi-shot | evidence passed at run time: a handler is found through the evidence vector | tail-resumptive operations run in place, near a virtual call (Koka book, §3.4) | the tail-resumptive optimisation is §2.3. Run-time evidence is what #541 forbids; our static names make the clause known at the `perform`. |
| Effekt (Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020; Schuster et al., *Compiling Effect Handlers in Capability-Passing Style*, ICFP 2020; *Zero-cost Effect Handlers by Staging*, tech report) | lexical handlers as capabilities; second-class blocks; boxes to store | lexical: a capability is passed to where the effect is used | the staging paper removes handler overhead when handlers and their order are known statically | the closest fit: lexical resolution is our §19 *Names*, and capability passing is §2.3's state argument. `docs/effects-scoping.md` §4.2 notes it is unverified whether the current compiler monomorphises; I have not checked either. |
| monomorphisation of effect-polymorphic code (Rust generics; MLton's whole-program monomorphisation and 0-CFA closure conversion, Cejtin, Jagannathan and Weeks, ESOP 2000) | — | static, per instance | one copy per instance; MLton defunctionalises with a flow analysis, as `Clos/Flow.lean` does | §3.2's S1 is Rust's key. MLton is our closure representation; its flow analysis is monovariant too, and so (b) is the class its cloning addresses. |
| OCaml 5 (Sivaramakrishnan et al., *Retrofitting Effect Handlers onto OCaml*, PLDI 2021), for contrast | deep handlers, one-shot checked at run time | dynamic: `perform` searches the handler stack | fibers, stack switching | the opposite design: what OCaml decides at run time, this design decides statically. Stack switching is excluded by decision 25. |

## 5. The test before building

### 5.1 Predictions

Ratios are ours over Rust, on `make bench`'s machine and inputs. `indirect` is from
`corpus/counts.expected`, or from `bcc-counts` at the bench's inputs. Each prediction names the
unit (§6) it depends on.

| row | now | predicted | units | why |
|---|---|---|---|---|
| sieve | 5.63× | ≤ 1.4× (sieve-for: 1.30×) | 2 | §14's machine only; no control operation |
| chain-yield | 6.10× | ≤ 1.2× (chain-for: 0.99×) | 1, 2 | the `yield` machine (unit 1) and the driver (unit 2). Unit 2 alone leaves a suspension per element: > 1.2× |
| chain-gen | 21.5× | ≤ 1.3× | 1, 2, 7 | push stages leave chain-yield's shape. Without unit 7, not predicted: it would rest on #540 resolving two pull machines per element |
| gen-tree | 1.72× | ≤ 1.4× | 8 | the right call a tail call; the depth budget stays (§20) |
| async-tree | 0.84×, indirect 201 at `n = 200` | ≤ 0.84×; indirect 0 | 5 | one task body: the return and await thunks become one code. Allocations (3 per `await`) unchanged without #537's fix 10 |
| raise-small | 1.30× | ≤ 1.1× | 8 | the error leaves `count_try`'s loop |
| raise-large | 1.03× | 1.03× ± noise | — | already parity |
| handlers-di | 0.98× | 0.98× ± noise | — | already direct; the state's load and store are #531 |

For the (b) and (c) programs, the predicted `indirect` after the units named:

| program | now | predicted | unit |
|---|---|---|---|
| `answers-two-types`, `clause-captures`, `div-infer`, `effects-cancel-two-sites`, `hygiene-handler-state`, `reconcile-chain`, `reconcile-clock` | 2, 3, 4, 4, 2, 3, 8 | 0 each | 3, 4 |
| `capture-store-raise`, `async-r1-cancel`, `-drain`, `-effects`, `-generator`, `-local-borrows`, `-nested`, `async-race` | 2, 5, 3, 6, 3, 4, 3, 15 | 0 each | 5 |
| `async-bank-inbox`, `async-cancel`, `async-lend-slots`, `async-logged`, `async-map`, `async-mapreduce`, `async-scheduler`, `async-scoped`, `async-try-join`, `async-workers-scoped` | 6, 3, 6, 4, 4, 9, 6, 4, 17, 7 | 0 each | 5 (both halves) |
| `clo-higher` | 6 | 0 | 6 |
| (a) and (d) programs | as now | unchanged: one dispatch per resume of a queue of several bodies (a); the fold chains (d) | — |

`allocs` and `copies` may not rise. `allocs` falls where a continuation is no longer built
(resume-or-cancel, §2.4): `reconcile-*`, `effects-cancel-two-sites`. I do not predict by how much.

### 5.2 Kill criteria

Any one of these shows the design wrong where it applies:

1. **chain-yield.** Units 1 and 2 land, the program has no machine left (the classification
   report) and `indirect 0`, and it still runs above 1.5× Rust. Then the cost is not where §1.5
   puts it.
2. **chain-gen.** Unit 7 lands, and chain-gen runs above twice chain-yield's time. Then push
   stages are not what separates them.
3. **A (c) program.** After its unit, a (c) program keeps a dispatched call that is not traced to
   (a) or (d). Then the classification of §1.4 is wrong for it.
4. **Meaning.** Any unit changes an output, a golden, an exit status, `live 0`, a falsifier mode,
   or raises `allocs` or `copies`. Then a law was applied outside its condition.
5. **Size.** S1 (§3.2) makes a corpus program's flat IR, or a bench program's `__text`, more than
   twice today's. Then the specialisation bound is wrong; return to the choice of §3.2.
6. **Loops by construction.** #540's pass cannot bring the count of loops still driven at a
   complete consumer to 0 on the corpus and `bench/`. Then L1 is an optimiser and L2 is needed.

## 6. Build plan

Units in dependency order. Each lands with its spec text, its acceptance programs and
`counts.expected`.

| # | unit | needs | acceptance |
|---|---|---|---|
| 1 | **Tail-resumptive by law** (§2.3): a resume in tail position of every arm; the clause's names unhandled in `K` in place of "neither suspends nor raises" | — | chain-yield: name 1 tail-resumptive, no machine; every count no higher; `gen-produce`, `gen-fib`, `gen-pipeline` unchanged |
| 2 | **#540**: loops as loops, narrowed state, `poison` padding; plus the `--sites` count of loops still driven, pinned at 0 | running | sieve ≤ 1.4×; with 1, chain-yield ≤ 1.2× |
| 3 | **Classify, then lower before `Capture`**: reorder `lowerEffects` (specialise, flow, classify, direct lowerings, `capture`, `unwind`, `collapse`); a native handler state for tail-resumptive clauses (§2.3), with its equation stated and proved over the elaborated terms | 1 | `hygiene-handler-state`, `clause-captures`, `answers-two-types`: indirect 0 |
| 4 | **Resume or cancel in place** (§2.4) | 3 | `div-infer`, `effects-cancel-two-sites`, `reconcile-chain`, `reconcile-clock`: indirect 0, allocations no higher; `corpus/reject/*` messages unchanged |
| 5 | **One code per codata value of a site; copies across non-nesting names merged** (§2.5) | 3 | `capture-store-raise`, `async-r1-*`, `async-race` and the same-body async programs: indirect 0; async-tree indirect 0; `scripts/falsify.sh` four modes |
| 6 | **Specialisation S1** (§3.2), with a code-size column in the counts | 3 | `clo-higher` indirect 0; #509's reproduction compiles once per key; kill criterion 5 |
| 7 | **Push stages** (§3.3) at elaboration, with the pull/push equation proved over elaborated terms | 1, 2 | chain-gen ≤ 1.3×; `gen-pipeline-adapters` `0 0 0`; `gen-adapters`, `gen-adapters-fail` counts no higher; `take-failing` still rejected |
| 8 | **Abortive pass-through and loop exit** (§2.2; #537 fixes 3 and 6) | — | gen-tree ≤ 1.4×; raise-small ≤ 1.1× |
| 9 | **H1 site table** (§3.1), if unit 5's merge condition or unit 3's state shape cannot be recovered from the closure IR | 3 | the backend's checks agree with every table entry on the corpus |

**#540.** This design keeps all of #540: its partial evaluator, its narrowing and its `poison`
padding (L1, §3.4). It adds unit 1, without which chain-yield keeps a suspension per element
whatever #540 does. Unit 7 replaces the last sentence of #540's scope item 1 ("a generator
consumed in place by `for` or `|>` should become the consumer's loop") for stored generators:
push at elaboration does it by construction. #540 may still recover it where unit 7 does not
apply.

**Unspent, untranscribed and unverified.**
- I have not verified why `ticker__n1` and `ticker__n2` stay two codes after `Collapse`'s merge.
  The payload keys are the likely difference. Unit 5 checks it first.
- §2.3's and §2.7's equations are hypotheses until units 3 and 7 prove them.
- #540's branch was read uncommitted, from its worktree. Its final form may differ.
