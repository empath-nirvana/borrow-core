# Effectful callbacks at the surface: every order, stored callbacks, stored continuations

**A proposal, not a decision.** Nothing here is built at the surface. It is the surface half of
the async colourless test, whose kernel half (A1) is built: `Core/EffAsyncPrograms.lean`, SPEC §19
*Programs*. Every rule is an elaboration into Core rules that exist; no kernel rule is proposed.
Spellings are today's surface where one exists, and are marked *provisional* where none does
(decisions 51, 55–57).

Each claim is marked as one of:

- **established**: a Lean declaration on this branch, named after `grep` found it;
- **measured**: a `bcc` run on a scratch program that is not registered in the corpus; each is
  described precisely enough to be repeated from a registered pending program;
- **by inspection**: read off a definition, the elaborator or its output (`bcc desugar`), with no
  theorem behind it;
- **hypothesis**: argued here, not checked.

## 0. Summary

**The test.** The user (2026-10-13): "the real colorless function test is actually async". One
generic function, written once with no marker, is used with a plain callback, where it compiles
to a plain loop, and with a callback that suspends to a scheduler, which stores the continuation,
runs another task and resumes the first later.

**Where it stands.**

- **Core: built.** `async-sync` measures `0 0 0`, `async-tasks` `6 0 0` and `async-colourless`
  `6 0 0` (established: `asyncSync_run`, `asyncTasks_run`, `asyncColourless_run`; the counts are
  `corpus/kernel-counts.expected`).
- **The surface, apart from the callback: works today** (measured):
  - higher-order functions with pure callbacks, up to order 4, and the generic `for_n` with a
    pure callback: `0 0 0`;
  - a scheduler written as a handler whose clause stores its continuation, with two tasks
    interleaving under a round robin, beside the sync use: the same answer at every stage,
    `live 0`, and `6 0 0`, the counts of `async-colourless`.
- **What fails is the callback.** A function or closure that performs an operation is rejected
  where it is passed as a value (#161; `Frontend/Elab/Effects.lean`, `notInClosure` and the
  "passed as a value" errors). Behind that is the generic function's loop at a row whose
  operation resumes. Today such a loop is a div loop when its body performs the operation, and no
  handler wraps a div computation; it is rejected when its body calls a function that performs it
  (E8, OQ-S1).

**The mechanism.** A callback's row is part of its type. A function's row includes the rows of
the callbacks it calls. A use of a function is a use of its copy at the rows its arguments carry.
Core checks each copy at concrete rows. Rows are variables only inside the elaborator's
inference; Core has no row variable, and one closed function used at several rows is
`[let-poly]`'s premise (SPEC §24), which the checker's copies already are.

**Order.** No rule reads the order of a callback, so a callback of order n + 1 is elaborated by
the rules that elaborate one of order n (§1). The rank is 1: a callback parameter has one row
inside the body that receives it (OQ-S2).

**Not covered.** A lend held across a suspension (T1, tier 2): its acceptance program is A2,
`corpus/pending/async-borrow.bc` (§5).

**Programs** (pending, each failing today at #161 with its message recorded):

| program | what it tests |
|---|---|
| `corpus/pending/async-colourless.bc` | A1 from source: `for_n` written once, used with `tick` and by two tasks with `yield_tick` under a scheduler written as a handler |
| `corpus/pending/effects-callback-orders.bc` | orders 1 to 4: effects at order 1 and order 2, each handled in `main`, through every level |
| `corpus/pending/async-borrow.bc` | A2: a task that yields inside a fold over a borrowed list; tier 2 |

`corpus/pending/effects-hof-two-rows.bc` (E1), `effects-sum-gen.bc` (E2d, a provided effect) and
`effects-tunnel.bc` (E6) stay as they are.

## 1. The order statement

### 1.1 Order

The order of a type counts the nesting of function types to the left of an arrow:

- `ord(T) = 0` when `T` contains no function type: data, and borrows of data;
- `ord(P => R) = max(ord(P) + 1, ord(R))`, for every kind of function (persistent, one-shot,
  affine) and whatever its row;
- a pair, a sum, a `μ`, or a codata type takes the largest order of its components (for codata,
  of its observations' arguments and results).

A callback of order n is a value of a type of order n, and a function of order n + 1 takes one.
In A1, `tick` and `yieldTick` have order 1 and `forN` order 2. In
`effects-callback-orders.bc`, the closures `plain` and `yielding` write have order 1, `both` and
the closure literal in `main` order 2, `plain` and `yielding` order 3, and `apply` order 4.

### 1.2 What a callback is

The elaboration maps a function type to a Core type built from three things only: the argument,
the result and the row.

    ⟦P => R with ε⟧     =   U(Caps(ε) ⊗ ⟦P⟧ ⊸ F_{ctl(ε)} (Caps(ε) ⊗ ⟦R⟧))      one use
    ⟦!(P => R with ε)⟧  =  !U(Caps(ε) ⊗ ⟦P⟧ ⊸ F_{ctl(ε)} (Caps(ε) ⊗ ⟦R⟧))      persistent

- `ctl(ε)` is `ε`'s control operations, each at the static name of the site that serves it
  (SPEC §19 *Names*).
- `Caps(ε)` is the capabilities of `ε`'s answering effects, `Mut 'l S` each, passed with the
  argument and handed back with the answer (§18's copies; E6 below). When `ε` has none, the type
  has no `Caps(ε)` component.
- An affine callback, one with captured state that is called many times, is `[@c] U(Aff^c …)`
  (SPEC §22), whose state `ν` hides: `νX. (⟦P⟧ ⊸ F_Σ(⟦R⟧ ⊗ [@c] U X)) & F_Σ 1`, positive at
  closed operation types (established: `affEffBody_nuOk`).

**A callback's type never mentions its environment.** A persistent callback captures persistent
values inside its thunk (`bangThunkV`). A one-shot callback captures anything inside its thunk.
An affine callback hides its state behind `ν`. In each case the type is a function of the
argument's, the result's and the row's, and `⟦·⟧` is defined by structural recursion on types: the
image of an order-(n + 1) type is built from images of types of order at most n.

### 1.3 The induction

**Statement** (by inspection; a hypothesis until built). For every n ≥ 1, each rule of §2 applies
to a callback of order n + 1 with the premises it has at order n, and yields a term that the Core
rules it names type. So a callback of order n + 1 is elaborated exactly as one of order n.

**Why.** Each rule reads a type, a row (a finite set of operations at static names), or the
lexical scope where a term is written. None reads an order:

| rule (§2) | what it reads | what changes at order n + 1 |
|---|---|---|
| E1 rows | the operations a body performs, and the rows of the callbacks it calls | nothing: a callback's row is read off its type, whatever its argument's type |
| E2 a callback value | the expected type (for a literal's parameter), and the scope (for the names of its operations) | an order-(n + 1) literal's parameter has an order-n type, read from the expected type; the body is elaborated with it in scope |
| E3 a call of a callback | the callback's type `⟦P⟧ ⊸ F_r ⟦R⟧` | `⟦P⟧` may be a callback type: the call is the same derelicting `let` and the same `[let]` |
| E4 instantiation | the arguments' types, matched against the parameters' | matching is structural, at every depth of a type; rows are matched as sets at `F_r` positions |
| E5 sites | an effect's operations, and the body's row | nothing |
| E6 capabilities | a row's answering effects | nothing: `Caps(ε)` depends on `ε` only |
| E7 a stored continuation | the operation's answer, and the handler's | nothing |

The Core rules these use are stated at every value type and every computation type: `bind`,
`ret`, `bangE`, `force`, `app`, `lam`, `lamDead` (`[λ-dead]`), `thunkV`, `bangThunkV`, `effLet`
(`[let]`, whose side condition reads the context held across a call, not the callee's type),
`effThen` (`[then]`), `effHandleV` (`[handle]`), `effSub`, `nuIn`, `nuOut`, `withI`, `proj₁`,
`proj₂`, `boundedFix` (sound at every computation type, `boundedFix_compatX`) and `letPoly`
(at every judgement, `letPoly_compatC`). All established.

**The base cases are built in Core.** E1's `hof` has order 2, typed at three rows by `[let-poly]`
(`d_hofTwoRows`, `hofTwoRows_run`). A1's `forN` has order 2, typed at every row `r` with no
hypothesis on `r` (`dAt_forN`), because across its call of the callback its step holds only `!`
values.

**At the surface today, the pure half holds at order 4** (measured).
`corpus/pending/effects-callback-orders.bc` with its `yield` and its `raise` taken out (`yielding`'s
closure becomes `!{ x -> x * 10 }` and loses its row, `b` is `apply(yielding, both)`, and `c` is
`inl (apply(plain, …))` with `0 - s` for `raise(s)`) checks and measures `0 0 0`.

**What the induction does not give: rank.** Inside the body that receives it, a callback
parameter is one value with one row, the union of what its uses need (`[sub]`). Its type may have
any order. A let-bound closed function, unlike a parameter, has as many rows as it has uses
(`[let-poly]`). A parameter used at two rows that cannot share one is rank 2 (OQ-S2).

### 1.4 What was first-order in #233's R2a, and why this is not

#233 built R2a (`docs/effect-polymorphism.md` §5.2; branch `effect-callbacks`, its SPEC §22). It
was closed unmerged: "It solves the first-order case only" (`docs/effects-state/03-attempts.md`
§7). Its pending programs name where it stopped: `cb-higher-rank.bc` (a callback whose parameter
is a computation), `cb-stored.bc` and `cb-policy-value.bc` (R6). The first-order parts were its
representation of a callback. Its rows were not:

| | R2a (#233) | this proposal |
|---|---|---|
| a callback is | `!` code `!(∀'k⃗. caps ⊗ (Env ⊗ A) ⊸ F[ports ∪ T] (caps ⊗ (Env ⊗ B)))`, and the environment `Env`, the tuple of its captures, passed beside it; the callee's copy is generic in `Env`, a type parameter | a thunk value: persistent `!U(…)` with persistent captures inside it, one-shot `U(…)`, or affine `Aff` with its state hidden by `ν` |
| its type mentions | its environment's type | its argument, result, row and capabilities |
| a callback whose parameter is a callback | the inner callback's `Env` is known only in the copy of the function that makes it. The outer callback's code, made where its caller writes it, would take that `Env` at a type its writer cannot name: "an existential, or a type exposed per copy, would" (`cb-higher-rank.bc`) | the inner callback's type is a type. The instance that makes it is the instance whose parameter type the outer callback is checked against, so its writer reads it there |
| lifetimes | each code generic in its capabilities' lifetimes (`∀'k⃗`). Passed on, it was η-expanded; at a call of a local code value it would be compared by `=` with no α-conversion (`Frontend/README.md`, Incompleteness 2) | a capability is at the copy's lifetime: rank 1. When the callee reborrows it, the callback is generic in its lifetime, and OQ-S5 applies |
| provided effects | ports fixed per (function, effect). Passing a callback on to another port needs a relabelling clause that holds `κ` across an operation, which is not typable at a resuming operation (R2c), so inlining | decision 57's ports, kept; passing on is OQ-S4 |
| storing, returning, capturing | second class (R5); R6 not built | first class: a callback is a value whose type states its row (E2, §3) |

Decision 57's provided and tunneled rows, its static names and site freshness (R3) are kept.
What changes is that nothing in a callback's type depends on the callback's body. §22 made the
same move for the affine closure: "That form names `E`, so a function over such closures is
written once per environment type (#233; R2a)."

## 2. Elaboration rules

Each rule gives the surface form, the Core term, the Core rules it uses, and its status. A rule
that changes something today's elaborator does says so.

### E1. Rows in types, inferred

- **Where a row is a variable.** A function type in a parameter of a `fn`, at any depth inside
  the parameter's type, has its row left open: a row variable of the elaborator, solved at each
  use (E4). `f: !(S => S)` has one; `g: !(!(i32 => i32) => i32)` has two, one per arrow. This is
  decision 57's tunneled row, never written, and §14's rule that only parameter types are
  instantiated. Whether the type of a `let` that binds a closed function also has open rows is
  OQ-S3.
- **Where a row is written.** Every other function type has its row written, and empty when
  nothing is written: in a `type` declaration, in data, in a cell, in a returned type (§14: "a
  callback's effect in a stored or returned type is the one its type says"). A row written after
  a parameter's type is the parameter's *provided* row (decision 57, E5), spelled
  `f: !(A => B) with E` (*provisional*, #233's spelling). A row on a function type in a stored
  position is spelled `!(A => B with E)` (*provisional*).
- **A function's row** is inferred as today (§18 *Rows*, in declaration order), and a call of a
  callback parameter adds the parameter's row. `for_n`'s row is its parameter's; `task`'s is
  `for_n`'s at `yield_tick`'s row, `Yield[bool]`, with nothing written on `task`.
- **Core:** none. Core never sees a row variable.
- **Status:** by inspection. The inference pass exists (`rowC`, `Frontend/Elab/Effects.lean`); the
  row variables are new.

### E2. A callback value

- **A named function with a row**, used as a value (`yield_tick` in `for_n(3, yield_tick, s0)`),
  is its copy for what serves its row where the value is written: the sites and capabilities in
  scope there, as a call of it would use (§18 *Rows*). A `fn` is closed and `!`-promoted, so the
  copy is a `!` value. Today the elaborator makes these copies for calls
  (`yield_tick__n1 : !U(… ⊸ F[1.0 aff 1 + 1 ~> 1] …)`, by inspection of `bcc desugar`), and
  rejects them as values.
- **A closure literal** (`!{ x -> M }`, `{ x -> M }`) is checked against its expected type, never
  synthesized. Its parameter's type is read from the expected type; at order n + 1 that type has
  order n. Its body is elaborated with the parameter in scope.
  - Its operations resolve lexically, as an operation anywhere does: to the innermost handler of
    their effect around the literal, or to the name the enclosing function's copy has for it
    (tunneling). A provided effect of its expected type is at the port that type names (E5).
  - Its captures: `!{…}` captures persistent values only (`bangThunkV`'s `Persistent Γ`). `{…}`
    captures anything and is used once (`thunkV`). A literal with mutable captured state used
    many times is an affine closure (§22), whose surface form is §22 *Open*.
  - `{ _ -> M }` at `1 ⊸ F_Σ B` is `[λ-dead]` (SPEC §26), which the checker emits.
- **Core:** `bangThunkV`, `thunkV`, `lam`, `lamDead`; a copy is a closed `def`.
- **Status:** established (the rules); by inspection (the copies and lexical resolution exist for
  calls). The change is to accept the value where `notInClosure` and the "passed as a value"
  errors reject it today.

### E3. A call of a callback

In a copy at the row `r`, the call `f(v)`, with `f : !U(Caps ⊗ ⟦P⟧ ⊸ F_r (Caps ⊗ ⟦R⟧))`, is

    g ← return (unbang f);  x ← (force g) (caps, v);  …

- The derelicting `let` (`bind`, `ret`, `bangE`) puts the callback in a `U` slot, which `force`
  reads; the call is `app`; binding its answer is `[let]` at `r` (`effLet`). At the pure row the
  call is a value-level application, as today (`(unbang f) st` in `for_n__g0`, by inspection).
- `[let]`'s side condition is on what the caller holds across the call. At a row with an affine or
  abortive operation it must drop (data, borrows, `!`) or be finalised by drop glue (`[then]`,
  SPEC §19 *Drop glue*). At a row with an unrestricted operation it must be persistent. A
  persistent callback held across a call, `f` called again, drops: this is the condition
  `forStep` meets (`dAt_forStep`, established).
- A one-shot callback is forced from its own `U` slot. An affine one is `aff_call`, which answers
  the result and the rest.
- Held across another call at an affine row, a one-shot callback is rejected: it has no
  destructor. An affine one is closed by drop glue; at `affEffBody`'s `F_Σ 1` that close is a
  finaliser with effects (SPEC §27), beyond the destructors at `F 1` the checker emits today. A
  persistent callback has neither problem. These conditions are the same at every order.
- **The `!U C` force rule is not needed.** Core's `force` reads a `U C` slot only (`CDerives.force`,
  `Core/Fundamental.lean`), and the derelicting `let` gives it one. The elaborator already emits
  this form for every call of a copy (§18: `g <- return f; a <- return v; (force g) a`; in
  `bcc desugar`, `io_fg <- return unbang yield_tick__n1; …; force io_fg io_fa`), and `forStep` is
  typed through it. The rule (`experiments/Targets/LANDING.md`, G1, branch `tier1-effects`) would
  shorten Core terms written by hand (the Targets instance's E2a–c and E10 `retry`); the
  elaboration does not need it.
- **Status:** established (the rules, `dAt_forStep`); by inspection (the elaborator's form).

### E4. Instantiation: a use is a use of a copy

- A call `h(…, c, …)` of a function with callback parameters is a call of `h`'s copy at the types,
  rows and port names (E5) that matching the arguments' types against `h`'s parameter types
  gives. There is one copy per (function, types, rows, names), made on first use and shared after.
  This is the instance of a generic function (§15 *Generic functions*, decision 45) and the copy
  of a function with a row (§18 *Rows*), together. §14's specialization at a callback's
  computation type is the same mechanism for one effect, div; §14 already says another control
  effect "may reuse it".
- Matching is first-order: types are trees, and a row is matched as a set at an `F_r` position.
  A call's rows are solved from all its arguments together: each argument's type, and each
  literal's own operations, give inclusions between rows, and each row variable takes the least
  row they allow. Two parameters may share a variable (`g(f)` inside the callee ties `f`'s row to
  `g`'s parameter's). Hypothesis: inclusions suffice, with no general row unification.
- **Core reads the copies as `[let-poly]` where they coincide.** A function that performs no
  operation of its own and threads nothing (its row is its callbacks' control operations) has one
  term at every row. A program holding it at several rows is `[let-poly]`'s premise term, and its
  derivation gives the let that binds the function once (established: `checkProgram_letPoly`,
  `CDerives.letPoly_copy`). `forN` is such a function. The other copies differ: a function with
  sites or operations of its own differs in name literals, and a copy that threads capabilities,
  or a `for`'s variables (§15), differs in what it passes. Those are separate `def`s, each
  checked; the renaming lemma (`docs/effect-polymorphism.md` §9.2, a hypothesis) would derive a
  copy from another that differs in names only.
- **Status:** established (`[let-poly]`, the copy reading); by inspection (the instance and copy
  machinery); hypothesis (matching suffices).

### E5. Sites; tunneled and provided effects

- A `with h(…) { M }` of a control handler is a site with a fresh static name, `hnd (n, H) M`,
  its clauses a value form (`effHandleV`, SPEC §24). An operation is caught by the site whose name
  it carries, so a function's own handler passes its callback's tunneled operation (established:
  E6's `tunnel`, `d_tunnel`, `tunnel_run`; `catch_fwd`, `fwd_abort`).
- **A provided effect** (`f: !(A => B) with E`, decision 57) is at a *port*: a static name carried
  in `f`'s type, `F_{p:E}`. The callee's `with` of `E` around its calls of `f` takes the name `p`
  (decision 57's R6 rule 5, applied to parameters). A literal passed at `f` performs `E` at `p`,
  read from its expected type (E2). `effects-sum-gen.bc` (E2d) is this case. Passing `f` on to
  another provided parameter is OQ-S4.
- **Core:** `effHandleV`, `effPerform`, `effRaise`, `effSub`.
- **Status:** established (Core); by inspection (ports read from types).

### E6. Answering effects: capabilities passed at each call

- An answering effect in a callback's row is a capability argument, passed with the argument and
  handed back with the answer: `Caps(ε)` in §1.2, the convention of §18's copies and decision 59's
  principle ("effectful code is `!` code, and its environment … is passed to it at each call"). The
  callee's copy takes its callbacks' capabilities among its own and passes each at each call
  (R2d). Nothing captures a capability, so two callbacks may use one in turn (`x_sharedUnit`,
  `sharedUnit_safe`; the capture that is refused is `twoBlocks_refused`, `not_sharedCapture`;
  `experiments/HandlersAsBorrows`, at the paper layer, not Core).
- `S` in `Mut 'l S` is the state type of the handler that serves the effect where the callback is
  written. It is concrete in each instance, since instances are per assignment of handlers (§18).
  It belongs to the row, not to the callback's environment: every callback whose row is `ε` has
  the same `Caps(ε)`.
- `'l` is the copy's lifetime parameter, so the callback's type is rank 1 in it. When the callee
  calls the callback inside a control `with` of its own, that `with` reborrows the capability at a
  fresh lifetime (`withbor3`, §18 *Where an abortive operation may stand*), and the callback must
  take it at every lifetime: `!U(∀'x. Mut 'x S ⊗ … )`. Core has these types (`allI`, `allE`).
  A named function's copy is itself generic in its capabilities' lifetimes (`fn h__op<'l>`, §18),
  so passing it where a type fixes `'l` instantiates it there. How the checker passes and
  converts these types is OQ-S5.
- **Core:** `withbor3U` (`withbor3U_compatX`), `withswap`, `allI`, `allE`, the copy's
  capability tuple.
- **Status:** established (§18's copies, the Core rules); by inspection.

### E7. A continuation stored as a value

- A clause of a handler without a state (SPEC §21) may answer its continuation as codata:

      handler spawn[S]: Yield[bool], S -> (bool * U (iter bool S 1)) + S = {
        return(s) = inr(s);
        yield(t, k) = inl((t, thunkv nu_in < u <- return (); (force k).1 u, (force k).2 >))
      }

  `κ`'s two entries become the two observations of an iterator `U (iter A S 1)`
  (`iter A R R' = νX. F((A ⊗ U X) ⊕ R) & F R'`, SPEC §7). `next` resumes `κ`, which runs the task
  under the handler again, to its next operation or its end. `close` cancels `κ`. It is §15's
  stored generator written as a clause, and A1's `genE`.
- The handler's answer type mentions the codata, never `κ`'s own type. A handler state holding `κ`
  itself would be a type recursive through a thunk, which neither `μ` nor `ν` forms (A1's report,
  from reading the type grammar; not machine-checked). The scheduler is therefore ordinary code
  over codata, the shape of option (b) of the draft spec's OQ-60
  (`docs/effects-state/05b-open-questions-35-68.md`).
- Today's surface writes the clause in core text, as above. A spelling for it (`k` coerced where
  an iterator is expected, as §15 coerces a generator's call where `pull` is expected) is
  *provisional* and not proposed here.
- **Core:** `effHandleV`, `thunkV`, `nuIn` (at `iterBody_nuOk`), `withI`, `force`, `proj₁`, `proj₂`,
  `bind`, `app`; `κ`'s capture cell (SPEC §25).
- **Status:** established in Core (`dAt_spawnCl`, `asyncTasks_run`). Measured at the surface: the
  clause above checks today (§3.3).

### E8. The generic function's loop at a row whose operation resumes

`for_n` loops: `for _ in 0..k { st = f(st) }`.

- **At the pure row** it is a counted loop, `count_try` over the count's length, total, `0 0 0`
  (measured: `for_n` with `tick` alone).
- **At `Yield`'s row, today**, the loop's form depends on how its body reaches the operation
  (SPEC §16 *Effectful bodies*; the rule finds a `perform` in the body):
  - a body that performs it is a div loop over the count's cursor (decision 58), and the function
    that holds it is div. No handler wraps a div computation (SPEC §21 *Open*). Measured: `task`
    with `for_n`'s loop written into it, `for _ in 0..3 { yield(tag); c = c + 1 }`, is reported
    "`for` is div", and `with spawn { task(false) }` is rejected, "the handler `spawn`: the body
    it handles does not have the type its declaration gives it";
  - a body that calls a function whose operation resumes is rejected, since `count_try`'s step is
    pure. Measured: `task` with the loop `for _ in 0..3 { st = yield_tick(st) }`, run by a `for`
    in `main`, is rejected at the call, "its row `[1.0 aff (1 + 1) * i32 ~> i32]` is not within
    `[]`". `for_n`'s body calls `f`, so it is this case.
- **A1 types the loop as a computation instead.** `forN` is `bounded_fix` with the count as its
  budget, one term at every row (`dAt_forN`). At `Yield`'s row it allocates nothing of its own:
  `async-tasks` measures `6 0 0`, the trace's nodes.
- Which elaboration a counted loop gets at a resuming row is OQ-S1. Until it is settled,
  `async-colourless.bc` needs both #161 and OQ-S1.

## 3. Stored callbacks and stored continuations

### 3.1 What may be stored

| what | Core type | captures | uses | bounded by |
|---|---|---|---|---|
| a persistent callback | `!U(Caps ⊗ A ⊸ F_r (Caps ⊗ B))` | persistent values only (`bangThunkV`): no borrow, no capability, nothing owned | any number | nothing: a `!` value outlives every lifetime |
| a one-shot callback | `U(A ⊸ F_r B)` | anything, borrows included | one | what it captures: `U C` outlives nothing, so it leaves a scope only boxed, `[@d] U C`, at a lifetime its captures outlive (`boxI`) |
| an affine callback | `[@c] U(Aff^c …)` | owned state; borrows only below `@c` (`logState_not_outlives`) | many, then `close` | `@c` (`d_mkBox`); dropping it closes it (`hasDtor_aff`) |
| a stored continuation | `U(iter A S 1)` over `κ` | what the task holds across its operation: what drops (data, borrows lent before its handler, `!`) and what drop glue finalises | one `next` or one `close` | as a one-shot callback; dropping it closes it (SPEC §7 *Destructor*) |

- **R6** (decision 57) in these terms: a many-use stored callback captures no borrow and no
  capability, and its answering effects' capabilities are passed by whoever calls it (E6). The
  object with a hidden handler state (`dyn`) stays deferred (decision 57).
- **No lend opened inside a task is held by its continuation.** An operation that resumes cannot
  occur inside a borrow block: every borrow's callback is at `Row.Unwind`, abortive operations
  only (SPEC §19; T1). So a stored `κ` captures no lend the task itself opened. Lifting this is
  tier 2 (§5).

### 3.2 Its row

- **A stored callback's row** is the row its type states (E1): nothing is inferred through
  storage. Its control operations are at static names: provided ones at ports in its type, served
  by whoever calls it (E5); tunneled ones at the names of the sites in scope where it was made.
  Site freshness (R3, decision 57: in the elaborator; not built today) keeps a value whose type
  names a site inside that site. R3 is an abstraction property, not a safety one: without it a
  call outside every live instance of the name is an operation with no handler, which typing
  rejects, and a call under another instance of the name reaches that instance, at the same
  signature (SPEC §19 *Names*, re-entry).
- **A stored continuation's observations** are at the handler's outer row `Σ`: `κ`'s resume
  answers `F_Σ R`. In A1 the spawn handler handles all of `Yield`, `Σ` is empty, and a task's
  observations are pure. A task with other effects that nothing inside it handles is OQ-S7.

### 3.3 The scheduler

A1's scheduler, as `corpus/pending/async-colourless.bc` writes it:

- **Per task, a handler.** `with spawn { task(tag) }` runs the task to its first `yield` and
  answers `inl (tag, rest)`, the rest the stored continuation (E7), or `inr s` when the task ended.
- **Across tasks, a loop.** The scheduler is ordinary code over the stored continuations: each
  round resumes each task that yielded (`next`), which runs to its next `yield` or its end, and
  records the tag it yielded with. Its state is both tasks and the trace. In Core it is
  `bounded_fix` at the pure row; at the surface a counted `for`.
- **Measured.** `corpus/pending/async-colourless.bc` with `task`'s last line,
  `for_n(3, yield_tick, s0)`, replaced by three calls of `yield_tick` (what `for_n`'s copy at
  `Yield`'s row computes) checks today. It runs at the source stage, the closure and flat IRs and
  WebAssembly to the answer its header records: the sync use's state `(A, 3)`, both tasks ended
  at 3, and the trace A B A B A B. It measures `6 0 0` with `live 0`. The reports show one copy of
  `task` and of `yield_tick` per spawn site, and the run makes no dispatched call.
- **Why one handler per task and a loop, not one handler holding a queue.** A handler state
  holding continuations is recursive through a thunk (E7). Option (a) of OQ-60, that recursion,
  needs step-indexing, which decision 7 rules out. The shape here is option (b). How far it goes,
  to n tasks and to spawning from inside a task, is OQ-S8.

### 3.4 Why it is safe, by Core theorems that exist

Nothing in §2 adds a rule, so every elaborated program is a `CDerives` derivation and the
existing theorems cover it. Each item is established:

- **Safety and adequacy.** `fundamentalC`, `adequacyC`, `adequacyD`, `adequacyD_obs`: no run of a
  typed closed program, under any allocator, is stuck. The relation at a row is total correctness
  (SPEC §19 *Semantics*), so a stored task's `next` runs to its next `yield` or its end.
- **The handler that stores `κ`.** `handleV_compatC` (`[handle]` at a value form); `κ`'s relation
  `KapRel` holds of the cell form (`ewp_kappaC_resume`, `ewp_kappaC_cancel`), so a stored task's
  `next` and `close` are in the relation at `U(iter …)` through `nuIn` (`cC_nu_iff`).
- **Every operation meets a live handler.** `effSafe_closed` (SPEC §19 *Laws* item 9). A resumed
  task's `yield` meets the spawn handler that `κ` reinstalls: handlers are deep
  (`kappa_resume_steps`, `kappaC_resume`).
- **No accidental handling.** Static names (`catch_fwd`, `fwd_abort`; E6 `tunnel`).
- **A continuation is used at most once by typing.** A clause that drops `κ`, resumes it twice, or
  cancels it and then resumes it has no derivation (`refuses_R_clauses`). A clause that stores
  `κ` in a cell and reads it out twice has none (`not_der_at08`); moving it through a cell and
  using it once is typed (`d_at08Once`). A stored task's thunk is not persistent, and its
  observations are an additive pair: one of `next` and `close` runs.
- **The capture cell.** A catch at an affine operation allocates `κ`'s cell (`catch_cell`,
  `catchEv_cell`), and resuming or cancelling releases it (`kappaC_resume`, `kappaC_cancel`,
  `use_frees_cell`). On a run that reaches a value at a persistent type every cell is released,
  `κ`'s among them (`leakFree_closed`). A1's runs end at the empty memory (`asyncTasks_run`,
  `asyncColourless_run`). That every run uses each `κ` exactly once (S6) is SPEC §25 *Open*.
- **A dropped task is cancelled.** Its destructor closes it (SPEC §7 *Destructor*), which cancels
  `κ`: the region's finalisers run innermost first, and the cancel is not interceptable
  (`cancel_prefix`, under its hypothesis `FinRow` on the finalisers, SPEC §19 *Laws* item 5).
- **Borrows.** No borrow rule changes. A lend opened inside a task never reaches its `κ` (§3.1),
  and a borrow from outside that a task holds keeps the task within that borrow's lifetime (§3.1,
  the table's last column).

## 4. Lowering

Handling is erased as decided (SPEC §19 *Lowering*): an operation whose handlers have one closed
clause that resumes in tail position is a direct call, an abortive one is a branch per call, and a
suspension is a state machine. There is no handler stack and no search.

### 4.1 The sync instance: per-row code

- Every copy is a `def` at its rows (E4), so each row gets its own code. `Backend/Clos/Poly.lean`
  gives the same for a `[let-poly]` let written once in a Core term (A1's `async-colourless`, SPEC
  §24 *Lowering*), so the two paths lower alike: no use dispatches, allocates, or answers for
  another use's effects.
- At the pure row a callback call is a direct call of the one code the flow finds, and the loop is
  `count_try`, or `bounded_fix`'s levels as native calls of known code in A1.
- **Measured:** A1's `async-sync`, `0 0 0`; `for_n` with `tick` at the surface, `0 0 0`; the
  order-4 program with its operations taken out (§1.3), `0 0 0`.

### 4.2 The stored case: state machines

- A code that may suspend answers its outcome; its state is a sum per resumption point holding
  the variables live there, and the callee's `k` at a call point, so a continuation has a size
  known statically (SPEC §19 *Lowering*, `Backend/Clos/Capture.lean`). A stored task is `κ` over
  the spawn handler and `for_n`'s state machine: a value held in the scheduler's state, with no
  heap object of its own. The backend builds `κ` itself and never sees its capture cell (SPEC §25
  *Lowering*).
- **Measured:** A1's `async-tasks` and `async-colourless`, `6 0 0`, the six list nodes of the
  trace, and every call direct (41 and 54 call sites, A1's report). The surface scheduler of §3.3,
  `6 0 0`.
- **Rust's comparison:** `join!` over two futures of one `async fn`: both state machines inline in
  the joining future, each poll a direct call. In Rust the generic function would have to be
  `async` itself to take an `async` callback.

### 4.3 Where dispatch and allocation appear

- **Several codes at one call.** One copy at one row that is given two different closures calls
  them through the closure's dispatcher, and resumes their continuations the same way (SPEC §24
  *Open*: one body per row is decision 57's default). A1 measured a variant with the callback
  written out at each use, `6 12 0`, and one with a single rotating task slot, `6 6 0`, the
  `Box<dyn Future>` executor's pattern without the boxes (A1's report; scratch variants, not
  registered). Rust would instantiate per closure. OQ-S6.
- **Recursion through a resumption point** costs one object per level, as Rust's `Box::pin`
  (SPEC §19 *Lowering*, `recursive-yield`). Nothing here adds such a recursion.
- **Code size** is one body per (function, types, rows, names). Copies that differ only in names
  (`task__n1`, `task__n2`) are separate code today (decision 57's typing artefacts; OQ-S6).

### 4.4 The pending programs' expected counts (hypothesis)

| program | expected | from |
|---|---|---|
| `async-colourless.bc` | `6 0 0` | the variant of §3.3 measures `6 0 0`. Under OQ-S1 (a), `for_n`'s copy at `Yield`'s row has A1's shape (`async-tasks`, `6 0 0`); under (b), not estimated |
| `effects-callback-orders.bc` | `0 0 0` | its pure variant measures `0 0 0`. The `for` over `apply`'s copy has a clause that resumes in tail position, a direct call (SPEC §15, as `gen-produce`), and the raise is a branch |
| `async-borrow.bc` (A2) | not estimated | its variant without the `yield` measures `7 0 0`, the list's cells. A place that spans a suspension is a cell today (`docs/effects-state/BRIEF.md` §1a); tier 2's representation is open |

## 5. What this does not cover

### 5.1 Borrows held across a suspension (T1, tier 2): A2

`corpus/pending/async-borrow.bc` is the acceptance program, rewritten without colouring. Two tasks
read one borrowed list under the scheduler of §3.3, inside the borrow's block. `sum` yields at
each element from inside its fold's callback, `sum_alg`; `len` does not yield. No function is
marked.

- **What blocks it.** `fold_imm`'s algebra is given an `imm 'y` view of each node at a lifetime
  `'y` of the fold's own (SPEC §6: the algebra is at `∀'y ⊏ ⊤`). The fold's term is a `withload`
  at each `Ref X`, a lend at each pointer hop, and a node's algebra runs inside the lend that
  reached the node (`travK`, `Core/FoldImm.lean`). `sum_alg` yields with those lends open, so the
  stored continuation would hold them across the suspension. Core's stops forbid it: T1 (conjunct
  40 of `wpG`'s stop) for an `imm` frame, and `↭` (conjunct 37) for a `mut` lend
  (`docs/effects-state/BRIEF.md` §3 item 1). Every borrow's callback is `Row.Unwind`, and
  `withload`'s too (`withloadU`).
- **Behind the same `yield`:** a fold whose algebra performs an operation (K4, SPEC §18 *Open*;
  draft spec OQ-62: the folds' algebras are pure), and effectful callbacks (#161), which is
  today's error.
- **What in it is tier 1** (by inspection): the borrow `b1` itself, lent by the enclosing block
  before the tasks start, comes from outside the handled computation, which T1's conjunct
  compares against at the stop. The tasks stay inside the block: `U C` outlives nothing (§3.1).
  With `sum_alg` not yielding, the program checks today and runs to `i32[9]` at `7 0 0`
  (measured).
- **The proposal stops there.** It adds no rule that lets a lend span a stop. Tier 2 is shelved
  (`research/effects/src/tier2-status.md`, branch `targets`); A2 is its test.

### 5.2 Also not covered

- **Rank 2:** a callback parameter used at two rows that cannot share one (OQ-S2).
- **A handler around a div computation**, and with it a task that never ends, such as a server's
  loop (OQ-S1 (b), the draft spec's OQ-67).
- **Spawning from inside a task**, an operation whose argument is a computation at its own row
  (the draft spec's OQ-61), and a queue of n tasks (OQ-S8).
- **Multi-shot:** ignored (decision 63). Nothing here depends on an unrestricted operation.
- **Operations that take computations** (higher-order effects): not now (decision 57).
- **Recursion through a site** whose callback tunnels that site: rejected, as today (decision 57,
  #173).

## 6. Open questions

Each is for the user. None is answered here.

> **OQ-S1. The loop of a function at a row whose operation resumes.**
> At `Yield`'s row, `for_n`'s counted loop calls a callback that resumes. Today a body that
> performs such an operation makes the loop div (decision 58), which no handler wraps, and a body
> that calls a function that performs one is rejected (E8). Either way the rule must read the
> rows of the calls in the body, not only its `perform`s.
> - **(a) `bounded_fix` over the count.** A counted loop whose body's row resumes is `bounded_fix`
>   at that row with the count's length as its budget, as A1's `forN`: total, and a computation a
>   handler wraps (`dAt_forN`; `async-tasks`, `6 0 0`). Used at every row, the pure one included,
>   the loop is one term at every row and its copies are `[let-poly]`'s premise; A1 measures it at
>   `0 0 0` at the pure row (`async-sync`), as `count_try` does. Changes decision 58's rule for
>   counted sources: the reports of `corpus/for-data-div.bc` change and its counts need measuring
>   again. Drains and `while` loops stay div.
> - **(b) Keep the div loop; handle a div computation per observation.** A `with` around a div
>   computation is installed at each observation: its return clause meets the loop's end, and a
>   skip continues the next observation under it. This is §15's stored generator over a looping
>   body, generalised to any handler (the draft spec's OQ-67, per-observation form). It is needed
>   anyway for a task that never ends. Its elaboration and its counts are not known.
> - **(c) Both:** (a) for counted sources, (b) for drains.

> **OQ-S2. Rank: a callback parameter used at two rows.**
> Inside one body a parameter has one row (§1.3).
> - **(a) Rank 1, with `[sub]`.** The parameter's row is the union its uses need. A program is
>   rejected where that union has no handler, with a message naming the parameter. The workaround
>   is two parameters, or a top-level function in place of the parameter. No kernel change.
> - **(b) A row binder in Core's types** (decision 62's means, "row variables in the kernel"):
>   `docs/effect-polymorphism.md` §4 Option 1's costs: two `CTy` formers, a row environment in the
>   relation, a substitution lemma, `Loop_ε`'s positivity at an abstract row.
> - **(c) Name variables** (`∀ν`, prompt variables; L1 of `docs/second-class-and-system-c.md` §8):
>   a name map in the relation. It would also remove copies per name, ports and R3.

> **OQ-S3. Whether a let-bound closed function has open rows.**
> - **(a) Yes.** A `let` that binds a closed function value is generalised over the rows its type
>   leaves unwritten, and each use gets a copy: `[let-poly]` read at the surface, ML's value
>   restriction.
> - **(b) No.** Only `fn`s and their parameters have open rows; a local function has one row, the
>   union of its uses. Simpler; a program binds a top-level `fn` where it needs two rows.

> **OQ-S4. Passing a callback with a provided effect on to another provided parameter.**
> Decision 57 leaves this open between (a) and (b).
> - **(a) `rename (p, m)`**, Frank's adaptor (`docs/effect-polymorphism.md` §5.6): one primitive,
>   one compatibility lemma, the unique-decomposition and determinism cases of one frame.
> - **(b) Inlining required** in exactly that case (R2c).
> - **(c) Ports as instance parameters.** The callee's copy takes its port's name from the callback
>   it is given, so a callback passed on is already at the right name. No relabelling and no
>   kernel change, but more copies (typing artefacts until a renaming lemma), and a renamed
>   instance where the name meets one of the callee's own sites (`docs/effect-polymorphism.md`
>   §6.2).

> **OQ-S5. A callback given a reborrowed capability (lifetime binders).**
> When a callee reborrows a capability for a callback's call, the callback's type is
> `!U(∀'x. Mut 'x S ⊗ …)`, and the checker compares types by `=` with no α-conversion of lifetime
> binders (`Frontend/README.md`, Incompleteness 2).
> - **(a) η-expansion where binders differ**, by `bangThunkV`, `allI`, `allE`, `force` and `app`,
>   with the checker deciding α-equivalence to know when. No kernel change. One wrapper per
>   conversion, which the backend may collapse; not measured.
> - **(b) A Core lemma:** `CDerives` invariant under renaming a bound lifetime, a structural
>   induction like `CDerives.append_dead`. No wrapper; the checker converts.

> **OQ-S6. One body per row, or one per closure.**
> Decision 57's default is one body per (function, profile), with specialising per callback an
> optimisation chosen by a heuristic, which is open. One copy given two closures at one row
> dispatches (`6 12 0` in A1's variant, §4.3), where Rust would not.
> - **(a) The default:** dispatch where several closures meet; less code.
> - **(b) One copy per (function, row, closure)** where the closure is known at the use: Rust's
>   monomorphisation per closure type; no dispatch, more code.
> - **(c) A heuristic between them** (decision 57's open item). Separately: sharing code between
>   copies that differ only in names, which the renaming lemma would allow.

> **OQ-S7. A task with other effects, or a capability across its `yield`.**
> - **Other effects.** A task that also raises has observations at a row: an iterator at `Σ`
>   (Core's `ν` admits effectful leaves at closed operation types, `EffLeaf`), resumed inside the
>   handlers of `Σ`. Today a stored generator's observations are pure (SPEC §15 *Open*).
>   (a) Iterators at a row; (b) tasks handle their other effects inside, so their observations
>   stay pure.
> - **A capability held across a `yield`.** What a task holds across an affine operation must
>   drop, and a capability has no destructor (SPEC §15 *Open*, `gen-digits.bc`).
>   (a) Thread the capability through the operation, `yield : (A ⊗ C) ↠ C`: it must be closed in
>   lifetimes, so an opaque host handle can and a `Mut` borrow cannot. (b) A cancel that hands back
>   a residual. (c) A `linear ctl` operation, which has no cancel.

> **OQ-S8. The scheduler's reach: n tasks, and spawning from inside a task.**
> - **n tasks.** (a) Fixed slots, as A1 and `join!`. (b) A list of stored tasks,
>   `μX. 1 ⊕ (U(iter …) ⊗ X)`: one allocation per node in this backend, and a resume through the
>   list dispatches when the tasks' codes differ (`6 6 0` in A1's rotating variant).
> - **Spawning from a task** is an operation whose argument is a computation at its own row (the
>   draft spec's OQ-61): (a) forbid it; (b) a positive recursive signature, read as a least fixed
>   point; (c) a `self` row reference. Threads, later, meet the same question.

## Sources

- `Core/EffAsyncPrograms.lean` (A1), `Core/EffTier1Programs.lean` (E1, E2d, E6, E9),
  `Core/LetCopy.lean`, `Core/PolyLet.lean`, `Core/EffSafety.lean`, `Core/EffMachine.lean`,
  `Core/EffCancelRuns.lean`, `Core/Inversions.lean`, `Core/Rejections.lean`, `Core/Aff.lean`.
- SPEC §6, §7, §14, §15, §16, §18, §19, §21, §22, §24–§27.
- `docs/effect-polymorphism.md` (decision 57's design: §4, §5.2–§5.8, §6, §9.2);
  `docs/second-class-and-system-c.md` (decision 59's principle, §3; L1, §8);
  `docs/effects-state/03-attempts.md` §7 (#233); `docs/effects-state/05b-open-questions-35-68.md`
  (OQ-60, OQ-61, OQ-62, OQ-67); `docs/decisions.md` 45, 57–59, 62, 63.
- Branch `effect-callbacks` (#233): its SPEC §22 and `corpus/pending/cb-*.bc`.
- Branch `tier1-effects`: `research/effects/src/decisions.md` (the decided algebra) and
  `experiments/Targets/LANDING.md` (the `!U C` force rule, G1).
