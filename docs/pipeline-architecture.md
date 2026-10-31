# Pipeline architecture: carry what the frontend knows (#552)

A design for how the structure the frontend knows reaches the backend. It changes no code. Each
claim is marked:

- **measured**: a run of `.lake/build/bin/bcc`, `bcc-counts` or `bcc-counts --sites`, built from
  `main` at `3b67803`, reproducible by the commands of §10;
- **by inspection**: read off the code or SPEC at `3b67803`, with the line cited;
- **hypothesis**: argued here, not checked.

The hard requirements are #552's: every decided law holds and the algebra hard stop applies
(`research/effects/src/decisions.md`, *The decided algebra*); nothing breaks the borrow calculus;
no run-time dispatch to handlers; performance by construction in our IR; code size is not a goal;
real choices as options, with a recommendation; no syntax decisions.

**Div is a handled effect.** The user, 2026-10-18: "The original plan was Div being a handled
effect." The user's earlier words are "Div should be an effect" (2026-09-28), with the runtime
driving `main` as the outermost handler. The reading that divergence is only codata and is never
handled was a recorder's sentence. This PR corrects the records that carried it
(`docs/effects-state/05a-open-questions-1-34.md` OQ-15, `docs/effects-state/04-decisions.md`
item 10 and D1, `docs/decisions.md` 67). This design takes that plan as its base.

## 0. Summary

- **What is lost, and where** (§1). The frontend decides each construct's shape, then emits a
  kernel term chosen for the proofs: a `ν` machine for every div body, whoever consumes it; a
  handler site with a captured `κ` for each `for` over a generator; a state-passing closure for
  each stateful handler; a copy per site. The erasure drops the types, and the backend compiles
  what is left and recovers the structure. §1.2 lists 31 such places, in four groups:
  - choices of the elaborator, recovered by searching user code (A1–A11);
  - checked facts the erasure drops (B1–B6);
  - recognisers of fixed schemes, which are exact and stay (C1–C7);
  - re-derivations inside the frontend (D1–D7).
- **The principle** (§1.4). Recognising a fixed scheme is exact. Recognising a property of user
  code is a search. Such a property should come from where it was decided.
- **The base design** (§3). `Div` is a library effect with one must-resume operation,
  `tick() -> Next`, where `Next` is `next` or `close`.
  - **Loops perform it.** A `while`, a `loop` or a drain is a kernel loop primitive, `iterate`,
    at a row holding `Div`. Ticks stand exactly where today's machine skips.
  - **Its handlers** are the runtime's driver of `main`, `div_fuel` and `reify`. `reify` makes a
    loop value where one is expected. Today's per-body machine is that same reification, done
    eagerly for every body.
  - **Every loop falls under effect-lowering's classification.** The runtime's clause and
    `div_fuel`'s resume in tail, so each is a direct call, and a loop is a native loop. `reify`
    keeps `κ`, so it is a state machine, built by `Capture`. State machines are built only there
    and at other stored `κ`.
  - **Totality** is the row without `Div`. Loops U2's class pass is the inference of `Div` in the
    row.
- **First unit: a proof spike, S0** (§4.1). It settles three unknowns:
  - the relation for computations that tick forever: a greatest fixed point over segments
    guarded by `tick`, or a step-indexed fragment, with the trade-off stated;
  - the residual a loop closed early hands back, by a resume with `close`, not a cancel;
  - the placement of ticks, so that `div_fuel`'s counts are unchanged.

  Its acceptance and kill criteria are given. If S0 is killed, §3.6's fallback (the previous
  revision's carry-then-verify path) applies.
- **What remains of carry-then-verify** (§3.5):
  - **dropped**: the loop entries, call modes, the span channel and N4. Loops are kernel terms,
    and their consumers are handlers;
  - **merged**: N1 (typed schemes) into the frontend build unit; N2 shrinks to keeping `qs` and
    passing the effect context on;
  - **kept**: the site table N3 (effect-lowering unit 9), for user-code clause kinds, copies and
    handler state. #216 is unchanged.
- **Kernel cost** (§4.2), on the effect side only:
  - one primitive (`iterate`);
  - one relation clause (`cwp` at rows with `Div`);
  - `reify` and `div_fuel` with their rules;
  - FP and adequacy restated at those rows.

  No value-type or computation-type former. `total_every_run` is unchanged. Borrow calculus
  unchanged while `tick` obeys T1.
- **Hard stops** (§9.1). None, if S0's candidates hold. Two are reported as conditional, with
  their law and programs: closing by a cancel that answers the residual; ticks off today's skip
  points. One restriction needs a recorded decision: a handler of `Div` typed at a row without
  `Div` would contradict `total_every_run`.
- **Defects** (§9.2). All three are kept: the qualifier dropped at conversion (it matters more,
  since `tick` is linear); string schemes (most are deleted with the machine, the rest still
  block laws); the lowering report that is not the lowering.

## 1. Inventory of recovery

### 1.1 The pipeline as built

| stage | file | input → output | keeps | drops |
|---|---|---|---|---|
| effects | `Frontend/Elab/Effects.lean` | surface → surface with sites | site names, `forSite`/`pullSite` nodes (`:2680–2754`), copies per assignment, rows | — |
| sugar | `Frontend/Sugar.lean` (`elaborateS`, `:5556`) | surface → core, by typed elaboration (`TCx`) and string templates (`template`, `:570`; `mTemplate`, `:1057`) | names in `perform`/`handle` | the site nodes' kinds, loop nodes, which call is direct-style |
| typed IR | `Frontend/Elab/Pipeline.lean:58–63` | core → TIR on core → core (identity) | — | — |
| check | `Frontend/Check/Program.lean:182` | core → `Checked` (`e : Expr`, `sigs`, `pins`, `:36–43`) | the derivation (a `Prop`), the effect context `Checked.Ξ` (`:49`) | types and spans, in `e` |
| driver | `Backend/Driver.lean:104–110` | `Checked` → `Clos.convert k.main.e` | `e` only | `sigs` |
| convert | `Backend/Clos/Convert.lean` | `Expr` → closure IR; pre-passes `prepare` (`:857`) | names (literal) | the qualifier tags `qs` (`:737–739`) |
| poly | `Backend/Clos/Poly.lean` | re-runs the effect analysis to find lets used at different rows | — | — |
| capture | `Backend/Clos/Capture.lean` | handlers → codes, machines | — | `hnd`/`perform` |
| unwind, collapse | `Clos/Unwind.lean`, `Clos/Collapse.lean` | raises → branches; codata thunks built eagerly | — | — |
| types, flow | `Clos/Types.lean`, `Clos/Flow.lean` | layout types by unification; 0-CFA | — | — |
| flat | `Flat/Lower.lean` | words; `drive` for `main` (`:1140`, `:1465–1480`); `count_loop`, `count_try_loop` (`:1405`, `:1439`) | — | — |
| #540 (WIP) | `Flat/Opt.lean`, branch `loops-as-loops` | a partial evaluator over the flat IR | — | — |

The program is elaborated twice: `checkProgram` calls `Frontend.Elab.elaborate`
(`Program.lean:183`), and `checkedOf` calls `Frontend.Sugar.elaborateO` again for the I/O wrapper
(`Driver.lean:63`). By inspection. The two runs are of pure functions, so they agree. The second
costs compile time (#537: "Compile time: we lose").

### 1.2 Every place a later stage reconstructs, or never gets, what an earlier one knew

"Knew" cites where the fact was in hand; "units" are the planned units that exist because of the
loss.

**A. Choices of the elaborator, recovered by searching user code**

| # | fact | how the backend gets it | who knew it | units |
|---|---|---|---|---|
| A1 | a clause resumes once in tail on every path | `tailClause?`, `TPath.resume?` (`Capture.lean:590–633`), applied per name in `tailResumptive` (`:712–727`) | `forSite` makes the `for` body the clause and knows its `break`/`return` (`Effects.lean:2680–2718`) | #541 u1 (#544), u3, u9 |
| A2 | a clause resumes or cancels on each path (`break` in an arm) | not recovered: a machine. Measured: `corpus/for-yield-branch.bc` site 3, `machines 17 suspending 9` | the same | u4 |
| A3 | a clause keeps `κ` as a stored generator's rest | `Capture`'s machine, correctly | `pullSite` (`Effects.lean:2722–2754`) | u5 |
| A4 | the clause code at a site | `Solver.clausesAt` over the 0-CFA, and "every handler of the name has one closed clause" (`Capture.lean:635–642`, `:716–722`) | the handler declaration | u3, u9 |
| A5 | the handler's state | lost: a closure `U(S ⊸ F …)` applied at each resume, a dispatched call (SPEC §19 *Open*; 7 programs, `docs/effect-lowering.md` §1.4) | `HInfo.params`, the `mut` parameters | u3 |
| A6 | two copies are one body | lost. Measured: `range__n1`, `range__n2`, `range__n3` in `for-yield-branch.bc` | the copy table (`copyFor`) | u5 |
| A7 | a stored generator is drained by one `for` | lost | the adapter instance and its argument | u7 |
| A8 | a codata value built by a fixed scheme | `Collapse` recognises `thunkv nu_in ⟨(nu_out (force f s₀)).1, …⟩` in two forms (`Collapse.lean:1–30`) | the scheme that wrote it (`io_mk`, `bcc desugar`) | u5 |
| A9 | the loops of a div body | the §14 machine built from templates (`mAssemble`, `Sugar.lean:1463–1527`; `mLoop`, `:1320`); `drive` turns it (`Flat/Lower.lean:1140`); #540 specialises `drive` back into loops, within `budget 8000`, `specMax 256`, `depthMax 256`, `copyWork 2000` (`Opt.lean:750–763`, uncommitted on `loops-as-loops`) | the loop node (U1, #548), and whether each call is direct-style (SPEC §14 *Inference and markers*) | #540, loops U2 and U4, effect-lowering L1/L2 and kill criterion 6 |
| A10 | the consumer of a loop: a complete driver, `div_fuel`, a stored value | lost | the expected type at the call: "a call checked against its own loop type is the loop as a value" (SPEC §14) | #540, kill criterion 6 |
| A11 | a let used at several rows | `Poly` converts once, runs `Prog.effects`, compares codes, converts again (`Poly.lean`, header) | the copies per row assignment | — |

**B. Checked facts the erasure drops**

| # | fact | how the backend gets it | who knew it | units |
|---|---|---|---|---|
| B1 | the operations each code may suspend with or raise | least solution over the flow, iterated (`SFacts.of`, `Capture.lean:469–519`; `UFacts`, `Unwind.lean`). SPEC.md:3204: "the rows' information, recovered after erasure" | the derivation's `F_Σ` types | — |
| B2 | layout types | unification (`Types.lean`); on failure `capture` runs again with answers as variants (`Driver.lean:93–101`) | the checker | u8 (the re-injection is the identity on one sum type) |
| B3 | the qualifier `lin`/`cancel`/`unr` | discarded at conversion (`Convert.lean:737–739`); `κ`'s cancel arm built for every qualifier (`kapBody`, `Capture.lean:259–266`) | the term: `hnd (n, (qs, H))` | — |
| B4 | abortive or control | read off `raise` against `perform` (`Ops.of`, `Capture.lean:178–194`) | kept: correct as is | — |
| B5 | the site of an operation | kept: the name is a literal (`Convert.lean:737`, `:755`) | — | — |
| B6 | each name's signature, the effect context | `Checked.sigs` reaches `CheckedProg.main` (`Driver.lean:47–51`), and nothing in `Backend/` reads it | the checker (`Checked.Ξ`, `Program.lean:49`) | — |

**C. Recognisers of fixed schemes** (exact; the scheme's shape does not depend on the program)

| # | scheme | recogniser |
|---|---|---|
| C1 | the Z combinator's fixed point (`Core/Fix.lean`) | `fixBody?` (`Convert.lean:300`) |
| C2 | `fold_own`, `fold_reuse` traversals | `travShape?`, `foldShape?` (`:308–337`), then pointer reversal (`Flat/Lower.lean:891`) |
| C3 | the axiom `swap` | `isSwap` (`:280`) |
| C4 | string literals and literal views | `litTable?`, `litView?` (`:371`, `:406`); "the shape is semantic" |
| C5 | a scoped cell, `withbor (alloc v)` freed once | `markScoped` (`:541`) |
| C6 | a finaliser frame's two clauses | `markUbinds` (`:460`); read back by `finRaises`, `finSuspends` (`Capture.lean:1116`, `:1124`) |
| C7 | a `case` on a code's parameter as `&`, a forwarder as `unfold`'s | `Types.lean` (header), `selArg`/`skeysG` (`Capture.lean:401–414`) |

**D. Re-derivations inside the frontend**

| # | fact | where | who knew it | units |
|---|---|---|---|---|
| D1 | a body loops | `loopsAt` (`Sugar.lean:440`), `loopsOnSpine` with `fin` by source form (`LoopLend.lean:123`) | the types, after inference | loops U2 |
| D2 | the operations a body performs | `opsC`/`opsV` (`Sugar.lean:2837`), re-read from `perform` nodes | the effects pass's rows | — |
| D3 | `return`'s type | the head of `DivSt.exits`, per form (`docs/loops.md` S4) | the function's result | loops U3 |
| D4 | types of the program | the TIR is inferred on core *after* the sugar (`Pipeline.lean:58–63`); the sugar has its own inference (`TCx`). `docs/typed-elaboration.md` §1.1 planned the TIR on the surface | — | — |
| D5 | each site's kind | reported as text only (`Effects.lean:2446`, `:2708`, `:2745`). The report is not the lowering. Measured: `for-yield-branch.bc`'s three sites have one report text; sites 1 and 2 are direct calls and site 3 is a machine | — | — |
| D6 | each scheme | 18 calls of `template` and `mTemplate` in `Sugar.lean` (`:784` to `:4844`), each a source string parsed at elaboration (`parseComp`, `:253`) | — | every unit that proves a law "over the template" (loops U2, effect-lowering u3, u7) |
| D7 | whether a `main` loops | `mainLoops` (`Sugar.lean`, `elaborateS`) by `loopsAt` | the class | — |

### 1.3 Measured

- **A div body is a machine whatever consumes it.** `fn spin(n) = … while i < n { s = s + i; i =
  i + 1 }; s` and `main -> i32 = spin(10)`: `spin : !(i32 => U (delay i32))`, and so
  `main : F U (delay i32)`. `main` becomes a machine because it calls `spin` in direct style. The
  module has 51 code functions and 34.7 KB of WAT. The same sum written `for i in 0..n` gives
  `spin : !(i32 => i32)`, `main : F i32`, 10 code functions and 12.6 KB. Both print `i32[45]`, with
  counts `0 0 0 0 0 0`.
- **Sites** (`bcc-counts --sites`):

  | program | direct / calls | dispatched | tail-resumptive | machines | suspending |
  |---|---|---|---|---|---|
  | `bench/chain-yield` | 209 / 213 | 4 | `[(1, 0)]` | 2 | 0 |
  | `bench/chain-gen` | 371 / 379 | 8 | `[(1, 0)]` | 28 | 18 |
  | `bench/sieve` | 300 / 300 | 0 | `[]` | 0 | 0 |
  | `bench/gen-tree` | 261 / 263 | 2 | `[(2, 0)]` | 1 | 0 |
  | `bench/async-tree` | 383 / 396 | 13 | `[]` | 4 | 4 |
  | `corpus/for-yield-branch` | 244 / 254 | 10 | `[(2, 0), (1, 0)]` | 17 | 9 |

  sieve has no control name, so its 5.63× (`bench/README.md:42`) is all §14's machine, which
  `Capture` does not count. chain-yield's two machines suspend nothing: they are dead codes left
  for effect-lowering unit 3 (#544's report). Its remaining 2.10× (`bench/README.md:47`) is the
  driven `while` of `range`.
- **The frontend knew the kinds.** `bcc check bench/chain-gen/main.bc` reports `for over filter
  (Yield): … the body is its clause`, and `stored generator of map (Yield): … its clause keeps the
  continuation as the rest`, at elaboration, before any backend pass.

### 1.4 The principle

Two kinds of recogniser look alike and are not.

- **A fixed scheme** (C1–C7, A8): the scheme's parameters do not change its shape, so matching
  it is a total, exact test. `litTable?`'s comment says "the shape is semantic: a λ of it
  computes exactly its table, however it was written". These stay.
- **A property of user code** (A1, A2, A4, A9): the shape is the user's program (a `for` body, a
  div body), so every way of writing it is a case the recogniser must know. chain-yield's `if`
  defeated `tailClause?` until #547 (`docs/effect-lowering.md` §1.5). #540's specialiser stops at
  its budgets and keeps `drive` past them. These facts were decided once, upstream. The backend
  should receive them, and check them.

## 2. Which route carries each fact

### 2.1 The routes, and the test for each

- **G (typed and checked).** The fact is a typing fact: a type, a row, a kernel term, or a form
  the checker checks, with a law it must satisfy. It is carried because the checked term has it.
  A new grade is admitted only when its equational theory is stated first.
- **M (structured IR and table).** The fact is about the program's shape, or about which scheme
  the elaborator chose. It is computed once on the typed surface tree, carried in a table keyed
  by static name, and verified against the checked term.
- **R (recovery kept).** The fact is a fixed scheme (§1.4), or a whole-program analysis with no
  better source, or the input has no frontend (the kernel programs of `Backend/Kernel.lean`, and
  hand-written core).

### 2.2 The G candidates of #552, judged

| candidate | the law it would have to satisfy | verdict |
|---|---|---|
| **Totality, or div, as an effect on loops and calls** | `total_every_run` at rows without `Div`; the handler laws at `Div` | **Adopted: `Div` in the row** (§3). A loop performs `tick`. A function whose row has no `Div` is total. Loops U2's class pass (`docs/loops.md` §2.2) is the bottom-up inference of `Div`, which the effects pass's row inference already does for every effect. `machine(L)` is "`L`'s body performs `Div`". Upward closure is the row's union. The `U(Loop B R)` result type was the encoding of the same fact |
| **A suspension or "may reify" mode** | `reify`'s observation is one segment up to the next tick | **Adopted as a handler, not a mode.** `reify` is an explicit term, where a loop value is expected. A kernel mode would be a second-class value-type former, and it is not needed: the handler is the reification point, as System C's box is |
| **The qualifier, refined: "exactly once on every path, in tail"** | `tail_resumes` (`Core/Handlers.lean`) | **Not a grade.** Tail position is not a count: `M; k y` and `k y; M` use `κ` the same number of times. The typing statement would be parametricity in the answer type, and the kernel has no type `∀` (decision 8). **Carried as a clause form**: one fixed scheme per kind, classified exactly (§3.4). `Div`'s own handlers are library constants with fixed clauses |
| **"0" for abortive branches** | `catch_abort`, `abort_absorbs` | **Already in the kernel**: answer `0`, no `κ` (B4) |
| **#216: clause multiplicity** | a clause of an abortive operation runs at most once per handler instance | **A real grade, admitted**, read from what `[handle]` has (qualifier and answer type). Its own unit (§4.4) |
| **Static handler sites in the row** | static per-site names (law 3) | **Kept already** (B5). `Div` follows the rule: the runtime's driver, each `div_fuel` and each `reify` is a site with its own name, and a div function is copied per site assignment, as any function with a row is (§18) |
| (added) **Types to the backend** | none: read off the derivation | **G, later**: a typed erasure removes B1, B2, A11 and the retry |

### 2.3 The routes, per fact

| fact (§1.2) | route | why |
|---|---|---|
| A1, A2 clause kind (tail, resume or cancel) of a user clause | **G**: a fixed scheme per kind, classified exactly | a checkable form with a law |
| A3 stored `κ` | **G**, the same | `Capture` builds the machine |
| A4 the clause code at a site | **M**: the table names it | which code is shape |
| condition 2 of effect-lowering §2.3 | **M**: a static check over names | not local to `[handle]` |
| A5 handler state | **G**: the state's type, in the effect context | unit 3's law |
| A6 copies, A7 drained by one `for` | **M** | facts of the elaboration |
| A8 the codata scheme | **R** | a fixed scheme |
| **A9 loops** | **G**: `iterate`, a primitive the erasure keeps, as `count_try` is | the kernel term *is* the loop |
| **A10 a loop's consumer** | **G**: the `Div` handler around it (runtime, `div_fuel`, `reify`) | a term, classified as any site |
| A11 lets at several rows | **R** now, **G** with types | — |
| B1 rows, B2 types | **R** now, **G** with a typed erasure | — |
| B3 the qualifier | **G**: keep `qs` | `tick`'s `κ` is linear |
| B6 the effect context | **G**: hand `Checked.sigs` to the backend, with clause kinds per name | the checker built it |
| C1–C7 | **R** | fixed schemes |
| **D1, D7 a body loops** | **G**: `Div` in the row | row inference |
| D2 a body's operations | **G**: the row | — |
| D3 `return`'s type | **M** (loops U3) | — |
| D4 types | the TIR on the surface (`docs/typed-elaboration.md` §1.1) | — |
| D5 the report | rendered from the table | — |
| D6 string templates | the per-body machine's are **deleted**; the others become typed schemes where a law needs them | — |

## 3. The resulting pipeline

### 3.1 The stages

    parse
    effects             sites, instances, copies; Div inferred like any effect
    typed elaboration   loops → iterate / count_try / bounded_fix at the row, ticks at
                        today's skip points; reify where a loop value is expected;
                        no per-body machine (typed schemes)
    check               Checked: e, sigs (+ clause kinds per name), pins
    erasure             e with iterate as a primitive; qs kept; sigs passed on
    backend
      convert, poly     qs kept through Convert
      classify          every site by its law, from the term and the table: the runtime's Div
                        clause and div_fuel's are tail-resumptive; reify and stored generators keep κ
      lower, no κ       direct calls, native handler state (div_fuel's counter), resume or
                        cancel in place (effect-lowering 3, 4)
      iterate           a native loop, as count_try_loop is
      capture           state machines: reify and other stored κ only
      unwind, collapse, types, flow, flat (+ #540's narrowing and poison padding)

### 3.2 `Div`

**The effect.** `effect Div { must_resume ctl tick() -> Next }`, with `Next = 1 + 1` (`inl ()` next,
`inr ()` close), in the library. Spellings are provisional. The continuation is **linear**: it
has no cancel, so closing a loop is a *resume* with `close`, never a cancel (§4.1, unknown 2).

**The loop primitive.**

    iterate : !(S ⊸ F_Σ(B ⊕ S) & F_Σ R) ⊗ S ⇒ F_Σ (B ⊕ R)        Div ∈ Σ

    iterate (f, s) ↦ (f s).1 to r. case r { inl b → return (inl b)
                                          | inr s' → tick () to n. case n { inl _ → iterate (f, s')
                                                                          | inr _ → (f s').2 to q. return (inr q) } }

- The step is `unfold`'s: one turn, or `close` handing back the residual `R` (SPEC §14 *The
  residual*).
- The primitive ticks at each back edge, so every iteration is guarded, whoever wrote the step.
- The result `B ⊕ R`: finished, or closed early with the residual.
- It is one machine step, like `count_try` (SPEC §16 *Why a step*). It is kept as a primitive by
  the erasure, so the backend sees the loop.

**Elaboration** (replacing §14's *One state machine per body*, `Sugar.lean:957–1527`):
- **Loops.** A `while`, a `loop`, a drain and a counted loop whose body performs `Div` are
  `iterate` or `bounded_fix` over the count at the row (SPEC §30's form at a resuming row).
- **Ticks.** Ticks stand exactly where today's machine skips: `mGoto` emits `MCx.skip`
  (`Sugar.lean:1103–1128`) at every move to a point at the empty row, and only at a move back to
  a loop's head at a row. Back edges are `iterate`'s own ticks. A forward move at the empty row is
  an explicit `tick()`.
- **After a `close`**, the code runs what today's state `close` runs (`mClose`, `Sugar.lean:1130`):
  it closes what it holds, innermost first, and returns `inr` of the residual by name.
- **A direct-style call** of a div function is an ordinary call at the row. The callee's ticks
  are the caller's, and an `inr` from it is handed on as the caller's residual (today's rule,
  SPEC §14 *Elaboration*).
- **A loop value** (an argument at a `U(Loop …)` parameter, an annotated binding, a `div_fuel`
  argument, a stored generator `U (pull A B R)`) is `reify` of the computation.
- **Specialisation at a callback's computation type** (SPEC §14) becomes rows: a callback with
  `Div` in its row is an effectful block (§30), and the callee is copied per row, as any function
  with a row is.

**The handlers.**

| handler | clause for `tick` | kind | lowering |
|---|---|---|---|
| the runtime, around `main` | `k.resume next` | tail-resumptive | a direct call answering a literal; `iterate`'s `case` on it folds; a native loop |
| `div_fuel n M` | `k.resume next` while the counter is positive, then `k.resume close` | tail-resumptive on every path, with a state | a direct call on a native counter (effect-lowering unit 3) |
| `reify M : U(Loop_Σ B R)` | answers `thunk nu_in ⟨(force κ) next…, (force κ) close…⟩` | keeps `κ` | `Capture`'s state machine |
| a stored generator | `Yield`'s clause and `tick`'s keep `κ` | keeps `κ` | the same; pull's skip is an observed tick |

- **Totality** is the row without `Div`. A `total fn`'s written row has no `Div`.
- **What stays.** `Loop`, `unfold`, `div_bind` and `div_defer` remain the kernel library of loop
  *values*: `reify`'s result, and hand-written core.
- **Borrows.** `tick` is a non-abortive control operation, so it cannot cross a borrow (T1).
  `LoopLend`'s per-observation lends stay (SPEC §14 *Borrow scopes over loops*). The native loop
  runs those lends one turn at a time.

### 3.3 Where state machines are built

Last, and only where something suspends:
- at `reify` (a loop value: `div_fuel`'s argument when it is a value, an annotated loop, a
  stored generator);
- at every other stored `κ` (BOXED-κ, task queues);
- at whatever forwards through those.

Everywhere else a loop is `iterate`, lowered as a native loop, and its consumer is a direct
call. `main`'s machine (§1.3: 51 code functions for one `while`) does not exist. Under `div_fuel`
the count of ticks is the meaning, and the counter is in the code.

### 3.4 What the erasure keeps, and what is verified

- **Kept**: static names, as now; `iterate`, as a primitive; the qualifier tags `qs`, which
  `Convert` drops today; `Checked.sigs`, extended per name with each operation's clause kind.
- **Classified by the checker**: clause kinds. `[handle]`'s builder sees each clause value, and
  the schemes are fixed, so this is exact (§8 choice 6).
- **Verified in the backend**: the site table's whole-program entries (copy groups, condition 2,
  the clause's code). The backend re-derives each entry's scheme and compares it with the erased
  term, the method of `Frontend/Check/CrossCheck.lean`. A mismatch is an internal error.
- **Table-less input** (kernel programs, hand-written core) takes the generic path. Its
  recognisers produce the same table, and the pinned kernel counts stay
  (`corpus/kernel-counts.expected`).

### 3.5 What remains of carry-then-verify

| piece (previous revision) | now |
|---|---|
| loop entries, call modes, native lowering of machines from a complete root (N4) | **dropped**: loops are `iterate`, and consumers are handlers |
| the span array (the previous revision's channel option C2) | **dropped** from this design; keys are static names. A span array may still come with #532's debug info |
| N1 typed schemes | **merged into B2**: the per-body machine's templates are deleted, not converted. The new elaboration is written as typed schemes. The remaining templates (`forData`, `forYield`, `pullView`) are converted when a unit owes a law over them |
| N2 the channel | **merged into B3**: keep `qs`, pass `Checked.sigs` on |
| N3 the site table | **kept** (effect-lowering unit 9): user `for` bodies' kinds, copy groups, handler state, condition 2 |
| #216 | **kept**, independent |

### 3.6 The fallback, if S0 is killed

The previous revision of this document applies. The meaning stays a machine. Loop entries and
call modes travel in a table, verified against the term. Native lowering runs from complete
roots (N4), and loops U2 is built as filed. It is kept in the PR's history (commit `908f122`).

### 3.7 Units, kept, merged or dropped

| unit | verdict | how |
|---|---|---|
| effect-lowering 1 (#544) | kept | `tailClause?` stays the table's producer for table-less input |
| 2 (#540, running) | **interim**; narrowing, `poison` padding, dead-word removal kept | it is the speed-up until B3. Afterwards `drive` runs only at `reify` and in hand-written core, so its loop recovery serves those alone. Let it finish its brief |
| 3 classify; native handler state | kept, **moved before B3** | `div_fuel`'s counter is its first client |
| 4 resume or cancel in place | kept | `break` out of a `for` over a generator |
| 5 one code per codata value; copies merged | kept | `reify`'s and stored generators' machines |
| 6 specialisation S1 | kept | — |
| 7 push stages | kept | an adapter drained by one `for` is pushed instead of reified |
| 8 abortive pass-through, loop exit | kept | — |
| 9 site table (N3) | kept, after 3 | user-code clause kinds |
| loops U1 (#548, running) | kept | the node |
| U2 (#549) | **class pass merged into B2**, as `Div` inference; **counted machine loops dropped** | a counted loop with `Div` in its body is `bounded_fix` at the row |
| U3 (#550) | kept, simpler | every loop is `iterate` or a fold, so an edge is `inr` per level |
| U4 (#551) | kept, simpler | moves between machine points are gone; exits are `up` sums per level |
| U5 (#58) | independent | — |
| N1, N2, N4 | merged, merged, dropped | §3.5 |

New units:

| # | unit | needs | acceptance |
|---|---|---|---|
| **S0** | **the proof spike** (§4.1) | — | §4.1 |
| B1 | **kernel**: `cwp` at rows with `Div`, `iterate`, `reify`, `div_fuel`; FP and adequacy at those rows; SPEC §14 and §19 rewritten | S0 | FP, adequacy, `total_every_run` with their statements; axioms within the three |
| B2 | **frontend**: the `Div` elaboration (§3.2) as typed schemes; the per-body machine, `div_bind`/`div_defer` emission and §14's specialisation deleted; loops U2's class pass as `Div` inference | B1, U1 | every output, golden, exit status, `live 0` and `div_fuel` answer unchanged; loops' matrix (24 non-AA cells) and `return` matrix run; sugar pairs' core forms rewritten, each diff listed |
| B3 | **backend**: `qs` kept, `Checked.sigs` passed on; `iterate` lowered natively; `Div`'s runtime clause as a direct call; `reify` through `Capture` | B2, unit 3 | sieve ≤ 1.4×, chain-yield ≤ 1.2×; `allocs`, `indirect`, `copies` only drop |

**Order.** U1 (running) and #540 (running) finish. Then S0. If S0 passes: B1 → B2 → unit 3 →
B3 → units 4, 5, 9 → U3 → U4 → 7 → 8, 6. #216 can go any time after unit 9.

## 4. Laws and proofs

### 4.1 S0, the proof spike

An experiment (`experiments/DivEffect`, per *Spec first*), kernel only, before any build. B1 (#563) promoted it into `Core/`; its code is at `f661c7b`.

**Unknown 1: the relation.** `ewpTS` is a least fixed point (SPEC §19 *Divergence*), so a
computation that ticks forever is not in it. That is why today's div is `ν` codata.
- **Candidate** (hypothesis): a greatest fixed point over segments, guarded by `tick`:

      cwp M Q  ≜  gfp W. ewpTS M Π_W Q,      Π_W(tick) = λ_. λκ. ∀ n : Next. W (κ n)

  Each segment, up to the next tick, is finite (`ewpTS`). The continuation after a tick is again
  in `W`. The functional is monotone by `ewp_mono`. No step-indexing is used: `tick` is the guard.
- **To prove**, at rows that hold `Div`:
  1. the compatibility of `[let]` and bind, `[sub]`, `[perform]` (of `tick` and of other names),
     `[then]`, and `[handle]` of another name, where `tick` is forwarded and its case is the
     coinductive one;
  2. `iterate`'s compatibility, by coinduction;
  3. safety: a closed program at the row `{Div}`, driven by the runtime's clause, is never
     stuck on any prefix of any run, under every allocator (as `externs_loop_every_run` is for
     `main`'s loop today);
  4. `div_fuel n M` is in `wpTS` (total), by induction on `n` with `cwp`'s unfolding;
  5. `reify M` is in `𝒱⟦U(Loop_Σ B R)⟧` (`Core/NuRel.lean`), by coinduction;
  6. `total_every_run` keeps its statement: its row is empty, so `cwp` never applies.
- **The alternative**: step-index only the `Div` fragment, with a `▷` at each tick. It gives
  guardedness uniformly. Its cost is that the indexed relation must meet the unindexed one at
  `reify` and `div_fuel`, and any borrow frame at a `Div` row would have to be indexed. None is
  needed while `tick` obeys T1. It is used only if the greatest fixed point fails at items 1–5.

**Unknown 2: the residual.** A loop closed early hands back what has no destructor (SPEC §14). The
cancel of a cancellable continuation answers `()`, and a cancel that answered the residual would
change "the canceller sees `()`" (algebra, *Cancel*).
- **Candidate** (hypothesis): `tick`'s continuation is linear, so closing is `κ close`, a resume.
  The code after the tick returns `inr` of the residual by name (§3.2).
- **To show**: a kernel program whose loop holds a capability with no destructor is closed by
  `div_fuel 3` and hands the capability back. It needs a tied derivation, a run, and its compiled
  form with `live 0`. This is `corpus/io-fuel.bc`'s `collatz_within` in the kernel.

**Unknown 3: the placement of ticks.** `div_fuel` counts observations, and a pull consumer may
treat a skip as the end (`first_two` in `corpus/for-data-div.bc`).
- **Candidate**: a tick at each `MCx.skip` of today's `mGoto` (`Sugar.lean:1103–1128`).
- **To prove**: a simulation over a schema of div bodies (loops, joins, direct-style calls; the
  empty row and a row). For every run, the number of ticks a `reify` of the `Div` elaboration
  observes equals the number of observations of today's machine. The two also give the same
  answers and the same effects in order.
- **To list**: the corpus programs whose observations are counted. Those using `div_fuel`:
  `io-fuel`, `lend-lib-each`, `lend-lib-loop`, `sugar/hof-closure`, `sugar/hof-local`,
  `sugar/hof-returned`, `sugar/surface-defer`. Those whose consumers observe a stored
  generator's skips: the pull consumers. They are B2's acceptance.

**Acceptance**: items 1–6 of unknown 1, the program of unknown 2 and the lemma of unknown 3,
each proved, with `#print axioms` within `[propext, Classical.choice, Quot.sound]`.

**Kill criteria**:
1. Items 1–5 are not provable, by the greatest fixed point or by the indexed fragment, without
   indexing a borrow frame. That would be a borrow-calculus cost. Then stop, and fall back
   (§3.6).
2. No must-resume `tick` program of unknown 2 hands the residual back, and only a cancel that
   answers it works. That is the algebra hard stop on *Cancel* (§9.1).
3. A counted program's observations cannot be matched by any placement. That is hard-stop item 2
   (§9.1).

### 4.2 G: typing rules, laws, and what the proofs need

**Typing** (B1, after S0):
- `iterate` is one constant, `CDerives.iterate`, at a row holding a `Div` name, with its machine
  step.
- `reify` and `div_fuel` are two constants with their own rules: today `div_fuel` is library code
  over `unfold`.
- A handler of `Div` written by the program is typed only when its result row holds `Div` again
  (it re-ticks). A handler that resumes forever at a row without `Div` would be a total-typed
  computation that does not end, against `total_every_run`. This is a typing rule, not a runtime
  one, and it needs a recorded decision (§8 choice 3).

**Laws**:

| law | statement | status |
|---|---|---|
| the handler laws, algebraicity | `Div` is an effect like any other: H-ret, H-op, H-fwd; `tick to x. P = tick(; n. (k n to x. P))` | from §19, at `cwp` |
| linearity | `tick`'s `κ` is resumed exactly once; it has no cancel (`kappaC_cancel_lin`) | §19's |
| complete drive | under the runtime's clause, `iterate (f, s)` runs `f` until `inl` | `tail_resumes` and `iterate`'s step |
| fuel | `div_fuel n M` observes at most `n` ticks, then closes; equal to today's `driveE n` | S0; today "by construction, not by a proved equation" (SPEC §14 *Open*) |
| reification | each observation of `reify M` runs one segment, to the next tick or the end | S0 |
| totality | a closed computation at a row without `Div` terminates | `total_every_run`, unchanged |

**What the existing proofs need**:
- FP and adequacy: restated over `cwp` at rows that hold `Div`, by S0's lemmas. Unchanged
  elsewhere.
- `total_every_run`: nothing.
- Borrow frames ([TR] 6.64–6.66 and the unwinding frames): nothing, since a borrow callback's row
  stays unwind-only.

**Formers**: no value-type or computation-type former. The additions are one primitive, one
relation clause, two constants and one `[handle]` side condition.

### 4.3 M: the agreement check

Only the site table remains in M (N3: user clause kinds' codes, copy groups, condition 2).

- **Per entry, on every compile**: the backend re-derives the entry's scheme and compares it with
  the erased term. A mismatch is an internal error.
- **Per scheme, once, in Lean**: the law each special lowering rests on (`tail_resumes`; units 3,
  4 and 7's equations), stated over the typed scheme functions.
- **Differential**: the stages' interpreters against the goldens, as today.
- **Rejected: compiling from an IR the checker never saw.** That is Lean's `partial` and
  `implemented_by` (§5). With `Div`, the checked term carries the loops itself, so the compiled
  code stays a function of it.

### 4.4 #216, clause multiplicity

- *Grades*: `{1, ω}` per clause, from the qualifier and the answer type: an abortive operation's
  clause is graded 1, a resuming one's ω.
- *Typing*: `[handle]`'s premise that the clauses' context is persistent holds where the clause
  is graded ω. Where it is graded 1, the context drops.
- *Law*: a clause graded 1 runs at most once per instance of its handler (`catch_abort`).
- *Proofs*: `handle_compatC`'s abortive case with an environment that holds no owned cell
  (`Ctx.OwnFree`).
- *Borrows*: none.
- Its own unit, after unit 9.

### 4.5 Borrow interactions

| change | borrow effect |
|---|---|
| `tick` as a linear control operation | cannot cross a borrow (T1): a `while` in a borrow block is rewritten per turn by `LoopLend`, as today |
| `iterate` lowered natively | the lends are the meaning's, one per turn, ended inside it. A frame slot only where no resumption point crosses the scope (`crossedScopes`) |
| `reify`'s machine | as today's stored continuations: the state holds a lent cell's location (SPEC §29) |
| #216 | a captured borrow outlives the site, as every capture |
| keeping `qs`, passing the effect context | none |

## 5. Prior art, compared on fit

| system | what it carries, and how | fit |
|---|---|---|
| Granule (Orchard, Liepelt, Eades, *Quantitative program reasoning with graded modal types*, ICFP 2019) | graded modalities over a semiring: how many times a value is used; graded effects | #216's clause multiplicity is such a grade. Tail position is not: grades compose by counting |
| QTT (McBride, *I Got Plenty o' Nuttin'*, 2016; Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS 2018; Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP 2021) | the 0 grade decides what erasure removes | the converse here: facts with no runtime meaning (kinds, spans, entries) that erasure must *keep* for the compiler. QTT's discipline applies: they must not change the meaning, which is why they sit beside the checked term |
| Koka (Leijen, *Type Directed Compilation of Row-Typed Algebraic Effects*, POPL 2017; Xie et al., *Effect Handlers, Evidently*, ICFP 2020; Xie and Leijen, *Generalized Evidence Passing for Effect Handlers*, ICFP 2021) | clause kinds are written in the handler (`fun`, `val`, `ctl`, `final ctl`); a `fun` runs in place; `div` is an effect in the row, and total means no effect | the clause kind as a declared, checked form is §2.3's route for A1. Koka's `div` row is this design's base (§3). Here it is a handled effect with a coinductive model (S0), where Koka's has no mechanised model. Koka's evidence is run-time, which #541 forbids |
| Effekt (Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*, OOPSLA 2020; Schuster, Brachthäuser, Ostermann, *Compiling Effect Handlers in Capability-Passing Style*, ICFP 2020; Brachthäuser, Schuster, Lee, Boruch-Gruszecki, *Effects, Capabilities, and Boxes*, OOPSLA 2022) | lifts are inserted by a type-directed translation, so the compiler knows them; blocks are second-class unless boxed | the closest fit. The translation's output carries what the types decided, as the table does. System C's box is the reification point. Here that point is `reify`, an explicit handler of `Div` (§3.2), not a value-type former |
| Lean 4 (Ullrich and de Moura, *`do` Unchained*, ICFP 2022; `partial`, `implemented_by`) | `do` elaborated to `forIn` with join points and a threaded tuple; the compiler compiles `partial` definitions from code the kernel sees as an opaque constant | the `do` translation is loops U3/U4's. `partial` is the M-direct design: compiled code the kernel never checked, trusted. §4.3 rejects it for borrow guarantees |
| MLIR (Lattner et al., *MLIR: Scaling Compiler Infrastructure for Domain Specific Computation*, CGO 2021) | `scf.for`/`scf.while` with loop-carried values, lowered to the unstructured `cf` dialect by a later conversion; progressive lowering | the loop node with live variables per edge (U3) is `scf`'s `iter_args`. Progressive lowering is §3.1's order: a loop stays `iterate` until the flat IR |
| Rust MIR (rustc's MIR building, NLL borrow checking, drop elaboration, `rustc_mir_transform/src/coroutine.rs`) | one IR is borrow-checked and compiled; the coroutine transform runs on MIR after borrow checking | the property kept here: the compiled code comes from the checked IR, and the state machine is made after checking, at `reify`. With `Div`, the checked term's loops become a good compilation IR too, as MIR's are |
| CPS, ANF, join points (Appel, *Compiling with Continuations*, 1992; Flanagan, Sabry, Duba, Felleisen, *The Essence of Compiling with Continuations*, PLDI 1993; Kennedy, *Compiling with Continuations, Continued*, ICFP 2007; Fluet and Weeks, *Contification Using Dominators*, ICFP 2001; Maurer, Downen, Ariola, Peyton Jones, *Compiling without Continuations*, PLDI 2017) | CPS reifies every continuation, then contification recovers the second-class ones. Kennedy separates local continuations from first-class ones. GHC's join points are a typed form of Core that Core Lint checks and the optimiser preserves | our kernel term is the reify-everything end: a `κ` per operation, a `ν` per div body. A1, A9 and #540 are contification. GHC's lesson is §2.3's: make the non-reified case a checked form, so that it is kept, not recovered. SSA (Kelsey 1995; Appel, *SSA is Functional Programming*, 1998) is ANF with join points. With `Div`, a loop arrives as `iterate` and never needs contifying |


## 6. The test before building

### 6.1 What disappears, what appears

- **Deleted, after B2–B3**:
  - the per-body machine (`mWalk`, `mAssemble`, `mLoop`, `divMachine`, `Sugar.lean:957–1527`)
    and its templates;
  - the emission of `div_bind` and `div_defer`;
  - §14's specialisation at a callback's computation type, which becomes rows;
  - `loopsAt` and `LoopLend`'s `fin` as tests of "loops", replaced by the row;
  - `drive` around `main`;
  - #540's loop recovery for elaborated programs;
  - A9, A10, D1 and D7 of §1.2.
- **No longer the decision for elaborated programs**: `tailClause?` and `clausesAt` (A1, A4),
  which stay for table-less input.
- **Unchanged**: C1–C7, B1, B2, `Capture` for `reify` and stored `κ`.
- **New kernel forms**: `iterate`; `cwp` at `Div` rows; `reify` and `div_fuel` as constants.

### 6.2 Predicted effect on #537's rows

| row | now | predicted | units | why |
|---|---|---|---|---|
| sieve | 5.63× | ≤ 1.4× (sieve-for 1.30×) | B3 | its `while`s are `iterate`; the runtime's tick is a direct call |
| chain-yield | 2.10× | ≤ 1.2× (chain-for 0.99×) | B3 | `yield` direct (#547); `range`'s `while` native |
| chain-gen | 21.5× | ≤ 1.3× | B3, 7 | push stages; without 7, two `reify` machines per element stay |
| gen-tree | 1.72× | ≤ 1.4× | 8 | unchanged by this design |
| async-tree | 0.84×, indirect 201 | ≤ 0.84×, indirect 0 | 5, 9 | — |
| raise-small | 1.30× | ≤ 1.1× | 8 | unchanged by this design |
| handlers-di, raise-large | 0.98×, 1.03× | unchanged | — | — |

§1.3's `while` program compiles to about the counted version's size: 10 code functions rather
than 51. Hypothesis. `allocs`, `indirect` and `copies` only drop. The count of `drive`s outside
`reify` and hand-written core is 0 on the corpus and `bench/`.

### 6.3 Kill criteria

1. **S0**: §4.1's three criteria.
2. **Meaning**: B2 or B3 changes an output, a golden, an exit status, `live 0`, a falsifier mode
   or a `div_fuel` answer. That is a hard stop.
3. **Construction**: after B3, a loop of an elaborated program is still turned by `drive`
   outside `reify`.
4. **Cost elsewhere**: after B3, sieve is above 1.6× or chain-yield above 1.5×.
5. **The table is incomplete**: after unit 9, an elaborated program still needs a search
   recogniser to decide a site's lowering.

## 7. Build plan

§3.7's order: S0, then B1, B2, unit 3, B3, units 4, 5 and 9, U3, U4, units 7, 8 and 6. #216 is
independent. Each unit lands with its spec text, its acceptance programs, `counts.expected` and
the desugar diff. B1–B3 touch `Core/`, `Frontend/` and `Backend/`, so `make gate-full` applies.

## 8. Open choices for the user

1. **Loops U2** (#549): **hold its counted-machine half until S0 reports (recommended)**, or
   build it as filed now. B2 accepts the same nests by construction, and U2's machine code would
   be deleted with the machine. If S0 is killed, U2 is built as filed.
2. **The relation**: **the greatest fixed point over segments (recommended)**, or the
   step-indexed fragment if S0 needs it (§4.1).
3. **Handlers of `Div` written by programs**: **typed only at a result row holding `Div`
   (recommended)**, or not provided. Either is a typing restriction to record.
4. **`reify` and `div_fuel`**: **kernel constants with their own rules (recommended)**, or
   ordinary handlers under a coinductive `[handle]` rule.
5. **#540**: land it on its own acceptance as the interim speed-up (recommended).
6. **Who classifies clause kinds**: **the checker (recommended)**, or the backend's verifier.
7. **#216's timing**: after unit 9 (recommended), or later.

## 9. Hard stops and defects

### 9.1 The algebra hard stop

No step of this design changes a decided equation, if S0's candidates hold. These would:

| candidate | law | change | programs | where it stands |
|---|---|---|---|---|
| closing a loop by a cancel that answers the residual | *Cancel*: "the canceller sees `()`" | a cancel answering `R` | every `div_fuel` over a loop holding a capability with no destructor: `corpus/io-fuel.bc`, `lend-lib-loop.bc`, `lend-lib-each.bc` | avoided by the must-resume `tick` (S0, unknown 2); a stop if S0 kills it |
| ticks other than at today's skips | hard-stop item 2 | `div_fuel`'s counts and the skips a pull consumer sees | the `div_fuel` programs of §4.1 and the pull consumers, e.g. `for-data-div.bc`'s `first_two` | avoided by placement (S0, unknown 3); a stop if no placement matches |

**A restriction to record**: a program's handler of `Div` at a row without `Div` (§4.2). No
existing program is rejected by it.

### 9.2 Defects

1. **The checked qualifier is discarded at conversion** (`Convert.lean:737–739`). The backend
   builds a cancel arm for every `κ` (`Capture.lean:259–266`), a must-resume `κ`'s included. It
   matters more now: `tick` is linear, so every `reify` machine would carry dead cancel arms.
   Root fix: keep `qs` (B3).
2. **The elaboration schemes are strings** (`Sugar.lean:253`, `:570`, `:1057`; 18 call sites).
   Most are the per-body machine's and are deleted by B2. The rest (`forData`, `forYield`,
   `pullView`, the count literal, `main`'s lifetime) still cannot carry a law. That matters for
   unit 7's push/pull equation and U4's exit propagation, which loops U2's acceptance and
   effect-lowering units 3 and 7 ask to be proved over elaborated terms. Root fix: B2 writes
   typed schemes, and each unit converts the scheme it proves a law over.
3. **The frontend's lowering report is not the lowering** (D5). `for-yield-branch.bc`'s three
   sites have one report text, and the backend made two direct calls and one machine. It still
   matters for user `for` bodies. Root fix: unit 9 renders the report from the table.

**Unverified.** #540 and U1 were read from WIP worktrees. S0's three candidates, the laws marked
S0 and every row of §6.2 are hypotheses.

## 10. Reproduction

All runs use `.lake/build/bin/` built from `3b67803`.

- `bcc-counts --sites bench/{chain-yield,chain-gen,sieve,gen-tree,async-tree}/main.bc` and
  `corpus/for-yield-branch.bc`: §1.3's table.
- `bcc check bench/chain-gen/main.bc | grep lowering`, and the same for
  `corpus/for-yield-branch.bc`: the reports.
- The two programs of §1.3:

      fn spin(n: i32) -> i32 =
        let mut i = 0;
        let mut s = 0;
        while i < n { s = s + i; i = i + 1 };
        s
      main -> i32 = spin(10)

  and the same with `let mut s = 0; for i in 0..n { s = s + i }; s`. Run `bcc check`,
  `bcc compile -o x.wat` (then `grep -c '(func \$f'`) and `bcc-counts` on each.
